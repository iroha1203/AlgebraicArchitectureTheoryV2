//! 第5章の問い3。変更の後も保たれるか。

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use globset::GlobSet;
use serde_json::{Value, json};

use crate::atom::Atom;
use crate::expr::{self, BinOp, Expr};
use crate::law::Law;
use crate::model::{Model, Step};
use crate::report::Finding;

const MAX_DEPTH: usize = 32;
const MAX_PATHS: usize = 4096;

pub const CONDITIONS: &[&str] = &[
    "フィールドは型ごとに一つの値として扱い、同じ型の別々の実体は区別しない。",
    "条件どうしの関係は見ない。",
    "操作の呼び出しの結果は、fresh を除き、同じ操作に同じ値を渡せば同じ結果が返るものとみなす。",
];

/// 計算に要る、Law ファイルとソースの情報。
pub struct Ctx {
    pub sources: Vec<String>,
    pub fresh: GlobSet,
}

/// 変更前の要素と変更後の要素の対応。
#[derive(Clone, Debug, Default)]
pub struct Corr {
    pub forward: BTreeMap<String, Vec<String>>,
    pub backward: BTreeMap<String, Vec<String>>,
    /// 行き先を `|` で並べた、まだ決めていない対応。
    pub undecided: Vec<Atom>,
}

impl Corr {
    pub fn build(before: &Model, after: &Model, change: &[Atom]) -> Corr {
        let mut corr = Corr::default();
        let mut explicit: BTreeMap<String, Vec<String>> = BTreeMap::new();
        for a in change.iter().filter(|a| a.kind == "corresponds") {
            let object = a.object.clone().unwrap_or_default();
            if object.contains('|') {
                corr.undecided.push(a.clone());
                continue;
            }
            explicit.entry(a.subject.clone()).or_default().push(object);
        }
        for (o, targets) in explicit.clone() {
            if !before.is_operation(&o) {
                continue;
            }
            for t in targets.iter().filter(|t| after.is_operation(t)) {
                let after_params = after.params(t);
                for p in before.params(&o).keys() {
                    let pe = format!("{o}.${p}");
                    if !explicit.contains_key(&pe) && after_params.contains_key(p) {
                        explicit.entry(pe).or_default().push(format!("{t}.${p}"));
                    }
                }
            }
        }
        let after_elems = after.elements();
        for e in before.elements() {
            if !explicit.contains_key(&e) && after_elems.contains(&e) {
                explicit.insert(e.clone(), vec![e]);
            }
        }
        for (s, ts) in &explicit {
            for t in ts {
                corr.backward.entry(t.clone()).or_default().push(s.clone());
            }
        }
        corr.forward = explicit;
        corr
    }

    fn images(&self, e: &str) -> &[String] {
        self.forward.get(e).map(Vec::as_slice).unwrap_or(&[])
    }
}

/// 候補を元の ArchMap に重ねた、変更後の Atom。
pub struct Overlay {
    pub atoms: Vec<Atom>,
    pub rewritten: BTreeSet<String>,
    pub removed: BTreeSet<String>,
}

pub fn is_removed(removed: &BTreeSet<String>, name: &str) -> bool {
    removed
        .iter()
        .any(|r| name == r || name.starts_with(&format!("{r}.")) || name.starts_with(&format!("{r}->")))
}

pub fn overlay(base: &[Atom], plan: &[Atom]) -> Overlay {
    let rewritten: BTreeSet<String> = plan.iter().filter(|a| a.is_structure() || a.kind == "meaning").map(|a| a.subject.clone()).collect();
    let removed: BTreeSet<String> = plan.iter().filter(|a| a.kind == "removes").map(|a| a.subject.clone()).collect();
    let replaced = |s: &str| {
        rewritten.contains(s) || rewritten.iter().any(|r| s.starts_with(&format!("{r}->"))) || is_removed(&removed, s)
    };
    let mut atoms: Vec<Atom> = base
        .iter()
        .filter(|a| a.kind == "observed" || !replaced(&a.subject))
        .cloned()
        .collect();
    atoms.extend(plan.iter().filter(|a| a.is_structure() || a.kind == "meaning").cloned());
    // 変更後の要素の意味は、corresponds で変更前の要素の意味を移したもの。
    let plan_name = plan.iter().find(|a| a.kind == "plan").map(|a| a.subject.clone()).unwrap_or_default();
    for c in plan.iter().filter(|a| a.kind == "corresponds") {
        let Some(target) = c.object.as_deref().filter(|o| !o.contains('|')) else { continue };
        for m in base.iter().filter(|a| a.kind == "meaning" && a.subject == c.subject) {
            let mut moved = m.clone();
            moved.subject = target.to_string();
            moved.at = Some(format!("plan:{plan_name}"));
            atoms.push(moved);
        }
    }
    Overlay { atoms, rewritten, removed }
}

// ---- 記号の値 ----

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Term {
    Const(String),
    /// フィールドの入力の値。名前は変更前の要素の名前。
    Input(String),
    /// 最上位の操作の引数。
    Param(String),
    Proj(Box<Term>, String),
    Call(String, Vec<Term>),
    /// `fresh` の操作の呼び出し。呼び出しの場所ごとに別の値。
    Fresh(String, String),
    Not(Box<Term>),
    Neg(Box<Term>),
    Bin(BinOp, Box<Term>, Box<Term>),
    Unknown,
}

impl Term {
    fn has_unknown(&self) -> bool {
        match self {
            Term::Unknown => true,
            Term::Proj(t, _) | Term::Not(t) | Term::Neg(t) => t.has_unknown(),
            Term::Call(_, args) => args.iter().any(Term::has_unknown),
            Term::Bin(_, a, b) => a.has_unknown() || b.has_unknown(),
            _ => false,
        }
    }

    fn bin(op: BinOp, a: Term, b: Term) -> Term {
        let commutative = matches!(op, BinOp::Eq | BinOp::Ne | BinOp::And | BinOp::Or | BinOp::Add | BinOp::Mul);
        if commutative && b < a {
            Term::Bin(op, Box::new(b), Box::new(a))
        } else {
            Term::Bin(op, Box::new(a), Box::new(b))
        }
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Term::Const(c) => write!(f, "{c}"),
            Term::Input(n) => write!(f, "入力({n})"),
            Term::Param(p) => write!(f, "{}", p.replacen(".$", " の引数 $", 1)),
            Term::Proj(t, n) => write!(f, "{t}.{}", n.rsplit('.').next().unwrap_or(n)),
            Term::Call(n, args) => {
                write!(f, "{n}(")?;
                for (i, a) in args.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{a}")?;
                }
                write!(f, ")")
            }
            Term::Fresh(n, site) => write!(f, "{n}()@{site}"),
            Term::Not(t) => write!(f, "not ({t})"),
            Term::Neg(t) => write!(f, "-({t})"),
            Term::Bin(op, a, b) => {
                let e = Expr::Bin(*op, Box::new(Expr::Name(a.to_string())), Box::new(Expr::Name(b.to_string())));
                write!(f, "({e})")
            }
            Term::Unknown => write!(f, "?"),
        }
    }
}

/// 条件を、形をそろえた原子と真偽の組の列にする。列は「かつ」で読む。
fn literals(t: &Term, pol: bool, out: &mut Vec<(Term, bool)>) {
    match t {
        Term::Not(x) => literals(x, !pol, out),
        Term::Bin(BinOp::And, a, b) if pol => {
            literals(a, true, out);
            literals(b, true, out);
        }
        Term::Bin(BinOp::Ne, a, b) => out.push((Term::bin(BinOp::Eq, (**a).clone(), (**b).clone()), !pol)),
        Term::Bin(BinOp::Gt, a, b) => out.push((Term::bin(BinOp::Lt, (**b).clone(), (**a).clone()), pol)),
        Term::Bin(BinOp::Ge, a, b) => out.push((Term::bin(BinOp::Lt, (**a).clone(), (**b).clone()), !pol)),
        Term::Bin(BinOp::Le, a, b) => out.push((Term::bin(BinOp::Lt, (**b).clone(), (**a).clone()), !pol)),
        _ => out.push((t.clone(), pol)),
    }
}

// ---- 操作を書き込みの列として実行する ----

#[derive(Clone, Copy, PartialEq)]
enum Side {
    Before,
    After,
}

#[derive(Clone, Debug)]
struct Written {
    key: String,
    field: String,
    value: Term,
    at: Option<String>,
    op: String,
}

#[derive(Clone, Debug, Default)]
struct Branch {
    state: BTreeMap<String, Term>,
    assign: BTreeMap<Term, bool>,
    /// 分岐の原子ごとに、それを持ち込んだ条件の字句、場所、字句が成り立つときの原子の真偽。
    origin: BTreeMap<Term, (String, Option<String>, bool)>,
    trace: Vec<Written>,
}

#[derive(Debug)]
struct Silence {
    reason: &'static str,
    next: Vec<(String, String)>,
    detail: String,
    at: Option<String>,
}

type Env = BTreeMap<String, (Term, Option<String>)>;

struct Exec<'a> {
    model: &'a Model,
    side: Side,
    corr: &'a Corr,
    ctx: &'a Ctx,
}

impl Exec<'_> {
    /// 名前を変更前の名前にそろえる。
    fn canon(&self, name: &str) -> String {
        if self.side == Side::After {
            if let Some([one]) = self.corr.backward.get(name).map(Vec::as_slice) {
                return one.clone();
            }
        }
        name.to_string()
    }

    /// フィールドの値を置く場所。一対一で対応するフィールドは、変更前の名前で置く。
    fn key(&self, field: &str) -> String {
        if self.side == Side::After {
            if let Some([one]) = self.corr.backward.get(field).map(Vec::as_slice) {
                if self.corr.images(one).len() == 1 {
                    return one.clone();
                }
            }
        }
        field.to_string()
    }

    /// フィールドの入力の値。変更後のフィールドは、対応する変更前のフィールドの値を写したもの。
    fn initial(&self, field: &str) -> Term {
        Term::Input(self.canon(field))
    }

    fn read(&self, b: &Branch, field: &str) -> Term {
        b.state.get(&self.key(field)).cloned().unwrap_or_else(|| self.initial(field))
    }

    fn eval(&self, e: &Expr, op: &str, env: &Env, b: &Branch, site: &str) -> (Term, Option<String>) {
        match e {
            Expr::Const(c) => (Term::Const(c.clone()), None),
            Expr::Unknown => (Term::Unknown, None),
            Expr::Name(n) if n.starts_with('?') => (Term::Unknown, None),
            Expr::Name(n) => (Term::Const(self.canon(n)), None),
            Expr::Path(p, fields) => {
                let (mut term, mut ty) = env.get(p).cloned().unwrap_or_else(|| {
                    let pe = format!("{op}.${p}");
                    (Term::Param(self.canon(&pe)), self.model.type_of(&pe))
                });
                let root = matches!(term, Term::Param(_));
                for (i, f) in fields.iter().enumerate() {
                    let fname = ty.as_ref().map(|t| format!("{t}.{f}")).filter(|n| self.model.is_field(n));
                    match fname {
                        Some(n) if i == 0 && root => term = self.read(b, &n),
                        Some(n) => term = Term::Proj(Box::new(term), self.canon(&n)),
                        None => term = Term::Proj(Box::new(term), f.clone()),
                    }
                    ty = fname_type(self.model, fields, i, &ty);
                }
                (term, ty)
            }
            Expr::Call(n, _) if n.starts_with('?') => (Term::Unknown, None),
            Expr::Call(n, args) => {
                if self.ctx.fresh.is_match(n) {
                    return (Term::Fresh(self.canon(n), site.to_string()), None);
                }
                let args = args.iter().map(|a| self.eval(a, op, env, b, site).0).collect();
                (Term::Call(self.canon(n), args), None)
            }
            Expr::Not(x) => (Term::Not(Box::new(self.eval(x, op, env, b, site).0)), None),
            Expr::Neg(x) => (Term::Neg(Box::new(self.eval(x, op, env, b, site).0)), None),
            Expr::Bin(o, x, y) => {
                let x = self.eval(x, op, env, b, site).0;
                let y = self.eval(y, op, env, b, site).0;
                (Term::bin(*o, x, y), None)
            }
        }
    }

    fn eval_text(&self, text: &str, op: &str, env: &Env, b: &Branch, site: &str) -> Term {
        match expr::parse(text) {
            Ok(e) => self.eval(&e, op, env, b, site).0,
            Err(_) => Term::Unknown,
        }
    }

    fn run(&self, op: &str) -> Result<Vec<Branch>, Silence> {
        let mut stack = vec![op.to_string()];
        self.exec_op(op, &Env::new(), vec![Branch::default()], &mut stack)
    }

    fn exec_op(&self, op: &str, env: &Env, mut branches: Vec<Branch>, stack: &mut Vec<String>) -> Result<Vec<Branch>, Silence> {
        let Some(steps) = self.model.steps.get(op) else { return Ok(branches) };
        for step in steps {
            let mut next = Vec::new();
            for b in branches {
                next.extend(self.step(op, env, step, b, stack)?);
            }
            if next.len() > MAX_PATHS {
                return Err(Silence { reason: "limit", next: vec![], detail: format!("{op} の分岐が {MAX_PATHS} を超えた"), at: None });
            }
            branches = next;
        }
        Ok(branches)
    }

    fn guard(&self, op: &str, env: &Env, atom: &Atom, b: Branch) -> Result<(Vec<Branch>, Vec<Branch>), Silence> {
        let Some(when) = &atom.when else { return Ok((vec![b], vec![])) };
        let site = atom.at.clone().unwrap_or_default();
        let t = self.eval_text(when, op, env, &b, &site);
        if t.has_unknown() {
            return Err(Silence {
                reason: "unresolved",
                next: vec![(site_path(&site), "structure".to_string())],
                detail: format!("条件 `{when}` に ? がある"),
                at: atom.at.clone(),
            });
        }
        let mut lits = Vec::new();
        literals(&t, true, &mut lits);
        let mut taken = vec![b];
        let mut skipped = Vec::new();
        for (a, pol) in lits {
            let mut nt = Vec::new();
            for mut q in taken {
                q.origin.entry(a.clone()).or_insert_with(|| (when.clone(), atom.at.clone(), pol));
                match q.assign.get(&a) {
                    Some(v) if *v == pol => nt.push(q),
                    Some(_) => skipped.push(q),
                    None => {
                        let mut t = q.clone();
                        t.assign.insert(a.clone(), pol);
                        nt.push(t);
                        let mut f = q;
                        f.assign.insert(a.clone(), !pol);
                        skipped.push(f);
                    }
                }
            }
            taken = nt;
        }
        Ok((taken, skipped))
    }

    fn step(&self, op: &str, env: &Env, step: &Step, b: Branch, stack: &mut Vec<String>) -> Result<Vec<Branch>, Silence> {
        let atom = match step {
            Step::Write(a) => a,
            Step::Call { atom, .. } => atom,
        };
        let site = atom.at.clone().unwrap_or_else(|| op.to_string());
        let (taken, mut out) = self.guard(op, env, atom, b)?;
        for mut b in taken {
            match step {
                Step::Write(a) => {
                    let field = a.object.clone().unwrap_or_default();
                    let value = self.eval_text(a.value.as_deref().unwrap_or("?"), op, env, &b, &site);
                    let key = self.key(&field);
                    b.state.insert(key.clone(), value.clone());
                    b.trace.push(Written { key, field, value, at: a.at.clone(), op: op.to_string() });
                    out.push(b);
                }
                Step::Call { atom, element } => {
                    let callee = atom.object.clone().unwrap_or_default();
                    if callee.starts_with('?') {
                        return Err(Silence {
                            reason: "unresolved",
                            next: vec![(site_path(&site), "structure".to_string())],
                            detail: format!("呼び出し先 `{callee}` が解決されていない"),
                            at: atom.at.clone(),
                        });
                    }
                    if !self.model.is_operation(&callee) {
                        if let Some(src) = self.model.unread_source_for(&callee, &self.ctx.sources) {
                            return Err(Silence {
                                reason: "unread",
                                next: vec![(src, "structure".to_string())],
                                detail: format!("{op} が呼ぶ {callee} の書き込みが分からない"),
                                at: atom.at.clone(),
                            });
                        }
                        out.push(b);
                        continue;
                    }
                    if stack.contains(&callee) || stack.len() >= MAX_DEPTH {
                        return Err(Silence { reason: "limit", next: vec![], detail: format!("{callee} の展開が再帰か上限に当たった"), at: atom.at.clone() });
                    }
                    let mut cenv = Env::new();
                    for pa in self.model.passes.get(element).into_iter().flatten() {
                        let target = pa.object.clone().unwrap_or_default();
                        let Some((_, p)) = target.rsplit_once(".$") else { continue };
                        let v = self.eval_text(pa.value.as_deref().unwrap_or("?"), op, env, &b, &site);
                        let ty = self.model.type_of(&target);
                        cenv.insert(p.to_string(), (v, ty));
                    }
                    stack.push(callee.clone());
                    let res = self.exec_op(&callee, &cenv, vec![b], stack);
                    stack.pop();
                    out.extend(res?);
                }
            }
        }
        Ok(out)
    }
}

fn fname_type(model: &Model, fields: &[String], i: usize, ty: &Option<String>) -> Option<String> {
    let t = ty.as_ref()?;
    model.type_of(&format!("{t}.{}", fields[i]))
}

fn site_path(site: &str) -> String {
    crate::atom::parse_location(site).map(|l| l.path).unwrap_or_else(|| site.to_string())
}

fn consistent(a: &BTreeMap<Term, bool>, b: &BTreeMap<Term, bool>) -> bool {
    a.iter().all(|(k, v)| b.get(k).is_none_or(|w| w == v))
}

fn trace_json(trace: &[Written]) -> Value {
    json!(trace.iter().map(|w| json!({"op": w.op, "field": w.field, "value": w.value.to_string(), "at": w.at})).collect::<Vec<_>>())
}

fn branch_json(assign: &BTreeMap<Term, bool>, origin: &BTreeMap<Term, (String, Option<String>, bool)>) -> Value {
    json!(assign
        .iter()
        .map(|(t, v)| match origin.get(t) {
            Some((text, at, pol)) => json!({"when": text, "holds": v == pol, "at": at, "atom": t.to_string()}),
            None => json!({"atom": t.to_string(), "holds": v}),
        })
        .collect::<Vec<_>>())
}

/// `changes commute with operations`。
pub fn commute(law: &Law, before: &Model, after: &Model, corr: &Corr, ctx: &Ctx, focus: &BTreeSet<String>) -> Vec<Finding> {
    let m = law.about.as_deref().unwrap_or_default();
    let name = law.name.as_str();
    let fields: BTreeSet<String> = before.meanings().filter(|a| a.meaning.as_deref() == Some(m) && before.is_field(&a.subject)).map(|a| a.subject.clone()).collect();
    let mut out = Vec::new();
    for f in &fields {
        if corr.images(f).is_empty() {
            let mut r = Finding::new("change", Some(name), f).fails("missing");
            r.at = before.defines.get(f).and_then(|d| d.at.clone()).into_iter().collect();
            r.check = json!({"element": f, "corresponds": []});
            r.theory = vec!["Rising Sea §1.8〜1.9".to_string()];
            out.push(r);
        }
    }
    let ex_a = Exec { model: before, side: Side::Before, corr, ctx };
    let ex_b = Exec { model: after, side: Side::After, corr, ctx };
    let mut compared = 0;
    for f in before.operations() {
        for g in corr.images(f).iter().filter(|g| after.is_operation(g)) {
            compared += 1;
            let touched = focus.contains(g) || focus.contains(f);
            let (a, b) = match (ex_a.run(f), ex_b.run(g)) {
                (Ok(a), Ok(b)) => (a, b),
                (Err(s), _) | (_, Err(s)) => {
                    if touched {
                        let mut r = Finding::new("change", Some(name), g).silent(s.reason);
                        r.at = s.at.into_iter().collect();
                        r.check = json!({"detail": s.detail});
                        r.next = s.next;
                        out.push(r);
                    }
                    continue;
                }
            };
            let pairs: Vec<(String, String)> = fields
                .iter()
                .flat_map(|fld| corr.images(fld).iter().map(move |img| (fld.clone(), img.clone())))
                .collect();
            let written = |fld: &str, img: &str| {
                a.iter().any(|x| x.trace.iter().any(|w| w.key == fld)) || b.iter().any(|x| x.trace.iter().any(|w| w.key == ex_b.key(img)))
            };
            let pairs: Vec<(String, String)> = pairs.into_iter().filter(|(fld, img)| written(fld, img)).collect();
            if pairs.is_empty() {
                continue;
            }
            let mut branches = Vec::new();
            let mut counter = Vec::new();
            let mut unknown = false;
            for x in &a {
                for y in &b {
                    if !consistent(&x.assign, &y.assign) {
                        continue;
                    }
                    let mut assign = x.assign.clone();
                    assign.extend(y.assign.clone());
                    let mut origin = y.origin.clone();
                    origin.extend(x.origin.clone());
                    let mut values = serde_json::Map::new();
                    for (fld, img) in &pairs {
                        let va = x.state.get(fld).cloned().unwrap_or_else(|| Term::Input(fld.clone()));
                        let vb = ex_b.read(y, img);
                        if va.has_unknown() || vb.has_unknown() {
                            unknown = true;
                        }
                        if va != vb {
                            counter.push((branch_json(&assign, &origin), img.clone(), fld.clone(), va.clone(), vb.clone(), x.clone(), y.clone()));
                        }
                        values.insert(img.clone(), json!({"operate_then_migrate": va.to_string(), "migrate_then_operate": vb.to_string()}));
                    }
                    branches.push(json!({"conditions": branch_json(&assign, &origin), "values": values}));
                }
            }
            let op_at = after.defines.get(g).and_then(|d| d.at.clone());
            let mut r = Finding::new("change", Some(name), g);
            r.conditions = CONDITIONS.iter().map(|s| s.to_string()).collect();
            r.theory = vec!["Rising Sea §1.8〜1.9".to_string(), "Rising Sea §4.10〜4.11".to_string()];
            r.basis = vec![json!({"law": name, "before": f, "after": g})];
            if unknown {
                r = r.silent("unresolved");
                r.check = json!({"detail": "比べる値に ? がある"});
            } else if let Some((assign, img, fld, va, vb, x, y)) = counter.first() {
                r = r.fails("counterexample");
                let origin = |t: &[Written], key: &str| t.iter().rev().find(|w| w.key == key).and_then(|w| w.at.clone());
                let oa = origin(&x.trace, fld);
                let ob = origin(&y.trace, &ex_b.key(img));
                r.at = oa.iter().chain(ob.iter()).cloned().collect();
                r.check = json!({
                    "input": assign,
                    "field": img,
                    "operate_then_migrate": {"writes": trace_json(&x.trace), "value": va.to_string(), "last_write": oa},
                    "migrate_then_operate": {"writes": trace_json(&y.trace), "value": vb.to_string(), "last_write": ob},
                    "failing_branches": counter.len(),
                    "branches": branches.len(),
                });
            } else {
                r = r.holds();
                r.at = op_at.into_iter().collect();
                r.check = json!({"branches": branches});
            }
            out.push(r);
        }
    }
    if out.is_empty() {
        let mut r = Finding::new("change", Some(name), name).holds();
        r.check = json!({"operations_compared": compared, "fields": fields, "note": "対応する操作のどれも、about の意味を持つフィールドを書かない"});
        r.conditions = CONDITIONS.iter().map(|s| s.to_string()).collect();
        out.push(r);
    }
    out
}

/// `changes keep`。`transferred` は、変更後の意味を対応で移したもの(候補の検査)か。
pub fn keep(law: &Law, before: &Model, after: &Model, corr: &Corr, transferred: bool) -> Vec<Finding> {
    let m = law.about.as_deref().unwrap_or_default();
    let name = law.name.as_str();
    let mut out = Vec::new();
    let mut kept = Vec::new();
    let elements: BTreeSet<String> = before.meanings().filter(|a| a.meaning.as_deref() == Some(m) && !a.subject.starts_with("local:")).map(|a| a.subject.clone()).collect();
    for e in &elements {
        let images = corr.images(e);
        if images.is_empty() {
            let mut r = Finding::new("change", Some(name), e).fails("missing");
            r.at = before.defines.get(e).and_then(|d| d.at.clone()).into_iter().collect();
            r.check = json!({"element": e, "corresponds": []});
            out.push(r);
            continue;
        }
        for img in images {
            if after.has_meaning(img, m) {
                kept.push(json!({"before": e, "after": img}));
                continue;
            }
            let src = after.source_of(img);
            let read = src.as_ref().is_some_and(|s| after.read_meaning.get(m).is_some_and(|r| r.contains(s)));
            if transferred || read {
                let mut r = Finding::new("change", Some(name), img).fails("missing");
                r.check = json!({"before": e, "after": img, "meaning": m, "detail": "対応する要素が同じ意味を持たない"});
                out.push(r);
            } else {
                let mut r = Finding::new("change", Some(name), img).silent("unread");
                r.next = src.into_iter().map(|s| (s, format!("meaning:{m}"))).collect();
                r.check = json!({"before": e, "after": img, "meaning": m});
                out.push(r);
            }
        }
    }
    if out.is_empty() {
        let mut r = Finding::new("change", Some(name), name).holds();
        r.check = json!({"kept": kept});
        out.push(r);
    }
    for r in &mut out {
        r.theory = vec!["Rising Sea §1.8〜1.9".to_string()];
    }
    out
}

/// 候補が書き直していない操作が、`removes` した要素を使っていれば挙げる。
pub fn missing_uses(ov: &Overlay) -> Vec<Finding> {
    let mut uses: BTreeMap<String, Vec<(String, Atom)>> = BTreeMap::new();
    for a in ov.atoms.iter().filter(|a| a.is_structure() && !a.is_plan_at()) {
        let mut names: Vec<String> = a.object.iter().cloned().collect();
        if let Some(p) = &a.params {
            names.extend(p.values().cloned());
        }
        names.extend(a.ty.iter().cloned());
        for n in names.into_iter().filter(|n| is_removed(&ov.removed, n)) {
            let owner = a.subject.split("->").next().unwrap_or(&a.subject);
            let owner = owner.split(".$").next().unwrap_or(owner).to_string();
            uses.entry(owner).or_default().push((n, a.clone()));
        }
    }
    uses.into_iter()
        .map(|(op, list)| {
            let mut r = Finding::new("change", None, &op).fails("missing");
            r.at = list.iter().filter_map(|(_, a)| a.at.clone()).collect();
            r.basis = list.iter().map(|(_, a)| serde_json::to_value(a).unwrap()).collect();
            r.check = json!({"uses_removed": list.iter().map(|(n, _)| n.clone()).collect::<BTreeSet<_>>(), "detail": "候補が書き直していない要素が、消える要素を使う"});
            r
        })
        .collect()
}
