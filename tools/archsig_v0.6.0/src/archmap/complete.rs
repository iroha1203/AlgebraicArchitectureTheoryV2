//! 依存参照・Map の全域性と、欠測 slot の補完の存在(入力仕様 §5)。
//!
//! 欠測した参照 slot を、型の合う登録 subject から選ぶ有限の変数とする。既知値だけで
//! 破れる条件は不正な参照、どの補完でも満たせない条件は `inconsistent_observation` とする。
//! Law の成立は補完の条件に使わない。

use super::*;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum RefSrc {
    Known(usize),
    Var(usize),
}

#[derive(Clone, Debug)]
enum Family {
    /// `E[p]`: holder の parameter p が指す subject に所属する E。
    Owned { entity: String, param: usize },
    /// `E`: 全 snapshot の登録 E。
    All(String),
}

#[derive(Clone, Debug)]
enum Cons {
    /// target が holder の parameter の族に属する。
    Member {
        holder: usize,
        family: Family,
        target: RefSrc,
        pointer: String,
    },
    /// 既知の Map の key 集合が始域の族と一致する。
    Cover {
        holder: usize,
        family: Family,
        keys: Vec<usize>,
        pointer: String,
    },
    /// 欠測 slot に型の値を置ける。
    Inhabit {
        holder: usize,
        ty: Type,
        pointer: String,
    },
}

impl Cons {
    fn pointer(&self) -> &str {
        match self {
            Cons::Member { pointer, .. }
            | Cons::Cover { pointer, .. }
            | Cons::Inhabit { pointer, .. } => pointer,
        }
    }
}

struct Model<'a> {
    subjects: Vec<&'a Subject>,
    index: HashMap<(&'a str, &'a str), usize>,
    by_type: HashMap<&'a str, Vec<usize>>,
    owner_field: Vec<Option<usize>>,
    /// 欠測した参照 slot ごとの変数 (subject, field) と候補。
    vars: Vec<(usize, usize, Vec<usize>)>,
    var_index: HashMap<(usize, usize), usize>,
    data_inhabited: HashMap<String, bool>,
}

fn and3(a: Option<bool>, b: Option<bool>) -> Option<bool> {
    match (a, b) {
        (Some(false), _) | (_, Some(false)) => Some(false),
        (Some(true), Some(true)) => Some(true),
        _ => None,
    }
}

fn or3(a: Option<bool>, b: Option<bool>) -> Option<bool> {
    match (a, b) {
        (Some(true), _) | (_, Some(true)) => Some(true),
        (Some(false), Some(false)) => Some(false),
        _ => None,
    }
}

impl<'a> Model<'a> {
    fn field_index(&self, g: usize, name: &str) -> usize {
        self.subjects[g]
            .fields
            .iter()
            .position(|f| f.name.rsplit('.').next() == Some(name))
            .expect("宣言済みの field")
    }

    fn slot_ref(&self, g: usize, f: usize) -> Option<RefSrc> {
        match &self.subjects[g].fields[f].slot {
            Slot::Known { value, .. } => {
                let (s, id) = value.as_ref()?;
                Some(RefSrc::Known(self.index[&(s, id)]))
            }
            Slot::Missing => self.var_index.get(&(g, f)).map(|v| RefSrc::Var(*v)),
        }
    }

    fn resolve(&self, r: RefSrc, assign: &[Option<usize>]) -> Option<usize> {
        match r {
            RefSrc::Known(g) => Some(g),
            RefSrc::Var(v) => assign[v],
        }
    }

    /// x の所属先。所属を持たない型は Some(None)、未定は None。
    fn owner(&self, x: usize, assign: &[Option<usize>]) -> Option<Option<usize>> {
        match self.owner_field[x] {
            None => Some(None),
            Some(f) => match self.slot_ref(x, f) {
                Some(r) => self.resolve(r, assign).map(Some),
                None => Some(None),
            },
        }
    }

    /// 族の根。Owned では holder の parameter の値。
    fn family_root(
        &self,
        holder: usize,
        family: &Family,
        assign: &[Option<usize>],
    ) -> Option<Option<usize>> {
        match family {
            Family::All(_) => Some(None),
            Family::Owned { param, .. } => {
                let r = self.slot_ref(holder, *param)?;
                self.resolve(r, assign).map(Some)
            }
        }
    }

    /// x が族に属するか。
    fn member(
        &self,
        x: usize,
        holder: usize,
        family: &Family,
        assign: &[Option<usize>],
    ) -> Option<bool> {
        match family {
            Family::All(e) => Some(self.subjects[x].ty == *e),
            Family::Owned { entity, .. } => {
                if self.subjects[x].ty != *entity {
                    return Some(false);
                }
                let root = self.family_root(holder, family, assign)??;
                if self.subjects[x].snapshot != self.subjects[root].snapshot {
                    return Some(false);
                }
                Some(self.owner(x, assign)? == Some(root))
            }
        }
    }

    fn candidates(&self, family: &Family) -> &[usize] {
        let e = match family {
            Family::All(e) | Family::Owned { entity: e, .. } => e,
        };
        self.by_type.get(e.as_str()).map_or(&[], Vec::as_slice)
    }

    fn nonempty(&self, holder: usize, family: &Family, assign: &[Option<usize>]) -> Option<bool> {
        let mut out = Some(false);
        for &x in self.candidates(family) {
            out = or3(out, self.member(x, holder, family, assign));
        }
        out
    }

    fn family_of(&self, holder: usize, ty: &Type) -> Option<Family> {
        match ty {
            Type::Owned(e, p) => Some(Family::Owned {
                entity: e.clone(),
                param: self.field_index(holder, p),
            }),
            Type::Ref(e) => Some(Family::All(e.clone())),
            _ => None,
        }
    }

    fn inhabited(&self, holder: usize, ty: &Type, assign: &[Option<usize>]) -> Option<bool> {
        match ty {
            Type::Ref(_) | Type::Owned(..) => {
                self.nonempty(holder, &self.family_of(holder, ty)?, assign)
            }
            Type::Map(a, b) => {
                let fa = self.family_of(holder, a)?;
                let fb = self.family_of(holder, b)?;
                let empty_a = self.nonempty(holder, &fa, assign).map(|n| !n);
                or3(empty_a, self.nonempty(holder, &fb, assign))
            }
            Type::Tuple(items) => {
                // 三値の連言。未定(None)の成分があっても、偽の成分があれば偽とする。
                let mut acc = Some(true);
                for t in items {
                    acc = and3(acc, self.inhabited(holder, t, assign));
                }
                acc
            }
            Type::Data(d) => Some(self.data_inhabited.get(d).copied().unwrap_or(true)),
            _ => Some(true),
        }
    }

    fn eval(&self, c: &Cons, assign: &[Option<usize>]) -> Option<bool> {
        match c {
            Cons::Member {
                holder,
                family,
                target,
                ..
            } => {
                let t = self.resolve(*target, assign)?;
                self.member(t, *holder, family, assign)
            }
            Cons::Cover {
                holder,
                family,
                keys,
                ..
            } => {
                let mut out = Some(true);
                for &k in keys {
                    out = and3(out, self.member(k, *holder, family, assign));
                }
                for &x in self.candidates(family) {
                    if !keys.contains(&x) {
                        out = and3(out, self.member(x, *holder, family, assign).map(|m| !m));
                    }
                }
                out
            }
            Cons::Inhabit { holder, ty, .. } => self.inhabited(*holder, ty, assign),
        }
    }
}

/// 既知値の中の依存参照と Map を、holder の parameter に対する条件として集める。
fn collect_known(
    m: &Model<'_>,
    holder: usize,
    ty: &Type,
    v: &Value,
    pointer: &str,
    out: &mut Vec<Cons>,
) {
    stacker::maybe_grow(128 * 1024, 4 * 1024 * 1024, || {
        collect_known_inner(m, holder, ty, v, pointer, out)
    })
}

fn collect_known_inner(
    m: &Model<'_>,
    holder: usize,
    ty: &Type,
    v: &Value,
    pointer: &str,
    out: &mut Vec<Cons>,
) {
    match (ty, v) {
        (Type::Owned(..), Value::Ref { snapshot, subject }) => {
            let target = RefSrc::Known(m.index[&(snapshot.as_str(), subject.as_str())]);
            let family = m.family_of(holder, ty).expect("依存参照");
            out.push(Cons::Member {
                holder,
                family,
                target,
                pointer: pointer.to_owned(),
            });
        }
        (Type::Tuple(ts), Value::Tuple(vs)) => {
            for (i, (t, v)) in ts.iter().zip(vs).enumerate() {
                collect_known(m, holder, t, v, &format!("{pointer}/{i}"), out);
            }
        }
        (Type::List(t) | Type::Set(t), Value::List(vs) | Value::Set(vs)) => {
            for (i, v) in vs.iter().enumerate() {
                collect_known(m, holder, t, v, &format!("{pointer}/{i}"), out);
            }
        }
        (Type::Option(t), Value::Option(Some(v))) => {
            collect_known(m, holder, t, v, &format!("{pointer}/some"), out)
        }
        (Type::Map(a, b), Value::Map(pairs)) => {
            let keys = pairs
                .iter()
                .map(|(k, _)| {
                    let (s, id) = k.as_ref().expect("Map の key は参照");
                    m.index[&(s, id)]
                })
                .collect();
            out.push(Cons::Cover {
                holder,
                family: m.family_of(holder, a).expect("参照型"),
                keys,
                pointer: pointer.to_owned(),
            });
            for (i, (_, v)) in pairs.iter().enumerate() {
                collect_known(m, holder, b, v, &format!("{pointer}/{i}/1"), out);
            }
        }
        _ => {}
    }
}

fn has_reference(ty: &Type) -> bool {
    ty.clone().any(&mut |t| {
        matches!(
            t,
            Type::Ref(_) | Type::Owned(..) | Type::Map(..) | Type::Data(_)
        )
    })
}

pub(crate) fn check_completion(snapshots: &[Snapshot], law: &CheckedLaw) -> AResult<()> {
    let subjects: Vec<&Subject> = snapshots.iter().flat_map(|s| s.subjects.iter()).collect();
    let mut index = HashMap::new();
    let mut by_type: HashMap<&str, Vec<usize>> = HashMap::new();
    for (g, s) in subjects.iter().enumerate() {
        index.insert((s.snapshot.as_str(), s.id.as_str()), g);
        by_type.entry(s.ty.as_str()).or_default().push(g);
    }
    let owner_field = subjects
        .iter()
        .map(|s| match law.declarations[&s.ty].signature {
            Signature::Entity { .. } | Signature::Arrow { .. } => s
                .fields
                .iter()
                .position(|f| f.name.rsplit('.').next() == Some("owner")),
            _ => None,
        })
        .collect();
    let data_inhabited = data_inhabitation(law, &by_type);
    let mut m = Model {
        subjects,
        index,
        by_type,
        owner_field,
        vars: Vec::new(),
        var_index: HashMap::new(),
        data_inhabited,
    };
    for g in 0..m.subjects.len() {
        for (f, field) in m.subjects[g].fields.iter().enumerate() {
            if field.slot == Slot::Missing
                && let Type::Ref(e) | Type::Owned(e, _) = &field.ty
            {
                let domain = m.by_type.get(e.as_str()).cloned().unwrap_or_default();
                m.var_index.insert((g, f), m.vars.len());
                m.vars.push((g, f, domain));
            }
        }
    }
    let mut cons = Vec::new();
    for g in 0..m.subjects.len() {
        let s = m.subjects[g];
        for (f, field) in s.fields.iter().enumerate() {
            match &field.slot {
                Slot::Known { value, pointer, .. } => {
                    collect_known(&m, g, &field.ty, value, pointer, &mut cons)
                }
                Slot::Missing => {
                    let pointer = s.pointer.clone();
                    if let Some(&v) = m.var_index.get(&(g, f)) {
                        if let Type::Owned(..) = field.ty {
                            let family = m.family_of(g, &field.ty).expect("依存参照");
                            cons.push(Cons::Member {
                                holder: g,
                                family,
                                target: RefSrc::Var(v),
                                pointer: pointer.clone(),
                            });
                        }
                        cons.push(Cons::Inhabit {
                            holder: g,
                            ty: field.ty.clone(),
                            pointer,
                        });
                    } else if has_reference(&field.ty) {
                        cons.push(Cons::Inhabit {
                            holder: g,
                            ty: field.ty.clone(),
                            pointer,
                        });
                    }
                }
            }
        }
    }
    let empty = vec![None; m.vars.len()];
    for c in &cons {
        if m.eval(c, &empty) == Some(false) {
            return Err(match c {
                Cons::Member { .. } => issue(
                    Code::Reference,
                    c.pointer(),
                    "参照先が依存型の所属先に属さない",
                ),
                Cons::Cover { .. } => issue(
                    Code::Reference,
                    c.pointer(),
                    "Map の key が始域の族をちょうど覆わない",
                ),
                Cons::Inhabit { .. } => issue(
                    Code::InconsistentObservation,
                    c.pointer(),
                    "欠測 field に置ける型の値がない",
                ),
            });
        }
    }
    let open: Vec<&Cons> = cons
        .iter()
        .filter(|c| m.eval(c, &empty).is_none())
        .collect();
    if open.is_empty() {
        return Ok(());
    }
    let mut assign = empty;
    if search(&m, &open, &mut assign, 0) {
        Ok(())
    } else {
        Err(issue(
            Code::InconsistentObservation,
            open[0].pointer(),
            "既知の値・参照・所属を保つ補完が一つもない",
        ))
    }
}

/// 欠測した参照 slot へ候補を順に置き、全条件を満たす補完を探す。
fn search(m: &Model<'_>, cons: &[&Cons], assign: &mut Vec<Option<usize>>, v: usize) -> bool {
    stacker::maybe_grow(128 * 1024, 4 * 1024 * 1024, || {
        if cons.iter().any(|c| m.eval(c, assign) == Some(false)) {
            return false;
        }
        if v == m.vars.len() {
            return cons.iter().all(|c| m.eval(c, assign) == Some(true));
        }
        for &x in &m.vars[v].2 {
            assign[v] = Some(x);
            if search(m, cons, assign, v + 1) {
                return true;
            }
        }
        assign[v] = None;
        false
    })
}

/// data 型が、登録 subject を使って有限の値を持つか。参照の引数は登録 subject を要する。
fn data_inhabitation(
    law: &CheckedLaw,
    by_type: &HashMap<&str, Vec<usize>>,
) -> HashMap<String, bool> {
    let datas: Vec<(&String, &Vec<crate::law::model::CtorSig>)> = law
        .declarations
        .iter()
        .filter_map(|(n, d)| match &d.signature {
            Signature::Data { constructors } => Some((n, constructors)),
            _ => None,
        })
        .collect();
    let mut ok: HashMap<String, bool> = datas.iter().map(|(n, _)| ((*n).clone(), false)).collect();
    fn inh(t: &Type, ok: &HashMap<String, bool>, by_type: &HashMap<&str, Vec<usize>>) -> bool {
        match t {
            Type::Ref(e) | Type::Owned(e, _) => {
                by_type.get(e.as_str()).is_some_and(|v| !v.is_empty())
            }
            Type::Data(d) => ok.get(d).copied().unwrap_or(false),
            Type::Tuple(items) => items.iter().all(|t| inh(t, ok, by_type)),
            _ => true,
        }
    }
    loop {
        let mut changed = false;
        for (n, ctors) in &datas {
            if !ok[*n]
                && ctors
                    .iter()
                    .any(|c| c.args.iter().all(|t| inh(t, &ok, by_type)))
            {
                ok.insert((*n).clone(), true);
                changed = true;
            }
        }
        if !changed {
            return ok;
        }
    }
}
