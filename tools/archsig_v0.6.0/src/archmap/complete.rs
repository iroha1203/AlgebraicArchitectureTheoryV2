//! 依存参照・Map の全域性と、欠測 slot の補完の存在(入力仕様 §5)。
//!
//! 欠測した参照 slot を、型の合う登録 subject から選ぶ有限の変数とする。既知値だけで
//! 破れる条件も、どの補完でも満たせない条件も `inconsistent_observation` とする。
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
    law: &'a CheckedLaw,
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

    /// 欠測 slot の変数のうち、族の所属を決めるもの。
    fn family_vars(&self, holder: usize, family: &Family, out: &mut Vec<usize>) {
        if let Family::Owned { param, .. } = family {
            if let Some(RefSrc::Var(v)) = self.slot_ref(holder, *param) {
                out.push(v);
            }
            for &x in self.candidates(family) {
                self.owner_var(x, out);
            }
        }
    }

    fn owner_var(&self, x: usize, out: &mut Vec<usize>) {
        if let Some(f) = self.owner_field[x]
            && let Some(RefSrc::Var(v)) = self.slot_ref(x, f)
        {
            out.push(v);
        }
    }

    fn type_vars(&self, holder: usize, ty: &Type, out: &mut Vec<usize>) {
        match ty {
            Type::Ref(_) | Type::Owned(..) => {
                if let Some(f) = self.family_of(holder, ty) {
                    self.family_vars(holder, &f, out);
                }
            }
            Type::Map(a, b) => {
                self.type_vars(holder, a, out);
                self.type_vars(holder, b, out);
            }
            Type::Tuple(items) => items.iter().for_each(|t| self.type_vars(holder, t, out)),
            _ => {}
        }
    }

    /// 条件の真偽が依存する変数。
    fn vars_of(&self, c: &Cons) -> Vec<usize> {
        let mut out = Vec::new();
        match c {
            Cons::Member {
                holder,
                family,
                target,
                ..
            } => {
                match target {
                    // 既知の参照先では、その所属だけが効く。
                    RefSrc::Known(t) => {
                        if let Family::Owned { param, .. } = family
                            && let Some(RefSrc::Var(v)) = self.slot_ref(*holder, *param)
                        {
                            out.push(v);
                        }
                        self.owner_var(*t, &mut out);
                    }
                    RefSrc::Var(v) => {
                        out.push(*v);
                        self.family_vars(*holder, family, &mut out);
                    }
                }
            }
            Cons::Cover { holder, family, .. } => self.family_vars(*holder, family, &mut out),
            Cons::Inhabit { holder, ty, .. } => self.type_vars(*holder, ty, &mut out),
        }
        out.sort_unstable();
        out.dedup();
        out
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
        (Type::Data(d), Value::Data { constructor, args }) => {
            let Signature::Data { constructors } = &m.law.declarations[d].signature else {
                unreachable!("data 型は Law の宣言")
            };
            let tag = &constructor[d.len() + 1..];
            let c = constructors
                .iter()
                .find(|c| c.name == tag)
                .expect("検査済みの constructor");
            for (i, (t, v)) in c.args.iter().zip(args).enumerate() {
                collect_known(m, holder, t, v, &format!("{pointer}/args/{i}"), out);
            }
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
        law,
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
    if feasible(&m, &cons) {
        return Ok(());
    }
    // 入力順に条件を足していき、初めて補完が無くなる条件を位置とする。
    let (mut lo, mut hi) = (0, cons.len());
    while hi - lo > 1 {
        let mid = (lo + hi) / 2;
        if feasible(&m, &cons[..mid]) {
            lo = mid;
        } else {
            hi = mid;
        }
    }
    Err(issue(
        Code::InconsistentObservation,
        cons[hi - 1].pointer(),
        "既知の値・参照・所属を保つ補完が一つもない",
    ))
}

/// 条件と、その真偽が依存する変数の組。
type Group<'a> = Vec<(&'a Cons, Vec<usize>)>;

/// 条件のすべてを満たす補完があるか。欠測 slot を共有する条件の組ごとに、
/// その組の変数だけで探す。
fn feasible(m: &Model<'_>, cons: &[Cons]) -> bool {
    let empty = vec![None; m.vars.len()];
    let mut open: Vec<(&Cons, Vec<usize>)> = Vec::new();
    for c in cons {
        match m.eval(c, &empty) {
            Some(false) => return false,
            Some(true) => {}
            None => open.push((c, m.vars_of(c))),
        }
    }
    let mut parent: Vec<usize> = (0..m.vars.len()).collect();
    fn find(parent: &mut [usize], mut v: usize) -> usize {
        while parent[v] != v {
            parent[v] = parent[parent[v]];
            v = parent[v];
        }
        v
    }
    for (_, vs) in &open {
        for w in vs.iter().skip(1) {
            let (a, b) = (find(&mut parent, vs[0]), find(&mut parent, *w));
            parent[a] = b;
        }
    }
    let mut groups: Vec<(usize, Group<'_>)> = Vec::new();
    for (c, vs) in open {
        let root = find(&mut parent, vs[0]);
        match groups.iter_mut().find(|(r, _)| *r == root) {
            Some((_, g)) => g.push((c, vs)),
            None => groups.push((root, vec![(c, vs)])),
        }
    }
    let mut assign = empty;
    groups
        .iter()
        .all(|(_, group)| search(m, group, &mut assign))
}

/// 組の変数へ候補を置き、組の全条件を満たす補完を探す。未定の変数が最も少ない条件の変数から、
/// 条件を多く満たす候補を先に置く。全条件が真に決まれば、残りの変数はどの候補でもよい。
fn search(m: &Model<'_>, cons: &[(&Cons, Vec<usize>)], assign: &mut Vec<Option<usize>>) -> bool {
    stacker::maybe_grow(128 * 1024, 4 * 1024 * 1024, || {
        let mut next: Option<(usize, usize)> = None;
        for (c, vs) in cons {
            match m.eval(c, assign) {
                Some(false) => return false,
                Some(true) => {}
                None => {
                    let free: Vec<usize> = vs
                        .iter()
                        .copied()
                        .filter(|&v| assign[v].is_none())
                        .collect();
                    debug_assert!(!free.is_empty(), "未定の条件は未定の変数を持つ");
                    if let Some(&v) = free.first()
                        && next.is_none_or(|(n, _)| free.len() < n)
                    {
                        next = Some((free.len(), v));
                    }
                }
            }
        }
        let Some((_, v)) = next else {
            return true;
        };
        // 破る条件のない候補を、真に決まる条件の多い順に置く。
        let mut order: Vec<(usize, usize)> = Vec::new();
        for &x in &m.vars[v].2 {
            assign[v] = Some(x);
            let mut decided = 0;
            let mut broken = false;
            for (c, _) in cons.iter().filter(|(_, vs)| vs.binary_search(&v).is_ok()) {
                match m.eval(c, assign) {
                    Some(true) => decided += 1,
                    Some(false) => {
                        broken = true;
                        break;
                    }
                    None => {}
                }
            }
            if !broken {
                order.push((decided, x));
            }
        }
        order.sort_by_key(|&(decided, _)| std::cmp::Reverse(decided));
        for (_, x) in order {
            assign[v] = Some(x);
            if search(m, cons, assign) {
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
            // 始域が空なら空の Map がある。
            Type::Map(a, b) => !inh(a, ok, by_type) || inh(b, ok, by_type),
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
