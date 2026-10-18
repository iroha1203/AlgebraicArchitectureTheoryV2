//! 依存参照・Map の全域性と、欠測 slot の補完の存在(入力仕様 §5)。
//!
//! 欠測した参照 slot を、型の合う登録 subject から選ぶ有限の変数とする。既知値だけで
//! 破れる条件も、どの補完でも満たせない条件も `inconsistent_observation` とする。
//! Law の成立は補完の条件に使わない。

use super::*;
use crate::json::InputError;
use crate::observed::control::{Checkpoint, Control};

pub(crate) struct FieldAssignment {
    pub snapshot: String,
    pub subject: String,
    pub field: String,
    pub value: Json,
}

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

struct Model<'a, E> {
    subjects: Vec<&'a Subject>,
    index: HashMap<(&'a str, &'a str), usize>,
    by_type: HashMap<&'a str, Vec<usize>>,
    owner_field: Vec<Option<usize>>,
    /// 欠測した参照 slot ごとの変数 (subject, field) と候補。
    vars: Vec<(usize, usize, Vec<usize>)>,
    var_index: HashMap<(usize, usize), usize>,
    pinned: HashMap<(usize, usize), Value>,
    data_inhabited: HashMap<String, bool>,
    definitions: &'a CheckedDefinitions,
    control: Control,
    error: std::marker::PhantomData<fn() -> E>,
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

impl<'a, E: InputError> Model<'a, E> {
    fn checkpoint(&self) -> Result<(), E> {
        E::checkpoint(&mut self.control.clone(), Checkpoint::Completion)
    }

    /// 各意味検査の結果を採用する前にも、共有された停止を確認する。
    fn done<T>(&self, value: T) -> Result<T, E> {
        self.checkpoint()?;
        Ok(value)
    }

    /// 偽はこの代入に対する否定の根拠として先に返す。呼出し側が未検査候補を
    /// 続ける前、またはprefix全体の不整合を位置付きで返す前に停止を確認する。
    fn truth(&self, value: Option<bool>) -> Result<Option<bool>, E> {
        match self.checkpoint() {
            Err(stop) if value == Some(false) && stop.is_budget_stop() => Ok(value),
            Err(stop) => Err(stop),
            Ok(()) => Ok(value),
        }
    }

    fn decision(&self, value: bool) -> Result<bool, E> {
        match self.checkpoint() {
            Err(stop) if !value && stop.is_budget_stop() => Ok(value),
            Err(stop) => Err(stop),
            Ok(()) => Ok(value),
        }
    }

    fn field_index(&self, g: usize, name: &str) -> Result<usize, E> {
        self.checkpoint()?;
        for (i, f) in self.subjects[g].fields.iter().enumerate() {
            self.checkpoint()?;
            if f.name.rsplit('.').next() == Some(name) {
                return self.done(i);
            }
            self.checkpoint()?;
        }
        unreachable!("宣言済みの field")
    }

    fn slot_ref(&self, g: usize, f: usize) -> Result<Option<RefSrc>, E> {
        self.checkpoint()?;
        if let Some(value) = self.pinned.get(&(g, f)) {
            return self.done(
                value
                    .as_ref()
                    .map(|(snapshot, subject)| RefSrc::Known(self.index[&(snapshot, subject)])),
            );
        }
        let out = match &self.subjects[g].fields[f].slot {
            Slot::Known { value, .. } => value
                .as_ref()
                .map(|(s, id)| RefSrc::Known(self.index[&(s, id)])),
            Slot::Missing => self.var_index.get(&(g, f)).map(|v| RefSrc::Var(*v)),
        };
        self.done(out)
    }

    fn resolve(&self, r: RefSrc, assign: &[Option<usize>]) -> Result<Option<usize>, E> {
        self.checkpoint()?;
        self.done(match r {
            RefSrc::Known(g) => Some(g),
            RefSrc::Var(v) => assign[v],
        })
    }

    /// x の所属先。所属を持たない型は Some(None)、未定は None。
    fn owner(&self, x: usize, assign: &[Option<usize>]) -> Result<Option<Option<usize>>, E> {
        self.checkpoint()?;
        let out = match self.owner_field[x] {
            None => Some(None),
            Some(f) => match self.slot_ref(x, f)? {
                Some(r) => self.resolve(r, assign)?.map(Some),
                None => Some(None),
            },
        };
        self.done(out)
    }

    /// 族の根。Owned では holder の parameter の値。
    fn family_root(
        &self,
        holder: usize,
        family: &Family,
        assign: &[Option<usize>],
    ) -> Result<Option<Option<usize>>, E> {
        self.checkpoint()?;
        let out = match family {
            Family::All(_) => Some(None),
            Family::Owned { param, .. } => match self.slot_ref(holder, *param)? {
                Some(r) => self.resolve(r, assign)?.map(Some),
                None => None,
            },
        };
        self.done(out)
    }

    /// x が族に属するか。
    fn member(
        &self,
        x: usize,
        holder: usize,
        family: &Family,
        assign: &[Option<usize>],
    ) -> Result<Option<bool>, E> {
        self.checkpoint()?;
        let out = match family {
            Family::All(e) => Some(self.subjects[x].ty == *e),
            Family::Owned { entity, .. } => {
                if self.subjects[x].ty != *entity {
                    return self.truth(Some(false));
                }
                let Some(Some(root)) = self.family_root(holder, family, assign)? else {
                    return self.done(None);
                };
                if self.subjects[x].snapshot != self.subjects[root].snapshot {
                    return self.truth(Some(false));
                }
                self.owner(x, assign)?.map(|owner| owner == Some(root))
            }
        };
        self.truth(out)
    }

    fn candidates(&self, family: &Family) -> Result<&[usize], E> {
        self.checkpoint()?;
        let e = match family {
            Family::All(e) | Family::Owned { entity: e, .. } => e,
        };
        self.done(self.by_type.get(e.as_str()).map_or(&[], Vec::as_slice))
    }

    fn nonempty(
        &self,
        holder: usize,
        family: &Family,
        assign: &[Option<usize>],
    ) -> Result<Option<bool>, E> {
        self.checkpoint()?;
        let mut out = Some(false);
        for &x in self.candidates(family)? {
            self.checkpoint()?;
            out = or3(out, self.member(x, holder, family, assign)?);
            if out == Some(true) {
                return self.done(out);
            }
            if out.is_none() {
                self.checkpoint()?;
            }
        }
        self.truth(out)
    }

    fn family_of(&self, holder: usize, ty: &Type) -> Result<Option<Family>, E> {
        self.checkpoint()?;
        let out = match ty {
            Type::Owned(e, p) => Some(Family::Owned {
                entity: e.clone(),
                param: self.field_index(holder, p)?,
            }),
            Type::Ref(e) => Some(Family::All(e.clone())),
            _ => None,
        };
        self.done(out)
    }

    fn inhabited(
        &self,
        holder: usize,
        ty: &Type,
        assign: &[Option<usize>],
    ) -> Result<Option<bool>, E> {
        stacker::maybe_grow(128 * 1024, 4 * 1024 * 1024, || {
            self.checkpoint()?;
            let out = match ty {
                Type::Ref(_) | Type::Owned(..) => match self.family_of(holder, ty)? {
                    Some(family) => self.nonempty(holder, &family, assign)?,
                    None => None,
                },
                Type::Map(a, b) => {
                    let Some(fa) = self.family_of(holder, a)? else {
                        return self.done(None);
                    };
                    let Some(fb) = self.family_of(holder, b)? else {
                        return self.done(None);
                    };
                    let empty_a = self.nonempty(holder, &fa, assign)?.map(|n| !n);
                    or3(empty_a, self.nonempty(holder, &fb, assign)?)
                }
                Type::Tuple(items) => {
                    // 未定(None)の成分があっても、偽の成分があれば偽とする。
                    let mut acc = Some(true);
                    for t in items {
                        self.checkpoint()?;
                        acc = and3(acc, self.inhabited(holder, t, assign)?);
                        if acc == Some(false) {
                            return self.truth(acc);
                        }
                        self.checkpoint()?;
                    }
                    acc
                }
                Type::Data(d) => Some(self.data_inhabited.get(d).copied().unwrap_or(true)),
                _ => Some(true),
            };
            self.truth(out)
        })
    }

    /// 欠測 slot の変数のうち、族の所属を決めるもの。
    fn family_vars(&self, holder: usize, family: &Family, out: &mut Vec<usize>) -> Result<(), E> {
        self.checkpoint()?;
        if let Family::Owned { param, .. } = family {
            if let Some(RefSrc::Var(v)) = self.slot_ref(holder, *param)? {
                out.push(v);
            }
            for &x in self.candidates(family)? {
                self.checkpoint()?;
                self.owner_var(x, out)?;
                self.checkpoint()?;
            }
        }
        self.done(())
    }

    fn owner_var(&self, x: usize, out: &mut Vec<usize>) -> Result<(), E> {
        self.checkpoint()?;
        if let Some(f) = self.owner_field[x]
            && let Some(RefSrc::Var(v)) = self.slot_ref(x, f)?
        {
            out.push(v);
        }
        self.done(())
    }

    fn type_vars(&self, holder: usize, ty: &Type, out: &mut Vec<usize>) -> Result<(), E> {
        stacker::maybe_grow(128 * 1024, 4 * 1024 * 1024, || {
            self.checkpoint()?;
            match ty {
                Type::Ref(_) | Type::Owned(..) => {
                    if let Some(f) = self.family_of(holder, ty)? {
                        self.family_vars(holder, &f, out)?;
                    }
                }
                Type::Map(a, b) => {
                    self.type_vars(holder, a, out)?;
                    self.type_vars(holder, b, out)?;
                }
                Type::Tuple(items) => {
                    for t in items {
                        self.checkpoint()?;
                        self.type_vars(holder, t, out)?;
                        self.checkpoint()?;
                    }
                }
                _ => {}
            }
            self.done(())
        })
    }

    /// 条件の真偽が依存する変数。
    fn vars_of(&self, c: &Cons) -> Result<Vec<usize>, E> {
        self.checkpoint()?;
        let mut out = Vec::new();
        match c {
            Cons::Member {
                holder,
                family,
                target,
                ..
            } => match target {
                RefSrc::Known(t) => {
                    if let Family::Owned { param, .. } = family
                        && let Some(RefSrc::Var(v)) = self.slot_ref(*holder, *param)?
                    {
                        out.push(v);
                    }
                    self.owner_var(*t, &mut out)?;
                }
                RefSrc::Var(v) => {
                    out.push(*v);
                    self.family_vars(*holder, family, &mut out)?;
                }
            },
            Cons::Cover { holder, family, .. } => self.family_vars(*holder, family, &mut out)?,
            Cons::Inhabit { holder, ty, .. } => self.type_vars(*holder, ty, &mut out)?,
        }
        out.sort_unstable();
        self.checkpoint()?;
        out.dedup();
        self.done(out)
    }

    fn eval(&self, c: &Cons, assign: &[Option<usize>]) -> Result<Option<bool>, E> {
        self.checkpoint()?;
        let out = match c {
            Cons::Member {
                holder,
                family,
                target,
                ..
            } => match self.resolve(*target, assign)? {
                Some(t) => self.member(t, *holder, family, assign)?,
                None => None,
            },
            Cons::Cover {
                holder,
                family,
                keys,
                ..
            } => {
                let mut out = Some(true);
                for &k in keys {
                    self.checkpoint()?;
                    out = and3(out, self.member(k, *holder, family, assign)?);
                    if out == Some(false) {
                        return self.truth(out);
                    }
                    self.checkpoint()?;
                }
                for &x in self.candidates(family)? {
                    self.checkpoint()?;
                    if !keys.contains(&x) {
                        out = and3(out, self.member(x, *holder, family, assign)?.map(|m| !m));
                        if out == Some(false) {
                            return self.truth(out);
                        }
                    }
                    self.checkpoint()?;
                }
                out
            }
            Cons::Inhabit { holder, ty, .. } => self.inhabited(*holder, ty, assign)?,
        };
        self.truth(out)
    }
}

/// 既知値の中の依存参照と Map を、holder の parameter に対する条件として集める。
fn collect_known<E: InputError>(
    m: &Model<'_, E>,
    holder: usize,
    ty: &Type,
    v: &Value,
    pointer: &str,
    out: &mut Vec<Cons>,
) -> Result<(), E> {
    stacker::maybe_grow(128 * 1024, 4 * 1024 * 1024, || {
        m.checkpoint()?;
        collect_known_inner(m, holder, ty, v, pointer, out)?;
        m.done(())
    })
}

fn collect_known_inner<E: InputError>(
    m: &Model<'_, E>,
    holder: usize,
    ty: &Type,
    v: &Value,
    pointer: &str,
    out: &mut Vec<Cons>,
) -> Result<(), E> {
    m.checkpoint()?;
    match (ty, v) {
        (Type::Owned(..), Value::Ref { snapshot, subject }) => {
            let target = RefSrc::Known(m.index[&(snapshot.as_str(), subject.as_str())]);
            let family = m.family_of(holder, ty)?.expect("依存参照");
            out.push(Cons::Member {
                holder,
                family,
                target,
                pointer: pointer.to_owned(),
            });
        }
        (Type::Tuple(ts), Value::Tuple(vs)) => {
            for (i, (t, v)) in ts.iter().zip(vs).enumerate() {
                m.checkpoint()?;
                collect_known(m, holder, t, v, &format!("{pointer}/{i}"), out)?;
                m.checkpoint()?;
            }
        }
        (Type::List(t) | Type::Set(t), Value::List(vs) | Value::Set(vs)) => {
            for (i, v) in vs.iter().enumerate() {
                m.checkpoint()?;
                collect_known(m, holder, t, v, &format!("{pointer}/{i}"), out)?;
                m.checkpoint()?;
            }
        }
        (Type::Option(t), Value::Option(Some(v))) => {
            collect_known(m, holder, t, v, &format!("{pointer}/some"), out)?;
        }
        (Type::Data(d), Value::Data { constructor, args }) => {
            let PrimitiveSignature::Data { constructors } =
                &m.definitions.declarations[d].signature
            else {
                unreachable!("data 型は Law の宣言")
            };
            let tag = &constructor[d.len() + 1..];
            let mut selected = None;
            for c in constructors {
                m.checkpoint()?;
                if c.name == tag {
                    selected = Some(c);
                    break;
                }
                m.checkpoint()?;
            }
            m.checkpoint()?;
            let c = selected.expect("検査済みの constructor");
            for (i, (t, v)) in c.arguments.iter().zip(args).enumerate() {
                m.checkpoint()?;
                collect_known(m, holder, t, v, &format!("{pointer}/args/{i}"), out)?;
                m.checkpoint()?;
            }
        }
        (Type::Map(a, b), Value::Map(pairs)) => {
            let mut keys = Vec::new();
            for (k, _) in pairs {
                m.checkpoint()?;
                let (s, id) = k.as_ref().expect("Map の key は参照");
                keys.push(m.index[&(s, id)]);
                m.checkpoint()?;
            }
            out.push(Cons::Cover {
                holder,
                family: m.family_of(holder, a)?.expect("参照型"),
                keys,
                pointer: pointer.to_owned(),
            });
            for (i, (_, v)) in pairs.iter().enumerate() {
                m.checkpoint()?;
                collect_known(m, holder, b, v, &format!("{pointer}/{i}/1"), out)?;
                m.checkpoint()?;
            }
        }
        _ => {}
    }
    m.done(())
}

fn has_reference<E: InputError>(m: &Model<'_, E>, ty: &Type) -> Result<bool, E> {
    stacker::maybe_grow(128 * 1024, 4 * 1024 * 1024, || {
        m.checkpoint()?;
        let out = match ty {
            Type::Ref(_) | Type::Owned(..) | Type::Map(..) | Type::Data(_) => true,
            Type::Tuple(items) => {
                let mut found = false;
                for t in items {
                    m.checkpoint()?;
                    if has_reference(m, t)? {
                        found = true;
                        break;
                    }
                    m.checkpoint()?;
                }
                found
            }
            Type::List(t) | Type::Set(t) | Type::Option(t) => has_reference(m, t)?,
            Type::Term(args, ret) => {
                let mut found = false;
                for t in args {
                    m.checkpoint()?;
                    if has_reference(m, t)? {
                        found = true;
                        break;
                    }
                    m.checkpoint()?;
                }
                m.checkpoint()?;
                found || has_reference(m, ret)?
            }
            _ => false,
        };
        m.done(out)
    })
}

pub(crate) fn check_completion<E: InputError>(
    snapshots: &[Snapshot],
    definitions: &CheckedDefinitions,
    control: &mut Control,
) -> Result<(), E> {
    check_completion_with_values::<E>(snapshots, definitions, &[], control)
}

/// 元欠測slotへ置いた型付き値が、既知Map/ownerを保つ補完へ拡張できるかを検査する。
/// 入力表やLawの真偽を変更せず、通常の存在検査と同じ制約を使う。
pub(crate) fn check_completion_with_values<E: InputError>(
    snapshots: &[Snapshot],
    definitions: &CheckedDefinitions,
    pinned: &[FieldAssignment],
    control: &mut Control,
) -> Result<(), E> {
    E::checkpoint(control, Checkpoint::Completion)?;
    let mut subjects = Vec::new();
    for snapshot in snapshots {
        E::checkpoint(control, Checkpoint::Completion)?;
        for subject in &snapshot.subjects {
            E::checkpoint(control, Checkpoint::Completion)?;
            subjects.push(subject);
            E::checkpoint(control, Checkpoint::Completion)?;
        }
        E::checkpoint(control, Checkpoint::Completion)?;
    }
    let mut index = HashMap::new();
    let mut by_type: HashMap<&str, Vec<usize>> = HashMap::new();
    for (g, s) in subjects.iter().enumerate() {
        E::checkpoint(control, Checkpoint::Completion)?;
        index.insert((s.snapshot.as_str(), s.id.as_str()), g);
        by_type.entry(s.ty.as_str()).or_default().push(g);
        E::checkpoint(control, Checkpoint::Completion)?;
    }
    let roster = value::Roster {
        types: subjects
            .iter()
            .map(|s| ((s.snapshot.as_str(), s.id.as_str()), s.ty.as_str()))
            .collect(),
    };
    let mut owner_field = Vec::new();
    for s in &subjects {
        E::checkpoint(control, Checkpoint::Completion)?;
        let mut owner = None;
        if matches!(
            definitions.declarations[&s.ty].signature,
            PrimitiveSignature::Entity { .. } | PrimitiveSignature::Arrow { .. }
        ) {
            for (f, field) in s.fields.iter().enumerate() {
                E::checkpoint(control, Checkpoint::Completion)?;
                if field.name.rsplit('.').next() == Some("owner") {
                    owner = Some(f);
                    break;
                }
                E::checkpoint(control, Checkpoint::Completion)?;
            }
        }
        owner_field.push(owner);
        E::checkpoint(control, Checkpoint::Completion)?;
    }
    let data_inhabited = data_inhabitation::<E>(definitions, &by_type, control)?;
    let mut m = Model::<E> {
        subjects,
        index,
        by_type,
        owner_field,
        vars: Vec::new(),
        var_index: HashMap::new(),
        pinned: HashMap::new(),
        data_inhabited,
        definitions,
        control: control.clone(),
        error: std::marker::PhantomData,
    };
    for assignment in pinned {
        m.checkpoint()?;
        let fail = || issue(Code::Reference, "", "補完値が元の欠測slotと違う");
        let Some(&g) = m
            .index
            .get(&(assignment.snapshot.as_str(), assignment.subject.as_str()))
        else {
            return Err(fail().into());
        };
        let mut selected = None;
        for (index, field) in m.subjects[g].fields.iter().enumerate() {
            m.checkpoint()?;
            if field.name == assignment.field {
                selected = Some((index, field));
                break;
            }
            m.checkpoint()?;
        }
        let Some((f, field)) = selected else {
            return Err(fail().into());
        };
        if field.slot != Slot::Missing || m.pinned.contains_key(&(g, f)) {
            return Err(fail().into());
        }
        let namespace = m.subjects[g]
            .ty
            .rsplit_once('.')
            .map_or("", |(namespace, _)| namespace);
        let value = value::check_assignment::<E>(
            &assignment.value,
            &field.ty,
            definitions,
            &roster,
            namespace,
            control,
        )?;
        m.pinned.insert((g, f), value);
        m.checkpoint()?;
    }
    for g in 0..m.subjects.len() {
        m.checkpoint()?;
        for (f, field) in m.subjects[g].fields.iter().enumerate() {
            m.checkpoint()?;
            if field.slot == Slot::Missing
                && !m.pinned.contains_key(&(g, f))
                && let Type::Ref(e) | Type::Owned(e, _) = &field.ty
            {
                let domain = m.by_type.get(e.as_str()).cloned().unwrap_or_default();
                m.var_index.insert((g, f), m.vars.len());
                m.vars.push((g, f, domain));
            }
            m.checkpoint()?;
        }
        m.checkpoint()?;
    }
    let mut cons = Vec::new();
    for g in 0..m.subjects.len() {
        m.checkpoint()?;
        let s = m.subjects[g];
        for (f, field) in s.fields.iter().enumerate() {
            m.checkpoint()?;
            if let Some(value) = m.pinned.get(&(g, f)) {
                collect_known(&m, g, &field.ty, value, &s.pointer, &mut cons)?;
                m.checkpoint()?;
                continue;
            }
            match &field.slot {
                Slot::Known { value, pointer, .. } => {
                    collect_known(&m, g, &field.ty, value, pointer, &mut cons)?
                }
                Slot::Missing => {
                    let pointer = s.pointer.clone();
                    if let Some(&v) = m.var_index.get(&(g, f)) {
                        if let Type::Owned(..) = field.ty {
                            let family = m.family_of(g, &field.ty)?.expect("依存参照");
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
                    } else if has_reference(&m, &field.ty)? {
                        cons.push(Cons::Inhabit {
                            holder: g,
                            ty: field.ty.clone(),
                            pointer,
                        });
                    }
                }
            }
            m.checkpoint()?;
        }
        m.checkpoint()?;
    }
    // subject順・field宣言順に条件を足す。初めて補完不能になるprefixとその
    // 最後の条件の位置を同時に確定し、停止後に原因位置を探し直さない。
    for end in 1..=cons.len() {
        m.checkpoint()?;
        if !feasible(&m, &cons[..end])? {
            return E::finish(
                Err(issue(
                    Code::InconsistentObservation,
                    cons[end - 1].pointer(),
                    "既知の値・参照・所属を保つ補完が一つもない",
                )
                .into()),
                control,
                Checkpoint::Completion,
            );
        }
        m.checkpoint()?;
    }
    m.done(())
}

/// 条件と、その真偽が依存する変数の組。
type Group<'a> = Vec<(&'a Cons, Vec<usize>)>;

/// 条件のすべてを満たす補完があるか。欠測 slot を共有する条件の組ごとに、
/// その組の変数だけで探す。
fn feasible<E: InputError>(m: &Model<'_, E>, cons: &[Cons]) -> Result<bool, E> {
    m.checkpoint()?;
    let empty = vec![None; m.vars.len()];
    let mut open: Vec<(&Cons, Vec<usize>)> = Vec::new();
    for c in cons {
        m.checkpoint()?;
        match m.eval(c, &empty)? {
            // このprefix全体の補完不能を確定したので、位置付きの入力不正へ
            // 変換するまで事後budgetと併せて否定の結果を保持する。
            Some(false) => return m.decision(false),
            Some(true) => {}
            None => open.push((c, m.vars_of(c)?)),
        }
        m.checkpoint()?;
    }
    fn find<E: InputError>(
        m: &Model<'_, E>,
        parent: &mut [usize],
        mut v: usize,
    ) -> Result<usize, E> {
        m.checkpoint()?;
        while parent[v] != v {
            m.checkpoint()?;
            parent[v] = parent[parent[v]];
            v = parent[v];
            m.checkpoint()?;
        }
        m.done(v)
    }

    let mut parent = Vec::new();
    for v in 0..m.vars.len() {
        m.checkpoint()?;
        parent.push(v);
        m.checkpoint()?;
    }
    for (_, vs) in &open {
        m.checkpoint()?;
        for w in vs.iter().skip(1) {
            m.checkpoint()?;
            let (a, b) = (find(m, &mut parent, vs[0])?, find(m, &mut parent, *w)?);
            parent[a] = b;
            m.checkpoint()?;
        }
        m.checkpoint()?;
    }
    let mut groups: Vec<(usize, Group<'_>)> = Vec::new();
    for (c, vs) in open {
        m.checkpoint()?;
        let root = find(m, &mut parent, vs[0])?;
        let mut found = None;
        for (i, (r, _)) in groups.iter().enumerate() {
            m.checkpoint()?;
            if *r == root {
                found = Some(i);
                break;
            }
            m.checkpoint()?;
        }
        m.checkpoint()?;
        match found {
            Some(i) => groups[i].1.push((c, vs)),
            None => groups.push((root, vec![(c, vs)])),
        }
        m.checkpoint()?;
    }
    let mut assign = empty;
    for (_, group) in &groups {
        m.checkpoint()?;
        if !search(m, group, &mut assign)? {
            return m.decision(false);
        }
        m.checkpoint()?;
    }
    m.done(true)
}

/// 組の変数へ候補を置き、組の全条件を満たす補完を探す。未定の変数が最も少ない条件の変数から、
/// 条件を多く満たす候補を先に置く。全条件が真に決まれば、残りの変数はどの候補でもよい。
fn search<E: InputError>(
    m: &Model<'_, E>,
    cons: &[(&Cons, Vec<usize>)],
    assign: &mut Vec<Option<usize>>,
) -> Result<bool, E> {
    stacker::maybe_grow(128 * 1024, 4 * 1024 * 1024, || {
        m.checkpoint()?;
        let mut next: Option<(usize, usize)> = None;
        for (c, vs) in cons {
            m.checkpoint()?;
            match m.eval(c, assign)? {
                Some(false) => return m.decision(false),
                Some(true) => {}
                None => {
                    let mut free = Vec::new();
                    for &v in vs {
                        m.checkpoint()?;
                        if assign[v].is_none() {
                            free.push(v);
                        }
                        m.checkpoint()?;
                    }
                    debug_assert!(!free.is_empty(), "未定の条件は未定の変数を持つ");
                    if let Some(&v) = free.first()
                        && next.is_none_or(|(n, _)| free.len() < n)
                    {
                        next = Some((free.len(), v));
                    }
                }
            }
            m.checkpoint()?;
        }
        let Some((_, v)) = next else {
            return m.done(true);
        };
        // 破る条件のない候補を、真に決まる条件の多い順に置く。
        let mut order: Vec<(usize, usize)> = Vec::new();
        for (candidate, &x) in m.vars[v].2.iter().enumerate() {
            m.checkpoint()?;
            assign[v] = Some(x);
            let mut decided = 0;
            let mut broken = false;
            for (c, vs) in cons {
                m.checkpoint()?;
                if vs.binary_search(&v).is_ok() {
                    match m.eval(c, assign)? {
                        Some(true) => decided += 1,
                        Some(false) => {
                            broken = true;
                            break;
                        }
                        None => {}
                    }
                }
                m.checkpoint()?;
            }
            if !broken {
                order.push((decided, x));
            }
            if candidate + 1 == m.vars[v].2.len() && order.is_empty() {
                assign[v] = None;
                return m.decision(false);
            }
            m.checkpoint()?;
        }
        if order.is_empty() {
            assign[v] = None;
            return m.decision(false);
        }
        order.sort_by_key(|&(decided, _)| std::cmp::Reverse(decided));
        m.checkpoint()?;
        let mut remaining = order.into_iter().peekable();
        while let Some((_, x)) = remaining.next() {
            m.checkpoint()?;
            assign[v] = Some(x);
            if search(m, cons, assign)? {
                return m.done(true);
            }
            if remaining.peek().is_some() {
                m.checkpoint()?;
            }
        }
        assign[v] = None;
        m.decision(false)
    })
}

/// data 型が、登録 subject を使って有限の値を持つか。参照の引数は登録 subject を要する。
fn data_inhabitation<E: InputError>(
    definitions: &CheckedDefinitions,
    by_type: &HashMap<&str, Vec<usize>>,
    control: &mut Control,
) -> Result<HashMap<String, bool>, E> {
    E::checkpoint(control, Checkpoint::Completion)?;
    let mut datas = Vec::new();
    let mut ok = HashMap::new();
    for (n, d) in &definitions.declarations {
        E::checkpoint(control, Checkpoint::Completion)?;
        if let PrimitiveSignature::Data { constructors } = &d.signature {
            datas.push((n, constructors));
            ok.insert(n.clone(), false);
        }
        E::checkpoint(control, Checkpoint::Completion)?;
    }
    fn inh<E: InputError>(
        t: &Type,
        ok: &HashMap<String, bool>,
        by_type: &HashMap<&str, Vec<usize>>,
        control: &mut Control,
    ) -> Result<bool, E> {
        stacker::maybe_grow(128 * 1024, 4 * 1024 * 1024, || {
            E::checkpoint(control, Checkpoint::Completion)?;
            let out = match t {
                Type::Ref(e) | Type::Owned(e, _) => {
                    by_type.get(e.as_str()).is_some_and(|v| !v.is_empty())
                }
                Type::Data(d) => ok.get(d).copied().unwrap_or(false),
                Type::Tuple(items) => {
                    let mut all = true;
                    for t in items {
                        E::checkpoint(control, Checkpoint::Completion)?;
                        if !inh::<E>(t, ok, by_type, control)? {
                            all = false;
                            break;
                        }
                        E::checkpoint(control, Checkpoint::Completion)?;
                    }
                    all
                }
                // 始域が空なら空の Map がある。
                Type::Map(a, b) => {
                    !inh::<E>(a, ok, by_type, control)? || inh::<E>(b, ok, by_type, control)?
                }
                _ => true,
            };
            E::checkpoint(control, Checkpoint::Completion)?;
            Ok(out)
        })
    }
    loop {
        E::checkpoint(control, Checkpoint::Completion)?;
        let mut changed = false;
        for (n, ctors) in &datas {
            E::checkpoint(control, Checkpoint::Completion)?;
            if !ok[*n] {
                let mut any = false;
                for c in *ctors {
                    E::checkpoint(control, Checkpoint::Completion)?;
                    let mut all = true;
                    for t in &c.arguments {
                        E::checkpoint(control, Checkpoint::Completion)?;
                        if !inh::<E>(t, &ok, by_type, control)? {
                            all = false;
                            break;
                        }
                        E::checkpoint(control, Checkpoint::Completion)?;
                    }
                    E::checkpoint(control, Checkpoint::Completion)?;
                    if all {
                        any = true;
                        break;
                    }
                    E::checkpoint(control, Checkpoint::Completion)?;
                }
                E::checkpoint(control, Checkpoint::Completion)?;
                if any {
                    ok.insert((*n).clone(), true);
                    changed = true;
                }
            }
            E::checkpoint(control, Checkpoint::Completion)?;
        }
        E::checkpoint(control, Checkpoint::Completion)?;
        if !changed {
            return Ok(ok);
        }
    }
}
