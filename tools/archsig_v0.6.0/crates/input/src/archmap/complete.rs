//! 依存参照・Map の全域性と、欠測 slot の補完の存在(入力仕様 §5)。
//!
//! 欠測した参照 slot を、型の合う登録 subject から選ぶ有限の変数とする。既知値だけで
//! 破れる条件も、どの補完でも満たせない条件も `inconsistent_observation` とする。
//! Law の成立は補完の条件に使わない。

use super::*;
use archsig_common::control::{Checkpoint, Control};
use archsig_common::json::InputError;

pub struct FieldAssignment {
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

type SlotPosition = (usize, usize);
// Only the variables visited by the current search get working entries.
type Assignment = HashMap<usize, usize>;

/// 元の snapshot と型定義に借用で結び付いた、逐次候補検査の不変部分。
pub struct CompletionPreparation<'a> {
    snapshots: &'a [Snapshot],
    definitions: &'a CheckedDefinitions,
    references: std::cell::OnceCell<ReferenceIndex>,
    compiled: std::cell::OnceCell<CompletionConstraints>,
}

#[derive(Default)]
struct ReferenceIndex {
    subjects: Vec<(usize, usize)>,
    names: HashMap<String, HashMap<String, usize>>,
}
impl ReferenceIndex {
    fn position(&self, snapshot: &str, subject: &str) -> Option<usize> {
        self.names.get(snapshot)?.get(subject).copied()
    }

    fn subject<'a>(&self, snapshots: &'a [Snapshot], position: usize) -> &'a Subject {
        let (snapshot, subject) = self.subjects[position];
        &snapshots[snapshot].subjects[subject]
    }
}

struct AssignmentReferences<'a> {
    prepared: &'a CompletionPreparation<'a>,
    control: &'a Control,
    point: Checkpoint,
}
impl<E: InputError> value::ReferenceTypes<E> for AssignmentReferences<'_> {
    fn type_of(&self, snapshot: &str, subject: &str) -> Result<Option<&str>, E> {
        let index = self
            .prepared
            .reference_index::<E>(self.control, self.point)?;
        Ok(index
            .position(snapshot, subject)
            .map(|g| index.subject(self.prepared.snapshots, g).ty.as_str()))
    }
}

struct CompletionConstraints {
    by_type: HashMap<String, Vec<usize>>,
    owner_field: Vec<Option<usize>>,
    /// 欠測参照変数の元slot。
    variables: Vec<SlotPosition>,
    var_index: HashMap<SlotPosition, usize>,
    ordered: Vec<(SlotPosition, Cons)>,
    data_inhabited: HashMap<String, bool>,
}

struct Model<'a, E> {
    prepared: &'a CompletionPreparation<'a>,
    references: &'a ReferenceIndex,
    compiled: &'a CompletionConstraints,
    pinned: BTreeMap<SlotPosition, Value>,
    control: &'a Control,
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
    fn new(
        prepared: &'a CompletionPreparation<'a>,
        references: &'a ReferenceIndex,
        compiled: &'a CompletionConstraints,
        control: &'a Control,
    ) -> Self {
        Self {
            prepared,
            references,
            compiled,
            pinned: BTreeMap::new(),
            control,
            error: std::marker::PhantomData,
        }
    }

    fn subject(&self, position: usize) -> &'a Subject {
        self.references.subject(self.prepared.snapshots, position)
    }

    fn position(&self, snapshot: &str, subject: &str) -> usize {
        self.references
            .position(snapshot, subject)
            .expect("元表で型検査済みの参照")
    }

    fn checkpoint(&self) -> Result<(), E> {
        E::checkpoint(self.control, Checkpoint::Completion)
    }

    /// 各意味検査の結果を採用する前にも、共有された停止を確認する。
    fn done<T>(&self, value: T) -> Result<T, E> {
        self.checkpoint()?;
        Ok(value)
    }

    fn field_index(&self, g: usize, name: &str) -> Result<usize, E> {
        self.checkpoint()?;
        for (i, f) in self.subject(g).fields.iter().enumerate() {
            self.checkpoint()?;
            if f.name.short() == name {
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
                    .map(|(snapshot, subject)| RefSrc::Known(self.position(snapshot, subject))),
            );
        }
        let out = match &self.subject(g).fields[f].slot {
            Slot::Known { value, .. } => value
                .as_ref()
                .map(|(s, id)| RefSrc::Known(self.position(s, id))),
            Slot::Missing => self
                .compiled
                .var_index
                .get(&(g, f))
                .map(|v| RefSrc::Var(*v)),
        };
        self.done(out)
    }

    fn resolve(&self, r: RefSrc, assign: &Assignment) -> Result<Option<usize>, E> {
        self.checkpoint()?;
        self.done(match r {
            RefSrc::Known(g) => Some(g),
            RefSrc::Var(v) => assign.get(&v).copied(),
        })
    }

    /// x の所属先。所属を持たない型は Some(None)、未定は None。
    fn owner(&self, x: usize, assign: &Assignment) -> Result<Option<Option<usize>>, E> {
        self.checkpoint()?;
        let out = match self.compiled.owner_field[x] {
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
        assign: &Assignment,
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
        assign: &Assignment,
    ) -> Result<Option<bool>, E> {
        self.checkpoint()?;
        let out = match family {
            Family::All(e) => Some(self.subject(x).ty == *e),
            Family::Owned { entity, .. } => {
                if self.subject(x).ty != *entity {
                    return self.done(Some(false));
                }
                let Some(Some(root)) = self.family_root(holder, family, assign)? else {
                    return self.done(None);
                };
                if self.subject(x).snapshot != self.subject(root).snapshot {
                    return self.done(Some(false));
                }
                self.owner(x, assign)?.map(|owner| owner == Some(root))
            }
        };
        self.done(out)
    }

    fn candidates(&self, family: &Family) -> Result<&[usize], E> {
        self.checkpoint()?;
        let e = match family {
            Family::All(e) | Family::Owned { entity: e, .. } => e,
        };
        self.done(
            self.compiled
                .by_type
                .get(e.as_str())
                .map_or(&[], Vec::as_slice),
        )
    }

    fn nonempty(
        &self,
        holder: usize,
        family: &Family,
        assign: &Assignment,
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
        self.done(out)
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

    fn inhabited(&self, holder: usize, ty: &Type, assign: &Assignment) -> Result<Option<bool>, E> {
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
                            return self.done(acc);
                        }
                        self.checkpoint()?;
                    }
                    acc
                }
                Type::Data(d) => Some(self.compiled.data_inhabited.get(d).copied().unwrap_or(true)),
                _ => Some(true),
            };
            self.done(out)
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
        if let Some(f) = self.compiled.owner_field[x]
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

    fn eval(&self, c: &Cons, assign: &Assignment) -> Result<Option<bool>, E> {
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
                        return self.done(out);
                    }
                    self.checkpoint()?;
                }
                for &x in self.candidates(family)? {
                    self.checkpoint()?;
                    if !keys.contains(&x) {
                        out = and3(out, self.member(x, *holder, family, assign)?.map(|m| !m));
                        if out == Some(false) {
                            return self.done(out);
                        }
                    }
                    self.checkpoint()?;
                }
                out
            }
            Cons::Inhabit { holder, ty, .. } => self.inhabited(*holder, ty, assign)?,
        };
        self.done(out)
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
            let target = RefSrc::Known(m.position(snapshot, subject));
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
                &m.prepared.definitions.declarations[d].signature
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
                let (s, id) = k.as_ref().expect("Map key must be a reference");
                keys.push(m.position(s, id));
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
    control: &Control,
) -> Result<(), E> {
    check_completion_with_values::<E>(snapshots, definitions, &[], control)
}

/// 元欠測slotへ置いた型付き値が、既知Map/ownerを保つ補完へ拡張できるかを検査する。
/// 入力表やLawの真偽を変更せず、通常の存在検査と同じ制約を使う。
pub fn check_completion_with_values<E: InputError>(
    snapshots: &[Snapshot],
    definitions: &CheckedDefinitions,
    pinned: &[FieldAssignment],
    control: &Control,
) -> Result<(), E> {
    CompletionPreparation::from_snapshots(snapshots, definitions)
        .check_unprepared(pinned, false, control)
}

/// 既知slotを含む内部候補も、同じ原始型・所属・Map全域性で検査する。
/// 観測表は不変とし、未代入の欠測が整合する補完を持つことを要求する。
pub fn check_valuation_with_values<E: InputError>(
    snapshots: &[Snapshot],
    definitions: &CheckedDefinitions,
    pinned: &[FieldAssignment],
    control: &Control,
) -> Result<(), E> {
    CompletionPreparation::from_snapshots(snapshots, definitions)
        .check_unprepared(pinned, true, control)
}

impl<'a> CompletionPreparation<'a> {
    /// 元入力の型付き参照索引を共有し、補完に特有の制約は初回に組み立てる。
    pub fn new(
        inputs: &'a crate::input::CheckedInputs,
        control: &Control,
        point: Checkpoint,
    ) -> Result<Self, archsig_common::control::Signal> {
        control.checkpoint(point)?;
        Ok(Self::from_snapshots(
            inputs.archmap().snapshots(),
            inputs.definitions(),
        ))
    }

    /// Check an encoded primitive candidate against this input's registered subjects.
    pub fn check_assignment<E: InputError>(
        &self,
        value: &archsig_common::canonical::Json,
        ty: &Type,
        namespace: &str,
        control: &Control,
        point: Checkpoint,
    ) -> Result<Value, E> {
        let roster = AssignmentReferences {
            prepared: self,
            control,
            point,
        };
        value::check_assignment_for(value, ty, self.definitions, &roster, namespace, control)
    }

    fn from_snapshots(snapshots: &'a [Snapshot], definitions: &'a CheckedDefinitions) -> Self {
        Self {
            snapshots,
            definitions,
            references: std::cell::OnceCell::new(),
            compiled: std::cell::OnceCell::new(),
        }
    }

    fn reference_index<E: InputError>(
        &self,
        control: &Control,
        point: Checkpoint,
    ) -> Result<&ReferenceIndex, E> {
        let checkpoint = || E::checkpoint(control, point);
        checkpoint()?;
        if let Some(index) = self.references.get() {
            return Ok(index);
        }
        let mut index = ReferenceIndex::default();
        for (snapshot_index, snapshot) in self.snapshots.iter().enumerate() {
            checkpoint()?;
            for (subject_index, subject) in snapshot.subjects.iter().enumerate() {
                checkpoint()?;
                let g = index.subjects.len();
                index.subjects.push((snapshot_index, subject_index));
                index
                    .names
                    .entry(subject.snapshot.clone())
                    .or_default()
                    .insert(subject.id.clone(), g);
            }
        }
        checkpoint()?;
        Ok(self.references.get_or_init(|| index))
    }

    fn constraints<E: InputError>(
        &self,
        references: &ReferenceIndex,
        control: &Control,
    ) -> Result<&CompletionConstraints, E> {
        let checkpoint = || E::checkpoint(control, Checkpoint::Completion);
        checkpoint()?;
        if let Some(compiled) = self.compiled.get() {
            return Ok(compiled);
        }
        let mut compiled = self.compile_index::<E>(references, control)?;
        let mut ordered = Vec::new();
        Self::compile_conditions(
            &Model::<E>::new(self, references, &compiled, control),
            |slot, condition| {
                ordered.push((slot, condition));
            },
        )?;
        compiled.ordered = ordered;
        Ok(self.compiled.get_or_init(|| compiled))
    }

    fn compile_index<E: InputError>(
        &self,
        references: &ReferenceIndex,
        control: &Control,
    ) -> Result<CompletionConstraints, E> {
        let checkpoint = || E::checkpoint(control, Checkpoint::Completion);
        checkpoint()?;
        let mut by_type = HashMap::<String, Vec<usize>>::new();
        let mut owner_field = Vec::new();
        let mut variables = Vec::new();
        let mut var_index = HashMap::new();
        for g in 0..references.subjects.len() {
            checkpoint()?;
            let subject = references.subject(self.snapshots, g);
            by_type.entry(subject.ty.to_string()).or_default().push(g);
            let has_owner = matches!(
                self.definitions.declarations[subject.ty.as_str()].signature,
                PrimitiveSignature::Entity { .. } | PrimitiveSignature::Arrow { .. }
            );
            let mut owner = None;
            for (f, field) in subject.fields.iter().enumerate() {
                checkpoint()?;
                if has_owner && owner.is_none() && field.name.is_owner() {
                    owner = Some(f);
                }
                if field.slot == Slot::Missing && matches!(field.ty, Type::Ref(_) | Type::Owned(..))
                {
                    var_index.insert((g, f), variables.len());
                    variables.push((g, f));
                }
            }
            owner_field.push(owner);
        }
        let data_inhabited = data_inhabitation::<E>(self.definitions, &by_type, control)?;
        Ok(CompletionConstraints {
            by_type,
            owner_field,
            variables,
            var_index,
            ordered: Vec::new(),
            data_inhabited,
        })
    }

    fn compile_conditions<E: InputError>(
        m: &Model<'_, E>,
        mut record: impl FnMut(SlotPosition, Cons),
    ) -> Result<(), E> {
        let mut cons = Vec::new();
        for g in 0..m.references.subjects.len() {
            m.checkpoint()?;
            let subject = m.subject(g);
            for (f, field) in subject.fields.iter().enumerate() {
                m.checkpoint()?;
                if let Some(value) = m.pinned.get(&(g, f)) {
                    collect_known(m, g, &field.ty, value, &subject.pointer, &mut cons)?;
                } else {
                    match &field.slot {
                        Slot::Known { value, pointer, .. } => {
                            collect_known(m, g, &field.ty, value, pointer, &mut cons)?;
                        }
                        Slot::Missing => {
                            if let Some(&v) = m.compiled.var_index.get(&(g, f))
                                && let Type::Owned(..) = field.ty
                            {
                                let family = m.family_of(g, &field.ty)?.expect("依存参照");
                                cons.push(Cons::Member {
                                    holder: g,
                                    family,
                                    target: RefSrc::Var(v),
                                    pointer: subject.pointer.clone(),
                                });
                            }
                            if has_reference(m, &field.ty)? {
                                cons.push(Cons::Inhabit {
                                    holder: g,
                                    ty: field.ty.clone(),
                                    pointer: subject.pointer.clone(),
                                });
                            }
                        }
                    }
                }
                for condition in cons.drain(..) {
                    record((g, f), condition);
                }
                m.checkpoint()?;
            }
        }
        m.done(())
    }

    /// 一つの代入を元の欠測slotへ同時に置き、補完が存在するかを検査する。
    pub fn check<E: InputError>(
        &self,
        pinned: &[FieldAssignment],
        control: &Control,
    ) -> Result<(), E> {
        self.check_inner(pinned, false, control)
    }

    /// 既知slotを変更する内部の原始valuationを同じ元制約で検査する。
    pub fn check_valuation<E: InputError>(
        &self,
        pinned: &[FieldAssignment],
        control: &Control,
    ) -> Result<(), E> {
        self.check_inner(pinned, true, control)
    }

    fn check_inner<E: InputError>(
        &self,
        pinned: &[FieldAssignment],
        replace_known: bool,
        control: &Control,
    ) -> Result<(), E> {
        let references = self.reference_index::<E>(control, Checkpoint::Completion)?;
        let compiled = self.constraints::<E>(references, control)?;
        let mut m = Model::<E>::new(self, references, compiled, control);
        self.pin_values(&mut m, pinned, replace_known)?;
        Self::check_pinned(&m, &compiled.ordered)
    }

    fn check_unprepared<E: InputError>(
        &self,
        pinned: &[FieldAssignment],
        replace_known: bool,
        control: &Control,
    ) -> Result<(), E> {
        let references = self.reference_index::<E>(control, Checkpoint::Completion)?;
        let compiled = self.compile_index::<E>(references, control)?;
        let mut m = Model::<E>::new(self, references, &compiled, control);
        // The raw Snapshot API can replace an original value before it is read.
        self.pin_values(&mut m, pinned, replace_known)?;
        let mut ordered = Vec::new();
        Self::compile_conditions(&m, |_, condition| ordered.push(condition))?;
        Self::check_conditions(&m, ordered.iter().map(|condition| (None, condition)))
    }

    fn pin_values<E: InputError>(
        &self,
        m: &mut Model<'_, E>,
        pinned: &[FieldAssignment],
        replace_known: bool,
    ) -> Result<(), E> {
        m.checkpoint()?;
        if pinned.is_empty() {
            return Ok(());
        }
        for assignment in pinned {
            m.checkpoint()?;
            let fail = || {
                issue(
                    Code::Reference,
                    "",
                    "completion value does not match the original missing slot",
                )
            };
            let Some(g) = m
                .references
                .position(&assignment.snapshot, &assignment.subject)
            else {
                return Err(fail().into());
            };
            let mut selected = None;
            for (index, field) in m.subject(g).fields.iter().enumerate() {
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
            if (!replace_known && field.slot != Slot::Missing) || m.pinned.contains_key(&(g, f)) {
                return Err(fail().into());
            }
            let namespace = m.subject(g).ty.namespace();
            let value = self.check_assignment::<E>(
                &assignment.value,
                &field.ty,
                namespace,
                m.control,
                Checkpoint::Completion,
            )?;
            m.pinned.insert((g, f), value);
            m.checkpoint()?;
        }
        m.done(())
    }

    fn check_pinned<E: InputError>(
        m: &Model<'_, E>,
        ordered: &[(SlotPosition, Cons)],
    ) -> Result<(), E> {
        let mut added = Vec::new();
        let mut cons = Vec::new();
        for (&(g, f), value) in &m.pinned {
            m.checkpoint()?;
            let subject = m.subject(g);
            collect_known(
                m,
                g,
                &subject.fields[f].ty,
                value,
                &subject.pointer,
                &mut cons,
            )?;
            added.extend(cons.drain(..).map(|condition| ((g, f), condition)));
        }
        let mut original = ordered.iter().peekable();
        let mut added = added.iter().peekable();
        let conditions = std::iter::from_fn(|| match (original.peek(), added.peek()) {
            (_, None) => original
                .next()
                .map(|(slot, condition)| (Some(slot), condition)),
            (Some((slot, _)), Some((position, _))) if slot <= position => original
                .next()
                .map(|(slot, condition)| (Some(slot), condition)),
            _ => added.next().map(|(_, condition)| (None, condition)),
        });
        Self::check_conditions(m, conditions)
    }

    fn check_conditions<'c, E: InputError>(
        m: &Model<'_, E>,
        conditions: impl Iterator<Item = (Option<&'c SlotPosition>, &'c Cons)>,
    ) -> Result<(), E> {
        // subject順・field宣言順に条件を足す。初めて補完不能になるprefixとその
        // 最後の条件の位置を同時に確定し、停止後に原因位置を探し直さない。
        let empty = Assignment::new();
        let mut pending = Vec::new();
        for (original_slot, condition) in conditions {
            m.checkpoint()?;
            if original_slot.is_some_and(|slot| m.pinned.contains_key(slot)) {
                continue;
            }
            // 既知trueは以後の補完を制約しない。未決条件を追加したときだけ、
            // それまでの未決prefixを探索する。既知falseも元の条件順で返す。
            let possible = match m.eval(condition, &empty)? {
                Some(value) => value,
                None => {
                    pending.push(condition);
                    feasible(m, &pending)?
                }
            };
            if !possible {
                return E::finish(
                    Err(issue(
                        Code::InconsistentObservation,
                        condition.pointer(),
                        "no completion preserves known values, references, and ownership",
                    )
                    .into()),
                    m.control,
                    Checkpoint::Completion,
                );
            }
            m.checkpoint()?;
        }
        m.done(())
    }
}

/// 条件と、その真偽が依存する変数の組。
type Group<'a> = Vec<(&'a Cons, Vec<usize>)>;

/// 条件のすべてを満たす補完があるか。欠測 slot を共有する条件の組ごとに、
/// その組の変数だけで探す。
fn feasible<E: InputError>(m: &Model<'_, E>, cons: &[&Cons]) -> Result<bool, E> {
    m.checkpoint()?;
    let empty = Assignment::new();
    let mut open: Vec<(&Cons, Vec<usize>)> = Vec::new();
    for &c in cons {
        m.checkpoint()?;
        match m.eval(c, &empty)? {
            Some(false) => return m.done(false),
            Some(true) => {}
            None => open.push((c, m.vars_of(c)?)),
        }
        m.checkpoint()?;
    }
    fn find<E: InputError>(
        m: &Model<'_, E>,
        parent: &mut HashMap<usize, usize>,
        mut v: usize,
    ) -> Result<usize, E> {
        m.checkpoint()?;
        while let Some(&next) = parent.get(&v) {
            m.checkpoint()?;
            let Some(&grandparent) = parent.get(&next) else {
                return m.done(next);
            };
            parent.insert(v, grandparent);
            v = grandparent;
        }
        m.done(v)
    }

    // 未決条件が同じ組に結ぶ変数だけを記録する。
    let mut parent = HashMap::new();
    for (_, vs) in &open {
        m.checkpoint()?;
        for w in vs.iter().skip(1) {
            m.checkpoint()?;
            let (a, b) = (find(m, &mut parent, vs[0])?, find(m, &mut parent, *w)?);
            if a != b {
                parent.insert(a, b);
            }
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
        assign.clear();
        if !search(m, group, &mut assign)? {
            return m.done(false);
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
    assign: &mut Assignment,
) -> Result<bool, E> {
    stacker::maybe_grow(128 * 1024, 4 * 1024 * 1024, || {
        m.checkpoint()?;
        let mut next: Option<(usize, usize)> = None;
        for (c, vs) in cons {
            m.checkpoint()?;
            match m.eval(c, assign)? {
                Some(false) => return m.done(false),
                Some(true) => {}
                None => {
                    let mut free = Vec::new();
                    for &v in vs {
                        m.checkpoint()?;
                        if !assign.contains_key(&v) {
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
        let (g, f) = m.compiled.variables[v];
        let (Type::Ref(entity) | Type::Owned(entity, _)) = &m.subject(g).fields[f].ty else {
            unreachable!("欠測参照変数の元型")
        };
        let domain = m
            .compiled
            .by_type
            .get(entity)
            .map_or(&[][..], Vec::as_slice);
        for (candidate, &x) in domain.iter().enumerate() {
            m.checkpoint()?;
            assign.insert(v, x);
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
            if candidate + 1 == domain.len() && order.is_empty() {
                assign.remove(&v);
                return m.done(false);
            }
            m.checkpoint()?;
        }
        if order.is_empty() {
            assign.remove(&v);
            return m.done(false);
        }
        order.sort_by_key(|&(decided, _)| std::cmp::Reverse(decided));
        m.checkpoint()?;
        let mut remaining = order.into_iter().peekable();
        while let Some((_, x)) = remaining.next() {
            m.checkpoint()?;
            assign.insert(v, x);
            if search(m, cons, assign)? {
                return m.done(true);
            }
            if remaining.peek().is_some() {
                m.checkpoint()?;
            }
        }
        assign.remove(&v);
        m.done(false)
    })
}

/// data 型が、登録 subject を使って有限の値を持つか。参照の引数は登録 subject を要する。
fn data_inhabitation<E: InputError>(
    definitions: &CheckedDefinitions,
    by_type: &HashMap<String, Vec<usize>>,
    control: &Control,
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
        by_type: &HashMap<String, Vec<usize>>,
        control: &Control,
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
