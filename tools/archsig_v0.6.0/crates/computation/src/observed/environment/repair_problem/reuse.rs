//! 再観測の間で共有する純粋なLaw関係。Graph・成功判断・旧由来は保持しない。
use super::super::validation_identity;
use super::*;
use std::{cell::RefCell, rc::Rc, sync::Arc};
fn tick(c: &Control) -> Result<(), ValidationFailure> {
    c.checkpoint(Checkpoint::Reuse)?;
    Ok(())
}

#[derive(Debug)]
struct SubjectShape {
    snapshot: String,
    subject: String,
    entity: String,
    owners: Vec<(String, Scalar)>,
}
#[derive(Debug)]
struct Key {
    root: Fact,
    reading: String,
    change: String,
    subjects: Vec<Scalar>,
    laws: Vec<String>,
    structure: Arc<Vec<SubjectShape>>,
    owners: Vec<(Fact, Scalar)>,
}
fn bindings_equal(
    a: &[(String, Arc<Scalar>)],
    b: &[(String, Arc<Scalar>)],
    c: &Control,
) -> Result<bool, ValidationFailure> {
    if a.len() != b.len() {
        return Ok(false);
    }
    for ((an, av), (bn, bv)) in a.iter().zip(b) {
        tick(c)?;
        if an != bn || !validation_identity::scalar(av, bv, c)? {
            return Ok(false);
        }
    }
    Ok(true)
}
impl Key {
    fn matches(&self, other: &Self, c: &Control) -> Result<bool, ValidationFailure> {
        tick(c)?;
        if self.root != other.root
            || self.reading != other.reading
            || self.change != other.change
            || self.laws != other.laws
            || self.subjects.len() != other.subjects.len()
            || self.structure.len() != other.structure.len()
            || self.owners.len() != other.owners.len()
        {
            return Ok(false);
        }
        for (a, b) in self.subjects.iter().zip(&other.subjects) {
            tick(c)?;
            if !validation_identity::scalar(a, b, c)? {
                return Ok(false);
            }
        }
        for (a, b) in self.structure.iter().zip(other.structure.iter()) {
            tick(c)?;
            if a.snapshot != b.snapshot
                || a.subject != b.subject
                || a.entity != b.entity
                || a.owners.len() != b.owners.len()
            {
                return Ok(false);
            }
            for ((an, av), (bn, bv)) in a.owners.iter().zip(&b.owners) {
                tick(c)?;
                if an != bn || !validation_identity::scalar(av, bv, c)? {
                    return Ok(false);
                }
            }
        }
        for ((af, av), (bf, bv)) in self.owners.iter().zip(&other.owners) {
            tick(c)?;
            if af != bf || !validation_identity::scalar(av, bv, c)? {
                return Ok(false);
            }
        }
        Ok(true)
    }
}
#[derive(Debug, PartialEq)]
enum Axis {
    Parameter(usize),
    Input(Fact),
    Output(Fact),
}
#[derive(Clone, Debug)]
struct Condition {
    expression: usize,
    reading: String,
    bindings: Vec<(String, Arc<Scalar>)>,
    positive: bool,
}
#[derive(Clone, Debug)]
pub(super) struct Signature {
    locator: u64,
    law: String,
    expression: usize,
    original_context: bool,
    reading: String,
    bindings: Vec<(String, Arc<Scalar>)>,
    conditions: Vec<Condition>,
}
impl Signature {
    fn matches(&self, other: &Self, c: &Control) -> Result<bool, ValidationFailure> {
        tick(c)?;
        if self.law != other.law
            || self.expression != other.expression
            || self.original_context != other.original_context
            || self.reading != other.reading
            || self.conditions.len() != other.conditions.len()
            || !bindings_equal(&self.bindings, &other.bindings, c)?
        {
            return Ok(false);
        }
        for (a, b) in self.conditions.iter().zip(&other.conditions) {
            tick(c)?;
            if a.expression != b.expression
                || a.reading != b.reading
                || a.positive != b.positive
                || !bindings_equal(&a.bindings, &b.bindings, c)?
            {
                return Ok(false);
            }
        }
        Ok(true)
    }
}
#[derive(Debug)]
struct Dependency {
    slot: Fact,
    value: Arc<Scalar>,
}
#[derive(Debug)]
struct Item {
    signature: Signature,
    relation: finite::Relation,
    dependencies: Vec<Dependency>,
    readings: BTreeSet<String>,
}
#[derive(Debug)]
pub(in crate::observed) struct Frame {
    key: Key,
    axes: Vec<Axis>,
    domains: Vec<Arc<Vec<Scalar>>>,
    items: Vec<Item>,
    lookup: BTreeMap<u64, Vec<usize>>,
}
#[derive(Default)]
pub(in crate::observed) struct Pool {
    pub previous: Vec<Arc<Frame>>,
    pub current: Vec<Arc<Frame>>,
    // None: 未検査。Some(None): 未観測owner等で共有条件を確認できない。
    structure: Option<Option<Arc<Vec<SubjectShape>>>>,
}
pub(in crate::observed) type SharedPool = Rc<RefCell<Pool>>;
#[derive(PartialEq, Eq, PartialOrd, Ord)]
enum ValueSlot {
    Binding(String),
    Dependency(Fact),
}
// 大きい共通束縛・依存値は名前/位置ごとの直近値を共有する。
// この一時索引はfinish時に破棄し、Frameへ履歴として残さない。
pub(super) struct Builder {
    frame: Frame,
    values: BTreeMap<ValueSlot, Arc<Scalar>>,
}
pub(super) struct Basis<'a> {
    pub domains: &'a [Arc<Vec<Scalar>>],
    pub parameters: usize,
    pub outputs: &'a [Output],
    pub inputs: Option<&'a InputSpace>,
}

#[cfg(test)]
thread_local! {
    static GENERATED:std::cell::Cell<usize>=const {std::cell::Cell::new(0)};
    static REUSED:std::cell::Cell<usize>=const {std::cell::Cell::new(0)};
}
#[cfg(test)]
pub(in crate::observed) fn counts() -> (usize, usize) {
    (
        GENERATED.with(std::cell::Cell::get),
        REUSED.with(std::cell::Cell::get),
    )
}
pub(super) fn generated() {
    #[cfg(test)]
    GENERATED.with(|n| n.set(n.get() + 1));
}

fn first_order(value: &Scalar, c: &Control) -> Result<bool, ValidationFailure> {
    stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
        tick(c)?;
        match value {
            Scalar::Path(_) | Scalar::Term(_) => return Ok(false),
            Scalar::Map { pairs, .. } => {
                for (a, b) in pairs {
                    if !first_order(a, c)? || !first_order(b, c)? {
                        return Ok(false);
                    }
                }
            }
            Scalar::List { items, .. }
            | Scalar::Set { items, .. }
            | Scalar::Tuple(items)
            | Scalar::Data { args: items, .. } => {
                for item in items {
                    if !first_order(item, c)? {
                        return Ok(false);
                    }
                }
            }
            Scalar::Option {
                value: Some(value), ..
            } => {
                if !first_order(value, c)? {
                    return Ok(false);
                }
            }
            _ => {}
        }
        Ok(true)
    })
}
fn structure(
    env: &Environment<'_>,
    c: &Control,
) -> Result<Option<Arc<Vec<SubjectShape>>>, ValidationFailure> {
    if let Some(saved) = &env.results.repair_relations.borrow().structure {
        return Ok(saved.clone());
    }
    let mut shapes = vec![];
    let mut complete = true;
    for snapshot in env.indexes.inputs.archmap().snapshots() {
        for subject in &snapshot.subjects {
            tick(c)?;
            let mut owners = vec![];
            for field in &subject.fields {
                if !field.name.is_owner() {
                    continue;
                }
                tick(c)?;
                let Slot::Known { value, .. } = &field.slot else {
                    complete = false;
                    break;
                };
                let value = match scalar_from(value, &field.ty, env.indexes.inputs.law(), c) {
                    Ok(value) => value,
                    Err(ValidationFailure::UnsupportedExpression { .. }) => None,
                    Err(error) => return Err(error),
                };
                let Some(value) = value else {
                    complete = false;
                    break;
                };
                if !first_order(&value, c)? {
                    complete = false;
                    break;
                }
                owners.push((field.name.to_string(), value));
            }
            if !complete {
                break;
            }
            shapes.push(SubjectShape {
                snapshot: snapshot.id.clone(),
                subject: subject.id.clone(),
                entity: subject.ty.to_string(),
                owners,
            });
        }
        if !complete {
            break;
        }
    }
    shapes.sort_by(|a, b| (&a.snapshot, &a.subject).cmp(&(&b.snapshot, &b.subject)));
    let result = complete.then(|| Arc::new(shapes));
    env.results.repair_relations.borrow_mut().structure = Some(result.clone());
    Ok(result)
}
impl Builder {
    pub(super) fn begin(
        env: &Environment<'_>,
        witness: &ArchitectureWitness,
        change: &str,
        subjects: &[Scalar],
        requirements: &[(String, Vec<(String, Scalar)>)],
        basis: Basis<'_>,
        c: &Control,
    ) -> Result<Option<Self>, ValidationFailure> {
        let Basis {
            domains,
            parameters,
            outputs,
            inputs,
        } = basis;
        if domains.iter().any(|d| d.is_empty()) {
            return Ok(None);
        }
        let Some(structure) = structure(env, c)? else {
            return Ok(None);
        };
        let owners = env
            .fixed_values()
            .into_iter()
            .filter(|(f, _)| f.field.as_ref().is_some_and(|f| f.is_owner()))
            .collect();
        let axes = (0..parameters)
            .map(Axis::Parameter)
            .chain(
                inputs
                    .into_iter()
                    .flat_map(|i| i.fields.iter().cloned().map(Axis::Input)),
            )
            .chain(outputs.iter().map(|o| Axis::Output(o.fact.clone())))
            .collect::<Vec<_>>();
        if axes.len() != domains.len() {
            return Err(internal!("再観測の座標と値域の長さが違う").into());
        }
        Ok(Some(Self {
            frame: Frame {
                key: Key {
                    root: witness.construction().root().clone(),
                    reading: witness.construction().reading().into(),
                    change: change.into(),
                    subjects: subjects.to_vec(),
                    laws: requirements.iter().map(|(n, _)| n.clone()).collect(),
                    structure,
                    owners,
                },
                axes,
                domains: domains.to_vec(),
                items: vec![],
                lookup: BTreeMap::new(),
            },
            values: BTreeMap::new(),
        }))
    }
    fn value(
        &mut self,
        slot: ValueSlot,
        value: &Scalar,
        c: &Control,
    ) -> Result<Arc<Scalar>, ValidationFailure> {
        if let Some(previous) = self.values.get(&slot)
            && validation_identity::scalar(previous, value, c)?
        {
            return Ok(previous.clone());
        }
        let value = Arc::new(value.clone());
        self.values.insert(slot, value.clone());
        Ok(value)
    }
    fn bindings(
        &mut self,
        bindings: &[(String, Scalar)],
        c: &Control,
    ) -> Result<Vec<(String, Arc<Scalar>)>, ValidationFailure> {
        let mut result = vec![];
        for (name, value) in bindings {
            tick(c)?;
            result.push((
                name.clone(),
                self.value(ValueSlot::Binding(name.clone()), value, c)?,
            ));
        }
        Ok(result)
    }
    pub(super) fn signature(
        &mut self,
        law: &str,
        factor: &law_factors::Factor,
        c: &Control,
    ) -> Result<Option<Signature>, ValidationFailure> {
        for (_, value) in factor.bindings.iter().chain(
            factor
                .conditions
                .iter()
                .flat_map(|condition| condition.bindings.iter()),
        ) {
            if !first_order(value, c)? {
                return Ok(None);
            }
        }
        let bindings = self.bindings(&factor.bindings, c)?;
        let mut conditions = vec![];
        for condition in &factor.conditions {
            tick(c)?;
            conditions.push(Condition {
                expression: condition.expression,
                reading: condition.reading.clone(),
                positive: condition.positive,
                bindings: self.bindings(&condition.bindings, c)?,
            });
        }
        let mut signature = Signature {
            locator: 0,
            law: law.into(),
            expression: factor.expression,
            original_context: factor.original_context,
            reading: factor.reading.clone(),
            bindings,
            conditions,
        };
        signature.locator = locator(&signature, c)?;
        Ok(Some(signature))
    }
    pub(super) fn prior(
        &self,
        env: &Environment<'_>,
        c: &Control,
    ) -> Result<Option<Arc<Frame>>, ValidationFailure> {
        let pool = env.results.repair_relations.borrow();
        for old in pool.current.iter().rev().chain(pool.previous.iter()) {
            tick(c)?;
            if old.key.matches(&self.frame.key, c)? {
                return Ok(Some(old.clone()));
            }
        }
        Ok(None)
    }
    pub(super) fn reuse(
        &mut self,
        env: &Environment<'_>,
        old: Option<&Frame>,
        signature: &Signature,
        updates: &finite::Problem,
        c: &Control,
    ) -> Result<Option<(finite::Relation, Vec<Fact>, Scope)>, ValidationFailure> {
        let Some(old) = old else {
            return Ok(None);
        };
        // Hashes narrow the search only. Full program/value correspondence follows.
        for index in old.lookup.get(&signature.locator).into_iter().flatten() {
            let item = &old.items[*index];
            tick(c)?;
            if !item.signature.matches(signature, c)? {
                continue;
            }
            let mut columns = vec![];
            for column in &item.relation.columns {
                tick(c)?;
                let mut found = None;
                for (index, axis) in self.frame.axes.iter().enumerate() {
                    tick(c)?;
                    if *axis == old.axes[*column] {
                        found = Some(index);
                        break;
                    }
                }
                let Some(index) = found else {
                    break;
                };
                let a = &self.frame.domains[index];
                let b = &old.domains[*column];
                if a.len() != b.len() {
                    break;
                }
                let mut equal = true;
                for (a, b) in a.iter().zip(b.iter()) {
                    if !validation_identity::scalar(a, b, c)? {
                        equal = false;
                        break;
                    }
                }
                if !equal {
                    break;
                }
                columns.push(index);
            }
            if columns.len() != item.relation.columns.len() {
                continue;
            }
            let mut support = BTreeSet::new();
            let mut scope = Scope::default();
            let mut dependencies = vec![];
            let mut valid = true;
            for dependency in &item.dependencies {
                tick(c)?;
                let Some(read) = read(env, &dependency.slot, &signature.reading)? else {
                    valid = false;
                    break;
                };
                let Some(value) = &read.known_value else {
                    valid = false;
                    break;
                };
                if !validation_identity::scalar(value, &dependency.value, c)? {
                    valid = false;
                    break;
                }
                dependencies.push(Dependency {
                    slot: dependency.slot.clone(),
                    value: self.value(ValueSlot::Dependency(dependency.slot.clone()), value, c)?,
                });
                support.extend(read.support.iter().cloned());
                scope.merge(&read.scope);
            }
            if !valid {
                continue;
            }
            // 両世代で、この座標の全値域を実際に評価できることを確認する。
            // 非到達点をLawの偽として保存せず、現在不要な観測を要求しない。
            if !rows_while(&columns, &self.frame.domains, c, |point| {
                let mut pins = vec![None; self.frame.domains.len()];
                for (column, value) in columns.iter().zip(point) {
                    pins[*column] = Some(*value);
                }
                updates.exists(&pins, c)
            })? {
                continue;
            }
            let relation = finite::Relation {
                columns,
                rows: item.relation.rows.clone(),
            };
            scope.readings.extend(item.readings.iter().cloned());
            self.push(Item {
                signature: signature.clone(),
                relation: relation.clone(),
                dependencies,
                readings: item.readings.clone(),
            });
            #[cfg(test)]
            REUSED.with(|n| n.set(n.get() + 1));
            return Ok(Some((relation, support.into_iter().collect(), scope)));
        }
        Ok(None)
    }
    pub(super) fn remember(
        &mut self,
        env: &Environment<'_>,
        signature: Signature,
        relation: &finite::Relation,
        support: &BTreeSet<Fact>,
        scope: &Scope,
        c: &Control,
    ) -> Result<(), ValidationFailure> {
        for column in &relation.columns {
            for value in self.frame.domains[*column].iter() {
                if !first_order(value, c)? {
                    return Ok(());
                }
            }
        }
        let mut slots = BTreeSet::new();
        let mut dependencies = vec![];
        for fact in support {
            tick(c)?;
            if fact.field.is_none() {
                return Ok(());
            }
            let slot = Fact::from(archsig_input::archmap::FactData {
                snapshot: fact.snapshot.clone(),
                subject: fact.subject.clone(),
                field: fact.field.clone(),
                atom: None,
            });
            if !slots.insert(slot.clone()) {
                continue;
            }
            let Some(read) = read(env, &slot, &signature.reading)? else {
                return Ok(());
            };
            let Some(value) = read.known_value else {
                return Ok(());
            };
            if !first_order(&value, c)? {
                return Ok(());
            }
            dependencies.push(Dependency {
                value: self.value(ValueSlot::Dependency(slot.clone()), &value, c)?,
                slot,
            });
        }
        self.push(Item {
            signature,
            relation: relation.clone(),
            dependencies,
            readings: scope.readings.clone(),
        });
        Ok(())
    }
    fn push(&mut self, item: Item) {
        self.frame
            .lookup
            .entry(item.signature.locator)
            .or_default()
            .push(self.frame.items.len());
        self.frame.items.push(item);
    }
    pub(super) fn finish(
        self,
        env: &Environment<'_>,
        c: &Control,
    ) -> Result<(), ValidationFailure> {
        if !self.frame.items.is_empty() {
            let mut pool = env.results.repair_relations.borrow_mut();
            for (index, frame) in pool.current.iter().enumerate() {
                if frame.key.matches(&self.frame.key, c)? {
                    pool.current[index] = Arc::new(self.frame);
                    return Ok(());
                }
            }
            pool.current.push(Arc::new(self.frame));
        }
        Ok(())
    }
}
// Position-preserving native-value hash. It never serializes a graph or certifies
// equality. Retained first-order programs/values are checked by validation_identity.
fn hash_scalar(
    value: &Scalar,
    hasher: &mut impl std::hash::Hasher,
    c: &Control,
) -> Result<(), ValidationFailure> {
    use std::hash::Hash;
    stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
        tick(c)?;
        std::mem::discriminant(value).hash(hasher);
        match value {
            Scalar::Unit | Scalar::Path(_) | Scalar::Term(_) => {}
            Scalar::Bool(value) => value.hash(hasher),
            Scalar::Text(value) => value.hash(hasher),
            Scalar::Z(value) => value.hash(hasher),
            Scalar::Q(a, b) => {
                a.hash(hasher);
                b.hash(hasher);
            }
            Scalar::Fp { modulus, value } => {
                modulus.hash(hasher);
                value.hash(hasher);
            }
            Scalar::Subject {
                snapshot,
                subject,
                entity,
            } => {
                snapshot.hash(hasher);
                subject.hash(hasher);
                entity.hash(hasher);
            }
            Scalar::Map { pairs, .. } => {
                pairs.len().hash(hasher);
                for (a, b) in pairs {
                    hash_scalar(a, hasher, c)?;
                    hash_scalar(b, hasher, c)?;
                }
            }
            Scalar::List { items, .. } | Scalar::Set { items, .. } | Scalar::Tuple(items) => {
                items.len().hash(hasher);
                for item in items {
                    hash_scalar(item, hasher, c)?;
                }
            }
            Scalar::Data { constructor, args } => {
                constructor.name().as_str().hash(hasher);
                args.len().hash(hasher);
                for arg in args {
                    hash_scalar(arg, hasher, c)?;
                }
            }
            Scalar::Option { value, .. } => {
                value.is_some().hash(hasher);
                if let Some(value) = value {
                    hash_scalar(value, hasher, c)?;
                }
            }
        }
        tick(c)?;
        Ok(())
    })
}
fn locator(signature: &Signature, c: &Control) -> Result<u64, ValidationFailure> {
    use std::hash::{Hash, Hasher};
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    signature.law.hash(&mut hasher);
    signature.expression.hash(&mut hasher);
    signature.original_context.hash(&mut hasher);
    signature.reading.hash(&mut hasher);
    for (name, value) in &signature.bindings {
        tick(c)?;
        name.hash(&mut hasher);
        hash_scalar(value, &mut hasher, c)?;
    }
    for condition in &signature.conditions {
        tick(c)?;
        condition.expression.hash(&mut hasher);
        condition.reading.hash(&mut hasher);
        condition.positive.hash(&mut hasher);
        for (name, value) in &condition.bindings {
            tick(c)?;
            name.hash(&mut hasher);
            hash_scalar(value, &mut hasher, c)?;
        }
    }
    Ok(hasher.finish())
}
fn read(
    env: &Environment<'_>,
    slot: &Fact,
    reading: &str,
) -> Result<Option<SourceValue>, ValidationFailure> {
    let subject = env.indexes.subject(&slot.snapshot, &slot.subject)?;
    let field = env.input_name(
        slot.field
            .as_deref()
            .ok_or(internal!("関係依存のfieldがない"))?,
    )?;
    let source = change_evaluation::known(Scalar::Subject {
        snapshot: slot.snapshot.clone(),
        subject: slot.subject.clone(),
        entity: subject.ty.to_string(),
    });
    let value = match env.scoped_field(source, &field, &Scope::default(), reading, (0, 0)) {
        Ok(value) => value,
        Err(ValidationFailure::UnsupportedExpression { .. }) => return Ok(None),
        Err(error) => return Err(error),
    };
    Ok(
        (!value.condition_failed && !value.condition_pending && value.known_value.is_some())
            .then_some(value),
    )
}
#[cfg(test)]
mod tests {
    use super::*;
    fn key() -> Key {
        Key {
            root: Fact::from(archsig_input::archmap::FactData {
                snapshot: "v".into(),
                subject: "r".into(),
                field: None,
                atom: None,
            }),
            reading: "R".into(),
            change: "R.change".into(),
            subjects: vec![],
            laws: vec![],
            structure: Arc::new(vec![SubjectShape {
                snapshot: "v".into(),
                subject: "r".into(),
                entity: "R.Root".into(),
                owners: vec![],
            }]),
            owners: vec![],
        }
    }
    #[test]
    fn reuse_condition_comparison_preserves_every_interruption_checkpoint() {
        use std::{cell::Cell, rc::Rc};
        let a = key();
        let b = key();
        let run = |stop: Option<usize>| {
            let count = Rc::new(Cell::new(0));
            let seen = count.clone();
            let c = Control::new(move |_| {
                seen.set(seen.get() + 1);
                stop.filter(|n| *n == seen.get())
                    .map(|_| archsig_common::control::Signal::Term)
            });
            let result = a.matches(&b, &c);
            (result, count.get())
        };
        let (result, count) = run(None);
        assert!(result.unwrap());
        for at in 1..=count {
            assert!(
                matches!(run(Some(at)).0, Err(ValidationFailure::Stop(_))),
                "checkpoint {at}"
            );
        }
    }
    #[allow(dead_code)]
    mod fixture {
        include!("../../../../../../tests/common/repair_problem_data.rs");
    }
    #[test]
    fn common_binding_values_have_one_owner_across_local_relations() {
        let names = (0..16).map(|i| format!("p{i}")).collect::<Vec<_>>();
        let parts = names
            .iter()
            .map(|n| (n.as_str(), false, n.as_str()))
            .collect::<Vec<_>>();
        let input = fixture::sources(
            &parts,
            "view all(r:Root):Set<Part> =Part[r];change choose(c:Part,p:Bool)=c with {flag=p};law required valid(r:Root,xs:Set<Part>):forall c in Part[r]. c.flag;",
        );
        let result = crate::observed::evaluate_observed_bytes(
            input,
            &[
                "u=evaluate(Selected.all,r=@v/root)",
                "p=prepare(Selected.valid,using=Selected.choose,on=@v/root,r=@v/root,xs=$u.value)",
            ],
            &archsig_common::control::quiet(),
        )
        .unwrap();
        assert_eq!(result.status(), "complete", "{:?}", result.issues);
        let frame = &result.repair_cache[0];
        let bindings = frame
            .items
            .iter()
            .filter_map(|item| {
                item.signature
                    .bindings
                    .iter()
                    .find(|(name, _)| name == "xs")
                    .map(|(_, value)| value)
            })
            .collect::<Vec<_>>();
        assert!(bindings.len() > 1);
        assert!(
            bindings.iter().all(|value| Arc::ptr_eq(bindings[0], value)),
            "共通のSet束縛を部品ごとに所有しない"
        );
        let Scalar::Set { items, .. } = bindings[0].as_ref() else {
            panic!()
        };
        assert_eq!(items.len(), 16);
    }

    #[test]
    fn locator_collisions_do_not_certify_relation_identity() {
        let c = archsig_common::control::quiet();
        let body = "view all(r:Root):Set<Part> =Part[r];change choose(c:Part,p:Bool)=c with {flag=p};law required valid(r:Root):forall c in Part[r]. if c.label=\"a\" then not c.flag else c.flag;";
        let input = || fixture::sources(&[("a", false, "a"), ("b", false, "b")], body);
        let asks = [
            "u=evaluate(Selected.all,r=@v/root)",
            "p=prepare(Selected.valid,using=Selected.choose,on=@v/root,r=@v/root)",
            "s=solve($p.problem,within=$u.value)",
        ];
        let mut old = crate::observed::evaluate_observed_bytes(input(), &asks, &c).unwrap();
        let frame = Arc::get_mut(&mut old.repair_cache[0]).unwrap();
        let all = (0..frame.items.len()).rev().collect::<Vec<_>>();
        assert!(all.len() > 1);
        // Simulate every index key colliding, without changing any certified row.
        for bucket in frame.lookup.values_mut() {
            *bucket = all.clone();
        }
        let mut asks = asks.to_vec();
        asks.push("second=candidate($s.solutions,index=1)");
        let result = crate::observed::reevaluate_observed_bytes(&old, input(), &asks, &c).unwrap();
        assert_eq!(result.status(), "complete", "{:?}", result.issues);
        assert_eq!(result.answers[3].status, Decision::Refuted);
        assert!(!result.answers[3].outputs.contains_key("assignment"));
    }
}
