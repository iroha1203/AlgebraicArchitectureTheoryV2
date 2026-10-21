//! 保存済みconfiguration操作の恒等・名前付き語・総作用の合成。
use super::*;

/// 各indexはこの有限表内の元操作を指す。合成の両indexは自身より前にある。
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum OperationStep {
    Generator {
        subject: FactPointer,
        /// 内部arrowの包含root。correspondenceはNone。
        root: Option<FactPointer>,
        reading: String,
        to_reading: String,
    },
    Identity {
        object: ObjectIdentity,
    },
    Compose {
        first: usize,
        then: usize,
    },
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct DerivedOrigin {
    pub(super) source: ObjectIdentity,
    pub(super) target: ObjectIdentity,
    pub(super) steps: Vec<OperationStep>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConfigurationOperation {
    map: ConfigurationMap,
    steps: Vec<OperationStep>,
    word: Vec<FactPointer>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OperationFailure {
    cause: ConstructionFailure,
    partial: Option<Box<ConfigurationOperation>>,
}
impl OperationFailure {
    pub fn cause(&self) -> &ConstructionFailure {
        &self.cause
    }
    pub fn partial(&self) -> Option<&ConfigurationOperation> {
        self.partial.as_deref()
    }
    pub(crate) fn into_parts(self) -> (ConstructionFailure, Option<Box<ConfigurationOperation>>) {
        (self.cause, self.partial)
    }
}
impl From<ConstructionFailure> for OperationFailure {
    fn from(cause: ConstructionFailure) -> Self {
        Self {
            cause,
            partial: None,
        }
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ActionDifference {
    fact: FactPointer,
    left: FactPointer,
    right: FactPointer,
}
impl ActionDifference {
    pub fn fact(&self) -> &FactPointer {
        &self.fact
    }
    pub fn left(&self) -> &FactPointer {
        &self.left
    }
    pub fn right(&self) -> &FactPointer {
        &self.right
    }
}
impl ConfigurationOperation {
    /// 保存確認済みのmapを再照合して操作を構成する。候補やPathを受け取らない。
    pub fn from_map(
        inputs: &CheckedInputs,
        map: &ConfigurationMap,
        control: &mut Control,
    ) -> Result<Self, ConstructionFailure> {
        Self::from_map_retained(inputs, map, control).map_err(|failure| failure.cause)
    }
    /// 最後の停止確認で中断した場合も、検査済みの操作を保持する。
    pub fn from_map_retained(
        inputs: &CheckedInputs,
        map: &ConfigurationMap,
        control: &mut Control,
    ) -> Result<Self, OperationFailure> {
        tick(control)?;
        map.recheck(inputs, control)?;
        from_verified_map_retained(map.clone(), control)
    }
    pub fn map(&self) -> &ConfigurationMap {
        &self.map
    }
    pub fn source(&self) -> ObjectIdentity {
        self.map.candidate.source_object()
    }
    pub fn target(&self) -> ObjectIdentity {
        self.map.candidate.target_object()
    }
    pub fn word(&self) -> &[FactPointer] {
        &self.word
    }
    /// 最後の行がこの操作。合成は元操作を指すindexを残す。
    pub fn derivation(&self) -> &[OperationStep] {
        &self.steps
    }
    pub fn recheck(
        &self,
        inputs: &CheckedInputs,
        control: &mut Control,
    ) -> Result<(), ConstructionFailure> {
        tick(control)?;
        self.map.recheck(inputs, control)?;
        if self != &from_verified_map(self.map.clone(), control)? {
            return Err(ConstructionFailure::Inconsistent(
                "操作の語・構成由来が現在のmapと違う".into(),
            ));
        }
        tick(control)
    }
    /// then∘self。作用を合成した後、family外の像を置き直さない。
    pub fn compose(
        &self,
        inputs: &CheckedInputs,
        then: &Self,
        control: &mut Control,
    ) -> Result<Self, ConstructionFailure> {
        self.compose_retained(inputs, then, control)
            .map_err(|failure| failure.cause)
    }
    /// 同じ合成を検査し、最後の停止確認でも完成済みの操作を保持する。
    pub fn compose_retained(
        &self,
        inputs: &CheckedInputs,
        then: &Self,
        control: &mut Control,
    ) -> Result<Self, OperationFailure> {
        tick(control)?;
        self.recheck(inputs, control)?;
        then.recheck(inputs, control)?;
        let data = compose_data(
            &Data::from_map(&self.map),
            &Data::from_map(&then.map),
            control,
        )?;
        let mut steps = Vec::new();
        for step in &self.steps {
            tick(control)?;
            steps.push(step.clone());
        }
        let first = steps.len() - 1;
        let offset = steps.len();
        for step in &then.steps {
            tick(control)?;
            steps.push(match step {
                OperationStep::Compose { first, then } => OperationStep::Compose {
                    first: first.checked_add(offset).ok_or_else(overflow)?,
                    then: then.checked_add(offset).ok_or_else(overflow)?,
                },
                step => step.clone(),
            });
        }
        let then = steps.len() - 1;
        steps.push(OperationStep::Compose { first, then });
        let map = derived_map(data, steps);
        from_verified_map_retained(map, control)
    }
    /// 恒等を除き平坦化した生成元名・順序を比較する。
    pub fn word_equal(
        &self,
        inputs: &CheckedInputs,
        other: &Self,
        control: &mut Control,
    ) -> Result<bool, ConstructionFailure> {
        self.recheck(inputs, control)?;
        other.recheck(inputs, control)?;
        if self.word.len() != other.word.len() {
            return Ok(false);
        }
        for (a, b) in self.word.iter().zip(&other.word) {
            tick(control)?;
            if a != b {
                return Ok(false);
            }
        }
        tick(control)?;
        Ok(true)
    }
    /// 同じ始終対象の全U作用を比較し、不一致なら元位置と両像を返す。
    pub fn action_difference(
        &self,
        inputs: &CheckedInputs,
        other: &Self,
        control: &mut Control,
    ) -> Result<Option<ActionDifference>, ConstructionFailure> {
        self.recheck(inputs, control)?;
        other.recheck(inputs, control)?;
        let a = &self.map.candidate;
        let b = &other.map.candidate;
        if self.source() != other.source()
            || self.target() != other.target()
            || a.universe != b.universe
        {
            return Err(ConstructionFailure::InvalidSelection(
                "作用比較の始終対象・reading・共通Uが違う".into(),
            ));
        }
        for ((fact, left), right) in a.universe.iter().zip(&a.images).zip(&b.images) {
            tick(control)?;
            if left != right {
                return Ok(Some(ActionDifference {
                    fact: fact.clone(),
                    left: left.clone(),
                    right: right.clone(),
                }));
            }
        }
        tick(control)?;
        Ok(None)
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IdentityConstruction {
    object: ObjectIdentity,
    configuration: ConfigurationCandidate,
    operation: Option<ConfigurationOperation>,
}
impl IdentityConstruction {
    pub fn object(&self) -> &ObjectIdentity {
        &self.object
    }
    pub fn configuration(&self) -> &ConfigurationCandidate {
        &self.configuration
    }
    pub fn missing(&self) -> &[FactPointer] {
        self.configuration.blocking_slots()
    }
    pub fn operation(&self) -> Option<&ConfigurationOperation> {
        self.operation.as_ref()
    }
    pub fn recheck(
        &self,
        inputs: &CheckedInputs,
        control: &mut Control,
    ) -> Result<(), ConstructionFailure> {
        if self != &identity_object(inputs, &self.object, control)? {
            return Err(ConstructionFailure::Inconsistent(
                "恒等の対象・構成が現在入力と違う".into(),
            ));
        }
        tick(control)
    }
}
fn tick(control: &mut Control) -> Result<(), ConstructionFailure> {
    control
        .checkpoint(Checkpoint::ConfigurationOperation)
        .map_err(Into::into)
}
fn overflow() -> ConstructionFailure {
    ConstructionFailure::Inconsistent("操作の構成indexが大きすぎる".into())
}
fn raw_step(map: &ConfigurationMap) -> Option<OperationStep> {
    let candidate = &map.candidate;
    let (subject, root) = match &candidate.origin {
        MapOrigin::Correspondence(subject) => (subject.clone(), None),
        MapOrigin::InternalArrow { root, arrow } => (arrow.clone(), Some(root.clone())),
        MapOrigin::Derived(_) => return None,
    };
    Some(OperationStep::Generator {
        subject,
        root,
        reading: candidate.reading.clone(),
        to_reading: candidate.to_reading.clone(),
    })
}
fn from_verified_map(
    map: ConfigurationMap,
    control: &mut Control,
) -> Result<ConfigurationOperation, ConstructionFailure> {
    from_verified_map_retained(map, control).map_err(|failure| failure.cause)
}
fn from_verified_map_retained(
    map: ConfigurationMap,
    control: &mut Control,
) -> Result<ConfigurationOperation, OperationFailure> {
    tick(control)?;
    let steps = match &map.candidate.origin {
        MapOrigin::Derived(origin) => origin.steps.clone(),
        _ => vec![
            raw_step(&map)
                .ok_or_else(|| ConstructionFailure::Inconsistent("原始mapの由来がない".into()))?,
        ],
    };
    let word = word(&steps, control)?;
    let operation = ConfigurationOperation { map, steps, word };
    match tick(control) {
        Ok(()) => Ok(operation),
        Err(cause) => Err(OperationFailure {
            cause,
            partial: Some(Box::new(operation)),
        }),
    }
}
fn validate_steps(
    steps: &[OperationStep],
    control: &mut Control,
) -> Result<(), ConstructionFailure> {
    tick(control)?;
    if steps.is_empty() {
        return Err(ConstructionFailure::Inconsistent("操作の構成表が空".into()));
    }
    let mut seen = vec![false; steps.len()];
    let mut pending = vec![steps.len() - 1];
    while let Some(i) = pending.pop() {
        tick(control)?;
        if seen[i] {
            continue;
        }
        seen[i] = true;
        if let OperationStep::Compose { first, then } = steps[i] {
            if first >= i || then >= i {
                return Err(ConstructionFailure::Inconsistent(
                    "合成の元操作が既出でない".into(),
                ));
            }
            pending.push(first);
            pending.push(then);
        }
    }
    for visited in seen {
        tick(control)?;
        if !visited {
            return Err(ConstructionFailure::Inconsistent(
                "操作の構成に未使用行がある".into(),
            ));
        }
    }
    Ok(())
}
fn word(
    steps: &[OperationStep],
    control: &mut Control,
) -> Result<Vec<FactPointer>, ConstructionFailure> {
    validate_steps(steps, control)?;
    let mut pending = vec![steps.len() - 1];
    let mut out = Vec::new();
    while let Some(i) = pending.pop() {
        tick(control)?;
        match &steps[i] {
            OperationStep::Generator { subject, .. } => out.push(subject.clone()),
            OperationStep::Identity { .. } => {}
            OperationStep::Compose { first, then } => {
                pending.push(*then);
                pending.push(*first);
            }
        }
    }
    Ok(out)
}
#[derive(Clone)]
struct Data {
    source: ObjectIdentity,
    target: ObjectIdentity,
    source_configuration: Configuration,
    target_configuration: Configuration,
    universe: Vec<FactPointer>,
    images: Vec<FactPointer>,
}
impl Data {
    fn from_map(map: &ConfigurationMap) -> Self {
        let c = &map.candidate;
        Self {
            source: c.source_object(),
            target: c.target_object(),
            source_configuration: c.source_configuration.clone(),
            target_configuration: c.target_configuration.clone(),
            universe: c.universe.clone(),
            images: c.images.clone(),
        }
    }
}
fn compose_data(a: &Data, b: &Data, control: &mut Control) -> Result<Data, ConstructionFailure> {
    tick(control)?;
    if a.target != b.source
        || a.universe != b.universe
        || (a.source.root == a.source.subject) != (b.source.root == b.source.subject)
    {
        return Err(ConstructionFailure::InvalidSelection(
            "合成の中間対象・reading・操作階層・共通Uが違う".into(),
        ));
    }
    let mut index = BTreeMap::new();
    for (i, fact) in b.universe.iter().enumerate() {
        tick(control)?;
        index.insert(fact, i);
    }
    let mut images = Vec::new();
    for intermediate in &a.images {
        tick(control)?;
        let i = *index
            .get(intermediate)
            .ok_or_else(|| ConstructionFailure::Inconsistent("中間像が共通Uにない".into()))?;
        images.push(
            b.images
                .get(i)
                .ok_or_else(|| ConstructionFailure::Inconsistent("総作用の像がない".into()))?
                .clone(),
        );
    }
    tick(control)?;
    Ok(Data {
        source: a.source.clone(),
        target: b.target.clone(),
        source_configuration: a.source_configuration.clone(),
        target_configuration: b.target_configuration.clone(),
        universe: a.universe.clone(),
        images,
    })
}
fn derived_map(data: Data, steps: Vec<OperationStep>) -> ConfigurationMap {
    ConfigurationMap {
        candidate: MapCandidate {
            source_root: data.source.subject.clone(),
            target_root: data.target.subject.clone(),
            reading: data.source.reading.clone(),
            to_reading: data.target.reading.clone(),
            origin: MapOrigin::Derived(DerivedOrigin {
                source: data.source,
                target: data.target,
                steps,
            }),
            source_configuration: data.source_configuration,
            target_configuration: data.target_configuration,
            universe: data.universe,
            images: data.images,
        },
    }
}
/// base、または指定owned entityの部分対象の全U恒等。未決の構成にはoperationを返さない。
pub fn identity(
    inputs: &CheckedInputs,
    reading: &str,
    root_snapshot: &str,
    root: &str,
    component: Option<(&str, &str)>,
    control: &mut Control,
) -> Result<IdentityConstruction, ConstructionFailure> {
    tick(control)?;
    if component.is_some_and(|(s, id)| s == root_snapshot && id == root) {
        return Err(ConstructionFailure::InvalidSelection(
            "root自身はbaseとして選び、部分対象にはowned entityを指定する".into(),
        ));
    }
    let root = FactPointer {
        snapshot: root_snapshot.into(),
        subject: root.into(),
        field: None,
        atom: None,
    };
    let subject = component
        .map(|(s, id)| FactPointer {
            snapshot: s.into(),
            subject: id.into(),
            field: None,
            atom: None,
        })
        .unwrap_or_else(|| root.clone());
    identity_object(
        inputs,
        &ObjectIdentity {
            reading: reading.into(),
            root,
            subject,
        },
        control,
    )
}
fn identity_object(
    inputs: &CheckedInputs,
    object: &ObjectIdentity,
    control: &mut Control,
) -> Result<IdentityConstruction, ConstructionFailure> {
    tick(control)?;
    let construction = construct(
        inputs,
        &object.reading,
        &object.root.snapshot,
        &object.root.subject,
        control,
    )?;
    if object.root != *construction.root()
        || object.subject.field.is_some()
        || object.subject.atom.is_some()
    {
        return Err(ConstructionFailure::InvalidSelection(
            "恒等の対象は存在事実を要求する".into(),
        ));
    }
    let candidate = if object.subject == object.root {
        construction.base().clone()
    } else {
        let selected = subject(
            inputs,
            &object.subject.snapshot,
            &object.subject.subject,
            control,
        )?;
        let root = subject(inputs, &object.root.snapshot, &object.root.subject, control)?;
        let namespaces = namespaces(inputs, &object.reading, control)?;
        if !visible(inputs, &selected.ty, &namespaces)
            || !matches!(inputs.definitions().declarations.get(&selected.ty).map(|d|&d.signature),Some(PrimitiveSignature::Entity{owner:Some(owner),..}) if owner==&root.ty)
        {
            return Err(ConstructionFailure::InvalidSelection(
                "恒等の部分対象は選択rootのowned entityを要求する".into(),
            ));
        }
        let mut missing = BTreeSet::new();
        if endpoint(selected, "owner", &mut missing, control)?
            .is_some_and(|k| k != (root.snapshot.clone(), root.id.clone()))
        {
            return Err(ConstructionFailure::InvalidSelection(
                "恒等の部分対象が別rootに属する".into(),
            ));
        }
        let mut index = BTreeMap::new();
        for snapshot in &inputs.archmap().snapshots {
            tick(control)?;
            for s in &snapshot.subjects {
                tick(control)?;
                index.insert((s.snapshot.as_str(), s.id.as_str()), s);
            }
        }
        configuration(inputs, &[selected], &index, missing, control)?
    };
    let operation = if let Some(configuration) = candidate.configuration() {
        let mut images = Vec::new();
        for fact in construction.universe() {
            tick(control)?;
            images.push(fact.clone());
        }
        let data = Data {
            source: object.clone(),
            target: object.clone(),
            source_configuration: configuration.clone(),
            target_configuration: configuration.clone(),
            universe: construction.universe().to_vec(),
            images,
        };
        Some(from_verified_map(
            derived_map(
                data,
                vec![OperationStep::Identity {
                    object: object.clone(),
                }],
            ),
            control,
        )?)
    } else {
        None
    };
    tick(control)?;
    Ok(IdentityConstruction {
        object: object.clone(),
        configuration: candidate,
        operation,
    })
}
pub(super) fn recompute(
    inputs: &CheckedInputs,
    steps: &[OperationStep],
    control: &mut Control,
) -> Result<ConfigurationMap, ConstructionFailure> {
    validate_steps(steps, control)?;
    let mut values: Vec<Data> = Vec::new();
    for step in steps {
        tick(control)?;
        let value = match step {
            OperationStep::Generator {
                subject,
                root,
                reading,
                to_reading,
            } => {
                let map = if let Some(root) = root {
                    internal_arrow(
                        inputs,
                        reading,
                        &root.snapshot,
                        &root.subject,
                        &subject.snapshot,
                        &subject.subject,
                        control,
                    )?
                    .map
                } else {
                    correspondence(
                        inputs,
                        &subject.snapshot,
                        &subject.subject,
                        reading,
                        Some(to_reading),
                        control,
                    )?
                    .map
                }
                .ok_or_else(|| {
                    ConstructionFailure::Inconsistent(
                        "元の操作のConfiguration保存が現在未確認".into(),
                    )
                })?;
                if raw_step(&map).as_ref() != Some(step) {
                    return Err(ConstructionFailure::Inconsistent(
                        "元の操作の選択・readingが現在入力と違う".into(),
                    ));
                }
                Data::from_map(&map)
            }
            OperationStep::Identity { object } => {
                let identity = identity_object(inputs, object, control)?;
                let operation = identity.operation.ok_or_else(|| {
                    ConstructionFailure::Inconsistent("恒等の対象が現在未決".into())
                })?;
                Data::from_map(&operation.map)
            }
            OperationStep::Compose { first, then } => {
                let a = values.get(*first).ok_or_else(|| {
                    ConstructionFailure::Inconsistent("合成の始操作が既出でない".into())
                })?;
                let b = values.get(*then).ok_or_else(|| {
                    ConstructionFailure::Inconsistent("合成の終操作が既出でない".into())
                })?;
                compose_data(a, b, control)?
            }
        };
        values.push(value);
    }
    tick(control)?;
    let data = values
        .pop()
        .ok_or_else(|| ConstructionFailure::Inconsistent("操作の構成が空".into()))?;
    Ok(derived_map(data, steps.to_vec()))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::observed::{
        control::{Limits, Usage},
        input::{InputSources, check_inputs},
    };
    use std::{cell::Cell, rc::Rc};
    fn inputs() -> CheckedInputs {
        check_inputs(
            InputSources::from_bytes(
                vec![include_bytes!("../../../tests/fixtures/reservations.atoms.json").to_vec()],
                include_bytes!("../../../tests/fixtures/configuration-operation.law").to_vec(),
                include_bytes!("../../../tests/fixtures/configuration-operation.archmap.json")
                    .to_vec(),
            ),
            &mut Control::unlimited(),
        )
        .unwrap()
    }
    #[test]
    fn recheck_rejects_forged_words_maps_origin_objects_and_composition_edges() {
        let inputs = inputs();
        let e = internal_arrow(
            &inputs,
            "Reservations",
            "v",
            "A",
            "v",
            "e",
            &mut Control::unlimited(),
        )
        .unwrap();
        let h = internal_arrow(
            &inputs,
            "Reservations",
            "v",
            "A",
            "v",
            "h",
            &mut Control::unlimited(),
        )
        .unwrap();
        let e =
            ConfigurationOperation::from_map(&inputs, e.map().unwrap(), &mut Control::unlimited())
                .unwrap();
        let h =
            ConfigurationOperation::from_map(&inputs, h.map().unwrap(), &mut Control::unlimited())
                .unwrap();
        let original = e.compose(&inputs, &h, &mut Control::unlimited()).unwrap();
        for kind in [
            "word",
            "action",
            "source",
            "target",
            "reading",
            "steps",
            "cycle",
            "unused",
            "reference",
            "generator",
            "identity",
        ] {
            let mut forged = original.clone();
            match kind {
                "word" => forged.word.clear(),
                "action" => forged.map.candidate.images.swap(0, 1),
                "source" => forged.map.candidate.source_root.subject = "q".into(),
                "target" => forged.map.candidate.target_root.subject = "q".into(),
                "reading" => forged.map.candidate.to_reading = "Alternative".into(),
                "steps" => forged.steps.swap(0, 1),
                kind => {
                    if let MapOrigin::Derived(origin) = &mut forged.map.candidate.origin {
                        match kind {
                            "cycle" => {
                                origin.steps[2] = OperationStep::Compose { first: 2, then: 1 }
                            }
                            "unused" => origin.steps[2] = origin.steps[0].clone(),
                            "reference" => {
                                if let OperationStep::Generator { subject, .. } =
                                    &mut origin.steps[0]
                                {
                                    subject.field = Some("Reservations.Reserve.from".into());
                                }
                            }
                            "generator" => {
                                if let OperationStep::Generator { subject, .. } =
                                    &mut origin.steps[0]
                                {
                                    subject.subject = "h".into();
                                }
                            }
                            "identity" => origin.source.subject.subject = "q".into(),
                            _ => unreachable!(),
                        }
                    }
                }
            }
            assert!(
                forged.recheck(&inputs, &mut Control::unlimited()).is_err(),
                "{kind}"
            );
        }
        let mut forged = identity(
            &inputs,
            "Reservations",
            "v",
            "A",
            Some(("v", "p")),
            &mut Control::unlimited(),
        )
        .unwrap();
        forged.operation = None;
        assert!(forged.recheck(&inputs, &mut Control::unlimited()).is_err());
        let mut forged = original.clone();
        forged.map.candidate.images.clear();
        assert!(forged.recheck(&inputs, &mut Control::unlimited()).is_err());
    }
    #[test]
    fn very_deep_identity_composition_is_iterative_and_latches_before_recomputation() {
        let inputs = inputs();
        let identity = identity(
            &inputs,
            "Reservations",
            "v",
            "A",
            None,
            &mut Control::unlimited(),
        )
        .unwrap();
        let mut operation = identity.operation.unwrap();
        let object = operation.source();
        let mut steps = vec![OperationStep::Identity {
            object: object.clone(),
        }];
        for _ in 0..10_000 {
            let first = steps.len() - 1;
            let then = steps.len();
            steps.push(OperationStep::Identity {
                object: object.clone(),
            });
            steps.push(OperationStep::Compose { first, then });
        }
        assert!(word(&steps, &mut Control::unlimited()).unwrap().is_empty());
        let MapOrigin::Derived(origin) = &mut operation.map.candidate.origin else {
            panic!("identity origin")
        };
        origin.steps = steps.clone();
        operation.steps = steps;
        let count = Rc::new(Cell::new(0usize));
        let seen = count.clone();
        let mut control = Control::new(
            Limits {
                time_ms: Some(1),
                memory_mib: None,
            },
            move |point| {
                if point == Checkpoint::ConfigurationOperation {
                    seen.set(seen.get() + 1);
                }
                Usage {
                    elapsed_ms: if seen.get() >= 50 { 1 } else { 0 },
                    ..Usage::default()
                }
            },
        );
        let failure = operation.recheck(&inputs, &mut control).unwrap_err();
        assert_eq!(
            failure,
            ConstructionFailure::Stopped(control.stop_reason().unwrap())
        );
        assert_eq!(count.get(), 50);
        assert_eq!(
            operation.map.recheck(&inputs, &mut control).unwrap_err(),
            failure
        );
        assert_eq!(count.get(), 50);
    }
}
