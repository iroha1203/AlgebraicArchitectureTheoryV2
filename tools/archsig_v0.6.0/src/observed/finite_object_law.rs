//! 選択対象の参照域を保つ有限Law族。元の完全束縛は固定参照として保持する。
use super::*;
use crate::{
    construction::{ConstructionFailure, maps::ObjectIdentity, readings::ObjectReadingInstances},
    observed::object_evaluate::ObjectDomain,
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct Selection {
    readings: ObjectReadingInstances,
    object: usize,
    domain: Arc<ObjectDomain>,
    reading_span: crate::law::ast::Span,
    reference_conditions: Vec<Fact>,
}
fn failure(cause: ConstructionFailure) -> ValidationFailure {
    match cause {
        ConstructionFailure::Stopped(reason) => reason.into(),
        other => format!("有限Law族の対象選択: {other:?}").into(),
    }
}
impl Selection {
    fn compute(
        inputs: &CheckedInputs,
        readings: &ObjectReadingInstances,
        object: usize,
        c: &mut Control,
    ) -> Result<Self, ValidationFailure> {
        c.checkpoint(Checkpoint::ObjectEvaluation)?;
        readings.recheck(inputs, c).map_err(failure)?;
        let domain = ObjectDomain::from_readings(inputs, readings, object, c)?;
        let mut reading_span = None;
        for info in &inputs.law().infos {
            c.checkpoint(Checkpoint::ObjectEvaluation)?;
            if info.kind == "reading" && info.name == domain.identity.reading() {
                reading_span = Some(info.span);
            }
        }
        let reading_span = reading_span.ok_or("有限Law族の元reading位置がない")?;
        let mut positions = BTreeSet::new();
        for condition in readings.objects()[object].conditions() {
            c.checkpoint(Checkpoint::ObjectEvaluation)?;
            positions.insert(condition.slot().clone());
        }
        if domain.identity.root() == domain.identity.subject() {
            for condition in readings.construction().local_domain().conditional() {
                c.checkpoint(Checkpoint::ObjectEvaluation)?;
                positions.insert(condition.owner_slot().clone());
            }
        }
        let mut reference_conditions = vec![];
        for position in positions {
            c.checkpoint(Checkpoint::ObjectEvaluation)?;
            reference_conditions.push(position);
        }
        Ok(Self {
            readings: readings.clone(),
            object,
            domain: Arc::new(domain),
            reading_span,
            reference_conditions,
        })
    }
    pub(super) fn identity(&self) -> &ObjectIdentity {
        &self.domain.identity
    }
    pub(super) fn pending_membership(&self) -> Option<Location> {
        (!self.readings.objects()[self.object].conditions().is_empty()).then_some(Location::Law {
            span: self.reading_span,
        })
    }
    pub(super) fn recheck(
        &self,
        inputs: &CheckedInputs,
        c: &mut Control,
    ) -> Result<(), ValidationFailure> {
        let expected = Self::compute(inputs, &self.readings, self.object, c)?;
        if self != &expected {
            return Err("有限Law族の対象参照域が元構成と違う".into());
        }
        Ok(())
    }
}
impl FiniteLawFamilyValuations {
    pub(super) fn in_object<'a>(&self, mut environment: Environment<'a>) -> Environment<'a> {
        environment.object = self.object.as_ref().map(|o| Arc::clone(&o.domain));
        environment
    }
    pub(in crate::observed) fn object_identity(&self) -> Option<&ObjectIdentity> {
        self.object.as_ref().map(|o| o.identity())
    }
    /// 参照域の所属に関する未観測位置。各列の依存はそのScopeと未決状態で読む。
    pub(in crate::observed) fn reference_domain_conditions(&self) -> &[Fact] {
        match &self.object {
            Some(object) => &object.reference_conditions,
            None => &[],
        }
    }
    /// 値が一致する別対象の由来でも、指定した対象の結果として消費しない。
    pub(in crate::observed) fn recheck_on_object(
        &self,
        inputs: &CheckedInputs,
        readings: &ObjectReadingInstances,
        object: usize,
        c: &mut Control,
    ) -> Result<(), FiniteLawFamilyFailure> {
        let expected = Selection::compute(inputs, readings, object, c).map_err(|cause| {
            FiniteLawFamilyFailure {
                cause,
                partial: None,
            }
        })?;
        if self.object.as_deref() != Some(&expected) {
            return Err(FiniteLawFamilyFailure {
                cause: "有限Law族が消費先の選択対象に由来しない".into(),
                partial: None,
            });
        }
        self.recheck(inputs, c)
    }
}
/// 同じ元Lawの完全束縛を、指定対象の内部参照量化で読む。
/// instanceの適用条件を生成する処理とは分け、ここで選んだ束縛を暗黙に変更しない。
pub(in crate::observed) fn finite_object_law_family_valuations(
    inputs: &CheckedInputs,
    readings: &ObjectReadingInstances,
    object: usize,
    selected: &[(String, Vec<(String, Scalar)>)],
    c: &mut Control,
) -> Result<FiniteLawFamilyValuations, FiniteLawFamilyFailure> {
    let object = Selection::compute(inputs, readings, object, c).map_err(|cause| {
        FiniteLawFamilyFailure {
            cause,
            partial: None,
        }
    })?;
    family_with_object(inputs, selected, Some(Arc::new(object)), c)
}

#[cfg(test)]
#[path = "finite_object_law_tests.rs"]
mod tests;
