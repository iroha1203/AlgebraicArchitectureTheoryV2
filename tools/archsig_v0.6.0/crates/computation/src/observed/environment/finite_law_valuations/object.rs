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
    reading_span: archsig_input::law::ast::Span,
    reference_conditions: Vec<Fact>,
}
pub(super) fn failure(cause: ConstructionFailure) -> ValidationFailure {
    match cause {
        ConstructionFailure::Stopped(reason) => reason.into(),
        other => other
            .internal_context(format!("有限Law族の対象選択: {other:?}"))
            .into(),
    }
}
impl Selection {
    fn compute(
        inputs: &CheckedInputs,
        readings: &ObjectReadingInstances,
        object: usize,
        c: &Control,
    ) -> Result<Self, ValidationFailure> {
        c.checkpoint(Checkpoint::ObjectEvaluation)?;
        readings.recheck(inputs, c).map_err(failure)?;
        let domain = ObjectDomain::from_readings(inputs, readings, object, c)?;
        let mut reading_span = None;
        for info in inputs.law().infos() {
            c.checkpoint(Checkpoint::ObjectEvaluation)?;
            if info.kind == "reading" && info.name == domain.identity.reading() {
                reading_span = Some(info.span);
            }
        }
        let reading_span = reading_span.ok_or(internal!("有限Law族の元reading位置がない"))?;
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
    pub(super) fn belongs_to(&self, readings: &ObjectReadingInstances) -> bool {
        &self.readings == readings
    }
    pub(super) fn has_reference_conditions(&self) -> bool {
        !self.reference_conditions.is_empty()
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
        c: &Control,
    ) -> Result<(), ValidationFailure> {
        let expected = Self::compute(inputs, &self.readings, self.object, c)?;
        if self != &expected {
            return Err(internal!("有限Law族の対象参照域が元構成と違う").into());
        }
        Ok(())
    }
}
impl FiniteLawFamilyValuations {
    pub(super) fn in_object<'a>(&self, mut environment: Environment<'a>) -> Environment<'a> {
        environment.indexes.object = self.object.as_ref().map(|o| Arc::clone(&o.domain));
        environment
    }
    /// 単一対象入口のidentity。列ごとの対象はcolumn_object_identityで読む。
    pub(in crate::observed) fn object_identity(&self) -> Option<&ObjectIdentity> {
        self.object.as_ref().map(|o| o.identity())
    }
    /// 単一対象入口の所属未観測位置。複数対象入口では列ごとの条件を読む。
    /// 各列の依存はそのScopeと未決状態で読む。
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
        c: &Control,
    ) -> Result<(), FiniteLawFamilyFailure> {
        let expected = Selection::compute(inputs, readings, object, c).map_err(|cause| {
            FiniteLawFamilyFailure {
                cause,
                partial: None,
            }
        })?;
        if self.object.as_deref() != Some(&expected) {
            return Err(FiniteLawFamilyFailure {
                cause: internal!("有限Law族が消費先の選択対象に由来しない").into(),
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
    c: &Control,
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
mod tests;

pub(in crate::observed) mod instances;

/// 各列の対象と、その空族にも残す元readings。
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct Columns {
    pub(super) readings: ObjectReadingInstances,
    pub(super) columns: Vec<Arc<Selection>>,
}
impl FiniteLawFamilyValuations {
    pub(super) fn select_column_object(
        &self,
        environment: &mut Environment<'_>,
        column: usize,
    ) -> Result<(), ValidationFailure> {
        let selection = match &self.column_objects {
            Some(objects) => Some(
                objects
                    .columns
                    .get(column)
                    .ok_or(internal!("有限Law列の対象がない"))?,
            ),
            None => self.object.as_ref(),
        };
        // Graphを読まない元ASTの評価でも、対象域は分析Contextの一部。
        // 対象を替えた列へ、同じ式・束縛の既存値を持ち越さない。
        if environment.indexes.object.as_deref() != selection.map(|object| object.domain.as_ref()) {
            environment.results.scoped_values.borrow_mut().clear();
        }
        environment.indexes.object = selection.map(|object| Arc::clone(&object.domain));
        Ok(())
    }
    pub(in crate::observed) fn column_object_identity(
        &self,
        column: usize,
    ) -> Option<&ObjectIdentity> {
        self.columns.get(column)?;
        match &self.column_objects {
            Some(objects) => objects.columns.get(column).map(|object| object.identity()),
            None => self.object_identity(),
        }
    }
    pub(in crate::observed) fn column_reference_domain_conditions(
        &self,
        column: usize,
    ) -> Option<&[Fact]> {
        self.columns.get(column)?;
        match &self.column_objects {
            Some(objects) => objects
                .columns
                .get(column)
                .map(|object| object.reference_conditions.as_slice()),
            None => Some(self.reference_domain_conditions()),
        }
    }
    pub(in crate::observed) fn recheck_on_objects(
        &self,
        inputs: &CheckedInputs,
        readings: &ObjectReadingInstances,
        objects: &[usize],
        c: &Control,
    ) -> Result<(), FiniteLawFamilyFailure> {
        let fail = |cause| FiniteLawFamilyFailure {
            cause,
            partial: None,
        };
        readings
            .recheck(inputs, c)
            .map_err(|cause| fail(failure(cause)))?;
        let Some(columns) = &self.column_objects else {
            return Err(fail(
                internal!("有限Law族が複数対象の選択に由来しない").into(),
            ));
        };
        if &columns.readings != readings || columns.columns.len() != objects.len() {
            return Err(fail(
                internal!("有限Law族の消費先readingsまたは対象列数が違う").into(),
            ));
        }
        for (selected, &object) in columns.columns.iter().zip(objects) {
            let expected = Selection::compute(inputs, readings, object, c).map_err(fail)?;
            if selected.as_ref() != &expected {
                return Err(fail(
                    internal!("有限Law列が消費先の対象に由来しない").into(),
                ));
            }
        }
        self.recheck(inputs, c)
    }
}
/// 完全束縛した元Law列を、列ごとの対象域と同じ原始代入Dで読む。
/// 全parameter軸の適用条件付き延長とは別の、型の合う完全束縛の族。
pub(in crate::observed) fn finite_multi_object_law_family_valuations(
    inputs: &CheckedInputs,
    readings: &ObjectReadingInstances,
    selected: &[(usize, String, Vec<(String, Scalar)>)],
    c: &Control,
) -> Result<FiniteLawFamilyValuations, FiniteLawFamilyFailure> {
    let (columns, laws) = multi_selection(inputs, readings, selected, c)?;
    family_with_column_objects(inputs, &laws, None, Some(columns), c)
}
fn multi_selection(
    inputs: &CheckedInputs,
    readings: &ObjectReadingInstances,
    selected: &[(usize, String, Vec<(String, Scalar)>)],
    c: &Control,
) -> Result<(Columns, Vec<(String, Vec<(String, Scalar)>)>), FiniteLawFamilyFailure> {
    readings
        .recheck(inputs, c)
        .map_err(|cause| FiniteLawFamilyFailure {
            cause: failure(cause),
            partial: None,
        })?;
    let mut domains = BTreeMap::new();
    let mut columns = Vec::new();
    let mut laws = Vec::new();
    for (object, law, bindings) in selected {
        c.checkpoint(Checkpoint::FiniteLawSelection)
            .map_err(|cause| FiniteLawFamilyFailure {
                cause: cause.into(),
                partial: None,
            })?;
        if !domains.contains_key(object) {
            let selection = Selection::compute(inputs, readings, *object, c).map_err(|cause| {
                FiniteLawFamilyFailure {
                    cause,
                    partial: None,
                }
            })?;
            domains.insert(*object, Arc::new(selection));
        }
        columns.push(Arc::clone(domains.get(object).ok_or_else(|| {
            FiniteLawFamilyFailure {
                cause: internal!("有限Law列の元対象域がない").into(),
                partial: None,
            }
        })?));
        laws.push((law.clone(), bindings.clone()));
    }
    Ok((
        Columns {
            readings: readings.clone(),
            columns,
        },
        laws,
    ))
}

#[cfg(test)]
mod multi_tests;

pub(in crate::observed) mod instance;
