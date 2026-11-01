//! 移行前のowner補完を独立差分試験にだけ残す。
use super::*;
/// 全整合補完で一つに定まったownerと、その列挙の原始支持。
/// 生成は現在の検査済み入力からの全列挙に限る。
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct DeterminedOwners {
    owners: Vec<(result::Fact, result::Fact)>,
    scope: result::Scope,
    support: Vec<result::Fact>,
}
impl DeterminedOwners {
    pub(crate) fn owners(&self) -> &[(result::Fact, result::Fact)] {
        &self.owners
    }
    pub(crate) fn scope(&self) -> &result::Scope {
        &self.scope
    }
    pub(crate) fn support(&self) -> &[result::Fact] {
        &self.support
    }
}
/// 返す値は観測Atomでも候補による更新でもない。
pub(crate) fn determined_owners(
    inputs: &crate::input::CheckedInputs,
    fields: &[result::Fact],
    control: &mut crate::control::Control,
) -> Result<Option<DeterminedOwners>, crate::construction::ConstructionFailure> {
    use crate::construction::ConstructionFailure;
    use result::{Scalar, ValidationFailure};
    if fields.is_empty()
        || fields.iter().any(|field| {
            field.atom.is_some()
                || !field.field.as_ref().is_some_and(|name| name.is_owner())
        })
    {
        return Err(ConstructionFailure::Inconsistent(
            "owner補完の元slotが違う".into(),
        ));
    }
    let env = environment::Environment::new(inputs, control)?;
    let all =
        env.completion_assignments(fields, &mut |_, _| {})
            .map_err(|failure| match failure {
                ValidationFailure::Stop(reason) => ConstructionFailure::Stopped(reason),
                other => {
                    ConstructionFailure::Inconsistent(format!("owner補完の構成検査: {other:?}"))
                }
            })?;
    if all.values.len() != 1 {
        return Ok(None);
    }
    let values = if fields.len() == 1 {
        vec![all.values[0].clone()]
    } else if let Scalar::Tuple(values) = &all.values[0] {
        values.clone()
    } else {
        return Err(ConstructionFailure::Inconsistent(
            "owner補完積の型が違う".into(),
        ));
    };
    if fields.len() != values.len() {
        return Err(ConstructionFailure::Inconsistent(
            "owner補完積の幅が違う".into(),
        ));
    }
    let mut owners = Vec::new();
    for (field, value) in fields.iter().zip(values) {
        control.checkpoint(crate::control::Checkpoint::Completion)?;
        let Scalar::Subject {
            snapshot, subject, ..
        } = &value
        else {
            return Err(ConstructionFailure::Inconsistent(
                "owner補完値が参照でない".into(),
            ));
        };
        owners.push((
            field.clone(),
            result::Fact {
                snapshot: snapshot.clone(),
                subject: subject.clone(),
                field: None,
                atom: None,
            },
        ));
    }
    let mut scope = all.scope;
    scope.completions = true;
    Ok(Some(DeterminedOwners {
        owners,
        scope,
        support: all.support,
    }))
}
