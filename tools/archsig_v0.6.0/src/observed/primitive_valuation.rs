//! 元の原始表を保った、内部数学計算の型付き候補代入。
use super::*;
use crate::observed::control::CheckFailure;

impl<'a> Environment<'a> {
    /// 全候補の生成器が選んだ値を検査し、独立した式評価環境を作る。
    /// 通常のGraph/観測評価への登録や、Law成立の証拠の供給は行わない。
    pub(in crate::observed) fn with_primitive_valuation(
        inputs: &'a CheckedInputs,
        assignments: &[(Fact, Scalar)],
        control: &mut Control,
    ) -> Result<Self, ValidationFailure> {
        let mut environment = Self::new(inputs, control)?;
        control.checkpoint(Checkpoint::PrimitiveValuation)?;
        let mut types = std::collections::HashMap::new();
        for snapshot in &inputs.archmap().snapshots {
            control.checkpoint(Checkpoint::PrimitiveValuation)?;
            for subject in &snapshot.subjects {
                control.checkpoint(Checkpoint::PrimitiveValuation)?;
                types.insert(
                    (subject.snapshot.as_str(), subject.id.as_str()),
                    subject.ty.as_str(),
                );
            }
        }
        let roster = crate::archmap::value::Roster { types };
        let mut values = BTreeMap::new();
        let mut pinned = Vec::new();
        for (position, value) in assignments {
            control.checkpoint(Checkpoint::PrimitiveValuation)?;
            if position.atom.is_some() || position.field.is_none() || values.contains_key(position)
            {
                return Err("候補代入の位置が重複・fieldなし・観測Atom付きである".into());
            }
            let subject = environment.subject(&position.snapshot, &position.subject)?;
            let field = environment.field(
                &position.snapshot,
                &position.subject,
                position.field.as_deref().ok_or("候補代入のfieldがない")?,
            )?;
            if value.ty() != field.ty.erase() {
                return Err("候補代入の値と元fieldの型が違う".into());
            }
            data::check(value, inputs.law(), control)?;
            let encoded = data::input_json(value, control)?;
            let namespace = subject.ty.rsplit_once('.').map_or("", |(ns, _)| ns);
            let original =
                crate::archmap::value::check_assignment::<CheckFailure<Box<crate::issue::Issue>>>(
                    &encoded,
                    &field.ty,
                    inputs.definitions(),
                    &roster,
                    namespace,
                    control,
                )
                .map_err(|failure| match failure {
                    CheckFailure::Stopped(stop) => ValidationFailure::Stop(stop),
                    CheckFailure::Input(issue) => ValidationFailure::Internal(format!(
                        "候補代入が元fieldの条件を満たさない: {}",
                        issue.message
                    )),
                })?;
            let checked = scalar_from(&original, &field.ty, inputs.law(), control)?
                .ok_or("候補代入の原始値を読めない")?;
            if !same_primitive_value(value, &checked, control)? {
                return Err("候補代入が元encodingの正規値と違う".into());
            }
            pinned.push(crate::archmap::FieldAssignment {
                snapshot: position.snapshot.clone(),
                subject: position.subject.clone(),
                field: field.name.clone(),
                value: encoded,
            });
            values.insert(position.clone(), checked);
            control.checkpoint(Checkpoint::PrimitiveValuation)?;
        }
        crate::archmap::check_valuation_with_values::<CheckFailure<Box<crate::issue::Issue>>>(
            &inputs.archmap().snapshots,
            inputs.definitions(),
            &pinned,
            control,
        )
        .map_err(|failure| match failure {
            CheckFailure::Stopped(stop) => ValidationFailure::Stop(stop),
            CheckFailure::Input(issue) => ValidationFailure::Internal(format!(
                "候補代入が原始型・所属・Map全域性を満たさない: {}",
                issue.message
            )),
        })?;
        environment.primitive_valuation = Some(values);
        control.checkpoint(Checkpoint::PrimitiveValuation)?;
        Ok(environment)
    }
}

// Graphの保存状態比較は変更せず、原始値の往復だけでTermのsource位置を除く。
fn same_primitive_value(a: &Scalar, b: &Scalar, c: &Control) -> Result<bool, ValidationFailure> {
    stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
        c.clone().checkpoint(Checkpoint::PrimitiveValuation)?;
        fn items(a: &[Scalar], b: &[Scalar], c: &Control) -> Result<bool, ValidationFailure> {
            if a.len() != b.len() {
                return Ok(false);
            }
            for (a, b) in a.iter().zip(b) {
                if !same_primitive_value(a, b, c)? {
                    return Ok(false);
                }
            }
            Ok(true)
        }
        Ok(match (a, b) {
            (Scalar::Term(a), Scalar::Term(b)) => a.same_input_program(b, c)?,
            (Scalar::Tuple(a), Scalar::Tuple(b)) => items(a, b, c)?,
            (
                Scalar::List {
                    element: a,
                    items: p,
                },
                Scalar::List {
                    element: b,
                    items: q,
                },
            )
            | (
                Scalar::Set {
                    element: a,
                    items: p,
                },
                Scalar::Set {
                    element: b,
                    items: q,
                },
            ) => a == b && items(p, q, c)?,
            (
                Scalar::Option {
                    element: a,
                    value: p,
                },
                Scalar::Option {
                    element: b,
                    value: q,
                },
            ) => {
                a == b
                    && match (p, q) {
                        (None, None) => true,
                        (Some(a), Some(b)) => same_primitive_value(a, b, c)?,
                        _ => false,
                    }
            }
            (
                Scalar::Data {
                    family: a,
                    constructor: k,
                    args: p,
                },
                Scalar::Data {
                    family: b,
                    constructor: l,
                    args: q,
                },
            ) => a == b && k == l && items(p, q, c)?,
            _ => validation_identity::scalar(a, b, c)?,
        })
    })
}

#[cfg(test)]
#[path = "primitive_valuation_tests.rs"]
mod tests;
