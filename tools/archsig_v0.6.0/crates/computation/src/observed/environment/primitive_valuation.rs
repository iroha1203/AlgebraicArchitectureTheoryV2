//! 元の原始表を保った、内部数学計算の型付き候補代入。
use super::*;
use archsig_common::control::CheckFailure;

impl<'a> Environment<'a> {
    /// 全候補の生成器が選んだ値を検査し、独立した式評価環境を作る。
    /// 通常のGraph/観測評価への登録や、Law成立の証拠の供給は行わない。
    pub(in crate::observed) fn with_primitive_valuation(
        inputs: &'a CheckedInputs,
        assignments: &[(Fact, Scalar)],
        control: &Control,
    ) -> Result<Self, ValidationFailure> {
        Self::try_primitive_valuation(inputs, assignments, control)?
            .ok_or_else(|| internal!("候補代入が原始型・所属・Map全域性を満たさない").into())
    }

    /// 型の正しい候補のうち、原始制約に適合する点だけを返す。停止/不正値は黙殺しない。
    pub(in crate::observed) fn try_primitive_valuation(
        inputs: &'a CheckedInputs,
        assignments: &[(Fact, Scalar)],
        control: &Control,
    ) -> Result<Option<Self>, ValidationFailure> {
        Self::primitive_valuation_on(Self::new(inputs, control)?, assignments, control, true)
    }

    /// 依存位置の発見中は、まだ固定されている別fieldとの制約で枝を刈らない。
    /// 元型・値の正規性は検査する。完成候補にはtry_primitive_valuation_fromを使う。
    pub(super) fn primitive_dependency_probe_from(
        &self,
        assignments: &[(Fact, Scalar)],
        control: &Control,
    ) -> Result<Self, ValidationFailure> {
        Self::primitive_valuation_on(self.fresh_candidate(control), assignments, control, false)?
            .ok_or_else(|| internal!("依存発見用の型付き候補が失われた").into())
    }

    pub(in crate::observed) fn try_primitive_valuation_from(
        &self,
        assignments: &[(Fact, Scalar)],
        control: &Control,
    ) -> Result<Option<Self>, ValidationFailure> {
        Self::primitive_valuation_on(self.fresh_candidate(control), assignments, control, true)
    }

    fn fresh_candidate(&self, control: &Control) -> Self {
        Self {
            indexes: self.indexes.fresh(),
            results: ResultStore::default(),
            state: EvaluationState::default(),
            control: control.clone(),
        }
    }

    fn primitive_valuation_on(
        mut environment: Self,
        assignments: &[(Fact, Scalar)],
        control: &Control,
        constraints: bool,
    ) -> Result<Option<Self>, ValidationFailure> {
        let inputs = environment.indexes.inputs;
        control.checkpoint(Checkpoint::PrimitiveValuation)?;
        let roster = &environment.indexes.roster;
        let mut values = BTreeMap::new();
        let mut original_values = BTreeMap::new();
        let mut pinned = Vec::new();
        let mut structurally_neutral = true;
        for (position, value) in assignments {
            control.checkpoint(Checkpoint::PrimitiveValuation)?;
            if position.atom.is_some() || position.field.is_none() || values.contains_key(position)
            {
                return Err(
                    internal!("候補代入の位置が重複・fieldなし・観測Atom付きである").into(),
                );
            }
            let subject = environment
                .indexes
                .subject(&position.snapshot, &position.subject)?;
            let field = environment.indexes.field(
                &environment.state,
                &position.snapshot,
                &position.subject,
                position
                    .field
                    .as_deref()
                    .ok_or(internal!("候補代入のfieldがない"))?,
            )?;
            if value.ty() != field.ty.erase() {
                return Err(internal!("候補代入の値と元fieldの型が違う").into());
            }
            data::check(value, inputs.law(), control)?;
            let encoded = data::input_json(value, control)?;
            let namespace = subject.ty.namespace();
            let original = archsig_input::archmap::value::check_assignment::<
                CheckFailure<Box<archsig_common::issue::Issue>>,
            >(
                &encoded,
                &field.ty,
                inputs.definitions(),
                roster,
                namespace,
                control,
            )
            .map_err(|failure| match failure {
                CheckFailure::Stopped(stop) => ValidationFailure::Stop(stop),
                CheckFailure::Input(issue) => ValidationFailure::Internal(internal!(
                    "候補代入が元fieldの条件を満たさない: {}",
                    issue.message
                )),
            })?;
            let checked = scalar_from(&original, &field.ty, inputs.law(), control)?
                .ok_or(internal!("候補代入の原始値を読めない"))?;
            if !same_primitive_value(value, &checked, control)? {
                return Err(internal!("候補代入が元encodingの正規値と違う").into());
            }
            if constraints && structurally_neutral {
                structurally_neutral = structural_neutral_value(&original, control)?;
            }
            if constraints {
                pinned.push((position, &field.name, encoded));
            }
            original_values.insert(position.clone(), original);
            values.insert(position.clone(), checked);
            control.checkpoint(Checkpoint::PrimitiveValuation)?;
        }
        // CheckedInputsには元の補完がある。Ref/Mapを含まない型検査済みpinは
        // 参照変数・owner読取りを変えず、元fieldの制約を除くだけなので再探索しない。
        if constraints && !structurally_neutral {
            let mut checked_pins = Vec::with_capacity(pinned.len());
            for (position, field, value) in pinned {
                control.checkpoint(Checkpoint::PrimitiveValuation)?;
                checked_pins.push(archsig_input::archmap::FieldAssignment {
                    snapshot: position.snapshot.clone(),
                    subject: position.subject.clone(),
                    field: field.to_string(),
                    value,
                });
            }
            match archsig_input::archmap::check_valuation_with_values::<
                CheckFailure<Box<archsig_common::issue::Issue>>,
            >(
                &inputs.archmap().snapshots(),
                inputs.definitions(),
                &checked_pins,
                control,
            ) {
                Ok(()) => {}
                Err(CheckFailure::Stopped(stop)) => return Err(ValidationFailure::Stop(stop)),
                Err(CheckFailure::Input(issue))
                    if issue.code == archsig_common::issue::Code::InconsistentObservation =>
                {
                    return Ok(None);
                }
                Err(CheckFailure::Input(issue)) => {
                    return Err(ValidationFailure::Internal(internal!(
                        "候補の原始制約検査: {}",
                        issue.message
                    )));
                }
            }
        }
        environment.indexes.primitive_valuation = Some(values);
        environment.indexes.primitive_input_valuation = Some(original_values);
        control.checkpoint(Checkpoint::PrimitiveValuation)?;
        Ok(Some(environment))
    }
}

/// collect_knownがMember/Coverを作らず、slot_refも変えない原始値。
/// 元CheckedInputsの補完存在を使う呼出しだけに適用する。Termは保守的に再検査する。
fn structural_neutral_value(value: &Value, c: &Control) -> Result<bool, ValidationFailure> {
    let mut pending = vec![value];
    while let Some(value) = pending.pop() {
        c.checkpoint(Checkpoint::PrimitiveValuation)?;
        match value {
            Value::Unit
            | Value::Bool(_)
            | Value::Z(_)
            | Value::Q(..)
            | Value::Fp(_)
            | Value::Text(_)
            | Value::Option(None) => {}
            Value::Tuple(items)
            | Value::List(items)
            | Value::Set(items)
            | Value::Data { args: items, .. } => {
                for item in items {
                    c.checkpoint(Checkpoint::PrimitiveValuation)?;
                    pending.push(item);
                }
            }
            Value::Option(Some(value)) => pending.push(value),
            // 空MapにもCoverがあり、参照leafの有無だけでは中立といえない。
            Value::Ref { .. } | Value::Map(_) | Value::Term(_) => return Ok(false),
        }
    }
    c.checkpoint(Checkpoint::PrimitiveValuation)?;
    Ok(true)
}

// Graphの保存状態比較は変更せず、原始値の往復だけでTermのsource位置を除く。
fn same_primitive_value(a: &Scalar, b: &Scalar, c: &Control) -> Result<bool, ValidationFailure> {
    stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
        c.checkpoint(Checkpoint::PrimitiveValuation)?;
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
mod tests;

#[cfg(test)]
mod candidate_path_tests;
