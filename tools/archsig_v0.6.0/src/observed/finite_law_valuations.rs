//! 固定した元Lawと束縛を、共有原始位置の有限候補上で読む。
use super::*;
use crate::law::model::{Declaration, Signature};
use crate::observed::{finite, input::InputSources};
use num_bigint::BigInt;
use std::sync::Arc;

#[derive(Clone, Debug, PartialEq, Eq)]
pub(in crate::observed) enum FiniteLawState {
    Pending,
    Ready,
    OutsideFinite { position: Fact, ty: Type },
    Undetermined { location: Location, reason: String },
    ConditionFailed,
    Unavailable { location: Location, feature: String },
}
#[derive(Clone, PartialEq, Eq)]
pub(in crate::observed) struct FiniteLawRow {
    pub point: usize,
    pub guard: Option<bool>,
    pub predicate: Option<bool>,
    pub operands: Option<(Type, Option<Scalar>, Option<Scalar>)>,
    pub indicator: Option<BigInt>,
    pub condition_failed: bool,
    pub support: Vec<Fact>,
    pub scope: Scope,
}
#[derive(Clone)]
struct Selection {
    law: String,
    bindings: Vec<(String, Scalar)>,
}
pub(in crate::observed) struct FiniteLawValuations {
    sources: InputSources,
    selection: Arc<Selection>,
    declaration: Declaration,
    bindings: Vec<(String, Scalar)>,
    positions: Vec<Fact>,
    types: Vec<Type>,
    domain: Vec<Vec<Scalar>>,
    domain_complete: bool,
    observed_point: Option<usize>,
    rows: Vec<FiniteLawRow>,
    state: FiniteLawState,
}
pub(in crate::observed) struct FiniteLawFailure {
    pub cause: ValidationFailure,
    pub partial: Option<Box<FiniteLawValuations>>,
}
impl std::fmt::Debug for FiniteLawFailure {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("FiniteLawFailure")
            .field("cause", &self.cause)
            .field("has_partial", &self.partial.is_some())
            .finish()
    }
}
fn tick(c: &Control) -> Result<(), ValidationFailure> {
    c.clone().checkpoint(Checkpoint::FiniteLawDomain)?;
    Ok(())
}
fn source(value: Scalar) -> SourceValue {
    SourceValue {
        condition_failed: false,
        condition_pending: false,
        symbolic: None,
        comparison: None,
        affine: None,
        scope: Scope::default(),
        known_value: Some(value),
        support: vec![],
        scalar_scope: Some(Scope::default()),
    }
}
impl FiniteLawValuations {
    pub fn declaration(&self) -> &Declaration {
        &self.declaration
    }
    pub fn bindings(&self) -> &[(String, Scalar)] {
        &self.bindings
    }
    pub fn positions(&self) -> &[Fact] {
        &self.positions
    }
    pub fn types(&self) -> &[Type] {
        &self.types
    }
    pub fn domain(&self) -> &[Vec<Scalar>] {
        &self.domain
    }
    pub fn domain_complete(&self) -> bool {
        self.domain_complete
    }
    pub fn observed_point(&self) -> Option<usize> {
        self.observed_point
    }
    pub fn rows(&self) -> &[FiniteLawRow] {
        &self.rows
    }
    pub fn state(&self) -> &FiniteLawState {
        &self.state
    }
    pub fn is_complete(&self) -> bool {
        self.state == FiniteLawState::Ready
    }
    pub fn recheck(&self, inputs: &CheckedInputs, c: &mut Control) -> Result<(), FiniteLawFailure> {
        let fail = |message: &str| FiniteLawFailure {
            cause: message.into(),
            partial: None,
        };
        if &self.sources != inputs.sources() {
            return Err(fail("有限Law表の元三入力が違う"));
        }
        let expected =
            finite_law_valuations(inputs, &self.selection.law, &self.selection.bindings, c)?;
        let result = (|| -> Result<bool, ValidationFailure> {
            tick(c)?;
            if self.declaration != expected.declaration
                || self.positions != expected.positions
                || self.types != expected.types
                || self.domain_complete != expected.domain_complete
                || self.observed_point != expected.observed_point
                || self.state != expected.state
                || self.bindings.len() != expected.bindings.len()
                || self.domain.len() != expected.domain.len()
                || self.rows.len() != expected.rows.len()
            {
                return Ok(false);
            }
            for ((n, a), (m, b)) in self.bindings.iter().zip(&expected.bindings) {
                tick(c)?;
                if n != m || !validation_identity::scalar(a, b, c)? {
                    return Ok(false);
                }
            }
            for (a, b) in self.domain.iter().zip(&expected.domain) {
                tick(c)?;
                if a.len() != b.len() {
                    return Ok(false);
                }
                for (a, b) in a.iter().zip(b) {
                    if !validation_identity::scalar(a, b, c)? {
                        return Ok(false);
                    }
                }
            }
            for (a, b) in self.rows.iter().zip(&expected.rows) {
                tick(c)?;
                if a != b {
                    return Ok(false);
                }
            }
            tick(c)?;
            Ok(true)
        })();
        match result {
            Ok(true) => Ok(()),
            other => Err(FiniteLawFailure {
                cause: other
                    .err()
                    .unwrap_or_else(|| "有限Law表が元宣言・束縛・全候補・元評価と違う".into()),
                partial: Some(Box::new(expected)),
            }),
        }
    }
}

pub(in crate::observed) fn finite_law_valuations(
    inputs: &CheckedInputs,
    law: &str,
    bindings: &[(String, Scalar)],
    c: &mut Control,
) -> Result<FiniteLawValuations, FiniteLawFailure> {
    let decl = inputs
        .law()
        .declarations
        .get(law)
        .ok_or_else(|| FiniteLawFailure {
            cause: "有限Lawの元宣言がない".into(),
            partial: None,
        })?;
    if !matches!(decl.signature, Signature::Law { .. }) {
        return Err(FiniteLawFailure {
            cause: "有限Lawの選択がLawでない".into(),
            partial: None,
        });
    }
    let mut result = FiniteLawValuations {
        sources: inputs.sources().clone(),
        selection: Arc::new(Selection {
            law: law.into(),
            bindings: bindings.to_vec(),
        }),
        declaration: decl.clone(),
        bindings: vec![],
        positions: vec![],
        types: vec![],
        domain: vec![],
        domain_complete: false,
        observed_point: None,
        rows: vec![],
        state: FiniteLawState::Pending,
    };
    match populate(inputs, bindings, &mut result, c) {
        Ok(()) => Ok(result),
        Err(cause) => Err(FiniteLawFailure {
            cause,
            partial: Some(Box::new(result)),
        }),
    }
}
fn validate_bindings(
    e: &Environment<'_>,
    decl: &Declaration,
    supplied: &[(String, Scalar)],
) -> Result<Vec<(String, Scalar)>, ValidationFailure> {
    let Signature::Law { params, .. } = &decl.signature else {
        return Err("元Law署名がない".into());
    };
    let mut named = BTreeMap::new();
    for (name, value) in supplied {
        tick(&e.control)?;
        if named.insert(name.as_str(), value).is_some() {
            return Err("有限Lawの束縛名が重複する".into());
        }
    }
    if named.len() != params.len() {
        return Err("有限Lawの完全束縛と元署名の個数が違う".into());
    }
    let mut result = vec![];
    for p in params {
        tick(&e.control)?;
        let value = named
            .remove(p.name.as_str())
            .ok_or("有限Lawの元parameterが未束縛")?;
        if value.ty() != p.ty.erase() {
            return Err("有限Lawの束縛型が元parameterと違う".into());
        }
        data::check(value, e.inputs.law(), &e.control)?;
        let mut pending = vec![value];
        while let Some(v) = pending.pop() {
            tick(&e.control)?;
            match v {
                Scalar::Subject {
                    snapshot,
                    subject,
                    entity,
                } => {
                    if e.subject(snapshot, subject)?.ty != *entity {
                        return Err("有限Lawの参照束縛が登録型と違う".into());
                    }
                }
                Scalar::Tuple(v)
                | Scalar::List { items: v, .. }
                | Scalar::Set { items: v, .. }
                | Scalar::Data { args: v, .. } => pending.extend(v),
                Scalar::Option { value: Some(v), .. } => pending.push(v),
                Scalar::Map { pairs, .. } => {
                    for (a, b) in pairs {
                        pending.extend([a, b]);
                    }
                }
                _ => {}
            }
        }
        result.push((p.name.clone(), value.clone()));
    }
    if !named.is_empty() {
        return Err("有限Lawに未知の束縛がある".into());
    }
    Ok(result)
}
fn type_dependencies(
    e: &Environment<'_>,
    position: &Fact,
    ty: &Type,
    found: &mut BTreeSet<Fact>,
) -> Result<(), ValidationFailure> {
    let mut pending = vec![ty.clone()];
    let mut data_seen = BTreeSet::new();
    while let Some(ty) = pending.pop() {
        tick(&e.control)?;
        match &ty {
            Type::Owned(entity, name) => {
                let holder = e.subject(&position.snapshot, &position.subject)?;
                let field = e.field(
                    &holder.snapshot,
                    &holder.id,
                    &format!("{}.{}", holder.ty, name),
                )?;
                found.insert(Fact {
                    snapshot: holder.snapshot.clone(),
                    subject: holder.id.clone(),
                    field: Some(field.name.clone()),
                    atom: None,
                });
                for s in e.subjects.values().filter(|s| s.ty == *entity) {
                    tick(&e.control)?;
                    let field = e.field(&s.snapshot, &s.id, &format!("{}.owner", s.ty))?;
                    found.insert(Fact {
                        snapshot: s.snapshot.clone(),
                        subject: s.id.clone(),
                        field: Some(field.name.clone()),
                        atom: None,
                    });
                }
            }
            Type::Tuple(items) => pending.extend(items.iter().cloned()),
            Type::List(t) | Type::Set(t) | Type::Option(t) => pending.push((**t).clone()),
            Type::Map(a, b) => pending.extend([(**a).clone(), (**b).clone()]),
            Type::Data(family) if data_seen.insert(family.clone()) => {
                for ctor in data::constructors(e.inputs.law(), &family)? {
                    pending.extend(ctor.arguments.iter().cloned());
                }
            }
            _ => {}
        }
    }
    Ok(())
}
fn domains(
    e: &Environment<'_>,
    positions: &[Fact],
) -> Result<Option<(Vec<Type>, Vec<Vec<Scalar>>)>, ValidationFailure> {
    let mut types = vec![];
    let mut product = vec![vec![]];
    for position in positions {
        tick(&e.control)?;
        let field = e.field(
            &position.snapshot,
            &position.subject,
            position
                .field
                .as_deref()
                .ok_or("有限Law位置のfieldがない")?,
        )?;
        let domain = finite::field_candidates_if_finite(
            &field.ty.erase(),
            e.inputs.law(),
            &e.control,
            &mut |entity| {
                let mut out = finite::Enumeration::default();
                for s in e.subjects.values().filter(|s| s.ty == entity) {
                    tick(&e.control)?;
                    out.values.push(Scalar::Subject {
                        snapshot: s.snapshot.clone(),
                        subject: s.id.clone(),
                        entity: s.ty.clone(),
                    });
                    out.support.push(Fact {
                        snapshot: s.snapshot.clone(),
                        subject: s.id.clone(),
                        field: None,
                        atom: None,
                    });
                }
                Ok(out)
            },
        )?;
        let Some(domain) = domain else {
            return Ok(None);
        };
        types.push(field.ty.clone());
        let mut next = vec![];
        for row in &product {
            for value in &domain.enumeration.values {
                tick(&e.control)?;
                let mut candidate = row.clone();
                candidate.push(value.clone());
                next.push(candidate);
                tick(&e.control)?;
            }
        }
        product = next;
    }
    Ok(Some((types, product)))
}
struct Probe {
    row: FiniteLawRow,
    admissible: bool,
    blocked: bool,
}
fn probe(
    e: &Environment<'_>,
    decl: &Declaration,
    bindings: &[(String, Scalar)],
    point: usize,
) -> Result<Probe, ValidationFailure> {
    let Signature::Law {
        params,
        guard,
        body,
        ..
    } = &decl.signature
    else {
        return Err("元Law署名がない".into());
    };
    let vars = bindings
        .iter()
        .map(|(n, v)| (n.clone(), source(v.clone())))
        .collect::<BTreeMap<_, _>>();
    let mut values = BTreeMap::new();
    let mut checks = owned_call::Checks::default();
    for (p, (_, v)) in params.iter().zip(bindings) {
        tick(&e.control)?;
        e.owned_call_value_check(
            &p.ty,
            &super::super::term::affine::Value::Known(v.clone()),
            &values,
            &decl.reading,
            decl.span,
            &mut checks,
        )?;
        values.insert(p.name.as_str(), Some(v));
    }
    let mut row = FiniteLawRow {
        point,
        guard: None,
        predicate: None,
        operands: None,
        indicator: None,
        condition_failed: false,
        support: checks.support,
        scope: checks.scope,
    };
    if checks.failure.is_some() || checks.blocked {
        return Ok(Probe {
            row,
            admissible: checks.failure.is_none(),
            blocked: checks.blocked,
        });
    }
    let mut scope = Scope::default();
    scope.readings.insert(decl.reading.clone());
    let g = match guard {
        Some(id) => Some(e.scoped_ast(*id, &vars, &scope, &decl.reading)?),
        None => None,
    };
    let b = e.scoped_ast(*body, &vars, &scope, &decl.reading)?;
    row.guard = match &g {
        None => Some(true),
        Some(g) => match &g.known_value {
            Some(Scalar::Bool(v)) => Some(*v),
            None => None,
            _ => return Err("元Law guardがBoolでない".into()),
        },
    };
    row.predicate = match &b.known_value {
        Some(Scalar::Bool(v)) => Some(*v),
        None => None,
        _ => return Err("元Law述語がBoolでない".into()),
    };
    let mut equality = *body;
    while let ExprKind::Group(child) = e.inputs.law().exprs[equality].kind {
        tick(&e.control)?;
        equality = child;
    }
    if let ExprKind::Binary {
        op: BinOp::Eq,
        lhs,
        rhs,
    } = &e.inputs.law().exprs[equality].kind
    {
        let a = e.scoped_ast(*lhs, &vars, &scope, &decl.reading)?;
        let b = e.scoped_ast(*rhs, &vars, &scope, &decl.reading)?;
        row.operands = Some((
            e.inputs
                .law()
                .expr_type(*lhs)
                .ok_or("元等式の型がない")?
                .clone(),
            a.known_value,
            b.known_value,
        ));
        row.support.extend(a.support);
        row.support.extend(b.support);
        row.scope.merge(&a.scope);
        row.scope.merge(&b.scope);
        row.condition_failed |= a.condition_failed || b.condition_failed;
    }
    for v in g.iter().chain(std::iter::once(&b)) {
        row.support.extend(v.support.iter().cloned());
        row.scope.merge(&v.scope);
        row.condition_failed |= v.condition_failed;
    }
    row.support.sort();
    row.support.dedup();
    if !row.condition_failed {
        if let (Some(g), Some(p)) = (row.guard, row.predicate) {
            row.indicator = Some(BigInt::from((g && !p) as u8));
        }
    }
    Ok(Probe {
        row,
        admissible: true,
        blocked: false,
    })
}
fn populate(
    inputs: &CheckedInputs,
    supplied: &[(String, Scalar)],
    r: &mut FiniteLawValuations,
    c: &mut Control,
) -> Result<(), ValidationFailure> {
    tick(c)?;
    let template = Environment::new(inputs, c)?;
    r.bindings = validate_bindings(&template, &r.declaration, supplied)?;
    let mut positions: BTreeSet<Fact> = BTreeSet::new();
    loop {
        tick(c)?;
        loop {
            let mut expanded = positions.clone();
            for p in &positions {
                let f = template.field(
                    &p.snapshot,
                    &p.subject,
                    p.field.as_deref().ok_or("有限Law fieldがない")?,
                )?;
                type_dependencies(&template, p, &f.ty, &mut expanded)?;
            }
            if expanded == positions {
                break;
            }
            positions = expanded;
        }
        r.positions = positions.iter().cloned().collect();
        let Some((types, candidates)) = domains(&template, &r.positions)? else {
            // 個々の位置を再走査して、列挙できない元位置・型を保持する。
            for p in &r.positions {
                if domains(&template, std::slice::from_ref(p))?.is_none() {
                    let f = template.field(
                        &p.snapshot,
                        &p.subject,
                        p.field.as_deref().ok_or("finite fieldがない")?,
                    )?;
                    r.state = FiniteLawState::OutsideFinite {
                        position: p.clone(),
                        ty: f.ty.clone(),
                    };
                    return Ok(());
                }
            }
            return Err("有限Law域の非有限位置を特定できない".into());
        };
        let mut discovered = positions.clone();
        let mut admissible = vec![];
        let mut blocked = false;
        for candidate in candidates {
            tick(c)?;
            let values = r
                .positions
                .iter()
                .cloned()
                .zip(candidate.iter().cloned())
                .collect::<Vec<_>>();
            let Some(e) = Environment::try_primitive_valuation(inputs, &values, c)? else {
                continue;
            };
            *e.primitive_reads.borrow_mut() = Some(BTreeSet::new());
            let result = probe(&e, &r.declaration, &r.bindings, 0);
            if let Some(reads) = e.primitive_reads.borrow().as_ref() {
                discovered.extend(reads.iter().cloned());
            }
            match result {
                Ok(p) => {
                    blocked |= p.blocked;
                    if p.admissible && !p.blocked {
                        admissible.push(candidate)
                    }
                }
                Err(ValidationFailure::UnsupportedExpression { location, feature }) => {
                    r.state = FiniteLawState::Unavailable { location, feature };
                    return Ok(());
                }
                Err(f) => return Err(f),
            }
            tick(c)?;
        }
        if discovered != positions {
            positions = discovered;
            continue;
        }
        if blocked {
            r.state = FiniteLawState::Undetermined {
                location: Location::Law {
                    span: r.declaration.span,
                },
                reason: "元の完全束縛の所属条件が未決".into(),
            };
            return Ok(());
        }
        r.types = types;
        r.domain = admissible;
        r.domain_complete = true;
        tick(c)?;
        break;
    }
    let mut observed = vec![];
    let mut all_known = true;
    for p in &r.positions {
        tick(c)?;
        let f = template.field(
            &p.snapshot,
            &p.subject,
            p.field.as_deref().ok_or("元fieldがない")?,
        )?;
        match &f.slot {
            Slot::Known { value, .. } => observed
                .push(scalar_from(value, &f.ty, inputs.law(), c)?.ok_or("元原始値が読めない")?),
            Slot::Missing => all_known = false,
        }
    }
    if all_known {
        for (i, point) in r.domain.iter().enumerate() {
            tick(c)?;
            let mut equal = point.len() == observed.len();
            for (a, b) in point.iter().zip(&observed) {
                equal &= data::equal(a, b, c)?;
            }
            if equal {
                if r.observed_point.replace(i).is_some() {
                    return Err("元観測点が有限域で重複する".into());
                }
            }
        }
    }
    for (point, candidate) in r.domain.iter().enumerate() {
        c.checkpoint(Checkpoint::FiniteLawEvaluation)?;
        let values = r
            .positions
            .iter()
            .cloned()
            .zip(candidate.iter().cloned())
            .collect::<Vec<_>>();
        let e = Environment::with_primitive_valuation(inputs, &values, c)?;
        let p = probe(&e, &r.declaration, &r.bindings, point)?;
        if !p.admissible || p.blocked {
            return Err("完成Dの元束縛条件が変わった".into());
        }
        r.rows.push(p.row);
        c.checkpoint(Checkpoint::FiniteLawEvaluation)?;
    }
    c.checkpoint(Checkpoint::FiniteLawEvaluation)?;
    r.state = if r.rows.iter().any(|p| p.condition_failed) {
        FiniteLawState::ConditionFailed
    } else if r.rows.iter().any(|p| p.indicator.is_none()) {
        FiniteLawState::Undetermined {
            location: Location::Law {
                span: r.declaration.span,
            },
            reason: "元guardまたは述語の値が未決".into(),
        }
    } else {
        FiniteLawState::Ready
    };
    Ok(())
}

#[cfg(test)]
#[path = "finite_law_valuations_tests.rs"]
mod tests;
