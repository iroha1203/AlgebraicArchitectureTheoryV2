//! 元の有限parameter域と全行の実評価から、Law族の判断を保持する。
use super::{
    construction_result::{ArchitectureWitness, ConstructionData as D, ConstructionValue, Witness},
    control::{Checkpoint, Control},
    environment::Environment,
    law_evaluation as frames,
    polynomial_law_diagram::FamilyInputs,
    result::*,
};
use crate::{canonical::Json, issue::Location, types::Type};
use std::{collections::BTreeMap, sync::Arc};
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Row {
    pub law: NodeRef,
    pub evaluation: NodeRef,
    pub proposition: NodeRef,
}
impl Row {
    fn arguments(&self) -> [NodeRef; 3] {
        [self.law, self.evaluation, self.proposition]
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Kind {
    Member {
        position: usize,
        values: Vec<NodeRef>,
        scalar: Scalar,
        wire: Json,
    },
    Domain {
        members: Vec<NodeRef>,
    },
    Value {
        domain: NodeRef,
        rows: Vec<Row>,
        scalar: Scalar,
    },
    Evaluation {
        domain: NodeRef,
        rows: Vec<Row>,
        value: Option<NodeRef>,
    },
    Exhaustion {
        evaluation: NodeRef,
    },
    Proposition {
        evaluation: NodeRef,
        evidence: Vec<NodeRef>,
    },
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Data {
    pub template: NodeRef,
    pub architecture: NodeRef,
    pub parameters: Vec<NodeRef>,
    pub kind: Kind,
    pub wire: Json,
    pub support: Vec<Fact>,
    pub scope: Scope,
    pub reasons: Vec<Reason>,
    pub evidence: Vec<NodeRef>,
    pub judgment: Option<Judgment>,
}
impl Data {
    pub fn scalar(&self) -> Option<&Scalar> {
        match &self.kind {
            Kind::Member { scalar, .. } | Kind::Value { scalar, .. } => Some(scalar),
            _ => None,
        }
    }
    pub fn ty(&self) -> NodeType {
        match &self.kind {
            Kind::Member { scalar, .. } => NodeType::Value(scalar.ty()),
            Kind::Domain { .. } => NodeType::Domain,
            Kind::Value { .. } => NodeType::Value(Type::Bool),
            Kind::Evaluation { .. } => NodeType::Evaluation(Type::Bool),
            Kind::Exhaustion { .. } => NodeType::Evidence,
            Kind::Proposition { .. } => NodeType::Proposition,
        }
    }
    pub fn construction(&self) -> &'static str {
        match self.kind {
            Kind::Member { .. } => "binding",
            Kind::Domain { .. } => "domain",
            Kind::Value { .. } | Kind::Evaluation { .. } => "evaluation",
            Kind::Exhaustion { .. } => "evidence",
            Kind::Proposition { .. } => "proposition",
        }
    }
    pub fn arguments(&self) -> Vec<NodeRef> {
        let mut a = vec![self.template, self.architecture];
        a.extend(&self.parameters);
        match &self.kind {
            Kind::Member { values, .. } => a.extend(values),
            Kind::Domain { members } => a.extend(members),
            Kind::Value { domain, rows, .. } | Kind::Evaluation { domain, rows, .. } => {
                a.push(*domain);
                for r in rows {
                    a.extend(r.arguments())
                }
            }
            Kind::Exhaustion { evaluation } | Kind::Proposition { evaluation, .. } => {
                a.push(*evaluation)
            }
        }
        if let Kind::Evaluation { value: Some(v), .. } = &self.kind {
            a.push(*v)
        }
        if let Kind::Proposition { evidence, .. } = &self.kind {
            a.extend(evidence)
        }
        a
    }
    pub fn position(&self, limit: usize) -> Result<(), ValidationFailure> {
        if self.arguments().iter().any(|r| r.0 >= limit) {
            return Err("元Law族の依存が既出Refでない".into());
        }
        Ok(())
    }
    pub fn wire(&self) -> Json {
        self.wire.clone()
    }
}
fn tick(c: &mut Control) -> Result<(), ValidationFailure> {
    c.checkpoint(Checkpoint::ObjectEvaluation)?;
    Ok(())
}
fn plan(
    g: &Graph,
    template: NodeRef,
    architecture: NodeRef,
) -> Result<Option<FamilyInputs>, ValidationFailure> {
    let Some(Payload::Construction(v)) = &g.get(template)?.payload else {
        return Err("元Law族templateがnativeでない".into());
    };
    let D::PolynomialLaw(d) = &v.data else {
        return Err("元Law族templateが元の記号的Lawでない".into());
    };
    let Some(p) = d.family_inputs(template)? else {
        return Ok(None);
    };
    if p.template.parameters != p.base.parameters {
        return Err("元Law族の元parameter宣言順が違う".into());
    }
    for r in p.base_rows.iter().chain(&p.target_rows) {
        let row = frames::origin(g, *r)?.ok_or("元Law族の完全行に由来がない")?;
        if !row.ready && !row.outside {
            return Ok(None);
        }
    }
    let origin = frames::origin(g, template)?.ok_or("元Law族の原式がない")?;
    frames::check_architecture(g, architecture, &origin)?;
    if p.target_rows.is_empty() && !p.base_rows.is_empty() && !origin.outside {
        return Ok(None);
    }

    let context = g.context_at(template.0);
    if context != g.context_at(architecture.0) {
        return Err("元Law族のRequest Contextが違う".into());
    }
    Ok(Some(p))
}
fn coordinates(g: &Graph, p: &FamilyInputs) -> Result<Vec<Vec<NodeRef>>, ValidationFailure> {
    let mut keys = vec![vec![]];
    for parameter in &p.parameters {
        g.tick()?;
        g.expect(parameter.reference, &NodeType::Domain)?;
        let mut next = vec![];
        for prefix in &keys {
            for &value in &parameter.values {
                g.tick()?;
                g.expect(value, &NodeType::Value(parameter.ty.clone()))?;
                let mut k = prefix.clone();
                k.push(value);
                next.push(k)
            }
        }
        keys = next;
    }
    if keys.len() != p.base_rows.len() {
        return Err("元Law族の全直積とbase実row数が違う".into());
    }
    for (key, r) in keys.iter().zip(&p.base_rows) {
        let b = frames::origin(g, *r)?.ok_or("元Law族のbase実rowがない")?;
        if !b.ready || b.object != 0 || !Arc::ptr_eq(&b.architecture, &p.architecture) {
            return Err("元Law族のbase行が完全束縛でない".into());
        }
        matching(g, p, key, &b.bindings)?;
    }
    Ok(keys)
}
fn matching(
    g: &Graph,
    p: &FamilyInputs,
    key: &[NodeRef],
    bindings: &[Binding],
) -> Result<(), ValidationFailure> {
    if bindings.len() != p.template.bindings.len() + p.parameters.len() {
        return Err("元Law族の全parameter数が違う".into());
    }
    for fixed in &p.template.bindings {
        g.tick()?;
        let candidates = bindings
            .iter()
            .filter(|b| b.name == fixed.name)
            .collect::<Vec<_>>();
        let [actual] = candidates.as_slice() else {
            return Err("元Law族の固定束縛が欠落/重複".into());
        };
        if actual.ty != fixed.ty || g.scalar(actual.value)? != g.scalar(fixed.value)? {
            return Err("元Law族の固定束縛が違う".into());
        }
    }
    for (parameter, value) in p.parameters.iter().zip(key) {
        g.tick()?;
        let matches = bindings
            .iter()
            .filter(|b| b.name == parameter.name)
            .collect::<Vec<_>>();
        let [actual] = matches.as_slice() else {
            return Err("元Law族の残parameterが欠落/重複".into());
        };
        if actual.ty != parameter.ty || g.scalar(actual.value)? != g.scalar(*value)? {
            return Err("元Law族の直積順・値・型が違う".into());
        }
    }
    Ok(())
}
fn same(g: &Graph, d: &Data, r: NodeRef) -> Result<Data, ValidationFailure> {
    let Some(Payload::Construction(v)) = &g.get(r)?.payload else {
        return Err("元Law族の依存がnativeでない".into());
    };
    let D::LawFamily(child) = &v.data else {
        return Err("元Law族の依存が別の構成".into());
    };
    if child.template != d.template
        || child.architecture != d.architecture
        || child.parameters != d.parameters
    {
        return Err("元Law族の依存が別の元Law/対象".into());
    }
    Ok(child.clone())
}
fn domain(g: &Graph, d: &Data, r: NodeRef, keys: &[Vec<NodeRef>]) -> Result<(), ValidationFailure> {
    let child = same(g, d, r)?;
    let Kind::Domain { members } = &child.kind else {
        return Err("元Law族の実直積Domainがない".into());
    };
    if members.len() != keys.len() {
        return Err("元Law族の直積member数が違う".into());
    }
    for (i, r) in members.iter().enumerate() {
        g.tick()?;
        let m = same(g, d, *r)?;
        if !matches!(&m.kind,Kind::Member{position,values,..} if *position==i && values==&keys[i]) {
            return Err("元Law族の直積memberの順序・由来が違う".into());
        }
    }
    Ok(())
}
struct Aggregate {
    value: Option<bool>,
    evidence: Vec<NodeRef>,
    reasons: Vec<Reason>,
    support: Vec<Fact>,
    scope: Scope,
}
fn rows(
    g: &Graph,
    d: &Data,
    p: &FamilyInputs,
    keys: &[Vec<NodeRef>],
    domain_ref: NodeRef,
    rs: &[Row],
) -> Result<Aggregate, ValidationFailure> {
    domain(g, d, domain_ref, keys)?;
    if rs.len() != keys.len() {
        return Err("元Law族の全行と実直積のcoverageが違う".into());
    }
    let (mut support, mut scope) = base_metadata(g, d, p)?;
    let mut evidence: Vec<NodeRef> = vec![];
    let mut reasons = vec![];
    let mut all = true;
    let mut false_row = false;
    for (key, row) in keys.iter().zip(rs) {
        g.tick()?;
        let origin = frames::origin(g, row.law)?.ok_or("元Law族の実rowに由来がない")?;
        if origin.object != p.object
            || origin.declaration
                != frames::origin(g, d.template)?
                    .ok_or("元Law族templateがない")?
                    .declaration
            || !Arc::ptr_eq(&origin.architecture, &p.architecture)
        {
            return Err("元Law族の実rowが別の対象/宣言".into());
        }
        matching(g, p, key, &origin.bindings)?;
        g.expect(row.evaluation, &NodeType::Evaluation(Type::Bool))?;
        g.expect(row.proposition, &NodeType::Proposition)?;
        let eval = g.get(row.evaluation)?;
        let prop = g.get(row.proposition)?;
        match &prop.payload {
            Some(Payload::Construction(v)) => {
                let D::OutsideLaw(data) = &v.data else {
                    return Err("元Law族の非適用命題が別の構成".into());
                };
                if data.origin != row.law
                    || data.architecture != d.architecture
                    || !matches!(data.kind,super::law_inapplicable::Kind::Proposition{evaluation} if evaluation==row.evaluation)
                {
                    return Err("元Law族の非適用命題が別の行/対象".into());
                }
            }
            Some(Payload::Proposition { .. }) => {
                let context = g.context_at(row.proposition.0);
                let index = context
                    .instance
                    .ok_or("元Law族の通常命題に実instanceがない")?;
                let record = g.instances.get(index).ok_or("元Law族の実instanceがない")?;
                if record.source != row.law
                    || record.caller != g.context_at(d.architecture.0)
                    || g.context_at(row.evaluation.0) != context
                    || prop.arguments.get(1) != Some(&row.evaluation)
                {
                    return Err("元Law族の通常命題が別の行/評価".into());
                }
                if frames::architecture(g, index, g.nodes.len())? != Some(d.architecture) {
                    return Err("元Law族の実行環境が違う".into());
                }
            }
            _ => return Err("元Law族の行命題がない".into()),
        }
        let status = prop
            .judgment
            .as_ref()
            .ok_or("元Law族の行判断がない")?
            .status;
        let value = match &eval.payload {
            Some(Payload::Evaluation { value, .. }) => g.boolean(*value)?,
            Some(Payload::Construction(v)) => {
                let D::OutsideLaw(data) = &v.data else {
                    return Err("元Law族の行評価が別の構成".into());
                };
                let super::law_inapplicable::Kind::Evaluation { value } = &data.kind else {
                    return Err("元Law族の非適用行評価がない".into());
                };
                g.boolean(Some(*value))?
            }
            _ => return Err("元Law族の行Evaluationがない".into()),
        };
        let expected = match value {
            Some(true) => Decision::Established,
            Some(false) => Decision::Refuted,
            None => Decision::Undetermined,
        };
        if status != expected {
            return Err("元Law族の実評価と行判断が違う".into());
        }
        all &= value == Some(true);
        false_row |= value == Some(false);
        evidence.extend(&prop.evidence);
        reasons.extend(prop.reasons.iter().cloned());
        support.extend(eval.support.iter().cloned());
        support.extend(prop.support.iter().cloned());
        scope.merge(&eval.scope);
        scope.merge(&prop.scope);
    }
    support.sort();
    support.dedup();
    evidence.sort_by_key(|r| r.0);
    evidence.dedup();
    reasons.sort_by_key(|r| r.wire().canonical());
    reasons.dedup();
    Ok(Aggregate {
        value: if false_row {
            Some(false)
        } else if all {
            Some(true)
        } else {
            None
        },
        evidence,
        reasons,
        support,
        scope,
    })
}
fn base_metadata(
    g: &Graph,
    d: &Data,
    p: &FamilyInputs,
) -> Result<(Vec<Fact>, Scope), ValidationFailure> {
    let mut support = g.get(d.template)?.support.clone();
    support.extend(g.get(d.architecture)?.support.iter().cloned());
    let mut scope = frames::base_scope(
        &p.architecture,
        &frames::origin(g, d.template)?
            .ok_or("元Law族の由来がない")?
            .declaration,
    )?;
    scope.merge(&g.get(d.architecture)?.scope);
    scope.assignments = true;
    for parameter in &p.parameters {
        support.extend(g.get(parameter.reference)?.support.iter().cloned());
        scope.merge(&g.get(parameter.reference)?.scope);
        scope.quantifiers.push(Quantifier {
            kind: crate::law::ast::QuantKind::Forall,
            name: parameter.name.clone(),
            ty: parameter.ty.clone(),
            domain: Some(parameter.reference),
            occurrence: parameter.occurrence,
            context: None,
        })
    }
    support.sort();
    support.dedup();
    Ok((support, scope))
}
fn ref_array(rs: &[NodeRef]) -> Json {
    Json::Arr(rs.iter().map(|r| r.wire()).collect())
}
fn expected(g: &Graph, d: &Data) -> Result<(Arc<ArchitectureWitness>, Data), ValidationFailure> {
    let p = plan(g, d.template, d.architecture)?.ok_or("元Law族の完全な有限parameter域がない")?;
    if d.parameters != p.parameters.iter().map(|p| p.reference).collect::<Vec<_>>() {
        return Err("元Law族のparameter域順が違う".into());
    }
    let keys = coordinates(g, &p)?;
    let (support, scope) = base_metadata(g, d, &p)?;
    let mut out = d.clone();
    out.support = support;
    out.scope = scope;
    out.reasons = vec![];
    out.evidence = vec![];
    out.judgment = None;
    let product_type = super::environment::family::family_type(
        &p.parameters
            .iter()
            .map(|p| p.ty.clone())
            .collect::<Vec<_>>(),
    );
    out.wire = match &d.kind {
        Kind::Member {
            position,
            values,
            scalar,
            wire,
        } => {
            if keys.get(*position) != Some(values) {
                return Err("元Law族のmember位置/束縛が違う".into());
            }
            let vs = values
                .iter()
                .map(|r| g.scalar(*r).cloned())
                .collect::<Result<Vec<_>, _>>()?;
            let actual = if vs.len() == 1 {
                vs[0].clone()
            } else {
                Scalar::Tuple(vs)
            };
            let actual_wire = g.scalar_wire(&actual, values)?;
            if scalar != &actual || wire != &actual_wire {
                return Err("元Law族のmember型/値/表示が違う".into());
            }
            actual_wire
        }
        Kind::Domain { members } => {
            if members.len() != keys.len() {
                return Err("元Law族の実直積Domainが全域でない".into());
            }
            for (i, r) in members.iter().enumerate() {
                let m = same(g, d, *r)?;
                if !matches!(m.kind,Kind::Member{position,..} if position==i) {
                    return Err("元Law族のDomain member順が違う".into());
                }
            }
            Json::obj([
                ("kind", Json::str("finite")),
                ("type", product_type.wire()),
                ("elements", ref_array(members)),
            ])
        }
        Kind::Value {
            domain,
            rows: rs,
            scalar,
        } => {
            let a = rows(g, d, &p, &keys, *domain, rs)?;
            if a.value.map(Scalar::Bool).as_ref() != Some(scalar) {
                return Err("元Law族の全称集約値が違う".into());
            }
            out.support = a.support;
            out.scope = a.scope;
            out.reasons = a.reasons;
            scalar.wire()
        }
        Kind::Evaluation {
            domain,
            rows: rs,
            value,
        } => {
            let a = rows(g, d, &p, &keys, *domain, rs)?;
            match (a.value, value) {
                (Some(b), Some(v)) => {
                    let actual = same(g, d, *v)?;
                    if !matches!(&actual.kind,Kind::Value{domain:vd,rows:vr,scalar:Scalar::Bool(vb)} if vd==domain && vr==rs && vb==&b)
                    {
                        return Err("元Law族の全称値が別の族/直積".into());
                    }
                }
                (None, None) => (),
                _ => return Err("元Law族の未決値を補完した".into()),
            }
            out.support = a.support;
            out.scope = a.scope;
            out.reasons = a.reasons;
            let origin = frames::origin(g, d.template)?.ok_or("元Law族のbodyがない")?;
            let location = Location::Law {
                span: Witness::Architecture(p.architecture.clone())
                    .inputs()
                    .law()
                    .exprs
                    .get(origin.body)
                    .ok_or("元Law族のbody式がない")?
                    .span,
            };
            let mut w = Json::obj([
                ("expression", origin.body_reference.wire()),
                ("environment", d.architecture.wire()),
                (
                    "bindings",
                    Json::Arr(
                        p.template
                            .bindings
                            .iter()
                            .map(|b| {
                                Json::obj([("name", Json::str(&b.name)), ("value", b.value.wire())])
                            })
                            .collect(),
                    ),
                ),
                (
                    "parts",
                    Json::Arr(vec![Json::obj([
                        ("location", crate::result::location_wire(&location)),
                        (
                            "children",
                            ref_array(&rs.iter().map(|r| r.evaluation).collect::<Vec<_>>()),
                        ),
                    ])]),
                ),
                ("applicability", Json::str("applicable")),
            ]);
            if let Some(v) = value {
                let Json::Obj(wire) = &mut w else {
                    unreachable!()
                };
                wire.insert("value".into(), v.wire());
                let Some(Json::Arr(parts)) = wire.get_mut("parts") else {
                    unreachable!()
                };
                let Json::Obj(part) = &mut parts[0] else {
                    unreachable!()
                };
                part.insert("value".into(), v.wire());
            }
            w
        }
        Kind::Exhaustion { evaluation } => {
            let e = same(g, d, *evaluation)?;
            let Kind::Evaluation {
                domain, rows: rs, ..
            } = &e.kind
            else {
                return Err("元Law族の全検査元評価がない".into());
            };
            let a = rows(g, d, &p, &keys, *domain, rs)?;
            if a.value != Some(true) {
                return Err("元Law族の全検査が成立でない".into());
            }
            out.support = a.support;
            out.scope = a.scope;
            Payload::FiniteExhaustion {
                domain: *domain,
                checked: rs.len(),
                instances: rs.iter().map(|r| r.evaluation).collect(),
            }
            .wire()
        }
        Kind::Proposition {
            evaluation,
            evidence,
        } => {
            let e = same(g, d, *evaluation)?;
            let Kind::Evaluation {
                domain, rows: rs, ..
            } = &e.kind
            else {
                return Err("元Law族の判断元評価がない".into());
            };
            let mut a = rows(g, d, &p, &keys, *domain, rs)?;
            if a.value == Some(true) {
                let Some(last) = evidence.last() else {
                    return Err("元Law族の全検査証拠がない".into());
                };
                let proof = same(g, d, *last)?;
                if !matches!(proof.kind,Kind::Exhaustion{evaluation:e} if e==*evaluation) {
                    return Err("元Law族の全検査証拠が別評価".into());
                }
                a.evidence.push(*last)
            }
            if evidence != &a.evidence {
                return Err("元Law族の判断証拠が実row/全検査と違う".into());
            }
            let status = match a.value {
                Some(true) => Decision::Established,
                Some(false) => Decision::Refuted,
                None => Decision::Undetermined,
            };
            out.support = a.support;
            out.scope = a.scope;
            out.reasons = a.reasons;
            out.evidence = a.evidence;
            out.judgment = Some(Judgment {
                status,
                evidence: out.evidence.clone(),
                reasons: out.reasons.clone(),
            });
            Json::obj([
                ("predicate", Json::str("law_holds")),
                ("operands", Json::Arr(vec![d.template.wire()])),
                (
                    "quantifiers",
                    Json::Arr(out.scope.quantifiers.iter().map(Quantifier::wire).collect()),
                ),
            ])
        }
    };
    Ok((p.architecture, out))
}
pub(super) fn validate_node(
    g: &Graph,
    n: &Node,
    v: &ConstructionValue,
    d: &Data,
) -> Result<(), ValidationFailure> {
    let (a, e) = expected(g, d)?;
    let Witness::Architecture(w) = &v.witness else {
        return Err("元Law族のArchitecture証拠がない".into());
    };
    if !Arc::ptr_eq(w, &a)
        || d != &e
        || n.ty != d.ty()
        || n.rule != Rule::Construction(d.construction())
        || n.arguments != d.arguments()
        || n.support != d.support
        || n.scope != d.scope
        || n.evidence != d.evidence
        || n.reasons != d.reasons
        || n.judgment != d.judgment
    {
        return Err("元Law族の型/全域/全行/判断/表示/metadataが違う".into());
    }
    Ok(())
}
fn put(
    env: &Environment<'_>,
    g: &mut Graph,
    d: &Data,
    kind: Kind,
) -> Result<NodeRef, ValidationFailure> {
    let mut d = d.clone();
    d.kind = kind;
    let (a, d) = expected(g, &d)?;
    let n = Node {
        ty: d.ty(),
        rule: Rule::Construction(d.construction()),
        arguments: d.arguments(),
        support: d.support.clone(),
        scope: d.scope.clone(),
        evidence: d.evidence.clone(),
        reasons: d.reasons.clone(),
        judgment: d.judgment.clone(),
        payload: Some(Payload::Construction(Box::new(ConstructionValue {
            witness: Witness::Architecture(a),
            data: D::LawFamily(d),
        }))),
    };
    env.validate(g, &n)?;
    g.push(n)
}
pub(super) fn check(
    env: &Environment<'_>,
    g: &mut Graph,
    template: NodeRef,
    architecture: NodeRef,
    c: &mut Control,
) -> Result<Option<Answer>, ValidationFailure> {
    tick(c)?;
    if g.active != g.context_at(template.0) {
        return Err("元Law族の生成が元Request Contextでない".into());
    }
    env.recheck_law_evaluation_inputs(g, template, architecture)?;
    let Some(p) = plan(g, template, architecture)? else {
        return Ok(None);
    };
    let keys = coordinates(g, &p)?;
    if !p.target_rows.is_empty() && p.target_rows.len() != keys.len() {
        return Err("元Law族の対象全row数が違う".into());
    }
    let d = Data {
        template,
        architecture,
        parameters: p.parameters.iter().map(|p| p.reference).collect(),
        kind: Kind::Domain { members: vec![] },
        wire: Json::Arr(vec![]),
        support: vec![],
        scope: Scope::default(),
        reasons: vec![],
        evidence: vec![],
        judgment: None,
    };
    let mut members = vec![];
    for (position, values) in keys.iter().enumerate() {
        tick(c)?;
        let vs = values
            .iter()
            .map(|r| g.scalar(*r).cloned())
            .collect::<Result<Vec<_>, _>>()?;
        let scalar = if vs.len() == 1 {
            vs[0].clone()
        } else {
            Scalar::Tuple(vs)
        };
        let wire = g.scalar_wire(&scalar, values)?;
        members.push(put(
            env,
            g,
            &d,
            Kind::Member {
                position,
                values: values.clone(),
                scalar,
                wire,
            },
        )?);
    }
    tick(c)?;
    let product = put(env, g, &d, Kind::Domain { members })?;
    let mut rs = vec![];
    for (position, (key, base)) in keys.iter().zip(&p.base_rows).enumerate() {
        tick(c)?;
        let law = if let Some(target) = p.target_rows.get(position) {
            let row = frames::origin(g, *target)?.ok_or("元Law族の対象rowがない")?;
            matching(g, &p, key, &row.bindings)?;
            *target
        } else {
            super::law_instantiation::instantiate(env, g, *base, template, architecture, c)?
        };
        let answer = if frames::origin(g, law)?
            .ok_or("元Law族の実rowがない")?
            .outside
        {
            super::law_inapplicable::check(env, g, law, architecture, c)?
                .ok_or("元Law族の非適用行評価がない")?
        } else {
            super::law_proposition::check(env, g, law, architecture, c)?
                .answer
                .ok_or("元Law族の実行が未完成")?
        };
        rs.push(Row {
            law,
            evaluation: *answer
                .outputs
                .get("evaluation")
                .ok_or("元Law族の行Evaluationがない")?,
            proposition: answer.claim.ok_or("元Law族の行判断がない")?,
        });
    }
    tick(c)?;
    let a = rows(g, &d, &p, &keys, product, &rs)?;
    let value = a
        .value
        .map(|b| {
            put(
                env,
                g,
                &d,
                Kind::Value {
                    domain: product,
                    rows: rs.clone(),
                    scalar: Scalar::Bool(b),
                },
            )
        })
        .transpose()?;
    tick(c)?;
    let evaluation = put(
        env,
        g,
        &d,
        Kind::Evaluation {
            domain: product,
            rows: rs,
            value,
        },
    )?;
    let mut evidence = a.evidence;
    if a.value == Some(true) {
        tick(c)?;
        evidence.push(put(env, g, &d, Kind::Exhaustion { evaluation })?)
    }
    tick(c)?;
    let proposition = put(
        env,
        g,
        &d,
        Kind::Proposition {
            evaluation,
            evidence,
        },
    )?;
    tick(c)?;
    let n = g.get(proposition)?;
    let judgment = n.judgment.as_ref().ok_or("元Law族の判断がない")?;
    Ok(Some(Answer {
        id: g
            .requests
            .get(g.active.request)
            .ok_or("元Law族のRequestがない")?
            .id
            .clone(),
        status: judgment.status,
        outputs: BTreeMap::from([
            ("evaluation".into(), evaluation),
            ("proposition".into(), proposition),
        ]),
        claim: Some(proposition),
        evidence: n.evidence.clone(),
        reasons: n.reasons.clone(),
        scope: n.scope.clone(),
    }))
}
#[cfg(test)]
#[path = "law_family_tests.rs"]
mod tests;
