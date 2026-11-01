//! 有限view族の元parameter位置とnative行から、値producerを照合する。
use super::*;
use crate::observed::finite::{Enumeration, FiniteDomain};

pub(in crate::observed) struct ParameterDomainReading {
    pub values: Option<Vec<Scalar>>,
    pub missing: Vec<Fact>,
    pub support: Vec<Fact>,
    pub scope: Scope,
}
fn record_domain_reads(reads: &RefCell<FiniteDomain>, enumeration: &Enumeration, missing: &[Fact]) {
    let mut reads = reads.borrow_mut();
    reads.enumeration.scope.merge(&enumeration.scope);
    reads
        .enumeration
        .support
        .extend(enumeration.support.iter().cloned());
    reads.missing.extend(missing.iter().cloned());
}

impl Environment<'_> {
    pub(in crate::observed) fn object_view_binding(
        &self,
        graph: &Graph,
        p: &crate::law::model::Param,
    ) -> Result<Option<Node>, ValidationFailure> {
        let Some(assignment) = self.indexes.object_values else {
            return Ok(None);
        };
        let request = graph
            .requests
            .get(self.current_context(graph).request)
            .ok_or("有限view行のRequestがない")?;
        let Some((value, scope, support)) = assignment.binding(self, request, p, &self.control)?
        else {
            return Ok(None);
        };
        Ok(Some(Node {
            ty: NodeType::Value(p.ty.erase()),
            payload: Some(Payload::Scalar(value)),
            rule: Rule::Input {
                kind: "law",
                location: Location::Law { span: p.span },
            },
            arguments: vec![],
            support,
            evidence: vec![],
            judgment: None,
            scope,
            reasons: vec![],
        }))
    }
    pub(in crate::observed) fn object_view_is_bound(&self, p: &crate::law::model::Param) -> bool {
        self.indexes.object_values
            .is_some_and(|assignment| assignment.parameter(p))
    }
    pub(super) fn object_view_binding_matches(
        &self,
        graph: &Graph,
        p: &crate::law::model::Param,
        value: NodeRef,
    ) -> Result<(), ValidationFailure> {
        let expected = self
            .object_view_binding(graph, p)?
            .ok_or("有限viewの元parameterがない")?;
        let node = graph.get(value)?;
        if node != &expected {
            return Err("有限view束縛が別parameterまたは値producerである".into());
        }
        self.validate_at(graph, node, value.0)
    }
    pub(super) fn object_view_binding_count(&self) -> usize {
        self.indexes.object_values.map_or(0, |values| values.count())
    }
    pub(super) fn finite_view_input(
        &self,
        graph: &Graph,
        node: &Node,
    ) -> Result<bool, ValidationFailure> {
        let (
            Some(assignment),
            Rule::Input {
                kind: "law",
                location: Location::Law { span },
            },
            Some(Payload::Scalar(value)),
        ) = (self.indexes.object_values, &node.rule, &node.payload)
        else {
            return Ok(false);
        };
        let request = graph
            .requests
            .get(self.current_context(graph).request)
            .ok_or("有限view producerのRequestがない")?;
        let declaration = self
            .indexes.inputs
            .law()
            .declarations()
            .get(request.declaration().ok_or("有限viewの宣言がない")?)
            .ok_or("有限view元宣言がない")?;
        let crate::law::model::Signature::View { params, .. } = &declaration.signature else {
            return Err("有限view producerがviewでない".into());
        };
        let Some(p) = params.iter().find(|p| p.span == *span) else {
            return Ok(false);
        };
        if assignment
            .binding(self, request, p, &self.control)?
            .is_none()
        {
            return Ok(false);
        }
        data::check(value, self.indexes.inputs.law(), &self.control)?;
        let expected = self
            .object_view_binding(graph, p)?
            .ok_or("有限view producerの値がない")?;
        if node != &expected {
            return Err("有限view parameterの値・型・元位置・支持・Scope・辺が違う".into());
        }
        Ok(true)
    }
}

impl Environment<'_> {
    pub(in crate::observed) fn object_view_domain(
        &self,
        parameter: &crate::law::model::Param,
        instance: &crate::construction::readings::ObjectInstance,
    ) -> Result<Option<(super::super::finite::Enumeration, Vec<Fact>)>, ValidationFailure> {
        let domain = self.object_parameter_domain(parameter, instance)?;
        Ok(domain.values.map(|values| {
            (
                Enumeration {
                    values,
                    scope: domain.scope,
                    support: domain.support,
                },
                domain.missing,
            )
        }))
    }
    /// 列挙できる値域と、型を読む過程の依存情報を別々に保持する。
    pub(in crate::observed) fn object_parameter_domain(
        &self,
        parameter: &crate::law::model::Param,
        instance: &crate::construction::readings::ObjectInstance,
    ) -> Result<ParameterDomainReading, ValidationFailure> {
        let declaration = self
            .indexes.inputs
            .law()
            .declarations()
            .get(&instance.declaration().name)
            .ok_or("有限view域の元宣言がない")?;
        let reads = RefCell::new(FiniteDomain::default());
        let enumeration = super::super::finite::values_if_finite_with_owned(
            &parameter.ty,
            self.indexes.inputs.law(),
            &self.control,
            &mut |entity| {
                let domain = self.indexes.reference_roster(&self.control, entity, &mut |_| {})?;
                record_domain_reads(&reads, &domain, &[]);
                Ok(domain)
            },
            &mut |entity, owner| {
                let binding = instance
                    .bindings()
                    .iter()
                    .find(|b| b.parameter().name == owner)
                    .ok_or("複合Owned型の固定owner束縛がない")?;
                let fact = binding.subject();
                let subject = self.indexes.subject(&fact.snapshot, &fact.subject)?;
                let owner = Scalar::Subject {
                    snapshot: fact.snapshot.clone(),
                    subject: fact.subject.clone(),
                    entity: subject.ty.to_string(),
                };
                let members =
                    self.owned_members(entity, &owner, None, &declaration.reading, &mut |_, _| {})?;
                record_domain_reads(&reads, &members.enumeration, &members.missing);
                Ok(super::super::finite::FiniteDomain {
                    enumeration: members.enumeration,
                    missing: members.missing,
                })
            },
            &mut |_| {},
        )?;
        // 完成した空型の証明など、列挙器が選んだ依存はそのまま使う。
        // 非有限で値列がない場合も、既に読んだ所属・参照の情報は失わない。
        let (values, mut domain) = match enumeration {
            Some(mut domain) => (Some(std::mem::take(&mut domain.enumeration.values)), domain),
            None => (None, reads.into_inner()),
        };
        domain.enumeration.support.sort();
        domain.enumeration.support.dedup();
        domain.missing.sort();
        domain.missing.dedup();
        Ok(ParameterDomainReading {
            values,
            missing: domain.missing,
            support: domain.enumeration.support,
            scope: domain.enumeration.scope,
        })
    }
}
