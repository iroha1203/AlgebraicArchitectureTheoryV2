//! 元view instanceの値と対象を通常Sourceの検査へ戻す。
use super::*;
use crate::observed::{
    construction_result::{ConstructionData as D, ConstructionValue},
    object_reading_evaluation as reading,
};
impl Environment<'_> {
    pub(super) fn recheck_object_reading_frame(
        &self,
        g: &Graph,
        v: &ConstructionValue,
        at: usize,
    ) -> Result<(), ValidationFailure> {
        let D::ObjectReadingFrame(d) = &v.data else {
            return Ok(());
        };
        d.position(at)?;
        for r in d.arguments() {
            self.tick()?;
            self.validate_at(g, g.get(r)?, r.0)?;
        }
        Ok(())
    }
    pub(super) fn native_view_source_inputs(
        &self,
        g: &Graph,
        index: usize,
    ) -> Result<Option<FrameInputs>, ValidationFailure> {
        self.tick()?;
        let Some(i) = reading::instance_inputs(g, index, self.cutoff.get().min(g.nodes.len()))?
        else {
            return Ok(None);
        };
        let record = g.instances.get(index).ok_or("元view instanceがない")?;
        for r in [
            record.source,
            record.domain,
            record.member,
            i.origin.architecture,
        ] {
            self.validate_at(g, g.get(r)?, r.0)?;
        }
        let mut variables = BTreeMap::new();
        let mut scope = Scope::default();
        for r in [record.source, i.origin.architecture] {
            scope.merge(&g.get(r)?.scope);
        }
        for b in &i.bindings {
            self.tick()?;
            self.validate_at(g, g.get(b.value)?, b.value.0)?;
            let value = g.scalar(b.value)?.clone();
            if value.ty() != b.ty {
                return Err("viewの実束縛型が違う".into());
            }
            variables.insert(
                b.name.clone(),
                SourceValue {
                    condition_failed: false,
                    condition_pending: false,
                    symbolic: None,
                    comparison: None,
                    affine: crate::observed::affine::constant(&value, &self.control)?.map(Box::new),
                    scope: scope.clone(),
                    known_value: Some(value),
                    support: g.get(b.value)?.support.clone(),
                    scalar_scope: Some(g.get(b.value)?.scope.clone()),
                },
            );
        }
        let declaration = self.inputs.law().declarations.get(&i.origin.declaration)
            .ok_or("元viewの宣言がない")?;
        if let crate::law::model::Signature::View { params, .. } = &declaration.signature {
            for parameter in params {
                self.tick()?;
                if !variables.contains_key(&parameter.name) && matches!(parameter.ty, Type::Z | Type::Q) {
                    let (free, _) = change_affine::law_variables(self, std::slice::from_ref(parameter), &[])?;
                    variables.extend(free);
                }
            }
        }
        Ok(Some((i.bindings, variables, scope)))
    }
}

impl Environment<'_> {
    pub(super) fn validate_object_reading_result(
        &self,
        g: &Graph,
        n: &Node,
        at: usize,
    ) -> Result<bool, ValidationFailure> {
        let Some(expression) = super::super::object_reading_result::source(g, n)? else {
            return Ok(false);
        };
        let context = self.current_context(g);
        if context != g.context_at(expression.0)
            || context.frame.is_some()
            || context.instance.is_some()
            || context.iteration.is_some()
            || context.case.is_some()
        {
            return Err("view全体評価の元Request Contextが違う".into());
        }
        let request = g
            .requests
            .get(context.request)
            .ok_or("view全体評価の元Requestがない")?;
        if self
            .original_requests
            .is_none_or(|rs| rs.get(context.request) != Some(request))
        {
            return Err("view全体評価の元Requestが現在の入力と違う".into());
        }
        for r in super::super::object_reading_result::dependencies(g, n)? {
            self.tick()?;
            if r.0 >= at {
                return Err("view全体評価の依存が既出でない".into());
            }
            self.validate_at(g, g.get(r)?, r.0)?;
        }
        super::super::object_reading_result::validate(g, n, at)?;
        Ok(true)
    }
}

#[cfg(test)]
impl Environment<'_> {
    pub(in crate::observed) fn object_reading_projection_for_test(
        &self,
        g: &Graph,
        r: NodeRef,
        path: &[crate::observed::projection::ProjectionStep],
        span: (usize, usize),
    ) -> Result<AnswerBinding, ValidationFailure> {
        self.answer_projection(g, r, path, span)
    }
    pub(in crate::observed) fn object_reading_recheck_evaluation_for_test(
        &self,
        g: &Graph,
        r: NodeRef,
    ) -> Result<(), ValidationFailure> {
        self.recheck_evaluation(g, r)
    }
}
impl Environment<'_> {
    pub(super) fn recheck_view_family(
        &self,
        g: &Graph,
        v: &ConstructionValue,
        at: usize,
    ) -> Result<(), ValidationFailure> {
        let D::ViewFamily(d) = &v.data else {
            return Ok(());
        };
        d.position(at)?;
        d.recheck(self, g, &mut self.control.clone())?;
        for r in d.arguments() {
            self.tick()?;
            if r.0 >= at {
                return Err("有限view族の依存が既出でない".into());
            }
            self.validate_at(g, g.get(r)?, r.0)?;
        }
        Ok(())
    }
    pub(super) fn validate_view_family_evaluation(
        &self,
        g: &Graph,
        n: &Node,
        at: usize,
    ) -> Result<bool, ValidationFailure> {
        let Some(rs) = super::super::view_family::family_dependencies(g, n)? else {
            return Ok(false);
        };
        let Some(Payload::Evaluation { expression, .. }) = &n.payload else {
            return Err("全view族のpayloadが違う".into());
        };
        let context = self.current_context(g);
        if context != g.context_at(expression.0)
            || context.frame.is_some()
            || context.instance.is_some()
            || context.iteration.is_some()
            || context.case.is_some()
        {
            return Err("全view族の元Request Contextが違う".into());
        }
        let request = g
            .requests
            .get(context.request)
            .ok_or("全view族の元Requestがない")?;
        if self
            .original_requests
            .is_none_or(|ps| ps.get(context.request) != Some(request))
        {
            return Err("全view族の元Requestが現在の入力と違う".into());
        }
        for r in rs {
            self.tick()?;
            if r.0 >= at {
                return Err("全view族の依存が既出でない".into());
            }
            self.validate_at(g, g.get(r)?, r.0)?;
        }
        super::super::view_family::validate_family(g, n, at)?;
        Ok(true)
    }
}
