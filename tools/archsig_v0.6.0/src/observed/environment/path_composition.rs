//! 式内thenと公開composeは同じPath合成を共有する。
use super::internal_path::PathResult;
use super::*;
impl Environment<'_> {
    pub(in crate::observed) fn path_operation(
        &self,
        id: usize,
        values: &[Scalar],
    ) -> Result<PathResult, ValidationFailure> {
        if self.builtin(id)? == Some("path") {
            return self.internal_path(id, values);
        }
        if self.builtin(id)? != Some("then") {
            return Err("Path構成の元演算が違う".into());
        }
        let [Scalar::Path(left), Scalar::Path(right)] = values else {
            return Err("thenの元実引数がPath2個でない".into());
        };
        let reading = self.path_reading(id)?;
        let result = super::super::path_compose::compose_retained(
            left,
            right,
            reading,
            &self.control,
            |stage, count| {
                #[cfg(test)]
                data::observe_actual(
                    self.inputs.law().exprs[id].span,
                    self.scoped_context
                        .get()
                        .or(self.context.get())
                        .unwrap_or_default(),
                    stage,
                    count,
                );
                #[cfg(not(test))]
                let _ = (stage, count);
            },
        )
        .map_err(|failure| failure.cause)?;
        let mut scope = Scope::default();
        scope.readings.insert(reading.into());
        Ok(PathResult {
            value: result.value.map(|p| Scalar::Path(Box::new(p))),
            scope,
            support: vec![],
            missing: vec![],
            failure: result.mismatch,
        })
    }
}
