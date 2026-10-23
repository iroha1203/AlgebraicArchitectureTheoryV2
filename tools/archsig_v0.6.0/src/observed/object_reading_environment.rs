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
        Ok(Some((i.bindings, variables, scope)))
    }
}
