//! 同じ原始carrier上の総写像を順に合成し、名前付き有限語を保持する。
use super::super::path_value::{PathValue, Step};
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
        self.tick()?;
        left.check(&self.control)?;
        right.check(&self.control)?;
        let reading = self.path_reading(id)?;
        let mut out = PathResult {
            value: None,
            scope: Scope::default(),
            support: vec![],
            missing: vec![],
            failure: None,
        };
        out.scope.readings.insert(reading.into());
        if left.target() != right.object() {
            out.failure = Some((left.target(), right.object()));
            return Ok(out);
        }
        let mut words = Vec::new();
        for path in [left, right] {
            if let Some(step) = &path.step {
                for generator in std::iter::once(&step.generator).chain(&step.word_tail) {
                    self.tick()?;
                    words.push(generator.clone());
                    #[cfg(test)]
                    data::observe_actual(
                        self.inputs.law().exprs[id].span,
                        self.scoped_context
                            .get()
                            .or(self.context.get())
                            .unwrap_or_default(),
                        "path_word",
                        words.len(),
                    );
                    self.tick()?;
                }
            }
        }
        let action = match (&left.step, &right.step) {
            (None, None) => None,
            (Some(one), None) | (None, Some(one)) => {
                let mut carrier = Vec::new();
                let mut images = Vec::new();
                for (a, b) in one.carrier.iter().zip(&one.images) {
                    self.tick()?;
                    carrier.push(a.clone());
                    images.push(b.clone());
                    #[cfg(test)]
                    data::observe_actual(
                        self.inputs.law().exprs[id].span,
                        self.scoped_context
                            .get()
                            .or(self.context.get())
                            .unwrap_or_default(),
                        "path_compose",
                        images.len(),
                    );
                    self.tick()?;
                }
                Some((carrier, images))
            }
            (Some(a), Some(b)) => {
                if a.carrier.len() != b.carrier.len() {
                    return Err("thenの共通carrier件数が違う".into());
                }
                let mut carrier = Vec::new();
                let mut images = Vec::new();
                for ((x, y), image) in a.carrier.iter().zip(&b.carrier).zip(&a.images) {
                    self.tick()?;
                    if x != y {
                        return Err("thenの原始carrierが同一でない".into());
                    }
                    let at = b
                        .carrier
                        .binary_search(image)
                        .map_err(|_| "thenの中間像が共通carrierにない")?;
                    carrier.push(x.clone());
                    images.push(b.images[at].clone());
                    #[cfg(test)]
                    data::observe_actual(
                        self.inputs.law().exprs[id].span,
                        self.scoped_context
                            .get()
                            .or(self.context.get())
                            .unwrap_or_default(),
                        "path_compose",
                        images.len(),
                    );
                    self.tick()?;
                }
                Some((carrier, images))
            }
        };
        let step = if let Some((carrier, images)) = action {
            let mut word = words.into_iter();
            let generator = word.next().ok_or("非空Path作用に元語がない")?;
            Some(Box::new(Step {
                generator,
                word_tail: word.collect(),
                target: right.target(),
                carrier,
                images,
            }))
        } else {
            if !words.is_empty() {
                return Err("空語恒等に生成元がある".into());
            }
            None
        };
        let path = PathValue {
            reading: reading.into(),
            snapshot: left.snapshot.clone(),
            subject: left.subject.clone(),
            entity: left.entity.clone(),
            step,
        };
        path.check(&self.control)?;
        out.value = Some(Scalar::Path(Box::new(path)));
        self.tick()?;
        Ok(out)
    }
}
