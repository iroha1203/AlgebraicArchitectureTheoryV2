//! Pathの共通carrier作用と名前付き語を合成し、最終停止で完成値を保持する。
use super::{
    control::{Checkpoint, Control},
    path_value::{PathValue, Step},
    result::{Scalar, ValidationFailure},
};
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct ComposedPath {
    pub value: Option<PathValue>,
    pub mismatch: Option<(Scalar, Scalar)>,
}
pub(super) struct ComposeFailure {
    pub cause: ValidationFailure,
    pub partial: Option<ComposedPath>,
}
fn tick(control: &Control) -> Result<(), ValidationFailure> {
    control
        .clone()
        .checkpoint(Checkpoint::FiniteIteration)
        .map_err(ValidationFailure::Stop)
}
pub(super) fn compose_retained(
    left: &PathValue,
    right: &PathValue,
    reading: &str,
    control: &Control,
    mut observe: impl FnMut(&'static str, usize),
) -> Result<ComposedPath, ComposeFailure> {
    let mut calculate = || -> Result<ComposedPath, ValidationFailure> {
        tick(control)?;
        left.check(control)?;
        right.check(control)?;
        if left.target() != right.object() {
            return Ok(ComposedPath {
                value: None,
                mismatch: Some((left.target(), right.object())),
            });
        }
        let mut words = Vec::new();
        for path in [left, right] {
            if let Some(step) = &path.step {
                for generator in std::iter::once(&step.generator).chain(&step.word_tail) {
                    tick(control)?;
                    words.push(generator.clone());
                    observe("path_word", words.len());
                    tick(control)?;
                }
            }
        }
        let action = match (&left.step, &right.step) {
            (None, None) => None,
            (Some(one), None) | (None, Some(one)) => {
                let mut carrier = Vec::new();
                let mut images = Vec::new();
                for (a, b) in one.carrier.iter().zip(&one.images) {
                    tick(control)?;
                    carrier.push(a.clone());
                    images.push(b.clone());
                    observe("path_compose", images.len());
                    tick(control)?;
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
                    tick(control)?;
                    if x != y {
                        return Err("thenの原始carrierが同一でない".into());
                    }
                    let at = b
                        .carrier
                        .binary_search(image)
                        .map_err(|_| "thenの中間像が共通carrierにない")?;
                    carrier.push(x.clone());
                    images.push(b.images[at].clone());
                    observe("path_compose", images.len());
                    tick(control)?;
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
        path.check(control)?;

        Ok(ComposedPath {
            value: Some(path),
            mismatch: None,
        })
    };
    let completed = calculate().map_err(|cause| ComposeFailure {
        cause,
        partial: None,
    })?;
    match tick(control) {
        Ok(()) => Ok(completed),
        Err(cause) => Err(ComposeFailure {
            cause,
            partial: Some(completed),
        }),
    }
}
