//! 同じ閉包walkを、詳細parameter族とautomaticの元列carrierへ接続する。
use super::*;

type Bindings = Vec<(String, Scalar)>;
type Columns = Vec<(usize, usize, Bindings)>;

pub(in crate::observed) trait ParameterSink:
    Default + Clone + PartialEq + Eq
{
    fn accept(
        &mut self,
        objects: Vec<ObjectLawInstances>,
        readings: &ObjectReadingInstances,
        c: &Control,
    ) -> Result<(), ValidationFailure>;
    fn finish(&mut self, c: &Control) -> Result<(), ValidationFailure>;
    fn columns(
        &self,
        readings: &ObjectReadingInstances,
        c: &Control,
    ) -> Result<Columns, ValidationFailure>;
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(in crate::observed) struct DetailedParameters {
    pub rows: Vec<ParameterRealization>,
}
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(in crate::observed) struct ParameterCarriers {
    bindings: Vec<Vec<Bindings>>,
}
fn same_bindings(
    a: &[(String, Scalar)],
    b: &[(String, Scalar)],
    c: &Control,
) -> Result<bool, ValidationFailure> {
    if a.len() != b.len() {
        return Ok(false);
    }
    for ((name, a), (other, b)) in a.iter().zip(b) {
        tick(c)?;
        if name != other || !validation_identity::scalar(a, b, c)? {
            return Ok(false);
        }
    }
    Ok(true)
}
fn add_binding(
    values: &mut Vec<Bindings>,
    binding: &[(String, Scalar)],
    c: &Control,
) -> Result<(), ValidationFailure> {
    let mut duplicate = false;
    for previous in values.iter() {
        duplicate |= same_bindings(previous, binding, c)?;
    }
    if !duplicate {
        values.push(binding.to_vec());
    }
    Ok(())
}
fn expand<B: AsRef<[(String, Scalar)]>>(
    readings: &ObjectReadingInstances,
    carriers: &[(usize, B)],
    c: &Control,
) -> Result<Columns, ValidationFailure> {
    let mut selected = vec![];
    for object in 0..readings.objects().len() {
        for (instance, bindings) in carriers {
            tick(c)?;
            selected.push((object, *instance, bindings.as_ref().to_vec()));
        }
    }
    Ok(selected)
}
impl ParameterSink for DetailedParameters {
    fn accept(
        &mut self,
        objects: Vec<ObjectLawInstances>,
        _: &ObjectReadingInstances,
        _: &Control,
    ) -> Result<(), ValidationFailure> {
        self.rows.push(ParameterRealization { point: 0, objects });
        Ok(())
    }
    fn finish(&mut self, c: &Control) -> Result<(), ValidationFailure> {
        let mut completed = 0;
        let result = (|| {
            for (point, row) in self.rows.iter_mut().enumerate() {
                c.checkpoint(Checkpoint::FiniteLawEvaluation)?;
                row.point = point;
                completed += 1;
                c.checkpoint(Checkpoint::FiniteLawRequired)?;
            }
            Ok::<_, ValidationFailure>(())
        })();
        if result.is_err() {
            self.rows.truncate(completed);
        }
        result
    }
    fn columns(
        &self,
        readings: &ObjectReadingInstances,
        c: &Control,
    ) -> Result<Columns, ValidationFailure> {
        let mut carriers = vec![];
        for (instance, original) in readings.instances().iter().enumerate() {
            tick(c)?;
            if original.declaration().kind != "law" {
                continue;
            }
            let mut bindings = vec![];
            for point in &self.rows {
                for object in &point.objects {
                    let entry = object
                        .entries()
                        .iter()
                        .find(|e| e.instance == instance)
                        .ok_or(internal!("自動Law族の元instanceがない"))?;
                    for row in &entry.rows {
                        tick(c)?;
                        add_binding(&mut bindings, &row.bindings, c)?;
                    }
                }
            }
            carriers.extend(bindings.into_iter().map(|binding| (instance, binding)));
        }
        expand(readings, &carriers, c)
    }
}
impl ParameterSink for ParameterCarriers {
    fn accept(
        &mut self,
        objects: Vec<ObjectLawInstances>,
        readings: &ObjectReadingInstances,
        c: &Control,
    ) -> Result<(), ValidationFailure> {
        // native consumerは詳細履歴を公開しない。実際のcarrier変換中に停止を確認する。
        c.checkpoint(Checkpoint::FiniteLawEvaluation)?;
        if self.bindings.is_empty() {
            self.bindings
                .resize_with(readings.instances().len(), Vec::new);
        }
        for object in objects {
            for entry in object.entries() {
                tick(c)?;
                let bindings = self
                    .bindings
                    .get_mut(entry.instance)
                    .ok_or(internal!("parameter carrierの元instanceがない"))?;
                for row in &entry.rows {
                    tick(c)?;
                    add_binding(bindings, &row.bindings, c)?;
                }
            }
        }
        Ok(())
    }
    fn finish(&mut self, c: &Control) -> Result<(), ValidationFailure> {
        c.checkpoint(Checkpoint::FiniteLawRequired)?;
        Ok(())
    }
    fn columns(
        &self,
        readings: &ObjectReadingInstances,
        c: &Control,
    ) -> Result<Columns, ValidationFailure> {
        let mut carriers = vec![];
        for (instance, original) in readings.instances().iter().enumerate() {
            tick(c)?;
            if original.declaration().kind != "law" {
                continue;
            }
            if let Some(bindings) = self.bindings.get(instance) {
                carriers.extend(bindings.iter().map(|binding| (instance, binding)));
            }
        }
        expand(readings, &carriers, c)
    }
}
