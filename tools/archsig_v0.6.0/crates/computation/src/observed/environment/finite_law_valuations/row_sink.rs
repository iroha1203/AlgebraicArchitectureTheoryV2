//! 同じ元Law評価行を詳細表または整数関数表へ消費する。
use super::*;
use num_traits::Zero;

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(in crate::observed) struct RowFlags {
    pub condition_failed: bool,
    pub comparison_missing: bool,
    pub indicator_missing: bool,
    pub completion_missing: bool,
    pub zero: bool,
}
impl RowFlags {
    fn of(row: &FiniteLawRow) -> Self {
        Self {
            condition_failed: row.condition_failed,
            comparison_missing: row.components.as_ref().is_some_and(|cs| {
                cs.iter()
                    .any(|p| p.left.is_some() && p.right.is_some() && p.equal.is_none())
            }),
            indicator_missing: row.indicator.is_none()
                || row
                    .components
                    .as_ref()
                    .is_some_and(|cs| cs.iter().any(|p| p.indicator.is_none())),
            completion_missing: row.scope.completions && row.indicator.is_none(),
            zero: match &row.components {
                Some(cs) => cs
                    .iter()
                    .all(|p| p.indicator.as_ref().is_some_and(Zero::is_zero)),
                None => row.indicator.as_ref().is_some_and(Zero::is_zero),
            },
        }
    }
    fn include(&mut self, other: Self) {
        self.condition_failed |= other.condition_failed;
        self.comparison_missing |= other.comparison_missing;
        self.indicator_missing |= other.indicator_missing;
        self.completion_missing |= other.completion_missing;
    }
}
pub(in crate::observed) trait LawRows: Default + Clone + PartialEq {
    fn store(&mut self, row: FiniteLawRow, c: &Control) -> Result<(), ValidationFailure>;
    fn publish(rows: &mut [&mut Self], points: usize, c: &Control)
    -> Result<(), ValidationFailure>;
    fn len(&self) -> usize;
    fn valid_point(&self, point: usize) -> bool;
    fn condition_failed(&self, point: usize) -> bool;
    fn flags(&self) -> RowFlags;
    fn zero(&self, point: usize) -> bool;
    fn indicator(&self, point: usize, component: Option<&[usize]>) -> Option<&BigInt>;
}
impl LawRows for Vec<FiniteLawRow> {
    fn store(&mut self, row: FiniteLawRow, _: &Control) -> Result<(), ValidationFailure> {
        self.push(row);
        Ok(())
    }
    fn publish(
        rows: &mut [&mut Self],
        points: usize,
        c: &Control,
    ) -> Result<(), ValidationFailure> {
        // 詳細APIは、元point/column順で完成した公開prefixを停止時にも返す。
        let mut published = vec![0usize; rows.len()];
        let result = (|| {
            for point in 0..points {
                c.checkpoint(Checkpoint::FiniteLawEvaluation)?;
                for (count, column) in published.iter_mut().zip(rows.iter_mut()) {
                    c.checkpoint(Checkpoint::FiniteLawEvaluation)?;
                    column
                        .get_mut(point)
                        .ok_or(internal!("安定passの元行がない"))?
                        .point = point;
                    *count += 1;
                    c.checkpoint(Checkpoint::FiniteLawEvaluation)?;
                }
            }
            Ok::<_, ValidationFailure>(())
        })();
        if result.is_err() {
            for (column, count) in rows.iter_mut().zip(published) {
                column.truncate(count);
            }
        }
        result
    }
    fn len(&self) -> usize {
        Vec::len(self)
    }
    fn valid_point(&self, point: usize) -> bool {
        self.get(point).is_some_and(|row| row.point == point)
    }
    fn condition_failed(&self, point: usize) -> bool {
        self.get(point).is_some_and(|row| row.condition_failed)
    }
    fn flags(&self) -> RowFlags {
        let mut flags = RowFlags::default();
        for row in self {
            flags.include(RowFlags::of(row));
        }
        flags
    }
    fn zero(&self, point: usize) -> bool {
        self.get(point).is_some_and(|row| RowFlags::of(row).zero)
    }
    fn indicator(&self, point: usize, component: Option<&[usize]>) -> Option<&BigInt> {
        let row = self.get(point)?;
        match component {
            None => row.indicator.as_ref(),
            Some(path) => row
                .components
                .as_ref()?
                .iter()
                .find(|p| p.path == path)?
                .indicator
                .as_ref(),
        }
    }
}
// native生成は完成族だけを消費し、停止時には理由だけを配送する。
// 各元行の型・支持・Scopeを評価し終えてから、必要な整数関数へ移して破棄する。
#[derive(Clone, Debug, Default, PartialEq)]
pub(in crate::observed) struct IntegerRows {
    whole: Vec<Option<BigInt>>,
    components: Vec<(Vec<usize>, Vec<Option<BigInt>>)>,
    flags: Vec<RowFlags>,
}
impl LawRows for IntegerRows {
    fn store(&mut self, row: FiniteLawRow, c: &Control) -> Result<(), ValidationFailure> {
        c.checkpoint(Checkpoint::FiniteLawEvaluation)?;
        let point = self.whole.len();
        self.flags.push(RowFlags::of(&row));
        self.whole.push(row.indicator);
        let mut components = row.components.unwrap_or_default();
        for (path, values) in &mut self.components {
            c.checkpoint(Checkpoint::FiniteLawEvaluation)?;
            values.push(None);
            if let Some(at) = components.iter().position(|p| p.path == *path) {
                values[point] = components.remove(at).indicator;
            }
        }
        for component in components {
            c.checkpoint(Checkpoint::FiniteLawEvaluation)?;
            if self
                .components
                .iter()
                .any(|(path, _)| *path == component.path)
            {
                continue;
            }
            let mut values = vec![None; point + 1];
            values[point] = component.indicator;
            self.components.push((component.path, values));
        }
        Ok(())
    }
    fn publish(
        rows: &mut [&mut Self],
        points: usize,
        c: &Control,
    ) -> Result<(), ValidationFailure> {
        for column in rows {
            c.checkpoint(Checkpoint::FiniteLawEvaluation)?;
            if column.whole.len() != points
                || column.flags.len() != points
                || column
                    .components
                    .iter()
                    .any(|(_, values)| values.len() != points)
            {
                return Err(internal!("整数関数表が完成Dと違う").into());
            }
        }
        Ok(())
    }
    fn len(&self) -> usize {
        self.whole.len()
    }
    fn valid_point(&self, point: usize) -> bool {
        point < self.whole.len() && point < self.flags.len()
    }
    fn condition_failed(&self, point: usize) -> bool {
        self.flags
            .get(point)
            .is_some_and(|row| row.condition_failed)
    }
    fn flags(&self) -> RowFlags {
        let mut flags = RowFlags::default();
        for row in &self.flags {
            flags.include(*row);
        }
        flags
    }
    fn zero(&self, point: usize) -> bool {
        self.flags.get(point).is_some_and(|row| row.zero)
    }
    fn indicator(&self, point: usize, component: Option<&[usize]>) -> Option<&BigInt> {
        let values = match component {
            None => &self.whole,
            Some(path) => &self.components.iter().find(|(p, _)| *p == path)?.1,
        };
        values.get(point)?.as_ref()
    }
}
