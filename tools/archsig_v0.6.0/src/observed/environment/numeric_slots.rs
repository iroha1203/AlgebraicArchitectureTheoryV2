//! 数値成分の証拠値を、元の一slotの型へ復元する。
use super::*;
impl Environment<'_> {
    pub(in crate::observed) fn restore_numeric_assignment(
        &self,
        values: &super::super::affine::MissingAssignment,
    ) -> Result<Vec<(Fact, Scalar)>, ValidationFailure> {
        fn put(
            value: &mut Scalar,
            path: &[usize],
            replacement: &Scalar,
            c: &Control,
        ) -> Result<(), ValidationFailure> {
            stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
                c.clone().checkpoint(Checkpoint::FiniteIteration)?;
                if let Some((&index, rest)) = path.split_first() {
                    let Scalar::Tuple(items) = value else {
                        return Err("数値補完成分の元型がTupleでない".into());
                    };
                    put(
                        items.get_mut(index).ok_or("数値補完成分位置が元型外")?,
                        rest,
                        replacement,
                        c,
                    )
                } else {
                    if value.ty() != replacement.ty() {
                        return Err("数値補完成分の型が違う".into());
                    }
                    *value = replacement.clone();
                    Ok(())
                }
            })
        }
        let mut fields = BTreeMap::<Fact, Scalar>::new();
        let mut seen = BTreeSet::new();
        for (key, value) in values {
            self.tick()?;
            if !seen.insert(key) {
                return Err("数値補完の同じ成分が重複する".into());
            }
            self.fact(&key.fact)?;
            let field = self.field(
                &key.fact.snapshot,
                &key.fact.subject,
                key.fact.field.as_deref().ok_or("数値成分の元fieldがない")?,
            )?;
            if !matches!(field.slot, Slot::Missing)
                || key.kind.ty() != value.ty()
                || !numeric::is_numeric_type(&field.ty, &self.control)?
            {
                return Err("数値補完の元slot・成分型が違う".into());
            }
            if !fields.contains_key(&key.fact) {
                fields.insert(key.fact.clone(), numeric::zero(&field.ty, &self.control)?);
            }
            put(
                fields.get_mut(&key.fact).ok_or("復元中のslotがない")?,
                &key.component,
                value,
                &self.control,
            )?;
        }
        Ok(fields.into_iter().collect())
    }
}
