//! 全整数fiberの共有更新への像と、見えない全fiber。Graphや由来を持たない。
use super::*;
use num_bigint::{BigUint, Sign};

#[derive(Debug)]
pub(in crate::observed) struct Projection {
    image: Arc<reuse::Entry>,
    pub shared_rows: Vec<usize>,
    pub origin: Vec<Z>,
    pub action: Matrix,
}
fn checked(c: &Control) -> Result<(), ValidationFailure> {
    c.checkpoint(Checkpoint::PrimitiveValuation)?;
    Ok(())
}
impl Projection {
    pub(in crate::observed) fn new(
        pool: &reuse::SharedPool,
        particular: &[Z],
        kernel: &Matrix,
        action: &Matrix,
        offset: &[Z],
        shared_rows: Vec<usize>,
        c: &Control,
    ) -> Result<Self, ValidationFailure> {
        let n = particular.len();
        let d = kernel.first().map_or(0, Vec::len);
        if kernel.len() != n
            || kernel.iter().any(|r| r.len() != d)
            || offset.len() != action.len()
            || action.iter().any(|r| r.len() != n)
        {
            return Err(internal!("整数fiberと更新写像の寸法が違う").into());
        }
        let mut matrix = Vec::with_capacity(shared_rows.len());
        let mut origin = Vec::with_capacity(shared_rows.len());
        for index in &shared_rows {
            checked(c)?;
            let row = action.get(*index).ok_or(internal!("共有更新の行がない"))?;
            let mut constant = offset[*index].clone();
            let mut values = vec![Z::zero(); d];
            for (i, a) in row.iter().enumerate() {
                checked(c)?;
                constant += a * &particular[i];
                for (j, k) in kernel[i].iter().enumerate() {
                    checked(c)?;
                    values[j] += a * k;
                }
            }
            origin.push(constant);
            matrix.push(values);
        }
        let image = reuse::factor(pool, matrix, d, c)?;
        let rank = image.decomposition().rank;
        // Cの実際の整数像の基底。右変換の先頭列を使い、周囲の格子へ拡大しない。
        let mut action = vec![vec![Z::zero(); rank]; shared_rows.len()];
        for (i, row) in image.matrix().iter().enumerate() {
            for (k, a) in row.iter().enumerate() {
                for (value, right) in action[i].iter_mut().zip(&image.decomposition().right[k]) {
                    checked(c)?;
                    *value += a * right;
                }
            }
        }
        Ok(Self {
            image,
            shared_rows,
            origin,
            action,
        })
    }
    pub(in crate::observed) fn coefficients(&self) -> &Matrix {
        self.image.matrix()
    }
    pub(in crate::observed) fn visible(&self) -> usize {
        self.image.decomposition().rank
    }
    pub(in crate::observed) fn hidden(&self) -> usize {
        self.image.decomposition().right.len() - self.visible()
    }
    pub(in crate::observed) fn constraints(
        &self,
        fixed: &[(usize, Z)],
        c: &Control,
    ) -> Result<(Matrix, Vec<Z>), ValidationFailure> {
        let mut matrix = Vec::with_capacity(fixed.len());
        let mut rhs = Vec::with_capacity(fixed.len());
        for (index, value) in fixed {
            checked(c)?;
            matrix.push(
                self.action
                    .get(*index)
                    .ok_or(internal!("固定する共有更新の行がない"))?
                    .clone(),
            );
            rhs.push(value - &self.origin[*index]);
        }
        Ok((matrix, rhs))
    }
    #[cfg(test)]
    pub(in crate::observed) fn solve(
        &self,
        pool: &reuse::SharedPool,
        fixed: &[(usize, Z)],
        c: &Control,
    ) -> Result<Fiber, ValidationFailure> {
        let (matrix, rhs) = self.constraints(fixed, c)?;
        reuse::solve(pool, &matrix, self.visible(), &rhs, c)
    }
    fn map_coefficients(
        &self,
        global_kernel: &Matrix,
        visible: &[Z],
        hidden: &[Z],
        c: &Control,
    ) -> Result<Vec<Z>, ValidationFailure> {
        if visible.len() != self.visible() || hidden.len() != self.hidden() {
            return Err(internal!("共有像と内部fiberの幅が違う").into());
        }
        let mut coefficients = Vec::with_capacity(visible.len() + hidden.len());
        for value in visible.iter().chain(hidden) {
            checked(c)?;
            coefficients.push(value.clone());
        }
        let original_free = apply(&self.image.decomposition().right, &coefficients, c)?;
        apply(global_kernel, &original_free, c)
    }
    pub(in crate::observed) fn free(&self, range: &Fiber) -> Result<usize, ValidationFailure> {
        if range.decomposition.right.len() != self.visible()
            || range.decomposition.rank > self.visible()
        {
            return Err(internal!("範囲fiberと共有像の座標が違う").into());
        }
        Ok(self.visible() - range.decomposition.rank + self.hidden())
    }
    pub(in crate::observed) fn candidate(
        &self,
        global_origin: &[Z],
        global_kernel: &Matrix,
        range: &Fiber,
        index: &BigUint,
        c: &Control,
    ) -> Result<Option<Vec<Z>>, ValidationFailure> {
        let Some(origin) = &range.particular else {
            return Ok(None);
        };
        let Some(coefficients) = ordinal(index, self.free(range)?, c)? else {
            return Ok(None);
        };
        let free_visible = self.visible() - range.decomposition.rank;
        let mut visible = apply(
            &range.decomposition.kernel,
            &coefficients[..free_visible],
            c,
        )?;
        for (a, b) in visible.iter_mut().zip(origin) {
            checked(c)?;
            *a += b;
        }
        let mut parameters =
            self.map_coefficients(global_kernel, &visible, &coefficients[free_visible..], c)?;
        if parameters.len() != global_origin.len() {
            return Err(internal!("元Assignmentの幅が違う").into());
        }
        for (a, b) in parameters.iter_mut().zip(global_origin) {
            checked(c)?;
            *a += b;
        }
        Ok(Some(parameters))
    }
    /// 必要な列だけ元座標へ戻す。全核の数値行列を表示前に複製しない。
    pub(in crate::observed) fn kernel_column(
        &self,
        global_kernel: &Matrix,
        range: &Fiber,
        j: usize,
        c: &Control,
    ) -> Result<Vec<Z>, ValidationFailure> {
        let free = self.free(range)?;
        let free_visible = self.visible() - range.decomposition.rank;
        if j >= free {
            return Err(internal!("整数fiberの核列が範囲外").into());
        }
        checked(c)?;
        let mut visible = vec![Z::zero(); self.visible()];
        let mut hidden = vec![Z::zero(); self.hidden()];
        if j < free_visible {
            for (i, row) in range.decomposition.kernel.iter().enumerate() {
                checked(c)?;
                visible[i] = row[j].clone();
            }
        } else {
            hidden[j - free_visible] = Z::one();
        }
        self.map_coefficients(global_kernel, &visible, &hidden, c)
    }
    #[cfg(test)]
    pub(in crate::observed) fn kernel(
        &self,
        global_kernel: &Matrix,
        range: &Fiber,
        c: &Control,
    ) -> Result<Matrix, ValidationFailure> {
        let free = self.free(range)?;
        let mut result = vec![vec![Z::zero(); free]; global_kernel.len()];
        for j in 0..free {
            for (row, value) in
                result
                    .iter_mut()
                    .zip(self.kernel_column(global_kernel, range, j, c)?)
            {
                row[j] = value;
            }
        }
        Ok(result)
    }
}
/// 公開済みの原点と核列の順序で、一つの元Assignmentだけを復元する。
pub(in crate::observed) fn in_basis(
    origin: Option<&[Z]>,
    kernel: &Matrix,
    index: &BigUint,
    c: &Control,
) -> Result<Option<Vec<Z>>, ValidationFailure> {
    checked(c)?;
    let Some(origin) = origin else {
        return Ok(None);
    };
    let dimensions = kernel.first().map_or(0, Vec::len);
    let Some(coefficients) = ordinal(index, dimensions, c)? else {
        return Ok(None);
    };
    let mut point = apply(kernel, &coefficients, c)?;
    if point.len() != origin.len() {
        return Err(internal!("公開整数fiberの原点と核の幅が違う").into());
    }
    for (value, constant) in point.iter_mut().zip(origin) {
        checked(c)?;
        *value += constant;
    }
    Ok(Some(point))
}
fn ordinal(
    index: &BigUint,
    dimensions: usize,
    c: &Control,
) -> Result<Option<Vec<Z>>, ValidationFailure> {
    checked(c)?;
    if dimensions == 0 {
        return Ok(index.is_zero().then(Vec::new));
    }
    let mut values = vec![BigUint::zero(); dimensions];
    for bit in 0..index.bits() {
        checked(c)?;
        if index.bit(bit) {
            values[(bit % dimensions as u64) as usize].set_bit(bit / dimensions as u64, true);
        }
    }
    let mut result = Vec::with_capacity(dimensions);
    for n in values {
        checked(c)?;
        let odd = n.bit(0);
        let half = n >> 1;
        result.push(if odd {
            Z::from_biguint(Sign::Plus, half) + 1
        } else {
            -Z::from_biguint(Sign::Plus, half)
        });
    }
    Ok(Some(result))
}

#[cfg(test)]
mod tests {
    use super::*;
    use archsig_common::control::quiet;
    use std::collections::BTreeSet;
    fn matrix(rows: &[&[i64]]) -> Matrix {
        rows.iter()
            .map(|r| r.iter().copied().map(Z::from).collect())
            .collect()
    }
    fn example(
        pool: &reuse::SharedPool,
        origin: &[Z],
        kernel: &Matrix,
        shared: Vec<usize>,
    ) -> Projection {
        Projection::new(
            pool,
            origin,
            kernel,
            &matrix(&[&[1, 0, 0], &[0, 1, 0], &[0, 0, 1]]),
            &vec![0.into(); 3],
            shared,
            &quiet(),
        )
        .unwrap()
    }
    #[test]
    fn exact_shared_image_keeps_divisibility_and_hidden_original_assignments() {
        let c = quiet();
        let pool = reuse::SharedPool::default();
        let kernel = matrix(&[&[1, 0], &[2, 0], &[0, 1]]);
        let origin = vec![0.into(); 3];
        let p = example(&pool, &origin, &kernel, vec![1]);
        assert_eq!(p.visible(), 1);
        assert_eq!(p.hidden(), 1);
        let odd = p.solve(&pool, &[(0, 1.into())], &c).unwrap();
        assert!(odd.particular.is_none());
        let even = p.solve(&pool, &[(0, 2.into())], &c).unwrap();
        assert_eq!(p.free(&even).unwrap(), 1);
        assert_eq!(
            p.kernel(&kernel, &even, &c).unwrap(),
            matrix(&[&[0], &[0], &[1]])
        );
        for (index, q) in [(0, 0), (1, 1), (2, -1), (3, 2)] {
            assert_eq!(
                p.candidate(&origin, &kernel, &even, &BigUint::from(index as u32), &c)
                    .unwrap(),
                Some(vec![1.into(), 2.into(), q.into()])
            );
        }
        let all = p.solve(&pool, &[], &c).unwrap();
        let points = (0u32..64)
            .map(|i| {
                p.candidate(&origin, &kernel, &all, &i.into(), &c)
                    .unwrap()
                    .unwrap()
            })
            .collect::<BTreeSet<_>>();
        assert_eq!(points.len(), 64);
        for u in -2..=2 {
            for q in -2..=2 {
                assert!(points.contains(&vec![u.into(), (2 * u).into(), q.into()]));
            }
        }
    }
    #[test]
    fn basis_changes_preserve_original_fibers_and_constant_updates_share_the_image() {
        let c = quiet();
        let pool = reuse::SharedPool::default();
        let kernel = matrix(&[&[1, 1], &[2, 2], &[1, 0]]);
        let origin = vec![0.into(); 3];
        let p = example(&pool, &origin, &kernel, vec![1]);
        let range = p.solve(&pool, &[(0, 2.into())], &c).unwrap();
        let k = p.kernel(&kernel, &range, &c).unwrap();
        assert_eq!(k[0], vec![Z::zero()]);
        assert_eq!(k[1], vec![Z::zero()]);
        assert_eq!(k[2][0].abs(), Z::one());
        for i in 0..7u32 {
            let point = p
                .candidate(&origin, &kernel, &range, &i.into(), &c)
                .unwrap()
                .unwrap();
            assert_eq!(&point[..2], &[Z::one(), Z::from(2)]);
        }
        let before = generated();
        let next = example(&pool, &[2.into(), 4.into(), 0.into()], &kernel, vec![1]);
        assert_eq!(generated(), before);
        assert!(Arc::ptr_eq(&p.image, &next.image));
        let range = next.solve(&pool, &[(0, 6.into())], &c).unwrap();
        let point = next
            .candidate(
                &[2.into(), 4.into(), 0.into()],
                &kernel,
                &range,
                &0u32.into(),
                &c,
            )
            .unwrap()
            .unwrap();
        assert_eq!(&point[..2], &[Z::from(3), Z::from(6)]);
    }
    #[test]
    fn empty_shared_part_and_zero_dimensional_assignments_keep_their_full_meaning() {
        let c = quiet();
        let pool = reuse::SharedPool::default();
        let k = matrix(&[&[1, 0], &[2, 0], &[0, 1]]);
        let p = example(&pool, &vec![0.into(); 3], &k, vec![]);
        let range = p.solve(&pool, &[], &c).unwrap();
        assert_eq!(p.visible(), 0);
        assert_eq!(p.hidden(), 2);
        assert_eq!(p.kernel(&k, &range, &c).unwrap(), k);
        let p =
            Projection::new(&pool, &[], &vec![], &vec![vec![]], &[3.into()], vec![0], &c).unwrap();
        let range = p.solve(&pool, &[(0, 3.into())], &c).unwrap();
        assert_eq!(
            p.candidate(&[], &vec![], &range, &0u32.into(), &c).unwrap(),
            Some(vec![])
        );
        assert_eq!(
            p.candidate(&[], &vec![], &range, &1u32.into(), &c).unwrap(),
            None
        );
        assert!(
            p.solve(&pool, &[(0, 4.into())], &c)
                .unwrap()
                .particular
                .is_none()
        );
    }
    #[test]
    fn projection_restore_and_ordinal_stop_at_every_checkpoint() {
        use std::{cell::Cell, rc::Rc};
        let run = |stop: Option<usize>| {
            let seen = Rc::new(Cell::new(0));
            let count = seen.clone();
            let c = Control::new(move |_| {
                count.set(count.get() + 1);
                stop.filter(|n| *n == count.get())
                    .map(|_| archsig_input::result::Signal::Term)
            });
            let result = (|| {
                let pool = reuse::SharedPool::default();
                let k = matrix(&[&[1, 0], &[2, 0], &[0, 1]]);
                let origin = vec![0.into(); 3];
                let p = Projection::new(
                    &pool,
                    &origin,
                    &k,
                    &matrix(&[&[0, 1, 0]]),
                    &[0.into()],
                    vec![0],
                    &c,
                )?;
                let range = p.solve(&pool, &[], &c)?;
                p.candidate(&origin, &k, &range, &BigUint::from(23u32), &c)?;
                p.kernel(&k, &range, &c)?;
                in_basis(Some(&origin), &k, &BigUint::from(23u32), &c)
            })();
            (result, seen.get())
        };
        let (done, n) = run(None);
        assert!(done.is_ok());
        for at in 1..=n {
            assert!(
                matches!(run(Some(at)).0, Err(ValidationFailure::Stop(_))),
                "checkpoint {at}"
            );
        }
    }
}
