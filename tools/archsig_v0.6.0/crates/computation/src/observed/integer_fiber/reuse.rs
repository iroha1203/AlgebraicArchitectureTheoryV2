//! 現在の整数行列に一致する分解だけを共有する。右辺・判断・由来は持たない。
use super::*;
use std::{cell::RefCell, rc::Rc};

#[derive(Debug)]
pub(in crate::observed) struct Entry {
    matrix: Matrix,
    columns: usize,
    decomposition: Arc<Decomposition>,
}
#[derive(Default)]
pub(in crate::observed) struct Pool {
    pub previous: Vec<Arc<Entry>>,
    pub current: Vec<Arc<Entry>>,
}
pub(in crate::observed) type SharedPool = Rc<RefCell<Pool>>;
fn tick(c: &Control) -> Result<(), ValidationFailure> {
    c.checkpoint(Checkpoint::Reuse)?;
    Ok(())
}
fn matches(
    entry: &Entry,
    matrix: &Matrix,
    columns: usize,
    c: &Control,
) -> Result<bool, ValidationFailure> {
    tick(c)?;
    if entry.columns != columns || entry.matrix.len() != matrix.len() {
        return Ok(false);
    }
    for (a, b) in entry.matrix.iter().zip(matrix) {
        tick(c)?;
        if a.len() != b.len() {
            return Ok(false);
        }
        for (a, b) in a.iter().zip(b) {
            tick(c)?;
            if a != b {
                return Ok(false);
            }
        }
    }
    Ok(true)
}
fn copy(matrix: &Matrix, c: &Control) -> Result<Matrix, ValidationFailure> {
    let mut result = Vec::with_capacity(matrix.len());
    for row in matrix {
        tick(c)?;
        let mut values = Vec::with_capacity(row.len());
        for value in row {
            tick(c)?;
            values.push(value.clone());
        }
        result.push(values);
    }
    Ok(result)
}
/// 係数の生成と適用条件は呼出し元が現在入力で検査する。この層の鍵は純粋なZ行列。
pub(in crate::observed) fn solve(
    pool: &SharedPool,
    matrix: &Matrix,
    columns: usize,
    rhs: &[Z],
    c: &Control,
) -> Result<Fiber, ValidationFailure> {
    tick(c)?;
    if matrix.len() != rhs.len() || matrix.iter().any(|r| r.len() != columns) {
        return Err(internal!("整数系の行列・右辺の次元が違う").into());
    }
    let found = {
        let pool = pool.borrow();
        let mut found = None;
        for (current, entry) in pool
            .current
            .iter()
            .map(|e| (true, e))
            .chain(pool.previous.iter().map(|e| (false, e)))
        {
            if matches(entry, matrix, columns, c)? {
                found = Some((current, entry.clone()));
                break;
            }
        }
        found
    };
    let (already_current, entry, reused) = if let Some((current, entry)) = found {
        (current, entry, true)
    } else {
        let decomposition = Arc::new(decompose(matrix, columns, c)?);
        let entry = Arc::new(Entry {
            matrix: copy(matrix, c)?,
            columns,
            decomposition,
        });
        (false, entry, false)
    };
    // 未完了fiberの生成で新しいentryをcurrentへ追加しない。
    let fiber = restore(entry.decomposition.clone(), rhs, c)?;
    if !already_current {
        pool.borrow_mut().current.push(entry);
    }
    #[cfg(test)]
    if reused {
        REUSED.with(|n| n.set(n.get() + 1));
    }
    #[cfg(not(test))]
    let _ = reused;
    Ok(fiber)
}
#[cfg(test)]
thread_local! { static REUSED: std::cell::Cell<usize> = const { std::cell::Cell::new(0) }; }
#[cfg(test)]
pub(in crate::observed) fn reused() -> usize {
    REUSED.with(std::cell::Cell::get)
}

#[cfg(test)]
mod tests {
    use super::*;
    use archsig_common::control::quiet;
    fn matrix(values: &[&[i64]]) -> Matrix {
        values
            .iter()
            .map(|r| r.iter().copied().map(Z::from).collect())
            .collect()
    }
    #[test]
    fn changed_rhs_reuses_elimination_and_keeps_divisibility_and_all_kernel_directions() {
        let c = quiet();
        let a = matrix(&[&[2, 4, 0], &[0, 0, 0]]);
        let old_pool = SharedPool::default();
        let old = solve(&old_pool, &a, 3, &[2.into(), 0.into()], &c).unwrap();
        assert!(old.particular.is_some());
        assert_eq!(old.decomposition.rank, 1);
        let next = SharedPool::default();
        next.borrow_mut().previous = old_pool.borrow().current.clone();
        for rhs in [
            vec![1.into(), 0.into()],
            vec![4.into(), 0.into()],
            vec![2.into(), 1.into()],
        ] {
            let before = generated();
            let new = solve(&next, &a, 3, &rhs, &c).unwrap();
            assert_eq!(generated(), before, "復元より前に分解生成を省く");
            assert!(Arc::ptr_eq(&old.decomposition, &new.decomposition));
            let cold = super::super::solve(&a, 3, &rhs, &c).unwrap();
            assert_eq!(new, cold);
        }
        assert_eq!(next.borrow().current.len(), 1);
        assert_eq!(
            multiply(&a, &old.decomposition.kernel, 2, &c).unwrap(),
            matrix(&[&[0, 0], &[0, 0]])
        );
    }
    #[test]
    fn changed_matrix_or_width_does_not_adopt_the_old_decomposition() {
        let c = quiet();
        let pool = SharedPool::default();
        let a = solve(&pool, &matrix(&[&[2]]), 1, &[2.into()], &c).unwrap();
        let before = generated();
        let b = solve(&pool, &matrix(&[&[3]]), 1, &[2.into()], &c).unwrap();
        assert!(generated() > before);
        assert!(b.particular.is_none());
        assert!(!Arc::ptr_eq(&a.decomposition, &b.decomposition));
        let a = solve(&pool, &vec![], 1, &[], &c).unwrap();
        let b = solve(&pool, &vec![], 2, &[], &c).unwrap();
        assert_eq!(a.decomposition.kernel, matrix(&[&[1]]));
        assert_eq!(b.decomposition.kernel, matrix(&[&[1, 0], &[0, 1]]));
        assert!(!Arc::ptr_eq(&a.decomposition, &b.decomposition));
    }
    #[test]
    fn every_reused_comparison_and_rhs_restoration_checkpoint_stops_without_publishing() {
        use std::cell::Cell;
        let base = SharedPool::default();
        let a = matrix(&[&[2, 4], &[0, 0]]);
        solve(&base, &a, 2, &[2.into(), 0.into()], &quiet()).unwrap();
        let run = |stop: Option<usize>| {
            let seen = Rc::new(Cell::new(0));
            let count = seen.clone();
            let c = Control::new(move |_| {
                count.set(count.get() + 1);
                stop.filter(|n| *n == count.get())
                    .map(|_| archsig_input::result::Signal::Term)
            });
            let pool = SharedPool::default();
            pool.borrow_mut().previous = base.borrow().current.clone();
            let result = solve(&pool, &a, 2, &[4.into(), 0.into()], &c);
            let current = pool.borrow().current.len();
            (result, seen.get(), current)
        };
        let (complete, count, n) = run(None);
        assert!(complete.unwrap().particular.is_some());
        assert_eq!(n, 1);
        for at in 1..=count {
            let (result, _, n) = run(Some(at));
            assert!(
                matches!(result, Err(ValidationFailure::Stop(_))),
                "checkpoint {at}"
            );
            assert_eq!(n, 0, "未完了fiberのcurrent登録なし");
        }
        assert_eq!(base.borrow().current.len(), 1);
    }
}
