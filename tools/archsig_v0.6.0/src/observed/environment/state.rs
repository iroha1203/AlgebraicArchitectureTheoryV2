//! 評価中だけ差し替える状態。通常終了・途中のエラー・panicのいずれでも元に戻す。
use std::cell::{Cell, RefCell};

pub(super) trait ScopedReplace<T> {
    fn swap(&self, value: T) -> T;

    fn scoped(&self, value: T) -> StateGuard<'_, Self, T>
    where
        Self: Sized,
    {
        StateGuard {
            cell: self,
            previous: Some(self.swap(value)),
        }
    }
}
impl<T> ScopedReplace<T> for RefCell<T> {
    fn swap(&self, value: T) -> T {
        self.replace(value)
    }
}
impl<T: Copy> ScopedReplace<T> for Cell<T> {
    fn swap(&self, value: T) -> T {
        self.replace(value)
    }
}

pub(super) struct StateGuard<'a, C: ScopedReplace<T>, T> {
    cell: &'a C,
    previous: Option<T>,
}
impl<C: ScopedReplace<T>, T> StateGuard<'_, C, T> {
    /// 集めた一時状態を返し、その場で外側の状態に戻す。
    pub(super) fn restore(mut self) -> T {
        self.cell
            .swap(self.previous.take().expect("未復元の一時状態"))
    }
}
impl<C: ScopedReplace<T>, T> Drop for StateGuard<'_, C, T> {
    fn drop(&mut self) {
        if let Some(previous) = self.previous.take() {
            self.cell.swap(previous);
        }
    }
}

// 評価の入れ子に応じてguardで切り替える状態。
use super::*;
pub(crate) struct EvaluationState {
    pub(super) architecture: RefCell<Option<architecture_environment::ArchitectureContext>>,
    pub(super) context: Cell<Option<crate::observed::call::Context>>,
    pub(super) completion_values: RefCell<CompletionValues>,
    pub(super) value_read: Cell<bool>,
    pub(super) primitive_reads: RefCell<Option<BTreeSet<Fact>>>,
    pub(super) missing_slot_reads: RefCell<Option<BTreeSet<Fact>>>,
    pub(super) evaluation_capture: RefCell<Option<quotient_evaluation::EvaluationCapture>>,
    pub(super) scoped_context: Cell<Option<crate::observed::call::Context>>,
    pub(super) validation_depth: Cell<usize>,
    pub(super) cutoff: Cell<usize>,
    pub(super) answer_rechecks: RefCell<BTreeSet<usize>>,
    pub(super) universal_context: RefCell<Option<universal::AnalysisContext>>,
    #[cfg(test)]
    pub(super) optional_name_context: Cell<Option<crate::observed::call::Context>>,
    #[cfg(test)]
    pub(super) name_token_observer: RefCell<Option<NameTokenObserver>>,
}

impl EvaluationState {
    pub(super) fn validation_session<T, E>(
        &self,
        results: &ResultStore,
        run: impl FnOnce() -> Result<T, E>,
    ) -> Result<T, E> {
        // Source/Frame の再分析と Evaluation の再検査は相互再入する。
        // Source・pattern・実引数復元の局所値を確保する前に十分な余白を取る。
        stacker::maybe_grow(256 * 1024, 1024 * 1024, || {
            let depth = self.validation_depth.get();
            if depth == 0 {
                *results.cache.borrow_mut() = ValidationCache::default();
                results.validation_snapshot.replace(None);
            }
            let depth_guard = self.validation_depth.scoped(depth + 1);
            let result = run();
            depth_guard.restore();
            // Graphのprefixを確認できないroot解析では、成功も失敗も必ず破棄する。
            if depth == 0 {
                *results.cache.borrow_mut() = ValidationCache::default();
                results.validation_snapshot.replace(None);
            }
            result
        })
    }
}

impl Default for EvaluationState {
    fn default() -> Self {
        Self {
            architecture: RefCell::new(None),
            context: Cell::new(None),
            completion_values: RefCell::new(Vec::new()),
            value_read: Cell::new(false),
            primitive_reads: RefCell::new(None),
            missing_slot_reads: RefCell::new(None),
            evaluation_capture: RefCell::new(None),
            scoped_context: Cell::new(None),
            validation_depth: Cell::new(0),
            cutoff: Cell::new(usize::MAX),
            answer_rechecks: RefCell::new(BTreeSet::new()),
            universal_context: RefCell::new(None),
            #[cfg(test)]
            optional_name_context: Cell::new(None),
            #[cfg(test)]
            name_token_observer: RefCell::new(None),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn nested_refcell_states_restore_on_question_mark_and_explicit_return() {
        fn inner(cell: &RefCell<Vec<u8>>) -> Result<(), ()> {
            let _state = cell.scoped(vec![2]);
            Err(())?;
            Ok(())
        }
        let cell = RefCell::new(vec![0]);
        let outer = cell.scoped(vec![1]);
        assert_eq!(inner(&cell), Err(()));
        assert_eq!(*cell.borrow(), vec![1]);
        let returned = (|| {
            let _state = cell.scoped(vec![3]);
            return 7;
        })();
        assert_eq!(returned, 7);
        assert_eq!(outer.restore(), vec![1]);
        assert_eq!(*cell.borrow(), vec![0]);
    }

    #[test]
    fn cells_restore_when_unwinding() {
        let cell = Cell::new(4);
        let captured = RefCell::new(vec![5]);
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let _cell = cell.scoped(6);
            let _captured = captured.scoped(vec![7]);
            panic!("injected early exit");
        }));
        assert!(result.is_err());
        assert_eq!(cell.get(), 4);
        assert_eq!(*captured.borrow(), vec![5]);
    }
    #[test]
    fn local_point_restores_both_collectors_after_an_evaluator_panic() {
        use super::super::{Environment, ValidationFailure};
        use crate::control::Control;
        use crate::input::{InputSources, check_inputs};
        use std::rc::Rc;
        let inputs = check_inputs(
            InputSources::from_bytes(
                vec![include_bytes!("../../../tests/fixtures/counter.atoms.json").to_vec()],
                include_bytes!("../../../tests/fixtures/counter.law").to_vec(),
                include_bytes!("../../../tests/fixtures/counter.archmap.json").to_vec(),
            ),
            &Control::unlimited(),
        )
        .unwrap();
        let armed = Rc::new(Cell::new(false));
        let observed = armed.clone();
        let control = Control::new(move |_| {
            assert!(!observed.get(), "injected evaluator panic");
            None
        });
        let env = Environment::new(&inputs, &control).unwrap();
        let declaration = inputs
            .law()
            .declarations()
            .values()
            .find(|d| matches!(d.signature, crate::law::model::Signature::Law { .. }))
            .unwrap();
        armed.set(true);
        let failure = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            env.local_point(declaration, &[])
        }));
        assert!(failure.is_err());
        assert!(env.state.missing_slot_reads.borrow().is_none());
        assert!(env.state.evaluation_capture.borrow().is_none());
        armed.set(false);
        let failure = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            env.state
                .validation_session(&env.results, || -> Result<(), ValidationFailure> {
                    panic!("injected validation panic")
                })
        }));
        assert!(failure.is_err());
        assert_eq!(env.state.validation_depth.get(), 0);
    }
}
