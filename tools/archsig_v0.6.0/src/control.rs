//! 検査・要求解決・評価で共有する、注入可能な協調中断制御。

use std::sync::{
    Arc,
    atomic::{AtomicI32, Ordering},
};
#[cfg(any(test, feature = "test-support"))]
use std::{rc::Rc, sync::Mutex};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Signal {
    Int,
    Term,
}

impl Signal {
    pub fn wire(self) -> &'static str {
        match self {
            Signal::Int => "SIGINT",
            Signal::Term => "SIGTERM",
        }
    }
    /// 取消のIssue。要求固有の依存は呼出し側が付ける。
    pub fn issue(self) -> crate::canonical::Json {
        use crate::canonical::Json;
        Json::obj([
            ("code", Json::str("cancelled")),
            ("dependencies", Json::Arr(vec![])),
            ("missing", Json::Arr(vec![])),
            (
                "message",
                Json::str(format!("interrupted by signal {}", self.wire())),
            ),
            ("details", Json::obj([("signal", Json::str(self.wire()))])),
        ])
    }
}

/// 原始演算または有限反復の境界。試験用 probe も同じ境界を受け取る。
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Checkpoint {
    Work,
    InputBundle,
    TableComparison,
    BeforeDefinitions,
    DefinitionIteration,
    DefinitionSchema,
    DefinitionCanonical,
    DefinitionSemantics,
    DefinitionData,
    DefinitionDependency,
    BeforeLaw,
    LawIteration,
    LawName,
    LawCanonical,
    LawSemantics,
    LawCycle,
    LawChange,
    AfterLaw,
    BeforeArchMap,
    ArchMapIteration,
    ArchMapSchema,
    ArchMapCanonical,
    ArchMapTerm,
    Completion,
    AfterArchMap,
    Resolve,
    RequestSyntax,
    RequestBinding,
    RequestDependency,
    Projection,
    Reuse,
    ObservationPlan,
    Configuration,
    ConfigurationMap,
    NativeResultNode,
    InternalArrow,
    InternalArrowRow,
    InternalArrowRoster,
    ConfigurationOperation,
    ConfigurationProfile,
    ConfigurationTransport,
    ConfigurationTransportObject,
    ConfigurationTransportGenerator,
    DeclarationCorrespondence,
    ReferenceTypeTransport,
    FiniteValueTransport,
    NumericValueTransport,
    ObjectInstances,
    ObjectEvaluation,
    ObjectEvaluationTable,
    ObjectViewFamily,
    ObjectViewFamilyRow,
    ObjectViewTransport,
    ObjectViewTransportFamily,
    ObjectViewCompatibility,
    ObjectViewCompatibilityPoint,
    ObjectViewTransportFamilyRow,
    ObjectLawTransport,
    ObjectLawFamily,
    ObjectLawCompatibility,
    ObjectLawCompatibilityPoint,
    ObjectLawResiduals,
    ObjectLawResidualPoint,
    ObjectLawCircuits,
    ObjectLawCircuit,
    ObjectLawCircuitTransport,
    ObjectLawCircuitTransportPoint,
    EquationPresentation,
    EquationPresentationRow,
    PolynomialObservable,
    PolynomialObservableCoordinate,
    FinitePolynomialTable,
    PrimitiveValuation,
    ChangeWitness,
    Quotient,
    QuotientGuardedInstance,
    Localize,
    FiniteLawSelection,
    FiniteLawAutomatic,
    FiniteLawDomain,
    FiniteLawEvaluation,
    FiniteLawRequired,
    FiniteLawComponent,
    FiniteLawOperand,
    FiniteLawFunction,
    FiniteLawQuotient,
    Expression,
    FiniteIteration,
}

/// 既存の入力エラーと協調中断を混同せずに伝播する。
#[derive(Debug)]
pub enum CheckFailure<F> {
    Input(F),
    Stopped(Signal),
}

#[cfg(any(test, feature = "test-support"))]
type Probe = Rc<Mutex<Box<dyn FnMut(Checkpoint) -> Option<Signal>>>>;

/// 最初に記録された取消を共有する。通常のcheckpointはatomicの読み取りだけを行う。
#[derive(Clone)]
pub struct Control {
    stopped: Arc<AtomicI32>,
    int: i32,
    term: i32,
    #[cfg(any(test, feature = "test-support"))]
    probe: Option<Probe>,
}

impl std::fmt::Debug for Control {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Control")
            .field("stopped", &self.stop_reason())
            .finish_non_exhaustive()
    }
}

/// 止めない制御。テストの既定の入力として使う。
#[cfg(any(test, feature = "test-support"))]
pub fn quiet() -> Control {
    Control::unlimited()
}

impl Default for Control {
    fn default() -> Self {
        Self::unlimited()
    }
}

impl Control {
    /// 試験用probe。通常のビルドにはcallbackもlockも含めない。
    #[cfg(any(test, feature = "test-support"))]
    pub fn new(probe: impl FnMut(Checkpoint) -> Option<Signal> + 'static) -> Self {
        let mut control = Self::unlimited();
        control.probe = Some(Rc::new(Mutex::new(Box::new(probe))));
        control
    }

    /// CLIが最初に捕捉したsignalを保持するatomicを共有する。
    /// 呼出し側は0からint/termへの一方向のcompare_exchangeだけで更新する。
    /// OSのsignal番号はCLIから渡し、共通層はOSに依存しない。
    pub fn from_signal_flag(stopped: Arc<AtomicI32>, int: i32, term: i32) -> Self {
        assert!(
            int != 0 && term != 0 && int != term,
            "distinct nonzero signal codes"
        );
        Self {
            stopped,
            int,
            term,
            #[cfg(any(test, feature = "test-support"))]
            probe: None,
        }
    }

    /// 取消を観測しない内部計算用の制御。
    pub fn unlimited() -> Self {
        Self::from_signal_flag(Arc::new(AtomicI32::new(0)), 1, 2)
    }

    pub fn stop_reason(&self) -> Option<Signal> {
        // Signal carries no accompanying data; atomic coherence alone is sufficient.
        let value = self.stopped.load(Ordering::Relaxed);
        if value == self.int {
            Some(Signal::Int)
        } else if value == self.term {
            Some(Signal::Term)
        } else {
            None
        }
    }

    #[inline]
    pub fn checkpoint(&self, _point: Checkpoint) -> Result<(), Signal> {
        if let Some(signal) = self.stop_reason() {
            return Err(signal);
        }
        #[cfg(any(test, feature = "test-support"))]
        if let Some(probe) = &self.probe
            && let Some(signal) = (probe.lock().expect("test probe is not poisoned"))(_point)
        {
            let code = match signal {
                Signal::Int => self.int,
                Signal::Term => self.term,
            };
            let _ = self
                .stopped
                .compare_exchange(0, code, Ordering::Relaxed, Ordering::Relaxed);
            return Err(self.stop_reason().expect("signal was recorded"));
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::cell::Cell;

    #[test]
    fn unlimited_and_default_never_stop() {
        for control in [Control::unlimited(), Control::default()] {
            let shared = control.clone();
            for point in [
                Checkpoint::InputBundle,
                Checkpoint::Localize,
                Checkpoint::Expression,
            ] {
                assert_eq!(control.checkpoint(point), Ok(()));
                assert_eq!(shared.checkpoint(point), Ok(()));
            }
            assert!(control.stop_reason().is_none());
            assert!(shared.stop_reason().is_none());
        }
    }

    #[test]
    fn atomic_signal_is_observed_by_shared_references() {
        for (code, expected) in [(2, Signal::Int), (15, Signal::Term)] {
            let flag = Arc::new(AtomicI32::new(0));
            let control = Control::from_signal_flag(flag.clone(), 2, 15);
            let shared = control.clone();
            assert_eq!(control.checkpoint(Checkpoint::Work), Ok(()));
            flag.compare_exchange(0, code, Ordering::Relaxed, Ordering::Relaxed)
                .unwrap();
            assert_eq!(control.checkpoint(Checkpoint::Work), Err(expected));
            assert_eq!(shared.stop_reason(), Some(expected));
            assert!(
                flag.compare_exchange(0, 99, Ordering::Relaxed, Ordering::Relaxed)
                    .is_err()
            );
            assert_eq!(shared.checkpoint(Checkpoint::Work), Err(expected));
        }
    }

    #[test]
    fn injected_signal_latches_and_is_shared() {
        let probes = Rc::new(Cell::new(0));
        let calls = probes.clone();
        let control = Control::new(move |_| {
            calls.set(calls.get() + 1);
            (calls.get() == 3).then_some(Signal::Term)
        });
        let shared = control.clone();
        assert_eq!(control.checkpoint(Checkpoint::InputBundle), Ok(()));
        assert_eq!(shared.checkpoint(Checkpoint::Localize), Ok(()));
        assert_eq!(
            control.checkpoint(Checkpoint::Expression),
            Err(Signal::Term)
        );
        assert_eq!(shared.checkpoint(Checkpoint::Resolve), Err(Signal::Term));
        assert_eq!(shared.stop_reason(), Some(Signal::Term));
        assert_eq!(probes.get(), 3, "停止後はprobeを呼ばない");
    }
}
