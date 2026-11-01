//! 検査・要求解決・評価で共有する、注入可能な協調中断制御。

use std::{cell::RefCell, rc::Rc};

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
}

/// 原始演算または有限反復の境界。試験用 probe も同じ境界を受け取る。
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Checkpoint {
    InputBundle,
    TableComparison,
    BeforeDefinitions,
    DefinitionIteration,
    DefinitionSchema,
    DefinitionCanonical,
    DefinitionSemantics,
    DefinitionData,
    DefinitionDependency,
    AfterDefinitions,
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
    ObjectLawResidualCase,
    ObjectLawResidualPoint,
    ObjectLawCircuits,
    ObjectLawCircuitPoint,
    ObjectLawCircuit,
    ObjectLawCircuitTransport,
    ObjectLawCircuitTransportPoint,
    EquationPresentation,
    EquationPresentationRow,
    PolynomialObservable,
    PolynomialObservableCoordinate,
    FinitePolynomialEvaluation,
    FinitePolynomialPoint,
    FinitePolynomialTable,
    FinitePolynomialRecheck,
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

/// 一度取消を観測した後は新しい導出を許さない。
#[derive(Clone)]
pub struct Control {
    state: Rc<RefCell<ControlState>>,
}

struct ControlState {
    probe: Box<dyn FnMut(Checkpoint) -> Option<Signal>>,
    stopped: Option<Signal>,
}

impl std::fmt::Debug for Control {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Control")
            .field("stopped", &self.state.borrow().stopped)
            .finish_non_exhaustive()
    }
}

/// 止めない制御。テストの既定の入力として使う。
#[cfg(test)]
pub(crate) fn quiet() -> Control {
    Control::unlimited()
}

impl Default for Control {
    fn default() -> Self {
        Self::unlimited()
    }
}

impl Control {
    /// probe は検査点ごとに呼ばれ、取消のシグナルを観測したらそれを返す。
    pub fn new(probe: impl FnMut(Checkpoint) -> Option<Signal> + 'static) -> Self {
        Self {
            state: Rc::new(RefCell::new(ControlState {
                probe: Box::new(probe),
                stopped: None,
            })),
        }
    }

    /// 取消を観測しない内部計算用の制御。CLIのsignal捕捉はアプリケーション側が所有する。
    pub fn unlimited() -> Self {
        Self::new(|_| None)
    }

    pub fn stop_reason(&self) -> Option<Signal> {
        self.state.borrow().stopped
    }

    pub fn checkpoint(&mut self, point: Checkpoint) -> Result<(), Signal> {
        let mut state = self.state.borrow_mut();
        if let Some(signal) = state.stopped {
            return Err(signal);
        }
        let Some(signal) = (state.probe)(point) else {
            return Ok(());
        };
        state.stopped = Some(signal);
        Err(signal)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::cell::Cell;

    #[test]
    fn unlimited_and_default_never_stop() {
        for mut control in [Control::unlimited(), Control::default()] {
            let mut shared = control.clone();
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
    fn injected_signal_latches_and_is_shared() {
        let probes = Rc::new(Cell::new(0));
        let calls = probes.clone();
        let mut control = Control::new(move |_| {
            calls.set(calls.get() + 1);
            (calls.get() == 3).then_some(Signal::Term)
        });
        let mut shared = control.clone();
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
