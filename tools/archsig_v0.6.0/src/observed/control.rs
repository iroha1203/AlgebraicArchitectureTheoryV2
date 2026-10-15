//! 検査・要求解決・評価で共有する、注入可能な協調中断制御。

use crate::{canonical::Json, result::Signal};
use std::collections::BTreeMap;
use std::time::Instant;
use std::{cell::RefCell, rc::Rc};

/// 原始演算または有限反復の境界。試験用 probe も同じ境界を受け取る。
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Checkpoint {
    BeforeDefinitions,
    DefinitionIteration,
    DefinitionSemantics,
    DefinitionData,
    DefinitionDependency,
    AfterDefinitions,
    BeforeLaw,
    LawIteration,
    LawSemantics,
    LawCycle,
    AfterLaw,
    BeforeArchMap,
    ArchMapIteration,
    ArchMapTerm,
    AfterArchMap,
    Resolve,
    Expression,
    FiniteIteration,
}

/// finalize を含まない内部計算の soft limit。
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Limits {
    pub time_ms: Option<u128>,
    pub memory_mib: Option<u128>,
}

impl Limits {
    pub fn wire(self) -> Json {
        let mut fields = BTreeMap::new();
        if let Some(n) = self.time_ms {
            fields.insert("time_ms".into(), Json::str(n.to_string()));
        }
        if let Some(n) = self.memory_mib {
            fields.insert("memory_mib".into(), Json::str(n.to_string()));
        }
        Json::Obj(fields)
    }
}

/// 外部から注入した単調時計・peak RSS・取消通知の観測。
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Usage {
    pub elapsed_ms: u128,
    pub memory_mib: u128,
    pub signal: Option<Signal>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Resource {
    TimeMs,
    MemoryMib,
}

impl Resource {
    pub fn wire(self) -> &'static str {
        match self {
            Self::TimeMs => "time_ms",
            Self::MemoryMib => "memory_mib",
        }
    }
}

/// 停止時点の実測値を保ち、未着手の問いにも同じ原因を渡す。
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StopReason {
    BudgetExhausted {
        resource: Resource,
        limit: u128,
        observed: u128,
    },
    Cancelled(Signal),
}

impl StopReason {
    pub fn code(&self) -> &'static str {
        match self {
            Self::BudgetExhausted { .. } => "budget_exhausted",
            Self::Cancelled(_) => "cancelled",
        }
    }

    /// 結果仕様 §6 の Issue。要求固有の request/dependencies は呼出し側が付ける。
    pub fn wire(&self) -> Json {
        let (message, details) = match self {
            Self::BudgetExhausted {
                resource,
                limit,
                observed,
            } => (
                "計算予算を使い切った",
                Json::obj([
                    ("resource", Json::str(resource.wire())),
                    ("limit", Json::str(limit.to_string())),
                    ("observed", Json::str(observed.to_string())),
                ]),
            ),
            Self::Cancelled(signal) => (
                "シグナルを受けて中断した",
                Json::obj([("signal", Json::str(signal.wire()))]),
            ),
        };
        Json::obj([
            ("code", Json::str(self.code())),
            ("message", Json::str(message)),
            ("details", details),
            ("dependencies", Json::Arr(vec![])),
            ("missing", Json::Arr(vec![])),
        ])
    }
}

/// 既存の入力エラーと協調中断を混同せずに伝播する。
#[derive(Debug)]
pub enum CheckFailure<F> {
    Input(F),
    Stopped(StopReason),
}

/// 一度消尽・取消を観測した後は新しい導出を許さない。
#[derive(Clone)]
pub struct Control {
    state: Rc<RefCell<ControlState>>,
}

struct ControlState {
    limits: Limits,
    probe: Box<dyn FnMut(Checkpoint) -> Usage>,
    usage: Usage,
    stopped: Option<StopReason>,
}

impl std::fmt::Debug for Control {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let state = self.state.borrow();
        f.debug_struct("Control")
            .field("limits", &state.limits)
            .field("usage", &state.usage)
            .field("stopped", &state.stopped)
            .finish_non_exhaustive()
    }
}

impl Default for Control {
    fn default() -> Self {
        Self::unlimited()
    }
}

impl Control {
    pub fn new(limits: Limits, probe: impl FnMut(Checkpoint) -> Usage + 'static) -> Self {
        Self {
            state: Rc::new(RefCell::new(ControlState {
                limits,
                probe: Box::new(probe),
                usage: Usage::default(),
                stopped: None,
            })),
        }
    }

    /// OS の取消捕捉は呼出し側に委ねる。通常の内部呼出しは時間と peak RSS を測る。
    pub fn unlimited() -> Self {
        let started = Instant::now();
        Self::new(Limits::default(), move |_| Usage {
            elapsed_ms: started.elapsed().as_millis(),
            memory_mib: u128::from(crate::run::peak_rss_bytes()) / (1024 * 1024),
            signal: None,
        })
    }

    pub fn limits(&self) -> Limits {
        self.state.borrow().limits
    }
    pub fn usage(&self) -> Usage {
        self.state.borrow().usage
    }
    pub fn stop_reason(&self) -> Option<StopReason> {
        self.state.borrow().stopped.clone()
    }

    pub fn checkpoint(&mut self, point: Checkpoint) -> Result<(), StopReason> {
        let mut state = self.state.borrow_mut();
        if let Some(reason) = &state.stopped {
            return Err(reason.clone());
        }
        let sample = (state.probe)(point);
        state.usage.elapsed_ms = state.usage.elapsed_ms.max(sample.elapsed_ms);
        state.usage.memory_mib = state.usage.memory_mib.max(sample.memory_mib);
        state.usage.signal = state.usage.signal.or(sample.signal);
        let reason = if let Some(signal) = state.usage.signal {
            Some(StopReason::Cancelled(signal))
        } else if let Some(limit) = state
            .limits
            .time_ms
            .filter(|n| state.usage.elapsed_ms >= *n)
        {
            Some(StopReason::BudgetExhausted {
                resource: Resource::TimeMs,
                limit,
                observed: state.usage.elapsed_ms,
            })
        } else {
            state
                .limits
                .memory_mib
                .filter(|n| state.usage.memory_mib >= *n)
                .map(|limit| StopReason::BudgetExhausted {
                    resource: Resource::MemoryMib,
                    limit,
                    observed: state.usage.memory_mib,
                })
        };
        if let Some(reason) = reason {
            state.stopped = Some(reason.clone());
            Err(reason)
        } else {
            Ok(())
        }
    }
}
