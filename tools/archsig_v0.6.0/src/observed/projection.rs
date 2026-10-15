//! 観測評価の公開射影の静的型付け。動的な constructor・index・owner 条件は評価へ残す。

use super::control::{Checkpoint, Control, StopReason};
use crate::{canonical::Json, definition::PrimitiveSignature, law::CheckedLaw, types::Type};

/// Law の型と、計算結果だけに存在する record 型を区別する。
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProjectionType {
    Law(Type),
    Evaluation(Type),
    Proposition,
    Architecture,
    /// 実値の constructor や異種生成元によって決まる候補型。
    Dynamic(Vec<ProjectionType>),
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum ProjectionStep {
    Field(String),
    Index(u64),
}

impl ProjectionStep {
    pub fn wire(&self) -> Json {
        match self {
            Self::Field(s) => Json::str(s),
            Self::Index(n) => Json::Nat(*n),
        }
    }
}

/// 静的に合法な射影。`conditional` は実値による適合検査を必要とする。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProjectionPlan {
    pub ty: ProjectionType,
    pub conditional: bool,
}

/// 射影の提示違反と、同じ中断制御による停止を区別する。
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProjectionFailure {
    Invalid(String),
    Interrupted(StopReason),
}
impl From<&str> for ProjectionFailure {
    fn from(message: &str) -> Self {
        Self::Invalid(message.into())
    }
}
impl From<StopReason> for ProjectionFailure {
    fn from(reason: StopReason) -> Self {
        Self::Interrupted(reason)
    }
}

/// 閉じた公開表と Law の構造射影だけを解決する。
pub fn resolve_projection(
    law: &CheckedLaw,
    initial: ProjectionType,
    path: &[ProjectionStep],
) -> Result<ProjectionPlan, String> {
    match resolve_projection_controlled(law, initial, path, &mut Control::unlimited()) {
        Ok(plan) => Ok(plan),
        Err(ProjectionFailure::Invalid(message)) => Err(message),
        Err(ProjectionFailure::Interrupted(_)) => unreachable!("上限と取消通知のない制御"),
    }
}

/// 各 path と型候補の走査前後で、要求解決と共有する制御を確認する。
pub fn resolve_projection_controlled(
    law: &CheckedLaw,
    initial: ProjectionType,
    path: &[ProjectionStep],
    control: &mut Control,
) -> Result<ProjectionPlan, ProjectionFailure> {
    tick(control)?;
    let mut plan = ProjectionPlan {
        ty: initial,
        conditional: false,
    };
    let mut at = 0;
    while at < path.len() {
        tick(control)?;
        let (next, used) = project(law, &plan.ty, &path[at..], control)?;
        plan.ty = next.ty;
        plan.conditional |= next.conditional;
        at += used;
        tick(control)?;
    }
    tick(control)?;
    Ok(plan)
}

fn tick(control: &mut Control) -> Result<(), StopReason> {
    control.checkpoint(Checkpoint::Projection)
}

fn project(
    law: &CheckedLaw,
    ty: &ProjectionType,
    path: &[ProjectionStep],
    control: &mut Control,
) -> Result<(ProjectionPlan, usize), ProjectionFailure> {
    tick(control)?;
    let result = project_inner(law, ty, path, control);
    finish_projection(result, control)
}

fn finish_projection<T>(
    result: Result<T, ProjectionFailure>,
    control: &mut Control,
) -> Result<T, ProjectionFailure> {
    match (result, tick(control)) {
        // Keep the completed result and the latched budget together. A Dynamic
        // caller must still stop before any untried candidate, or when a prior
        // candidate succeeded; only exhaustive rejection establishes its error.
        (Err(error @ ProjectionFailure::Invalid(_)), Err(StopReason::BudgetExhausted { .. })) => {
            Err(error)
        }
        (_, Err(reason)) => Err(ProjectionFailure::Interrupted(reason)),
        (result, Ok(())) => result,
    }
}

fn project_inner(
    law: &CheckedLaw,
    ty: &ProjectionType,
    path: &[ProjectionStep],
    control: &mut Control,
) -> Result<(ProjectionPlan, usize), ProjectionFailure> {
    use ProjectionStep::{Field, Index};
    use ProjectionType::{Architecture, Dynamic, Evaluation, Law};
    let exact = |ty| {
        Ok((
            ProjectionPlan {
                ty,
                conditional: false,
            },
            1,
        ))
    };
    let conditional = |ty| {
        Ok((
            ProjectionPlan {
                ty,
                conditional: true,
            },
            1,
        ))
    };
    match (ty, &path[0]) {
        (Evaluation(t), Field(f)) if f == "value" => conditional(Law(t.clone())),
        (Evaluation(_), Field(f)) if f == "environment" => conditional(Architecture),
        (Architecture, Field(f)) if f == "root" => {
            let mut candidates = Vec::new();
            for d in law.definitions.declarations.values() {
                tick(control)?;
                if matches!(&d.signature, PrimitiveSignature::Entity { owner: None, .. }) {
                    candidates.push(Law(Type::Ref(d.name.clone())));
                }
                tick(control)?;
            }
            conditional(Dynamic(candidates))
        }
        (Law(Type::Tuple(ts)), Index(i)) => {
            let t = usize::try_from(*i)
                .ok()
                .and_then(|i| ts.get(i))
                .ok_or("Tuple の index が範囲外")?;
            exact(Law(t.clone()))
        }
        (Law(Type::List(t)), Index(_)) => conditional(Law((**t).clone())),
        (Law(Type::Option(t)), Field(f)) if f == "some" => conditional(Law((**t).clone())),
        (Law(Type::Data(name)), Index(i)) => {
            let Some(d) = law.definitions.declarations.get(name) else {
                return Err("data 宣言がない".into());
            };
            let PrimitiveSignature::Data { constructors } = &d.signature else {
                return Err("data 型でない".into());
            };
            let mut ts = Vec::new();
            for (index, c) in constructors.iter().enumerate() {
                tick(control)?;
                if let Some(t) = usize::try_from(*i).ok().and_then(|i| c.arguments.get(i)) {
                    push_unique(&mut ts, Law(t.clone()), control)?;
                }
                if index + 1 == constructors.len() && ts.is_empty() {
                    return finish_projection(
                        Err("全 constructor で index が範囲外".into()),
                        control,
                    );
                }
                tick(control)?;
            }
            if ts.is_empty() {
                return Err("全 constructor で index が範囲外".into());
            }
            conditional(if ts.len() == 1 {
                ts.remove(0)
            } else {
                Dynamic(ts)
            })
        }
        (Law(Type::Path(a, _)), Field(f)) if f == "source" => exact(Law(Type::Ref(a.clone()))),
        (Law(Type::Path(_, b)), Field(f)) if f == "target" => exact(Law(Type::Ref(b.clone()))),
        (Law(Type::Path(_, _)), Field(f)) if f == "generators" => {
            if !matches!(path.get(1), Some(Index(_))) {
                return Err("generators は index まで指定する".into());
            }
            let mut ts = Vec::new();
            for d in law.definitions.declarations.values() {
                tick(control)?;
                if matches!(
                    &d.signature,
                    PrimitiveSignature::Arrow { .. } | PrimitiveSignature::Correspondence { .. }
                ) {
                    ts.push(Law(Type::Ref(d.name.clone())));
                }
                tick(control)?;
            }
            Ok((
                ProjectionPlan {
                    ty: Dynamic(ts),
                    conditional: true,
                },
                2,
            ))
        }
        (Dynamic(ts), _) => {
            let mut out = Vec::new();
            let mut used = None;
            for (index, t) in ts.iter().enumerate() {
                tick(control)?;
                match project(law, t, path, control) {
                    Ok((p, n)) => {
                        if used.is_some_and(|u| u != n) {
                            return Err("射影の構造が型候補間で異なる".into());
                        }
                        used = Some(n);
                        push_unique(&mut out, p.ty, control)?;
                    }
                    Err(ProjectionFailure::Invalid(_)) => {}
                    Err(stopped @ ProjectionFailure::Interrupted(_)) => return Err(stopped),
                }
                if index + 1 == ts.len() && out.is_empty() {
                    // Every candidate has now rejected this step. Form that
                    // conclusion before the final iteration's post checkpoint,
                    // including a budget latched by the last candidate's post.
                    return finish_projection(Err("公開された射影が型候補にない".into()), control);
                }
                tick(control)?;
            }
            if out.is_empty() {
                return Err("公開された射影が型候補にない".into());
            }
            Ok((
                ProjectionPlan {
                    ty: if out.len() == 1 {
                        out.remove(0)
                    } else {
                        Dynamic(out)
                    },
                    conditional: true,
                },
                used.unwrap(),
            ))
        }
        _ => Err("この型で公開されていない射影".into()),
    }
}

/// 動的な候補が一つでも宣言型へ適合し得る場合だけ、束縛制約として残せる。
pub fn can_bind(actual: &ProjectionType, expected: &Type) -> bool {
    can_bind_controlled(actual, expected, &mut Control::unlimited())
        .expect("上限と取消通知のない制御")
}

/// 候補と型構造に共有制御を通し、全候補の不適合を確定した場合だけ予算と false を保持する。
pub fn can_bind_controlled(
    actual: &ProjectionType,
    expected: &Type,
    control: &mut Control,
) -> Result<bool, StopReason> {
    tick(control)?;
    let mut candidates = vec![actual];
    while let Some(actual) = candidates.pop() {
        tick(control)?;
        let compatible = match actual {
            ProjectionType::Law(t) => law_types_match(t, expected, true, control)?,
            ProjectionType::Dynamic(ts) => {
                for t in ts {
                    tick(control)?;
                    candidates.push(t);
                    tick(control)?;
                }
                false
            }
            _ => false,
        };
        if compatible {
            tick(control)?;
            return Ok(true);
        }
        if candidates.is_empty() {
            return finish_type_match(false, control);
        }
        // 未検査の候補が残る間は、一候補の不適合で全体を決めず停止を伝播する。
        tick(control)?;
    }
    finish_type_match(false, control)
}

/// 確定した不一致は予算とともに保つ。適合後の予算と取消は停止として返す。
/// 呼出し側で、一候補の不一致と全候補の不適合を区別する。
fn finish_type_match(same: bool, control: &mut Control) -> Result<bool, StopReason> {
    match tick(control) {
        Err(StopReason::BudgetExhausted { .. }) if !same => Ok(false),
        Err(reason) => Err(reason),
        Ok(()) => Ok(same),
    }
}

/// Owned の所属条件を別制約に残し、型の全構造を一段ずつ比較する。
fn law_types_match(
    left: &Type,
    right: &Type,
    erase_owner: bool,
    control: &mut Control,
) -> Result<bool, StopReason> {
    let mut pending = vec![(left, right)];
    while let Some((left, right)) = pending.pop() {
        tick(control)?;
        let same = match (left, right) {
            (Type::Unit, Type::Unit)
            | (Type::Bool, Type::Bool)
            | (Type::Z, Type::Z)
            | (Type::Q, Type::Q)
            | (Type::Text, Type::Text) => true,
            (Type::Ref(a), Type::Ref(b))
            | (Type::Fp(a), Type::Fp(b))
            | (Type::Data(a), Type::Data(b)) => a == b,
            (Type::Owned(a, p), Type::Owned(b, q)) => a == b && (erase_owner || p == q),
            (Type::Ref(a), Type::Owned(b, _)) | (Type::Owned(a, _), Type::Ref(b)) => {
                erase_owner && a == b
            }
            (Type::Path(a, b), Type::Path(c, d)) => a == c && b == d,
            (Type::Tuple(a), Type::Tuple(b)) => {
                if a.len() != b.len() {
                    false
                } else {
                    for (a, b) in a.iter().zip(b) {
                        tick(control)?;
                        pending.push((a, b));
                        tick(control)?;
                    }
                    true
                }
            }
            (Type::List(a), Type::List(b))
            | (Type::Set(a), Type::Set(b))
            | (Type::Option(a), Type::Option(b)) => {
                pending.push((a, b));
                true
            }
            (Type::Map(a, b), Type::Map(c, d)) => {
                pending.push((a, c));
                pending.push((b, d));
                true
            }
            (Type::Term(a, r), Type::Term(b, s)) => {
                if a.len() != b.len() {
                    false
                } else {
                    for (a, b) in a.iter().zip(b) {
                        tick(control)?;
                        pending.push((a, b));
                        tick(control)?;
                    }
                    pending.push((r, s));
                    true
                }
            }
            _ => false,
        };
        if !same {
            return finish_type_match(false, control);
        }
        tick(control)?;
    }
    finish_type_match(true, control)
}

/// 型候補の重複除去にも制御を通し、従来の候補順と一意化を保つ。
fn push_unique(
    candidates: &mut Vec<ProjectionType>,
    candidate: ProjectionType,
    control: &mut Control,
) -> Result<(), StopReason> {
    tick(control)?;
    for existing in candidates.iter() {
        tick(control)?;
        let same = projection_types_match(existing, &candidate, control)?;
        tick(control)?;
        if same {
            return Ok(());
        }
    }
    candidates.push(candidate);
    tick(control)?;
    Ok(())
}

fn projection_types_match(
    left: &ProjectionType,
    right: &ProjectionType,
    control: &mut Control,
) -> Result<bool, StopReason> {
    let mut pending = vec![(left, right)];
    while let Some((left, right)) = pending.pop() {
        tick(control)?;
        let same = match (left, right) {
            (ProjectionType::Law(a), ProjectionType::Law(b))
            | (ProjectionType::Evaluation(a), ProjectionType::Evaluation(b)) => {
                law_types_match(a, b, false, control)?
            }
            (ProjectionType::Architecture, ProjectionType::Architecture)
            | (ProjectionType::Proposition, ProjectionType::Proposition) => true,
            (ProjectionType::Dynamic(a), ProjectionType::Dynamic(b)) => {
                if a.len() != b.len() {
                    false
                } else {
                    for (a, b) in a.iter().zip(b) {
                        tick(control)?;
                        pending.push((a, b));
                        tick(control)?;
                    }
                    true
                }
            }
            _ => false,
        };
        tick(control)?;
        if !same {
            return Ok(false);
        }
    }
    tick(control)?;
    Ok(true)
}
