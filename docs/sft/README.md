# SFT: Software Field Theory

このディレクトリは、Software Field Theory, SFT を整理する。

SFT は、field-shaped software evolution の計算理論である。
要求、artifact、実践、ツール、AI agent、レビュー、CI/CD、運用 feedback、
lifecycle decision が、コードベースの到達可能なアーキテクチャ未来をどう変えるかを扱う。

```text
AAT makes architecture locally algebraic.
ArchSig makes architecture observable.
SFT makes software evolution computable.
```

日本語では次のように読む。

```text
AAT はアーキテクチャを局所代数にする。
ArchSig はアーキテクチャを観測可能にする。
SFT はソフトウェア進化を計算可能にする。
```

## 読む順序

1. [Software Field Theory](software_field_theory.md)
2. [AAT / SFT Interface](aat_interface.md)
3. [Architecture Signature Dynamics 互換入口](../design/architecture_signature_dynamics.md)
4. [Architecture Dynamics tooling 設計](../design/architecture_dynamics_tooling_design.md)

## SFT の中心対象

```text
DevelopmentField
CodebaseAsFieldMemory
SoftwareField
ArchitectureProjection
ArtifactMediatedChange
ForceDescriptor
OperationSupport
OperationPolicy
SupportedOperation
ObservationBoundary
GovernanceIntervention
ForecastCone
ConsequenceEnvelope
ObservedSignatureRecord
ObstructionWitnessCandidate
ProposalAccounting
ReviewMediation
FieldUpdate
StableRegion
ReachablePreimage
AIProposalGovernance
LifecycleTrajectory
EndOfLifeDecision
```

## SFT の問い

```text
この PRD はどの consequence envelope を作るか。
どの architecture region と signature axis が影響を受けるか。
どの operation family が自然・可能・危険・低コストに見えるか。
どの missing invariant / boundary が forecast boundary に残るか。
どの review / CI / issue decomposition が cone を狭めるか。
AI agent の proposal support は bounded field model 内に収まっているか。
observed PR / review / CI / incident outcome は field model をどう更新するか。
いつ repair し、いつ migration し、いつ contraction / end-of-life を選ぶべきか。
```

## AAT / ArchSig / SFT の分業

```text
AAT:
  architecture の局所代数。

ArchSig:
  実 artifact と codebase を観測可能な signature / witness / boundary report に写す計測層。

SFT:
  artifact / practice / AI / feedback が architecture-signature trajectory の
  reachable future をどう変えるかを扱う計算理論。
```

SFT は AAT の数学的核を置き換えない。
SFT は AAT の architecture object、operation、invariant、obstruction witness、
signature、theorem boundary / non-conclusions を観測量・制約・制御入力として使う。

Lean theorem claim として読める範囲は [AAT](../aat/README.md) 側に置く。
SFT の forecast、consequence envelope、proposal accounting、organization field、AI governance は、
明示された computable core と claim boundary の下で tooling / empirical / governance model として扱う。
