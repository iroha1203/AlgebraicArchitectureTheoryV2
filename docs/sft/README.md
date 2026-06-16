# SFT: Software Field Theory

このディレクトリは、Software Field Theory, SFT を整理する。

SFT は、field-shaped software evolution の計算理論である。
要求、artifact、実践、ツール、AI agent、レビュー、CI/CD、運用 feedback、
lifecycle decision が、コードベースの到達可能なアーキテクチャ未来をどう変えるかを扱う。

```text
AAT builds algebraic-geometric architecture from atoms.
ArchSig measures selected architecture evidence.
SFT makes software evolution computable.
```

日本語では次のように読む。

```text
AAT は Atom から代数幾何的 architecture を構成する。
ArchSig は選ばれた architecture evidence を測定する。
SFT はソフトウェア進化を計算可能にする。
```

## 読む順序

1. [Software Field Theory](software_field_theory.md)
2. [AAT / SFT Interface](aat_interface.md)
3. [SFT 編集ガイドライン](guideline.md)

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
この PRD はどの ConsequenceEnvelope を作るか。
どの architecture region と selected measurement coordinate が影響を受けるか。
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
  Atom / Atom axiom system から architecture object を構成し、
  AAT site、sheaf、law algebra、lawful locus へ持ち上げる代数幾何。

ArchSig:
  ArchMap + LawPolicy + evidence contract から選ばれた architecture evidence を測定し、
  bounded diagnostic artifact に写す tooling 層。

SFT:
  artifact / practice / AI / feedback が architecture-signature trajectory の
  reachable future をどう変えるかを扱う計算理論。
```

ウィトゲンシュタイン的責務境界では、ArchSig は与えられた
`ArchMap + LawPolicy + evidence contract` から語れることだけを語り、
語れないことには沈黙する。ArchMap の観測・Atom mapping・evidence の正しさは
ArchMap author の責務であり、law / axis / witness / coverage の選択は
LawPolicy author の責務である。SFT は ArchSig output を、その入力 contract に相対化された
bounded observation として読み、raw ArchMap や ArchSig conclusion を forecast truth として読まない。

SFT は AAT の数学的核を置き換えない。
SFT は AAT の architecture object、operation、invariant、obstruction witness、
signature、theorem boundary / non-conclusions を観測量・制約・制御入力として使う。

Lean theorem claim として読める範囲は [AAT](../aat/README.md) 側に置く。
SFT の forecast、ConsequenceEnvelope、proposal accounting、organization field、AI governance は、
明示された computable core と claim boundary の下で tooling / empirical / governance model として扱う。
