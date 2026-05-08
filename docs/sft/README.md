# SFT: ソフトウェアの場の理論

このディレクトリは、Software Field Theory, SFT を整理する。

SFT は、AAT の上で、要求、仕様、Issue、PR、レビュー、CI、組織、AI、運用、
終焉がソフトウェア場に及ぼす力と軌道を扱う力学・制御理論である。

```text
AAT provides the algebra.
SFT studies the field.
ArchSig observes the signature.
AI agents act under control.
```

日本語では次のように読む。

```text
AAT は代数を与える。
SFT は場を扱う。
ArchSig は署名を観測する。
AI はその場の上で操作する。
```

## 読む順序

1. [ソフトウェアの場の理論](software_field_theory.md)
2. [Architecture Signature Dynamics 互換入口](../design/architecture_signature_dynamics.md)
3. [Architecture Dynamics tooling 設計](../design/architecture_dynamics_tooling_design.md)
4. [Attractor Engineering](../design/attractor_engineering.md)

## SFT の中心対象

```text
SoftwareField
PRDForce
SpecForceShaping
IssueOperationSupport
PRSignatureDelta
ReviewConstraint
CIFilter
RuntimeFeedback
IncidentPressure
PostmortemLawUpdate
OrganizationField
AIAgentOperationPressure
ForecastCone
Dissipation
AttractorEngineering
LifecycleTrajectory
EndOfLifeOperation
```

## SFT の問い

```text
この PRD はコードベースの場にどのくらいの力をかけるか。
その力はどの subsystem に流れるか。
forecast cone はどれくらい広いか。
どの bad basin に落ちやすいか。
どの spec clause が forecast cone を狭めるか。
Issue は lawful operation 単位に分割されているか。
PR は予測された signature delta と一致したか。
組織構造はどの operation distribution を誘導しているか。
AI agent は安全な operation support 内で動いているか。
いつ repair し、いつ migration し、いつ終焉させるべきか。
```

## AAT との境界

```text
AAT = local / algebraic / formal / certifiable
SFT = global / dynamical / predictive / controllable
```

SFT は AAT の数学的核を置き換えない。SFT は AAT の signature、witness、
certificate、proof obligation boundary を観測量・制約・制御入力として使う。

Lean theorem claim として読める範囲は [AAT](../aat/README.md) 側に置く。
SFT の forecast、force、dissipation、organization field、AI dynamics は、
明示された bounded formal kernel を除いて tooling / empirical / control model として扱う。
