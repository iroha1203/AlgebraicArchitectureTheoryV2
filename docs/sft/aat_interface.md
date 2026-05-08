# AAT / SFT Interface

この文書は、SFT が AAT から何を借りるかを定義する。
AAT 側の数学理論は [AAT 数学理論](../aat/mathematical_theory.md) に閉じており、
SFT はその理論に逆依存を作らない。

```text
AAT  ->  SFT

AAT provides local algebra.
SFT uses that algebra to study field dynamics.
```

## 1. 依存方向

AAT は、ソフトウェアアーキテクチャの局所代数として独立に成立する。
SFT は、その局所代数を state space、observable coordinate、local law として使う。

```text
AAT does not depend on SFT.
SFT depends on AAT.
```

したがって、AAT の概念を SFT のために定義し直さない。
SFT は AAT の概念を、予測、制御、feedback、organization field、AI operation field の
モデルへ写す。

## 2. SFT が AAT から借りるもの

| SFT 側の役割 | AAT から借りるもの |
| --- | --- |
| field state | `ArchitectureObject` |
| local transition | `ArchitectureOperation` |
| conserved / protected quantity | `InvariantFamily` |
| local defect / resistance | `ObstructionWitness` |
| observable coordinate | `ArchitectureSignature` |
| admissibility boundary | theorem boundary / non-conclusions |
| local path skeleton | `ArchitecturePath` |
| operation support | bounded operation family |
| safe region predicate | selected invariant / flatness predicate |

この対応は、SFT が AAT の theorem を経験的予測へ変換するという意味ではない。
AAT は selected universe と selected assumptions の下での局所主張を与える。
SFT は、その局所主張を field model の観測量、制約、制御入力として使う。

## 3. SFT 側で導入するもの

SFT は、自分の理論側で次の概念を導入する。

```text
force
field state
trajectory
operation distribution
forecast cone
forecast boundary
dissipation
field update
attractor / basin
feedback control
organization field
AI operation pressure
lifecycle / end-of-life dynamics
```

これらは AAT の概念ではない。
AAT の `ArchitectureSignature` があることから forecast cone は従わない。
AAT の `ArchitectureOperation` が lawful であることから trajectory-level safety は従わない。
AAT の selected obstruction absence から empirical cost reduction は従わない。

## 4. 変換規約

SFT は AAT の語彙を次の規約で読む。

```text
ArchitectureObject
  -> field state の局所断面

ArchitectureOperation
  -> accepted / proposed transition の局所型

InvariantFamily
  -> field が保存しようとする constraint family

ObstructionWitness
  -> force が流れにくい箇所、または dissipation / repair の対象

ArchitectureSignature
  -> trajectory を観測する座標系

theorem boundary / non-conclusions
  -> forecast と control が越えてはいけない claim boundary
```

この変換は片方向である。
SFT 側で観測された force、trajectory、forecast、dissipation から、
AAT 側の theorem が自動的に強まるわけではない。

AAT claim が SFT 側へ移るときの許される読みは、次の境界に従う。

| AAT 側 | SFT 側で許される読み | 禁止される読み |
| --- | --- | --- |
| selected witness absence | selected local defect が観測されていない。 | future trajectory が安全である。 |
| signature axis zero | selected measured coordinate が 0 である。 | 未測定 axis も安全である。 |
| operation preserves invariant | one accepted transition が局所的に admissible である。 | policy 全体が globally safe である。 |
| theorem boundary | forecast boundary の条件として使える。 | empirical prediction theorem である。 |
| non-conclusion | forecast non-conclusion として残す。 | tool failure と同一視する。 |
| observed signature delta | trajectory observation として使える。 | causal force を一意に同定する。 |

## 5. 非混同

次を混同しない。

```text
AAT lawfulness
  != future trajectory safety

AAT measured zero
  != unmeasured axis safety

AAT static split
  != runtime / semantic flatness

AAT signature coordinate
  != empirical prediction by itself

AAT operation preservation
  != SFT policy safety

AAT witness absence
  != absence of latent force

SFT forecast cone narrowing
  != global risk reduction

Observed signature delta
  != identified causal force

ArchSig extraction
  != ground truth architecture object

AI agent policy compliance
  != architecture lawfulness

SFT forecast
  != Lean theorem
```

SFT は AAT の上に立つが、AAT を SFT の一部にしない。
AAT は独立した数学理論であり、SFT はその理論を使う後続理論である。

## 6. ArchSig bridge

ArchSig は AAT でも SFT でもない。
実 artifact を AAT の観測量と SFT の field estimate へ写す tooling layer である。

```text
real artifacts
  -> ArchSig
  -> AAT observables
  -> SFT field model
```

より細かく見ると、ArchSig は次の中間層を持つ。

```text
real artifact
  -> extracted candidate ArchitectureCore
  -> selected ArchitectureObject presentation
  -> AAT observable
  -> SFT field estimate
```

AAT 側では、ArchSig は component universe、signature axes、obstruction witnesses、
theorem boundary status、non-conclusions を抽出する。
SFT 側では、ArchSig は force、forecast cone、expected signature delta、
trajectory、feedback update を推定する。

同じ tool family であっても、claim level は分ける。

```text
ArchSig-AAT Extractor
  -> signature / witness / theorem-boundary report

ArchSig-SFT Forecaster
  -> force / operation-support / forecast-boundary estimate

ArchSig-Control Reporter
  -> missing invariant / review rule / issue decomposition recommendation
```

この bridge は片方向の観測・推定層である。
ArchSig output があることから、AAT theorem が強まるわけではなく、
SFT forecast が Lean theorem になるわけでもない。
