# AAT / SFT Interface

この文書は、SFT が AAT から何を借り、どう読み替えるかを定義する。
AAT 側の数学理論は [AAT 数学理論](../aat/mathematical_theory.md) に閉じており、
SFT はその理論に逆依存を作らない。

```text
AAT  ->  SFT

AAT provides local algebra.
SFT uses that algebra to make software evolution computable.
```

## 1. 依存方向

AAT は、ソフトウェアアーキテクチャの局所代数として独立に成立する。
SFT は、その局所代数を architecture projection、observable coordinate、
local transition law の前提として使う。

```text
AAT does not depend on SFT.
SFT depends on AAT.
```

したがって、AAT の概念を SFT のために定義し直さない。
SFT は AAT の概念を、field-shaped software evolution の計算理論における
architecture projection、observable coordinate、local law premise として片方向に写す。

## 2. SFT が AAT から借りるもの

| SFT 側の役割 | AAT から借りるもの |
| --- | --- |
| architecture projection | `ArchitectureObject` |
| local transition | `ArchitectureOperation` |
| conserved / protected quantity | `InvariantFamily` |
| local defect / repair target | `ObstructionWitness` |
| partial observation coordinate | `ArchitectureSignature` |
| admissibility boundary | theorem boundary / non-conclusions |
| local path skeleton | `ArchitecturePath` |
| operation support | bounded operation family |
| safe region predicate | selected invariant / flatness predicate |

この対応は、AAT theorem を経験的予測へ変換するものではない。
AAT は selected universe と selected assumptions の下での局所主張を与え、
SFT はそれを field model の admissibility predicate、観測量、制約、制御入力として使う。
`SoftwareField` 自体は `ArchitectureObject` ではなく、AAT 側の object は field からの
architecture projection として現れる。

```text
arch : SoftwareField -> ArchitectureObject
```

## 3. SFT 側で導入するもの

SFT は、自分の理論側で次の概念を導入する。

```text
force
field state
arch projection
trajectory
operation distribution
ForecastCone
ConsequenceEnvelope
forecast boundary
proposal accounting
field update
stable region / reachable preimage
feedback governance
organization field
AI operation pressure
lifecycle / end-of-life dynamics
```

これらは AAT の概念ではない。
AAT の `ArchitectureSignature` から `ForecastCone` は従わず、
AAT の `ArchitectureOperation` が lawful であることから trajectory-level safety は従わず、
AAT の selected obstruction absence から empirical cost reduction は従わない。

## 4. 変換規約

SFT は AAT の語彙を次の規約で読む。

```text
ArchitectureObject
  -> field state の architecture projection

ArchitectureOperation
  -> accepted / proposed transition の local law premise

InvariantFamily
  -> field が保存しようとする constraint family

ObstructionWitness
  -> selected unsafe / costly / blocked trajectory coordinate,
     repair target, or forecast boundary axis

ArchitectureSignature
  -> trajectory を観測する partial coordinate system

theorem boundary / non-conclusions
  -> forecast と governance が越えてはいけない claim boundary
```

この変換は片方向である。
SFT 側の artifact-mediated change、trajectory、forecast、proposal accounting は、
AAT 側の theorem を強めない。

AAT claim が SFT 側へ移るときの許される読みは、次の境界に従う。

| AAT 側 | SFT 側で許される読み | 禁止される読み |
| --- | --- | --- |
| selected witness absence | selected local defect が観測されていない。 | future trajectory が安全である。 |
| signature axis zero | selected measured coordinate が 0 である。 | 未測定 axis も安全である。 |
| operation preserves invariant | one accepted transition が局所的に admissible である。 | policy 全体が globally safe である。 |
| theorem boundary | forecast boundary の条件として使える。 | empirical prediction theorem である。 |
| non-conclusions | forecast non-conclusions として残す。 | tool failure と同一視する。 |
| observed signature delta | trajectory observation として使える。 | causal artifact action を一意に同定する。 |
| obstruction witness | repair target / forecast boundary axis として使える。 | 物理的 resistance と同一視する。 |

claim level を移す場合も、主張の水準を保つ。
AAT theorem は SFT theorem そのものではなく、SFT reachability / safety theorem schema の
local transition law または admissibility premise として使う。

| AAT claim level | SFT 側の読み |
| --- | --- |
| AAT theorem level | SFT theorem schema の local premise |
| AAT tooling claim | SFT field estimate |
| AAT empirical hypothesis | SFT calibrated forecast |
| AAT non-conclusions | SFT forecast boundary item |

### AAT-supported Grand Theorem package

Lean 側では、AAT boundary 上で SFT Grand Theorem を読むための package を
`Formal/Arch/Evolution/SFTAATFundamentalModularity.lean` に分離している。小さな
canonical finite example は
`Formal/Arch/Evolution/SFTAATFundamentalModularityExamples.lean` に置く。

`SFTAATFundamentalModularity.AATSupportedSFTBoundary` は、AAT の selected
architecture slice、`AATTheoremStatus`、`SFTForecastStatus`、
`AATToSFTInterfaceBoundary`、`FiniteExactSFTModel`、selected source、selected
horizon を同じ record に保持する。ここで AAT theorem status は SFT local premise として
読むだけであり、projection / observation / reconstruction / missing-evidence /
theorem / ArchSig report boundary は残る。
`AATSupportedSFTBoundary.ofSelectedSliceAndFiniteExactModel` は、この record を
selected slice / interface boundary / finite exact model boundary records から構成する
constructor helper であり、selected source / horizon、projection / observation /
reconstruction / missing-evidence boundary、ArchSig report boundary と theorem-status
boundary、non-conclusions preservation を accessor theorem として取り出せる。

`SFTAATFundamentalModularity.AATSupportedFundamentalModularityPackage` は、この
boundary と既存の `SFTFundamentalModularity.FiniteSelectedFundamentalModularityTheorem`
を接続する。したがって得られる結論は selected finite package 上の
governed-or-typed-boundary-failure と modularity-as-ForecastCone-descent accessor である。
assumption-free Grand Theorem、all software systems / all covers / all runtime schedules、
empirical calibration correctness、operational governance effectiveness、global AI safety、
extractor completeness は結論しない。

review / calibration / agentic component は、それぞれ final component へ読むための
discharge helper accessor を持つ。canonical finite example は singleton finite exact
model 上で `AATSupportedFundamentalModularityPackage` を end-to-end に instantiate し、
final typed conclusion と non-conclusions preservation を取り出す。

canonical example の descent / obstruction / governance component は、それぞれ finite
selected descent package、finite descent obstruction package、finite
obstruction-governance package から既存 helper 経由で構成される。この例は、主要な final
component を theorem-package surface から組み立てる読みを示す。ただし、singleton
selected example であり、任意の software system、all covers、all runtime schedules、
extractor completeness、classifier completeness の無条件化、operational governance
effectiveness へ一般化しない。

`AATSFTBoundaryFailureKind` は typed conversion 後も
`AATTypedComputationBoundaryFailure` に保持される。final typed conclusion は governed /
existing finite typed failure / AAT-SFT boundary failure の三分岐として読めるため、
expression / projection / observation / reconstruction / missing-evidence / theorem-status /
ArchSig report のどの AAT/SFT 境界が破れたかを AAT/SFT branch まで保持できる。

## 5. 非混同

次の同一視は禁止する。

| A | B |
| --- | --- |
| AAT lawfulness | future trajectory safety |
| AAT measured zero | unmeasured axis safety |
| AAT static split | runtime / semantic flatness |
| AAT signature coordinate | empirical prediction by itself |
| AAT operation preservation | SFT policy safety |
| AAT witness absence | absence of latent action |
| SFT `ForecastCone` narrowing | global risk reduction |
| observed signature delta | identified causal artifact action |
| ArchSig extraction | ground truth architecture object |
| AI agent policy compliance | architecture lawfulness |
| SFT forecast | Lean theorem |

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

ArchSig は次の中間層を持つ。

```text
real artifact
  -> extracted candidate ArchitectureCore
  -> selected ArchitectureObject presentation
  -> AAT observable
  -> SFT field estimate
```

AAT 側では、ArchSig は component universe、signature axes、obstruction witnesses、
theorem boundary status、non-conclusions を抽出する。
SFT 側では、ArchSig は artifact action / force descriptor、ForecastCone、
ConsequenceEnvelope、comparable signature axes、expected axis delta range、
trajectory、feedback update を推定する。
signature delta は、両側で測定済みで、axis ごとの比較順序が定義されている場合に限って
比較される。

`ForecastCone` formal core との接続は、次の境界で読む。

```text
SFT formal core:
  SoftwareField
  + OperationSupport
  + bounded Horizon
  + StepRelation
  + ReachableFieldPath
  + ForecastCone

ArchSig-SFT tooling:
  finite support refs
  + bounded horizon config
  + path class candidates
  + forecast boundary
  + unknown remainder
```

tooling skeleton は formal core の入力候補や review surface を有限に記録するが、
`ReachableFieldPath` の完全性、`StepRelation` の妥当性、cone projection theorem、
または calibrated forecast correctness を証明しない。

同じ tool family であっても、claim level は分ける。

```text
ArchSig-AAT Extractor
  -> signature / witness / theorem-boundary report

ArchSig-SFT Forecaster
  -> force descriptor / operation-support / forecast-boundary estimate
  -> ConsequenceEnvelope report
  -> comparable signature axis report

ArchSig-Governance Reporter
  -> missing invariant / review rule / issue decomposition recommendation
```

この bridge は片方向の観測・推定層である。
ArchSig output があることから、AAT theorem が強まるわけではなく、
SFT forecast が Lean theorem になるわけでもない。
