# ソフトウェアの場の理論

SFT は、AAT の上で、ソフトウェア進化を場の力学として扱う理論である。
AAT が局所的な変更代数を与え、SFT はその変更が要求、仕様、Issue、PR、組織、AI、
運用の力でどのように生まれ、流れ、散逸し、制御されるかを扱う。

```text
SFT studies software evolution as:

software field
  + artifact-induced forces
  + operation distributions
  + signature trajectories
  + dissipation
  + feedback control
```

## 1. AAT との関係

SFT は AAT の上に載る。

| SFT | AAT 的な支え |
| --- | --- |
| `SoftwareField` | `ArchitectureObject` + `ArchitectureSignature` + history + operation support |
| `PRDForce` | `FeatureExtension` candidate + expected signature delta |
| `SpecForceShaping` | `LawUniverse` + invariant family + observation model |
| `IssueOperationSupport` | bounded `ArchitectureOperation` set |
| `PRSignatureDelta` | actual `ArchitectureOperation` + signature difference |
| `ReviewConstraint` | proof obligation checker + repair / projection |
| `CIFilter` | bounded witness detector + theorem precondition checker |
| `ForecastCone` | possible `ArchitecturePath` distribution |
| `Dissipation` | feature force が obstruction / ambiguity / coupling へ流れる現象 |
| `AttractorEngineering` | operation support shaping + safe region preservation |
| `IncidentPressure` | runtime obstruction manifestation |
| `PostmortemLawUpdate` | witness reclassification + law universe update |
| `EndOfLifeOperation` | contraction / migration / deletion operation |

Lean core に置けるのは、有限または bounded な state、operation support、accepted transition、
signature observation、明示された preservation assumption である。
確率、組織、AI、予報、運用効果は、原則として tooling / empirical layer に置く。

## 2. Software Field

`SoftwareField` は、現在の architecture state だけでなく、未来の operation distribution を
誘導する文脈を含む。

```text
SoftwareField :=
  architecture state
  + architecture signature
  + history
  + operation support
  + requirement context
  + review / CI constraints
  + organization policy
  + AI agent policy
  + runtime feedback
```

コードベースは真空中の構造ではない。名前、型、境界、canonical example、テスト粒度、
既存の shortcut、レビュー規則、CI、要件文脈が、次の変更でどの operation が選ばれやすいかを
変える。

```text
current field
  -> operation distribution
  -> accepted / rejected transitions
  -> signature trajectory
  -> updated field
```

## 3. Artifact-induced Force

要求、仕様、Issue、PR、レビュー、CI、incident は、field に force をかける artifact として読む。

```text
PRD / Spec
  -> candidate feature force
  -> expected operation support
  -> expected signature delta
  -> forecast cone
```

force は一つではない。

```text
feature force
repair force
coupling force
boundary force
invariant force
effect force
debt force
refactor force
```

良い変更は feature force と stabilizing force を同時に持つ。
悪い変更は feature force と小さな debt force を同時に持ち、その小さな力が反復で蓄積する。

## 4. Force Taxonomy

SFT では force を観測可能性に応じて分ける。

| force class | 定義方向 | 主な evidence |
| --- | --- | --- |
| `ObservedForce` | 実際に accepted された transition の before / after signature delta。 | PR before / after Signature、drift ledger、Feature Extension Report。 |
| `LatentForce` | 要求、設計、prompt、組織判断、既存 local grammar が operation distribution に与える見えない作用。 | requirement metadata、design boundary、prompt / agent policy、PR proposal distribution、case study。 |
| `DissipatedForce` | review / CI / type / policy によって拒否、修正、減衰された raw force。 | rejected PR、CI failure、review-requested changes、policy decision report。 |

AAT theorem は主に observed transition と accepted-step predicate を扱う。
latent force と dissipated force は tooling / empirical dataset で推定する。

## 5. Forecast Cone

`ForecastCone` は、現在の field と artifact force から到達しうる architecture path の集合または
分布である。

```text
ForecastCone(field, force)
  = possible ArchitecturePath distribution
  + expected signature delta
  + obstruction risk distribution
  + non-conclusion boundary
```

forecast は theorem ではない。AAT の theorem precondition、signature axes、
witness families、historical dataset、review / CI policy を使った bounded prediction である。

Spec は forecast cone を狭める force-shaping artifact として読む。
よい spec clause は、operation support を狭め、lawful path を明確にし、
hidden interaction や ambiguity へ流れる力を減らす。

## 6. Issue と PR

Issue は、field にかかる feature force を bounded operation support へ分解する単位である。

```text
IssueOperationSupport :=
  allowed operation family
  + target invariant
  + expected witness impact
  + theorem preconditions
  + non-conclusions
```

PR は、予測された force が実際にどの transition になったかを観測する点である。

```text
PRSignatureDelta :=
  actual architecture operation
  + before signature
  + after signature
  + expected / actual delta comparison
  + unexpected obstruction witnesses
```

PR が局所的に通ることから、trajectory 全体が安全であることは従わない。
SFT は single-step correctness と trajectory-level safety を分ける。

## 7. Dissipation と Control

review、CI、type checker、architecture rules、theorem precondition checker は、raw force を
拒否、射影、減衰、修正する control / dissipation field である。

```text
raw operation distribution
  -> review / CI / type / policy
  -> accepted operation distribution
```

damping が十分なら bad-axis measure は非増加または減少する、という形の主張は
明示前提を必要とする。operation が accepted されたという事実だけから bad-axis nonincrease は
従わない。

## 8. Attractor Engineering

attractor は、反復操作により trajectory が滞留しやすい signature 領域である。
basin は、その attractor へ落ちやすい初期 configuration の集合である。

```text
Attractor :=
  recurrent signature region
  + stability condition
  + observation boundary

Basin :=
  initial configurations that reach the attractor region
```

Attractor Engineering は、悪い operation を外から止めるだけではなく、良い operation が
自然に選ばれやすい field を作る制御である。

```text
support shaping :=
  remove bad operation
  + add good operation
  + make lawful path easier
  + make unlawful shortcut harder
```

refactoring は、その時点の構造整理だけでなく、未来の operation distribution を変える
field transformation として読む。

## 9. Organization Field

開発組織は architecture state に force を注入する multi-agent field として読む。

```text
Demand field
  -> Requirement field
  -> Design field
  -> Agent / developer operation field
  -> Review / CI dissipation field
  -> Architecture Signature trajectory
```

| field | 発生源 | SFT 上の作用 |
| --- | --- | --- |
| demand field | PdM、顧客価値、KPI、ロードマップ | feature force の方向と頻度を決める。 |
| requirement field | PO、要件、acceptance criteria、優先順位 | operation script の粒度、順序、局所性を変える。 |
| design field | architect、境界、canonical pattern、非目標 | future PR force の流路を作り、bad force を局所化する。 |
| operation field | developer、AI agent、automation | 実際の architecture transition を生成する。 |
| dissipation field | review、CI、type checker、architecture rules | raw force を減衰、射影、拒否、修正する。 |
| observation field | Signature、Feature Extension Report、drift ledger | trajectory を観測し、制御入力へ戻す。 |

組織判断そのものを Lean theorem 化しない。組織判断が architecture transition distribution に
与える作用を観測対象にする。

## 10. AI-driven Development

AI agent は、field の上で operation を生成する制御対象 / 操作生成器である。

```text
AI agent operation
  = proposal distribution
  + prompt / policy boundary
  + allowed operation support
  + theorem precondition boundary
  + review / CI feedback
```

AI の安全性は、生成速度ではなく operation support と feedback control の問題として扱う。
AI agent が提案する operation が、AAT の certificate boundary と SFT の forecast / control
boundary の中に留まるかを観測する。

## 11. Lifecycle と End of Life

software field は生成と成長だけでなく、老朽化、migration、縮約、削除、終焉を含む。

```text
LifecycleTrajectory :=
  birth
  + growth
  + stabilization
  + drift
  + repair / migration
  + contraction
  + end-of-life
```

End-of-life は失敗ではなく、field control の一種である。
修復コスト、migration path、runtime risk、organization damping capacity、forecast cone の広がりを
見て、repair、migration、deletion のどれを選ぶかを扱う。

## 12. ArchSig の位置づけ

ArchSig は、AAT 的観測量を抽出し、SFT 的予測・制御に渡す計測層である。

```text
ArchSig
  = AAT signature / witness / certificate extractor
  + SFT force / forecast / trajectory analyzer
```

AAT 側:

```text
codebase / PR
  -> component universe
  -> signature axes
  -> obstruction witnesses
  -> proof obligation status
  -> certificate / non-conclusion
```

SFT 側:

```text
PRD / Spec / Issue / PR / Review / Incident
  -> force analysis
  -> forecast cone
  -> expected signature delta
  -> obstruction risk distribution
  -> force-shaping recommendation
  -> feedback update
```

ArchSig は、PR 後に危険を見る tool から、PRD 時点で architecture trajectory を予報する
tool へ拡張される。

## 13. 非目標

SFT は次を主張しない。

```text
- forecast cone が未来を決定する。
- same signature から same future operation support が従う。
- safe endpoint から safe trajectory が従う。
- accepted step から bad-axis nonincrease が無条件に従う。
- organization policy から incident reduction が Lean theorem として従う。
- AI agent policy から architecture lawfulness が無条件に従う。
- empirical correlation が causal proof である。
```

SFT の役割は、AAT の局所代数を観測量と制約として使い、ソフトウェア進化の大域的な場を
予測・制御・検証可能な研究対象へ分解することである。
