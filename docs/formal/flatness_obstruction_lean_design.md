# アーキテクチャ零曲率定理 Lean 化設計

Lean status: `proved` core / `defined only` schema /
`future proof obligation` / `empirical hypothesis`.

この文書は、archive した
[Flatness–Obstruction Conjecture](../archive/Flatness–Obstruction%20Conjecture.md)
を歴史的な数学面の草案として参照しつつ、現在の Lean 化方針を整理する設計メモである。
この中心定理候補を、研究本文では **アーキテクチャ零曲率定理** と呼ぶ。

定理候補の日本語表現は次である。

```text
有限な法則宇宙と完全被覆の下で、
アーキテクチャが法則健全であることは、
要求法則族に対する有限な阻害証人が存在しないこと、
すなわち ArchitectureSignature の要求阻害軸がすべて零であることと同値である。
```

Lean 側では、この主張を最初から数値的な `Curv_A = Sem_A(p) - Sem_A(q)`
として定義しない。まず、要求された law family に対して有限
`obstruction witness` が存在するかどうかを扱う。可換であるべき図式の非可換性は、
その最重要な特殊例として定義する。数値的な curvature, distance, norm, rank は、
観測値に追加構造を入れた後の派生 executable metric として扱う。
したがって、数値 curvature の未導入は Lean proved core の未完了を意味しない。

## 形式化の基本方針

最初の Lean target は、任意の law universe に依存しない generic witness-count
kernel である。これは、witness の型 `W`、悪い witness を判定する述語 `bad`、
測定候補 `List W` から violation list と count を作る薄い構造である。

```text
violatingWitnesses bad xs :=
  xs.filter bad

violationCount bad xs :=
  length (violatingWitnesses bad xs)
```

最初に証明する theorem は、有限 list 上の zero-count bridge に留める。

```text
violationCount bad xs = 0
  <-> forall w, w in xs -> not bad w
```

この theorem は `[DecidablePred bad]` を仮定する executable / finite metric 用の
補題として置く。

可換図式は、この kernel の特殊例として定義する。

```text
RequiredDiagram Expr :=
  lhs : Expr
  rhs : Expr

Semantics Expr Obs :=
  eval : Expr -> Obs

DiagramCommutes sem d :=
  sem.eval d.lhs = sem.eval d.rhs

DiagramBad sem d :=
  not (DiagramCommutes sem d)
```

この段階では `Expr` を自由 category や状態遷移代数に固定しない。
`Expr` は、projection square、状態遷移履歴、effect trace などを後から入れられる
抽象パラメータとして扱う。

required diagram 全体への bridge は、測定候補 list が required diagram を cover する
仮定を使って次の形にする。

```text
CoversRequired required measured :=
  forall d, required d -> d in measured

complete coverage ->
diagramViolationCount sem measured = 0 ->
forall d, required d -> DiagramCommutes sem d
```

`DiagramBad sem d` を `not (DiagramCommutes sem d)` と定義した場合、
`not (DiagramBad sem d)` から `DiagramCommutes sem d` を取り出す逆向きには
二重否定除去が必要になる。したがって、初期実装では theorem statement に
`[DecidableEq Obs]` を置くか、theorem 内で `by classical` を使う。
構成的に証明できる向きと、classical / decidable に依存する向きは分けておく。

この設計は既存の `projectionSoundnessViolation_eq_zero_of_projectionSound`,
`projectionSound_of_projectionSoundnessViolation_eq_zero`,
`lspViolationCount_eq_zero_of_lspCompatible` と同じ形の
zero-count bridge として実装する。

将来、厳密な等号ではなく観測同値で law を読む必要が出た場合は、
`DiagramCommutes` の内部を `=` から `Setoid` の `≈`、または明示的な
`equiv : Obs -> Obs -> Prop` へ置き換える。初期実装では `=` で始めてよいが、
名前は `DiagramCommutes` のままにして、後から観測同値へ一般化できる余地を残す。

## module 配置案

当面は `Formal/Arch` 直下の flat layout を維持する。
新規 module を追加する場合は、`Formal.lean` と
[Lean 定義・定理索引](../lean_theorem_index.md) を同じ PR で更新する。

候補は次である。

| module 候補 | 役割 |
| --- | --- |
| `Formal/Arch/Obstruction.lean` | generic witness-count kernel, finite witness list, zero-count bridge, diagram obstruction の最小特殊例。 |
| `Formal/Arch/Law.lean` | `RequiredDiagram`, `LawUniverse`, `DiagramCommutes` などを分離したくなった場合の law 側 module。初期段階では必須ではない。 |
| `Formal/Arch/Curvature.lean` | 観測値に距離・差分・重みを入れた後の派生 metric。初期段階では追加しない。 |

最初の実装では `Law.lean` と `Obstruction.lean` を分けず、
小さな `Obstruction.lean` から始めてもよい。`Curvature.lean` は名前の印象が強いので、
数値的構造を本当に導入するまで作らない。

## 用語

この文書では、次の日本語を優先する。

| 英語 | 日本語 |
| --- | --- |
| law universe | 法則宇宙 |
| required law family | 要求法則族 |
| complete coverage | 完全被覆 |
| lawfulness | 法則健全性 |
| obstruction witness | 阻害証人 |
| zero-count bridge | 零カウント橋渡し |

Lean identifier では、既存の英語技術語と整合させるため
`RequiredDiagram`, `Semantics`, `DiagramCommutes`, `violationCount`,
`CoversRequired` などの英語名を使う。

## 証明強度の段階

generic witness-count kernel は必要だが、それだけではアーキテクチャ零曲率定理の
実質的な証明とは呼ばない。

```text
violationCount bad xs = 0
  <-> forall w, w in xs -> not bad w
```

これは list filter の基本補題であり、Lean 実装上の共通部品である。
この補題単体、または `DiagramBad sem d := not (DiagramCommutes sem d)` の定義展開だけを
「アーキテクチャ零曲率定理の証明」とは扱わない。

強い形式化貢献と呼べるのは、次の三つを独立に定義した上で橋渡しできた場合である。

```text
Lawful A L
NoRequiredObstruction A L
RequiredAxesAvailableAndZero L sig
```

`Lawful A L` は、既存の意味論的 predicate や law family の充足条件として定義する。
たとえば `ProjectionSound`, `LSPCompatible`, `WalkAcyclic`,
`LocalReplacementContract`, `DiagramCommutes` などである。
`Lawful` を最初から `not exists obstruction witness` として定義しない。

`NoRequiredObstruction A L` は、各 law family に付随する witness 型 `W` と
`bad : W -> Prop` によって定義する。

`RequiredAxesAvailableAndZero L sig` は、`ArchitectureSignature` の required axis が
測定済みで、かつ 0 であることとして定義する。
`none` や未測定 axis は、lawfulness の証明では zero として扱わない。

この三者を bridge theorem で接続できたとき、アーキテクチャ零曲率定理は
単なる list 補題ではなく、異種アーキテクチャ法則族を阻害証人と Signature 零性へ
統一する表現定理になる。

## 既存 Lean API との接続

この設計は、既存 module を置き換えず、各 module の violation witness を共通語彙へ
持ち上げるための上位層として使う。

| 草案の成分 | 既存 Lean API | Lean 化の入口 |
| --- | --- | --- |
| dependency obstruction | `ClosedWalkWitness`, `Walk`, `HasClosedWalk`, `WalkAcyclic`, `Acyclic` | 閉 walk を forbidden dependency witness として扱う。 |
| nilpotence obstruction | `adjacencyNilpotent_iff_no_closedWalkObstruction`, `spectralRadiusOfAdjacency` | 有限 `ComponentUniverse` 上の matrix bridge を obstruction family として参照する。 |
| projection obstruction | `ProjectionSound`, `projectionSoundnessViolationEdges` | 抽象辺に写らない具象辺を projection witness とする。 |
| observation / LSP obstruction | `ObservationFactorsThrough`, `lspViolationPairs` | 同じ抽象 fiber 内の観測不一致を observation witness とする。 |
| local replacement | `LocalReplacementContract` | projection obstruction 不在、representative stability、observation factorization へ分解し、そこから projection / LSP obstruction の同時消滅を得る。 |
| state transition / effect boundary laws | `StateTransitionExpr`, `EffectBoundaryExpr` | replay / roundtrip / compensation を required diagram family として扱う。 |
| signature axis | `ArchitectureSignatureV1` | witness family ごとの count / optional metric として接続する。 |

状態遷移代数、effect algebra, boundary policy は、まず `Expr` と `Semantics`
による一般 law diagram として受け皿を作る。Lean では
`StateTransitionExpr` と `EffectBoundaryExpr` を追加し、replay / roundtrip /
compensation を finite required diagram family として表せるようにした。
この段階では、実コードベース抽出器の完全性や数値 curvature metric は主張しない。

特に dependency obstruction は、最初から `lhs != rhs` 型の diagram として無理に
表さない。`ClosedWalkWitness` のような forbidden witness 型を generic kernel に乗せる。
projection / LSP も既存 API の witness list を尊重し、それらが generic
`violatingWitnesses` の特殊例であることを bridge theorem として追加する。

各 law family では、次のような exactness theorem を目標にする。

```text
ProjectionSound
  <-> no projection obstruction witness

LSPCompatible
  <-> no LSP obstruction witness

WalkAcyclic
  <-> no closed-walk obstruction witness

DiagramLawful
  <-> no diagram obstruction witness
```

ここで左辺は obstruction framework とは独立に定義された意味論的 predicate である。
この独立性を保つことで、同値定理が定義展開だけにならないようにする。

## `ArchitectureSignature` との関係

`ArchitectureSignature` は単一スコアではなく、多軸診断として扱う。
Flatness–Obstruction 設計では、各 axis を次のいずれかとして分類する。

- `proved witness axis`: Lean 上で witness list と zero-count theorem がある。
- `defined executable axis`: executable metric はあるが、graph-level theorem が未完了。
- `empirical axis`: 実コードベースの観測値・運用データで評価する仮説。
- `unmeasured required law`: law universe には含まれるが、現時点では測定していない。

`signature = 0` を健全性と同一視するのは、complete coverage がある場合に限る。
coverage が不完全な場合は、測定済み violation がないことと、未測定の required law が
残っていることを区別する。

`Option Nat` で表される extension axis では、次の二つの predicate を分ける。

```text
MeasuredZero x :=
  forall n, x = some n -> n = 0

AvailableAndZero x :=
  x = some 0
```

`MeasuredZero none` は「測定された範囲では非零 violation がない」と読めるが、
lawfulness の証明には使わない。complete coverage や required law の充足には
`AvailableAndZero` 型の predicate を使い、未測定 `none` を risk zero と混同しない。

Signature との主 bridge では、各 axis ごとに exactness を分けて定義する。

```text
AxisExact axis witnessFamily :=
  axis is available and zero
    <-> no bad witness in the covered witness family
```

required axis 全体では、次を目標にする。

```text
RequiredAxesAvailableAndZero L sig
  <-> NoRequiredObstruction A L
```

この bridge が入ることで、`ArchitectureSignature` は単なる表示 schema ではなく、
要求法則族に対する阻害証人の零性を表す多軸座標として扱える。
Lean では、抽象 `LawFamily` に対して axis ごとの `AxisExact`、required witness
cover、required axis 全体の
`requiredAxesAvailableAndZero_iff_noRequiredObstruction_of_axisExactFamily`
を証明済みである。具体的な `ProjectionSound` / `LSPCompatible` /
`WalkAcyclic` / `LocalReplacementContract` / finite diagram law family については、
それぞれの witness 不在との exactness bridge を証明済みである。
さらに `Formal/Arch/SignatureLawfulness.lean` では、selected required Signature
axes を concrete `LawFamily` としてまとめ、`ArchitectureSignatureV1.axisValue`
の concrete valuation へ接続する final theorem
`architectureLawful_iff_requiredSignatureAxesZero` を追加した。

したがって、現時点で Lean proved と呼べる範囲は、抽象 `LawFamily` の structural
core と、selected required axes (`hasCycle`, projection, LSP, boundary,
abstraction) に対する Signature-integrated theorem である。今後この到達点を
**static structural core の QED** と呼ぶ。具体的には
`ArchitectureLawful X ↔ RequiredSignatureAxesZero (ArchitectureLawModel.signatureOf X)`
および `ArchitectureLawful X ↔ ArchitectureZeroCurvatureTheoremPackage X` を指す。
`nilpotencyIndex`, runtime / empirical metrics, numerical curvature、実コード
extractor の完全性は required zero axis ではなく、別の診断軸、実証仮説、または
future bridge work として扱う。

Issue [#222](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/222)
では、この境界を full law universe policy として固定した。Lean 側の
`ArchitectureLawUniverseCandidate` は、required law 5 件、LocalReplacement
packaging、state-effect diagram laws、matrix / spectral diagnostics、runtime
diagnostics、empirical axes を候補として列挙する。分類は
`architectureLawCandidateRole` で行い、required law は
`closedWalkAcyclicity`, `projectionSoundness`, `lspCompatibility`,
`boundaryPolicySoundness`, `abstractionPolicySoundness` だけである。
`localReplacementContract` と `stateEffectDiagramLaw` は derived corollary、
`nilpotencyIndex`, `spectralRadius`, `runtimePropagation` は diagnostic axis、
`relationComplexity`, `empiricalChangeCost` は empirical axis とする。
この分類により、final theorem の `ArchitectureLawful` を拡張せずに、後続 theorem
群で corollary / diagnostic bridge を追加できる。

Issue [#224](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/224)
では、その corollary / diagnostic bridge のうち matrix 側を
`MatrixDiagnosticCorollaries` として束ねた。`ArchitectureLawful X` または
`RequiredSignatureAxesZero (ArchitectureLawModel.signatureOf X)` から、finite
adjacency nilpotence、`nilpotencyIndexOfFinite X.U = some k`、および
`spectralRadiusOfAdjacency X.U = 0` が従う。これは `nilpotencyIndex` や
`spectralRadius` を required zero-axis に昇格するものではない。

Issue [#225](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/225)
では、runtime / empirical 系の境界を固定する。`runtimePropagation` は
0/1 `RuntimeDependencyGraph` 上の outgoing exposure radius として定義済みの
diagnostic axis であり、selected required law theorem の zero-axis ではない。
`runtimeBlastRadius` は reverse reachability 由来の tooling / analysis metric、
Circuit Breaker coverage とその policy-aware 派生 metric は empirical extension、
incident scope / repair time / hotfix size との関係は empirical hypothesis として
扱う。したがって、`ArchitectureLawful` と `RequiredSignatureAxesZero` の同値に
`runtimePropagation = some 0` や coverage ratio 0/1 条件を追加しない。未抽出の
`none`、測定済みの `some 0`、risk 0 の主張は常に区別する。

Issue [#226](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/226)
では、static structural core の theorem package を
`ArchitectureZeroCurvatureTheoremPackage` として追加した。この package は
`RequiredSignatureAxesZero (ArchitectureLawModel.signatureOf X)` と
`MatrixDiagnosticCorollaries X` を束ねる。Lean theorem
`architectureLawful_iff_architectureZeroCurvatureTheoremPackage` は、current
law-universe policy のもとで `ArchitectureLawful X` とこの package が同値で
あることを示す。runtime / empirical / 一般数値 curvature は package に含めず、
diagnostic / empirical boundary として残す。

complete coverage は単なる強い仮定として放置しない。
有限 component universe から component pair を列挙する、有限 diagram universe から
required diagram を列挙するなど、一部の law family では `CoversRequired` を実際に
構成・証明する。Lean では、finite required witness list を predicate として使う
`RequiredByList` / `RequiredDiagramsByList` と、その list が measured list に
含まれることから coverage を得る bridge を追加済みである。また、
`ComponentUniverse.componentPairWitnesses` は finite component universe から
ordered component-pair witness list を生成し、
`ComponentUniverse.coversWitnesses_componentPairWitnesses` により、その required pair
universe を cover する。

## Lean 化ロードマップ

1. `violatingWitnesses`, `violationCount`, zero-count bridge の generic
   witness-count kernel を作る。
2. `RequiredDiagram`, `Semantics`, `DiagramCommutes`, `DiagramBad` を
   diagram obstruction の特殊例として追加する。
3. `CoversRequired` と complete coverage 下の diagram zero-count bridge を証明する。
4. `ProjectionSound`, `LSPCompatible`, `WalkAcyclic` などの lawfulness predicate を
   obstruction framework とは独立に保ち、それぞれの witness 不在との exactness theorem を証明する。
5. `Projection` と `LSP` の既存 violation list が generic witness-count kernel の
   特殊例であることを bridge theorem として追加する。
6. closed walk / nilpotence obstruction を、diagram ではなく forbidden witness family
   として接続する。
7. `ArchitectureSignatureV1` の axis を witness family status に分類し、
   `MeasuredZero` と `AvailableAndZero` を分ける。
8. selected required law axes を `hasCycle`, projection, LSP, boundary,
   abstraction に固定し、required axis 用 constructor で concrete count を
   `some count` として埋める。
9. axis ごとの `AxisExact` と、required axis 全体の
   `RequiredAxesAvailableAndZero <-> NoRequiredObstruction` bridge を追加する。
10. 有限 universe から `CoversRequired` を構成できる law family を増やす。
11. 状態遷移履歴、effect boundary, replay / roundtrip / compensation law を
   個別の `Expr` と `Semantics` として追加する。Lean status: `proved` /
   `defined only`。`StateTransitionExpr`, `EffectBoundaryExpr` は `defined only`、
   各 finite diagram family の `DiagramLawful <-> NoDiagramObstruction` bridge は
   `proved`。
12. runtime metrics と一般数値 curvature は、実コード extractor や empirical
   hypothesis とは分け、数学的コアの拡張として Lean 化する。まず runtime 側は
   0/1 `RuntimeDependencyGraph` 上の obstruction / zero metric bridge、数値 curvature
   側は `curvature = 0 <-> commutativity` bridge を証明対象にする。

## 数値 curvature metric の派生層

数値 curvature metric は、zero-count bridge や required obstruction witness 不在の
代替ではなく、それらの上に載る数学的コアの拡張である。ここで Lean theorem として
狙うのは、現実の変更コストとの相関ではなく、数値的な 0 が diagram commutativity
または obstruction absence と一致するという bridge である。`Formal/Arch/Curvature.lean`
のような module は、少なくとも次の追加構造を固定してから導入する。

- 観測値 `Obs` 上の差分・距離・同値など、diagram 非可換性を数値化する構造。
- `d x y = 0 <-> x = y` のような zero-separation law。
- finite measured universe から非負値を集約する方法。`Nat` または `NNReal` のように、
  総和が 0 なら各項が 0 である構造を優先する。
- `none`、測定済み 0、測定済み非零を区別する Signature axis への載せ方。
- 数値と変更コスト・障害率・レビュー負荷の関係を検証する empirical protocol。ただし
  これは数学的コアの theorem ではなく、実証層で扱う。

最初の proof target は次である。

```text
curvature d p q = 0
  <-> DiagramCommutes semantics p q
  <-> no numerical curvature obstruction for (p, q)
```

finite universe 上の集約では、次を bridge theorem とする。

```text
totalCurvature measuredDiagrams = 0
  <-> every measured diagram has curvature 0
  <-> no measured numerical curvature obstruction
```

したがって、一般数値 curvature は `future proof obligation` として Lean 化できる。
一方、curvature の大きさと変更コスト・障害率・レビュー負荷の関係、重みの calibration、
現実 repository からの値の抽出完全性は `empirical hypothesis` / tooling validation
として数学的コアから分離する。数値 metric が入っても、既存の obstruction witness
zero-count theorem を置き換えず、追加の axis または派生評価として接続する。

## runtime metrics の数学的コア拡張

runtime metrics についても、Lean theorem と empirical / extractor 側の主張を分ける。
数学的コアへ入れる対象は、0/1 `RuntimeDependencyGraph` が既に与えられたときの
runtime obstruction と metric zero の bridge である。runtime edge metadata から
0/1 graph を抽出する完全性、Circuit Breaker coverage が incident scope や repair time
を下げるという主張は theorem 本体に含めない。

Issue #237 で証明した最小 bridge は次である。

```text
runtimePropagationOfFinite runtime components = 0
  <-> NoRuntimeExposureObstruction runtime components
```

ここで `NoRuntimeExposureObstruction` は、まず
`reachesWithin runtime components components.length` ベースの measured / bounded
obstruction として定義する。つまり、測定 universe 内の `source != target` な
runtime reachable cone が空であることを `some 0` の意味にする。semantic
`Reachable runtime source target` ベースの theorem として述べたい場合は、
`ComponentUniverse` coverage / edge-closure の下で `reachesWithin` と `Reachable` を
接続する bridge theorem を追加または再利用する。より policy-aware な拡張では、
raw graph とは別に `unprotectedRuntimeGraph` を入力として受け取り、同じ形の theorem
を証明する。

```text
unprotectedRuntimeExposureRadius unprotectedRuntimeGraph components = 0
  <-> NoUnprotectedRuntimeExposureObstruction unprotectedRuntimeGraph components
```

必要なら blast 側も、reverse runtime graph を明示的な入力として受け取る別 theorem
にする。reverse graph を extractor / tooling の暗黙処理にせず、Lean 側では
`RuntimeDependencyGraph` と `ReverseRuntimeDependencyGraph` または edge reversal
function の性質として扱う。

runtime theorem package は、static structural core の theorem package へ直接混ぜず、
まず次のような独立 package として育てる。

```text
ArchitectureRuntimeZeroCurvaturePackage
  = RequiredRuntimeAxesZero runtimeSignature
  ∧ RuntimeDiagnosticCorollaries
```

将来、static structural core、runtime core、numerical curvature core をまとめる場合も、
extractor completeness と empirical hypotheses は含めない。

## 証明対象と非対象

最初に Lean で証明する対象は、構造的・有限・全称的な命題に限定する。

- `proved`: finite witness list 上の generic zero-count bridge,
  `violationCount_eq_zero_iff_forall_not_bad`, [Issue #189](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/189)
- `proved`: required diagram の可換性と diagram obstruction witness 不在の同値,
  `diagramViolationCount_eq_zero_iff_forall_measured_DiagramCommutes`, [Issue #189](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/189)
- `proved`: finite measured law universe での diagram zero-count bridge,
  `requiredDiagramCommutes_of_coversRequired_and_diagramViolationCount_eq_zero`, [Issue #189](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/189)
- `proved`: 抽象 `LawFamily` で、独立 `Lawful` predicate、`NoRequiredObstruction`,
  `RequiredAxesAvailableAndZero` を分離し、complete witness coverage と
  required axis exactness を前提にした中心 bridge,
  `lawful_iff_requiredAxesAvailableAndZero_of_completeCoverage_and_requiredAxisExact`,
  [Issue #191](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/191)
- `proved`: required Signature axis について、`MeasuredZero` と
  `AvailableAndZero` を分離し、axis ごとの `AxisExact` と required witness cover
  から `RequiredAxesAvailableAndZero <-> NoRequiredObstruction` を得る抽象 bridge,
  `requiredAxesAvailableAndZero_iff_noRequiredObstruction_of_axisExactFamily`,
  [Issue #195](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/195)
- `proved`: `ProjectionSound` / `LSPCompatible` と obstruction witness 不在の
  exactness bridge、および既存 finite violation list membership が generic
  `violatingWitnesses` の特殊例であること,
  `projectionSound_iff_noProjectionObstruction`,
  `lspCompatible_iff_noLSPObstruction`, [Issue #188](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/188)
- `proved`: `ClosedWalkWitness` を forbidden dependency witness として追加し、
  `WalkAcyclic`, `Acyclic`, finite `AdjacencyNilpotent` と witness 不在を接続する
  exactness bridge,
  `walkAcyclic_iff_no_closedWalkObstruction`,
  `adjacencyNilpotent_iff_no_closedWalkObstruction`,
  [Issue #190](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/190)
- `proved`: `LocalReplacementContract` は projection obstruction 不在、
  representative stability、observation factorization に分解され、そこから
  projection obstruction と LSP obstruction の同時消滅、および対応する finite
  violation count が 0 であること,
  `localReplacementContract_iff_noProjectionObstruction_and_representativeStable_and_observationFactorsThrough`,
  `noProjectionObstruction_and_noLSPObstruction_of_localReplacementContract`,
  `violationCounts_eq_zero_of_localReplacementContract`,
  [Issue #188](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/188)
- `proved`: 抽象 `LawFamily` では、complete coverage 下での measured zero から
  global lawfulness への bridge,
  `lawViolationCount_eq_zero_iff_lawful`, `lawful_iff_noRequiredObstruction_of_completeCoverage`,
  [Issue #191](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/191)
- `proved`: concrete `ArchitectureWitness` family と selected required
  `ArchitectureSignatureV1` axes について、`ArchitectureLawful X` と
  `RequiredSignatureAxesZero (ArchitectureLawModel.signatureOf X)` を接続する
  static structural core の QED の中核となる Signature-integrated zero-curvature theorem,
  `architectureLawful_iff_requiredSignatureAxesZero`,
  [Issue #212](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/212)
- `proved`: finite required witness / diagram list から coverage predicate を構成し、
  finite component universe から ordered component-pair witness coverage を得る bridge,
  `coversWitnesses_requiredByList_self`,
  `coversRequired_requiredDiagramsByList_self`,
  `ComponentUniverse.coversWitnesses_componentPairWitnesses`,
  [Issue #192](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/192)
- `proved`: 状態遷移履歴と effect boundary の replay / roundtrip / compensation
  finite diagram family について、lawfulness と diagram obstruction witness 不在を
  接続する bridge,
  `stateReplayLawful_iff_noStateReplayObstruction`,
  `stateRoundtripLawful_iff_noStateRoundtripObstruction`,
  `stateCompensationLawful_iff_noStateCompensationObstruction`,
  `effectReplayLawful_iff_noEffectReplayObstruction`,
  `effectRoundtripLawful_iff_noEffectRoundtripObstruction`,
  `effectCompensationLawful_iff_noEffectCompensationObstruction`,
  [Issue #193](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/193)
- `proved`: LocalReplacement を required law に追加せず derived corollary として
  selected required Signature axes および final zero-curvature theorem に接続する
  bridge, および state-effect diagram laws を aggregate package と obstruction absence
  の同値として束ねる bridge,
  `localReplacementContract_requiredSignatureProjectionLSPAxes`,
  `requiredSignatureAxesZero_of_localReplacementContract`,
  `stateTransitionLawFamilyLawful_iff_noStateTransitionLawFamilyObstruction`,
  `effectBoundaryLawFamilyLawful_iff_noEffectBoundaryLawFamilyObstruction`,
  [Issue #223](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/223)
- `proved`: concrete required-law Signature entry point 上で、
  `.projectionSoundnessViolation` と `.lspViolationCount` の available-and-zero を
  それぞれ `NoProjectionObstruction` / `NoLSPObstruction` へ接続する direct axis
  exactness theorem,
  `projectionSoundnessViolation_axisExact`,
  `lspViolationCount_axisExact`,
  [Issue #209](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/209)
- `proved`: concrete required-law Signature entry point 上で、`.hasCycle` の
  available-and-zero を `WalkAcyclic` および closed-walk obstruction witness 不在へ
  接続する direct axis exactness theorem,
  `hasCycle_axisExact`,
  `hasCycle_axisExact_no_closedWalkObstruction`,
  [Issue #210](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/210)
- `proved`: concrete required-law Signature entry point 上で、
  `.boundaryViolationCount` と `.abstractionViolationCount` の available-and-zero を
  それぞれ `BoundaryPolicySound` / `AbstractionPolicySound` へ接続する direct axis
  exactness theorem,
  `boundaryViolation_axisExact`,
  `abstractionViolation_axisExact`,
  [Issue #211](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/211)
- `defined only` / `proved`: full law universe policy を
  `ArchitectureLawUniverseCandidate` と `ArchitectureLawCandidateRole` として
  列挙し、required law が current final theorem の 5 条件に限られることを
  `architectureLawCandidateRole_requiredLaw_iff` で証明した,
  [Issue #222](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/222)。
- `proved`: full law universe policy に従い、nilpotency / spectral diagnostics を
  required zero-axis へ追加せず derived diagnostic corollary として theorem index
  へ接続する bridge,
  `MatrixDiagnosticCorollaries`,
  `matrixDiagnosticCorollaries_of_architectureLawful`,
  `matrixDiagnosticCorollaries_of_requiredSignatureAxesZero`,
  [Issue #224](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/224)。
  `nilpotencyIndex` は `some k` として最初の zero adjacency power を返す
  executable index であり、`RequiredAxesAvailableAndZero` の zero-axis ではない。
- `defined only` / `proved` / `empirical hypothesis`: runtime / empirical 系の required-law
  境界を固定する。`runtimePropagation` は 0/1 `RuntimeDependencyGraph` 上の
  exposure radius として定義済みの diagnostic axis であり、
  `ArchitectureLawful` や `RequiredSignatureAxesZero` の required zero-axis ではない。
  0/1 graph 上の runtime zero bridge は proved bridge として扱い、
  policy-aware runtime exposure、blast radius、extractor completeness と
  incident / repair cost との関係は tooling / empirical protocol 側に残す,
  [Issue #225](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/225)。
- `defined only` / `proved`: static structural core の QED を読むための theorem package を
  `ArchitectureZeroCurvatureTheoremPackage` として追加し、current law-universe
  policy のもとで `ArchitectureLawful X` と theorem package が同値であることを
  `architectureLawful_iff_architectureZeroCurvatureTheoremPackage` で証明した。
  LocalReplacement から package へ進む derived bridge も
  `architectureZeroCurvatureTheoremPackage_of_localReplacementContract` で証明済みである,
  [Issue #226](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/226)。
- `defined only`: witness family をまとめる signature schema と
  `ArchitectureSignatureV1` axis measurement classification。
- `proved`: zero-separating distance 上の数値 curvature について、
  `curvature = 0 <-> DiagramCommutes` を証明し、さらに有限な測定済み
  diagram list 上の `Nat` 和として
  `totalCurvature = 0 <-> no measured numerical curvature obstruction` を証明した,
  [Issue #239](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/239),
  [Issue #240](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/240)。
- `defined only` / `proved`: positive-weighted curvature について、
  `totalWeightedCurvature = 0 <-> no measured numerical curvature obstruction`
  を証明した。Signature axis への載せ方、およびより一般の集約構造での
  zero-reflection bridge は future proof obligation として残す。
- `proved`: 0/1 `RuntimeDependencyGraph` が与えられたとき、
  runtime exposure zero metric と measured / bounded runtime obstruction absence を
  接続する bridge、および `ComponentUniverse` 下で semantic `Reachable` 版へ接続する
  bridge。
- `future proof obligation`: policy-aware runtime exposure、blast radius 版の zero metric と
  obstruction absence を接続する bridge。
- `empirical hypothesis`: 数値 curvature や runtime metrics と変更コスト・障害率・
  レビュー負荷・incident scope の相関。
- `empirical hypothesis`: obstruction count と変更コスト・障害率・レビュー負荷の相関。

次は初期 Lean proof の対象にしない。

- 任意のリスク評価が `ArchitectureSignature` を通して因子化するという完全な普遍性予想。
- 変更波及や障害伝播が spectral mass によって支配されるという実証的主張。
- runtime exposure / blast radius や Circuit Breaker coverage が incident scope,
  repair time, hotfix size を支配するという実証的主張。
- 実コード extractor が完全な `RuntimeDependencyGraph` や numerical curvature input を
  生成するという tooling correctness claim。

これらは、必要な追加構造と empirical protocol が固まった後に、別 Issue として扱う。
