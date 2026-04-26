# アーキテクチャ零曲率定理 Lean 化設計

Lean status: `future proof obligation` / formalization design.

この文書は [Flatness–Obstruction Conjecture](../math/Flatness–Obstruction%20Conjecture.md)
を、数学面の草案として残したまま Lean 化するための設計メモである。
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
観測値に追加構造を入れた後の executable metric として扱う。

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
[Lean 定義・定理索引](lean_theorem_index.md) を同じ PR で更新する。

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
| local replacement | `LocalReplacementContract` | projection witness と observation witness の同時消滅として扱う。 |
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
を証明済みである。具体的な `ProjectionSound` / `LSPCompatible` などの
law family への exactness 接続は、個別の proof obligation として残す。

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
8. axis ごとの `AxisExact` と、required axis 全体の
   `RequiredAxesAvailableAndZero <-> NoRequiredObstruction` bridge を追加する。
9. 有限 universe から `CoversRequired` を構成できる law family を増やす。
10. 状態遷移履歴、effect boundary, replay / roundtrip / compensation law を
   個別の `Expr` と `Semantics` として追加する。Lean status: `proved` /
   `defined only`。`StateTransitionExpr`, `EffectBoundaryExpr` は `defined only`、
   各 finite diagram family の `DiagramLawful <-> NoDiagramObstruction` bridge は
   `proved`。
11. 観測値に距離・重み・半環などを入れる必要が出た時点で、数値的 curvature metric を
   派生定義として追加する。

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
- `proved`: 抽象 `LawFamily` では、complete coverage 下での measured zero から
  global lawfulness への bridge,
  `lawViolationCount_eq_zero_iff_lawful`, `lawful_iff_noRequiredObstruction_of_completeCoverage`,
  [Issue #191](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/191)
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
- `future proof obligation`: 残る具体的な lawfulness predicate と witness 不在の
  exactness bridge。
- `future proof obligation`: required Signature axis の abstract bridge を具体的な
  projection / LSP / walk / nilpotence witness family に接続する定理。
- `defined only`: witness family をまとめる signature schema と
  `ArchitectureSignatureV1` axis classification。
- `empirical hypothesis`: obstruction count と変更コスト・障害率・レビュー負荷の相関。

次は初期 Lean proof の対象にしない。

- 任意のリスク評価が `ArchitectureSignature` を通して因子化するという完全な普遍性予想。
- 変更波及や障害伝播が spectral mass によって支配されるという実証的主張。
- 一般の観測値に対する `Sem_A(p) - Sem_A(q)` 型の数値 curvature。

これらは、必要な追加構造と empirical protocol が固まった後に、別 Issue として扱う。
