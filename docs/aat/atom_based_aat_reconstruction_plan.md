# AAT Atom-Based Reconstruction Plan

この文書は、AAT を完全な Atom-generated algebra として再構成するための計画書である。

目的は小さな補修ではない。既存の AAT theorem package に薄い Atom wrapper を足すことでもない。
実コードから検出できる primitive architectural facts を Atom として置き、その Atom から
architecture object、law、obstruction、operation、flatness、path / homotopy、signature、
analytic representation、SFT handoff までを生成する理論へ書き直す。

## 0. 背景

Atom を AAT に導入した理由は、以前の AAT が boundary、selected universe、coverage assumption、
explicit witness family に強く依存し、形式的には綺麗でも実コードから浮いた理論になっていたからである。

本来の要求は次である。

```text
source code
  -> detected Atoms
  -> Atom-generated algebra
  -> Molecule / ArchitectureObject
  -> Law / Obstruction / Operation
  -> Flatness / Path / Homotopy / Signature / Analytic representation
  -> ArchSig / FieldSig readings
```

現状の `AtomAxiomSystem` は Atom を observation、law、tool output、SFT event から独立させる
root としては有効である。しかし、それだけでは Atom から後半の数学が生成されたことにならない。
この計画は、その不足を根本から直す。

## 1. 最大スコープ

この計画のスコープは最大である。

- すべての AAT theorem package は、最終的に Atom-generated representation に接続される。
- `ArchGraph`、`ArchitectureLawModel`、`FeatureExtension`、`Path`、`Diagram`、`Curvature`、
  `Signature`、`SFT` の既存定理は、手で与えた representation 上の孤立定理として残さない。
- 既存 API の互換維持は目的にしない。Atom-generated algebra に接続できない surface は、
  rewrite、archive、または後段 library として明示的に降格する。
- ArchSig は AAT の欠落を heuristic、proxy、boundary-heavy output で補わない。
- docs は実装を正当化するために先行更新しない。Lean / Rust の acceptance test が通った事実だけを
  後から同期する。

## 2. 非目標

次は明示的に非目標である。

- 現状の claim を下げるだけの docs 修正。
- 後半 theorem に `AATCore` 引数を足すだけの wrapper。
- `architectureLawfulFromAAT` のような bridge field を仮定として渡し、接続済みと呼ぶこと。
- `nonConclusions` や boundary 文言を増やして慎重に見せること。
- Viewer の配置 heuristic を改善して、理論改善の代替にすること。
- ArchMap の不完全性だけを理由に ArchSig の診断力不足を説明すること。

## 3. 中心原理

### 3.1 Atom は無構造な点ではない

Atom は最小単位であるが、性質を持たない点ではない。Atom は「これ以上分けると同じ typed fact として
意味を保てない」primitive architectural fact である。

したがって Atom は少なくとも次の形を持つ。

```text
AtomShape
  family
  axis
  subject
  predicate
  object slots
  payload slots
  direction
  arity
  ports / valence
```

`sourceRefs`、`confidence`、`evidenceBoundary` は observation metadata であり Atom core ではない。
しかし、`subject`、`predicate`、`object slots`、`payload slots`、`ports / valence` は Atom の内的形である。

### 3.2 Molecule は単なる Atom 集合ではない

Molecule は Atom の有限配置である。しかし、任意の集合ではない。
AtomShape の ports / valence が噛み合い、同じ architecture reading を生成できる compatible composition
でなければならない。

```text
CompatibleComposition(a, b)
GeneratedMolecule(M)
```

を AAT core の第一級概念にする。

### 3.3 ArchitectureObject は手で与えた graph ではない

`ArchGraph` や `ArchitectureLawModel` は Atom-generated structure の projection または analytic representation
でなければならない。

```text
AtomConfiguration
  -> GeneratedArchitectureObject
  -> generated ArchGraph
  -> generated Observation
  -> generated LawModel
```

この生成写像を持たない theorem package は、Atom-based AAT の完了条件を満たさない。

### 3.4 Boundary は主役ではない

Boundary、coverage、exactness、non-conclusion は必要である。しかしそれらは出発点ではない。
出発点は実コードから検出される Atom と、その Atom が生成する algebra である。

```text
悪い順序:
selected boundary -> theorem package -> possible atom interpretation

正しい順序:
detected atoms -> generated algebra -> theorem package -> remaining boundary
```

## 4. 新しい Lean kernel

新しい kernel は、既存の `AtomAxiomSystem` を削除するのではなく、薄い root から生成代数へ進める層を追加する。

### 4.1 Atom shape layer

追加候補:

```text
Formal/Arch/Atom/Shape.lean
Formal/Arch/Atom/Valence.lean
Formal/Arch/Atom/Composition.lean
```

必須概念:

- `AtomSubject`
- `AtomObjectSlot`
- `AtomPayloadSlot`
- `AtomPort`
- `AtomValence`
- `AtomShape`
- `AtomShapeOf : system.Atom -> AtomShape`
- `shape_kind_aligned`
- `shape_axis_aligned`
- `shape_single_fact`

### 4.2 Composition layer

追加候補:

```text
Formal/Arch/AAT/AtomComposition.lean
Formal/Arch/AAT/GeneratedMolecule.lean
```

必須概念:

- `PortCompatible`
- `SlotCompatible`
- `PredicateSlotCompatible`
- `CompatibleComposition`
- `CompositionGraph`
- `GeneratedMolecule`
- `GeneratedMolecule.atomsPrimitive`
- `GeneratedMolecule.compatiblePairs`
- `GeneratedMolecule.notArbitrarySet`

negative theorem:

```text
incompatible_slots_not_generatedMolecule
missing_required_port_not_generatedMolecule
```

### 4.3 Generated architecture object layer

追加候補:

```text
Formal/Arch/AAT/GeneratedObject.lean
Formal/Arch/AAT/GeneratedGraph.lean
Formal/Arch/AAT/GeneratedLawModel.lean
```

必須概念:

- `GeneratedArchitectureObject`
- `GeneratedCarrier`
- `GeneratedRelation`
- `GeneratedEffect`
- `GeneratedAuthority`
- `GeneratedContract`
- `GeneratedObservation`
- `GeneratedArchGraph`
- `GeneratedArchitectureLawModel`

重要 theorem:

```text
generated_graph_edges_from_relation_atoms
generated_observation_from_semantic_atoms
generated_authority_policy_from_authority_atoms
generated_effect_law_input_from_effect_atoms
generated_law_model_from_generated_object
```

### 4.4 Generated theorem bridge layer

追加候補:

```text
Formal/Arch/AAT/GeneratedSignature.lean
Formal/Arch/AAT/GeneratedFlatness.lean
Formal/Arch/AAT/GeneratedFeatureExtension.lean
Formal/Arch/AAT/GeneratedPath.lean
Formal/Arch/AAT/GeneratedDiagram.lean
Formal/Arch/AAT/GeneratedCurvature.lean
Formal/Arch/AAT/GeneratedAnalyticRepresentation.lean
Formal/Arch/AAT/GeneratedSFT.lean
```

目的:

- 既存 theorem package を捨てるのではなく、Atom-generated input に接続し直す。
- 手作り representation を受け取る theorem は後段 library として残してよいが、AAT theorem の主張は
  generated input 版を source of truth にする。

## 5. 既存 theorem package の再分類

すべての既存 theorem package を次に分類する。

```text
A. Atom-generated
   AtomShape / CompatibleComposition / GeneratedArchitectureObject から発火する。

B. Atom-rooted but bridge-assumed
   AtomAxiomSystem / AATCore を受け取るが、重要な生成写像や lawfulness bridge が field 仮定。

C. Representation-level
   ArchGraph / Path / Observation / ArchitectureLawModel / FeatureExtension などの上で成立するが、
   Atom から生成されたことを要求しない。
```

完了時には、主要 theorem package は A へ移行する。
B は一時状態としてのみ許す。
C は後段 library、legacy surface、または rewrite target として扱う。

## 6. Acceptance Tests

この再構成は、テスト駆動で進める。ただし ordinary unit test ではなく、逃げ道を塞ぐ acceptance theorem を置く。

### 6.1 Lean positive acceptance

最初に必要な赤い theorem:

```text
AtomGeneratedSignatureExamples
```

要求:

```text
source-like AtomShape を持つ atom 群
  -> CompatibleComposition
  -> GeneratedMolecule
  -> GeneratedArchitectureObject
  -> GeneratedArchGraph / GeneratedObservation / GeneratedArchitectureLawModel
  -> existing Signature theorem applies
  -> RequiredSignatureAxesZero is derived for the generated law model
```

合格条件:

- `ArchGraph` を手で与えない。
- `ArchitectureLawModel` を手で与えない。
- `architectureLawfulFromAAT` を field として仮定しない。
- `GeneratedArchitectureLawModel` が Atom-generated object から構成される。

### 6.2 Lean negative acceptance

通ってはいけない theorem:

```text
IncompatibleAtomCompositionExamples
```

要求:

- slot / valence が合わない Atom は generated molecule にならない。
- relation endpoint が存在しない relation atom は generated graph edge にならない。
- effect atom に対応する authority port がない場合、authority/effect law satisfied は出ない。
- concern hint は obstruction circuit にならない。
- observation gap は measured zero にならない。
- hand-authored graph は Atom-generated graph として扱えない。

### 6.3 Rust / ArchSig acceptance

代表的な ArchMap acceptance fixture を用意し、次を検査する。

```text
atomObservations
  -> generatedMolecules
  -> generatedLawInputs
  -> applicableLawAxes
  -> localSatisfied / localViolated / locallyBlocked
  -> viewerDistanceInputs
```

合格条件:

- `nonConclusions` の数ではなく、生成された中間物の有無を見る。
- 観測済み Atom から構成可能な molecule / law input を boundary に逃がさない。
- proxy、concern-only cue、schema presence だけで nonzero reading を出さない。

## 7. 破壊的移行計画

### Phase 1: Red acceptance suite

目的:

- まだ通らない acceptance theorem / fixture を先に置く。
- 現状が要求に届いていないことを機械的に固定する。

成果物:

- `Formal/Arch/Examples/AtomGeneratedSignatureExamples.lean`
- `Formal/Arch/Examples/IncompatibleAtomCompositionExamples.lean`
- `tools/archsig/tests/fixtures/atom_generated_acceptance/`
- CI / local verification command list

### Phase 2: AtomShape / Valence kernel

目的:

- Atom を無構造な root から typed shape を持つ生成元に引き上げる。

成果物:

- `AtomShape`
- `AtomValence`
- `AtomPort`
- shape alignment theorem
- examples for existence / relation / capability / state / effect / authority / contract / semantic / runtime atoms

### Phase 3: Compatible composition and generated molecule

目的:

- Molecule を任意集合ではなく compatible finite configuration にする。

成果物:

- `CompatibleComposition`
- `GeneratedMolecule`
- composition graph
- positive / negative examples

### Phase 4: Generated architecture object

目的:

- Atom-generated molecule から architecture object を構成する。

成果物:

- generated carrier
- generated relation graph
- generated observation
- generated policy / authority surface
- generated effect / state transition surface

### Phase 5: Signature and lawfulness bridge rewrite

目的:

- `ArchitectureLawModel` を手で与えるのではなく、generated object から作る。

成果物:

- `GeneratedArchitectureLawModel`
- `signatureOfGenerated`
- `generatedArchitectureLawful_iff_requiredSignatureAxesZero`
- AATCore bridge から field 仮定を減らす、または削除する。

### Phase 6: Flatness / path / homotopy / curvature bridge rewrite

目的:

- FeatureExtension、Path、Diagram、Curvature を Atom-generated object から発火させる。

成果物:

- generated path family
- generated diagram family
- generated filler / non-fillability witness
- generated self-view feature-step lifting bridge over generated carriers
- generated filling-failure bridge from `GeneratedNonFillabilityWitnessFor` to
  `NonSplitExtensionWitnessPackage` over generated identity feature extensions
- generated curvature measurement input
- generated flatness theorem package

### Phase 7: Operation / repair / synthesis rewrite

目的:

- repair と synthesis を solver boundary ではなく Atom-generated obstruction / operation algebra として読む。

成果物:

- generated operation
- operation preserves / transforms AtomShape
- non-identity generated operation transport between distinct source / target generated molecules
- transport circuit delta keeps source / target law and molecule selections separate
- generated repair problem configuration before `GeneratedMolecule`
- repair clears port / slot / valence mismatch into a generated target object
- repair clears selected generated obstruction
- repair target is port / slot / valence mismatch, not free-form recommendation

### Phase 8: ArchSig integration

目的:

- ArchSig が AAT の欠落を補うのではなく、AAT-generated structure を読むようにする。

成果物:

- generated molecule readings
- generated law input readings
- generated local obstruction readings
- generated repair target readings
- viewer distance inputs from AtomShape / generated structure
- generated SFT consequence-envelope input from `GeneratedSFTInput` and
  generated ArchSig transition evidence

### Phase 9: Docs synchronization

目的:

- 実装と acceptance theorem が通った事実だけを docs に反映する。

成果物:

- `docs/aat/proof_obligations.md` update
- `docs/aat/lean_theorem_index.md` update
- 必要なら `docs/aat/mathematical_theory/` 本文更新。ただしこれは実装後に行う。

## 8. 検査体系

### 8.1 Lean checks

必須:

```bash
lake build
```

追加スキャン:

```bash
rg -n "\b(axiom|admit|sorry|unsafe)\b" Formal docs
rg -n "architectureLawfulFromAAT|DoesNotDefineAAT|DoesNotCreateAtoms" Formal/Arch
rg -n "ArchGraph|ArchitectureLawModel|FeatureExtension|Path|Observation" Formal/Arch
```

`architectureLawfulFromAAT` 型の bridge field は theorem package source として扱わない。
残す場合は legacy surface として分離し、対応する generated replacement entrypoint と
「registry row ではない」acceptance theorem を置く。

### 8.2 Theorem classification check

機械的に各 theorem package を分類する。

```text
Atom-generated theorem:
  signature に Generated* 入力がある。

Bridge-assumed theorem:
  AtomAxiomSystem / AATCore はあるが、重要結論が field 仮定。

Representation-level theorem:
  ArchGraph / Path / Observation / FeatureExtension だけで完結する。
```

分類不能な theorem は合格扱いしない。

実装済み検査:

```text
Formal/Arch/AAT/TheoremClassification.lean
Formal/Arch/Examples/AtomGeneratedClassificationExamples.lean
```

`TheoremPackageClass` は `atomGenerated` / `bridgeAssumed` / `representationLevel`
だけを持ち、`unclassified` constructor を持たない。各 registry row は分類に応じて
generated entrypoint、bridge assumption、representation surface の evidence list と
許可された migration action を要求する。

current registry は `theorem_package_registry_has_no_bridge_assumed_rows` と
`theorem_package_registry_has_no_rewrite_targets` により、bridge-assumed row と
rewrite target row が残っていないことを Lean 上で固定する。generic Signature bridge は
`legacyBridgeSurfaces` に移し、`architectureLawfulFromAAT` bridge assumption と
`AATCoreSignatureLawfulnessBridge.ofGeneratedLawModel` replacement を明示するが、
theorem package registry の source row には数えない。

### 8.3 ArchSig checks

必須:

```bash
cargo test --manifest-path tools/archsig/Cargo.toml
```

追加 acceptance:

```text
atom_generated_acceptance fixture:
  expected generatedMolecules > 0
  expected generatedLawInputs > 0
  expected applicableLawAxes > 0
  expected localSatisfied/localViolated/locallyBlocked present
  expected generatedRepairTargets > 0
  expected viewerDistanceInputs present
```

## 9. 完了条件

この計画は、次を満たすまで完了しない。

- AtomShape / AtomValence / CompatibleComposition が Lean に存在する。
- Molecule は compatible finite configuration として扱われる。
- GeneratedArchitectureObject が Lean に存在する。
- `ArchGraph` / `Observation` / `ArchitectureLawModel` の主要 entrypoint が generated object から構成される。
- Signature lawfulness theorem が generated law model に対して発火する。
- Flatness / path / homotopy / curvature の主要 theorem package が generated input に接続される。
- Operation / repair / synthesis が generated obstruction / generated operation として接続される。
- ArchSig が generated molecule / law input / obstruction / repair target を出力する。
- Viewer の距離・配置は AtomShape と generated structure を根拠にする。
- hand-authored representation theorem は AAT の主張ではなく後段 library として扱われる。
- theorem package registry に `bridgeAssumed` / `rewriteTarget` の残存 row がない。

## 10. 失敗条件

次のいずれかが起きたら、この再構成は失敗である。

- 後半 theorem に Atom wrapper だけを足して完了扱いする。
- `Generated*` という名前の structure が、実際には手作り graph / law model を field として持つだけになる。
- ArchSig が generated middle layer を出さず、summary 文言だけを改善する。
- non-conclusion や boundary が増え、構成的診断が増えない。
- docs が先行し、Lean / Rust acceptance が後追いになる。
- ArchMap の不完全性を理由に、観測済み Atom から構成できる結論まで出さない。

## 11. 最初の PR の形

最初の PR は完成 PR ではない。赤い acceptance theorem と、AAT 再構成の第一生成 kernel を置く PR である。

推奨タイトル:

```text
AAT Atom-generated algebra の acceptance suite と生成核を導入する
```

PR の完了条件:

- positive acceptance theorem が少なくとも一つ通る。
- negative acceptance theorem が少なくとも一つ通る。
- existing representation-level theorem を Atom-generated input に一つ接続する。
- thin bridge field だけでは acceptance が通らない。
- `lake build` が通る。

## 12. ArchSig への期待される変化

AAT 側の生成核が入ると、ArchSig の出力は次の方向へ変わる。

```text
before:
  coverage boundary
  exactness boundary
  non-conclusion
  partial reading

after:
  generated molecule present
  law axis applicable
  required ports satisfied
  missing port identified
  local obstruction constructed
  repair target identified
  remaining boundary localized
```

ArchSig は boundary を消す必要はない。しかし、boundary が主役であってはならない。
Atom が十分に観測されているなら、AAT-generated middle layer が構成され、そこから診断が出なければならない。

## 13. AAT 完全形式化への次段計画

この文書のここまでの計画は、Atom-generated layer と代表 theorem package の接続を作る
第一段階である。次段階の目的は、ArchSig fixture を増やすことではなく、AAT の主張集合を
Lean 上の閉じた theorem suite として定義し、各 theorem package がその suite のどの field を
満たすかを明示することである。

この段階では、`boundary` は「原理的に証明できない巨大 claim」を並べるための語ではない。
必要なのは、実装がどこまで到達していて、次にどの Lean field が未充足なのかを見える形にする
実装境界である。

### 13.1 直近の実装境界

現状の到達点:

- `AtomShape` / `AtomValence` / `CompatibleComposition` が存在する。
- `GeneratedMolecule` は primitive atoms、composition graph、required-port matching を要求する。
- `GeneratedArchitectureObject`、generated relation / runtime graph、`GeneratedArchitectureLawModel` が存在する。
- Signature、flatness、path / diagram、curvature、analytic representation、operation / repair / synthesis、
  SFT / ArchSig / FieldSig handoff への代表 entrypoint が存在する。
- theorem package classification registry は、current row に `bridgeAssumed` / `rewriteTarget` が
  残らないことを Lean 上で検査する。

未到達の実装境界:

- AAT 全体の claim family を束ねる top-level theorem suite がまだない。
- theorem package registry は重要 candidate の curated registry であり、AAT の完成 claim set そのものではない。
- 各 theorem package が「AAT source of truth の field」なのか「downstream representation library」なのかを、
  top-level suite の型で強制していない。
- `GeneratedGraphRank` など、外部 certificate を受け取る箇所がどの suite field の未充足前提なのか、
  一箇所で読める形になっていない。
- ArchSig generated packet と Lean generated theorem layer は対応する surface を持つが、
  proof-carrying handoff としてはまだ束ねていない。

### 13.2 単一設計点: AATCompleteFormalization

次の PR では、大量の新 theorem を先に書かない。まず AAT 完全形式化の受け皿を作る。

候補ファイル:

```text
Formal/Arch/AAT/CompleteFormalization.lean
Formal/Arch/Examples/AATCompleteFormalizationExamples.lean
```

候補 API:

```text
AtomGeneratedAATWorld
AATTheoremSuite
AATImplementationFrontier
AATCompleteFormalization
```

`AtomGeneratedAATWorld` は、Atom root、shape presentation、generated molecule、
generated architecture object、generated graph / law model など、AAT theorem suite が読む
共通 world を持つ。`AATTheoremSuite` は、AAT が source of truth として主張する theorem family を
field として列挙する。

最初の suite field family:

- Atom / shape / composition kernel
- generated molecule / generated architecture object
- generated graph / runtime graph / graph rank
- generated law model / Signature / zero-curvature package
- flatness / curvature
- path / homotopy / diagram / non-fillability
- feature extension / obstruction / extension formula
- operation / repair / synthesis
- analytic representation / obstruction valuation
- SFT / ArchSig / FieldSig handoff
- theorem package classification / downstream representation separation

`AATImplementationFrontier` は未充足 field を明示するための台帳である。これは
「いつか証明できるか分からない巨大 claim」を置く場所ではない。対象は、既存の Lean API、
今後追加すべき theorem、または外部 certificate を受け取っている concrete entrypoint に限る。

### 13.3 Suite 設計ルール

- `AATTheoremSuite` の source field は Atom-generated input を読む。
- hand-authored `ArchGraph` / `ArchitectureLawModel` / `FeatureExtension` だけで閉じる theorem は、
  source field ではなく downstream representation library として分離する。
- `architectureLawfulFromAAT` のような bridge assumption は source field に入れない。
- compatibility wrapper は残してよいが、対応する generated replacement を持ち、
  suite の source field ではないことを Lean 上で示す。
- 未実装箇所は `non-conclusion` と呼ばず、`AATImplementationFrontier` の concrete task として書く。
- docs は suite field、Lean theorem、proof obligation の対応を反映する。docs だけで完了 claim を増やさない。

### 13.4 サブエージェント並列化の手順

並列化は `AATCompleteFormalization` skeleton が main に入ってから行う。
先に skeleton を固定しない場合、各サブエージェントが別々の `Generated*` surface や bridge を増やし、
統合時に AAT の claim set が分裂する。

手順:

1. 単一エージェントで `AATCompleteFormalization` skeleton を作る。
2. skeleton PR を merge し、`main` を同期する。
3. suite field ごとに sub-issue / work package を切る。
4. 各サブエージェントは別 worktree / 別 branch で、割り当てられた field だけを埋める。
5. core world 型、suite field 名、source/downstream 境界を変える必要がある場合は、
   個別エージェントではなく統合エージェントが先に coordination PR を作る。
6. 各 work package は `lake build` と、必要に応じて対象 tool test を通してから PR 化する。
7. 統合エージェントは conflict と docs synchronization を処理し、suite の未充足 field を減らす。

サブエージェントへ渡す work package には、必ず次を含める。

```text
target suite field
allowed files
forbidden files
existing theorem entrypoints
required new theorem / example names
verification command
docs synchronization target
```

### 13.5 並列化してよい領域

次は suite skeleton が固定された後に並列化しやすい。

- generated Signature / static structural core
- generated flatness / curvature
- generated path / homotopy / diagram / non-fillability
- generated feature extension / obstruction / extension formula
- generated operation / repair / synthesis
- generated analytic representation / obstruction valuation
- generated SFT / ArchSig / FieldSig handoff
- theorem package classification audit
- docs / theorem index / proof obligation synchronization

### 13.6 並列化してはいけない領域

次は coordination PR で先に固定する。

- `AtomGeneratedAATWorld` の型
- `AATTheoremSuite` の field 名と依存関係
- `AATImplementationFrontier` の status vocabulary
- `GeneratedArchitectureObject` / `GeneratedArchitectureLawModel` の基本 API
- source-of-truth と downstream representation library の分離規則

### 13.7 第 1 coordination PR の完了条件

第 1 coordination PR は、完全形式化を完了する PR ではない。完全形式化を並列で進められるようにする
coordination PR である。

完了条件:

- `Formal/Arch/AAT/CompleteFormalization.lean` が存在する。
- `AtomGeneratedAATWorld` と `AATTheoremSuite` の skeleton が存在する。
- 主要 theorem family が suite field として列挙されている。
- 既存の generated theorem package のうち、少なくとも Signature / generated law model / classification registry が
  suite field に接続されている。
- 未充足 field が `AATImplementationFrontier` として列挙されている。
- downstream representation library と source-of-truth field が混同されていない。
- `lake build` が通る。

この PR が入った後、suite field ごとにサブエージェントを投入する。
