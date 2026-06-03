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

`architectureLawfulFromAAT` 型の bridge field は原則として rewrite target とする。
残す場合は、なぜ生成写像で置き換えられないかを Issue と acceptance test に落とす。

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
