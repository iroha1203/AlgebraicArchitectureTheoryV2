---
status: picked
goal: G-aat-quality-surface-01
candidate_type: orientation / unification / computability
capability_category: obstruction / certificate-transport / traceability / computability / invariance / quality-surface
expected_base_score: 80
expected_evidence_multiplier: 2.0
expected_final_score: 160
evidence_stage: proved-in-research
rival_advantage: ADL / architecture conformance tools can display an ordered first failure, but this candidate separates that report-facing witness from the order-independent source-ref handoff obstruction locus.
origin: cycle-61
tags: [quality-surface, source-ref, handoff, obstruction, invariance, holonomy]
created: 2026-06-21
cycle: 61
lean: Formal/AG/Research/QualitySurface/SourceRefHandoffObstructionLocus.lean
---

# Order-independent source-ref handoff obstruction locus for finite atlases

## 主張

selected finite source-ref handoff atlas に対して、supplied order に依存する
`firstHandoffObstructingLoop?` ではなく、failed `(loop, component)` の
`HandoffObstructionLocus` を定義する。
この locus は source-ref handoff law failure、derived bridge obstruction、
loop holonomy support、atlas interaction exactness failure を読む order-independent protected layer である。

local exactness の下で、locus が空であることは handoff holonomy vanishing および
atlas interaction exactness と同値になる。さらに、ordered first selector が返す witness は
この locus の report-facing projection として sound / complete であり、membership-equivalent atlas は同じ
obstruction locus と exactness verdict を持つ。

この主張は selected finite atlas、bounded `SourceRefHandoff`、finite packet / endpoint tuple、
supplied loop membership、existing heterogeneous route state に相対化する。source extraction completeness、
ArchMap correctness、runtime repair synthesis、arbitrary route enumeration、whole-codebase quality は主張しない。

## 候補種別

`orientation / unification / computability`

## 依拠

- Cycle 56: ordered first-failing selector
- Cycle 58: finite route holonomy obstruction support theorem
- Cycle 59: source-ref handoff derived bridge certificate theorem
- Cycle 60: source-ref handoff holonomy correspondence for finite route atlases

## 非自明性

Cycle 60 は ordered selector が返す loop から source-ref failure、derived bridge obstruction、
holonomy support、interaction exactness obstruction を取り出した。
本候補は、その `first` 表示を成果の中心にせず、order-independent な failed `(loop, component)` locus を
protected structure として導入する。これにより、report の順序と canonical obstruction geometry を分離する。

## 数学的興味

closed-route holonomy obstruction は、最初に表示された witness ではなく、finite atlas 上の support locus として読む方が自然である。
同じ locus から ordered first witness、component support、interaction exactness failure が射影されるなら、
Quality Surface は dashboard 的な first failure 表示ではなく、finite certificate geometry として見える。

## GOAL への前進

obstruction、certificate transport、traceability、computability、invariance を、
source-ref handoff atlas 上の order-independent finite locus として統合する。
Cycle 60 の supplied-order boundary を外し、finite holonomy-obstruction correspondence theorem program の
normal support cycle として前進させる。

## ライバルに対する有効性

ADL、architecture conformance checker、metric dashboard は、選ばれた順序で failing route や first violation を表示できる。
この候補は、その表示を faithful な本体とは扱わず、order-independent source-ref handoff obstruction locus への
projection として位置づける。rival が報告順序に依存してしまう箇所を、AAT 側では finite protected locus として分離する。

## SCORE 見込み

- `score_reason`: Cycle 60 の handoff-holonomy correspondence を、ordered first selector から invariant finite locus へ上げる。G2 厳密性審判の strict base 80 を G4 入力値とする。
- `dullness_risk`: `firstHandoffObstructingLoop?` の soundness を言い換えるだけなら reject。locus empty / nonempty criterion、local exactness 下の interaction exactness criterion、membership-equivalent atlas preservation、first selector の projection 性を同時に固定する。
- `proof_or_evidence_plan`: Lean で `HandoffObstructionPoint`、`HandoffObstructionLocusNonempty`、`HandoffObstructionLocusEmpty`、`SameHandoffObstructionLocus` を定義した。`firstHandoffObstructingLoop?_none_iff_holonomyVanishes`、`firstHandoffObstructingLoop?_some_point`、`handoffObstructionLocus_empty_iff_holonomyVanishes`、`handoffObstructionLocus_nonempty_iff_not_holonomyVanishes`、`handoffAtlas_not_interactionExact_iff_locus_nonempty_of_local`、`sameHandoffObstructionLocus_preserves_*`、`sourceRefHandoffObstructionLocus_package` を証明した。

## CS / SWE への帰結

route dashboard の first failing item は有用な表示であるが、canonical な品質対象ではない。
この候補により、UI / report は ordered first witness を出しつつ、保存すべき本体は order-independent obstruction locus であると区別できる。
ただしこれは supplied finite evidence surface 上の theorem であり、runtime source observation、repair generation、global conformance completeness ではない。

## 証明・根拠

Lean file `Formal/AG/Research/QualitySurface/SourceRefHandoffObstructionLocus.lean` に固定した。
`lake env lean Formal/AG/Research/QualitySurface/SourceRefHandoffObstructionLocus.lean`、
`lake env lean Formal/AG/Research.lean`、`lake build FormalAGResearch`、full `lake build` は通過した。
full build の警告は既存 `Formal/Arch/Extension/FeatureExtensionExamples.lean` の linter 警告のみである。

証明済み declaration は次である。

- `HandoffObstructionPoint`
- `HandoffObstructionLocusNonempty`
- `HandoffObstructionLocusEmpty`
- `SameHandoffObstructionLocus`
- `HandoffObstructionPoint.toFailure`
- `HandoffObstructionPoint.toBridgeObstruction`
- `HandoffObstructionPoint.toLoopHolonomySupport`
- `firstHandoffObstructingLoop?_none_iff_holonomyVanishes`
- `firstHandoffObstructingLoop?_some_iff_locusNonempty`
- `firstHandoffObstructingLoop?_some_point`
- `handoffObstructionLocus_nonempty_iff_not_holonomyVanishes`
- `handoffObstructionLocus_empty_iff_holonomyVanishes`
- `handoffAtlas_not_interactionExact_iff_locus_nonempty_of_local`
- `sameHandoffObstructionLocus_preserves_nonempty`
- `sameHandoffObstructionLocus_preserves_holonomyVanishes`
- `sameHandoffObstructionLocus_preserves_localExact`
- `sameHandoffObstructionLocus_preserves_interactionExact`
- `sameHandoffObstructionLocus_preserves_interactionExact_of_local`
- `mixedSourceRefHandoffAtlas_locusNonempty`
- `alignedSourceRefHandoffAtlas_locusEmpty`
- `mixedSourceRefHandoffAtlas_notExact_iff_locusNonempty`
- `sourceRefHandoffObstructionLocus_package`

`#print axioms` では、`sameHandoffObstructionLocus_preserves_nonempty`、
`sameHandoffObstructionLocus_preserves_holonomyVanishes`、
`sameHandoffObstructionLocus_preserves_localExact`、
`sameHandoffObstructionLocus_preserves_interactionExact` は axiom-free である。
selector projection、empty/nonempty criterion、local exactness criterion は `propext` を使う。
aligned / mixed concrete witness と package は既存 exactness infrastructure 由来の `propext` / `Quot.sound` を継承する。
`sorryAx`、custom axiom、`Classical.choice` はない。
finite witness として標準公理を自動 clean 扱いせずに監査し、`Quot.sound` は今回の locus 定義そのものではなく既存 concrete atlas witness からの伝播として扱う。

## 審判メモ

- G1: 四つの独立候補生成サブエージェントは、order-independent source-ref handoff obstruction locus、three-law minimality matrix、selector nonfaithfulness、component support bitset、repair/transport commutator bridge を主要候補として提示した。order-independent locus は四体すべてに現れ、複数体が最有力候補と判定した。
- G1: repair/transport commutator bridge はより genius target に近いが、型接続のリスクが高く、この cycle では通常高 SCORE support として order-independent locus を picked にする。
- G1: genius unlock はない。finite holonomy-obstruction correspondence theorem program の support cycle として扱う。
- G2 A 厳密性: accept、base 80、genius no。即時系に近いリスクを認めつつ、failed `(loop, component)` locus、empty/nonempty criterion、local exactness 下の interaction exactness criterion、membership-equivalent atlas preservation、first selector sound/complete projection を同時に要求した。
- G2 B 研究価値: accept、base 86、genius no。first failure 表示ではなく finite protected locus から source-ref law failure / derived bridge obstruction / holonomy support / interaction exactness failure を読む方向への前進を評価した。
- G2 C repo 全体価値: accept、base 86、genius no。Tooling / Website では first displayed failure は UI projection であり、本体は locus だと説明できる点を評価した。
- G2 D ライバル比較: accept、base 84、genius no。rival の violation set ではなく、source reference を持つ handoff law failure、bridge obstruction、holonomy support、exactness failure を同じ locus として扱う点を評価した。
- G3 形式化品質監査: 初回は `HandoffObstructionLocusEmpty` が holonomy vanishing の別名になっており、空 locus と holonomy vanishing の同値が `Iff.rfl` に潰れていたため revise。`HandoffObstructionLocusEmpty := Not (HandoffObstructionLocusNonempty atlas)` に修正し、`handoffObstructionLocus_empty_iff_holonomyVanishes` を実証明にした。さらに `firstHandoffObstructingLoop?_some_point` を追加し、selector から locus point への projection を明示した。再監査は pass。
- G3 公理検査: pass。`sorryAx`、custom axiom、`Classical.choice` はなく、標準 `propext` / `Quot.sound` のみ。finite witness としての理由を上記に記録した。
- G4 SCORE 監査: confirm、base 80、evidence multiplier 2.0、penalty 0、final 160、category `obstruction / certificate-transport / traceability / computability / invariance / quality-surface`。G2 四審判は全員 accept かつ genius no であり、strictest base 80 を採用した。`HandoffObstructionLocusEmpty` を true emptiness とし、empty / nonempty criterion、local exactness criterion、same-locus preservation、selector projection を Lean 証拠として固定したため x2.0 を承認した。genius scoring は適用しない。

## 関連

- `research/ideas/g-aat-quality-surface-01-finite-route-holonomy-obstruction-support.md`
- `research/ideas/g-aat-quality-surface-01-source-ref-handoff-derived-bridge.md`
- `research/ideas/g-aat-quality-surface-01-source-ref-handoff-holonomy-correspondence.md`

## 進捗ログ

- 2026-06-21: cycle 61 G1 候補 pool から G2 審判対象として作成。
- 2026-06-21: Lean proof を固定し、空 locus 定義の G3 revise を解消して候補カードを `proved-in-research` に同期。
- 2026-06-21: G4 SCORE 監査で final SCORE 160 を確定。
