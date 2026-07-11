---
status: picked
goal: G-aat-quality-surface-01
candidate_type: unification / computability
capability_category: obstruction / computability / traceability / certificate-transport / invariance
expected_base_score: 80
expected_evidence_multiplier: 2.0
expected_final_score: 160
evidence_stage: proved-in-research
rival_advantage: ADL / conformance tools can display a failing rule or route, but this candidate extracts the protected source-ref handoff component support and tests whether support, trace, and repair-frontier laws are independent coordinates of the obstruction locus.
origin: cycle-63
tags: [quality-surface, source-ref, handoff, component-support, minimality]
created: 2026-06-21
cycle: 63
lean: research/lean/ResearchLean/AG/QualitySurface/SourceRefHandoffComponentSupport.lean
---

# Source-ref handoff component support bitset and law minimality matrix

## 主張

selected finite `SourceRefHandoffAtlas` に対して、failed `BridgeComponent` の canonical component support

```text
HandoffComponentSupport atlas component :=
  exists loop, loop in atlas.loops and HandoffHolonomySupport loop component
```

を定義する。この support は ordered first selector ではなく、order-independent obstruction locus の
component projection として読む。

さらに、`support` / `trace` / `repairFrontier` の三つの source-ref handoff component law について、
selected finite one-component deletion witness を構成し、任意の 2-of-3 law だけでは
`HandoffObstructionLocusEmpty`、handoff holonomy vanishing、local exactness 下の interaction exactness を
復元できないことを示す。三 component law は selected finite handoff exactness の protected coordinate
basis として独立に必要である。

具体的には次の三 singleton atlas を固定する。

- `supportLawDeletionHandoff`: `trace` と `repairFrontier` law は保持するが、`support` law だけが壊れる。
- `traceLawDeletionHandoff`: `support` と `repairFrontier` law は保持するが、`trace` law だけが壊れる。
- `repairFrontierLawDeletionHandoff`: `support` と `trace` law は保持するが、`repairFrontier` law だけが壊れる。

各 deletion atlas は locally exact な route state を持つが、該当 component の
`HandoffComponentSupport` を持ち、`HandoffObstructionLocusNonempty` と
`Not HandoffAtlasInteractionExact` を満たす。これにより、component support bitset が単なる
`HandoffObstructionPoint` の projection ではなく、2-of-3 projection の非忠実性を検出する finite
minimality matrix になる。

主張は bounded source-ref handoff、selected finite atlas、existing heterogeneous route state、
finite `BridgeComponent` vocabulary に相対化する。global canonical minimality、runtime repair synthesis、
source extraction completeness、ArchMap correctness、arbitrary route enumeration、実コード全体の品質判定は主張しない。

## 候補種別

`unification / computability`

## 依拠

- Cycle 59: source-ref handoff derived bridge certificate theorem
- Cycle 60: source-ref handoff holonomy correspondence
- Cycle 61: order-independent source-ref handoff obstruction locus
- Cycle 62: repair/transport commutator bridge for handoff obstruction loci

## 非自明性

Cycle 61 は failed `(loop, component)` point の locus を主対象にしたが、どの component law が壊れているかを
finite support bitset として読む層はまだない。Cycle 59 には trace-token failure witness があり、Cycle 62 には
repair-frontier / trace point があるが、`support` / `trace` / `repairFrontier` の三 component law が
selected finite exactness に対して独立に必要であることは matrix として固定されていない。

単に `BridgeComponent` を cases するだけなら価値はない。本候補の非自明性は、component support empty criterion、
same-locus preservation、三つの one-component deletion witness、2-of-3 nonfaithfulness、local exactness 下の
interaction exactness failure を同じ theorem package に入れる点にある。

## 数学的興味

obstruction locus の非空性は存在論的な情報である。component support bitset はそれを有限の coordinate support に落とし、
どの protected law が exactness を支えているかを示す。これは Quality Surface の obstruction を単なる
failure flag ではなく、component-indexed support geometry として読むための小さな不変量である。

## GOAL への前進

source-ref handoff obstruction locus を、traceability、certificate transport、obstruction、computability の
共通 finite invariant として精密化する。これにより、後続の component support hitting theorem や
finite holonomy-obstruction correspondence theorem program に必要な component-level support object が得られる。

## ライバルに対する有効性

ADL、architecture conformance checker、metric dashboard は failing route、failing rule、violation count を表示できる。
しかし、それらは source-ref handoff の support / trace / repair-frontier law を protected coordinate basis として分解し、
ordered first display と component support invariant の差、2-of-3 green projection の非忠実性、local exactness 下の
interaction exactness failure を同一 theorem package として示さない。

## SCORE 見込み

- `score_reason`: component support bitset と three-law minimality matrix が両方通れば、Cycle 61 の locus と Cycle 62 の repair/transport bridge を、計算可能な component support invariant へ進めるため strict base 80 を見込む。
- `dullness_risk`: `BridgeComponent` の三 Bool を列挙するだけなら reject。support bitset の empty / nonempty criterion、same-locus preservation、support / trace / repairFrontier 各 one-component deletion witness、2-of-3 nonfaithfulness、local exactness 下の exactness failure が必要。
- `proof_or_evidence_plan`: Lean で `HandoffComponentSupport`、`handoffComponentSupport_nonempty_iff_locusNonempty`、`handoffComponentSupport_empty_iff_locusEmpty`、`sameHandoffObstructionLocus_preserves_componentSupport`、support / trace / repair-frontier deletion cells、`sourceRefHandoffComponentSupport_package` を証明する。

## CS / SWE への帰結

UI や dashboard 上の first failure 表示や violation count だけでは、どの protected component law が修復・説明・handoff の対象かが失われる。
component support bitset は、source-ref handoff の failed law を component coordinate として保持し、
report が「trace だけの失敗」「repair-frontier だけの失敗」「support だけの失敗」を区別すべき理由を与える。

## 証明・根拠計画

Lean file: `research/lean/ResearchLean/AG/QualitySurface/SourceRefHandoffComponentSupport.lean`

証明済み declaration:

- `HandoffComponentSupport`
- `HandoffComponentSupportEmpty`
- `HandoffComponentSupportNonempty`
- `handoffComponentSupport_nonempty_iff_locusNonempty`
- `handoffComponentSupport_empty_iff_locusEmpty`
- `handoffComponentSupport_empty_iff_holonomyVanishes`
- `sameHandoffObstructionLocus_preserves_componentSupport`
- `componentSupportAtlas_localExact`
- `supportLawDeletionHandoff`
- `traceLawDeletionHandoff`
- `repairFrontierLawDeletionHandoff`
- `supportLawDeletion_twoOfThreeLaws`
- `traceLawDeletion_twoOfThreeLaws`
- `repairFrontierLawDeletion_twoOfThreeLaws`
- `supportLawDeletion_componentSupport`
- `traceLawDeletion_componentSupport`
- `repairFrontierLawDeletion_componentSupport`
- `supportLawDeletion_handoffLocusNonempty`
- `traceLawDeletion_handoffLocusNonempty`
- `repairFrontierLawDeletion_handoffLocusNonempty`
- `supportLawDeletion_not_interactionExact`
- `traceLawDeletion_not_interactionExact`
- `repairFrontierLawDeletion_not_interactionExact`
- `sourceRefHandoffComponentSupport_package`

証明方針:

1. `HandoffComponentSupport atlas component` を `exists loop, loop in atlas.loops and HandoffHolonomySupport loop component` として定義する。
2. `HandoffObstructionLocusNonempty atlas` と `exists component, HandoffComponentSupport atlas component` の同値を示す。
3. component support が空であることと `HandoffObstructionLocusEmpty atlas`、handoff holonomy vanishing が同値であることを示す。
4. `SameHandoffObstructionLocus` が component support を保存することを示す。
5. `support` / `trace` / `repairFrontier` の各 component だけが壊れる selected handoff witness を構成する。
6. 各 deletion witness が残りの 2 law を保持することを個別 theorem として示す。
7. 各 witness の singleton atlas が local exactness を保ちながら nonempty handoff locus と interaction exactness failure を持つことを示す。

G2-A revise への対応:

- `canonical` は global canonical object ではなく、selected finite atlas の order-independent locus projection としてだけ使う。
- SCORE の核を component support projection ではなく、三つの one-component deletion witness と 2-of-3 nonfaithfulness matrix に置く。
- G3 に進む前に、予定 Lean statement と候補カード上で support-only / trace-only / repair-frontier-only deletion witness を明示した。

## G2 revise response

- G2-A 厳密性: initial revise、base 70 provisional、genius no。component support projection だけでは既存 locus theorem の射影に近く、support-only / trace-only / repair-frontier-only deletion witness と 2-of-3 nonfaithfulness matrix を statement レベルで固定する必要がある。
- G2-A 再審判: accept、base 80、genius no。三つの concrete singleton deletion witness、残り 2 law の保持、local exactness 下でも interaction exactness を復元できないことをカードに明示したため、厳密性と boundary fidelity は満たす。
- G2-B 研究価値: accept、base 82、genius no。Cycle 59-62 の source-ref bridge、holonomy、order-independent locus、repair/transport commutator を component support と law independence の theorem package に圧縮すると評価。
- G2-C repo 全体価値: accept、base 82、genius no。AAT/Lean/paper seed への価値が強く、将来の Tooling / Website drill-down 表示にも接続するが、source-ref handoff 系の細分化リスクがあると評価。
- G2-D rival 比較: accept、base 82、genius no。ADL / conformance checker の failure display を、protected component law support と 2-of-3 nonfaithfulness theorem へ持ち上げる差分があると評価。
- 対応: expected base を strict base 80 に下げ、G3 の必須証拠を `HandoffComponentSupport` criterion、same-locus preservation、三 deletion witness、local exactness 下の exactness failure、package theoremに絞った。

## G3 evidence

- Lean file: `research/lean/ResearchLean/AG/QualitySurface/SourceRefHandoffComponentSupport.lean`
- aggregate import: `research/lean/ResearchLean.lean`
- local checks:
  - `lake env lean research/lean/ResearchLean/AG/QualitySurface/SourceRefHandoffComponentSupport.lean`: pass
  - `lake env lean research/lean/ResearchLean.lean`: pass
  - `lake build ResearchLean`: pass
  - `lake build`: pass。既存 `Formal/Arch/Extension/FeatureExtensionExamples.lean` の linter warning のみ。
  - `lake env lean .tmp/source_ref_handoff_component_support_axioms.lean`: pass
  - target `axiom|admit|sorry|unsafe` scan: no matches

G3 公理検査: pass。`sorryAx`、custom axiom、`axiom`、`admit`、`sorry`、`unsafe` はない。
`HandoffComponentSupport`、nonempty / empty criterion、same-locus component support preservation、
support deletion / repair-frontier deletion の two-of-three law は axiom-free。
holonomy vanishing criterion、trace deletion、component support witnesses、locus nonempty witnesses は標準 `propext` を継承する。
local exactness と interaction-exactness failure、package theorem は既存 local exactness infrastructure 由来の
標準 `propext` / `Quot.sound` を継承する。これらは finite component witness を隠していない。

G3 Lean 形式化品質監査: pass。`HandoffComponentSupport` は ordered first selector ではなく
order-independent locus の component projection として定義され、same-locus preservation、empty/nonempty criterion、
holonomy vanishing criterion を持つ。三つの deletion witness は arbitrary Bool flip ではなく、
`HandoffSupportCompatible`、`HandoffTraceCompatible`、`HandoffRepairFrontierCompatible` の actual compatibility law failure として証明される。
各 witness は残り 2 law を保持し、singleton atlas が local exactness を満たしつつ
`HandoffObstructionLocusNonempty` と `Not HandoffAtlasInteractionExact` を持つ。

## G3.5 sync notes

G4 後の report には、Cycle 63 section として次の declaration 名を載せる。

- `HandoffComponentSupport`
- `handoffComponentSupport_nonempty_iff_locusNonempty`
- `handoffComponentSupport_empty_iff_locusEmpty`
- `handoffComponentSupport_empty_iff_holonomyVanishes`
- `sameHandoffObstructionLocus_preserves_componentSupport`
- `supportLawDeletion_twoOfThreeLaws`
- `traceLawDeletion_twoOfThreeLaws`
- `repairFrontierLawDeletion_twoOfThreeLaws`
- `supportLawDeletion_componentSupport`
- `traceLawDeletion_componentSupport`
- `repairFrontierLawDeletion_componentSupport`
- `supportLawDeletion_handoffLocusNonempty`
- `traceLawDeletion_handoffLocusNonempty`
- `repairFrontierLawDeletion_handoffLocusNonempty`
- `supportLawDeletion_not_interactionExact`
- `traceLawDeletion_not_interactionExact`
- `repairFrontierLawDeletion_not_interactionExact`
- `sourceRefHandoffComponentSupport_package`

G3.5 初回監査で指摘された `*_componentSupport` declaration の一覧漏れは修正済み。
G4 confirm 後に、report の total、category scores、proved-in-research count、Cycle 63 section、
Next Frontier を同時に更新済み。

## G4 SCORE audit

```text
score_verdict: confirm
base_score: 80
evidence_multiplier: 2.0
penalty: 0
final_score: 160
category: obstruction / computability / traceability / certificate-transport / invariance
genius_verdict: downgrade-to-normal
```

G4 は、G2 の strict base 80 と Lean-proved evidence multiplier x2.0 を confirm した。
三 deletion witness、残り 2 law 保持、component support 非空、local exactness、
not interaction exactness が実際に Lean evidence として固定されているため SCORE は維持する。
一方で G2 四審判はいずれも `genius_eligibility: no` であり、1000 点級の `genius unlock` ではない。

GOAL delta: source-ref handoff obstruction locus を component-indexed support invariant に持ち上げ、
support / trace / repair-frontier の三 law が selected finite exactness の独立座標であることを固定した。

Rival delta: ADL / conformance checker の failure display では保持しにくい protected component support、
2-of-3 nonfaithfulness、local-exact だが interaction-exact でない deletion witness を示した。

Report sync: `research/reports/G-aat-quality-surface-01.md` は total 8326、proved artifacts 63、
Cycle 63 section、Next Frontier の残り 1674 SCORE として更新した。

## G1 候補 pool

四つの独立候補生成サブエージェントは、重複を除いて次を主要候補として出した。

- Source-ref handoff bridge law minimality matrix
- Canonical component support bitset for handoff obstruction loci
- Component support hitting theorem for handoff repairs
- Handoff atlas refinement invariance theorem
- Finite holonomy-obstruction correspondence theorem program / genius-target seed

三体が component support bitset / minimality matrix を第一または高順位候補として出し、二体が hitting theorem を
後続の高 SCORE frontier として出した。hitting theorem は component repair semantics まで含むため、
本 cycle では bitset と three-law minimality matrix に絞る。

## Genius potential

この候補単体は `genius unlock` ではない。
ただし、finite holonomy-obstruction correspondence theorem program を将来 `genius-target` として立てる場合、
component support / minimality support node になりうる。1000 点級の unlock は、route atlas、source-ref handoff atlas、
repair/transport commutator、component support、refinement、repair hitting を同一 finite obstruction calculus として統合し、
G2/G3/G4 を通った場合にのみ別途扱う。

## 関連

- `research/ideas/g-aat-quality-surface-01-source-ref-handoff-derived-bridge.md`
- `research/ideas/g-aat-quality-surface-01-source-ref-handoff-holonomy-correspondence.md`
- `research/ideas/g-aat-quality-surface-01-source-ref-handoff-obstruction-locus.md`
- `research/ideas/g-aat-quality-surface-01-repair-transport-handoff-obstruction-bridge.md`

## 進捗ログ

- 2026-06-21: cycle 63 G1 候補 pool から G2 審判対象として作成。
- 2026-06-21: G2-A revise を受け、three one-component deletion witness と 2-of-3 nonfaithfulness matrix を statement レベルで明示。
- 2026-06-21: Lean proof を固定し、G3 公理検査と形式化品質監査を通過。
- 2026-06-21: G4 SCORE 監査で +160 を confirm。report を total 8326 / proved artifacts 63 へ同期。
