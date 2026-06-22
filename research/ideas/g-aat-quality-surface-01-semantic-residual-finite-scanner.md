---
status: picked
goal: G-aat-quality-surface-01
exploration_role: computability / scanner / genius-support
candidate_type: genius-support / finite-scanner / transport-diagnostic
capability_category: semantic-obstruction / computability / transport-naturality / repair-coherence / quality-surface
expected_base_score: 78
expected_evidence_multiplier: 2.0
expected_final_score: 156
evidence_stage: proved-in-research
rival_advantage: A finite supplied residual order can return a proof-carrying missed residual or unsupported transport residual certificate, rather than only reporting a component-level or dashboard row failure.
origin: cycle-86
tags: [quality-surface, semantic-repair, residual-scanner, transport-diagnostic, computability, genius-support]
created: 2026-06-22
cycle: 86
lean: proved-in-research
---

# Semantic residual finite scanner

## 主張

finite supplied order と decidability に相対化すれば、semantic repair closure の失敗を executable scanner で証明付き certificate に落とせる。
source support が closed で、scan order が source-supported residuals を覆うなら、`firstMissedSemanticResidual? = none` は target semantic repair closure と同値である。
`some residual` が返ると、Cycle 84 の `MissedSemanticResidual` と、same component projection の下での `ResidualAliasGap` が得られる。

さらに Cycle 85 の transport kernel に対して、target residual order 上の `firstUnsupportedTargetResidual?` を定義する。
complete target residual order の下では、`none` は `TargetResidualSupportedBySource` と同値であり、selected `obligationAliasTransport` は `repairFrontierObligation` を unsupported target residual として返す。

## 候補種別

`genius-support` / `finite-scanner` / `transport-diagnostic`

## 依拠

- Cycle 84: explicit missed residual と alias gap の normal form。
- Cycle 85: supported target residual lift と residual support transport。
- 既存 scan 系: ordered scan / first missed branch / prefix-minimal selected residual scanner。

## 非自明性

bare `Not (SemanticRepairClosed ...)` から witness を取り出すのではなく、finite supplied order、decidability、coverage hypothesis をすべて明示する。
これにより、constructive witness extraction の claim boundary を守りながら、semantic residual obstruction を finite diagnostic interface に変換できる。
transport scanner は component-preserving alias transport が落とす target residual を executable certificate として返す。

## 数学的興味

`firstMissedSemanticResidual?` は source-closed repair closure の finite decision surface である。
`firstUnsupportedTargetResidual?` は Cycle 85 の supported-lift criterion の finite decision surface である。
両者は、finite semantic repair-gluing obstruction theorem に必要な「residual obstruction を certificate として返す selector」を提供する。

## GOAL への前進

open genius target `Semantic repair-gluing obstruction theorem for finite atom-supported quality atlases` に対し、
semantic residual obstruction を finite scanner certificate として固定した。
これは 1000 点 unlock ではなく、finite atlas / cover / transport に相対化した computability-obstruction support node である。

## ライバルに対する有効性

ADL、dashboard、component-preserving migration、AI review summary は first failing component row を出せる。
しかし semantic residual scanner は、その row の背後にある actual residual atom と transport unsupported residual を証明付き witness として返す。
component row ではなく residual atom identity を certificate 化する点が差分である。

## SCORE 見込み

- `score_reason`: Cycle 84/85 の residual identity / transport lift criteria を finite executable scanner に落とし、selected alias transport failure を diagnostic certificate として返す。
- `dullness_risk`: scan recursion 自体は既存 scan 系に近い。価値は semantic residual / transport-lift criteria への接続と selected transport witness にある。
- `proof_or_evidence_plan`: `SemanticResidualFiniteScanner.lean` で finite list coverage、none iff closure / supported-lift criterion、some witness、selected refined semantic witness、selected transport witness を証明する。

## CS / SWE への帰結

quality surface は、semantic repair closure の failure を finite diagnostic result として返せる。
component-level green / red ではなく、missed residual atom または unsupported transported residual atom を返すことで、repair target と transport failure の責務境界を明確化する。

## 証明・根拠

Lean 証拠は `Formal/AG/Research/QualitySurface/SemanticResidualFiniteScanner.lean` に固定した。

- `ListedSourceSemanticResidualsComplete`
- `ListedSourceSemanticResidualsClosed`
- `firstMissedSemanticResidual?`
- `firstMissedSemanticResidual?_some_mem`
- `firstMissedSemanticResidual?_some_missed`
- `firstMissedSemanticResidual?_some_missedSemanticResidual`
- `firstMissedSemanticResidual?_none_iff_listedClosed`
- `firstMissedSemanticResidual?_none_iff_target_semanticRepairClosed`
- `firstMissedSemanticResidual?_some_aliasGap_of_sameComponentProjection`
- `TransportSupportedTarget`
- `ListedTargetSemanticResidualsComplete`
- `ListedTargetResidualsSupported`
- `firstUnsupportedTargetResidual?`
- `firstUnsupportedTargetResidual?_some_mem`
- `firstUnsupportedTargetResidual?_some_missed`
- `firstUnsupportedTargetResidual?_some_missedTargetResidualTransport`
- `firstUnsupportedTargetResidual?_none_iff_listedSupported`
- `firstUnsupportedTargetResidual?_none_iff_targetResidualSupported`
- `selectedSemanticResidualScanOrder`
- `selectedSemanticResidualScanOrder_complete`
- `selectedSemanticTargetResidualScanOrder_complete`
- `selected_firstMissedSemanticResidual`
- `selected_firstMissedSemanticResidual_witness`
- `selected_firstMissedSemanticResidual_none_iff_surfaceClosure`
- `selected_firstMissedSemanticResidual_aliasGap`
- `selected_firstUnsupportedTargetResidual`
- `selected_firstUnsupportedTargetResidual_missedTransport`
- `selected_firstUnsupportedTargetResidual_none_iff_supportedLift`
- `selected_firstUnsupportedTargetResidual_obstructs_surfaceClosure`
- `semanticResidualFiniteScanner_package`

G3 初期実績:

- `lake env lean Formal/AG/Research/QualitySurface/SemanticResidualFiniteScanner.lean`: pass。
- `lake build Formal.AG.Research.QualitySurface.SemanticResidualFiniteScanner`: pass。
- `lake build FormalAGResearch`: pass。
- `lake build`: pass。既存の `Formal/Arch/Extension/FeatureExtensionExamples.lean` linter warning のみ。
- axiom probe: scanner theorem / selected witness / package declarations use standard `propext` only。`sorryAx`、custom axiom、`Classical.choice`、`unsafe` はない。
- `git diff --check`: pass。
- hidden / bidirectional Unicode scan: pass。
- local path scan: pass。

## 審判メモ

- G1 theorem-candidate review: finite scanner は accept-with-narrowing。coverage なしの `none ↔ closure` は過大。expected final は 130-140 程度。
- G1 boundary review: bare negated closure から unconditional witness は reject。finite supplied order、complete list、decidability、source-closedness を明示すれば safe。
- G1 repo-fit review: finite scanner 単独は base 65 見込み。indexed residual support transport の方が高得点だが、transport scanner を入れるなら Cycle 85 からの computable diagnostic node として有効。
- G1 genius-support review: finite residual scanner は 1000 点 unlock ではなく、finite repair-gluing obstruction theorem への computability-obstruction support node。
- G2 rigor: accept / base 76 / genius no。finite supplied order、completeness、decidability 前提が明示され、bare negated closure からの witness overclaim はない。
- G2 research value: accept / base 78 / genius no。Cycle 84/85 を complete finite order 下の proof-carrying diagnostic へ落とすが、新 obstruction 原理ではない。
- G2 repo integration: accept / base 78 / genius no。protected docs / `research/GOALS.md` / report SCORE ledger 変更なし、leakage なし。
- G2 rival comparison: accept / base 78 / genius no。component row / summary を actual residual atom と unsupported transported residual certificate に持ち上げる差分あり。
- G4 SCORE 監査: confirm / base 78 / multiplier 2.0 / penalty 0 / final +156。total 11668 -> 11824。genius は support node であり unlock ではない。

## 追加 required fields

- `mathematical_interest`: semantic repair closure / supported-lift criterion を finite residual scanner の `none` / `some` result として特徴づける。
- `goal_advancement`: finite semantic repair-gluing obstruction theorem に必要な residual certificate selector を Lean-proved にする。
- `planned_theorem_names`: `firstMissedSemanticResidual?_none_iff_target_semanticRepairClosed`, `firstUnsupportedTargetResidual?_none_iff_targetResidualSupported`, `semanticResidualFiniteScanner_package`
- `visible_projection`: finite supplied residual order。
- `protected_structure`: actual residual atom, unsupported target residual, source-supported residual coverage, supported source lift。
- `exactness_or_minimality_claim`: supplied finite order と coverage hypothesis に相対化した scanner criterion。canonical global order や global minimality は主張しない。
- `nonfaithfulness_or_failure_mode`: selected component-preserving alias transport returns the obligation atom as an unsupported target residual。
- `previous_cycle_delta`: Cycle 85 の transport naturality kernelを finite diagnostic interface へ落とす。
- `rival_stress_test`: first failing component row cannot substitute for a proof-carrying semantic residual certificate。
- `genius_potential`: support node
- `genius_target`: Semantic repair-gluing obstruction theorem for finite atom-supported quality atlases
- `genius_support_role`: finite certificate selector for residual obstruction / transport lift failure.

## 関連

- `research/ideas/g-aat-quality-surface-01-semantic-residual-transport-naturality.md`
- `research/ideas/g-aat-quality-surface-01-semantic-residual-alias-classification.md`
- `research/ideas/g-aat-quality-surface-01-semantic-residual-component-faithfulness.md`

## 進捗ログ

- 2026-06-22: G1 finite scanner / transport diagnostic candidate として picked。
- 2026-06-22: Lean 証拠を `SemanticResidualFiniteScanner.lean` に固定し、単体 `lake env lean` と module build が通った。
- 2026-06-22: G4 SCORE 監査で base 78 / final +156 に確定した。
