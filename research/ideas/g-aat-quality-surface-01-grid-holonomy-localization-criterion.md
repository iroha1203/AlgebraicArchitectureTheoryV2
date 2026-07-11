---
status: picked
goal: G-aat-quality-surface-01
candidate_type: closure
capability_category: profile-curvature/certificate-transport/invariance/computability/obstruction
expected_base_score: 60
expected_evidence_multiplier: 2.0
expected_final_score: 120
evidence_stage: proved-in-research
origin: G-aat-quality-surface-01-cycle20
tags:
  - grid-holonomy
  - finite-square
  - localization
created: 2026-06-20
---

# Grid-level flatness and holonomy localization criterion

## 主張

有限 profile grid 上の selected two-cell decomposition で endpoint holonomy が protected invariant に
現れるなら、cellwise visible-flatness と shared-boundary compatibility の下で、その holonomy は
少なくとも一つの selected elementary square の reading curvature として局所化できる。逆に、
selected decomposition の各 cell が protected-flat であり、shared boundary が protected invariant を
保って貼り合わされていれば、endpoint protected holonomy は消える。

Cycle 10 の `ProfileGridHolonomy` は一つの 3x3 witness を固定し、Cycle 12 は単一 finite-square
criterion を固定した。この候補は、selected two-cell path decomposition に限って、cellwise
flatness と endpoint holonomy localization を Lean で接続する。

主張は supplied finite grid、selected two-cell decomposition、selected visible reading、selected
protected invariant、cellwise visible-flatness、shared-boundary protected compatibility に相対化する。
任意 grid の global flatness theorem、任意 path family の pasting theorem、canonical profile transport、
source extraction completeness、ArchMap correctness、実コード全体の traceability は結論しない。

## 候補種別

`closure`

## 依拠

- `research/lean/ResearchLean/QualitySurface/ProfileGridHolonomy.lean`
- `research/lean/ResearchLean/QualitySurface/FiniteSquareCriterion.lean`
- `research/lean/ResearchLean/QualitySurface/TupleProtectedDataSquareCriterion.lean`
- `gridHolonomy_visibleAgreement`
- `localized_curvature_cell`
- `same_grid_surface_but_path_ordered_frontier_diff`
- `finiteSquare_curvature_of_visible_agreement_protected_discrepancy`

## 非自明性

Cycle 10 は localized upper-right cell の具体 witness、Cycle 12 は一つの endpoint pair に対する
generic criterion だった。この候補は endpoint-level holonomy を cell-level witness に戻し、selected
two-cell decomposition で all-cell flatness が endpoint holonomy を消すことを示す。

単なる Cycle 10 の再掲にしないため、cell endpoint pair、cell reading、shared-boundary compatibility、
flatness-to-no-endpoint-holonomy、endpoint-holonomy-to-curved-cell の両方向を theorem package として固定する。

## 数学的興味

holonomy を「二つの path endpoint が違う」という現象から、「どの elementary cell が obstruction を
支えるか」という局所化問題へ移す。これは Quality Surface の curvature を計算可能な cell-level
obstruction として扱うための基礎になる。

## GOAL への前進

profile-curvature / certificate-transport / invariance / computability / obstruction を接続し、
grid-level flatness / holonomy criterion frontier を前進させる。

## SCORE 見込み

- `score_reason`: G2-B/C は base 70 を認めたが、G2-A が selected decomposition の shared-boundary compatibility と cellwise visible-flatness を required evidence として要求したため、revised candidate は base 60 / final 120 に下げる。
- `dullness_risk`: medium-high。Cycle 10 witness の再包装に落ちないよう、cellwise flatness sufficient condition と holonomy localization を明示する。
- `proof_or_evidence_plan`: `GridHolonomyLocalization.lean` で selected cell reading、cell pair、shared-boundary compatibility、all-cell flatness predicate、endpoint protected-flatness theorem、curved-cell localization theorem、theorem package を証明済み。

## CS / SWE への帰結

grid endpoint の quality reading が同じでも protected data が違う場合、その差分を selected cell に
戻せる。これは loss-aware visualization や repair planning で「どこを drill down すべきか」を
数学的に扱う土台になる。ただし supplied finite grid の claim であり、tooling completeness ではない。

## 証明・根拠

Lean proof は `research/lean/ResearchLean/QualitySurface/GridHolonomyLocalization.lean` に閉じた。
`research/lean/ResearchLean.lean` はこの Research evidence file を import する。

主要 theorem / declaration:

- `GridCellEndpointPair`
- `gridUpperRightCellPair`
- `gridTraceCellReading`
- `gridRepairCellReading`
- `SelectedTwoCellDecomposition`
- `SharedBoundaryProtectedCompatible`
- `gridUpperRightCell_visibleFlat`
- `gridUpperRightCell_repair_visibleFlat`
- `gridUpperRightCell_traceDiscrepancy`
- `gridUpperRightCell_repairDiscrepancy`
- `AllSelectedCellsProtectedFlat`
- `AllSelectedCellsVisibleFlat`
- `endpointProtectedFlat_of_allSelectedCellsFlat`
- `curvedCell_of_endpointTraceHolonomy`
- `curvedCell_of_endpointRepairHolonomy`
- `gridUpperRightCell_instantiates_traceCriterion`
- `gridUpperRightCell_instantiates_repairCriterion`
- `gridHolonomy_localization_package`

固定された内容:

- `SharedBoundaryProtectedCompatible` は common prefix と branch endpoint 手前の trace-complete /
  no-database-repair-frontier を明示する。
- `SelectedTwoCellDecomposition` は shared prefix、二つの branch vertex、upper-right endpoint pair、
  shared-boundary protected compatibility を束ねる。
- `AllSelectedCellsVisibleFlat` と `AllSelectedCellsProtectedFlat` は selected decomposition に相対化した
  visible-flat / protected-flat 条件である。
- `endpointProtectedFlat_of_allSelectedCellsFlat` は selected cells が protected-flat なら endpoint
  protected holonomy が消える sufficient condition を固定する。
- `curvedCell_of_endpointTraceHolonomy` と `curvedCell_of_endpointRepairHolonomy` は、cellwise
  visible-flatness と endpoint protected holonomy から selected upper-right cell の
  `ReadingCurved` を返す。
- `gridUpperRightCell_instantiates_traceCriterion` と `gridUpperRightCell_instantiates_repairCriterion`
  は Cycle 10 の concrete grid witness を Cycle 12 の finite-square criterion に接続する。

検証:

- `lake env lean research/lean/ResearchLean/QualitySurface/GridHolonomyLocalization.lean`: pass。
- `lake build ResearchLean`: pass。
- `.tmp/grid_holonomy_localization_axioms.lean` の `#print axioms`: listed declarations are all
  `does not depend on any axioms`。`sorryAx`、`propext`、`Classical.choice`、`Quot.sound` は出ていない。
- G3 公理検査: pass。
- G3 Lean 形式化品質監査: pass。`endpointProtectedFlat_of_allSelectedCellsFlat` は package 内の
  sufficient-condition 成分であり、非自明性は concrete discrepancy と endpoint-holonomy localization
  theorem 側で固定されている。

## 審判メモ

- 厳密性: G2-A は revise、base 60。endpoint holonomy から reading-curved cell を出すには cellwise visible-flatness と shared-boundary protected compatibility が必要。単なる `localized_curvature_cell` 再掲を避けること。
- 厳密性再審判: G2-A は revised card を accept、base 60。two-cell decomposition package と
  endpoint-to-cell localization / all-cell-flatness-to-endpoint-flatness を Lean で弱めずに出すことを required evidence とした。
- 研究価値: G2-B は accept、base 70。selected two-cell decomposition への相対化により完全 global theorem ではないが、grid-level frontier に直接効くと判定。
- repo 全体価値: G2-C は accept、base 70。Lean / paper seed として価値は高いが、selected decomposition に閉じるため base 80 は過大。

## 関連

- `research/ideas/g-aat-quality-surface-01-grid-holonomy.md`
- `research/ideas/g-aat-quality-surface-01-finite-square-protected-criterion.md`
- `research/ideas/g-aat-quality-surface-01-tuple-protected-data-square-criterion.md`
- `research/reports/G-aat-quality-surface-01.md`

## 進捗ログ

- 2026-06-20: Cycle 20 candidate card 作成。
- 2026-06-20: G2-A revise を反映し、cellwise visible-flatness と shared-boundary protected compatibility を required evidence に追加し、base 60 / final 120 に下げた。
- 2026-06-20: G2-A 再審判 accept。`GridHolonomyLocalization.lean` を追加し、単体 Lean、`ResearchLean`、axiom harness、G3 公理検査、G3 Lean 形式化品質監査を通した。
