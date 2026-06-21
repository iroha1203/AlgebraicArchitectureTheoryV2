---
status: picked
goal: G-aat-quality-surface-01
candidate_type: computability / canonical-certificate
capability_category: computability / obstruction / certificate-transport / traceability / quality-surface
expected_base_score: 70
expected_evidence_multiplier: 2.0
expected_final_score: 140
evidence_stage: proved-in-research
rival_advantage: ADL / conformance tools can report failing route entries, but do not turn a supplied ordered evidence surface into a first-failing-slot certificate theorem tied to family exactness.
origin: cycle-56
tags: [quality-surface, finite-scan, failing-slot, computability]
created: 2026-06-21
cycle: 56
lean: Formal/AG/Research/QualitySurface/OrderedScanFirstFailingSlot.lean
---

# Ordered scan first-failing slot certificate

## 主張

Supplied ordered route-slot list `slots` と staged assignment `assignment` に相対化して、
`firstFailingSlot? assignment slots` を定義する。この ordered scan が `none` を返すことは
listed all-branches condition と同値であり、cover list の下では family source-ref exactness と同値である。
また `some slot` を返す場合、その slot は list 上の failing-slot certificate を与え、
その前方 prefix は all-branches であり、family exactness を阻む。

## 候補種別

`computability` / `closure`

## 依拠

- Cycle 53: `FiniteRouteFamilyExactLocus`
- Cycle 54: `FailingSlotCertificate`
- Cycle 55: `FiniteRouteScan`

## 非自明性

Cycle 55 は boolean scan と listed failing certificate を与えたが、false result からどの certificate を報告するかは固定していなかった。
本候補は supplied order に相対化した first failing slot と prefix exactness を証明対象にし、scan result、certificate、family exactness obstruction を一つの interface に接続する。

## 数学的興味

Quality Surface の failure は単なる truth value ではなく、ordered evidence surface 上で reportable な obstruction certificate として返せる。
これは canonicality を絶対的な最小性ではなく、declared scan order に相対化するため、claim boundary を守りながら計算可能な certificate selection を与える。

## GOAL への前進

`computability` と `obstruction` を進め、finite evidence surface から exactness failure certificate を選ぶ interface を追加する。

## ライバルに対する有効性

ADL / conformance checker は failing component や failing route を表示できるが、declared ordered evidence surface、family exactness theorem、first-failing certificate obstruction を同じ証明対象としては束ねない。

## SCORE 見込み

- `score_reason`: ordered scan が failure certificate selection を固定し、Cycle 55 の open frontier `canonical/minimal failing slot under ordered scans` を claim-boundary 内で進める。G2 厳密性審判は、既存 exactness/certificate lemmas に近い list-recursive refinement であるため base 70 が妥当と判定した。
- `dullness_risk`: absolute canonical / minimal failing slot と言うと過大主張になる。supplied ordered list に相対化し、global minimality は主張しない。
- `proof_or_evidence_plan`: Lean で recursive scanner、none/listed-all-branches equivalence、some-to-certificate、cover-list exactness equivalence、concrete mixed route-slot witness を証明する。

## CS / SWE への帰結

有限 route-family check で false が出たとき、単なる fail flag ではなく ordered scan が返す reportable obstruction certificate を運べる。
ただし ordered list と cover proof は入力 contract であり、任意コードベースの自動列挙や ArchMap completeness は主張しない。

## 証明・根拠の見込み

Lean file `OrderedScanFirstFailingSlot.lean` に置く。
主要 declaration は `firstFailingSlot?_none_iff_listedAllBranches`、
`firstFailingSlot?_failingCertificate`、
`firstFailingSlot?_some_prefixAllBranches`、
`assignmentFamilySourceRefExact_iff_firstFailingSlot?_none`、
`mixedRouteSlot_firstFailingSlot?_secondary`、
`orderedScanFirstFailingSlot_package`。

## 審判メモ

- 厳密性: accept; base 70. order-relative canonicity と prefix exactness は新規だが、Cycle 53-55 の exactness/certificate lemmas に近いため 80 までは上げない。
- 研究価値: accepted; base 80. boolean scan を certificate selection に変え、finite route-family exactness section の reportable interface になる。
- repo 全体価値: accept; base 80. research-to-tooling interface として有効だが、SFT / Website への直接効果は弱い。
- ライバル比較: accept; base 80. ADL-style first failing entry display ではなく、scan result、prefix exactness、certificate、family exactness obstruction を theorem-backed に束ねる。
- genius: not eligible. A/B/D は `genius_eligibility: no`、C は条件付き評価に留まったため、四者 yes を満たさず通常 SCORE として扱う。
- resolved revise: G3 formalization audit が `orderedScanFirstFailingSlot_package` の weak existential certificate conjunct を指摘したため、package theorem を `slot ∈ slots`、`assignment slot ≠ allBranches`、prefix exactness、family exactness obstruction を直接返す形へ強化した。

## 関連

- `research/ideas/g-aat-quality-surface-01-finite-route-scan.md`
- `Formal/AG/Research/QualitySurface/FiniteRouteScan.lean`

## 進捗ログ

- 2026-06-21: cycle 56 candidate picked and Lean evidence added.
