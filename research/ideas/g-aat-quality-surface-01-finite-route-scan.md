---
status: picked
goal: G-aat-quality-surface-01
candidate_type: computable finite scan / closure
capability_category: computability / obstruction / certificate-transport / repair-potential / traceability / quality-surface
expected_base_score: 70
expected_evidence_multiplier: 2.0
expected_final_score: 140
evidence_stage: proved-in-research
rival_advantage: ADL / conformance checker can list failing routes, but this result proves that a supplied covering slot list computes the exactness gate and exposes the same failing certificate interface.
origin: G-aat-quality-surface-01-cycle55
tags: [quality-surface, route-family, finite-scan, computability, failing-slot]
created: 2026-06-21
cycle: 55
lean: proved-in-research
---

# Finite route scan

## 主張

任意の staged route-slot assignment `Slot -> RepairStage` と supplied finite slot list `slots : List Slot` について、`slots` が全 slot を cover するなら、boolean scan `listedAllBranchesScan assignment slots` が `true` であることと family source-ref exactness は同値である。Concrete mixed two-slot assignment では supplied list `[primary, secondary]` が cover し、scan は `false` を返し、secondary slot の failing certificate を露出する。

## 候補種別

`computable finite scan / closure`

## 依拠

- `research/lean/ResearchLean/AG/QualitySurface/FailingSlotCertificate.lean`
- `research/lean/ResearchLean/AG/QualitySurface/FiniteRouteFamilyExactLocus.lean`

## 非自明性

Cycle 53 は exact locus を任意 slot family 上の theorem として固定し、Cycle 54 は failure を certificate object にした。Cycle 55 は supplied finite list が cover する場合に限り、exactness gate を boolean scan で計算できる theorem に変換し、mixed two-slot example で false scan と failing certificate を同時に固定する。

## 数学的興味

Quality Surface の route-family exactness を、抽象的な `∀ slot` 命題から、cover certificate 付きの finite scan へ落とす。これは arbitrary type の自動列挙ではなく、supplied cover list に相対化した computability statement であり、reportable UI / finite evidence surface へ移す最小の型付き橋になる。

## GOAL への前進

この候補は `computability`、`obstruction`、`certificate-transport`、`repair-potential`、`traceability`、`quality-surface` を前進させる。Cycle 54 の open question だった computable finite scan instance を、supplied covering list に相対化して閉じる。

## ライバルに対する有効性

ADL / conformance checker は failing route の一覧や status を表示できるが、cover list が exactness gate を計算すること、false scan が same certificate interface に接続することを theorem としては与えない。

## SCORE 見込み

- `score_reason`: supplied covering finite list、boolean scan true iff family exactness、mixed two-slot false scan、scan-exposed failing certificate を Lean で固定する。Cycle 54 の certificate interface を computable finite surface に接続するが、canonical enumeration や minimal failing slot までは主張しないため base70 とする。
- `dullness_risk`: exact locus theorem を list scan に移しただけに見える危険がある。cover condition、boolean scan theorem、false concrete scan、certificate obstructionへの接続により computability frontier として採る。
- `proof_or_evidence_plan`: Lean file `FiniteRouteScan.lean` で proved-in-research。G2/G3/G4 監査後に report と Issue score を同期する。

## CS / SWE への帰結

route family repair status は、ArchMap / observation layer などが supplied slot list を与えた場合、boolean scan と failing-slot certificate に落とせる。これは runtime patch synthesis や source extraction completeness ではなく、有限 evidence surface 上の exactness gate computation である。

## 証明・根拠

Lean file: `research/lean/ResearchLean/AG/QualitySurface/FiniteRouteScan.lean`

Proved declarations:

- `SlotListCovers`
- `ListedSlotsAllBranches`
- `listedAllBranchesScan`
- `listedAllBranchesScan_eq_true_iff`
- `assignmentFamilySourceRefExact_iff_listedScan`
- `listedFailingSlotCertificate`
- `routeSlotScanOrder`
- `routeSlotScanOrder_covers`
- `mixedRouteSlot_listedAllBranchesScan_false`
- `mixedRouteSlot_familyExact_iff_listedScan`
- `mixedRouteSlot_scanFailingCertificate`
- `mixedRouteSlot_scanCertificate_obstructs`
- `finiteRouteScan_package`

Boundary:

- supplied finite slot list と、その cover proof に相対化する。Lean statement は arbitrary `Slot` を自動列挙しない。
- canonical failing slot、minimal failing slot、arbitrary repair planner、runtime patch synthesis、source extraction completeness、ArchMap correctness、whole-codebase quality は主張しない。

## 審判メモ

- 厳密性: accept/base70。supplied cover list による exactness iff scan は厳密だが、Cycle 53 exact locus と list induction の合成でもある。generic false-scan-to-certificate、canonical/minimal failing slot、arbitrary enumeration は主張しない。
- 研究価値: accept/base70。Cycle 54 の certificate interface を finite scan へ接続し、computability frontier と finite evidence gate を閉じる。
- repo 全体価値: accept/base70。reportable finite evidence surface と paper seed の computability frontier を補い、将来の tooling/report/UI projection へ接続できる。
- ライバル比較: accept/base70。ADL / conformance checker との差分は status 表示ではなく、cover-list scan true iff exactness と certificate theorem の接続に限定する。

## Verification

- `focused Lean check: ResearchLean/AG/QualitySurface/FiniteRouteScan.lean`: pass
- `Research package build`: pass
- `lake build`: pass, with the pre-existing `Formal/Arch/Extension/FeatureExtensionExamples.lean` linter warning only
- forbidden-token scan for `sorry` / `admit` / `axiom` / `unsafe` / broad autoImplicit setting in the Lean file: pass
- hidden / bidirectional Unicode scan and private/local path scan: pass
- `.tmp/finite_route_scan_axioms.lean`: pass
  - axiom-free: `listedFailingSlotCertificate`
  - standard axioms only: scan/equivalence/package declarations depend only on `propext` / `Quot.sound`
- G3 independent audit: pass
  - axiom audit: no `sorryAx`; no nonstandard axioms; finite scan function and listed certificate constructor are axiom-free
  - formalization quality audit: pass; `SlotListCovers` is a strong but explicit supplied-list assumption, and the Lean statement does not claim arbitrary enumeration, generic false-scan-to-certificate, canonical/minimal slot, or repair planning

## 関連

- Cycle 53: `Finite route-family exact locus`
- Cycle 54: `Failing slot certificate`

## 進捗ログ

- 2026-06-21: Cycle 55 候補として作成し、Lean 証明を追加。
