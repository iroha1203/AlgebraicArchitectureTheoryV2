---
status: picked
goal: G-aat-quality-surface-01
candidate_type: obstruction-certificate / closure
capability_category: obstruction / certificate-transport / repair-potential / traceability / invariance / quality-surface
expected_base_score: 70
expected_evidence_multiplier: 2.0
expected_final_score: 140
evidence_stage: proved-in-research
rival_advantage: ADL / conformance checker can mark failing route slots, but this result packages family exactness failure as an explicit certificate object with obstruction and no-certificate exactness theorems.
origin: G-aat-quality-surface-01-cycle54
tags: [quality-surface, route-family, exact-locus, failing-slot, certificate]
created: 2026-06-21
cycle: 54
lean: proved-in-research
---

# Failing slot certificate

## 主張

任意の staged route-slot assignment `Slot -> RepairStage` について、family source-ref exactness の失敗は、ある slot と `allBranches` でない証拠からなる明示的な `FailingSlotWitness` の存在と同値である。逆に、そのような certificate が存在しなければ family exactness が成り立つ。Cycle 52 の mixed route-slot assignment には secondary slot の failing certificate が具体的に存在する。

## 候補種別

`obstruction-certificate / closure`

## 依拠

- `research/lean/ResearchLean/QualitySurface/FiniteRouteFamilyExactLocus.lean`
- `research/lean/ResearchLean/QualitySurface/MultiRouteCorrectionSystem.lean`

## 非自明性

Cycle 53 は arbitrary staged route family の exact locus と failing-slot obstruction を固定した。Cycle 54 は failure を単なる否定命題として残さず、slot と stage failure を持つ certificate object に変換し、exactness failure / no-certificate exactness / concrete mixed witness を同じ theorem package に束ねる。これにより、family-level failure を reportable な obstruction certificate として扱える。

## 数学的興味

exact locus の補集合を「どこかが失敗している」という古典的な論理形から、AAT Quality Surface の certificate tuple に載せられる明示 witness へ変換する。これは minimal failing slot theorem や computable finite scan instance へ進むための、failure mode の型付き界面である。

## GOAL への前進

この候補は `obstruction`、`certificate-transport`、`repair-potential`、`traceability`、`invariance`、`quality-surface` を前進させる。family exactness の failure を route slot certificate として取り出し、quality surface 上で obstruction を局所化して運べる形にする。

## ライバルに対する有効性

ADL / conformance checker は route ごとの failing status を表示できるが、family exactness の否定を certificate object と obstruction theorem、no-certificate exactness theorem、concrete mixed witness として同じ Lean surface に固定しない。

## SCORE 見込み

- `score_reason`: arbitrary route-slot assignment で failure iff certificate、exactness iff no certificate、certificate obstruction、mixed route-slot concrete certificate を Lean で固定する。Cycle 53 の failing-slot obstruction を certificate interface へ上げる成果なので base70 とする。
- `dullness_risk`: Cycle 53 の否定命題を構造体に包むだけに見える危険がある。逆向きの no-certificate exactness、mixed witness、theorem package により failure mode を次の computable scan / minimal witness へ接続する。
- `proof_or_evidence_plan`: Lean file `FailingSlotCertificate.lean` で proved-in-research。G2/G3/G4 監査後に report と Issue score を同期する。

## CS / SWE への帰結

route family repair status が失敗したとき、その失敗は単なる boolean false ではなく、どの route slot が required correction stage に入っていないかを持つ certificate として扱える。有限 scan や UI 表示へ移す場合は、ArchMap / observation layer が slot family を供給することに相対化する。

## 証明・根拠

Lean file: `research/lean/ResearchLean/QualitySurface/FailingSlotCertificate.lean`

Proved declarations:

- `FailingSlotWitness`
- `failingSlotCertificate_obstructs_familyExact`
- `not_familyExact_iff_exists_failingSlotCertificate`
- `familyExact_iff_no_failingSlotCertificate`
- `mixedRouteSlotFailingCertificate`
- `mixedRouteSlotFailingCertificate_obstructs`
- `mixedRouteSlot_exists_failingSlotCertificate`
- `failingSlotCertificate_package`

Boundary:

- supplied route slots、staged selected correction semantics、explicit source-ref packet bridge に相対化する。Lean statement は `Slot : Type u` 全般であり、finite enumeration / computable scan は主張しない。
- arbitrary repair planner、runtime patch synthesis、source extraction completeness、ArchMap correctness、whole-codebase quality は主張しない。

## 審判メモ

- 厳密性: accept/base70。Cycle 53 の exact locus と failing-slot theorem から直接に出る面はあるが、typed certificate、no-certificate exactness、mixed concrete package により単なる rename ではない。claim boundary は `research/lean/ResearchLean` の route-slot family に限定する。
- 研究価値: accept/base70。Cycle 53 の exact locus を failure certificate interface へ上げる。minimality / computable scan までは出ていないため base80 にはしない。
- repo 全体価値: accept/base70。reportable obstruction certificate として route-family failure を固定し、paper seed と次 frontier へ接続する。
- ライバル比較: accept/base70。ADL / conformance checker との差分は failing status 表示ではなく、certificate object と no-certificate exactness theorem に限定する。

## Verification

- `lake env lean research/lean/ResearchLean/QualitySurface/FailingSlotCertificate.lean`: pass
- `lake build ResearchLean`: pass
- forbidden-token scan for `sorry` / `admit` / `axiom` / `unsafe` / broad autoImplicit setting in the Lean file: pass
- `.tmp/failing_slot_certificate_axioms.lean`: pass
  - axiom-free: `mixedRouteSlotFailingCertificate`, `mixedRouteSlot_exists_failingSlotCertificate`
  - standard axioms only: certificate obstruction / failure equivalence / no-certificate exactness / package declarations depend only on `propext` / `Classical.choice` / `Quot.sound`
- G3 independent audit: pass
  - axiom audit: no `sorryAx`; only allowed standard axioms; concrete mixed witness existence axiom-free
  - formalization quality audit: pass; `FailingSlotWitness` is a reusable typed obstruction certificate, and `∃ _, True` is acceptable because the certificate data lives in the witness object

## 関連

- Cycle 52: `Multi-route correction system`
- Cycle 53: `Finite route-family exact locus`

## 進捗ログ

- 2026-06-21: Cycle 54 候補として作成し、Lean 証明を追加。
