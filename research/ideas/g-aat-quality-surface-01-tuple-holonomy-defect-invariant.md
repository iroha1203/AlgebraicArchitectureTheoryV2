---
status: picked
goal: G-aat-quality-surface-01
candidate_type: unification
capability_category: profile-curvature/certificate-transport/invariance/obstruction/traceability
expected_base_score: 60
expected_evidence_multiplier: 2.0
expected_final_score: 120
evidence_stage: proved-in-research
origin: G-aat-quality-surface-01-cycle22
tags:
  - tuple-holonomy
  - defect-invariant
  - protected-data
created: 2026-06-20
---

# Tuple holonomy defect invariant for protected certificate data

## 主張

profile tuple certificate の protected data 差分を、obligation、repair frontier、trace field の
component defect として分解する。zero tuple-holonomy defect は protected tuple data agreement と同値であり、
visible tuple surface が flat に見える selected finite square でも、component defect が非ゼロなら
protected-data holonomy は消えない。

さらに、cross-profile transport についても zero defect across profiles を protected-data preserving
transport と同値に読み、tuple transport が protected data を保存しない場合は component defect が
lossless tuple transport を阻害することを theorem package として固定する。

主張は selected finite tuple certificate、existing profile tuple fields、declared tuple transport に相対化する。
任意 profile family の global classification、canonical transport、source extraction completeness、
ArchMap correctness、実コード全体の traceability は結論しない。

## 候補種別

`unification`

## 依拠

- `Formal/AG/Research/QualitySurface/ProfileTupleIntegration.lean`
- `Formal/AG/Research/QualitySurface/TupleProtectedDataSquareCriterion.lean`
- `Formal/AG/Research/QualitySurface/TupleTransportExactness.lean`
- `ProfileTupleIntegration.SameTupleProtectedData`
- `ProfileTupleIntegration.endpointTuple_visibleAgreement`
- `ProfileTupleIntegration.endpointTuple_omega_diff`
- `ProfileTupleIntegration.endpointTuple_repairFrontier_diff`
- `ProfileTupleIntegration.endpointTuple_traceField_diff`
- `TupleTransportExactness.SameTupleProtectedDataAcross`
- `TupleTransportExactness.protectedDataDivergence_obstructs_losslessTupleTransport`

## 非自明性

Cycle 11 は same visible tuple surface の背後で protected tuple data が違う witness を固定し、
Cycle 18 は finite square criterion にその witness を接続した。この候補は、差分を単なる
`¬ SameTupleProtectedData` として扱わず、obligation / repair frontier / trace field の component
defect に分解し、zero-defect criterion と transport obstruction を同じ invariant surface に置く。

単なる rename にしないため、次を required evidence にする。

- no-defect iff protected tuple data agreement。
- obligation defect、repair-frontier defect、trace-field defect がそれぞれ no-defect を阻害する。
- selected endpoint pair で visible surface は一致するが、三つの component defect がすべて非ゼロである。
- selected tuple square の curvature を component defect から読める。
- cross-profile no-defect は `SameTupleProtectedDataAcross` と一致し、defect across transport は
  protected-data-preserving transport を阻害する。

## 数学的興味

profile curvature を「protected tuple data が違う」という一枚岩の否定命題から、有限 component
defect invariant へ分解する。これにより、Quality Surface の hidden holonomy をどの protected
component が支えているかを theorem statement として参照できる。

## GOAL への前進

profile-curvature / certificate-transport / invariance / obstruction / traceability を接続し、
tuple certificate geometry の holonomy を component-level invariant として扱えるようにする。

## SCORE 見込み

- `score_reason`: G2-B は base 75 を認めたが、G2-A/C が Cycle 11/18/14 の既存 witness と theorem に近い
  rename risk を指摘したため、revised candidate は base 60 / final 120 に下げる。
- `dullness_risk`: medium-high。`¬ SameTupleProtectedData` の再命名に落ちないよう、explicit component index、
  component theorem、selected endpoint instantiation、finite-square curvature reading、cross-profile transport
  obstruction を必須にする。
- `proof_or_evidence_plan`: `TupleHolonomyDefect.lean` に component defect、no-defect criterion、
  selected endpoint witness、selected square witness、transport obstruction theorem、package theorem を置く。

## CS / SWE への帰結

loss-aware visualization や drill-down report では、visible tuple surface が同じ場合でも、obligation /
repair frontier / trace field のどの component defect が hidden holonomy を作っているかを保持できる。
これは finite selected tuple certificate の数学的 witness であり、tooling completeness や実コード全体の
traceability は主張しない。

## 証明・根拠

Lean proof は `Formal/AG/Research/QualitySurface/TupleHolonomyDefect.lean` に閉じた。
`Formal/AG/Research.lean` はこの Research evidence file を import する。

主要 theorem / declaration:

- `TupleProtectedComponent`
- `NoTupleHolonomyDefect`
- `HasTupleHolonomyDefect`
- `TupleHolonomyDefect`
- `TupleHolonomyDefectAcross`
- `noTupleHolonomyDefect_iff_protectedData`
- `tupleHolonomyDefect_obstructs_noTupleHolonomyDefect`
- `endpointTuple_visibleSurface_hides_indexedDefects`
- `tupleProtectedDataSquare_componentDefects_curve`
- `noTupleHolonomyDefectAcross_iff_protectedDataAcross`
- `tupleHolonomyDefectAcross_obstructs_losslessTransport`
- `tupleTransportOfGridMap_noTupleHolonomyDefectAcross`
- `tupleHolonomyDefect_invariant_package`

固定された内容:

- `TupleProtectedComponent` は `obligation`、`repairFrontier atom`、`traceField atom` を component-indexed
  defect surface として持つ。
- `NoTupleHolonomyDefect` は same-profile protected tuple data agreement と同値であり、
  `TupleHolonomyDefect` は各 component の nonzero defect を表す。
- `tupleHolonomyDefect_obstructs_noTupleHolonomyDefect` は、任意 component defect が zero defect を
  阻害することを示す。
- `endpointTuple_visibleSurface_hides_indexedDefects` は、selected endpoint pair が visible tuple
  surface では一致する一方、三つの protected component defect をすべて持つことを示す。
- `tupleProtectedDataSquare_componentDefects_curve` は、selected finite square の visible flatness と
  component defect を `ReadingCurved` に接続する。
- `TupleHolonomyDefectAcross` と `tupleHolonomyDefectAcross_obstructs_losslessTransport` は、declared
  tuple transport 上の component defect が protected-data-preserving transport を阻害することを示す。
- `tupleTransportOfGridMap_noTupleHolonomyDefectAcross` は、grid-map tuple transport が protected data を
  pointwise に運ぶため zero cross-profile defect を持つことを示す。

検証:

- `lake env lean Formal/AG/Research/QualitySurface/TupleHolonomyDefect.lean`: pass。
- `lake build FormalAGResearch`: pass。
- `.tmp/tuple_holonomy_defect_axioms.lean` の `#print axioms`: listed declarations are all
  `does not depend on any axioms`。`sorryAx`、`propext`、`Classical.choice`、`Quot.sound` は出ていない。
- 対象 Lean file の `axiom` / `admit` / `sorry` / `unsafe` scan: no hits。
- G3 Lean 形式化品質監査: pass。component-indexed defect、endpoint/square witness、cross-profile
  transport obstruction により、単なる `¬ SameTupleProtectedData` の rename には留まらない。

## 審判メモ

- 厳密性: G2-A は初回 revise、base 60。`SameTupleProtectedData` は既に三成分の conjunction なので、
  no-defect iff だけでは定義展開に近い。explicit `TupleProtectedComponent` と component-indexed
  defect surface、endpoint/square/transport obstruction を required evidence とした。
- 厳密性再審判: G2-A は revised card / Lean proof を accept、base 60 / final 120。
- 研究価値: G2-B は初回 accept、base 75 / final 150。hidden protected tuple curvature を成分別に
  追跡できる invariant にする価値を認めた。
- repo 全体価値: G2-C は初回 revise、base 65。既存 Cycle 11/14/18 に近いため、candidate type の正規化と
  score reduction、explicit defect interface を要求した。再審判では accept、base 60 / final 120。
- SCORE 監査: G4 は confirm、base 60 / evidence multiplier 2.0 / penalty 0 / final 120。

## 関連

- `research/ideas/g-aat-quality-surface-01-profile-tuple-integration.md`
- `research/ideas/g-aat-quality-surface-01-tuple-transport-exactness.md`
- `research/ideas/g-aat-quality-surface-01-tuple-protected-data-square-criterion.md`
- `research/reports/G-aat-quality-surface-01.md`

## 進捗ログ

- 2026-06-20: Cycle 22 candidate card 作成。
- 2026-06-20: G2-A/C revise を反映し、candidate type を `unification` に正規化し、
  expected score を base 60 / final 120 へ下げ、explicit component index を required evidence に追加した。
- 2026-06-20: `TupleHolonomyDefect.lean` を追加し、単体 Lean、`FormalAGResearch`、axiom harness、
  G3 Lean 形式化品質監査を通した。
- 2026-06-20: G4 SCORE 監査 confirm。report の Cycle 22 と Current SCORE を total 2680 に更新した。
