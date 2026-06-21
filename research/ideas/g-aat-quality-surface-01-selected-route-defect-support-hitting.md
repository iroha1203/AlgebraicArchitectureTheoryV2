---
status: picked
goal: G-aat-quality-surface-01
candidate_type: closure
capability_category: obstruction / repair-potential / traceability / atom-supported-quality-geometry
expected_base_score: 70
expected_evidence_multiplier: 2.0
expected_final_score: 140
evidence_stage: proved-in-research
rival_advantage: ADL / conformance checker can detect a selected route mismatch, but this result turns the protected route defect into a selected singleton-minimal support family and proves that packet-level protected-component correction must hit every selected branch.
origin: G-aat-quality-surface-01-cycle43
tags: [quality-surface, route-defect-support, repair-hitting, source-ref]
created: 2026-06-21
cycle: 43
lean: proved-in-research
---

# Selected route defect support hitting theorem

## 主張

visible tuple equivalence が固定された selected repair/transport commutator において、source-ref exact visualization failure を protected route defect support family として読み、その selected singleton-minimal support branches をすべて hit しなければ selected protected-component packet correction は成立しない。Cycle 28 / 38 の visible-flat route では、obligation、storage repair-frontier、storage source-ref table の三つが selected defect branches になる。

## 候補種別

`closure`

## 依拠

- `Formal/AG/Research/QualitySurface/RouteDefectSupport.lean`
- `Formal/AG/Research/QualitySurface/VisibleRepairTransportCommutator.lean`
- `Formal/AG/Research/QualitySurface/SourceRefExactVisualization.lean`
- `Formal/AG/Research/QualitySurface/InternalExcursionMinSupport.lean`

## 非自明性

Cycle 38 の route defect support は endpoint support の exact computation だった。Cycle 43 ではこれを selected singleton-minimal support family と correction hitting theorem に持ち上げる。単なる support 列挙ではなく、missed branch remains、all-hit necessity、hit した branch が実際に corrected packet と右 endpoint の protected component agreement を復元することを証明する。

## 数学的興味

route mismatch を failure として終わらせず、repair-potential / obstruction の対象に変換する。visible-flat でも protected support が非空なら exact visualization は失敗し、その失敗には correction が触るべき selected branch family がある。

## GOAL への前進

この候補は `obstruction`、`repair-potential`、`traceability`、`atom-supported-quality-geometry` を前進させ、selected commutator localization と selected support-defect localization を接続する。

## ライバルに対する有効性

ADL / conformance checker は mismatch component を表示できるが、protected route defect を selected support family として読み、その correction necessity を packet-level protected-component agreement theorem として固定するわけではない。この結果は、source-ref exactness failure から repair planning frontier へ進む AAT 側の差分を与える。

## SCORE 見込み

- `score_reason`: Cycle 38 の route support calculus と Cycle 41 の hitting theorem を接続し、さらに selected singleton-minimal branch と selected protected-component packet correction semantics へ持ち上げる closure。G2 改訂審判では厳密性 / repo-wide value が base 70、研究価値 / rival 比較が base 75 だったため、保守的に base 70、Lean proof が未完証明なしなら multiplier 2.0。
- `dullness_risk`: Cycle 41 の internal excursion hitting theorem の横滑りに見える危険がある。endpoint commutator support、visible-flat exactness failure、selected singleton minimality、corrected packet agreement を明確に分けることで回避する。
- `proof_or_evidence_plan`: `RouteDefectAtom`、`RouteDefectBranch`、`IsSelectedMinimalRouteDefectBranch`、`CorrectionHitsRouteDefectBranch`、`RouteDefectCorrectionEliminates`、`correctedVisibleRouteLeft`、`SourceRefRouteCorrectionEliminates` を定義し、missed branch remains、all-hit theorem、packet-level correction theorem を Lean で証明した。

## CS / SWE への帰結

loss-aware quality view で route defect を表示するだけでなく、どの protected branch を correction が必ず触るべきかを説明できる。これは tooling 実装 claim ではなく、finite selected witness 上の repair frontier theorem である。

## 証明・根拠の見込み

Lean file: `Formal/AG/Research/QualitySurface/SelectedRouteDefectSupportHitting.lean`

Planned / proved declarations:

- `visibleRoute_selectedDefectSupport_grounded`
- `routeDefectBranch_grounded`
- `routeDefectBranch_selectedMinimal`
- `selectedRouteDefectSupportFamily_minimal`
- `missed_routeDefectBranch_remains`
- `hits_every_selectedRouteDefectSupport_of_eliminates`
- `correctedBranchAgreement_iff_hits`
- `sourceRefRouteCorrection_eliminates_iff_hits`
- `sourceRefRouteCorrection_hits_every_of_eliminates`
- `obligationOnlyCorrection_does_not_eliminate`
- `allRouteDefectCorrection_eliminates`
- `obligationOnly_packetCorrection_does_not_eliminate`
- `allRouteDefect_packetCorrection_eliminates`
- `selectedRouteDefectSupportHitting_package`

Verification:

- `lake env lean Formal/AG/Research/QualitySurface/SelectedRouteDefectSupportHitting.lean`: pass
- `lake build FormalAGResearch`: pass
- `#print axioms` for all listed declarations: all `does not depend on any axioms`
- forbidden-token scan on the Lean file and candidate card: no matches

Boundary:

- selected finite source-ref packet route 上の theorem であり、global repair planner、canonical correction、source extraction completeness、ArchMap correctness、whole-codebase quality は主張しない。
- `correctedVisibleRouteLeft` は selected protected component を右 endpoint からコピーする有限 packet correction semantics であり、runtime patch や tooling 実装 claim ではない。

## 審判メモ

- 厳密性: 初回 G2 は revise。Bool branch hitting だけでは Cycle 41 の近傍に寄りすぎるため、formal minimal-support predicate、packet/source-ref correction semantics、非 rename bridge が要求された。Cycle 43 revise で `IsSelectedMinimalRouteDefectBranch` と `SourceRefRouteCorrectionEliminates` を追加済み。改訂後は accept / base 70。`SourceRefRouteCorrectionEliminates` は全 packet exactness ではなく selected protected-component agreement と読む。
- 研究価値: accept / base 75。source-ref exact visualization failure から selected three-branch support family と all-hit correction necessity へ圧縮している点を評価。
- repo 全体価値: accept / base 70。Cycle 38、41、42 の closure として有効だが、tooling / website 実装 claim ではない。
- ライバル比較: accept / base 75。ADL / conformance checker の mismatch 表示に対し、support-local repair semantics と all-hit necessity を加える点を評価。
- G3 公理監査: clean。listed declarations はすべて公理依存なしで、evidence multiplier x2.0 が許可された。
- G3 形式化品質監査: pass。`SourceRefRouteCorrectionEliminates` は selected protected-component agreement に限定され、全 packet exactness や global correction planner ではないことが確認された。

## 関連

- Cycle 38: `Route defect support calculus for selected repair/transport endpoints`
- Cycle 41: `Minimal internal excursion support family hitting theorem`
- Cycle 42: `Exact-visualization criterion and four-law selected minimality matrix`

## 進捗ログ

- 2026-06-21: Cycle 43 候補として作成。Lean 単体チェックは `lake env lean Formal/AG/Research/QualitySurface/SelectedRouteDefectSupportHitting.lean` で pass。
- 2026-06-21: G2 厳密性 revise に対応し、selected branch minimality と packet-level correction semantics を Lean に追加。単体チェックは再度 pass。
- 2026-06-21: G3 で `lake build FormalAGResearch`、網羅的 `#print axioms`、形式化品質監査が pass。
