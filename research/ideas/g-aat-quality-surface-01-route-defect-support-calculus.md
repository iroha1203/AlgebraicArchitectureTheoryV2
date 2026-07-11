---
status: picked
goal: G-aat-quality-surface-01
candidate_type: unification
capability_category: certificate-transport / traceability / obstruction / invariance / repair-potential / computability
expected_base_score: 70
expected_evidence_multiplier: 2.0
expected_final_score: 140
evidence_stage: proved-in-research
origin: G-aat-quality-surface-01-cycle38
tags: [quality-surface, route-defect, holonomy, support, repair-transport, source-ref]
created: 2026-06-20
cycle: 38
lean: research/lean/ResearchLean/AG/QualitySurface/RouteDefectSupport.lean
---

# Route defect support calculus for selected repair/transport endpoints

## 主張

repair/transport endpoint pair に対し、component-indexed packet holonomy defect を `RouteDefectSupport`
として読む。support が空であることは packet zero holonomy と同値であり、defect support は packet-to-tuple
bridge を通じて tuple protected component defect へ射影される。また zero packet leg に沿って route defect support は
preserve / reflect される。

selected witnesses では、Cycle 37 の transport table-law deletion route は `sourceRefTable endpoint` と
`sourceRefTable worker` の exact two-table support を持つ。ここで exact とは、この二つの table components で defect があり、
obligation、全 repair frontier components、`sourceRefTable storage` では defect がない、という pointwise
nonmembership を含む。Cycle 28 の visible-only repair/transport route は obligation、`repairFrontier storage`、
`sourceRefTable storage` の exact triple support を持つ。こちらも triple 以外の source-ref table / repair-frontier
coordinates では defect がないことを含む。したがって visible route flatness は route defect support に faithful ではなく、
commutator defect は atom/component support を持つ traceable obstruction として計算できる。

これは global な minimality matrix ではなく、route endpoint pair の defect support calculus と selected finite witness
計算である。`RouteDefectSupport` の名前替えだけでは成果としない。exact two-table / triple support の membership と
off-coordinate nonmembership を Lean statement に含める。

## 候補種別

`unification`

## 依拠

- Cycle 23: `research/lean/ResearchLean/AG/QualitySurface/CodebaseTraceHolonomyPacket.lean`
- Cycle 26: `research/lean/ResearchLean/AG/QualitySurface/ComponentDefectPropagation.lean`
- Cycle 28: `research/lean/ResearchLean/AG/QualitySurface/VisibleRepairTransportCommutator.lean`
- Cycle 37: `research/lean/ResearchLean/AG/QualitySurface/TransportTableLawRouteLocalization.lean`

## 非自明性

既存成果は component defect の存在や source-ref exact visualization failure を個別に示している。この候補は、
route endpoint pair の defect を support calculus として再読し、空性同値、tuple projection、zero-leg propagation、
selected exact two-table/triple support 計算を同じ Lean package に入れる。特に exact support 計算では、defect がある
coordinate だけでなく、他 coordinate に defect がないことを全 component case で固定する。これにより単なる defect
predicate の名前替えを避け、route defect を traceable support として運ぶための再利用可能な証拠境界を作る。

## 数学的興味

repair/transport commutator defect を、命題の失敗ではなく atom/component support を持つ obstruction として扱える。
これにより、source-ref exactness、loss-aware visualization、lawful criterion minimality matrix の各 cell を、
「どの protected coordinate が defect を支えるか」という幾何的な言葉で比較できる。

## GOAL への前進

selected commutator localization と route defect support calculus の frontier を直接進める。特に、Cycle 37 の
`open_questions` に残った route defect support calculus を Lean-backed な計算対象へ移す。

## SCORE 見込み

- `score_reason`: 直近 cycles の table-law / frontier-local / visible-only route obstruction を、traceable support calculus へ圧縮する。GOAL の certificate-transport、traceability、obstruction、repair-potential、computability を同時に増やすが、新現象そのものより再編成と support 化が主なので、G2 A の保守評価に合わせて base 70 / final 140 とする。
- `dullness_risk`: medium。`RouteDefectSupport := SourceRefPacketHolonomyDefect` の単なる別名に留まると低価値。empty iff、tuple projection、zero-leg propagation、Cycle 37 exact two-table support、Cycle 28 exact triple support、off-coordinate nonmembership を入れることで研究差分を確保する。
- `proof_or_evidence_plan`: `CodebaseTraceHolonomyPacket` の component defect と `ComponentDefectPropagation` の zero-leg propagation を使う。Cycle 37 route endpoint pair と Cycle 28 visible-only route endpoint pair に対し、support membership と non-membership を component cases で証明する。`propext` を避けるため、Set equality ではなく pointwise membership / non-membership theorem と package theorem を優先する。

## CS / SWE への帰結

repair/transport dashboard や report surface は、visible commutation の有無だけでなく、route defect support を
component label と atom label の drill-down として表示できる。table-only loss と multi-component loss を同じ
route surface に載せられる。ただしこの候補が示すのは supplied finite packets と selected route endpoint pair に相対化された
Lean witness であり、source extraction completeness、ArchMap correctness、実コード全体の品質判定は結論しない。

## 証明・根拠

Lean file:

- `research/lean/ResearchLean/AG/QualitySurface/RouteDefectSupport.lean`

Lean declarations:

- `RouteComponentAgreement`
- `RouteDefectSupport`
- `RouteDefectSupportEmpty`
- `routeDefectSupport_iff_packetHolonomyDefect`
- `routeDefectSupport_empty_iff_noPacketHolonomy`
- `routeDefectSupport_projects_to_tupleDefects`
- `routeDefectSupport_propagates_left_of_zero`
- `routeDefectSupport_propagates_right_of_zero`
- `tokenSwapRoute_defectSupport_endpointTable`
- `tokenSwapRoute_defectSupport_workerTable`
- `tokenSwapRoute_noObligationDefect`
- `tokenSwapRoute_noRepairFrontierDefect`
- `tokenSwapRoute_noStorageTableDefect`
- `tokenSwapRoute_defectSupport_exact_tablePair`
- `visibleRepairTransport_defectSupport_obligation`
- `visibleRepairTransport_defectSupport_storageRepair`
- `visibleRepairTransport_defectSupport_storageTable`
- `visibleRepairTransport_noRepairFrontierDefect_offStorage`
- `visibleRepairTransport_noTableDefect_offStorage`
- `visibleRepairTransport_defectSupport_triple`
- `routeDefectSupportCalculus_package`

Claim boundary:

- finite `SourceRefPacket`
- component-indexed `SourceRefPacketProtectedComponent`
- selected repair/transport endpoint pairs already supplied in `research/lean/ResearchLean`
- explicit packet-to-tuple bridge
- pointwise support membership / non-membership, not global codebase quality

Local G3 checks:

- `focused Lean check: ResearchLean/AG/QualitySurface/RouteDefectSupport.lean`: pass
- `Research package build`: pass
- `lake env lean .tmp/route_defect_support_axioms.lean`: pass; reported declarations depend on no axioms
- `rg -n "\\b(axiom|admit|sorry|unsafe)\\b" research/lean/ResearchLean/AG/QualitySurface/RouteDefectSupport.lean`: pass; no hits in the Lean evidence file

## 審判メモ

- 厳密性: 初回 G2 A は `revise`、base 45。一般 calculus 部分は既存定理の pointwise lift に近いため、Cycle 37 exact support と Cycle 28 triple support を、存在だけでなく全 off-coordinate nonmembership まで含む theorem として明示することが要求された。実装前確認で Cycle 37 token-swap route は endpoint だけでなく worker も table defect を持つため、claim を exact two-table support に修正した。再審査は `accept`、base 70。
- 研究価値: G2 B は `accept`、base 75。新現象そのものより再編成と support 化が主なので、初期期待 base 80 から 75 へ下げる。
- repo 全体価値: G2 C は `accept`、base 75。Lean / paper / future loss-aware visualization surface に価値があるが、selected finite witness を tooling verdict や whole-codebase quality へ昇格しないことが要求された。
- G3 audit summary: 公理 harness は reported declarations すべて axiom-free。Lean は `RouteDefectSupport` の空性同値、tuple projection、zero-leg propagation、Cycle 37 exact two-table support、Cycle 28 exact triple support を pointwise membership / nonmembership として表現している。

## 関連

- `research/ideas/g-aat-quality-surface-01-transport-table-law-route-localization.md`
- `research/ideas/g-aat-quality-surface-01-visible-repair-transport-commutator.md`
- `research/ideas/g-aat-quality-surface-01-supported-token-mismatch-obstruction.md`

## 進捗ログ

- 2026-06-20: Cycle 38 G1 で三者の候補生成から採択候補として作成。複数 agent が route defect support calculus または exact support localization を推した。
- 2026-06-20: G2 A の `revise` を受け、expected score を base 75 / final 150 に下げ、exact support と off-coordinate nonmembership を必須化した。実装前確認により Cycle 37 は singleton ではなく endpoint/worker の exact two-table support として修正した。
- 2026-06-20: G2 A 再審査が `accept`、base 70。保守評価に合わせて expected score を base 70 / final 140 に更新した。
- 2026-06-20: G3 Lean 実装を追加。対象 file、`ResearchLean`、axiom harness が pass。
