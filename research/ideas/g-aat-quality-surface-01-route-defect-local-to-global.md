---
status: picked
goal: G-aat-quality-surface-01
candidate_type: closure
capability_category: certificate-transport / obstruction / invariance / computability / repair-potential
expected_base_score: 75
expected_evidence_multiplier: 2.0
expected_final_score: 150
evidence_stage: proved-in-research
origin: cycle-40
tags: [quality-surface, route-defect-support, localization, cancellation]
created: 2026-06-20
---

# Route-chain defect excursion support and selected local-to-global localization

## 主張

selected finite route chain `left -> middle -> right` において、片側 boundary leg が protected-zero なら、もう片側 local leg の route defect support は global endpoint route defect support と一致する。したがって selected decomposition の周辺 cell が zero である regime では、global endpoint defect support は selected nonzero cell support に局在する。

主対象は endpoint support ではなく、chain 内部の二つの leg の defect を合併して読む `InternalRouteDefectSupport` である。boundary leg も nonzero の場合には、二つの local route defect support が endpoint で cancellation しうる。特に flat chain `full -> full -> full` と token-swap/un-swap chain `full -> swapped -> full` は同じ empty endpoint support を持つが、internal support は後者だけが endpoint/worker table coordinates に非空である。したがって endpoint support だけを読む surface は、path-internal defect excursion に faithful ではない。

この主張は supplied finite source-ref packets、selected route endpoint chain、explicit packet-to-tuple bridge に相対化される。global additive defect group、canonical transport、canonical repair planning、source extraction completeness、ArchMap correctness、実コード全体の品質判定は結論しない。

## 候補種別

`closure`

## Lean 証拠

- `research/lean/ResearchLean/AG/QualitySurface/RouteDefectExcursionSupport.lean`
- `research/lean/ResearchLean.lean`

主要 declaration:

- `InternalRouteDefectSupport`
- `EndpointRouteDefectSupport`
- `RouteDefectExcursion`
- `SameEndpointRouteDefectSupport`
- `SameInternalRouteDefectSupport`
- `internalRouteDefectSupport_eq_endpoint_leftZero`
- `internalRouteDefectSupport_eq_endpoint_rightZero`
- `sourceRefExact_of_visible_and_emptyRouteSupport`
- `flatChain_endpointSupport_empty`
- `flatChain_internalSupport_empty`
- `tokenSwapUnswap_endpointSupport_empty`
- `tokenSwapUnswap_internalSupport_endpointTable`
- `tokenSwapUnswap_internalSupport_workerTable`
- `tokenSwapUnswap_noInternalObligationSupport`
- `tokenSwapUnswap_noInternalRepairFrontierSupport`
- `tokenSwapUnswap_noInternalStorageTableSupport`
- `TokenSwapUnswapExactInternalTablePairSupport`
- `tokenSwapUnswap_internalSupport_exact_tablePair`
- `tokenSwapUnswap_endpointTable_excursion`
- `flat_tokenSwapUnswap_sameEndpointSupport`
- `endpointSupport_not_faithful_to_internalSupport`
- `routeDefectExcursionSupport_package`

## 依拠

- `research/lean/ResearchLean/AG/QualitySurface/ComponentDefectPropagation.lean`
- `research/lean/ResearchLean/AG/QualitySurface/RouteDefectSupport.lean`
- `research/lean/ResearchLean/AG/QualitySurface/SourceRefRepairHolonomy.lean`
- `research/lean/ResearchLean/AG/QualitySurface/TransportTableLawRouteLocalization.lean`
- `research/lean/ResearchLean/AG/QualitySurface/VisibleRepairTransportCommutator.lean`

## 非自明性

Cycle 38 は route defect support の empty criterion、tuple projection、zero-leg propagation、selected exact support computation を与えた。この候補は、endpoint pair ではなく route chain 内部の defect excursion を新しい certificate surface として定義し、どの条件で local defect が endpoint defect と一致するか、またどの条件で endpoint から消えるかを分離する。

## 数学的興味

Quality Surface の endpoint reading は path の内部履歴を忘れる。zero boundary leg があると defect support は正確に伝播するが、二つの nonzero legs では cancellation により endpoint support が空になりうる。この「internal support / endpoint support / cancellation boundary」の三分法は、profile grid や repair/transport square を局所 obstruction geometry として読むための有限 calculus になる。

## GOAL への前進

route defect support を単発 endpoint predicate から finite chain 内部の defect excursion certificate へ上げる。これは selected commutator localization、profile curvature、loss-aware visualization、repair-potential の frontier に直接接続する。

## SCORE 見込み

- `score_reason`: Cycle 38 の route support calculus と Cycle 26 の cancellation witness を、`InternalRouteDefectSupport` という新しい chain certificate surface に統合する。G2 再審判は base 75 で一致したため、flat chain と token-swap/un-swap chain の same endpoint / different internal support nonfaithfulness まで Lean-proved できた場合の expected score を base 75 / final 150 に下げる。
- `dullness_risk`: zero-leg propagation theorem の再掲だけなら dull。internal support object、endpoint-support nonfaithfulness、token-swap/un-swap の exact internal support computation、source-ref exactness criterion を同じ package に入れる必要がある。
- `proof_or_evidence_plan`: 完了。`InternalRouteDefectSupport`、`RouteDefectExcursion`、`SameEndpointRouteDefectSupport`、`SameInternalRouteDefectSupport` を定義した。既存 zero-leg propagation を internal/endpoint support equality として再利用しつつ、flat chain と token-swap/un-swap chain の endpoint support は同じ empty だが internal support が異なることを Lean で証明した。token-swap/un-swap chain では internal support が endpoint/worker table pair にちょうど局在し、obligation、repair frontier、storage table coordinate には出ないことを明示した。

## CS / SWE への帰結

endpoint dashboard が clean に見えても、profile path の途中で defect excursion が発生している可能性がある。逆に、周辺 boundary が protected-zero であることが確認できる場合には、endpoint defect badge を selected local cell へ正確に戻せる。

## 証明・根拠

Lean では次の declaration を固定した。

- `InternalRouteDefectSupport`
- `EndpointRouteDefectSupport`
- `RouteDefectExcursion`
- `SameEndpointRouteDefectSupport`
- `SameInternalRouteDefectSupport`
- `internalRouteDefectSupport_eq_endpoint_leftZero`
- `internalRouteDefectSupport_eq_endpoint_rightZero`
- `sourceRefExact_of_visible_and_emptyRouteSupport`
- `tokenSwapUnswap_internalSupport_exact_tablePair`
- `tokenSwapUnswap_endpointSupport_empty`
- `tokenSwapUnswap_internalSupport_endpointTable`
- `tokenSwapUnswap_internalSupport_workerTable`
- `tokenSwapUnswap_noInternalObligationSupport`
- `tokenSwapUnswap_noInternalRepairFrontierSupport`
- `tokenSwapUnswap_noInternalStorageTableSupport`
- `endpointSupport_not_faithful_to_internalSupport`
- `routeDefectExcursionSupport_package`

検証:

- `cd research/lean && lake env lean ResearchLean/AG/QualitySurface/RouteDefectExcursionSupport.lean`: pass
- `cd research/lean && lake build ResearchLean`: pass
- `.tmp/route_defect_excursion_axioms.lean`: 全対象 declaration が axiom 依存なし
- `rg -n "\\b(axiom|admit|sorry|unsafe)\\b" research/lean/ResearchLean research/lean/ResearchLean.lean`: 新規差分に該当なし

G3 監査:

- 公理検査: pass。全対象 declaration は `does not depend on any axioms`。`sorryAx`、`propext`、`Classical.choice`、`Quot.sound` は残っていない。
- Lean 形式化品質監査: pass。zero-boundary localization、token-swap/un-swap exact internal support table pair、off-coordinate nonmembership、flat/token-swap same endpoint but different internal support nonfaithfulness が候補主張の強さで表現されている。arbitrary-length chain abstraction は未主張であり、この候補の claim boundary 外。

## 審判メモ

- 厳密性: 初回 G2 では base 45 revise。既存 propagation の再包装を避け、token-swap/un-swap exact route-level support、endpoint empty、nonmembership、nonfaithfulness を要求された。再審判では base 75 revise。base 85 は過大だが、exact internal support table pair と endpoint/internal nonfaithfulness まで証明すれば進めてよい、という判定。
- 研究価値: 初回 G2 では base 45 revise。route-chain/internal-excursion object と nonfaithfulness theorem を要求された。再審判では base 75 accept。
- repo 全体価値: 再審判で base 75 accept。endpoint dashboard が path-internal defect excursion を隠すことを Quality Surface の loss-aware visualization へ接続できる、と判定。

## 関連

- `g-aat-quality-surface-01-route-defect-support-calculus.md`
- `g-aat-quality-surface-01-visible-law-deletion-protected-zero.md`
- Cycle 26 component defect cancellation

## 進捗ログ

- 2026-06-20: Cycle 40 候補として作成。
- 2026-06-20: G2 A/B の revise を受け、既存 propagation の再包装を避けるため `InternalRouteDefectSupport` と endpoint/internal nonfaithfulness を主張へ追加。
- 2026-06-20: G2 再審判は A revise base 75、B accept base 75、C accept base 75。base 85 は下げ、picked 候補として base 75 で進める。
- 2026-06-20: `RouteDefectExcursionSupport.lean` で route-chain internal support、zero-boundary localization、token-swap/un-swap exact internal table-pair support、endpoint/internal nonfaithfulness を Lean-proved にした。
