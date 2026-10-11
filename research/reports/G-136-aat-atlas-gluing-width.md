# G-136 証明記録

固定 GOAL・設計・共通基準: `636ea3d45558fd0e511e3184cfa74ab1c23142c0`。
GOAL blob: `dbc5b584987a1f3e1987125b7ccde2e361a89533`。
既存宣言の参照版: `ed16acc02229fdfe3846303de341d600878f03dc`。
追跡: [#5321](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5321)。

## 現 proof obligation

T0・A–E は固定 target を維持する。初回 selection は実装前の開始報告で固定した。
A は PR #5328、merge `bb80b4068979dd1ecca354d8cebe9cad66f54e16` で部分受理済み。
B は PR #5329、merge `a06669caf8b6983068a32f7ab81b5d390bb42b22`、
C は PR #5330、merge `0626e53e5ff4dd8e80756d0bf9be133e84c10feb` で部分受理済み。
現在は D の実Lawと係数/fiber接続をCycle 4受理候補として構成・検証する。
E の任意k指定族・全Law幅・MV発火と全GOAL最終判定は未実施。
G-135 の Research 達成済み結果を再利用する。Formal は `unported (Research-proved)`。

## Cycle 1 selection

```yaml
ledger_type: target_cycle_result
goal: G-136-aat-atlas-gluing-width
cycle: 1
goal_blob_sha: dbc5b584987a1f3e1987125b7ccde2e361a89533
base_oid: 5f235b43edb2410070d7f59a13aa45640f1114c8
tracking_issue: 5321
report_path: research/reports/G-136-aat-atlas-gluing-width.md
selection:
  proof_state_ref: Issue 5321 の証明未着手記録
  proof_dag_predecessors: [RI.TargetSupportedNerve, RI.targetSubsetComplex, FRS.IncidenceSupportedComparison]
  milestone: GOAL A の真のセル交差・三次数 SES・原始比較の可換性
  proof_obligations: [K1 による閉性, 和と交差, 元セル評価と微分, 三次数 SES, 部分比較の交差制限, 粗細図式]
  exit_criteria: [通常領域と既存複体の同定, 全三次数の単射と完全性と全射, 原始比較による可換性, focused check と全宣言公理監査]
  selection_reason: B と C が必要とする原始 SES を構成する
  expected_result_type: proof-obligation-discharged
  lean_targets: [ResearchLean/AG/AtlasGluingWidth/CellSelection.lean, ResearchLean/AG/AtlasGluingWidth/RegionShortExact.lean, ResearchLean/AG/AtlasGluingWidth/SelectionComparison.lean]
  risks: [セル交差と target 部分集合交差の混同, 退化 face の符号, 零延長の cochain 射への誤認]
  unchecked: [正式査読, 粗細図式]
```

## A の条項別対応と受理候補宣言

namespace は `AAT.AG.AtlasGluingWidth`。

| 条項 | 実宣言 | 入力・放電・使用先 |
| --- | --- | --- |
| 同じ元セルの和・交差 | `CellSelection.region`, `inter`, `union`, `region_union` | K1 の支持交差から全 incidence 閉性を生成。交差は二つの存在条件の積。B/C の SES 入力。 |
| 原始微分 | `CellSelection.d0`, `d1`, `d1_d0`, `complex`, `region_complex` | 三つの元面端点等式を使い d1d0=0 を導出。通常領域は既存 targetSubsetComplex と全複体が一致。 |
| 全三次数 SES | `Cellwise.inclusion_injective`, `difference_surjective`, `exact`, `CellSelection.union_intersection_exact0/1/2` | 元セル評価・差・次数別零延長・一致する組の貼り合わせ。`unionInclusion_injective0/1/2`, `intersectionDifference_surjective0/1/2` を伴う。 |
| cochain 射 | `CellSelection.unionInclusion`, `intersectionDifference`, `regionInclusion` | 制限は元 incidence の評価で可換、差制限は有理係数の符号計算。 |
| 原始部分比較 | `SelectionCompatible.region`, `inter`, `union`, `pull_comm0`, `degenerate_face_sum`, `pull_comm1`, `hom` | chart 台と K1 edge/face 台輸送。退化 face の符号付き零和は G-134 `optionCell_incidence_iff` で相殺へ移す。 |
| 粗細可換図式 | `SelectionCompatible.union_square0/1/2`, `inter_square0/1/2`, `region_hom_eq`, `intersectionHom` | 全三次数の同じ原始部分像の評価。通常領域の Hom は G-134 aSubnerveComparisonHom と全 Hom が一致。 |
| 非空虚性の API | `SelectionCompatible.region`, `not_empty_coarse_univ_fine` | 前者は任意領域に対し生成。後者は任意 fine chart を持つ原始比較で、空 coarse/全 fine の選択が輸送不可能と証明。 |

一般 `CellSelection` の閉性 field と `SelectionCompatible` の輸送 field は中間 API。
受理経路では `region`・`inter`・`union` の生成定理からのみ取得する。
SES の完全性、微分可換性、線形同型、H¹ 消滅を入力 field へ置いていない。
`direction-hypothesis` は今回の A にない。T0 の原始幾何は `ambient-boundary`（本文由来）、
A の閉性・完全性・輸送・可換性は `discharge-required`（上表の構成で放電する候補）。
`Cellwise` の任意述語は次数別の一般補題であり、受理経路で必ず K1 選択へ適用する。

## 再利用の実宣言照合

G-134 の Research 成果の受理記録は [PR #5287 の完了台帳](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5287#issuecomment-6030258596)。
参照版 `ed16acc02` と今回 base の関連 source の差分は空。
`TargetSupportedNerve` の有限セルと chart 非空台、三つの face 端点等式、
`IncidenceSupportedComparison` の Option 部分像・原始零和・chart 台包含を実型で確認。
`edgeSupport_compatible`・`faceSupport_compatible` は mapped セルの台輸送を導出し、
今回の `SelectionCompatible.region` がそれぞれの所属点に使う。
`aSubnerveComparisonHom` は全三次数の targetSubsetPullback、原始 d0/d1 可換性を持つ。
今回の `region_hom_eq` が追加前提なく全 Hom を同定する。

G-133 `zeroExtensionMap`・`oldH1Equiv`・`cone_short_exact` は、三項複体と任意 Hom からの
標準零延長・旧商対応・全整数次数の余核/錐/次核の列を構成する。
受理記録は [PR #5269 完了台帳](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5269#issuecomment-6007700344)。
今回 A から B へ渡す原始複体・Hom は同じ型。B での新 LES との接続は次の義務。

G-135 `directH1`・`directH1_old`・`coefficientCokernel_shortExact` は、任意混在 M と固定 X の
同じ u の標準 H¹・旧商自然性・余核の短完全列。
受理記録は [Issue #5290 全目標完了記録](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5290#issuecomment-6078348119)。
通常領域は今回の `region_hom_eq` で同じ u を保持する。D の射・核商の具体的接続は後続義務。
G-135 の fiber 項や τ を未証明へ戻す工程は置かない。

## 検証記録

Research 検証はこの到達点の個別 source に限定する。root aggregate と Research 全体 build は実行しない。
各 source 末尾の `#assert_standard_axioms_only` は当該 module の全新規宣言を検査する。
同じ source に基づく全実宣言の `#print axioms` を単一の監査 file で照会し、PR に実行結果を保存する。
各 cycle の proposal は受理候補であり、正式受理は固定headのPR監査に置く。Cycle 1 の受理記録は下記を参照。

## Cycle 1 result proposal

```yaml
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: K1 選択・真のセル和交差・原始微分・全三次数 SES・原始比較と二つの可換正方形を構成
  exit_criteria_status: [region_complex と region_hom_eq による既存 API 同定, 全三次数の単射/完全性/全射, union_square と inter_square, 各 source focused check と公理監査]
  split_reason: none
  completion_candidate: no
  lean_artifacts: [CellSelection.lean, CellwiseShortExact.lean, RegionShortExact.lean, SelectionComparison.lean]
  evidence: [region_union, d1_d0, union_intersection_exact0/1/2, region, pull_comm0/1, union_square0/1/2, inter_square0/1/2, region_hom_eq]
  claim_mapping:
    theorem_names: [region_union, region_complex, union_intersection_exact0/1/2, region_hom_eq, union_square0/1/2, inter_square0/1/2]
    source_labels: [GOAL A, 設計 exact-sequence §1]
    conjuncts: [前節の条項別対応表]
    undischarged_assumptions: []
    acceptance_point: 任意原始 M と任意 A/B への全三次数の構成
    port_status: unported
audits:
  premise_delta:
    discharged: [K1 閉性, 台輸送, 微分可換性, 原始 SES と粗細可換図式]
    remaining: [B–E の構成義務]
  certificate_provenance:
    discharged: [CellSelection.region/inter/union, SelectionCompatible.region/inter/union]
    unresolved: []
  proof_use:
    used: [face 端点等式→d1_d0, K1 台→region 輸送, 原始零和→degenerate_face_sum, 部分像→二つの可換正方形]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [各 source の個別 focused check, 全実宣言の明示公理照会, PR 差分 scan]
  blocking_findings: [標準 PR 独立査読前]
  next_obligation: A の正式受理後に B の標準錐 SES と全整数次数 LES
```

cycle scaffold は追加していない。受理候補は前節の宣言と、それらの定義・公開 API・
instance chain を支える4 source の全宣言。登録は同じ4 source の manifest 行だけ。
固定カード・設計・保護領域・既存の G-133〜135 source は変更していない。
正式 review evidence と root acceptance 判定、CI、merge、次 obligation は PR/Issue に同期する。

Cycle 1 初回 head `6fef3d8fc82fc638d6f269b5c368fcbda92e9bd8` の個別 source focused check は全4 file が exit 0。
公式検査 `bash research/lean/check_research_modules.sh --focused ResearchLean/AG/AtlasGluingWidth/SelectionComparison.lean`
は exit 0、対象 module の45宣言は標準公理のみ。
同じ依存 source の全116実宣言を単一非 aggregate の監査 file から明示照会し、全て標準公理のみ。
照会 log SHA256 は `70eff3576f63c2bed934cb0026f64bcb3ee97b706112275746e102449325cf97`、
公式 focused log は `2088aed2a2001f68e603b8c16bfc7d10c507163f04f9e8048bef14fdd550d9a8`。
placeholder、hidden/BiDi、privacy、語彙、import 方向、diff whitespace は該当違反なし。

修正後の Lean source head `d8227fbd3b5f36d97b9e04ffab7f4284c7fd20cf` でも個別 focused check は全4 file が exit 0。
同じ公式 focused command は exit 0、対象 module の49宣言は標準公理のみ。
同じ依存 source の全128実宣言を単一非 aggregate の監査 file から明示照会し、
全て標準公理のみ。照会 log SHA256 は
`707f3e01b62eb8938c46f8222775cf21bf9bc5dc7383f9361309208e329e76a6`、
公式 focused log は `16e1f30736ad29ff441a74b1ab7488a7f8a02ff56e7393c51826eba097ee994a`。
この追記は検証対象版の記録修正であり、Lean source と受理候補 status は変更していない。

## Cycle 1 正式受理と Cycle 2 selection

Cycle 1 は [PR #5328 の正式再査読・直接対応・root acceptance](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5328#issuecomment-6107488109)
で A に限り `proof-obligation-discharged / approve`。最終head `9bc23d2890f8091bdc897518e367a147445d4296`、
merge `bb80b4068979dd1ecca354d8cebe9cad66f54e16`、全CI7pass。
[Issue同期](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5321#issuecomment-6107496247)。
全GOALは `target-proof-checkpoint`。B–EとFormal移植は未実施。

```yaml
ledger_type: target_cycle_result
goal: G-136-aat-atlas-gluing-width
cycle: 2
goal_blob_sha: dbc5b584987a1f3e1987125b7ccde2e361a89533
base_oid: bb80b4068979dd1ecca354d8cebe9cad66f54e16
tracking_issue: 5321
report_path: research/reports/G-136-aat-atlas-gluing-width.md
selection:
  proof_state_ref: PR 5328 A受理とIssue同期6107496247
  proof_dag_predecessors: [Aの実原始SESと六square, G133零延長と標準錐座標とcone_short_exact, mathlib HomologySequence]
  milestone: GOAL Bの同じ図式から標準錐Mayer–Vietoris SESと全整数次数LESを構成
  proof_obligations: [三項SESの標準零延長, 同じ粗細二行図式, 標準mappingCone SES, 錐の二領域直和同定, 標準LESの全整数次数完全性, cocycle持ち上げ微分貼り合わせと標準δ符号同定, 同じG133隣接次数核余核列への接続]
  exit_criteria: [原始Mと任意A/Bから全構成を生成, 実標準錐とその直和のSESと全ℤ LES, δの代表式と選択独立性, 同じ四つの比較へG133 cone_short_exactを適用, 対象source focused checkと全実宣言公理監査]
  selection_reason: Cの実Q/Pとsnakeが必要とする標準LESを生成し錐の隣接次数寄与を保持する
  expected_result_type: proof-obligation-discharged
  lean_targets: [AtlasGluingWidth/StandardShortExact.lean, AtlasGluingWidth/ConeShortExact.lean, AtlasGluingWidth/ConnectingRepresentatives.lean, AtlasGluingWidth/MayerVietoris.lean]
  risks: [三項と標準零延長のtransport, 錐のfine_m/coarse_m+1の座標順と負号, 標準直和と次数積の同定, δ代表元公式の符号, localJ零から錐消滅への誤推論]
  unchecked: [Bの実装と正式査読, C–Eの全構成]
```

## B の条項別対応と受理候補宣言

| 固定要求 | 実構成・宣言 | 入力からの放電と同じ射 |
| --- | --- | --- |
| 三項 SES の標準零延長 | `StandardRow.row_zero`, `row_shortExact`, `cellRow`, `cellRow_shortExact` | A の全三次数の単射/完全性/全射を使い、次数外は零対象から生成。標準 `zeroExtensionMap` の同じ f/g。 |
| 同じ二行図式 | `StandardRow.pairHom`, `cellRowMap` | 原始 M から生成した hs/ht の六squareを標準零延長の全Homへ移す。 |
| 標準錐 SES | `ConeRow.inc`, `diff`, `inc_coordinate`, `diff_coordinate`, `row_shortExact` | mathlib mappingCone.map。fine のmとcoarse のm+1の同じSESの実完全性を使う。 |
| 実二領域直和 | `PairComplex.degreeEquiv/fst/snd/map_fst/map_snd`, `ConeBiprod.degreeEquiv`, `split_coordinate`, `iso`, `iso_hom_fst/snd` | 元の二領域比較の標準錐の両座標を同じ領域へ並べ直す。実projectionを保つ全複体同型。 |
| 原始入力への適用 | `AtlasMayerVietoris.coneRow_shortExact`, `coneBiprodRow_shortExact`, `region_cone_shortExact` | M と任意A/Bのregion certificateから生成し、新しいexactness引数を要求しない。 |
| 全整数次数 LES | `StandardLES.connecting`, `exact_before/middle/after`, `AtlasMayerVietoris.cochain_les`, `cone_les`, `coneBiprod_les` | 標準 ShortExact のhomology列を全m∈ℤに適用。degree -1〜2へのstatement縮小なし。 |
| δ の代表元・持ち上げ・独立性 | `CohomologyRepresentatives.cycleClass_surjective`, `lift_cocycle`, `connecting_cycleClass`, `connecting_choice_independent`, `connecting_representative_independent`, `AtlasMayerVietoris.coneBiprod_lift_cocycle`, `coneBiprod_connecting_representative` | 任意classを実cocycleで表し、degreewise epi/exact/monoから持ち上げ・微分貼り合わせ・cocycleを生成。同じ元をmathlib δ_eqへ渡す。 |
| 符号・自然性 | `AtlasMayerVietoris.cochain_connecting_natural`, `coneBiprod_connecting_eq`, `cone_union_d` | 差制限x|-y|を変えず、錐微分(d_f y+u x,-d_c x)と標準δを保持。端点を固定する同型でδそのものを保つ。 |
| G-133 隣接次数寄与 | `AtlasMayerVietoris.comparison_cone_shortExact`, `region_comparison`, `regionUnionHom_eq`, `region_union_comparison` | 同じhs/ht/union/inter Homの零延長へ既存cone_short_exactを適用。coker H^mとker H^(m+1)を保持。UもAの全セル等号に沿う全Hom輸送で通常領域の同じ比較へ接続。局所J零から錐消滅を推論しない。 |

`StandardRow` の一般exact/injective/surjective引数、`ConeRow`・`StandardLES`・代表元APIの一般ShortExact引数は、一般補題のdirection-hypothesisである。
受理経路ではAのcellRow_shortExact→原始cellRowMap→ConeRow.row_shortExact→実biproductへの同型輸送としてすべて放電する。
`hs/ht`は領域では既存 `SelectionCompatible.region` がT0入力から生成する。
新しい結論certificate fieldやexpected-rank条件は追加していない。持ち上げの非計算的選択は標準epiの全射性から得る。
新規Prop certificateは追加していない。

B の依存は A受理PR5328、G-133受理PR5269の現在 `ZeroExtension/ConeCoordinates/ConeExactSequence`、
固定mathlibの `ShortComplex.ShortExact`/`HomologySequence`/`HomologySequenceLemmas`/複体・ModuleCat biproduct API。
実宣言の型・適用引数を読み、同じ比較・degree m/m+1・標準符号を保持することを確認する。
C のQ/Pとsnake、D の実Law/G135欠損、E の指定全k族は、この部分cycleの達成として数えない。
cycle scaffold は追加していない。B受理候補を支える6 sourceの全宣言を公理監査対象とし、同じ6 sourceをmanifestへ登録する。

## Cycle 2 result proposal

```yaml
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: Aの実二行図式から標準零延長SES・標準錐SES・実錐直和同定・全整数次数LES・標準δ代表式と独立性・同じG133隣接核余核列を構成
  exit_criteria_status: [原始regionからのSES生成, 実mappingConeと標準biproduct, 全m∈ℤの三位置完全性, 任意classの実cocycleと入力生成の持ち上げ, δ_eqの同じ元と符号, 同じ四比較のG133 SES, 通常合併Uの全Hom輸送]
  split_reason: none
  completion_candidate: no
  lean_artifacts: [StandardShortExact.lean, PairComplex.lean, ConeShortExact.lean, ConnectingRepresentatives.lean, ConeBiprod.lean, MayerVietoris.lean]
  evidence: [cellRow_shortExact, cellRowMap, ConeRow.row_shortExact, ConeBiprod.iso, coneBiprodRow_shortExact, coneBiprod_les, cycleClass_surjective, coneBiprod_lift_cocycle, coneBiprod_connecting_representative, connecting_choice_independent, coneBiprod_connecting_eq, cone_union_d, comparison_cone_shortExact, regionUnionHom_eq]
  claim_mapping:
    theorem_names: [B条項別対応表の実宣言]
    source_labels: [GOAL B, 設計exact-sequence §2]
    conjuncts: [同じ原始図式からの標準錐SES, 全整数次数LES, 代表式と標準δと符号, G133隣接次数SES接続]
    undischarged_assumptions: []
    acceptance_point: 任意原始Mと任意A/Bへの入力生成・全次数・実標準錐と直和
    port_status: unported
audits:
  premise_delta:
    discharged: [三項SESから標準零延長SES, 原始六squareから二行比較, fine_mとcoarse_m+1から錐SES, 実biproductへの同型, 標準LESとδ代表元と独立性]
    remaining: [C–Eの構成義務]
  certificate_provenance:
    discharged: [AのregionからcellRow_shortExact, 同じcellRowMapとConeRow.row_shortExact, coneBiprodRowIsoによるShortExact輸送]
    unresolved: []
  proof_use:
    used: [三次数exact/injective/surjectiveと次数外zero, 二行の実exactとmono/epiによる錐座標, 標準δ_eqとdegreewise epi/exact/mono, 同じ二つの錐制限による実biproduct同型, 全セル等号から合併全Hom輸送]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [各sourceの個別focusedとmodule公理監査, 全実宣言の明示公理照会, 共通scan]
  blocking_findings: [標準PR独立査読前]
  next_obligation: B正式受理後にCの実Q/P・自然な二行SES・snake・局所J零下の欠損
```

## Cycle 2 検証記録

このPRの新規6 sourceの個別focused checkはすべてexit 0。
各moduleの標準公理監査は順に10・13・7・12・15・26宣言、計83新規宣言。
公式単一 `bash research/lean/check_research_modules.sh --focused ResearchLean/AG/AtlasGluingWidth/MayerVietoris.lean`
はexit 0、MayerVietorisの26宣言は標準公理のみ。
Aの128宣言とこの83宣言を含む累積全211実宣言を、単一非aggregate監査fileから
明示 `#print axioms` 照会し、exit 0、重複なし、標準propext/Classical.choice/Quot.sound以内。
公式focused log SHA256は `6b3ed6fc5ae2f6a47118e6394f40f542ddd038ccc8dc55729acc7d23c8f85896`、
全宣言log SHA256は `b6fd8363b7574ec290c624c94cd50e58bcebf38acd58f0876faee18bcc0818a3`。
固定G133参照版ed16acc…から使用3 sourceへの差分は空。
Research全体build・aggregate・全file elaboration・Formal移植は実行していない。
正式4 lane査読、内容受理、CI、mergeはこの段階では未実施であり、PR監査へ同期する。

## Cycle 2 初回査読と修正スナップショット

初回固定 head `9f008cdce07c2f6042d5f1710db4ae1ae80913ec` の通常4 lane独立査読は、
数学A/B・Lean A/Bすべて `Minor issues`、中心findingなし。合格・受理はまだ出していない。
非中心findingを統合し、錐SES主要証明を公開 `inc_coordinate/diff_coordinate` へ変更し、
座標交換 `shuffle` を固定mathlibの `LinearEquiv.prodProdProdComm` の使用へ置換した。
新規6 sourceの説明に固定GOAL B／設計§2との対応、一般方向仮定の出所と原始適用時の
放電元、実装選択と退けた代替案・理由を記録した。
定義本体の変更を含むため、共有review protocolの直接対応資格を満たさない。
修正後固定headに対して新しい数学2本・Lean2本による正式再実行1へ進む。

修正した `ConeShortExact`・`ConeBiprod` と下流 `MayerVietoris` の個別focusedはexit0。
公式単一MayerVietoris focusedもexit0（26宣言）、全211実宣言の明示公理照会もexit0。
両logは前記SHA256とそれぞれ一致し、宣言数と標準公理のみの結果は維持した。
placeholder、hidden/BiDi、privacy、語彙、import方向、diff whitespaceはclean。
上の「正式4 lane査読未実施」は初回head時点の履歴であり、この修正headの受理状態を表さない。
C–E・Formal移植・Research全体buildはこのcycleの達成に含めない。

## Cycle 2 正式受理と Cycle 3 selection

B は [PR #5329 の正式再査読とroot acceptance](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5329#issuecomment-6107924638)
で `proof-obligation-discharged / approve`。最終head `46251ad81d54548a80f7d5240dcf910f1cc23bcb`、
merge `a06669caf8b6983068a32f7ab81b5d390bb42b22`、CI全7pass。
[Issue同期](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5321#issuecomment-6107930962)。
全GOALはtarget-proof-checkpoint。C–E、Formal移植、Research全体buildは未実施。

```yaml
ledger_type: target_cycle_result
goal: G-136-aat-atlas-gluing-width
cycle: 3
goal_blob_sha: dbc5b584987a1f3e1987125b7ccde2e361a89533
base_oid: a06669caf8b6983068a32f7ab81b5d390bb42b22
tracking_issue: 5321
report_path: research/reports/G-136-aat-atlas-gluing-width.md
selection:
  proof_state_ref: PR5329 B受理とIssue同期6107930962
  proof_dag_predecessors: [Aの原始SESと六square, Bの標準LESとδ自然性, G133 ShortExactFive/oldH1Equiv, mathlib標準snake]
  milestone: GOAL Cの同じ実比較の一次欠損をQ/Pと交差Zから正確に同定
  proof_obligations: [実Q/P短完全列, 同じH0/H1比較によるq/pと可換図式, 実核余核snake全列と代表式, 局所J零からp単射とcoker p≃Z, 実phantom同型とhidden短完全列, 次元式と零欠損iff, 通常Uの旧H1商と同じ核余核への接続]
  exit_criteria: [任意原始MとA/Bから一般Q/Pとsnakeの全前提を放電, 各射の代表式と標準snakeδ同定, 局所J零以外の交差比較同型を追加しない, 実phantom/hiddenとZの射を保つ, 次元式と両方向iff, 対象focusedと全新規実宣言公理監査]
  selection_reason: Dの実Law有限和とEの非零MV生成元が使う欠損分解を先に閉じる
  expected_result_type: proof-obligation-discharged
  lean_targets: [AtlasGluingWidth/QuotientKernelRow.lean, AtlasGluingWidth/LinearSnake.lean, AtlasGluingWidth/PairHomology.lean, AtlasGluingWidth/GluingDefect.lean, AtlasGluingWidth/PrimitiveGluing.lean]
  risks: [標準snakeの成分を実LinearMap.ker/range quotientへ輸送, δ代表式の符号, localH1同型からp単射とZへの同定, 通常Uの同じ旧H1商と核余核transport]
  unchecked: [Cの登録実装と正式査読, D/Eの全構成]
```

## C の条項別対応と受理候補宣言

| 固定要求 | 実構成・宣言 | 前提の出所・使用先 |
| --- | --- | --- |
| 実二領域H⁰/H¹と差制限 | `PairHomology.homologyIso_fst/snd`, `homologyMap_pair`; `PrimitiveGluing.difference`, `difference_natural`, `difference_comparison`, `qProductEquiv`, `pProductEquiv` | 同じ原始射影を保つ全次数積同型。Qの商代表元とPの元の積成分を固定。粗細squareは原始Mの同じ図式。 |
| 実Q/P SES | `QuotientKernelRow.Q/P`, `inclusion`, `projection`, `row_shortExact`, `inclusion_mk`, `projection_val` | QはH⁰差制限像のliteral quotient、PはH¹差制限のliteral kernel。Aから生成したSESとBの三位置LES完全性をG133 ShortExactFiveへ渡す。 |
| 同じq/pと二行SES図式 | `QuotientKernelRow.q/p`, `q_mk`, `p_val`, `inclusion_natural`, `projection_natural`, `rowMap` | qは同じ交差H⁰比較の商射、pは同じ二領域H¹比較の核制限。H⁰比較を零や任意射に置換せず、元のcomm23とδ自然性を使用。 |
| 標準snakeの実核・余核 | `LinearSnake.snake`, `K1/K2/K3`, `C1/C2/C3`, `first/second/connecting/fourth/fifth`, `exact1/2/3/4` | 元の二行SESから標準SnakeInputを生成。標準kernel/cokernelを普遍性による包含・商を保つ同型でliteral kernel/range quotientへ移す。 |
| 標準δの代表式・存在・独立性 | `LinearSnake.connecting_representative`, `connecting_lift`, `connecting_choice_independent`; `GluingDefect.connecting_representative`, `connecting_lift` | 標準δ_eqへ同じ持ち上げ・貼り合わせを渡す。任意ker p元の持ち上げは元のepiとexactから生成し、符号は標準δそのもの。任意二選択は同じδの値へ一致。 |
| 通常Uの同じT/Ph/Hdと全snake列 | `PrimitiveGluing.regionUnion_natural`, `phantomEquiv`, `hiddenEquiv`, `first/second/connecting/fourth/fifth`, `first_injective`, `exact1/2/3/4`, `fifth_surjective`, 各 `*_val/*_mk` と `connecting_lift` | Aの全セル和等号とBのregionUnionHom_eqに沿う全H¹射の同定。G133 oldH1Equiv_naturalから元のH¹商の実核・実余核へ戻し、全位置完全性と代表式を輸送。 |
| 局所J零の放電 | `PairHomology.oldH1_bijective_iff`, `homologyMap_pair_bijective`; `PrimitiveGluing.cell_local_bijective`, `local_bijective` | 同じA/BのblockDefect=0から元のH¹射全単射を導き、その積同型で実二領域標準比較を全単射にする。交差比較同型は追加しない。 |
| p単射、実coker pとZ | `QuotientKernelRow.p_injective`, `Z`, `zMap`, `p_z_exact`, `zMap_surjective`, `cokerPZEquiv`, `cokerPZEquiv_mk` | 同じ局所比較の逆と粗差制限で射を構成。Zは元の粗差制限像と元の交差H¹比較核の交差。像・核・全射を元のsquareで証明する。 |
| 実phantom同型と実hidden/Z SES | `GluingDefect.phantomEquiv`, `hiddenZRow_shortExact`; `PrimitiveGluing.localPhantomEquiv`, `oldHiddenRow_shortExact`, `oldHiddenRow_f_mk/g_mk` | ker p=0から標準snakeの前後を使う。通常Uの既存literal余核を中間項にするSES。包含は細δ、射は細制限・同じ局所逆比較・粗差制限の代表式。 |
| 同じJの次元式と両方向零条件 | `GluingDefect.shortExact_dimension`, `defect_dimension`, `defect_zero_iff`; `PrimitiveGluing.defect_standard`, `defect_dimension`, `defect_zero_iff` | G133実核商次元式と上の実同型/SESから導出。有限次元性は元の有限三項複体の標準homologyから生成し、新しいrank入力を置かない。 |

受理spineはこの対応表で名指しした構成・定理と、それを支える新規5sourceの全公開宣言。
cycle scaffold・新しい結論certificate・expected-rank fieldは追加していない。
`ShortExact`・自然な二行比較・局所H¹比較の全単射性は一般補題ではdirection-hypothesisである。
`PrimitiveGluing` の原始適用では `StandardRow.cellRow_shortExact`、同じ `cellRowMap`、
同じA/Bの局所J零からすべて生成し、完全性や交差比較同型を引数として追加していない。
局所J零そのものはGOAL C特殊化のdirection-hypothesisであり、Eの指定例で放電する義務は残る。

依存の使用版は固定mathlib `8f9d9cff6bd728b17a24e163c9402775d9e6a365`、Lean 4.28.0。
標準snake・kernel/cokernel普遍性・additive homologyFunctor/mapBiprod・線形exactの
同型輸送APIは型と適用条件を実読した。受理済みA/BはPR5328/5329の同じ不変source、
G133はPR5269の `ShortExactFive`、`ZeroExtension.oldH1Equiv_natural`、`LinearConjugation`、
G134はPR5287の同じ `SubsetComparison`、既存欠損意味論は `blockDefect_eq_zero_iff_bijective`。
現在の実宣言と適用引数を照合し、受理記録は再利用資格、現在のsourceは適用の証拠とする。
DのLaw有限和とG135係数・fiber分解、Eの任意k指定原始族は引き続き未達。

## Cycle 3 result proposal

```yaml
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: 実Q/Pと同じq/p二行SES、全snake列と代表式、原始局所J零からp単射とcoker p≃Z、通常Uの同じ実phantom/hidden、J次元式と両方向零条件を構成
  exit_criteria_status: [任意原始MとA/BによるSESとsquareの放電, 全snake位置と元の核商, 標準δの代表式と存在と選択独立性, 元の局所J零から同じ局所比較同型, 元のZと実余核の同定, 通常Uの同じ全H1射とliteral核商, 次元式と両方向iff]
  split_reason: none
  completion_candidate: no
  lean_artifacts: [QuotientKernelRow.lean, LinearSnake.lean, PairHomology.lean, GluingDefect.lean, PrimitiveGluing.lean]
  evidence: [C条項別対応表の実宣言]
  claim_mapping:
    theorem_names: [PrimitiveGluing.exact1/2/3/4, PrimitiveGluing.connecting_representative, PrimitiveGluing.localPhantomEquiv, PrimitiveGluing.oldHiddenRow_shortExact, PrimitiveGluing.defect_dimension, PrimitiveGluing.defect_zero_iff]
    source_labels: [GOAL C, 設計exact-sequence §3–4]
    conjuncts: [実Q/Pと自然な図式, 実snake全列と代表式, 局所J零下の実核余核分解, 同じJ次元式と零iff]
    undischarged_assumptions: []
    acceptance_point: 原始Mと任意A/Bの同じ比較から生成し、通常Uの既存H1商と核余核に接続
    port_status: unported
audits:
  premise_delta:
    discharged: [原始cochain SESから実Q/P SES, 元のH0/H1squareとδ自然性からq/p, 標準snakeの全kernel/cokernel資格, 元の局所J零から同じL全単射, 同じ差制限によるcoker p≃Z, 元の通常U核商への同定]
    remaining: [Dの実Law和とG135接続, Eの全k原始族と特殊化前提放電]
  certificate_provenance:
    discharged: [AのcellRow_shortExact, 同じ原始cellRowMap, Q/Prow_shortExact, 標準SnakeInputの生成と普遍核商同型]
    unresolved: []
  proof_use:
    used: [標準LES三位置, 元の比較squareとδ自然性, 標準δ_eqと元のepi/exact, 実積射影と局所H1比較の全単射性, 元の差制限像と交差比較核, 全セル等号と同じ全Homの旧H1自然性]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [新規5sourceの個別focusedとmodule公理監査, 公式単一PrimitiveGluing focused, 累積全実宣言の明示公理照会, 共通scan]
  blocking_findings: [標準PR独立査読前]
  next_obligation: C正式受理後にDの同じ実Law比較とG135の同じ核余核へ接続
```

## Cycle 3 検証記録

新規5sourceの個別focused checkはすべてexit0。module公理監査は
QuotientKernelRow 29、LinearSnake 69、PairHomology 16、GluingDefect 32、PrimitiveGluing 56、
計202新規実宣言（うち178 source明示宣言）で標準公理のみ。
公式単一 `bash research/lean/check_research_modules.sh --focused ResearchLean/AG/AtlasGluingWidth/PrimitiveGluing.lean`
はexit0、56宣言、log SHA256 `0bf6ad62fb1a4a9da9395cc022c5b8920ddd47226fc275718f6ef09fb63d85fb`。
累積A/B/C全413実宣言（354 source明示、59生成）を単一非aggregate監査fileから明示
`#print axioms` で全件照会し、exit0、413unique、標準propext/Classical.choice/Quot.sound以内。
新規178明示宣言の完全修飾名も全件照合、欠落なし。log SHA256
`ce5963490b7d8d51e5f2a2f002659050d93c43d6e22cec6f8e6512a3ab595cd7`。
placeholder、hidden/BiDi、privacy、語彙、import方向、staged diff whitespaceはclean。
使用G133三sourceは固定参照版ed16acc…からdiff空。固定GOAL blobもdbc5b584…で不変。
Research全体build・aggregate・全file elaboration・Formal移植は実行していない。
正式4 lane査読、内容受理、CI、mergeはこのhead確定前の記録時点では未実施であり、PR監査へ同期する。

## Cycle 3 初回独立査読後の修正

初回固定head `51afa7c1f657cba8a03778e219f3c64f451d4824` の数学A/B・Lean A/Bは
いずれも `Minor issues`、中心0・非中心2。同じ2件を一括し、全lane受領後に修正した。
監査は [PR5330初回内容監査](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5330#issuecomment-6108314277)。
`PrimitiveGluing.coarseUnionEq/fineUnionEq` は同じ等号statementと証明を
`theorem` として公開する。`LinearSnake.conjugate_refl_left/right` は査読が名指した
恒等同型の正規化APIであり、`PrimitiveGluing.exact1–4` はこれを使って輸送を正規化する。
元の実射・完全性のstatement・入力・import・instanceを保持した。
この修正記録は内容受理を表さず、修正後確認を固定PR headへ同期する。

修正前の検証記録は上の初回headに対応する。修正後の個別
`LinearSnake` checkはexit0、71宣言、標準公理のみ、log SHA256
`807439841eb1f493f1e42fc17f5e676b72399aecc0d30d6c2acca313664392d0`。
`PrimitiveGluing` とその公式単一focusedはexit0、56宣言、標準公理のみ。
公式focused logの内容は初回と同じで、SHA256も
`0bf6ad62fb1a4a9da9395cc022c5b8920ddd47226fc275718f6ef09fb63d85fb`。
修正後累積全415実宣言（356 source明示、59生成）を同じ単一監査fileで全件照会し、
exit0、415unique、標準3公理以内。新規180明示宣言の完全修飾名照合に欠落なし。
log SHA256 `12e8cf465c21c93afd759311a7942aa6203d34b6c6157e2bfdb3d1cc908b6bc3`。placeholder/Unicode/privacy/import方向/diffcheckもclean。

## Cycle 3 正式再査読1後の命名修正

固定head `797725fb2effd85eb4c7a92958c7fc5c0903b1d1` の正式再査読1は、
数学A/B・Lean Aが `No major findings`、Lean Bが `Minor issues`。
中心0・非中心1であり、新規公開等号theoremのsnake_case命名が残った。
[再査読1統合監査](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5330#issuecomment-6108458477)
に従い、上の履歴で旧名として記録した2宣言を
`PrimitiveGluing.coarse_union_eq/fine_union_eq` とし、全使用箇所を同期した。
statement・証明・比較射・仮定を保持する。宣言の削除・追加を伴うため直接対応
確認には回さず、固定headに対する新規4 laneの正式再査読2へ進む。
この記録は修正内容であり、受理を表さない。

改名後の個別PrimitiveGluingと公式単一focusedはexit0、56宣言、標準公理のみ。
公式focused SHA256 `0bf6ad62fb1a4a9da9395cc022c5b8920ddd47226fc275718f6ef09fb63d85fb`。
改名後の累積415実宣言を全件明示公理照会し、exit0、415unique、標準3公理以内、
180新規明示宣言の欠落なし。log SHA256 `9190e4c853a0c0fa921fdf728103028dee71f0cf01390a5ccf83dfdfc312b590`。
placeholder/Unicode/privacy/import方向/diffcheckはclean、固定仕様は不変。

## Cycle 3 正式受理

PR [#5330](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5330)、
head `0e0595402924c9a162e8dc2af546c55629b3d7ab`、
merge `0626e53e5ff4dd8e80756d0bf9be133e84c10feb`。
新規独立4 laneの正式再実行2はすべて `No major findings`、中心・非中心0。
[内容監査とroot全13回帰受理](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5330#issuecomment-6108600454)
がC全体を `proof-obligation-discharged` と判定し、
[Issue同期](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5321#issuecomment-6108614793)
に記録した。CI全7成功（38135557771/38135557765/Workers）。
全GOAL完了ではなく、D/Eは残る。

## Cycle 4 selection：同じ実Lawと係数・fiber分解

```yaml
ledger_type: target_cycle_result
goal: G-136-aat-atlas-gluing-width
cycle: 4
goal_blob_sha: dbc5b584987a1f3e1987125b7ccde2e361a89533
base_oid: 0626e53e5ff4dd8e80756d0bf9be133e84c10feb
tracking_issue: 5321
report_path: research/reports/G-136-aat-atlas-gluing-width.md
selection:
  proof_state_ref: PR5330最終受理・Issue5321同期・Cycle3全C実宣言
  proof_dag_predecessors: [受理済みA/B/C, G133有限族と実核商, G134実Law比較, G135係数余核SES]
  milestone: D全体の有限ラベル和と同じ通常Xの係数・fiber分解への接続
  proof_obligations:
    - 各label原始A/BセルSES・錐SES・Cを有限族へ集め、同じ標準delta・Q/Pを保持
    - 任意粗adequateLawから細adequacy、A/Bと各発生fiberの交差領域を生成
    - 各fiberを覆うとunion=fiber、実generatedLaw比較の全chain同定
    - 同じ実LawH1・核余核・全整数次数錐・有限直和・代表元とJ和へ接続
    - 任意通常Xの旧H1核商をG135同じdirectH1・unit核・係数余核SESへ接続
    - CのU実hiddenと係数SESの同じ中間商・全代表元・両方向零iffを照合
  exit_criteria:
    - D全条項・射と商・全整数次数・空index・同じ支持のlabel重複をLean構成
    - 全宣言focusedと公理照会・共通scan・条項前提対応・正式独立PR査読
  selection_reason: Cの実欠損をG134/G135同じ実診断へ接続し固定targetへの未接続nodeを消す
  expected_result_type: proof-obligation-discharged
  lean_targets: [FiniteGluing.lean, LawGluing.lean, CoefficientBridge.lean, LawDefect.lean]
  risks: [同次元置換, 細adequacy追加入力, label重複消去, 旧H1と標準H1混同, 真Iへの通常fiber分解の誤適用, suppliedSES, delta符号, 下流API不足]
  unchecked: [D構成と接続の実装・検証・独立査読]
```

G135は受理PR5318 head `3f4524e2f01dfb924c063478bd3161c8a3683db2`、
merge/再利用参照 `ed16acc02229fdfe3846303de341d600878f03dc`。
[全目標受理記録](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5290#issuecomment-6078348119)
と[独立最終査読](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5318#issuecomment-6077753512)、
[root完了判定](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5318#issuecomment-6078269788)
を再利用資格として固定した。使用する現在の型・必要定義・適用引数は実読し、当該sourceの参照版との差分は空。
`DefectMaps.lean` SHA256 `0d45260ccf0bc021c223c1a5c8b5fa09288bfd728684fab5af13513b3d3d4449`、
`DefectShortExact.lean` `91d48bcd53b9979e35f93f5bee351d0ac48ac6c6432bbf8e435ac770e987d4c8`、
`DefectDiagnostics.lean` `bd3d93c50341909af0ad968c8dec37ae7a591bfeaf1500e9a2a583ac67977504`。
G135と今回のFormalはunported (Research-proved)。E任意k指定族と全GOALcompletionは今回の到達点に含めない。

## Dの条項別対応と受理候補spine

以下の新規namespaceは `AAT.AG.AtlasGluingWidth` の下にある。
Dの一般Law入力は同じ `laws` と粗adequacy `ha`。細adequacyを追加入力にしない。

| 固定要求 | 実宣言と射の対応 | 出所と使用先 |
| --- | --- | --- |
| 各発生labelでA–C | `LawGluing.labelA/labelB`, `coarseLabelRow/fineLabelRow`, `labelComparison`, `label_qp_shortExact` | 元fiberとA/Bの集合交差を使い、受理済みPrimitiveGluingと原始セルSESを適用。真Iは選択セル交差のまま。 |
| 全labelの同じcochain SESと図式 | `FiniteGluing.row_shortExact/rowMap`, `LawGluing.coarseRow_shortExact/fineRow_shortExact/comparison` | 成分の単射・完全性・全射を原始Aから生成。一般hRは方向仮定だがLaw適用では全件放電。 |
| 標準δ・実Q/Pと自然性 | `FiniteGluing.qEquiv/pEquiv`, `inclusion_component/projection_component/connecting_component`, `q_component/p_component` | 同じH⁰差制限のrange quotientとH¹差制限kernel。δは標準SESのδ_naturalityから成分化し符号を保持。 |
| 粗adequacyから細adequacy | `LawGluing.fine_adequate` | G133 `adequate_of_coarser` に同じh/haを渡す。以後全Law射の細入力をここから取得。 |
| fiber全体への合併・全chain同定 | `LawGluing.fiber_union/fine_fiber_union`, `coarseBlockIso/fineBlockIso/block_natural`, `coarseLawIso/fineLawIso/law_natural` | 覆いhcはDの方向条件。G134の混在Mに対する全三次数block同定と `lawZeroExtension_square` を使い、同じgeneratedComparisonHomを保つ。 |
| 同じ実LawのH¹と核余核 | `LawGluing.coarseH1Equiv/fineH1Equiv/h1_natural`, `phantomEquiv/hiddenEquiv`, `phantomFamilyEquiv/hiddenFamilyEquiv` とval/mk | G133 oldH1Equivから標準H¹へ移し、実Law比較の核・商から同じ各labelの核・商へ戻す。 |
| 同じLaw診断の有限和・重複度 | `LawGluing.defect_subset_sum/defect_gluing_sum` | G134 `lawH1Defect_subset_sum` の同じfiberJに戻す。添字は全LawValueLabelのまま、同じ台の異なるlabelを圧縮しない。 |
| 同じ実Law錐の全整数次数と実局所直和 | `LawGluing.lawConeIso/lawConeFamilyIso/lawConeDirectSumIso/lawConeHomologyEquiv`, `coneRow_shortExact`, `actualConeRowIso/actualConeRow_shortExact/actualCone_les` | 成分はBの実 `coneBiprodRow`。全Law標準錐が合併項。G133 `cone_short_exact` は同じgeneratedLaw零延長射に適用でき、隣接次数を保持する。 |
| 錐の標準δ・持ち上げ・微分・貼り合わせ | `LawGluing.actualCone_connecting_natural/actualCone_lift` | 同じ短複体同型のδ_naturalityとCohomologyRepresentativesの生成持ち上げを使い、実Law錐cocycle classと標準δの等号まで得る。 |
| 実Lawの全snakeと代表式 | `LawDefect.first/second/connecting/fourth/fifth`, `exact1–4`, `first_injective/fifth_surjective`, `first_val/second_val/fourth_mk/fifth_mk/connecting_representative/connecting_lift` | Cの同じQ/P二行SESと全snakeを、実Lawの核商同型に沿って輸送。H¹持ち上げは同じ粗Law class。 |
| labelごとの局所J零下のLaw欠損 | `LawDefect.local_bijective/localPhantomEquiv`, `localHiddenRow_shortExact/oldHiddenRow_shortExact`, `oldHiddenRow_f_mk/oldHiddenRow_g_mk`, `defect_dimension/defect_zero_iff` | 各labelのhA/hBはCと同じ方向条件。有限族比較の全単射を成分から導出し、実Lawのliteral hiddenを中間項とする。交差比較同型を追加しない。 |
| 任意通常XのG135同じ核商 | `CoefficientBridge.phantomEquiv/hiddenEquiv/phantomUnitEquiv` とval/mk/symm_mk | G135 `directH1_old/directKernelUnitEquiv` の同じu/Tへ接続。任意XなのでA/B/Uを含む。真Iには適用しない。 |
| 同じ実hiddenの係数・fiber SES | `CoefficientBridge.coefficientRow_shortExact/oldCoefficientRow_shortExact`, `oldCoefficientRow_f_mk/oldCoefficientRow_g_mk_val` | G135の実evaluationH1/fiberRestrictionH1を保つ。原係数余核とkerτの実射を旧H¹実余核に輸送する。 |
| 二方向分解の同じ中間商と判定 | `CoefficientBridge.union_hidden_same/union_zero_iff` | CのUの実hiddenとG135係数SESの中間項はliteral等号。q/Z条件とunit/τ条件は同じJ零を介する両方向同値。両SESの端点相互同型は主張しない。 |

### D material premise・provenance・proof-use

| 前提・中間構成 | 分類 | 放電・実使用 |
| --- | --- | --- |
| T0 Source有限、qc/qf/h、Nc/Nf、混在M、ℚ | ambient-boundary | 原始入力。A/B/Cの領域生成・全Hom・有限セルH¹をそのまま使う。 |
| lawsと粗adequacy ha | ambient-boundary | Dの任意入力。ha/hはfine_adequateと同じ発生fiberの逆像・block比較に使用。 |
| 細adequacy、fiber選択、全三次数block同定 | discharge-required | fine_adequate、labelA/B、fiber_union/fine_fiber_union、block_naturalから生成。 |
| hc：各fiberがA∪Bに含まれる | direction-hypothesis | 固定Dで全Lawへ戻す場合の覆い条件。fiber_unionから全chain/H¹/錐同型に使用。未覆いの場合も各label原始行は構成できる。 |
| labelごとのhA/hB：同じ実局所J零 | direction-hypothesis | C特殊化の方向条件。PrimitiveGluing.local_bijective→FiniteGluing.homology_bijective→LawDefect.local_bijective→実核同型・hidden/Z SES・両方向零iff。 |
| 成分SES・有限族SES・Q/P SES・snake・錐SES | discharge-required | A/B/C受理生成定理→FiniteGluing.row_shortExact→LawGluing各行→LawDefect全列。完全性fieldを一般Law入力へ追加しない。 |
| 全LawH¹と核商・有限直和 | discharge-required | 全chain law_natural→oldH1Equiv_natural→h1_natural→LinearConjugation→FiniteLinearFamily。全商代表元のval/mkを保持。 |
| 局所逆比較・coker p≃Z・有限次元 | discharge-required | C受理定理と各labelの局所J零、有限セルのzeroExtension homology、有限族homologyEquivから生成。追加vanishing・exactness・intersection bijectivityはない。 |
| 通常XのdirectH1・係数SES・実H¹商 | discharge-required / reviewed predecessor | G135受理済み同じM/Xのsource型と適用引数を実読。directH1_old→核商輸送、実余核包含・射の代表元へ接続。 |

新規structure/axiom/instanceの結論fieldはない。有限族の元は全発生labelの関数であり、
空indexの場合も同じ関数空間・商・短完全列を扱う。同じ台の複数labelは別成分として残る。
任意A/Bは原始幾何の後で量化する。部分像・K1・原始incidence・符号を減らす選択は行わない。
本cycleのspineは新規4sourceの全明示宣言で、cycle scaffoldはPR外の検証script/logだけである。
全修飾名とsource版を検証記録・PR監査で固定する。

## Cycle 4 result proposal

```yaml
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: Dの各label原始行と有限族・同じ実generatedLaw全chain/H1/錐/核商/診断和・通常Xの同じG135係数分解を接続
  exit_criteria_status: [上表のD全条項と代表元・両方向, 全整数次数, 空indexとlabel重複を保持, focusedと公理照会・scanは下の検証記録, 正式独立査読はPR固定headで実施]
  split_reason: none
  completion_candidate: no
  lean_artifacts: [FiniteGluing.lean, CoefficientBridge.lean, LawGluing.lean, LawDefect.lean]
  evidence: [D条項別対応表の全実宣言]
  claim_mapping:
    theorem_names: [D条項別対応表とPR監査の全修飾名リスト]
    source_labels: [GOAL D, exact-sequence設計§5, 再利用G133/G134/G135]
    conjuncts: [上のD条項別対応表]
    undischarged_assumptions: []
    acceptance_point: 同じ実比較の全chainとH1・核商・標準錐の射を保持
    port_status: unported
audits:
  premise_delta:
    discharged: [細adequacy, 各label原始SESと有限族SES, 標準delta/Q/P/snake, 実Law全chain同定と核商, 実錐LES, 同じ通常Xの係数SES輸送]
    remaining: [E任意k指定原始対と全指定評価]
  certificate_provenance:
    discharged: [原始A/B/C生成定理と同じ有限族, G134実Law同定, G135実directH1と係数SES]
    unresolved: []
  proof_use:
    used: [h/haから細adequacyとfiber逆像, hcから元全Lawblock, 原始SESから有限族とQ/P・snake, 局所J零から同じ比較逆とZ, directH1_oldと実係数射から同じ核商]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [下記focused・全宣言公理照会・共通scan]
  blocking_findings: [標準PR独立査読前]
  next_obligation: D正式受理後にE任意k指定族と同じLaw幅・MV発火を構成
```

## Cycle 4 検証記録

新規4sourceの個別focused checkは全てexit0、各module時点の公理監査は
FiniteGluing 23、CoefficientBridge 16、LawGluing 56、LawDefect 33で標準公理のみ。
新規source明示宣言118（23/16/50/29）は全件をspineとする。
公式単一 `bash research/lean/check_research_modules.sh --focused ResearchLean/AG/AtlasGluingWidth/LawDefect.lean`
はexit0、33宣言、log SHA256 `78b82966acc070b5101a2b3e5aec7d019642a9e600449b44e9ab940f53a36f16`。
同じ単一非aggregate監査fileから累積全546実宣言（474 source明示、72生成）へ明示
`#print axioms` を全件実行し、exit0、546 unique、標準propext/Classical.choice/Quot.sound以内。
新規118明示宣言の照合に欠落なし。新規実宣言は131で、module末尾時点以後に下流で生成された
LawGluing congr_simp 3宣言も全照会へ含める。log SHA256
`aecf0f345e0a380ea8cb89d5f7b45b632865d20850389767f4a89504d22b3b87`。

| source | SHA256 | 明示宣言数 |
| --- | --- | --- |
| `FiniteGluing.lean` | `dae447da3fc8ee8aef8dbe8fb2d60efe0389126b861584d8e4018f33cc382887` | 23 |
| `CoefficientBridge.lean` | `5449d78aabe584ed3cc3306590eb58422e02b53871f94bf539476cb9f3dc0231` | 16 |
| `LawGluing.lean` | `f3a792d7439ba465cc8f317332f5313104085177f48f762fca4fd299e7f1785d` | 50 |
| `LawDefect.lean` | `da07f9a5310b872d570c7f9b8761ce010cd3319ae8fe0bd158433664a4edde53` | 29 |

placeholder・hidden/BiDi・privacy・語彙・diff whitespaceはclean。reportの方針説明中の検査語は文脈で除外。
Research import方向gateはexit0（228本体moduleを静的走査）。固定GOAL/designとの差分は空。
今回使用したG133/G134/G135の17 source版は固定再利用参照ed16acc…とbyte同一で、
型・必要定義・適用引数・今回のproof-useを実読した。Lean4.28/mathlib8f9d9cff…を使用。
Research全体build・aggregate・全file elaboration・Formal移植は実行していない。
正式4 lane査読・内容受理・CI・mergeはこの記録では未実施であり、PR監査とIssueへ同期する。
