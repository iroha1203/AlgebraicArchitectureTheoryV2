# G-136 証明記録

固定 GOAL・設計・共通基準: `636ea3d45558fd0e511e3184cfa74ab1c23142c0`。
GOAL blob: `dbc5b584987a1f3e1987125b7ccde2e361a89533`。
既存宣言の参照版: `ed16acc02229fdfe3846303de341d600878f03dc`。
追跡: [#5321](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5321)。

## 現 proof obligation

T0・A–E は固定 target を維持する。初回 selection は実装前の開始報告で固定した。
A は PR #5328、merge `bb80b4068979dd1ecca354d8cebe9cad66f54e16` で部分受理済み。
現在は B の標準零延長・錐 SES と全整数次数 LES を到達点とする。
B の錐 SES/LES は Cycle 2 の受理候補として構成中。
C の Q/P と snake、D の実 Law と係数/fiber 接続、E の任意 k の族は未実装。
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
