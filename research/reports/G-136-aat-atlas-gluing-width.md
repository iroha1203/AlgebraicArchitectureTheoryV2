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
D は PR #5332、merge `48482786950efee29b4e7f6fb3b128f0412e891f` で受理済み。
Eの全幅群は PR #5333、merge `282f056b988b6b9a76239c0a402346e18dc18aa5` で部分受理済み。
Cycle 6では残る同じMV標準delta・Q/P/Z・hidden/G135生成元と指定回帰例の実装が通り、
全固定targetの完了候補を監査する。初回PR前には標準PR査読と別の全GOAL最終4本査読は未実施だった。
初回内容査読の非中心API修正とその検証は後述し、最終判定は固定headのPR監査コメントへ置く。
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
| `LawGluing.lean` | `53efc5eea14bdb7bed1551d870f650962b7340be2ac504556297cb35baf3d741` | 50 |
| `LawDefect.lean` | `da07f9a5310b872d570c7f9b8761ce010cd3319ae8fe0bd158433664a4edde53` | 29 |

placeholder・hidden/BiDi・privacy・語彙・diff whitespaceはclean。reportの方針説明中の検査語は文脈で除外。
Research import方向gateはexit0（228本体moduleを静的走査）。固定GOAL/designとの差分は空。
今回使用したG133/G134/G135の17 source版は固定再利用参照ed16acc…とbyte同一で、
型・必要定義・適用引数・今回のproof-useを実読した。Lean4.28/mathlib8f9d9cff…を使用。
Research全体build・aggregate・全file elaboration・Formal移植は実行していない。
正式4 lane査読・内容受理・CI・mergeはこの記録では未実施であり、PR監査とIssueへ同期する。

## Cycle 4 初回独立査読後のdocstring修正

固定head `11d1d172a81a76c15abcfd11a4e0b33e230f39bc` の初回査読は、
数学A・LeanBが `Minor issues`、数学B・LeanAが `No major findings`。
中心0、非中心1の重複指摘を全lane受領後に一括して修正した。
[標準PR内容監査](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5332#issuecomment-6108944832)
に従い、`LawGluing.cone_les` の説明を覆い条件なしの各label地域合併錐族へ限定し、
全Law標準錐のLESはhcを持つ `actualCone_les` に対応することを記載した。
statement・def本体・proof・import・instance・宣言集合は変更していない。
上のLawGluing source SHAはdoc修正後に同期した。公理logは同じ全宣言・証明の検証であり、
修正前後で数学部分が不変なことを直接対応確認へ渡す。
この記録は修正内容だけであり、内容受理・mergeを表さない。

修正後LawGluing単一focusedはexit0、56宣言、標準公理のみ。log SHA256 `6db3f0280085ecf721c9d60acd5df3375c6f2484f8d099f9c70636d2d0733870`。

## Cycle 4 正式受理

D全体は[最終監査](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5332#issuecomment-6109044624)
で有資格のdoc修正直接確認とroot再統合を経て受理した。exact head
`fd5cacd693397f3e35db5f2d29f43a443e7c6d64` の全7 CI成功後、PR #5332を
merge commit `48482786950efee29b4e7f6fb3b128f0412e891f` としてmergeした。
[Issue同期](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5321#issuecomment-6109056955)。
A–D受理済み、Eと累積最終completionは未完。Formal unported (Research-proved)。

## Cycle 5 selection（実装前固定）

```yaml
ledger_type: target_cycle_result
goal: G-136-aat-atlas-gluing-width
cycle: 5
goal_blob_sha: dbc5b584987a1f3e1987125b7ccde2e361a89533
base_oid: 48482786950efee29b4e7f6fb3b128f0412e891f
tracking_issue: 5321
report_path: research/reports/G-136-aat-atlas-gluing-width.md
selection:
  proof_state_ref: Issue5321comment6109056955とCycle4正式受理
  proof_dag_predecessors: [A/PR5328, B/PR5329, C/PR5330, D/PR5332, 固定G133/G134/G135再利用]
  milestone: E任意kの指定cycle/path原始対の低幅H1一致・一様零欠損分離・同じLawとMV/係数非零生成元
  proof_obligations: [指定原始表とK1・reading全field, 一般閉路periodと累積積分, 全真部分集合forest/pathのd0全射, 同じ全X実H1比較とJ, 全低幅明示同型と可換性および判定不能, 全発生label幅の任意Law族と定数/indicator両クラス, 同じI二点と空領域交差・Q/P/Z・delta符号とhidden実商, G135同じUの係数/fiber生成元と局所A/B条件, k0空観測と幅0Law]
  exit_criteria: [固定witnesses§1–4全評価を任意kでLean証明, 実比較・実商・両方向/代表元の条項対応, 期待rank/Jを原始fieldへ入れない, 全新規/累積宣言の公理監査とfocused/scan, 正式PR内容監査と累積最終completionは別gate]
  selection_reason: 未完E全群を同じ指定有限入力から閉じて全GOALのproof distanceを零へ縮める
  expected_result_type: proof-obligation-discharged
  lean_targets: [AtlasGluingWidth/WidthInput.lean, WidthIntegration.lean, WidthHomology.lean, WidthLaw.lean, WidthMayerVietoris.lean]
  risks: [一般nのwrap積分とn2K1, selectededge零延長補正の不変性, 旧H1商と標準H1/deltaの実同定, indicator補集合と全発生ラベル, sameMV/G135類照合]
  unchecked: [E構成/全証明/代表元/公理・独立内容監査/累積completion未実施]
```

## Cycle 5 到達点と途中分割

元のselection・終了条件は上に保持する。独立に再利用できる到達点として、
任意nの閉路積分から指定全幅対の全X診断・全低幅観測と実Law分離までが完成した。
この一般族の証明と、同じ族を標準MV連結射・G135係数SESへ輸送する代表元監査は、
原始graph/periodと標準homology/snake/fiberという異なる依存領域へ広がる。
既に6source・132明示宣言を持つ全幅構成を固定し、後者の全射・商・符号・代表元接続を
次cycleで独立に監査可能なまとまりとして進める。未完Eを完了と呼ぶために終了条件を縮めない。

| 固定条項・指定評価 | 実宣言（namespace `AAT.AG.AtlasGluingWidth.Width`） | 状況 |
| --- | --- | --- |
| E/witnesses§1 共通C/Source/reading、π=fst、粗一点、細v/w・a/b、plus=a0削除、原始全field | `Concept`, `Source`, `coarseReading`, `fineReading`, `coarser`, `factor`, `Edge`, `left`, `right`, `coarse`, `fine`, `hereditary`, `comparison` | 構成 |
| K1 singleton辺台と全選択式 | `edge_support`, `chart_selected`, `edge_selected`, `factor_region` | 原始台/端点から生成 |
| 一般nの一周period、境界零、period核=微分像、指定a0 period1 | `period_difference`, `sum_range_concept`, `cumulative_succ`, `cumulative_full`, `difference_potential`, `period_ker`, `period_generator`, `period_surjective` | 任意n、wrapを含む一般証明 |
| 全真部分集合forestとplus全領域の実H¹零 | `extendEdges_selected`, `selected_d0_surjective`, `proper_d0_surjective`, `plus_d0_surjective`, `proper_H1_zero`, `plus_H1_zero` | 全辺値の原始関数を構成 |
| minus全領域の実商H¹≃ℚと同じa0生成元 | `fullCyclesEquiv`, `full_boundary`, `full_image`, `periodQuotientEquiv`, `fullH1Equiv`, `fullH1Equiv_mk`, `fullGenerator`, `fullGenerator_value`, `fullGenerator_ne_zero` | 同じ実境界商、全代表式 |
| 同じ原始全X比較/J評価、全k低幅明示同型/square/J | `actualMap`, `coarse_H1_zero`, `proper_actual_H1_zero`, `plus_actual_H1_zero`, `full_actual_H1_equiv`, `plus_defect`, `proper_defect`, `full_defect`, `size`, `size_positive`, `low_proper`, `width_fine_equiv`, `width_observation` | 全幅一般証明 |
| 観測同値で一様零欠損の異なる二入力、判定不能 | `LowEquivalent`, `width_lowEquivalent`, `width_uniform_separation`, `no_width_classifier` | 全入力上の判定の指定二入力への制限が既に矛盾 |
| 全発生label幅の同じ任意粗adequate Law、実H¹同型と比較/J | `fineAdequate`, `lawMap`, `coarse_law_H1_zero`, `fine_law_H1_zero`, `width_law_H1_zero`, `width_law_equiv`, `width_law_square`, `width_law_defect` | G133実fiber族同型/G134同じ比較へ接続 |
| 同じ定数LawでplusJ0/minusJ(0,1) | `constantLaw`, `constantAdequate`, `constantLabel`, `constantLabelsUnique`, `constantFiber`, `constant_plus_defect`, `constant_minus_defect` | G134実Law欠損和、唯一発生label |
| indicator両値クラスと補集合・空/全の幅超過 | `indicator`, `indicatorAdequate`, `indicatorFiber`, `indicatorTrueLabel`, `indicatorFalseLabel`, `indicatorFalseFiber`, `indicator_width`, `indicator_endpoint_fiber`, `indicator_endpoint_not_width` | 片クラスだけを幅に数えない |
| k0はn2の空領域観測、幅0Law族は空 | `size_zero`, `width_zero_region`, `empty_degrees_zero`, `width_zero_laws_empty` | n2四角形の同じ一般構成 |
| 同じminusのI二点・辺なし、領域交差は空 | `intersection_chart`, `intersection_edges_empty`, `intersectionChartEquiv`, `intersection_card`, `intersection_H1_zero`, `region_inter_empty`, `region_inter_charts_empty`, `intersectionH0Equiv` | 順序false=w−1/true=w0、原始セルから生成 |
| E/witnesses§4 Qc0/Qfℚ/P/Z0・H0差制限・標準delta符号・同じhidden/G135生成元 | 未実装 | 次cycleで元selectionの残義務を継続 |

本cycleの一般補題が受け取るperiod零、欠けたa辺、真部分集合、fiber真部分集合は方向仮定。
それぞれ補正cochain、missing jまたはplus削除a0、card幅k<n、全発生labelの幅条件から
`selected_d0_surjective`・`proper_d0_surjective`・`plus_d0_surjective`・`low_proper`・
`width_law_H1_zero` 内で放電する。原始構造fieldへ期待rank・診断・H¹零・同型を含めない。
`no_width_classifier` の観測不変性と正解性は反証対象の判定の条件であり、証人構成の入力ではない。

```yaml
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: E任意kの指定原始対・閉路積分・全X実H1/J・全低幅同型/squareとLaw幅/検出・真交差幾何を構成
  exit_criteria_status: [原始族/一般積分/実商/全観測/同じLawは上の実宣言, MV標準deltaとQ/P/Z・hidden/G135同じ類は未完]
  split_reason: 独立再利用可能な全幅分類定理群132明示宣言を固定し、別依存領域の標準MV/係数生成元接続を次cycleで監査可能にする
  completion_candidate: no
  lean_artifacts: [WidthInput.lean, WidthIntegration.lean, WidthHomology.lean, WidthObservation.lean, WidthLaw.lean, WidthIntersection.lean]
  claim_mapping:
    source_labels: [GOAL E, witnesses§1–3, witnesses§4真交差幾何]
    undischarged_assumptions: [E残条項の未実装義務]
    port_status: unported
audits:
  premise_delta:
    discharged: [指定原始全field, period積分と全forest/path, 全幅比較・実欠損, 全低幅同型, 全発生Law幅・定数/indicator, 真交差二点]
    remaining: [E標準MV/Q/P/Z/hiddenとG135同じ生成元・局所条件, 累積completion]
  certificate_provenance:
    discharged: [同じ元辺台/端点/微分から累積和と商同型, 同じ生成Law/fiber族とG134診断和]
    unresolved: []
  proof_use:
    used: [readingからπ, K1から選択, periodから原始関数, 非選択a座標から補正, 幅とncardから真部分集合, Law値fiber逆像から同じ全Law商]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  blocking_findings: [正式PR独立査読前]
  next_obligation: 同じ指定族のH0差制限/Q/P/Z・標準delta lift/glue・hidden/G135生成元照合を継続
```

## Cycle 5 spine declaration list（初回132・評価API追加3・移行先7、現142明示宣言）

新規6sourceの全明示宣言をspineとする。生成補助宣言は全公理照会に別途含める。

### WidthHomology.lean

```text
AAT.AG.AtlasGluingWidth.Width.selected
AAT.AG.AtlasGluingWidth.Width.generatorAt
AAT.AG.AtlasGluingWidth.Width.generatorAt_apply
AAT.AG.AtlasGluingWidth.Width.period_generatorAt
AAT.AG.AtlasGluingWidth.Width.extendEdges
AAT.AG.AtlasGluingWidth.Width.extendEdges_selected
AAT.AG.AtlasGluingWidth.Width.selected_d0_surjective
AAT.AG.AtlasGluingWidth.Width.proper_d0_surjective
AAT.AG.AtlasGluingWidth.Width.plus_d0_surjective
AAT.AG.AtlasGluingWidth.Width.proper_H1_zero
AAT.AG.AtlasGluingWidth.Width.plus_H1_zero
AAT.AG.AtlasGluingWidth.Width.fullEdge
AAT.AG.AtlasGluingWidth.Width.fullChart
AAT.AG.AtlasGluingWidth.Width.fullCyclesEquiv
AAT.AG.AtlasGluingWidth.Width.full_boundary
AAT.AG.AtlasGluingWidth.Width.full_image
AAT.AG.AtlasGluingWidth.Width.periodQuotientEquiv
AAT.AG.AtlasGluingWidth.Width.fullH1Equiv
AAT.AG.AtlasGluingWidth.Width.fullH1Equiv_mk
AAT.AG.AtlasGluingWidth.Width.fullGenerator
AAT.AG.AtlasGluingWidth.Width.fullGenerator_value
AAT.AG.AtlasGluingWidth.Width.fullGenerator_ne_zero
```

### WidthInput.lean

```text
AAT.AG.AtlasGluingWidth.Width.Concept
AAT.AG.AtlasGluingWidth.Width.Source
AAT.AG.AtlasGluingWidth.Width.coarseReading
AAT.AG.AtlasGluingWidth.Width.fineReading
AAT.AG.AtlasGluingWidth.Width.coarser
AAT.AG.AtlasGluingWidth.Width.factor
AAT.AG.AtlasGluingWidth.Width.Edge
AAT.AG.AtlasGluingWidth.Width.Chart
AAT.AG.AtlasGluingWidth.Width.left
AAT.AG.AtlasGluingWidth.Width.right
AAT.AG.AtlasGluingWidth.Width.coarseNerve
AAT.AG.AtlasGluingWidth.Width.fineNerve
AAT.AG.AtlasGluingWidth.Width.support
AAT.AG.AtlasGluingWidth.Width.coarse
AAT.AG.AtlasGluingWidth.Width.fine
AAT.AG.AtlasGluingWidth.Width.hereditary
AAT.AG.AtlasGluingWidth.Width.comparison
AAT.AG.AtlasGluingWidth.Width.region
AAT.AG.AtlasGluingWidth.Width.factor_region
AAT.AG.AtlasGluingWidth.Width.chart_selected
AAT.AG.AtlasGluingWidth.Width.edge_support
AAT.AG.AtlasGluingWidth.Width.edge_selected
```

### WidthIntegration.lean

```text
AAT.AG.AtlasGluingWidth.Width.Cochain
AAT.AG.AtlasGluingWidth.Width.difference
AAT.AG.AtlasGluingWidth.Width.difference_apply
AAT.AG.AtlasGluingWidth.Width.period
AAT.AG.AtlasGluingWidth.Width.period_apply
AAT.AG.AtlasGluingWidth.Width.period_difference
AAT.AG.AtlasGluingWidth.Width.sum_range_concept
AAT.AG.AtlasGluingWidth.Width.cumulative
AAT.AG.AtlasGluingWidth.Width.cumulative_succ
AAT.AG.AtlasGluingWidth.Width.cumulative_full
AAT.AG.AtlasGluingWidth.Width.potential
AAT.AG.AtlasGluingWidth.Width.successor_val
AAT.AG.AtlasGluingWidth.Width.difference_potential
AAT.AG.AtlasGluingWidth.Width.generator
AAT.AG.AtlasGluingWidth.Width.period_generator
AAT.AG.AtlasGluingWidth.Width.period_surjective
AAT.AG.AtlasGluingWidth.Width.period_ker
AAT.AG.AtlasGluingWidth.Width.difference_zero_constant
```

### WidthIntersection.lean

```text
AAT.AG.AtlasGluingWidth.Width.regionA
AAT.AG.AtlasGluingWidth.Width.regionB
AAT.AG.AtlasGluingWidth.Width.intersection
AAT.AG.AtlasGluingWidth.Width.one_ne_zero
AAT.AG.AtlasGluingWidth.Width.neg_one_ne_zero
AAT.AG.AtlasGluingWidth.Width.intersection_chart
AAT.AG.AtlasGluingWidth.Width.intersection_edges_empty
AAT.AG.AtlasGluingWidth.Width.intersection_faces_empty
AAT.AG.AtlasGluingWidth.Width.intersectionPoint
AAT.AG.AtlasGluingWidth.Width.intersectionChartEquiv
AAT.AG.AtlasGluingWidth.Width.intersection_card
AAT.AG.AtlasGluingWidth.Width.intersection_H1_zero
AAT.AG.AtlasGluingWidth.Width.region_inter_empty
AAT.AG.AtlasGluingWidth.Width.region_inter_charts_empty
AAT.AG.AtlasGluingWidth.Width.intersectionH0Equiv
AAT.AG.AtlasGluingWidth.Width.empty_degrees_zero
```

### WidthLaw.lean

```text
AAT.AG.AtlasGluingWidth.Width.fine_adequate
AAT.AG.AtlasGluingWidth.Width.lawMap
AAT.AG.AtlasGluingWidth.Width.coarse_law_H1_zero
AAT.AG.AtlasGluingWidth.Width.fine_law_H1_zero
AAT.AG.AtlasGluingWidth.Width.plus_law_H1_zero
AAT.AG.AtlasGluingWidth.Width.plus_law_defect
AAT.AG.AtlasGluingWidth.Width.width_law_H1_zero
AAT.AG.AtlasGluingWidth.Width.width_law_equiv
AAT.AG.AtlasGluingWidth.Width.width_law_square
AAT.AG.AtlasGluingWidth.Width.width_law_defect
AAT.AG.AtlasGluingWidth.Width.constantLaw
AAT.AG.AtlasGluingWidth.Width.constant_adequate
AAT.AG.AtlasGluingWidth.Width.constantLabel
AAT.AG.AtlasGluingWidth.Width.constantLabelsUnique
AAT.AG.AtlasGluingWidth.Width.constant_fiber
AAT.AG.AtlasGluingWidth.Width.constant_plus_defect
AAT.AG.AtlasGluingWidth.Width.constant_minus_defect
AAT.AG.AtlasGluingWidth.Width.indicator
AAT.AG.AtlasGluingWidth.Width.indicator_adequate
AAT.AG.AtlasGluingWidth.Width.indicator_fiber
AAT.AG.AtlasGluingWidth.Width.indicatorFalseLabel
AAT.AG.AtlasGluingWidth.Width.indicatorTrueLabel
AAT.AG.AtlasGluingWidth.Width.indicatorFalseLabel_value
AAT.AG.AtlasGluingWidth.Width.indicator_false_fiber
AAT.AG.AtlasGluingWidth.Width.size_positive
AAT.AG.AtlasGluingWidth.Width.indicator_width
AAT.AG.AtlasGluingWidth.Width.indicator_endpoint_fiber
AAT.AG.AtlasGluingWidth.Width.indicator_endpoint_not_width
AAT.AG.AtlasGluingWidth.Width.width_zero_laws_empty
AAT.AG.AtlasGluingWidth.Width.fineAdequate
AAT.AG.AtlasGluingWidth.Width.constantAdequate
AAT.AG.AtlasGluingWidth.Width.constantFiber
AAT.AG.AtlasGluingWidth.Width.indicatorAdequate
AAT.AG.AtlasGluingWidth.Width.indicatorFiber
AAT.AG.AtlasGluingWidth.Width.indicatorFalseFiber
```

### WidthObservation.lean

```text
AAT.AG.AtlasGluingWidth.Width.coarseH1
AAT.AG.AtlasGluingWidth.Width.fineH1
AAT.AG.AtlasGluingWidth.Width.actualMap
AAT.AG.AtlasGluingWidth.Width.coarse_H1_zero
AAT.AG.AtlasGluingWidth.Width.proper_actual_H1_zero
AAT.AG.AtlasGluingWidth.Width.plus_actual_H1_zero
AAT.AG.AtlasGluingWidth.Width.full_actual_H1_equiv
AAT.AG.AtlasGluingWidth.Width.defect_zero_domain
AAT.AG.AtlasGluingWidth.Width.plus_defect
AAT.AG.AtlasGluingWidth.Width.proper_defect
AAT.AG.AtlasGluingWidth.Width.full_defect
AAT.AG.AtlasGluingWidth.Width.low_coarse_equiv
AAT.AG.AtlasGluingWidth.Width.low_fine_equiv
AAT.AG.AtlasGluingWidth.Width.low_square
AAT.AG.AtlasGluingWidth.Width.low_defect
AAT.AG.AtlasGluingWidth.Width.size
AAT.AG.AtlasGluingWidth.Width.size_neZero
AAT.AG.AtlasGluingWidth.Width.size_two
AAT.AG.AtlasGluingWidth.Width.size_gt
AAT.AG.AtlasGluingWidth.Width.low_proper
AAT.AG.AtlasGluingWidth.Width.width_fine_equiv
AAT.AG.AtlasGluingWidth.Width.width_observation
AAT.AG.AtlasGluingWidth.Width.width_uniform_separation
AAT.AG.AtlasGluingWidth.Width.LowEquivalent
AAT.AG.AtlasGluingWidth.Width.width_low_equivalent
AAT.AG.AtlasGluingWidth.Width.no_width_classifier
AAT.AG.AtlasGluingWidth.Width.size_zero
AAT.AG.AtlasGluingWidth.Width.width_zero_region
AAT.AG.AtlasGluingWidth.Width.width_lowEquivalent
```

## Cycle 5 検証と再利用（初回headの記録）

新規6sourceの個別focused elaborationは全てexit0。最終公式単一
`bash research/lean/check_research_modules.sh --focused ResearchLean/AG/AtlasGluingWidth/WidthIntersection.lean`
はexit0、16実宣言・標準公理のみ、log SHA256
`29b5bf348d100f902e82d43b6051b3c4f9f1715a4d3e43d9cc610a9f7ca8ea27`。

同じ現環境の全679実宣言（累積606明示・73生成、新規132明示・133実宣言）を列挙し、
全件の明示公理照会と照合した。既存677宣言は最終Law版からの全件照会、追加した
`intersection_card`・`empty_degrees_zero`は追加後の現環境で別の単一非aggregate監査fileから
明示照会した。既存677宣言のstatement/def/proofは追加時に変更していない。
全679 uniqueの現環境名との照合は欠落0・余剰0、新規132明示の欠落0、
全てpropext/Classical.choice/Quot.sound以内。新規生成1は`Width.period.congr_simp`。
全677照会log SHA256 `137c19f764be06df1b2757041e8ca83616f0f7d42dd50774887b2860853a1c69`、
追加2と現環境全名log SHA256 `3782532173919eb3570b75dc7238b53511a4124b90c6966434c3ad54ac206668`。

| source | SHA256 | 明示宣言数 |
| --- | --- | --- |
| `WidthHomology.lean` | `58419a42c3aa76a764d07e25ee90f2119d33c3ba1f4974b82ec11d8d4082b113` | 21 |
| `WidthInput.lean` | `56cd164d1e4a7f841c96c15a49d2ce8254161fbedc6ef6afda65391e9042609b` | 22 |
| `WidthIntegration.lean` | `4a5f8341ab0abfdfa74c5f7cf452b31fda18d2241f7a979f7df3f2d2fc9bcc91` | 16 |
| `WidthIntersection.lean` | `9fcd4b3ca89a5bbbb884fea8206bdeec667f1b7344bd35ff3ce738c266df99de` | 16 |
| `WidthLaw.lean` | `deedad0af17afccb413444d08961286e0d3b54a37169ce2a5f518d1382a17cc8` | 29 |
| `WidthObservation.lean` | `cf652acae22db6c70dfee05ca17c0c646639b44df8ab22febafd0018f7f00e78` | 28 |

再利用は固定ed16acc…と使用する6sourceがbyte同一。G135の
[受理監査](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5318#issuecomment-6078269788)
から`PhiInterval.h1_subsingleton_of_d0_surjective`を実d0全射へ適用、
G133 [受理PR5269](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5269) の
`LawFiberH1Family.lawFiberH1FamilyEquiv`を全発生labelの同じ実商へ適用、
G134 [受理PR5287](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5287) の
`LawComparisonFiberDiagnostics.lawH1Defect_subset_sum`を指定定数Lawの唯一fiberへ適用する。
G107 [受理PR3994監査](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/3994#issuecomment-5279154319)
の`IndicatorLawFamily`のeval/adequacy/descent/trueLabelを現在の型と引数で読み、
false発生label/補集合fiber/全幅条件を新規に証明した。`ASubnerveReduction`と
`TwoPhase.CohomologyComparison`の同じtargetSubsetComplex・labelValueFiber・境界商を使う。
既存A–D sourceは受理版から不変。Lean4.28/mathlib8f9d9cff…のZModと有限和・商同型APIへ依存する。

共通placeholder/hidden/BiDi/privacy/whitespace scanはclean。本体からResearchへのimport hit0、
通常import方向gateはexit0（本体228moduleの静的確認）。Researchだけを仮想rootとした
追加試行は外側のFormal importを解決できないため検証として採用しない。
固定GOAL/designは変更していない。Formal移植、Research全体build/aggregate/全file elaboration、
全GOAL最終completionは未実施。今回の独立4 lane内容査読・CI・受理はPR固定headで行い、
この記録はその自己代替ではない。残るE接続を次cycleで継続し、Issueをcloseしない。

`difference_zero_constant` は同じ全閉路のH⁰計算に使う独立一般補題として証明した。
Eの残るMV H⁰差制限の輸送は、この補題の存在だけで完了とはしない。

## Cycle 5 初回査読と一括修正

PR #5333初回head `2ca4cd0420525858f4df263772705c1d5932ff96` の
[標準review-prから数学2・Lean2への独立監査](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5333#issuecomment-6109458785)
は全4本Minor issues、中心finding0、非中心4件（重複統合）。初回修正後の135明示spineは
上の初回132に名指し公開評価API3を加えた。

- 自明でない定義のImplementation notesと退けた代替案の理由を6sourceへ補完。
- `period_apply`・`difference_apply`・`generatorAt_apply`を定義側へ追加し、
  下流積分証明を既存`CellSelection.complex_d0_apply`と公開API経由へ変更。
- `fineAdequate`・`indicatorAdequate`を明示Prop型のtheoremへ変更し、不要なNeZero仮定を除いた。
  粗adequacyからの実放電経路とindicator evaluationは保持する。
- `LowEquivalent`のこの指定二入力では全4組が低幅同値となるためnegative instanceが
  存在しない理由を記載。一様零欠損の相違の証明は保持する。

全findingは一括対応した。Prop def/abbrevからtheoremへの宣言種別・透明性の変更について
直接対応資格を確定できないため、共有手順に従って新規4本の正式r1で確認する。
元selection/終了条件、proposed_result_type=proof-checkpoint、completion_candidate=noは不変。

初回修正後source（正式r1対象）:

| source | SHA256 | 明示宣言数 |
| --- | --- | --- |
| `WidthHomology.lean` | `f86de3020d3f95d41d08e760397bb4b79b3905a2a21a98adab429d885b28a073` | 22 |
| `WidthInput.lean` | `f25bfcb73be8dbae975da12c5881c34a9190a2c34b659ec4f48102201f27c7ed` | 22 |
| `WidthIntegration.lean` | `2f1c45e7fe855ab00a56a76d3bb4cac3ea7f5ba79b0482d01e7323b8d2716da4` | 18 |
| `WidthIntersection.lean` | `5809036f00abdde7d5ab7b5eafd2beb1c48ff53efd073a60b29c256c20964105` | 16 |
| `WidthLaw.lean` | `e490f0c816ec7558bc0b364eb38d01f2e11e7ae945340a1d25f83134001fbad6` | 29 |
| `WidthObservation.lean` | `4d96297494d19e12673bed95a034b67328ba8b8b74d3e6794b57e935cf4c2761` | 28 |

修正後の対象 `WidthIntegration`・`WidthHomology`・`WidthObservation`・`WidthLaw`・
`WidthIntersection` の個別focusedは全てexit0、最終出力にwarningなし。
公式単一focused `WidthIntersection.lean` はexit0・16実宣言標準公理のみ、
log SHA256 `29b5bf348d100f902e82d43b6051b3c4f9f1715a4d3e43d9cc610a9f7ca8ea27`。

現環境全682 unique（累積609明示・73生成、新規135明示・136実宣言）の
全件明示公理照会を同じ環境全名へ照合し、欠落0・余剰0・新135明示欠落0。
全依存はpropext/Classical.choice/Quot.sound以内。全件log SHA256
`f311eb1aa84e481f07d6baf490a3ca6af4ab7f974dee9f262bd84942ac2d8974`。

修正前CIは全7成功。Lean workflow run38141926112の実stepを確認し、Research
integrityでは方向・分離・fixture・public artifactが実行された。Formal build・
Formal axiom auditのstepはSKIPPEDであり、CI job名を実buildの証拠へ読み替えない。
修正後固定headのCIは別に確認する。Formal移植とResearch全体buildは未実施。

## Cycle 5 正式r1査読と一括命名修正

固定head `b698ff81ebfe4b68ff7d9b10b389ffe2679a7e0b` の
[正式r1統合](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5333#issuecomment-6109674660)
は全4本Minor issues、中心0。非中心は独立定理7件のsnake_case命名と、公開API3件の
spine所属ファイル表示。現在spineを実sourceのファイル別全名から再生成した。
品質§4.2に従って次の旧名をdeprecated alias（2026-10-11）で保持し、使用先を現名へ同期する。
固定GOALに旧名参照はなく、カードと設計の固定内容は変更しない。

| 旧名（deprecated alias） | 現名 |
| --- | --- |
| `fineAdequate` | `fine_adequate` |
| `constantAdequate` | `constant_adequate` |
| `constantFiber` | `constant_fiber` |
| `indicatorAdequate` | `indicator_adequate` |
| `indicatorFiber` | `indicator_fiber` |
| `indicatorFalseFiber` | `indicator_false_fiber` |
| `width_lowEquivalent` | `width_low_equivalent` |

現在spineは142明示（査読済み135を保持し、移行先の現名7を加えた）である。
statementの内容・強度、入力・比較・幅・結論は不変。関連defの証明参照名も変わるため
直接対応資格を確定できず、正式r2を新規数学2・Lean2で行う。
元selection/終了条件、proof-checkpoint、completion_candidate=no、残るE接続を保持する。

命名修正後source（142明示）:

| source | SHA256 | 明示宣言数（alias含む） |
| --- | --- | --- |
| `WidthHomology.lean` | `f86de3020d3f95d41d08e760397bb4b79b3905a2a21a98adab429d885b28a073` | 22 |
| `WidthInput.lean` | `f25bfcb73be8dbae975da12c5881c34a9190a2c34b659ec4f48102201f27c7ed` | 22 |
| `WidthIntegration.lean` | `2f1c45e7fe855ab00a56a76d3bb4cac3ea7f5ba79b0482d01e7323b8d2716da4` | 18 |
| `WidthIntersection.lean` | `5809036f00abdde7d5ab7b5eafd2beb1c48ff53efd073a60b29c256c20964105` | 16 |
| `WidthLaw.lean` | `bdc17d333d2f680af3f873820ab560ac2d9dd7082789a674a946122c0e4744f9` | 35 |
| `WidthObservation.lean` | `dce11a8a08b6901580f1865fa66965c724f0e9e86323646d317ce4bc53815b2f` | 29 |

命名修正後の個別 WidthObservation / WidthLaw / WidthIntersection と公式単一focusedは
exit0・warningなし。公式focused log SHA256 `29b5bf348d100f902e82d43b6051b3c4f9f1715a4d3e43d9cc610a9f7ca8ea27`。
現環境の全689 unique（累積616明示・73生成、新規142明示・143実宣言）を
全件明示公理照会し、現環境名・全明示名と突合した。欠落0・余剰0・新142欠落0、
全依存は標準3公理以内。全件log SHA256 `de4e521f627d193dab94968ecdf4549fc6ee913b822d2b33d300f2662d0ed893`。
共通placeholder/hidden/BiDi/privacy/whitespace scan clean、静的方向gate228module pass、
本体からResearch import0、GOAL/design/先行A–D/指定predecessor不変。
正式r2の独立査読と同head CIはこの記録の後に確認する。Formal移植・実build、
Research全体build/aggregate/全file elaborationは未実施。

## Cycle 5 受理点

[PR #5333](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5333) の最終head
`1be64c28554f2914b7dd7e4c681d9164638a3211`、merge commit
`282f056b988b6b9a76239c0a402346e18dc18aa5` を固定する。
[正式r2/root acceptance](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5333#issuecomment-6109828693)
は新規独立数学2・Lean2が全てNo major findings、中心/非中心0、全142明示実読、
全689公理照会一致/標準公理のみ、全13scenario再統合。同head全7CI成功。
[Issue受理記録](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5321#issuecomment-6109841105)
のcycle resultはproof-checkpointであり、元E全selectionと残義務を保持する。

## Cycle 6 selection（実装前）

```yaml
ledger_type: target_cycle_result
goal: G-136-aat-atlas-gluing-width
cycle: 6
goal_blob_sha: dbc5b584987a1f3e1987125b7ccde2e361a89533
base_oid: 282f056b988b6b9a76239c0a402346e18dc18aa5
tracking_issue: 5321
report_path: research/reports/G-136-aat-atlas-gluing-width.md
selection:
  proof_state_ref: PR5333#6109828693・Issue5321#6109841105・Cycle5残義務
  proof_dag_predecessors: [受理T0/A-D, WidthInput/Integration/Homology/Observation/Law/Intersection, G133標準endpoint/代表元, G135同じ原fiber制限・係数完全列]
  milestone: 同じ全幅指定minus族のMV発火とhidden・係数fiber生成元を接続してGOAL Eを閉じる
  proof_obligations:
    - 任意n>=2の実fine A/B/U H0核と粗A/B/I H0を元chart値から構成し、標準homologyへ輸送する
    - 同じ粗H0差制限(x,y)->x-yと細二点差制限(x,y)->(x-y,x-y)を全元で同定する
    - literal Qc零・Qfと有理数の全代表同型・q零、Pc/Pf零・Zbot、同じ局所JA/JB零を導出する
    - 指定真交差z=(0,1)の実liftと微分glueを生成し、標準deltaの符号込み像を同じa0実H1類へ同定する
    - 同じCのoldHiddenRow/cokerq包含の指定生成元を同じ旧H1商へ照合し非零を示す
    - 同じG135 X=A/B/UのactualPhiComplex・原順像係数・R/kerTauを構成し、同じa0類とMVhidden生成元を実射で照合する
    - 原始path/cycleから成分連結・順像係数有理数・H1/H2零・Tau零を生成し、局所unitbij/Tauinjを放電する
    - 設計witnesses§5のn2 H0次元相違とH1零、原始一点対二点の実標準coneH0非零回帰例を構成する
  exit_criteria:
    - 上の全一般nと指定size kについて同じ原始入力・実射・実商・全代表式・全方向がLeanで閉じる
    - Q/P/Zと標準delta lift/glue/符号、同じhidden/kerTau/a0の照合と局所条件が入力から放電される
    - 強化誤推論の指定原始回帰例を同じ実微分・標準coneへ接続する
    - 対象focused・対象全宣言公理・共通scanを通し、条項/前提/依存/spineを同期する
  selection_reason: Cycle5が閉じた全幅群を、受理A-Dの同じ射へ具体適用して最後の生成元輸送gapを閉じる
  expected_result_type: proof-obligation-discharged
  lean_targets: [WidthLocalH0, WidthMayerVietoris, WidthConnecting, WidthCoefficient, WidthRegression]
  risks: [真交差と集合交差の混同, 標準H0と旧核の輸送, delta符号, 同次元だけの類同定, Rを全PhiH1へ無条件置換, H1零からconnected/錐消滅を推論]
  unchecked: [選定群のLean実装・検証・正式PR査読, 累積全GOAL最終判定]
```

固定GOAL/design/common版636ea3d…、reuse版ed16acc…、Lean4.28/mathlib8f9d9cff…は継続する。
元Cycle5の全E終了条件を変更しない。内部API/ファイル分割は設計選択であり、
到達点を閉じるまで同じcycleで実装を反復する。累積全criteria照合前にcompletion candidateを出さない。

## Cycle 6 到達点と固定目標の対応

Cycle 5受理済みの任意k指定族を変えず、残るwitnesses§4を同じ原始比較の
真交差・標準MV連結射・旧H¹商・G-135原fiber制限へ接続した候補である。
namespaceは `AAT.AG.AtlasGluingWidth.Width`。一般n≥2を先に証明し、
`size_ge_two` により全kのn=max(2,k+1)へ適用する。有限検算を一般証明へ替えていない。

| 固定要求 | 実宣言・構成 | 出所と使用 |
| --- | --- | --- |
| 細A/B/Uと粗A/B/Iの実H⁰ | `a_zero_constant`, `b_w_constant`, `b_zero_constant`, `full_zero_constant`, `constantKernelEquiv`, `aH0Equiv`, `bH0Equiv`, `fullH0Equiv`, `coarseH0Equiv`, `coarseIntersectionH0Equiv` | 原a₀・b₋₁とBの自然数代表path、全閉路の零微分値を追う。両逆を元chartで証明し、H¹消滅を連結性へ使わない。 |
| 同じ二つの標準H⁰差制限 | `pairKernelEquiv`, `fine/coarsePairStandardH0Equiv`, `fine_standard_H0_difference`, `coarse_standard_H0_difference` | 受理G-133 oldH0自然性で実homologyMapを輸送。粗はx-y、細は両点x-yという全元等式。 |
| literal Q/P/q/Z | `diagonal_range`, `endpoint_difference_surjective`, `fineQEquiv`, `fine_Q_mk`, `coarse_Q_zero`, `fine_P_zero`, `coarse_P_zero`, `width_q_zero`, `width_Z_zero`, `primitiveQEquiv`, `primitive_P_zero`, `primitive_q_zero`, `primitive_Z_zero` | 実差制限像の商・H¹核から生成する。PrimitiveGluingの元行へ全短複体等号で戻す。qはQc=0から零、Zは粗交差H¹=0から⊥。 |
| 同じ局所J零 | `regionA_proper`, `regionB_proper`, `local_defects_zero` | C5の任意真部分集合の同じ実H¹比較へ適用。局所零を引数へ渡す前に放電する。 |
| 指定zの標準δの符号 | `intersectionValues`, `intersectionLift`, `intersection_lift`, `a_lift_d0`, `b_generator_zero`, `intersection_lift_derivative`, `standard_connecting_generator`, `standard_connecting_period_one` | z(false)=w₋₁値、z(true)=w₀値。Aはw₀のみz(true)、他はz(false)、Bは0。微分・glueは(z(true)-z(false))a₀。受理の実持上げ/微分/glue APIと標準δへ同定。 |
| 同じCのhidden包含 | `primitive_fine_row_eq`, `primitive_delta_same`, `primitive_delta_period`, `gluingOldClass`, `gluingHiddenClass`, `primitiveQClass`, `hidden_inclusion_same`, `gluing_hidden_nonzero` | 原因子をfstへ正規化した全短複体同型のδ自然性。Cのliteral cokerqのmkが実oldHiddenRow.fで同じ旧H¹商代表へ送られる。coarseU実像は0、period1の同じ類は非零。 |
| 原G-135の実Φ、連結成分、順像係数 | `phiChartEquiv`, `phiEdgeEquiv`, `phi_endpoint_same`, `phiActualEquiv`, `phi_components_subsingleton`, `width_chart_coefficient_bijective`, `full/a/bChartCoefficientEquiv`, `fullPhiH1Equiv`, `a/b_phi_H1_zero` | 追加所属を忘却/付加した同じセルと両端点の全cochain同型。零微分の成分指示関数から原categoryConnectedComponents一意性を証明し、原rightKan係数APIへ適用。 |
| 原R、τ、係数SESと同じ生成元 | `pushforward_H1_zero`, `pushforward_H2_zero`, `width_gamma_forest`, `width_R_top`, `width_tau_zero`, `width_fiber_restriction_bijective`, `widthFiberKernelEquiv`, `coefficient_hidden_same`, `gluing_kernel_tau_same`, `gluing_kernel_tau_value`, `gluing_kernel_tau_generator`, `fullFiberREquiv`, `local_A_R_zero`, `local_B_R_zero`, `local_coefficient_preservation` | 空粗辺/面と空混在面から原五項列の両方向完全性・forestを放電。Dの同じoldCoefficientRow.gがCの同じ実hidden類に原fiberRestrictionH1を適用する値を証明。kerτを任意に定義せず、独立原τのliteral核へ制限する。 |
| 任意kの同時発火 | `size_ge_two`, `all_width_gluing_fires` | 全kで同じhidden非零、kerτ値1、真交差二点・集合交差空を同時に結論。C5の全低幅観測・実Law・非一様性の同じ入力。 |
| 設計§5 H⁰回帰 | `plus_a_back_value`, `plusAH0Equiv`, `h0_width_regression`, `h0_width_regression_two` | 同じplusAの孤立点はw₀、w₋₁とv₀はb₋₁で連結。元の核への両逆からminus1・plus2次元、H¹両零。 |
| 設計§5 標準錐回帰 | `cone_h0_regression`, `cone_h0_regression_nonzero` | G133受理W3aの同じSource Bool、粗Fin1/細Fin2、全台・空辺面・定数Lawの実generatedBlockComparisonHom actualAと標準錐。実H¹欠損(0,0)、実錐H⁰次元1・非零を再利用し、一次零欠損から錐acyclicへの強化を反証する。 |

`fullFiberREquiv` は原Γ forestを証明した後にだけRを全Φ H¹へ移す。
生成元の照合は `gluing_kernel_tau_same` の既存実商と独立fiber射の等式であり、
同次元の線形空間を恣意的に合わせる工程ではない。`phiActualEquiv` は全三次数と
両微分を比較する。`primitive_fine_row_eq` は全短複体等号であり、objectだけの等号ではない。

## Cycle 6 material premise・proof DAG

| material premise | 役割・状態 | 生成元 / proof-use |
| --- | --- | --- |
| 一般T0の有限Source/reading/K1/部分incidence | 本文由来一般入力、Eで放電 | C5 WidthInputの同じ全field構成 → 全選択・微分・比較 |
| n≥2 / NeZero n | 一般補題の方向仮定、全kで放電 | `size_neZero`, `size_ge_two` → 二交差点区別・B非空・周期wrap |
| H⁰値一定/成分一意性 | 構成・放電義務 | 実辺値帰納と全閉路difference_zero_constant → H⁰両逆・原Φ成分・係数constant全単射 |
| 局所J零 | 一般Cの方向仮定、指定例で放電 | `local_defects_zero` → `oldHiddenRow.f`, `local_coefficient_preservation` |
| SES完全性・δ代表式 | 構成・放電義務 | 受理A–Cの同じ実図式 + 今回具体lift/d/glue → same standard δ/hidden |
| Qc/Pc/Pf/Z消滅、Qf同型 | 構成・放電義務 | 差制限全元式・実像核・空交差辺 → q/P/Z/hidden非零 |
| 原順像H¹/H²消滅・Γ forest | 構成・放電義務 | 原空粗辺面と空MixedFace → 原五項列の実fiber全単射・τ零・Rtop |
| 同じhidden/fiber類とkerτ | 構成・放電義務 | `hidden_inclusion_same`, `coefficient_hidden_same`, `gluing_kernel_tau_same` → 同じperiod値1/非零 |
| 指定Law粗adequacy/全幅一致/k0 | C5で構成・放電済み | 同じfst/indicator/constant、全発生ラベル支持・実generatedHomと両値クラス → 幅限界 |

DAGはC5原始族→raw period/H¹→局所H⁰→真交差差制限/Q→実δlift/glue→
PrimitiveGluing全行輸送→同じ旧H¹商/hidden→原G135fiberRestrictionH1/literalkerτ。
並行して同じ原始族→実Φ全cochain同型/H⁰成分→rightKan係数、空面forest→R/τ。
これらは受理T0/A–Dの一般理論へ具体適用する。結論を保持する新certificate fieldはない。

## Cycle 6 result proposal

```yaml
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: C5全E指定族の残る真交差H0/Q/P/Z・標準delta・hidden・原G135係数fiber生成元と回帰例を接続
  exit_criteria_status: [一般n>=2と全size k, 全三次数輸送と全元H0差制限, 実lift/d/glueとdelta符号, literal実商からhidden/kerTauへの同じ生成元, 原係数/成分/forest放電, 指定両回帰例, focused/全宣言公理/共通scan]
  split_reason: none
  completion_candidate: yes
  lean_artifacts: [WidthLocalH0, WidthMayerVietoris, WidthConnecting, WidthHidden, WidthPhi, WidthCoefficient, WidthH0Regression, WidthConeRegression]
  evidence: [fine_standard_H0_difference, primitive_q_zero, primitive_Z_zero, standard_connecting_generator, hidden_inclusion_same, gluing_kernel_tau_same, gluing_kernel_tau_generator, all_width_gluing_fires, h0_width_regression_two, cone_h0_regression_nonzero]
  claim_mapping:
    theorem_names: [all_width_gluing_fires, width_observation, width_uniform_separation, no_width_classifier, width_law_defect, constant_minus_defect]
    source_labels: [固定GOAL T0/A-E, witnesses§1-5, exact-sequence§1-5]
    conjuncts: [受理A真セルSES, 受理B標準錐LES/代表, 受理C実Q/P/snake/欠損, 受理D実Law/同じ係数核商, C5全k/Law/交差とC6同じ生成元接続]
    undischarged_assumptions: []
    acceptance_point: 実装候補は全固定終了条件へ対応し、標準PR監査と別の全GOAL最終4本査読を待つ
    port_status: unported (Research-proved)
audits:
  premise_delta:
    discharged: [局所H0/成分, Qc/P/Z, 指定delta/hidden, 原係数/forest/kerTau, H0/錐回帰]
    remaining: []
  certificate_provenance:
    discharged: [原始セルからの両逆と実微分, 原標準delta, 原五項列の同じfiber制限]
    unresolved: []
  proof_use:
    used: [原端点値, n>=2/size k, 真交差二証拠, 局所J零, 原五項列完全性, 空混在面]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [後続検証記録と固定headのPR監査]
  blocking_findings: []
  next_obligation: 標準review-prと別の最終GOAL数学2・Lean2査読、root全gate再判定、同headCI、受理後merge/Issue同期
```

全GOAL最終判定はまだ行っていない。候補を `target-theorem-proved` と認定するのは、
固定headの標準PR監査・root acceptance・別の独立最終4本全gate・CI後である。
G136/G135 Formal移植は未実施（unported (Research-proved)）。本体実buildとResearch全体build、
aggregate/全file elaborationは未実施。ArchSig PRDの保留作業は実行しない。

## Cycle 6 spine declaration list

8新sourceの全163明示宣言を含む（自動生成宣言は公理監査の全実環境リストにも含める）。
名前は全て `AAT.AG.AtlasGluingWidth.Width` 以下。

### WidthCoefficient.lean（23明示）

```text
AAT.AG.AtlasGluingWidth.Width.pushforward_H1_zero
AAT.AG.AtlasGluingWidth.Width.pushforward_H2_zero
AAT.AG.AtlasGluingWidth.Width.pushforward_standard_H1_zero
AAT.AG.AtlasGluingWidth.Width.pushforward_standard_H2_zero
AAT.AG.AtlasGluingWidth.Width.width_gamma_forest
AAT.AG.AtlasGluingWidth.Width.width_R_top
AAT.AG.AtlasGluingWidth.Width.width_tau_zero
AAT.AG.AtlasGluingWidth.Width.width_fiber_restriction_bijective
AAT.AG.AtlasGluingWidth.Width.widthFiberKernelMap
AAT.AG.AtlasGluingWidth.Width.widthFiberKernelEquiv
AAT.AG.AtlasGluingWidth.Width.widthFiberKernelEquiv_val
AAT.AG.AtlasGluingWidth.Width.gluingFineH1Equiv
AAT.AG.AtlasGluingWidth.Width.gluingKernelTauEquiv
AAT.AG.AtlasGluingWidth.Width.gluingKernelTauClass
AAT.AG.AtlasGluingWidth.Width.gluing_kernel_tau_same
AAT.AG.AtlasGluingWidth.Width.gluing_kernel_tau_value
AAT.AG.AtlasGluingWidth.Width.gluing_kernel_tau_generator
AAT.AG.AtlasGluingWidth.Width.local_coefficient_preservation
AAT.AG.AtlasGluingWidth.Width.fullFiberREquiv
AAT.AG.AtlasGluingWidth.Width.local_A_R_zero
AAT.AG.AtlasGluingWidth.Width.local_B_R_zero
AAT.AG.AtlasGluingWidth.Width.size_ge_two
AAT.AG.AtlasGluingWidth.Width.all_width_gluing_fires
```

### WidthConeRegression.lean（2明示）

```text
AAT.AG.AtlasGluingWidth.Width.cone_h0_regression
AAT.AG.AtlasGluingWidth.Width.cone_h0_regression_nonzero
```

### WidthConnecting.lean（23明示）

```text
AAT.AG.AtlasGluingWidth.Width.intersectionValues
AAT.AG.AtlasGluingWidth.Width.intersection_values_closed
AAT.AG.AtlasGluingWidth.Width.aLift
AAT.AG.AtlasGluingWidth.Width.intersectionLift
AAT.AG.AtlasGluingWidth.Width.intersection_lift
AAT.AG.AtlasGluingWidth.Width.unionGenerator
AAT.AG.AtlasGluingWidth.Width.a_lift_d0
AAT.AG.AtlasGluingWidth.Width.b_generator_zero
AAT.AG.AtlasGluingWidth.Width.intersection_lift_derivative
AAT.AG.AtlasGluingWidth.Width.union_generator_closed
AAT.AG.AtlasGluingWidth.Width.intersectionClass
AAT.AG.AtlasGluingWidth.Width.unionGeneratorClass
AAT.AG.AtlasGluingWidth.Width.standard_connecting_generator
AAT.AG.AtlasGluingWidth.Width.union_full_eq
AAT.AG.AtlasGluingWidth.Width.selectionCyclesEquiv
AAT.AG.AtlasGluingWidth.Width.selectionCyclesEquiv_val
AAT.AG.AtlasGluingWidth.Width.selectionH1Equiv
AAT.AG.AtlasGluingWidth.Width.selectionH1Equiv_mk
AAT.AG.AtlasGluingWidth.Width.unionPeriodEquiv
AAT.AG.AtlasGluingWidth.Width.union_generator_value
AAT.AG.AtlasGluingWidth.Width.intersection_Q_value
AAT.AG.AtlasGluingWidth.Width.standard_connecting_period_one
AAT.AG.AtlasGluingWidth.Width.standard_connecting_nonzero
```

### WidthH0Regression.lean（7明示）

```text
AAT.AG.AtlasGluingWidth.Width.plusARoot
AAT.AG.AtlasGluingWidth.Width.plusAIsolated
AAT.AG.AtlasGluingWidth.Width.plusABackEdge
AAT.AG.AtlasGluingWidth.Width.plus_a_back_value
AAT.AG.AtlasGluingWidth.Width.plusAH0Equiv
AAT.AG.AtlasGluingWidth.Width.h0_width_regression
AAT.AG.AtlasGluingWidth.Width.h0_width_regression_two
```

### WidthHidden.lean（23明示）

```text
AAT.AG.AtlasGluingWidth.Width.primitiveFineRow
AAT.AG.AtlasGluingWidth.Width.primitive_fine_row_eq
AAT.AG.AtlasGluingWidth.Width.primitiveFineRowIso
AAT.AG.AtlasGluingWidth.Width.primitiveUnionH1Equiv
AAT.AG.AtlasGluingWidth.Width.primitiveIntersectionH0Equiv
AAT.AG.AtlasGluingWidth.Width.primitiveIntersectionClass
AAT.AG.AtlasGluingWidth.Width.primitiveDelta
AAT.AG.AtlasGluingWidth.Width.primitive_delta_same
AAT.AG.AtlasGluingWidth.Width.primitive_delta_period
AAT.AG.AtlasGluingWidth.Width.region_union_full
AAT.AG.AtlasGluingWidth.Width.gluingOldClass
AAT.AG.AtlasGluingWidth.Width.gluingOldClass_fineUnionEquiv
AAT.AG.AtlasGluingWidth.Width.gluingHiddenClass
AAT.AG.AtlasGluingWidth.Width.primitiveQClass
AAT.AG.AtlasGluingWidth.Width.hidden_inclusion_same
AAT.AG.AtlasGluingWidth.Width.coefficient_hidden_same
AAT.AG.AtlasGluingWidth.Width.gluing_old_nonzero
AAT.AG.AtlasGluingWidth.Width.union_actual_range_zero
AAT.AG.AtlasGluingWidth.Width.gluing_hidden_nonzero
AAT.AG.AtlasGluingWidth.Width.primitiveQEquiv
AAT.AG.AtlasGluingWidth.Width.primitive_P_zero
AAT.AG.AtlasGluingWidth.Width.primitive_q_zero
AAT.AG.AtlasGluingWidth.Width.primitive_Z_zero
```

### WidthLocalH0.lean（29明示）

```text
AAT.AG.AtlasGluingWidth.Width.localChart
AAT.AG.AtlasGluingWidth.Width.localEdge
AAT.AG.AtlasGluingWidth.Width.local_zero_edge
AAT.AG.AtlasGluingWidth.Width.aRoot
AAT.AG.AtlasGluingWidth.Width.aEdge
AAT.AG.AtlasGluingWidth.Width.aBackEdge
AAT.AG.AtlasGluingWidth.Width.a_zero_constant
AAT.AG.AtlasGluingWidth.Width.b_w_selected
AAT.AG.AtlasGluingWidth.Width.bW
AAT.AG.AtlasGluingWidth.Width.bV
AAT.AG.AtlasGluingWidth.Width.bAEdge
AAT.AG.AtlasGluingWidth.Width.bBEdge
AAT.AG.AtlasGluingWidth.Width.b_a_value
AAT.AG.AtlasGluingWidth.Width.b_b_value
AAT.AG.AtlasGluingWidth.Width.positive_cast_ne_zero
AAT.AG.AtlasGluingWidth.Width.b_w_constant
AAT.AG.AtlasGluingWidth.Width.b_zero_constant
AAT.AG.AtlasGluingWidth.Width.constantKernelEquiv
AAT.AG.AtlasGluingWidth.Width.constantKernelEquiv_apply
AAT.AG.AtlasGluingWidth.Width.constantKernelEquiv_symm_apply
AAT.AG.AtlasGluingWidth.Width.aH0Equiv
AAT.AG.AtlasGluingWidth.Width.bH0Equiv
AAT.AG.AtlasGluingWidth.Width.full_zero_constant
AAT.AG.AtlasGluingWidth.Width.fullH0Equiv
AAT.AG.AtlasGluingWidth.Width.coarseRoot
AAT.AG.AtlasGluingWidth.Width.coarseH0Equiv
AAT.AG.AtlasGluingWidth.Width.regionB_nonempty
AAT.AG.AtlasGluingWidth.Width.coarseIntersectionRoot
AAT.AG.AtlasGluingWidth.Width.coarseIntersectionH0Equiv
```

### WidthMayerVietoris.lean（35明示）

```text
AAT.AG.AtlasGluingWidth.Width.pairKernelEquiv
AAT.AG.AtlasGluingWidth.Width.finePairH0Equiv
AAT.AG.AtlasGluingWidth.Width.coarsePairH0Equiv
AAT.AG.AtlasGluingWidth.Width.fine_H0_difference
AAT.AG.AtlasGluingWidth.Width.coarse_H0_difference
AAT.AG.AtlasGluingWidth.Width.finePairStandardH0Equiv
AAT.AG.AtlasGluingWidth.Width.coarsePairStandardH0Equiv
AAT.AG.AtlasGluingWidth.Width.fineIntersectionStandardH0Equiv
AAT.AG.AtlasGluingWidth.Width.fineIntersectionStandardH0Equiv_oldH0Equiv
AAT.AG.AtlasGluingWidth.Width.coarseIntersectionStandardH0Equiv
AAT.AG.AtlasGluingWidth.Width.widthFineRow
AAT.AG.AtlasGluingWidth.Width.widthCoarseRow
AAT.AG.AtlasGluingWidth.Width.fine_standard_H0_difference
AAT.AG.AtlasGluingWidth.Width.coarse_standard_H0_difference
AAT.AG.AtlasGluingWidth.Width.diagonalDifference
AAT.AG.AtlasGluingWidth.Width.endpointDifference
AAT.AG.AtlasGluingWidth.Width.diagonal_range
AAT.AG.AtlasGluingWidth.Width.endpoint_difference_surjective
AAT.AG.AtlasGluingWidth.Width.diagonalCokernelEquiv
AAT.AG.AtlasGluingWidth.Width.fineQEquiv
AAT.AG.AtlasGluingWidth.Width.fine_Q_mk
AAT.AG.AtlasGluingWidth.Width.coarse_standard_H0_surjective
AAT.AG.AtlasGluingWidth.Width.coarse_Q_zero
AAT.AG.AtlasGluingWidth.Width.width_selection_compatible
AAT.AG.AtlasGluingWidth.Width.widthRowComparison
AAT.AG.AtlasGluingWidth.Width.regionA_proper
AAT.AG.AtlasGluingWidth.Width.regionB_proper
AAT.AG.AtlasGluingWidth.Width.local_defects_zero
AAT.AG.AtlasGluingWidth.Width.fine_pair_standard_H1_zero
AAT.AG.AtlasGluingWidth.Width.coarse_pair_standard_H1_zero
AAT.AG.AtlasGluingWidth.Width.fine_P_zero
AAT.AG.AtlasGluingWidth.Width.coarse_P_zero
AAT.AG.AtlasGluingWidth.Width.coarse_intersection_standard_H1_zero
AAT.AG.AtlasGluingWidth.Width.width_Z_zero
AAT.AG.AtlasGluingWidth.Width.width_q_zero
```

### WidthPhi.lean（21明示）

```text
AAT.AG.AtlasGluingWidth.Width.actualSelected
AAT.AG.AtlasGluingWidth.Width.phiChartEquiv
AAT.AG.AtlasGluingWidth.Width.phiEdgeEquiv
AAT.AG.AtlasGluingWidth.Width.width_phi_faces_empty
AAT.AG.AtlasGluingWidth.Width.phi_endpoint_same
AAT.AG.AtlasGluingWidth.Width.phiActualEquiv
AAT.AG.AtlasGluingWidth.Width.actual_chart_nonempty
AAT.AG.AtlasGluingWidth.Width.actual_zero_constant
AAT.AG.AtlasGluingWidth.Width.phi_endpoint_component
AAT.AG.AtlasGluingWidth.Width.phi_components_subsingleton
AAT.AG.AtlasGluingWidth.Width.phi_components_nonempty
AAT.AG.AtlasGluingWidth.Width.width_chart_coefficient_bijective
AAT.AG.AtlasGluingWidth.Width.a_actual_zero_constant
AAT.AG.AtlasGluingWidth.Width.b_actual_zero_constant
AAT.AG.AtlasGluingWidth.Width.full_actual_zero_constant
AAT.AG.AtlasGluingWidth.Width.fullChartCoefficientEquiv
AAT.AG.AtlasGluingWidth.Width.aChartCoefficientEquiv
AAT.AG.AtlasGluingWidth.Width.bChartCoefficientEquiv
AAT.AG.AtlasGluingWidth.Width.fullPhiH1Equiv
AAT.AG.AtlasGluingWidth.Width.a_phi_H1_zero
AAT.AG.AtlasGluingWidth.Width.b_phi_H1_zero
```

## Cycle 6 再利用sourceの版と適用

G133/G135の受理参照は既出PR5269#6007700344 / PR5318#6078269788。
現在sourceは指定reuse版ed16acc02229fdfe3846303de341d600878f03dcとbyte一致。
今回使う実型と適用引数は上の条項・premise表で固定した。
GammaForestの必要closure65sourceは既存受理cacheとbyte照合し、欠けた3cacheだけを専用worktreeへコピーした。
他worktreeへ書き込んでいない。新8sourceは専用cacheに個別elaborateした。

| source | SHA256 |
| --- | --- |
| `GammaForest.lean` | `c783cd60bb052d487adaee010650109b8df5d89d31fb1c0b81458316d8f09948` |
| `LocalCoefficientSingle.lean` | `6520da925b2d8b2cf009869213b02c9fc780ec2557cd4573b62144f730e92505` |
| `LocalNaturality.lean` | `1015b5e418fd49a243ef430b1ec87ec114a9e01df209e43befe1fc46f2dfd6b2` |
| `FiveTermSequence.lean` | `c9fb934891dfd966ac23711e566cda115987220862e904c63cc5f9ed002687e3` |
| `HomologyRepresentatives.lean` | `cee43137f7be42212ff7a02f9f0ff48a0541d5ea0a3f5ebb2c9a306dcae5c614` |
| `RestrictionHomology.lean` | `44317eec491e425838829730a8c8c1474b8f855c8a97f58f82d8d0ac3ed1f5d0` |
| `PushforwardComplex.lean` | `d9a640dec22caae23efc7518a600e587fa0b643523376ea63848f40648865332` |
| `WitnessThreeActual.lean` | `dedd79f16cc6426bd4b71853d525db27709b8aa892f8fbe22335d330d9205b40` |
| `WitnessThreeInput.lean` | `dd228a5fde0acf813a0126527382494aaef9d2d5feda6a3166b1784e776dd347` |
| `WitnessThreeNamed.lean` | `b27892a58d955e6e9af818fc6a6097d2d52f4847a58044d8287591142217b6c6` |
| `WitnessThreeConeRanks.lean` | `d852ba0613fc279d4ebb500fd0da42a0aafdc8b4e3e8f524ec4f33a2ce759079` |

## Cycle 6 初回検証記録（head018c7b6eの固定実体）

全33sourceの累積777明示と80生成、857実宣言を現環境で列挙し、
全857の明示 `#print axioms` を一つの非aggregate監査fileで照会した。
現環境857名・実出力857名・全明示777名・新161名の突合は欠落0/余剰0。
依存はpropext/Classical.choice/Quot.soundのみ。全件log SHA256
`d78bd01dcedb239d04cd503004e8bbd8e5a1fa8cccd31def96f94ee56215b947`。

新8sourceは各必要targeted `lake env lean -o <専用cache> <対象file>` でexit0、
warningなし。cacheは専用worktree内だけ。公式単一focusedコマンド
`bash research/lean/check_research_modules.sh --focused ResearchLean/AG/AtlasGluingWidth/WidthConeRegression.lean`
はexit0、log SHA256 `a7814e1d667a9d03e18881c22603bf43a70c54ac9734658d484e6e6cf91e70dd`。

| source | 明示宣言数 | SHA256 |
| --- | --- | --- |
| `WidthCoefficient.lean` | 23 | `f71511816877738c44dbd7286f9843f555138c0cd1ed4ec6d416617790cead45` |
| `WidthConeRegression.lean` | 2 | `1484ee823501f815b9849d97e9d9d4c79a45f1f70ec6fdb6a2d4a8eaa46df1cc` |
| `WidthConnecting.lean` | 23 | `7ee60088339f187c224afbd102e4197928b5779e854706d11a77376970eb6a25` |
| `WidthH0Regression.lean` | 7 | `447b112bea031286c6fc130da94ebec35115caa67a2d8b34bad61a531437d832` |
| `WidthHidden.lean` | 22 | `d251057024bc317b3df996dac4407f86f7ca3aeba8bc90dc591abaf162a5f085` |
| `WidthLocalH0.lean` | 29 | `904665a89efa0a30e60a673a4c7055bef9860a2771239d547d995d04c301868b` |
| `WidthMayerVietoris.lean` | 34 | `c41418c52c4aa4a339e5fb7b96c11f69ed9fb8c1547cd1e37662b380b70a05ef` |
| `WidthPhi.lean` | 21 | `175296d55b498c19511faa3f9dd7b11d47bf11e8ab5f7a638d56400d3164d1df` |

| targeted source | exit | 実出力SHA256 |
| --- | --- | --- |
| `WidthLocalH0.lean` | 0 | `0fc80c5b5c386e8ba76e224a1a596218ffb51c0f7925b0366b375d669cedc242` |
| `WidthMayerVietoris.lean` | 0 | `e7cb7eb3ceb2b94010b0faca824d05e49f2e719fec010b5ae0936a434065d098` |
| `WidthConnecting.lean` | 0 | `7dcee6bbb803fee28cd331917e3680fa6fc44dc0563d9124955acd79c341d718` |
| `WidthHidden.lean` | 0 | `38bee3a0782065a653f6e78c471e07c1bea0c3ebc5ee61872240b55ce2d6be40` |
| `WidthPhi.lean` | 0 | `0ddfd2acc6b6d1272b19a030db47f0d06659d3e5645f8b6c457130407caa779d` |
| `WidthCoefficient.lean` | 0 | `38bee3a0782065a653f6e78c471e07c1bea0c3ebc5ee61872240b55ce2d6be40` |
| `WidthH0Regression.lean` | 0 | `1c3b70e7fb5005908438be919a3efff06e299979347860e2ca5c5ab690d06ffb` |
| `WidthConeRegression.lean` | 0 | `e3a97f6df94b0b3e2bfcc58a2470bdf91e67d7c4f7baa9ffdb67513cbcce0a12` |

placeholder/hidden/BiDi/privacy/追加語彙/whitespace scan clean。reportの既存
axiom方針記載2hitは宣言やplaceholderではない。静的方向gate228module pass、
本体→Research import0、固定GOAL/design5fileと受理A–D/C5の25sourcebyte不変。
共通skill/品質/workflow参照も固定636ea3d版と同一。正式新4lanePR監査と
別の全GOAL最終新4lane監査・固定headCIはこの記録後に行う。


## Cycle 6 非中心API修正の範囲

[初回正式4本査読](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5336#issuecomment-6110615009)
はhead018c7b6ec053fdec01e2aaff97e9cf8ebc7f4592に対し、中心finding0、
no-unfold API不足を一括指摘した。修正は名指しされた公開評価補題7本と
指摘consumerのproof内部、およびこのspine/hash/検証記録の同期に限る。
既存signature、def/instance値、宣言、import方向、固定target、result proposalのstatusは変えない。

| 追加公開API | 所有moduleと下流使用 |
| --- | --- |
| `CellSelection.left_val`, `CellSelection.right_val` | CellSelection、選択辺の元chart値。WidthLocalH0/WidthConnecting/WidthH0Regressionの端点評価 |
| `StandardRow.cellRow_g` | StandardShortExact、元差制限の標準零延長。WidthMayerVietorisの粗細H⁰自然性 |
| `Width.left_apply`, `Width.right_apply` | WidthInput、元辺のBool分岐。指定path/lift/H⁰回帰の端点評価 |
| `Width.fineIntersectionStandardH0Equiv_oldH0Equiv` | WidthMayerVietoris、全元oldH⁰輸送の評価。WidthConnecting.intersection_Q_value |
| `Width.gluingOldClass_fineUnionEquiv` | WidthHidden、全元同じ旧H¹類の和同型評価。WidthCoefficient.gluing_kernel_tau_value |

受理済み25source中22sourceはbyte不変。残るCellSelection/StandardShortExact/WidthInputは
上の5補題を追記しただけで、受理済み全定義・定理のstatementと定義値は保持する。
8新sourceの明示163＋既存ownerへの5補題＝今回明示168、生成6を含むdelta174。
累積33sourceは明示784＋生成79＝863実宣言。最終公理名/実出力/全spineはこの修正後実体へ同期する。

上の初回PR前検証節・source表はその初回固定実体の履歴である。
最新修正後検証・source/output hashは後続表が正であり、初回値を現在headの証拠へ流用しない。
別の全GOAL最終4本査読は内容判定合格後の工程である。

## Cycle 6 API修正後の検証記録

全33sourceの明示784＋生成79＝863実宣言について、同じ実環境名・全公理出力名・
全source明示名を突合し、欠落0/余剰0。依存は標準propext/Classical.choice/Quot.soundのみ。
全件公理log SHA256 `1050dc4856afd78c267bda24f585c48f7c6cd9300315ef1ede5f54f0d1b5b532`。
初回からの差は名指し7補題の追加と、証明内部のAPI使用により不要になった
Lean自動生成 `Width.intersectionValues.congr_simp` 1名の減少であり、source明示宣言の削除は0。

必要な所有側3moduleと新8moduleを依存順に個別targeted検証し、全11exit0・warningなし。
公式単一focused WidthConeRegressionもexit0、出力SHA256
`a7814e1d667a9d03e18881c22603bf43a70c54ac9734658d484e6e6cf91e70dd`。
全Research/aggregate/all-file elaborationを実行していない。

| source | 明示数 | source SHA256 | targeted出力 SHA256 |
| --- | --- | --- | --- |
| `CellSelection.lean` | 29 | `38a93430abe7bd66532199a1dd25cbe14ea00ef5ee45e4d7d1035aaeb6ba7ca8` | `f8405c1dd971e6d615fd2f4822003ef9a8b8683648addd28c9f06d480ecf6b03` |
| `StandardShortExact.lean` | 11 | `3b6d792137e60e6d65374c5d6a1c261ac0f5a2b2391bc5d468c0f77fec140ce4` | `8dcc6038ad966f35dddf2496d4b8b9048766a29221ab4cc7256226442a7d2e7f` |
| `WidthInput.lean` | 24 | `561d43056f54f01006fb8d558959e45eb1dfbb3b0346d9eaae41bc9b0d387a6f` | `7dcee6bbb803fee28cd331917e3680fa6fc44dc0563d9124955acd79c341d718` |
| `WidthLocalH0.lean` | 29 | `ef8b1cf88e7d17b6c399f81caaa43e542a63ed26ada6622c9d0b211ad78766dd` | `0fc80c5b5c386e8ba76e224a1a596218ffb51c0f7925b0366b375d669cedc242` |
| `WidthMayerVietoris.lean` | 35 | `4af152d93d6e427d181354df61e1c4ab3ad9b9c6cc30bda7a8b72deeff5d3110` | `37f67ca954d0c2f0cb573456aa61404ea6a81ea7e07cad42e109875a9e52ace7` |
| `WidthConnecting.lean` | 23 | `27453874b3b78b5f48f3aec201a6f123a5d34f93b192fec68023032bf9776f3f` | `38bee3a0782065a653f6e78c471e07c1bea0c3ebc5ee61872240b55ce2d6be40` |
| `WidthHidden.lean` | 23 | `bf8548d1796fa05329880904022c3183563ac6b1aa18dcb5997f241d50eb6fa9` | `7dcee6bbb803fee28cd331917e3680fa6fc44dc0563d9124955acd79c341d718` |
| `WidthPhi.lean` | 21 | `175296d55b498c19511faa3f9dd7b11d47bf11e8ab5f7a638d56400d3164d1df` | `0ddfd2acc6b6d1272b19a030db47f0d06659d3e5645f8b6c457130407caa779d` |
| `WidthCoefficient.lean` | 23 | `d4c5bd0b26c56cd7c5d00590a56caef73081f8a24ba9e6fb5056a1cb339a053e` | `38bee3a0782065a653f6e78c471e07c1bea0c3ebc5ee61872240b55ce2d6be40` |
| `WidthH0Regression.lean` | 7 | `bc699a9cb7cf77c81d17043896fb37a41286e8f651c8682e3006868b3cc6fe8d` | `1c3b70e7fb5005908438be919a3efff06e299979347860e2ca5c5ab690d06ffb` |
| `WidthConeRegression.lean` | 2 | `1484ee823501f815b9849d97e9d9d4c79a45f1f70ec6fdb6a2d4a8eaa46df1cc` | `e3a97f6df94b0b3e2bfcc58a2470bdf91e67d7c4f7baa9ffdb67513cbcce0a12` |

修正対象placeholder/Unicode/privacy/語彙/whitespace scan clean。本体→Research import0、
静的import direction228module pass、package direction pass。reportの歴史的axiom説明語は
宣言placeholderではない。固定GOAL/design/common版とreuse sourceは不変。

この記録は修正後の実検証であり、直接対応の独立資格確認と別の全GOAL最終gateは
後続の固定head PR監査コメントで判定する。result proposal/candidateのstatusは変更していない。
Formal移植/実build、Research全体build、ArchSig保留レビュー、他worktree書込は未実施。
