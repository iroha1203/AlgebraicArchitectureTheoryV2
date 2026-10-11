# G-136 証明記録

固定 GOAL・設計・共通基準: `636ea3d45558fd0e511e3184cfa74ab1c23142c0`。
GOAL blob: `dbc5b584987a1f3e1987125b7ccde2e361a89533`。
既存宣言の参照版: `ed16acc02229fdfe3846303de341d600878f03dc`。
追跡: [#5321](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5321)。

## 現 proof obligation

T0・A–E は固定 target を維持する。初回 selection は実装前の開始報告で固定した。
A のセル選択・交差・三次数完全性・原始比較の可換性を到達点とする。
B の錐 SES/LES、C の Q/P と snake、D の実 Law と係数/fiber 接続、E の任意 k の族は未実装。
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
正式 PR 査読前のため、ここでの達成表示は受理候補である。

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

Cycle 1 の個別 source focused check は全4 file が exit 0。
公式検査 `bash research/lean/check_research_modules.sh --focused ResearchLean/AG/AtlasGluingWidth/SelectionComparison.lean`
は exit 0、対象 module の45宣言は標準公理のみ。
同じ依存 source の全116実宣言を単一非 aggregate の監査 file から明示照会し、全て標準公理のみ。
照会 log SHA256 は `70eff3576f63c2bed934cb0026f64bcb3ee97b706112275746e102449325cf97`、
公式 focused log は `2088aed2a2001f68e603b8c16bfc7d10c507163f04f9e8048bef14fdd550d9a8`。
placeholder、hidden/BiDi、privacy、語彙、import 方向、diff whitespace は該当違反なし。
