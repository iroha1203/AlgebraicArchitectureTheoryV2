# G-130：相対修復合成の証拠対応

一次仕様は [固定GOAL](../goals/G-130-aat-relative-repair-composition.md)、
構成方針は [設計](../designs/G-130-aat-relative-repair-composition/README.md) にある。
実行・検証・査読・PRの記録は [tracking Issue #5132](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5132) を参照する。

## Cycle 1：固定実辺を保つ対象と再同定の座標化

```yaml
ledger_type: target_cycle_result
goal: G-130-aat-relative-repair-composition
cycle: 1
goal_blob_sha: 8da0fb4eb75d1cb5c37a9d4ddf5e03c18c0bb8a2
base_oid: fe2653be02da9b2024f37928b50ff606e9eb229d
tracking_issue: 5132
report_path: research/reports/G-130-aat-relative-repair-composition.md
selection:
  proof_state_ref: "Issue #5132 の初期proof state"
  proof_dag_predecessors: [OriginalTowerPresentation.solutionOfCorrection, OriginalTowerPresentation.solutionCorrection, OriginalTowerPresentation.vertexGauge_edge_arrow]
  milestone: "Aの実修復と範囲付き補正の対象の相互逆、および元の頂点再同定の対応"
  proof_obligations: ["補正零と基準実辺の一致の双方向", "任意の固定辺集合に対する対象の相互逆", "固定頂点と固定辺を保つ再同定部分群の構成", "実頂点作用と補正加算の対応、作用元を保つ射の相互逆", "範囲包含に対する対象・作用元の互換"]
  exit_criteria: ["任意の一般塔の実辺に対する両逆", "実射等号と補正零の一致をstrong uniquenessで証明", "固定条件を保つ作用群と射対応を同じd0で構成", "登録した単一fileのfocused checkと全宣言axiom監査"]
  selection_reason: "実修復を補正方程式から定義し直さず、後続の相対化と全範囲合成の土台を作る"
  expected_result_type: proof-obligation-discharged
  lean_targets: [ResearchLean/AG/RelativeRepairComposition/SupportedRepairs.lean, ResearchLean/AG/RelativeRepairComposition/LabeledAction.lean]
  risks: ["実辺の等号をchoiceの等号へ無証明で置換しない", "頂点作用のkernelを潰さず異なる射を保つ", "一般塔と全実核をG129と同じ意味で使う"]
  unchecked: ["実装・検証・独立査読前"]
```

### 同じ実辺と射への対応

宣言のnamespaceは `AAT.AG.RelativeRepairComposition`、pathは
`research/lean/ResearchLean/AG/RelativeRepairComposition/` 以下である。

| Aの対応する要求 | 宣言 | 原始入力からの構成・使用 |
| --- | --- | --- |
| 固定実辺の一致と補正零 | `solution_edge_eq_iff_choice`, `solution_correction_zero_iff_edge` | 元のstrong辺で自己同型を一意に取消し、全実核の差を使用 |
| 実修復と支持付き補正の両逆 | `SupportedRepair`, `SupportedCorrection`, `repairCoord`, `repairRec`, `repairEquiv`, `repairRec_coord`, `repairCoord_rec` | 実修復は元のchoice/core/面と実辺等号で定義。G-129の同じ差と復元を制限 |
| 許された全ての再同定 | `supportedC0`, `repairGauge`, `gauge_between_supported`, `originalHomEquiv`, `repairHomEquiv`, `repairHomEquiv_label` | P上で零の元のbについて、両端の固定実辺からd0bの零を導く。bの値を射のラベルとして保つ |
| 元辺に対する頂点作用 | `repairGauge_coord`, `coord_gauge`, `rec_gauge` | G-129の `vertexGauge_edge_arrow` と同じ作用。補正への作用は同じd0の加算 |
| native作用groupoidの対応 | `RepairGroupoid`, `CorrectionGroupoid`, `coordFunctor`, `recFunctor`, `rec_coord_obj`, `coord_rec_obj`, `coordFunctor_map_label`, `recFunctor_map_label`, `repairGroupoidEquivalence` | Mathlib `ActionCategory`。対象の両逆、射の同一ラベル、恒等・合成と自然同型を構成 |
| 変更範囲の包含 | `fixedEdgesForRange`, `fixedEdgesForRange_antitone`, `repairInclusion`, `correctionInclusion`, `gaugeInclusion`, `coord_inclusion`, `rec_inclusion`, `gauge_inclusion` | 同じ辺名の集合P∪(候補\S)を用い、Sの増加で固定条件を緩和。対象と全作用元を保持 |
| 存在と自己同型の計算への接続 | `supported_repair_nonempty_iff`, `repairGauge_eq_self_iff` | 前者は同じ支持付き方程式、後者は同じd0のkernel。修復の存在を前提に置かない |

`LabeledAction.lean` は一般の同変な対象同値からnative作用groupoidの同値を構成するAPIである。
`labeledActionFunctor`, `labeledActionInverse` は各射の群ラベルを保持し、
`labeledAction_left_obj`, `labeledAction_right_obj` は対象の両逆、
`labeledActionUnit`, `labeledActionCounit`, `labeledActionEquivalence` は自然同型と三角恒等式を与える。
実修復への適用時の同変性は `coord_gauge` から生成する。

### 前提と証明依存

| 前提・構成 | 分類 | 出所・使用先 |
| --- | --- | --- |
| K、一般の圏の塔、元辺、core、基準lift、比較 | 本文由来、ambient-boundary | GOAL Aの原始入力 `OriginalTowerPresentation`。元の実Solutionと固定実辺へ |
| 強さ、面の底とcoreの整合、全核の可換性、生成輸送の全単射性、比較の中央化 | 本文由来、direction-hypothesis | G-129と同じTのfield。strong一意性、同じ輸送・微分・解対応を使用。FとW1–W5での具体放電は後続義務 |
| fixed辺名と固定頂点の集合 | 本文由来、ambient-boundary | 任意の同じ型付き辺・頂点の集合。AのPと禁止候補から `fixedEdgesForRange` で構成 |
| 支持部分群、許容再同定、対象の往復、作用、射対応、native同値 | 放電済み、discharge-required | 上表の構成と両逆、`gauge_between_supported`, `coord_gauge`, `labeledActionEquivalence` |
| 修復対象R、二対象間の射b | 定理の量化対象 | 既存の対象や射を調べるAPIに現れる。修復の存在判定では対象の存在を仮定しない |
| 一般の同変対象同値e | 一般APIのdirection-hypothesis、実適用で放電済み | `repairEquiv` と `coord_gauge` が同じ実入力から生成 |

既存宣言の参照版はIssueのactive化で固定された `dbed043cb514e8c964589d2e12e982750c87ae83`。
`Solutions.lean` の往復は [PR #5116の受理レビュー](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5116#issuecomment-5894001032)
(head `c72263023bf7a775d207f57503a5723e3e5b9f0a`)で、
`VertexGauge.lean` の元辺作用は [PR #5118の受理レビュー](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5118#issuecomment-5894428822)
(head `20f63e8f4cf39d5ed7a8dfc31af7ccfe5550f5e6`)で受理されている。
今回の使用宣言は参照版まで変更されておらず、同じT・全実核・d0・d1を適用する。
Mathlibはactive化で固定された `8f9d9cff6bd728b17a24e163c9402775d9e6a365` の
`CategoryTheory/Action.lean` を使用する。

```yaml
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "固定実辺と補正零の双方向、支持付き対象の両逆、全再同定の同一ラベル、native同値、範囲包含を構成"
  exit_criteria_status: ["一般塔と元strong辺に対する双方向を構成", "対象と全射を同じcochainで対応", "包含互換を構成", "検証結果はPRへ固定"]
  split_reason: none
  completion_candidate: no
  lean_artifacts: [SupportedRepairs.lean, LabeledAction.lean]
  evidence: [solution_correction_zero_iff_edge, repairEquiv, originalHomEquiv, repairHomEquiv, repairGroupoidEquivalence, gauge_inclusion]
  claim_mapping:
    theorem_names: [solution_correction_zero_iff_edge, repairRec_coord, repairCoord_rec, gauge_between_supported, coord_gauge, rec_gauge, supported_repair_nonempty_iff, repairGauge_eq_self_iff]
    source_labels: ["G-130 Aの実修復・射・範囲包含", "n1017 §2.2・2.5"]
    conjuncts: ["固定実辺等号↔補正零", "対象の相互逆", "全ての元のb↔支持付きb↔同じd0方程式", "native作用groupoidと包含"]
    undischarged_assumptions: []
    acceptance_point: "Aの実辺と射の座標化という独立した到達点。A–F全体は後続の構成義務"
    port_status: unported
audits:
  premise_delta:
    discharged: ["同じ原始入力からの支持部分群・対象往復・全射対応・包含"]
    remaining: ["FとW1–W5での具体入力条件の放電"]
  certificate_provenance:
    discharged: ["repairEquiv/coord_gaugeからnative同値を生成"]
    unresolved: []
  proof_use:
    used: ["original.edgeStrong→固定実辺の一意性", "G129解往復→支持付き両逆", "vertexGauge_correction→許容群・射・自己同型", "集合包含→同じ辺名・作用元"]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: ["登録した2fileのfocused check・全宣言#print axiomsはPRに記録"]
  blocking_findings: []
  next_obligation: "閉じた部分表示・制限・相対複体、同じH0/H1/H2への分類、参照座標の輸送。その後B–F・W1–W5"
```

## 後続の構成義務

Aの部分表示と全次数の制限、相対複体・H0/H1/H2分類、参照座標変更、Bのdescentと
統合障害、Cの有限生成と局所厳密合成、Dの双対分類、Eの更新・文脈同値・分割、
Fの全アフィン実現、W1–W5の全要求と一般定理への接続が必要である。
G-130全体の判定には固定GOALの全完了条件と独立最終査読を用いる。
