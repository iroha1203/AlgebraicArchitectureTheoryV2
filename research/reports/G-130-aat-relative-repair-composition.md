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

## Cycle 2：閉部分表示への制限と相対・支持付き複体

```yaml
ledger_type: target_cycle_result
goal: G-130-aat-relative-repair-composition
cycle: 2
goal_blob_sha: 8da0fb4eb75d1cb5c37a9d4ddf5e03c18c0bb8a2
base_oid: 2a3c7f0448087ab77616047fb9e4aeb8c8343973
tracking_issue: 5132
report_path: research/reports/G-130-aat-relative-repair-composition.md
selection:
  proof_state_ref: "Cycle 1 の支持付き実修復・全再同定対応"
  proof_dag_predecessors: [supportedC1, supportedC0, pathCorrection, pastingCorrection, d1_d0, d2_d1]
  milestone: "Aの閉包条件から同じ微分の制限を構成し、相対・支持付き四項複体を得る"
  proof_obligations: ["元セル名と全書き換え文脈による閉部分表示", "0–3次の制限と微分の交換", "相対kernelへの微分の制限", "候補零条件と固定頂点を保つ支持付き複体", "native複体と同じH0/H1/H2の定義・零判定"]
  exit_criteria: ["閉包条件だけから3本の制限交換を証明", "相対・支持付き微分の二乗零を証明", "Cycle 1の部分群と支持付き複体の同じデータへの対応", "native四項複体とkernel/image商への接続、focused checkとaxiom監査"]
  selection_reason: "実修復の存在・分類とdescentに必要な複体を、元の輸送と微分から生成する"
  expected_result_type: proof-obligation-discharged
  lean_targets: [ResearchLean/AG/RelativeRepairComposition/ClosedRegions.lean, ResearchLean/AG/RelativeRepairComposition/RelativeComplex.lean]
  risks: ["次数ごとの零拡張をchain mapと誤認しない", "3-cellのprefix/suffixを閉包から落とさない", "C0を固定頂点のkernel内で取る", "実部分塔の完全な制限や分類全体は後続義務として区別する"]
  unchecked: ["構成・検証・独立査読前"]
```

### 同じ相対微分と実障害への対応

以下の宣言のnamespaceは `AAT.AG.RelativeRepairComposition`。
`ClosedRegions.lean` は元のセル族の閉領域、`RelativeComplex.lean` は同じ係数族の部分群を使う。
これらは部分塔の対象・射・比較の制限の全構成とは区別する。

| Aの構成義務 | 受理spine候補 | 入力からの構成と証明 |
| --- | --- | --- |
| 閉部分表示のincidence | `ClosedRegion`, `pathEdges`, `pastingFaces`, `pastingContextEdges` | 元の型付き辺名・面名・書き換えprefix/suffixを集合として保持。fieldは入力の幾何的閉包条件だけ |
| 微分と制限の交換 | `ClosedRegion.r_d0`, `ClosedRegion.r_d1`, `ClosedRegion.r_d2`, `ClosedRegion.d1_d0`, `ClosedRegion.d2_d1` | 同じ元輸送・path/pastingCorrectionから生成。零拡張は次数ごとの補助に限り、閉包から交換を証明 |
| 相対kernelと候補支持 | `RelativeComplex.relativeC0`〜`relativeC3`, `C0Group`, `C1Group`, `C0Group_all`, `C1Group_all` | 0〜3次は元の制限のkernel。支持C0は固定頂点のkernel内で支持C1の逆像を取る。全候補許可時は元の相対kernelに一致 |
| 元微分の相対・支持部分群への制限 | `d0_mem_relative`, `d1_mem_relative`, `d2_mem_relative`, `d0Supported`, `d1Supported`, `d2Relative`, `d1Supported_d0Supported`, `d2Relative_d1Supported` | 制限交換から値域条件を導き、元の二乗零を同じcochainへ適用 |
| 同じnative複体とH1/H2 | `cochainComplex`, `firstCochainHomologyIso`, `secondCochainHomologyIso`, `h1_eq_zero_iff`, `h2_eq_zero_iff` | 同じkernel/image商をnative四項複体のhomologyに対応。零性は同じboundaryの存在と双方向 |
| 範囲によらないH0 | `h0Equiv`, `h0Equiv_label` | 元の固定頂点cochainとd0のkernelへの加法同値。元の頂点ラベルを保つ |
| Cycle 1との同じ実修復・再同定 | `ActualRelative.supportedC1_eq`, `supportedC0_eq` | 既存の支持部分群と相対・支持群が同じ部分群であることを証明 |
| 実defectの相対化と存在障害 | `defect_zero_of_face`, `defect_mem_relative`, `obstructionCocycle`, `obstructionClass`, `repair_nonempty_iff_obstruction_zero` | P上の元の実面整合から同じ実全核のdefect零を導く。元3-cellのauthored syzygyからcocycleを導き、支持方程式の両方向から実修復の存在判定を得る |

`RelativeComplex` 内の表の宣言は同namespaceを補って読む。
`ActualRelative` 内の表の宣言は同namespaceを補って読む。
内部の補助はfamily制限・次数ごとの零拡張、path/pastingのcongruence、
membership API、short-complexとnative複体のsegment同定である。

| material premise | 分類 | 出所・使用先 |
| --- | --- | --- |
| 元の有限セル提示・局所係数・実全核輸送 | ambient-boundary、本文由来 | G-129の同じK・M・Tを固定。元の微分と実defectへ |
| 閉領域の端点・両面経路・3-cell面とprefix/suffixのincidence | direction-hypothesis、本文由来 | `ClosedRegion`の入力。`r_d0/r_d1/r_d2`の生成へ。完全な部分塔の制限は後続義務 |
| 固定Pの元基準実面の整合 | direction-hypothesis、本文由来 | 実経路の面等号 `hfixed`。`defect_zero_of_face`→相対cocycleへ |
| 元3-cellのauthored syzygy | direction-hypothesis、本文由来 | G-129と同じ条件4。元の`defect_cocycle`から相対cocycleへ。F・例の実入力では後続の放電義務 |
| 相対微分の値域・二乗零、支持群の一致、native homology同定、H0比較 | discharge-required、構成済み | 表の制限交換と部分群構成から生成。結論をfieldで受け取らない |
| 相対障害の零性と実修復の存在 | discharge-required、双方向証明済み | 元の実faceDefect、Cycle 1の独立実修復と支持方程式、同じ商の零判定。存在を前提にしない |

依存はCycle 1の同じ実修復対応、G-129の `Cochains`・`Cohomology`・
`Defect`・`Solutions` と固定Mathlibの同じnative homology APIである。
元の新規定義を対象入力から生成し、全候補許可のC0/C1同定とH0比較では
閉包・kernel条件を実際に使用する。

```yaml
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "閉領域の元セルincidenceから制限交換、相対・支持四項複体、native H1/H2、範囲によらないH0、実相対障害と存在判定を構成"
  exit_criteria_status: ["3本の制限交換を閉包から証明", "元の微分を同じkernelと支持群へ制限し二乗零を証明", "Cycle 1の支持群と一致", "native複体のhomology同定と全宣言監査はPRに固定"]
  split_reason: none
  completion_candidate: no
  lean_artifacts: [ClosedRegions.lean, RelativeComplex.lean]
  evidence: [ClosedRegion.r_d0, ClosedRegion.r_d1, ClosedRegion.r_d2, RelativeComplex.cochainComplex, RelativeComplex.h0Equiv, ActualRelative.repair_nonempty_iff_obstruction_zero]
  claim_mapping:
    theorem_names: [ClosedRegion.r_d0, ClosedRegion.r_d1, ClosedRegion.r_d2, RelativeComplex.C0Group_all, RelativeComplex.C1Group_all, RelativeComplex.firstCochainHomologyIso, RelativeComplex.secondCochainHomologyIso, ActualRelative.supportedC0_eq, ActualRelative.repair_nonempty_iff_obstruction_zero]
    source_labels: ["G-130 Aの相対・支持複体と存在障害", "n1017 §2.2・2.4"]
    conjuncts: ["制限と同じ微分の交換", "相対・支持複体", "同じnative H0/H1/H2", "元の実相対障害による存在の双方向"]
    undischarged_assumptions: []
    acceptance_point: "相対・支持複体と実存在障害という到達点。部分塔の完全な制限とAの分類・参照変更は後続義務"
    port_status: unported
audits:
  premise_delta:
    discharged: ["閉包からの微分制限と相対・支持複体", "実基準面の整合からdefect相対化", "同じ実修復の存在障害"]
    remaining: ["完全な部分塔と実defect・補正・再同定の制限", "H1 torsorと実自己同型群の同定、参照変更", "FとW1–W5の実入力条件放電"]
  certificate_provenance:
    discharged: ["元微分・閉incidence・実faceDefectから構成"]
    unresolved: []
  proof_use:
    used: ["edge閉包→r_d0", "両面経路閉包→r_d1", "pasting面閉包→r_d2", "実face整合→defect零", "authored syzygy→相対cocycle", "同じ支持方程式・商零判定→実存在障害"]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: ["登録した2fileのfocused check・全宣言#print axiomsはPRに記録"]
  blocking_findings: []
  next_obligation: "部分塔の完全な制限、H1 torsor・実自己同型群・参照座標変更、その後B–F・W1–W5"
```

## Cycle 3：同じ実修復の同型類と自己同型群

```yaml
ledger_type: target_cycle_result
goal: G-130-aat-relative-repair-composition
cycle: 3
goal_blob_sha: 8da0fb4eb75d1cb5c37a9d4ddf5e03c18c0bb8a2
base_oid: e15d7648931778f84011fc4b22f18ec5f6cb3e43
tracking_issue: 5132
report_path: research/reports/G-130-aat-relative-repair-composition.md
selection:
  proof_state_ref: "Cycle 1の実修復・全射、Cycle 2の相対・支持複体と存在障害"
  proof_dag_predecessors: [repairEquiv, repairGauge_coord, repairGauge_eq_self_iff, RelativeComplex.h1_eq_zero_iff, RelativeComplex.h0Equiv]
  milestone: "Aの実修復の同型類を同じH1 torsorで分類し、native実自己同型群を同じ頂点ラベルのH0に同定する"
  proof_obligations: ["支持付き実修復の差と全cocycle作用の構成・相互逆", "全許容頂点再同定のorbitとH1差の零性の双方向", "非空時のnative AddTorsorと代表元に対する作用・差公式", "orbit等号とnative groupoidのisomorphismの双方向", "native Autと範囲によらない相対H0の群同値・全ラベル保持"]
  exit_criteria: ["差と作用の両逆を元の全実修復について証明", "orbitのH1座標同値と代表元に対するtorsor公式", "native isomorphismとorbit、AutとH0の両方向を証明", "単一file focused checkと報告対象全宣言axiom監査"]
  selection_reason: "支持方程式の解だけでなく元の実修復の全対象・全射の分類を閉じる"
  expected_result_type: proof-obligation-discharged
  lean_targets: [ResearchLean/AG/RelativeRepairComposition/SupportedClassification.lean]
  risks: ["非空時のtorsorと無条件の存在判定を混同しない", "異なる再同定をorbit quotientで消すのは同型類だけに限定", "Autはnative実groupoidとし単なるkernelの別名にしない", "範囲包含と参照変更の全比較は後続義務"]
  unchecked: ["実装・検証・独立査読前"]
```

### 同じ実修復のH1 torsorとnative Aut

宣言は `SupportedClassification.lean` の `AAT.AG.RelativeRepairComposition.ActualRelative`。
元の支持付き実修復と、Cycle 2の同じ複体・商を使用する。

| Aの分類要求 | 受理spine候補 | 同じ実操作への接続 |
| --- | --- | --- |
| 全修復のcocycle作用と差 | `repairDifference`, `repairCocycleAction`, `repairCocycleAction_coord`, `repairDifference_action`, `repairCocycleAction_difference`, `repairDifference_sub` | 元の実修復を同じ支持座標へ移し、cocycleを加算して元の実辺へ戻す。差と作用の両逆 |
| 全再同定とH1の零差 | `repairOrbit_mk_eq_iff`, `repairOrbit_mk_eq_iff_difference_zero`, `repairOrbit_mk_eq_iff_coord` | Cycle 1の全許容頂点ラベルを保持する実作用のorbitを取り、同じd0の像と同値にする |
| 同型類のH1座標とtorsor | `repairOrbitEquivH1`, `repairOrbitAddTorsor`, `repairOrbit_vadd_mk`, `repairOrbit_vsub_mk` | 任意の実baseでH1との両逆。非空時のみnative AddTorsorを構成し、作用・差を実代表元の式に同定 |
| native groupoidの同型類 | `repairOrbit_mk_eq_iff_iso` | 同じ元ラベルの射からnative groupoidのisoを生成。逆向きはnative isoの逆射から同じラベルを取得 |
| native実自己同型群とH0 | `relativeLabel`, `labelAut`, `autH0Equiv`, `autSupportedH0Equiv`, `autH0Equiv_label`, `autSupportedH0Equiv_label`, `labelAut_label` | 同じd0-kernelの元からnative Autの射と逆射を構成。native Autから元の全頂点ラベルへ戻す群同値。相対H0・支持H0双方と接続 |

補助 `repairOrbitCoord`・`repairOrbitFromH1` は同じ商のwell-definednessと両逆を与え、
`repairDifference_action_base` は作用のbaseによらない代表元の式を支える。
private `orbitBase` は非空時のtorsor構造の内部選択だけに使う。
存在判定にはこの選択も非空仮定も追加せず、Cycle 2の無条件の同値を用いる。

| premise・certificate | 分類 | 使用・放電 |
| --- | --- | --- |
| 原始T、閉P、候補名、許可集合 | ambient-boundary・本文由来 | 同じ全実核、同じ支持実修復と元のd0/d1を適用 |
| 個々のbase修復、調べる修復・iso・Aut・cocycle | 定理の量化対象 | 個々の座標同値とnative対象・射の往復。存在判定の仮定にはしない |
| 非空の修復型 | direction-hypothesis・本文由来 | GOALの「非空ならtorsor」の条件。native AddTorsor構造の内部baseを選ぶ場合だけ使用 |
| 支持付き作用・差、商への降下、両逆、native AutとH0 | discharge-required・構成済み | 同じ修復往復・d0作用・支持d1のkernelと同じrange商から生成。torsorや群同値を結論fieldで受け取らない |

依存はCycle 1の実対象・全射、Cycle 2の同じH1商とH0比較、固定Mathlibの
`AddAction.orbitRel`・`AddTorsor`・`ActionCategory`・`Groupoid.isoEquivHom`・`Aut`。
構成形はG-129の受理済みH1分類と同じbaseからの商座標化を使うが、
今回の支持付き作用・差・商・両逆はこのfile内で証明する。

```yaml
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "全支持実修復の作用・差の両逆、全頂点再同定orbitと同じH1、native torsorの代表元公式、native isoとorbit、native AutとH0のラベル保持を構成"
  exit_criteria_status: ["任意実修復の作用・差の両逆", "同じH1商の座標同値とnative AddTorsor公式", "native iso/orbit・Aut/H0の全方向", "focused check・全対象宣言axiom監査はPRへ固定"]
  split_reason: none
  completion_candidate: no
  lean_artifacts: [SupportedClassification.lean]
  evidence: [repairCocycleAction_difference, repairOrbitEquivH1, repairOrbitAddTorsor, repairOrbit_vadd_mk, repairOrbit_vsub_mk, repairOrbit_mk_eq_iff_iso, autSupportedH0Equiv]
  claim_mapping:
    theorem_names: [repairDifference_action, repairCocycleAction_difference, repairOrbit_mk_eq_iff_difference_zero, repairOrbitEquivH1, repairOrbit_vadd_mk, repairOrbit_vsub_mk, autH0Equiv, autSupportedH0Equiv_label, repairOrbit_mk_eq_iff_iso]
    source_labels: ["G-130 Aの同型類・自己同型群", "n1017 §2.2・2.5"]
    conjuncts: ["全実修復の支持cocycle差と作用", "同型類は非空なら同じH1 torsor", "native Autは同じH0、全ラベルを保持"]
    undischarged_assumptions: []
    acceptance_point: "元の対象と全射に対する分類。範囲・参照の全比較と部分塔制限は後続義務"
    port_status: unported
audits:
  premise_delta:
    discharged: ["同じ支持実修復のH1 torsor", "native実Autと相対・支持H0の全ラベル保持"]
    remaining: ["部分塔の完全な制限", "範囲包含と参照座標変更の全比較", "B–F・W1–W5"]
  certificate_provenance:
    discharged: ["同じ実修復往復・元d0作用・同じH1商からnative構造を生成"]
    unresolved: []
  proof_use:
    used: ["実修復往復→作用と差の両逆", "全頂点作用→orbitとboundaryの双方向", "同じ商→torsor公式", "元d0kernel→native Autとその逆射・群同値"]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: ["登録1fileのfocused check・全宣言#print axiomsはPRに記録"]
  blocking_findings: []
  next_obligation: "範囲・参照の全比較、部分塔の完全な制限、その後B–F・W1–W5"
```

## Cycle 4：範囲包含と同じ物理的固定条件の参照移送

```yaml
ledger_type: target_cycle_result
goal: G-130-aat-relative-repair-composition
cycle: 4
goal_blob_sha: 8da0fb4eb75d1cb5c37a9d4ddf5e03c18c0bb8a2
base_oid: 7136aee01c1be8aa75c4de4843e9696e415789df
tracking_issue: 5132
report_path: research/reports/G-130-aat-relative-repair-composition.md
selection:
  proof_state_ref: "Cycle 1–3の同じ支持実修復、複体、存在障害、H1 torsor、全Aut/H0"
  proof_dag_predecessors: [repairEquiv, gauge_inclusion, repairOrbitEquivH1, autH0Equiv, obstructionClass, solutionChangeReference, localCoefficients_changeReference, vertexGauge_changeReference]
  milestone: "Aの範囲包含と参照座標変更を同じ実修復・全ラベル・障害へ接続する"
  proof_obligations: ["範囲包含の支持複体/H1/H2とnative実関手・orbitの構成", "identity/compositionとH1座標・torsor・Aut/H0・障害の可換性", "同じ物理的固定辺を保つ参照移送とh'=h-a・固定値h'=-aの両方向", "参照移送のnative groupoid同値と全元ラベル、支持座標・障害の同じ往復"]
  exit_criteria: ["任意S⊆Uについて元の実対象・全射の包含を構成し分類・障害と交換", "任意の同じcoreの参照liftで固定物理辺と移送方程式の全往復", "新旧実作用・全ラベルのnative groupoid同値", "登録focusedと報告対象全宣言axiom監査"]
  selection_reason: "Aの分類を個別範囲・個別参照から全包含と同じ物理操作の移送へ進める"
  expected_result_type: proof-obligation-discharged
  lean_targets: [ResearchLean/AG/RelativeRepairComposition/RangeMaps.lean, ResearchLean/AG/RelativeRepairComposition/ReferenceShift.lean]
  risks: ["参照変更後にh'=0を再課して物理固定辺を変更しない", "新δそのものの相対性を仮定せずアンカーのアフィン項を移す", "full部分塔制限とB–F/W1–W5は後続義務"]
  unchecked: ["実装・検証・独立査読前"]
```

### 同じ実対象・全ラベル・支持障害の比較

`RangeMaps.lean` は、同じ局所係数と閉Pについて任意の候補許可集合S⊆Uを扱う。
`ReferenceShift.lean` は、同じ原始表示・core・比較を保つ任意の代替参照liftを扱う。

| Aの要求 | 受理spine候補 | 同じ実操作との対応 |
| --- | --- | --- |
| 支持複体の包含 | `RelativeComplex.c0Inclusion`, `c1Inclusion`, `cochain_inclusion_comm`, `cochainMap`, `cochain_map_comp` | 元の0/1-cochain値を保ち、2/3-cochainは恒等。元の全微分と可換なnative chain map |
| H1/H2包含と障害 | `h1_boundaries_inclusion`, `h2_boundaries_inclusion`, `h1Inclusion`, `h2Inclusion`, `obstruction_inclusion` | 同じboundaryを大きい支持のboundaryへ送り、同じ実defect cocycleの類を保つ |
| 実包含と分類 | `ActualRelative.rangeFunctor`, `range_functor_map_label`, `range_functor_comp`, `range_orbit_coord_inclusion`, `range_orbit_inclusion_vadd`, `range_orbit_inclusion_vsub`, `range_aut_h0` | 全元の実辺選択と全頂点ラベルを保つnative関手。H1座標・torsor作用/差・同じ相対H0と可換 |
| 同じ物理的な固定条件 | `AnchoredRepair`, `referenceRepairEquiv`, `solution_correction_change_reference`, `anchored_correction_iff_edge` | 新参照の独立実Solutionに旧物理辺の等式を課す。元の実修復と両逆、h'=h-a、固定物理辺とh'=-aの双方向 |
| 移送方程式の全修復 | `AnchoredCorrection`, `anchoredEquiv`, `referenceCorrectionEquiv`, `reference_correction_equiv_val`, `reference_correction_equiv_symm_val`, `anchored_rec_choice` | 新参照の実d1と実defectを使用。移送した固定値から全元の実辺へ戻し、両逆と全候補名を保持 |
| 参照移送の全射 | `anchored_gauge_solution`, `anchoredOriginalHomEquiv`, `referenceGroupoidEquiv`, `reference_groupoid_equiv_map_label`, `reference_groupoid_inclusion` | 任意の元頂点再同定から同じ支持labelを導く。native同値の両関手は同じ全ラベル。範囲包含と関手自体の等式で交換 |
| 参照移送の分類 | `referenceOrbitEquiv`, `anchoredOrbitEquivH1`, `anchoredOrbitAddTorsor`, `reference_orbit_equiv_vadd`, `reference_orbit_equiv_vsub`, `referenceAutEquiv`, `anchoredAutH0Equiv`, `anchored_aut_h0_equiv_label` | 新参照の独立実修復のorbit、native torsor・Autを同じH1/H0へ接続。非空時だけtorsor |
| 同じ係数と障害 | `reference_defect_value`, `anchored_defect_eq`, `reference_cochain_complex_eq`, `anchored_obstruction_cocycle_eq`, `anchored_obstruction_class_eq`, `anchored_repair_nonempty_iff_obstruction_zero` | 実新defectからアンカー項d1(-a)を加えた相対cocycleを生成して旧defectに同定。全範囲の存在障害を保持 |

APIの`*_val`・`*_mk`・`*_label`・`*_choice`は元の座標・実辺・頂点ラベルの
計算を公開する。包含の恒等・合成はcochain/H1/H2/orbitとnative関手で同じ写像を使う。
参照変更後のdefectの相対性を追加仮定せず、移送された物理固定値のアフィン項を使う。

| premise・certificate | 分類 | 使用・放電 |
| --- | --- | --- |
| 原始T、閉P、候補名・S⊆U | ambient-boundary・本文由来 | 元の固定集合の反単調性から支持包含を構成。係数や候補名を変更しない |
| other、hother | direction-hypothesis・本文由来 | 同じcoreの代替liftという入力。G-129の`withAlternativeLift`が全核・輸送・比較条件を再構成 |
| 固定物理面の整合、原始3-cell整合 | direction-hypothesis・本文由来 | 元の相対cocycleと移送したアンカー付き相対障害を生成 |
| 個々の実修復・補正・ラベル・Aut・base | 定理の量化対象 | 全対象と全射の往復。存在判定の仮定にしない |
| 修復型の非空性 | direction-hypothesis・本文由来 | 非空時のnative torsorだけ。新旧非空性は実修復同値から移送 |
| 包含、全射、商写像、両逆、native構造、アンカー付き障害 | discharge-required・構成済み | 元の実修復往復・元d0/d1/d2・同じboundary商から生成。結果を入力fieldに受け取らない |

受理依存はCycle 1–3とG-129の参照不変構成。参照変更の新しい固定物理条件、
支持方程式・全射・native群oidと分類への接続は今回の宣言で証明する。
完全な部分塔の制限、B–F・W1–W5は後続義務である。

```yaml
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "全範囲包含のnative複体/実関手/H1/H2/torsor/Aut/障害比較と、任意参照liftで同じ物理固定条件を移送した全対象・全射・分類・障害の往復"
  exit_criteria_status: ["任意S⊆Uで元の対象・全射を保持する包含と全分類・障害の交換", "h'=h-a、h'fixed=-aの全修復往復", "新旧実作用と任意の元ラベル・native群oid同値", "focused check・全宣言axiom監査はPRへ固定"]
  split_reason: none
  completion_candidate: no
  lean_artifacts: [RangeMaps.lean, ReferenceShift.lean]
  evidence: [cochain_map_comp, range_orbit_inclusion_vadd, range_aut_h0, referenceCorrectionEquiv, referenceGroupoidEquiv, anchoredOriginalHomEquiv, reference_groupoid_inclusion, anchoredAutH0Equiv, anchored_repair_nonempty_iff_obstruction_zero]
  claim_mapping:
    theorem_names: [cochainMap, h1Inclusion, h2Inclusion, range_functor_comp, range_orbit_equiv_h1, referenceRepairEquiv, anchoredEquiv, reference_correction_equiv_val, anchoredOriginalHomEquiv, reference_groupoid_inclusion, anchored_obstruction_class_eq]
    source_labels: ["G-130 AのS⊆Tとの対応・同じ物理操作の参照座標移送", "n1017 §2.2・2.5"]
    conjuncts: ["同じ支持複体・実対象/射と分類・障害の包含", "同じ物理固定辺と全ラベルの参照変更", "アンカーを反映した同じ相対障害"]
    undischarged_assumptions: []
    acceptance_point: "Aの包含と参照比較。部分塔の完全な制限、B–F/W1–W5は後続義務"
    port_status: unported
audits:
  premise_delta:
    discharged: ["範囲包含と全分類・障害の比較", "同じ物理固定条件の全参照移送・全射・分類・障害"]
    remaining: ["部分塔の完全な制限", "B–F・W1–W5"]
  certificate_provenance:
    discharged: ["元の全実核の支持部分群と同じ実微分から包含を生成", "同じcoreの代替liftから実修復・新実defectと移送アンカーを生成"]
    unresolved: []
  proof_use:
    used: ["支持包含→boundary包含→native商写像", "同じ実包含→torsor/Aut/H0/障害の交換", "実solution参照変更→固定物理辺とアフィン固定値の双方向", "元の全vertexGauge→新native全射同値", "新実defect+移送アンカー→同じ相対cocycle/障害"]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: ["登録2fileのfocused check・全宣言#print axiomsはPRへ固定"]
  blocking_findings: []
  next_obligation: "元の全typed経路・面・3-cellと塔の部分表示制限、その後B–F・W1–W5"
```

## Cycle 5：閉領域の全表示・元実塔・同じ補正と再同定の制限

```yaml
ledger_type: target_cycle_result
goal: G-130-aat-relative-repair-composition
cycle: 5
goal_blob_sha: 8da0fb4eb75d1cb5c37a9d4ddf5e03c18c0bb8a2
base_oid: f0d77f93036353dd47c0fc3961da1151c8ac7c63
tracking_issue: 5132
report_path: research/reports/G-130-aat-relative-repair-composition.md
selection:
  proof_state_ref: "Cycle 1–4の支持実修復・相対複体・分類・包含/参照比較と、ClosedRegionsの原始セル制限"
  proof_dag_predecessors: [ClosedRegion, r_d0, r_d1, r_d2, OriginalTowerPresentation, solutionCorrection, vertexGauge_correction, repairEquiv]
  milestone: "Aの閉領域に全typed表示と元実塔を構成し、全核・輸送・微分・実defect・補正・全再同定の制限を同じ値で接続する"
  proof_obligations: ["閉辺/面/3-cellの経路・全書換え列を部分型へ制限し元幾何へ戻す", "元対象/強い辺・core・lift・比較を保つOriginalTowerPresentationの制限", "実全核の同じ輸送と元0–3cochain制限の対応・全微分交換", "実defect・修復/補正・全元再同定の制限とnative関手", "原始実3-cell整合の制限・固定条件と範囲包含の交換"]
  exit_criteria: ["全typedセル/書換えの元幾何を保持する制限", "新追加仮定なく同じ実塔/全核/輸送を生成", "元全微分・実defect・実補正・全再同定との可換性", "固定条件/全ラベルのnative制限と範囲包含比較", "登録focusedと全対象宣言axiom監査"]
  selection_reason: "相対複体の原始添字制限を完全な実部分塔へ接続し、B/Cの実局所合成の入力を生成する"
  expected_result_type: proof-obligation-discharged
  lean_targets: [ResearchLean/AG/RelativeRepairComposition/RestrictedPresentation.lean, ResearchLean/AG/RelativeRepairComposition/TowerRestriction.lean]
  risks: ["3-cellを面の集合だけへ忘れず全typed順序・orientation・prefix/suffixを保持", "係数/射を自分の像や供給certificateへ縮めない", "原始実syzygyを仮定から適切に制限し実defectへ接続"]
  unchecked: ["構成・登録検証・独立査読前"]
```

### 元の表示・実操作と制限先の対応

| Aの要求 | 受理spine候補 | 保持する対象・計算 |
| --- | --- | --- |
| 全typed部分表示 | `ClosedRegion.presentation`, `restrictPasting`, `forget_restrict_pasting`, `forget_three_left`, `forget_three_right` | 元の部分型セル、全経路、各faceの向き・prefix/suffix、隣接middle path、両3-cellの完全なtyped列。bookend輸送後の列そのものの等号 |
| 同じ係数と元制限複体 | `restrictCoefficients`, `nativeR0`–`nativeR3`, `nativeC1Equiv`, `native_d0_eq`, `native_d1_eq`, `native_d2_eq` | 元の端点係数・各edge輸送と全0–3微分。先行`ClosedRegions`の原始添字複体と同じ値へreindex |
| 元実塔と全核 | `restrictLiftData`, `restrictTower`, `restrict_tower_coefficients`, `restrict_selected_path_lift` | 元対象・実辺と両strong性・core・lift・比較を制限。生成される全実核・輸送は同じ係数系の制限そのもの |
| 元実defectと3-cell整合 | `restrict_canonical_face`, `restrict_face_defect`, `restrict_defect`, `restrict_whisker`, `restrict_authored_pasting`, `restrict_authored_syzygy` | strong一意性で同じcanonical比較/全fiber輸送を同定。実比較をtemporal順に合成して両3-cellの整合を制限し、元kernel defectを保持 |
| 独立実修復・補正・再同定 | `restrictSolution`, `restrict_solution_correction`, `restrict_vertex_gauge`, `restrictRepair`, `restrictCorrection`, `restrict_coord`, `restrict_rec` | 各実choiceと固定実辺を保持し、独立方程式の制限を元d1/defectから構成。全補正と復元・元vertex gaugeは同じ値で可換 |
| nativeな対象と全射の制限 | `repairRestrictionFunctor`, `correctionRestrictionFunctor`, `repair_restriction_map_label`, `coord_restriction_functors`, `rec_restriction_functors` | 選択した各元vertex labelを保持するnative関手。座標化/復元の比較は対象写像だけでなく関手そのものの等号 |
| 固定名・全範囲包含 | `restricted_fixed_range`, `repairRelaxationFunctor`, `repair_restriction_relaxation` | 固定部分/候補/許可集合を同じ元edge名で選択。任意の固定集合包含について、制限と範囲relaxationが対象・全射で交換 |

全順序付きface contextのtraceは内部の幾何比較APIであり、
`pasting_trace_injective`によって同じbookendを持つ全typed列を復元できる。
最終APIはtraceの等号だけでなく、bookend transport後の元列そのものの等号を示す。
零延長は次数ごとの比較sectionにだけ使い、chain mapとする追加主張はない。

| premise・構成条件 | 分類 | 出所・使用/放電 |
| --- | --- | --- |
| 原始K、閉領域Uの0–3セルと全閉包 | ambient-boundary・本文由来(G-130 A) | 元の部分型、両face経路、全context・step・3-cellを生成。閉包から全中間経路の所属を導く |
| 元の一般T、圏p/q、原始対象/辺/core/lift/比較 | ambient-boundary・本文由来(G-130 A) | 同じ実対象/辺/比較を`restrictTower`へ制限。原始入力の特別化なし |
| 元strong・全核可換・transport bijective・底/core整合・中央化 | direction-hypothesis・本文由来(G-130 A) | 新fieldは元の同じfieldの適用と経路評価保存から生成。新repair/cohomology/defect結論をfieldへ受け取らない。F/Wでの具体的放電は後続 |
| 原始実3-cell整合 | direction-hypothesis・本文由来(G-130 A) | `restrict_whisker`と`restrict_authored_pasting`の同じ実経路比較から制限先の整合を証明 |
| 抽象Mの群・edge同型・face輸送整合 | direction-hypothesis・本文由来(一般複体) | 同じMを制限して全微分交換。実適用でMはTから生成した全実kernel系そのもの |
| 固定vertex/edge名・範囲包含、個々の実修復/補正/label | 本文由来の入力条件・定理の量化対象 | 任意の元固定条件・全作用元を選択部分へ制限。修復可否を事前に仮定しない |
| 制限先の全表示/実塔・係数/微分・defect・独立解/方程式・全関手 | discharge-required・構成済み | 上表のconstructor/比較APIから生成し、結論相当certificateを入力にしない |

```yaml
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "全typed閉部分表示・同じ原始実塔/全核・全微分/実defect/補正/再同定の制限と全ラベルnative関手、範囲包含の交換"
  exit_criteria_status: ["全typed経路/面context/両3-cellの列そのものを保持", "同じ実塔条件と全kernel輸送を元入力から生成", "原始実syzygy/defect/補正/全gaugeの制限可換性", "固定条件・全ラベルnative関手とrelaxationの全成分等号", "登録2file個別focused・全対象axiom監査はPRへ固定"]
  split_reason: none
  completion_candidate: no
  lean_artifacts: [RestrictedPresentation.lean, TowerRestriction.lean]
  evidence: [forget_restrict_pasting, forget_three_left, forget_three_right, native_d0_eq, native_d1_eq, native_d2_eq, restrict_tower_coefficients, restrict_defect, restrict_authored_syzygy, restrict_coord, restrict_rec, coord_restriction_functors, rec_restriction_functors, repair_restriction_relaxation]
  claim_mapping:
    theorem_names: [presentation, restrictTower, restrict_tower_coefficients, native_r_d0, native_r_d1, native_r_d2, restrict_authored_syzygy, restrict_defect, restrict_vertex_gauge, repairRestrictionFunctor, correctionRestrictionFunctor, coord_restriction_functors, rec_restriction_functors, repair_restriction_relaxation]
    source_labels: ["G-130 Aの閉じた部分表示・同じ実対象/射/比較/係数の制限と可換性", "n1017 §2.1–2.2"]
    conjuncts: ["全typed元幾何の保存", "同じ元実塔/全kernel系/全微分/実defect", "実修復/補正と全labelのnative制限・同じ往復", "固定候補名/範囲包含との交換"]
    undischarged_assumptions: []
    acceptance_point: "単一閉領域への全原始実データと修復の制限。閉領域同士の交差/被覆descent・有限局所合成とB–F/W1–W5は後続義務"
    port_status: unported
audits:
  premise_delta:
    discharged: ["全typed部分表示/経路/面/3-cell生成と元幾何保存", "元実塔/全kernel/輸送/微分/実defect/実syzygyの制限", "固定実修復/独立方程式の制限と全gaugeのnative関手・範囲比較"]
    remaining: ["閉領域同士の交差・被覆の全比較とdescent", "B–F・W1–W5"]
  certificate_provenance:
    discharged: ["元セルのincidence閉包から全typed部分表示を生成", "元実辺と同じfieldから全塔/係数系を生成", "同じstrong一意性/実経路比較からdefect・syzygyを制限", "元独立解/方程式・d0から対象と全射の関手を生成"]
    unresolved: []
  proof_use:
    used: ["閉context→全中間path/typed書換えの生成", "元strong/経路評価→canonical/全fiber輸送の同一性", "同じ実比較のtemporal合成→syzygyの制限", "元d1/defect→独立方程式制限→座標/復元の全関手比較", "元d0/固定名→全gauge制限→範囲relaxation比較"]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: ["登録2fileのfocused・全新規宣言/自動equation宣言#print axiomsはPRへ固定"]
  blocking_findings: []
  next_obligation: "閉領域の交差・被覆と同じ相対複体の完全列、全修復descent、その後B–F・W1–W5"
```

## 後続の構成義務

Aの部分表示と全次数の制限、相対複体・H0/H1/H2分類、参照座標変更、Bのdescentと
統合障害、Cの有限生成と局所厳密合成、Dの双対分類、Eの更新・文脈同値・分割、
Fの全アフィン実現、W1–W5の全要求と一般定理への接続が必要である。
G-130全体の判定には固定GOALの全完了条件と独立最終査読を用いる。


## Cycle 6：同じ固定部分を保つ閉被覆の相対短完全列

```yaml
ledger_type: target_cycle_result
goal: G-130-aat-relative-repair-composition
cycle: 6
goal_blob_sha: 8da0fb4eb75d1cb5c37a9d4ddf5e03c18c0bb8a2
base_oid: 0ee7be5084c9382489c8d5772d7ddc663b5f0d79
tracking_issue: 5132
report_path: research/reports/G-130-aat-relative-repair-composition.md
selection:
  proof_state_ref: "Cycle 5の全typed実塔制限とCycle 2の相対kernel複体"
  proof_dag_predecessors: [ClosedRegion.presentation, forget_three_left, forget_three_right, nativeC1Equiv, native_d0_eq, native_d1_eq, native_d2_eq, relativeC0, relativeC1, relativeC2, relativeC3]
  milestone: "Bの閉二領域被覆に、同じ元全係数と固定Pを保つ相対cochain次数0–3短完全列を構成する"
  proof_obligations: ["交差・合併の全typed閉包と元セル包含", "制限表示内のnative P∩Uを全閉包から構成", "相対原始添字族とnative restriction kernelを同定", "対角制限・差写像の全次数の単射/完全性/全射", "元微分との交換とnative複体の短完全列"]
  exit_criteria: ["同じ元0–3セル、固定P、full coefficientを使用", "短完全性をexactness certificateなしで各元値から証明", "同じ全微分と制限/差が交換", "native相対複体へ群/微分を接続", "登録focusedと全宣言公理監査"]
  selection_reason: "全typed局所実塔を受理済み相対複体へ接続し、修復descentとH1/H2連結写像の入力短完全列を生成する"
  expected_result_type: proof-obligation-discharged
  lean_targets: [ResearchLean/AG/RelativeRepairComposition/ClosedCovers.lean, ResearchLean/AG/RelativeRepairComposition/RelativeFamilies.lean, ResearchLean/AG/RelativeRepairComposition/NativeFixedRegions.lean, ResearchLean/AG/RelativeRepairComposition/RelativeCoverComplex.lean]
  risks: ["同じPを別固定条件へ置換しない", "typed三セルの全文脈を保持", "依存係数の元添字を保持", "degreewise零延長をchain mapと扱わない", "exactness/descentの結論certificateを受け取らない"]
  unchecked: ["実装・検証・独立査読前"]
```


### 同じ元の固定部分・係数・全微分への対応

| Bの短完全列に必要な条項 | 宣言 | 入力からの構成と保持する値 |
| --- | --- | --- |
| 閉交差・閉合併、全0–3セルを覆う被覆 | `ClosedRegion.inter`, `union`, `Inclusion`, `Cover` | 元端点、両面path、両三セルの全face/context/bookend閉包を各領域の閉包から生成。Coverは元セル集合の和が全体であるという入力条件だけ |
| 制限先の同じ固定部分 | `nativeIntersection`, `path_edge_mem_forget`, `pasting_face_mem_forget`, `pasting_context_edge_mem_forget` | 全元セル名のP所属の逆像。完全typed三セル列とbookend輸送の保存から全閉包fieldを生成。別の固定部分や追加closure証書を供給しない |
| 相対族とnative kernel | `Family.relative`, `univRelativeEquiv`, `native0`–`native3`, `nativeComplexIso`, `originalComplexIso` | 各元係数群を保持し、P∩Uで零という条件をnative restriction kernelと同定。各局所複体と元Kの大域複体へ、全次数・同じ微分を含むnative同型を構成 |
| 任意領域包含の制限と全微分 | `r0Between`–`r3Between`, `inclusion_d0`–`inclusion_d2`, `RelativeCover.r_d0`–`r_d2` | 同じ端点・両面path・両三セルrouteから微分交換を導出。零延長は各次数のsectionだけとして使用 |
| 対角制限・固定targetの差写像 | `diagonal0`–`diagonal3`, `difference0`–`difference3`, `diagonalMap`, `differenceMap` | 全元値を保持。差は固定targetと同じr_U−r_V。局所修復差z=h_V−h_Uは後続義務として区別 |
| 次数ごとの単射・完全性・全射 | `Family.cover_diagonal_injective`, `cover_glue`, `cover_difference_surjective`, `degree0_exact`–`degree3_exact` | 共有値の一致から全元familyを復元し、零延長で任意の重なりの値を差の像として構成。exactnessをfieldや仮定で受け取らない |
| native全複体の短完全列 | `cover_short_exact`, `originalCoverIso`, `original_cover_short_exact` | 各次数の具体的完全性からnative ShortComplex.ShortExactを生成。大域側は元Kの受理済相対複体そのものへ同型で戻し、両native写像も含めて比較 |
| 新述語の成立・不成立 | `coverAllLeft`, `not_cover_empty`, `Inclusion.refl`, `not_inclusion_all_empty`, `zero_mem_relative`, `not_relative_single` | 被覆・包含は全領域で成立し、非空の元頂点をもつ空領域で不成立。相対族は零族で成立し、含まれる固定セルで非零な実係数値を置いた族で不成立 |

### Material premise と生成経路

| 入力・前提 | 分類 | 生成・使用・放電 |
| --- | --- | --- |
| 元有限typed表示K、閉P/U/V、元セル集合 | ambient-boundary | GOAL A/Bの同じ入力。交差/合併、部分表示内のnative P∩Uを全incidenceから生成 |
| 同じLocalCoefficients M、全係数群・元edge transportとface relation | 一般複体定理のdirection-hypothesis | 実適用のMはCycle 5で同定したT.toTower.localCoefficientsとその制限。今回は全核生成の条件を変更せず、元の全微分を使う |
| U/Vの全0–3セル被覆 | ambient-boundary | GOAL Bの閉被覆。元値のgluingと対角単射に使用。修復存在/整合/完全性を入力fieldに含まない |
| 相対群、native kernel同定、微分保存、対角単射/差全射/完全性、native短完全性 | discharge-required、今回放電済み | 同じ元値、元閉包と微分、degreewise sectionと値のgluing、受理済相対kernel API、native homological-complex APIから構成 |
| 原始実tower条件、具体的有限体/全核/指定W1–W5 | 全GOALの後続義務 | 今回の一般相対短完全列の完成からF/Wの具体入力放電を推論しない |

```yaml
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "閉交差/合併とnative固定部分、全相対族/複体同型、元微分制限交換、次数0–3と全native複体の短完全列を構成"
  exit_criteria_status: ["同じ元全係数/セル/Pを保持", "全typed閉包を生成", "各元値の完全性を生成", "全微分とnative複体の同型/短完全列", "登録focusedと209個別宣言公理監査"]
  split_reason: none
  completion_candidate: no
  lean_artifacts: [ClosedCovers.lean, RelativeFamilies.lean, NativeFixedRegions.lean, RelativeCoverComplex.lean]
  claim_mapping:
    theorem_names: [nativeComplexIso, originalComplexIso, cover_short_exact, original_cover_short_exact]
    source_labels: ["GOAL Bの相対cochain短完全列", "n1017 §2.3（短完全列(E)）"]
    conjuncts: ["全閉領域/P∩U", "同じ元係数/全微分", "元Kの相対複体と各局所native複体", "対角制限とr_U−r_V", "次数ごとと全native複体の短完全性"]
    undischarged_assumptions: ["一般Mの群/輸送/face relationと本文の閉領域/被覆条件は定理入力", "G-130 Bのdescent/統合障害とC–F/Wは後続"]
    acceptance_point: "独立に再利用する同じ元相対複体の閉被覆短完全列"
    port_status: not-applicable
audits:
  premise_delta:
    discharged: ["交差/合併/native P∩Uの全閉包", "相対membershipと全複体の同型", "各元値の完全性とnative短完全性"]
    remaining: ["本文の一般入力条件", "後続descent/統合障害とC–F/W"]
  certificate_provenance:
    discharged: ["ShortExactをdegreewise元値gluingから生成", "全局所微分は元d0–d2と一致"]
    unresolved: []
  proof_use:
    used: ["元全incidence閉包", "両typed三セルの完全忘却等式", "元全微分と閉制限", "同じPのkernel条件", "元全セルのcover条件"]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: ["4登録source個別focused exit0", "同じ本体の単一audit209宣言標準公理、SHA256 98b8b022351023ad41f12e64d16ee4d50cc0dfb59b00cdba3d8b6a1fbd049909"]
  blocking_findings: []
  next_obligation: "同じ実修復の制限関手によるnative homotopy pullback、有限被覆のcocycle整合と統合障害/連結写像"
```

新規明示宣言は191件。elaborationで現れたconstructor/accessor/生成式等18件を含め、
209宣言を個別に公理監査した。生成式には参照した先行pasting定義の式も含む。
`inter_left` / `inter_right` / `to_all` / `cover_all_left` を正規の証明名とし、旧名の互換theorem aliasをdeprecatedとして保持する。
rootの自己監査は受理候補であり、標準PRレビューの独立判定と区別する。


## Cycle 7：元の実修復と全再同定の閉二領域descent

```yaml
ledger_type: target_cycle_result
goal: G-130-aat-relative-repair-composition
cycle: 7
goal_blob_sha: 8da0fb4eb75d1cb5c37a9d4ddf5e03c18c0bb8a2
base_oid: 63140a52534b480dcb3a07425787bb1d84a281dc
tracking_issue: 5132
report_path: research/reports/G-130-aat-relative-repair-composition.md
selection:
  proof_state_ref: "Cycle 6の相対閉被覆短完全列とCycle 5の同じ実塔/修復制限"
  proof_dag_predecessors: [degree0_exact, difference0_surjective, diagonal0_injective, degree1_exact, diagonal1_injective, diagonal2_injective, nativeSupported0, nativeSupported1, native_supported_d0, native_supported_d1, originalSupported0, originalSupported1, restrict_defect, repairGroupoidEquivalence]
  milestone: "Bの閉二領域被覆について元Kの独立実修復groupoidを、局所実修復と重なりでの同型のnative homotopy pullbackへ同値として貼り合わせる"
  proof_obligations: ["元添字の全相対方程式/作用groupoidと全ラベルの包含制限", "元Kとnative局所実修復への全辺/全ラベルを保つ同値", "制限関手が同じ実辺と全再同定を制限すること", "native commaの対角制限関手", "degree0全射/degree1完全/degree2単射からseam厳密化とglobal修復復元", "degree0完全/単射から全射の復元とfaithful", "元Kの実修復と局所native groupoid間の全同値と比較自然同型"]
  exit_criteria: ["元の独立実修復・全元辺/全vertex labelsを保持", "本文以外のdescent/effectivity/gluing certificateを入力しない", "重なりの再同定と全可換な局所射を扱うnative同値", "制限の値と全inverse/unit/counitを比較", "focusedと全宣言の個別公理監査・scan"]
  selection_reason: "受理済の元値短完全性を、pi0だけでは失われるseamと全安定化群を保つ実修復descentへ直接接続する"
  expected_result_type: proof-obligation-discharged
  lean_targets: [ResearchLean/AG/RelativeRepairComposition/AffineEquation.lean, ResearchLean/AG/RelativeRepairComposition/CoverEquation.lean, ResearchLean/AG/RelativeRepairComposition/CommaCoordinates.lean, ResearchLean/AG/RelativeRepairComposition/NativeEquationBridge.lean, ResearchLean/AG/RelativeRepairComposition/NativeDescent.lean]
  risks: ["元Kをall-subtypeのみに置換しない", "native局所のnested型をsilent同一視しない", "全labelsをpi0へ落とさない", "seamと差写像の符号", "degreewise延長をchain mapと扱わない", "exactness/descent結果のfield逃げをしない"]
  unchecked: ["実装・検証・独立PR査読前"]
```

有限被覆の三重cocycleと組立て比較、統合障害/連結写像は、この二領域native実修復同値に続く独立の到達点である。今回を全GOALの完了候補としない。

### Cycle 7 の実装結果

```yaml
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "元Kの独立実修復groupoidを、同じ実修復制限によるnative局所comma groupoidへ同値として復元。全元辺choices、全vertex labels、恒等seam、元の制限への比較自然同型を構成"
  exit_criteria_status: ["元K実修復・全choices/labels: original/nativeRepairEquationEquivalenceとequivalence_*値API", "結論certificateなし: degreewise短完全性からglue_solution/full/faithful/ess_surjを生成", "全重なり射と可換な局所射: native Commaとis_groupoid", "全inverse/unit/counit: native EquivalenceとglobalRestrictionComparisonIso", "5登録source focusedと全135明示宣言の個別公理監査を確認"]
  split_reason: none
  completion_candidate: no
  lean_artifacts: [AffineEquation.lean, CoverEquation.lean, CommaCoordinates.lean, NativeEquationBridge.lean, NativeDescent.lean]
  evidence: [CoverEquation.glue_solution, CoverEquation.diagonal_full, CoverEquation.diagonal_faithful, CoverEquation.diagonal_ess_surj, CommaCoordinates.equivalence, ActualEquation.originalRepairEquationEquivalence, ActualEquation.nativeRepairEquationEquivalence, NativeDescent.equivalence, NativeDescent.globalRestrictionComparison]
  claim_mapping:
    theorem_names: [NativeDescent.equivalence, NativeDescent.equivalence_left_choice, NativeDescent.equivalence_right_choice, NativeDescent.equivalence_left_map_value, NativeDescent.equivalence_right_map_value, NativeDescent.equivalence_seam_label, NativeDescent.globalRestrictionComparison]
    source_labels: ["固定GOAL B: 二領域native実修復homotopy pullback", "n1017 §2.3(E)"]
    conjuncts: ["大域側は元KそのもののRepairGroupoid", "各局所は同じ実塔の閉部分表示とnative P∩U", "重なりに全実再同定を保持", "全edge choicesとvertex labelsを保つ制限", "完全なnative同値のinverse/unit/counit", "受理済実修復制限への自然同型と恒等seam"]
    undischarged_assumptions: []
    acceptance_point: "今回の二領域descentの全exit criteriaを入力から構成。判定は固定headの独立PR監査へ渡す"
    port_status: unported (Research-proved)
audits:
  premise_delta:
    discharged: ["d1∘d0零: RelativeCover.d1_d0", "実δのP零: ActualRelative.defect_mem_relative", "元/native全coords: Cycle6原値同型", "seam吸収: difference0_surjective", "global対象復元: degree1_exact/diagonal2_injective", "全射復元: degree0_exact/diagonal1_injective", "faithful: diagonal0_injective", "全comma比較: 生成済equivalenceのunit/counit", "同じ実辺制限: correctionChoice_solutionCorrection"]
    remaining: ["有限被覆の三重cocycleと細分化/組立て比較", "指定局所案H1条件・Ω/connecting/kernel比較", "C–F、W1–W5"]
  certificate_provenance:
    discharged: ["全affine action: 元d0からAddAction", "全native座標同値: 受理済actual repair/correctionと原値群同型", "Fully faithful/EssSurj: 閉被覆degreewise完全性から対象/全射を構成", "comma比較とnative同値: 生成済座標同値の全unit/counit", "制限比較: 同じ実辺のchoice復元から全対象同一性と恒等ラベルの両方向の射"]
    unresolved: []
  proof_use:
    used: ["hfixedから実δのP零", "Cover全0–3-cell条件の先行完全性", "difference0全射によるseam吸収", "degree1完全/degree2単射による大域equation", "degree0完全/単射による全morphism復元", "original/native支持群同型とd0/d1交換", "actual solutionCorrection/correctionChoice両逆"]
    unused: ["d2δ零はこの二領域effectivityの証明では不要。後続Ω/connectingには別途用いる"]
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  blocking_findings: []
  next_obligation: "Bの有限被覆cocycle・細分化/組立て、統合障害と連結写像"
```

今回のmaterial premiseは、元の`OriginalTowerPresentation`の許された実塔・全核入力、固定閉領域P/U/V、P上の元の実lift/comparatorの面整合、全cell被覆である。全核係数Mと実δは同じTから生成する。generic `Equation` APIのd1∘d0零はnative適用時に先行`RelativeCover.d1_d0`で放電し、affine RHSを自由な外部certificateから供給しない。Coverには元集合の被覆だけを持たせ、完全性、effectivity、同値を入力へ移さない。元Kのgroupoidからall-cellの方程式への原値同型を明示し、大域実修復をall-cell subtypeの実塔へ置換しない。

重なりの再同定を持つ全comma対象に対し、`glue_solution`が全局所補正とdegree0差のsectionから大域補正を構成する。degree0完全性が全compatible局所射を復元する。`Equivalence`のinverse/unit/counitを含む全native構造を用い、pi0だけの対応へ落とさない。恒等ラベルの実際の比較射と逆射から`globalRestrictionComparisonIso`を構成し、既存の同じ実修復制限関手と自然に比較する。

正負の回帰は、零RHSの全affine equationの零解と、非零RHS/零d1の解不存在、全被覆の先行非空性/空被覆失敗、全原値のobject/map/inverse/unit/counitのAPI、seam恒等性を対象にする。W1–W5の実有限体入力は今回のgeneric回帰から放電済みと数えない。

### Cycle 7 の受理spineと検証

受理spineは次の5fileの明示135宣言である。仮のcycle足場をproductionへ収録せず、全宣言にdocstringを持たせる。

`AffineEquation.lean` (23宣言):

`Equation.Solution`, `Equation.solution_zero_nonempty`, `Equation.not_solution_zero_differential`, `Equation.gauge`, `Equation.addAction`, `Equation.Groupoid`, `Equation.hom_condition`, `Equation.homOfLabel`, `Equation.homOfLabel_label`, `actionLabelFunctor`, `changedLabelFunctor`, `changed_label_inverse_equivariant`, `changedLabelInverse`, `changed_label_functor_label`, `changed_label_left_obj`, `changed_label_right_obj`, `changedLabelUnit`, `changedLabelCounit`, `changedLabelEquivalence`, `changed_label_unit_label`, `changed_label_unit_inv_label`, `changed_label_counit_label`, `changed_label_counit_inv_label`。

`CoverEquation.lean` (20宣言):

`CoverEquation.defect`, `CoverEquation.defect_all`, `CoverEquation.restrict_defect`, `CoverEquation.Solution`, `CoverEquation.Groupoid`, `CoverEquation.restrictSolution`, `CoverEquation.restrict_gauge`, `CoverEquation.restrictionFunctor`, `CoverEquation.restriction_obj_value`, `CoverEquation.restriction_map_value`, `CoverEquation.Descent`, `CoverEquation.diagonalObj`, `CoverEquation.diagonalFunctor`, `CoverEquation.diagonal_seam_label`, `CoverEquation.diagonal_faithful`, `CoverEquation.diagonal_full`, `CoverEquation.glue_solution`, `CoverEquation.diagonal_ess_surj`, `CoverEquation.diagonal_is_equivalence`, `CoverEquation.descentEquivalence`。

`CommaCoordinates.lean` (15宣言):

`CommaCoordinates.leftRestriction`, `CommaCoordinates.rightRestriction`, `CommaCoordinates.leftComparison`, `CommaCoordinates.rightComparison`, `CommaCoordinates.left_comparison_hom`, `CommaCoordinates.right_comparison_hom`, `CommaCoordinates.restoreFunctor`, `CommaCoordinates.restore_seam`, `CommaCoordinates.restore_left_obj`, `CommaCoordinates.restore_right_obj`, `CommaCoordinates.restore_left_map`, `CommaCoordinates.restore_right_map`, `CommaCoordinates.restore_is_equivalence`, `CommaCoordinates.equivalence`, `CommaCoordinates.comma_is_groupoid`。

`NativeEquationBridge.lean` (55宣言):

`ActualEquation.defectFamily`, `ActualEquation.native_defect_value`, `ActualEquation.fixed_edges_all`, `ActualEquation.native_supportedC0_eq`, `ActualEquation.native_supportedC1_eq`, `ActualEquation.nativeGaugeEquiv`, `ActualEquation.nativeEdgeEquiv`, `ActualEquation.native_gauge_value`, `ActualEquation.native_gauge_inverse_value`, `ActualEquation.native_edge_value`, `ActualEquation.native_edge_inverse_value`, `ActualEquation.native_d0`, `ActualEquation.nativeEquationEquiv`, `ActualEquation.native_equation_value`, `ActualEquation.native_equation_inverse_value`, `ActualEquation.native_equation_equivariant`, `ActualEquation.nativeCorrectionEquationEquivalence`, `ActualEquation.nativeRepairEquiv`, `ActualEquation.native_repair_equivariant`, `ActualEquation.nativeRepairEquationEquivalence`, `ActualEquation.native_repair_obj_value`, `ActualEquation.native_repair_map_value`, `ActualEquation.native_repair_inverse_map_value`, `ActualEquation.native_repair_inverse_choice`, `ActualEquation.native_repair_unit_label`, `ActualEquation.native_repair_counit_label`, `ActualEquation.native_repair_counit_inv_label`, `ActualEquation.original_supportedC0_eq`, `ActualEquation.original_supportedC1_eq`, `ActualEquation.originalGaugeEquiv`, `ActualEquation.originalEdgeEquiv`, `ActualEquation.original_gauge_value`, `ActualEquation.original_gauge_inverse_value`, `ActualEquation.original_edge_value`, `ActualEquation.original_d0`, `ActualEquation.original_defect_value`, `ActualEquation.originalEquationEquiv`, `ActualEquation.original_equation_equivariant`, `ActualEquation.originalRepairEquiv`, `ActualEquation.original_repair_equivariant`, `ActualEquation.originalRepairEquationEquivalence`, `ActualEquation.original_repair_obj_value`, `ActualEquation.original_repair_inverse_choice`, `ActualEquation.original_repair_map_value`, `ActualEquation.original_repair_inverse_map_value`, `ActualEquation.original_repair_unit_label`, `ActualEquation.original_repair_counit_label`, `ActualEquation.native_repair_inverse_obj_value`, `ActualEquation.native_repair_left_obj`, `ActualEquation.native_repair_right_obj`, `ActualEquation.original_equation_value`, `ActualEquation.original_equation_inverse_value`, `ActualEquation.original_repair_inverse_obj_value`, `ActualEquation.original_repair_left_obj`, `ActualEquation.original_repair_right_obj`。

`NativeDescent.lean` (22宣言):

`NativeDescent.LocalGroupoid`, `NativeDescent.restrictionFunctor`, `NativeDescent.restriction_map_value`, `NativeDescent.restriction_obj_choice`, `NativeDescent.globalRestrictionFunctor`, `NativeDescent.global_restriction_obj_choice`, `NativeDescent.global_restriction_map_value`, `NativeDescent.originalRestrictionFunctor`, `NativeDescent.global_restriction_obj_eq`, `NativeDescent.globalRestrictionComparisonHom`, `NativeDescent.globalRestrictionComparisonIso`, `NativeDescent.globalRestrictionComparison`, `NativeDescent.global_restriction_comparison_label`, `NativeDescent.Descent`, `NativeDescent.commaEquivalence`, `NativeDescent.equivalence`, `NativeDescent.equivalence_left_choice`, `NativeDescent.equivalence_right_choice`, `NativeDescent.equivalence_left_map_value`, `NativeDescent.equivalence_right_map_value`, `NativeDescent.is_groupoid`, `NativeDescent.equivalence_seam_label`。

5登録sourceに個別の`research/lean/check_research_modules.sh --focused ResearchLean/AG/RelativeRepairComposition/<file>.lean`を実行し、全exit0。正確な全5source本体からimport行だけを除いた単一のCycle7Auditで全135明示宣言と生成された先行`RelativeCover.r0.congr_simp`、計136宣言を個別`#print axioms`し、標準公理のみを確認。監査log SHA256 `3c577ac430971c990a153ffa9e28f4dd7197aec309f5f215867f4ce918b09630`。必要なsingle targeted dependency checkはrootのみで実施。Research全体/aggregate/全file loop、subagent lake buildは実行しない。比較自然同型とseam値APIの局所elaborationには最大1,000,000 heartbeatsの有限上限を用い、statementとkernel条件を変更しない。

placeholder/hidden-BiDi/privacy/import方向とdiff checkを確認。PR正式査読と同一head CIは、この実装結果の独立判定として後続する。有限被覆・Ω/connecting・C–F・W1–W5の未達を維持し、今回を全GOAL完了候補としない。

## Cycle 8：有限閉被覆の全cocycleとnative実修復の復元比較

```yaml
ledger_type: target_cycle_result
goal: G-130-aat-relative-repair-composition
cycle: 8
goal_blob_sha: 8da0fb4eb75d1cb5c37a9d4ddf5e03c18c0bb8a2
base_oid: d7d56e80eded4095000ce7f15320ead051338e3a
tracking_issue: 5132
report_path: research/reports/G-130-aat-relative-repair-composition.md
selection:
  proof_state_ref: "Cycle7の二領域全native実修復同値とCycle6の元セル族・全微分"
  proof_dag_predecessors: [RelativeCover.r0, RelativeCover.r1, RelativeCover.r_d0, RelativeCover.r_d1, NativeDescent.restrictionFunctor, NativeDescent.restriction_obj_choice, NativeDescent.restriction_map_value, ActualEquation.originalRepairEquationEquivalence, ActualEquation.nativeRepairEquationEquivalence]
  milestone: "Bの有限閉被覆について、三重交差の全再同定cocycleを保持する全native descent groupoidから元Kの独立実修復を復元し、細分化・組立て比較を同じ大域復元と整合させる"
  proof_obligations: ["元0–3-cellの領域族被覆と相対原値族の全貼り合わせ", "全局所解・全overlap labels・三重cocycleと全compatible局所射のnative groupoid", "頂点別の所属領域と全seamから生成する厳密化と全大域修復復元", "全射復元とfaithful・全inverse/unit/counit", "同じ実辺・全再同定・全seamのnative局所実修復との対応", "包含制限の合成/恒等比較と全typed三重cocycle", "原値細分化関手と大域復元比較", "閉合併による組立て/並べ替え比較と同じ大域復元"]
  exit_criteria: ["任意有限被覆・全descent対象/全compatible射を量化", "実修復は元Kとnative局所の独立定義", "全choice/vertex labels/overlap arrowsと三重cocycleを保持", "結論のgluing/effectivity/同値certificateを入力にしない", "refinement/assemblyの全native比較を大域復元へ接続", "focused・全宣言個別公理・scanとPR監査"]
  selection_reason: "二領域の全実修復descentを有限被覆の三重再同定と組立てへ接続し、Bの復元・比較の未放電義務を消す"
  expected_result_type: proof-obligation-discharged
  lean_targets: [ResearchLean/AG/RelativeRepairComposition/IndexedFamilies.lean, ResearchLean/AG/RelativeRepairComposition/IndexedClosedCovers.lean, ResearchLean/AG/RelativeRepairComposition/IndexedEquationDescent.lean, ResearchLean/AG/RelativeRepairComposition/NativeRestrictionCoherence.lean, ResearchLean/AG/RelativeRepairComposition/IndexedNativeDescent.lean, ResearchLean/AG/RelativeRepairComposition/DescentRefinement.lean]
  risks: ["cocycleをpi0に落とさない", "同じ元Kと全kernelを保持", "全gauge actionのinstanceとeffectivityを入力から生成", "三重交差の型/比較/全文脈を省かない", "degreewise延長をchain mapと扱わない", "general BのchoiceをCの有限計算sectionへ転用しない", "refinement/assemblyを裸の同型存在へ縮小しない"]
  unchecked: ["実装・検証・独立PR監査前"]
```

相対原値族と頂点別厳密化は一般の領域族で構成し、有限被覆をその同じ対象・射に適用する。Cの有限生成アルゴリズムや停止を今回の非計算的構成から推論しない。指定局所案H1条件とΩ/connecting/kernel比較、C–F、W1–W5は別の未完義務として保持する。

```yaml
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "全元0–3-cell被覆、全局所実修復と全overlap gauge/triple cocycleから元Kへのeffectivityを生成。全compatible射、制限の合成/恒等、refinement/assembly/reorder/bracketの全native比較を同じ元K復元へ接続"
  exit_criteria_status: ["全有限被覆を含む一般index族: IndexedCoverとdegree0–3 familyEquiv", "独立実修復・全seam射: IndexedNative.Datum/overlapArrow", "全対象復元: strictification_difference/restore_equation/restoreActual/canonicalRestorationIso", "全射・inverse/unit/counit: diagonal_full/faithful/essSurjとnative Equivalence", "制限合成/恒等と全typed重なり: restrictionComposition/Identityとtriple_gauge_cocycle", "全refinement/assembly/order/bracketと元K復元: 各restoration*Comparison", "6登録source focused、165明示宣言を含む212宣言の個別公理監査"]
  split_reason: none
  completion_candidate: no
  lean_artifacts: [IndexedFamilies.lean, IndexedClosedCovers.lean, IndexedEquationDescent.lean, NativeRestrictionCoherence.lean, IndexedNativeDescent.lean, DescentRefinement.lean]
  evidence: [IndexedEquation.strictification_difference, IndexedEquation.restore_equation, IndexedEquation.diagonal_full, IndexedEquation.diagonal_faithful, IndexedEquation.diagonal_essSurj, IndexedNative.actual_coordinates, IndexedNative.coordinates_actual, IndexedNative.arrowOfLabels, IndexedNative.equivalence, IndexedNative.global_choice, IndexedNative.global_map_value, IndexedNative.canonicalRestorationIso, IndexedNative.triple_gauge_cocycle, IndexedNative.restorationRefinementComparison, IndexedNative.restorationAssemblyComparison, IndexedNative.restorationReorderComparison, IndexedNative.restorationAssemblyBracketComparison]
  claim_mapping:
    theorem_names: [IndexedNative.equivalence, IndexedNative.canonicalRestorationIso, IndexedNative.restorationRefinementComparison, IndexedNative.restorationAssemblyComparison, IndexedNative.restorationReorderComparison, IndexedNative.restorationAssemblyBracketComparison]
    source_labels: ["固定GOAL B: 有限閉被覆のcocycleと全native復元・細分化・組立て比較", "n1017 §2.3(E)"]
    conjuncts: ["同じ元Kの全独立実修復", "全局所実修復と全overlap arrows", "全元vertexの三重cocycle", "全compatible局所gauge射", "全元edge choices/vertex labels/seamの保存", "native inverse/unit/counitと生成済canonical restoration", "全refinement/assembly/order/bracketから同じ元K復元への自然同型"]
    undischarged_assumptions: []
    acceptance_point: "今回の有限被覆descent到達点の全exit criteriaを構成。独立受理判定は固定headのPR監査へ渡す"
    port_status: unported (Research-proved)
audits:
  premise_delta:
    discharged: ["全次数の元セル復元: Family.indexedEquiv", "三重cocycleからseam厳密化: strictification_difference", "大域face方程式: 全face被覆とr_d1/局所解条件", "全射復元/faithful: 全元vertex/edge被覆", "全実修復/全native labels: actual_coordinates/coordinates_actualとlabelEquiv", "実辺制限合成: 全choice値からrestriction_comp_obj", "full refinement/effectivity: common global diagonal comparison", "assembly/order/bracket: 元cell inclusionと全cover保存"]
    remaining: ["指定局所案H1条件・Ω/connecting/kernel比較", "C–F、W1–W5"]
  certificate_provenance:
    discharged: ["IndexedCoverは元集合の被覆だけ", "全indexed action: 局所gauge equationと全seam/cocycleから生成", "native action: 独立実修復/実seam datumの全往復と全label同型から生成", "effectivity: 頂点別seam厳密化と元edge/faceの全gluing", "全逆関手/比較: 生成済full/faithful/essSurjとnative Equivalence", "同じ大域復元比較: raw refinementと両global diagonalの全自然同型から生成"]
    unresolved: []
  proof_use:
    used: ["hfixedは実δのP零", "各閉領域の元incidenceはd0/d1 restriction交換", "全vertex被覆は全seam厳密化とgauge injectivity", "全edge被覆は大域edge gluingと全射条件", "全face被覆は大域affine equation", "全triple被覆はdegree3全原値族同型", "全overlap gauge/cocycleはstrictification difference", "原始solutionCorrection/correctionChoice両逆は全physical choicesの保存"]
    unused: ["d2δ零はeffectivityには不要。後続Ω/connectingで別途使用", "非計算的coveringIndexをCの有限消去/停止/計算sectionへ転用しない"]
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  blocking_findings: []
  next_obligation: "Bの指定局所案H1条件、Ω/connecting/kernel比較"
```

### 構成と元値保存

`IndexedCover`は元Kの0–3-cellを各々含む領域があるという条件だけを持つ。元cell別の所属領域を選び、全互換局所族から元値を復元する`familyEquiv0`–`familyEquiv3`を構成した。非空index/非空修復/有限carrierは追加しない。空indexの場合も元cell被覆という同じ条件で扱う。非空indexの全領域族の被覆と、元vertexを持つ空領域族の不被覆を補助補題で提供する。共有元cellの二値が異なる局所族は`not_mem_indexedCompatible_of_ne`で不適合を証明し、零族の適合と正負を揃える。

全局所解`hᵢ`と全overlap labels`bᵢⱼ`は`hⱼ|=hᵢ|+d0 bᵢⱼ`、対角零、元vertex上の`bᵢⱼ+bⱼₖ=bᵢₖ`を満たす。元vertex別に`r(v)`を選び、`aᵢ(v)=bᵣ₍ᵥ₎,ᵢ(v)`を生成する。三重cocycleから`bᵢⱼ=aⱼ−aᵢ`、補正局所解`hᵢ−d0 aᵢ`の全共有edge値の等値を得る。全edge gluingと全face検出から、元Kの大域解を復元する。全compatible局所gauge射も、元vertex gluingと全edge検出で生成し、全射・faithful・essSurjを証明する。

`IndexedNative.Datum`は各native閉領域の独立`SupportedRepair`と全native vertex labelsを持ち、seam fieldには実際のgauge action equationを要求する。`overlapArrow`はその全実射であり、`triple_gauge_cocycle`は固定bracketの三重原値族における全文のcocycleである。制限の合成/恒等比較は元の全physical choicesから対象等式を生成し、identity labelsを持つ両方向の射と全raw labelsのnaturalityを備える。全datum/labelsの往復から生成するnative actionが各独立局所gaugeに一致すること、全compatible射を生成する`arrowOfLabels`、全seam値の条件を証明した。

大域sourceは元Kの`RepairGroupoid T P.vertices P.edges`である。全局所physical choices、全元vertex label、全zero seamsを保存し、`restoreActual`は全native datumから元Kの独立実修復を生成する。`canonicalRestorationIso`はその大域修復の全局所制限から入力datumへの具体的な全gauge isomorphismであり、各labelは同じ元vertexで生成した`aᵢ(v)`そのものである。逆方向には全inverse labelsを持つ。単なるorbit対応へ縮小しない。

raw refinementはindex mapと全0–3-cell inclusionから、全局所対象・射・seamを元値制限するfunctorとして構成した。粗細の独立vertex choiceにより復元objectは一般には等号にならないため、両方の元K復元functorの全自然同型`restorationRefinementComparison`を構成した。閉合併assembly、順序変更、nested assemblyのbracket変更も、全元cell inclusion・cover保存を証明して同じnative比較へ接続した。

### Material premise と一次生成経路

| premise・条件 | 分類 | 使用・放電 |
| --- | --- | --- |
| 元`OriginalTowerPresentation`の実塔、全核、strong edge lifts、comparators | 許された数学入力 | 先行元/native座標同型のcurrent statementと同じargsを使用 |
| 固定閉Pと全閉領域族 | 幾何入力 | 元incidence、P零、restrictionとd0/d1交換 |
| P上の実lift面整合 | 固定条件 | 同じ実δの相対所属を生成 |
| 全元0–3-cell被覆 | 集合被覆 | 各次数の全原値gluing、全射の元値検出 |
| 全local actual repairs/seams/cocycle | descent入力 | 独立実修復と全実再同定を保持しstrictificationを生成 |
| full/faithful/essSurj/effectivity | 結論 | 元cell gluingと局所equation/cocycleから証明 |
| 全native gauge action | 構成 | 独立actual datum往復、全label同型から生成し全局所gaugeと全seam値に照合 |
| 全refinement/assembly比較 | 結論 | raw原値functorと両global diagonalsから生成 |
| 非計算的coveringIndex | general Bの構成 | Cの有限計算・停止・sectionではない |

### 全宣言と検証

`IndexedFamilies.lean` (17明示宣言):

`Family.indexedCompatible`, `Family.mem_indexedCompatible`, `Family.not_mem_indexedCompatible_of_ne`, `Family.indexedRestriction`, `Family.indexed_restriction_val`, `Family.coveringIndex`, `Family.covering_index_mem`, `Family.indexedGlue`, `Family.indexed_glue_on`, `Family.indexed_glue_restriction`, `Family.indexed_restriction_glue`, `Family.indexed_restriction_injective`, `Family.indexedEquiv`, `Family.indexedRefinement`, `Family.indexed_refinement_val`, `Family.indexed_refinement_restriction`, `Family.indexed_glue_refinement`。

`IndexedClosedCovers.lean` (37明示宣言):

`ClosedRegion.IndexedCover`, `ClosedRegion.indexed_cover_all`, `ClosedRegion.not_indexed_cover_empty`, `ClosedRegion.indexedUnion`, `ClosedRegion.to_indexed_union`, `ClosedRegion.triple`, `ClosedRegion.triple_first_pair`, `ClosedRegion.triple_second_pair`, `ClosedRegion.triple_outer_pair`, `IndexedCover.Compatible0`, `IndexedCover.restriction0`, `IndexedCover.glue0`, `IndexedCover.familyEquiv0`, `IndexedCover.restriction0_injective`, `IndexedCover.glue0_value`, `IndexedCover.restrict_glue0`, `IndexedCover.Compatible1`, `IndexedCover.restriction1`, `IndexedCover.glue1`, `IndexedCover.familyEquiv1`, `IndexedCover.restriction1_injective`, `IndexedCover.glue1_value`, `IndexedCover.restrict_glue1`, `IndexedCover.Compatible2`, `IndexedCover.restriction2`, `IndexedCover.glue2`, `IndexedCover.familyEquiv2`, `IndexedCover.restriction2_injective`, `IndexedCover.glue2_value`, `IndexedCover.restrict_glue2`, `IndexedCover.Compatible3`, `IndexedCover.restriction3`, `IndexedCover.glue3`, `IndexedCover.familyEquiv3`, `IndexedCover.restriction3_injective`, `IndexedCover.glue3_value`, `IndexedCover.restrict_glue3`。

`IndexedEquationDescent.lean` (26明示宣言):

`IndexedEquation.Datum`, `IndexedEquation.Labels`, `IndexedEquation.gauge`, `IndexedEquation.gauge_zero`, `IndexedEquation.gauge_add`, `IndexedEquation.addAction`, `IndexedEquation.Groupoid`, `IndexedEquation.diagonalDatum`, `IndexedEquation.diagonalLabels`, `IndexedEquation.diagonal_gauge`, `IndexedEquation.diagonalFunctor`, `IndexedEquation.strictificationLabels`, `IndexedEquation.strictification_difference`, `IndexedEquation.strictification_seam_zero`, `IndexedEquation.strictCompatible`, `IndexedEquation.restoreEdges`, `IndexedEquation.restore_restriction`, `IndexedEquation.restore_equation`, `IndexedEquation.restoreSolution`, `IndexedEquation.diagonal_restore`, `IndexedEquation.gauge_diagonal_restore`, `IndexedEquation.diagonal_faithful`, `IndexedEquation.diagonal_full`, `IndexedEquation.diagonal_essSurj`, `IndexedEquation.diagonal_is_equivalence`, `IndexedEquation.equivalence`。

`NativeRestrictionCoherence.lean` (14明示宣言):

`actionLabelIso`, `action_label_iso_label`, `action_label_iso_inverse_label`, `identityLabelIso`, `identityLabelComparison`, `identity_comparison_label`, `NativeDescent.restriction_comp_obj`, `NativeDescent.restriction_comp_map`, `NativeDescent.restriction_id_obj`, `NativeDescent.restriction_id_map`, `NativeDescent.restrictionComposition`, `NativeDescent.restrictionIdentity`, `NativeDescent.restriction_composition_label`, `NativeDescent.restriction_identity_label`。

`IndexedNativeDescent.lean` (37明示宣言):

`IndexedNative.LocalRepair`, `IndexedNative.LocalLabels`, `IndexedNative.labelValue`, `IndexedNative.label_value_native`, `IndexedNative.restrictRepair`, `IndexedNative.restriction_coordinates`, `IndexedNative.Datum`, `IndexedNative.coordinates`, `IndexedNative.actual`, `IndexedNative.actual_coordinates`, `IndexedNative.coordinates_actual`, `IndexedNative.datumEquiv`, `IndexedNative.Labels`, `IndexedNative.labelEquiv`, `IndexedNative.addAction`, `IndexedNative.Groupoid`, `IndexedNative.coordinates_gauge`, `IndexedNative.coordinateEquivalence`, `IndexedNative.equivalence`, `IndexedNative.gauge_local`, `IndexedNative.gauge_seam_value`, `IndexedNative.arrow_local`, `IndexedNative.arrow_seam_value`, `IndexedNative.arrowOfLabels`, `IndexedNative.arrow_of_labels_label`, `IndexedNative.global_choice`, `IndexedNative.global_map_value`, `IndexedNative.global_seam`, `IndexedNative.restoreActual`, `IndexedNative.restore_actual_choice`, `IndexedNative.overlapArrow`, `IndexedNative.overlap_arrow_label`, `IndexedNative.triple_gauge_cocycle`, `IndexedNative.restored_coordinates`, `IndexedNative.gauge_global_restore`, `IndexedNative.canonicalRestorationIso`, `IndexedNative.canonical_restoration_label_value`。

`DescentRefinement.lean` (34明示宣言):

`ClosedRegion.inter_inclusion`, `IndexedEquation.refineDatum`, `IndexedEquation.refineLabels`, `IndexedEquation.refine_gauge`, `IndexedEquation.refinementFunctor`, `IndexedEquation.refinement_obj_value`, `IndexedEquation.refinement_map_value`, `IndexedEquation.refinement_seam_value`, `IndexedEquation.refine_diagonal`, `IndexedEquation.diagonalRefinementComparison`, `IndexedEquation.diagonal_refinement_comparison_label`, `IndexedEquation.refinement_is_equivalence`, `IndexedEquation.refinementEquivalence`, `IndexedEquation.restorationRefinementComparison`, `ClosedRegion.assembly`, `ClosedRegion.to_assembly`, `ClosedRegion.assembly_cover`, `ClosedRegion.assembly_flatten`, `ClosedRegion.assembly_unflatten`, `ClosedRegion.reindex_cover`, `IndexedNative.refinementFunctor`, `IndexedNative.refinement_local_choice`, `IndexedNative.refinement_map_value`, `IndexedNative.refinement_seam_value`, `IndexedNative.diagonalRefinementComparison`, `IndexedNative.refinement_is_equivalence`, `IndexedNative.refinementEquivalence`, `IndexedNative.restorationRefinementComparison`, `IndexedNative.assemblyEquivalence`, `IndexedNative.restorationAssemblyComparison`, `IndexedNative.reorderEquivalence`, `IndexedNative.restorationReorderComparison`, `IndexedNative.assemblyBracketEquivalence`, `IndexedNative.restorationAssemblyBracketComparison`。

6登録sourceの個別focused checkは全exit0。正確な6source本体からimport行だけを除いた単一Cycle8Auditにより、全165明示宣言とstructure生成宣言等を含む全212宣言を個別`#print axioms`し、全件標準公理のみ。公理log SHA256 `03abf403b7bf940b16c6560246839c246f1b373f331cf5794ab442b742547be4`。rootのみ必要single targeted dependencyを確認し、Research全体/aggregate/全file loopとsubagent lake buildは実行しない。局所elaborationの有限heartbeats上限でstatement/仮定を変更しない。

placeholder/hidden-BiDi/privacy/import方向/diff checkを確認。正式PR査読と同一head CIはこの実装結果の独立判定として後続する。指定局所案H1条件、Ω/connecting/kernel、C–F、W1–W5は未達であり、全GOAL completion candidateとはしない。

## Cycle 9：局所修復の統合障害と元相対複体の接続写像

```yaml
ledger_type: target_cycle_result
goal: G-130-aat-relative-repair-composition
cycle: 9
goal_blob_sha: 8da0fb4eb75d1cb5c37a9d4ddf5e03c18c0bb8a2
base_oid: 97ec5ac9468febbdf95416f82c4dfcfbde0c1d8f
tracking_issue: 5132
report_path: research/reports/G-130-aat-relative-repair-composition.md
selection:
  proof_state_ref: "Cycle6の元相対複体のcover SES、Cycle7の元K/native二領域descent、Cycle8の有限閉被覆effectivity"
  proof_dag_predecessors: [RelativeCover.original_cover_short_exact, RelativeCover.originalComplexIso, RelativeCover.nativeComplexIso, CoverEquation.glue_solution, ActualEquation.originalRepairEquiv, ActualEquation.nativeRepairEquiv, ActualRelative.obstructionCocycle]
  milestone: "Bの指定局所案H1条件と統合障害Ωを、同じ元相対複体のnative接続写像およびH2制限kernelへ構成する"
  proof_obligations: ["全局所H1/H2とoriginal/native原値class・制限比較", "z=hV|−hU|のcocycleと全overlap gauge存在iff H1零", "両local H1 imageの和による商Ωと局所案変更非依存", "ω零iff元Kの独立実修復存在", "pair native homologyの全product比較とdifference image=両local image和", "元CPcomplexのShortExact.δに対し(-hU,-hV)から∂[z]=[δ]", "同じH2制限kernelへのΩの全AddEquivとclass値保持"]
  exit_criteria: ["同じ全核・閉固定P・全局所案を量化", "追加global修復/障害零/LES certificateなし", "native適用の実δとd2零を同じactual3cell条件から生成", "差分rU−rVとzの符号を原値で検証", "商の分母は両local H1 imageの和そのもの", "同じ元K実修復と全seam射に接続", "全同型・class値保存・focused・個別公理・scanとPR監査"]
  selection_reason: "Bの残る一般統合条件を実修復の復元と元CP複体のcohomologyへ閉じる"
  expected_result_type: proof-obligation-discharged
  lean_targets: [ResearchLean/AG/RelativeRepairComposition/CoverCohomology.lean, ResearchLean/AG/RelativeRepairComposition/CoverObstruction.lean, ResearchLean/AG/RelativeRepairComposition/CoverConnecting.lean, ResearchLean/AG/RelativeRepairComposition/CoverPairCohomology.lean, ResearchLean/AG/RelativeRepairComposition/CoverNativeCohomology.lean, ResearchLean/AG/RelativeRepairComposition/CoverCohomologyMaps.lean, ResearchLean/AG/RelativeRepairComposition/CoverObstructionKernel.lean, ResearchLean/AG/RelativeRepairComposition/CoverPlanConnecting.lean, ResearchLean/AG/RelativeRepairComposition/NativeCoverObstruction.lean]
  risks: ["zはsecond−first、SES差分はfirst−second", "片方だけのimage商にしない", "元K/全核をall-subtypeモデルに置換しない", "native LES存在だけで符号を済ませない", "d2δ零certificateを独立入力にしない", "Bの非計算構成をCのアルゴリズムへ転用しない", "範囲付きordinarydescentに適用しない"]
  unchecked: ["実装・検証・PR独立査読前"]
```

局所cohomologyは同じ全相対複体のnative homologyを用い、classを元cochain値から生成する。元Kの複体とnative部分表示の全比較を保持する。Ωの分母と接続写像を同じcover SESへ接続し、符号と実δを実修復から検証する。C–FとW1–W5は未完のまま保持する。

```yaml
ledger_type: target_cycle_result
goal: G-130-aat-relative-repair-composition
cycle: 9
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "全局所H1/H2のnative quotient比較、全原値restriction/pair difference/diagonal、全specified overlap gauge、Ωのplan非依存と元K実修復存在iff、native接続符号、Ωと元H2制限kernelの全同型"
  exit_criteria_status: ["任意の一般塔・全実核・同じ閉P・全局所案", "native original cover SESを既存元cell exactnessから生成", "同じ実3cell条件からActualRelative.obstructionCocycleを生成", "(-hU,-hV)の実liftと微分による正符号", "分母は両local H1 imageの和そのもの", "全overlap arrowsと全vertex labelsの両逆", "元Kの全独立実修復へ存在同値", "全native class/isomorphism/原値比較"]
  split_reason: none
  completion_candidate: no
  lean_artifacts: [CoverCohomology, CoverConnecting, CoverObstruction, CoverPairCohomology, CoverNativeCohomology, CoverCohomologyMaps, CoverObstructionKernel, CoverPlanConnecting, NativeCoverObstruction]
  evidence: [NativeCoverObstruction.specified_plans_glue_iff, NativeCoverObstruction.omega_independent, NativeCoverObstruction.omega_eq_zero_iff_original_repair, CoverObstructionKernel.omegaKernelEquiv, CoverObstructionKernel.restriction_original_class, NativeCoverObstruction.connecting_actual_difference, NativeCoverObstruction.omega_kernel_actual_class]
  claim_mapping:
    source_labels: ["GOAL B", "n1017 §2.3(E)", "n1017 §2.4"]
    conjuncts: ["[z]=0 iff全specified overlap gauge", "ωは全局所案に非依存", "ω=0 iff元Kの全実修復存在", "native ∂[z]=[δ]", "Ω≃ker(H2元K→H2U×H2V)"]
    undischarged_assumptions: []
    acceptance_point: "Bの統合条件を同じactual/native descentとoriginal CPcomplexへ接続"
    port_status: unported (Research-proved)
audits:
  premise_delta:
    discharged: ["全原値cycles/boundaries/native classes", "full local pair product", "両H1 imageの和", "native connecting kernel/range", "actual authored defect class", "全overlap arrowsと全labels"]
    remaining: ["C–FとW1–W5の指定要求"]
  certificate_provenance:
    discharged: ["ShortExactはRelativeCover.original_cover_short_exactから生成", "native δの原値はCoverConnecting.connecting_classから計算", "実defect cocycleは同じActualRelative.obstructionCocycleから生成"]
    unresolved: []
  proof_use:
    used: ["cover exactness→LES→両kernel/range", "hfixed→実δ相対所属", "authored3cell→実δcycle→∂actual class", "全local equations→negative plan differential", "original/native full object equivalence→元K修復存在", "full faithful inverse→全overlap label bijection"]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  blocking_findings: []
  next_obligation: "Cの有限体上の全核座標と候補/共有変数を保持する一回の局所消去"
```

### 構成と元値の対応

全cochain群は元Kの同じ全相対係数群である。`firstHomologyIso` / `secondHomologyIso` はmathlibのnative homologyと全cycle/boundary商の同型であり、middle cochainが恒等なsegment isomorphismを通す。各`native_h1_class` / `native_h2_class`は元値classをそのまま保存し、`restriction_h1` / `restriction_h2`は全classに対して同じ元値制限になる。元Kとnative部分表示の全複体同型から局所および元のH1/H2比較を得る。局所対の`componentEquiv` / `secondComponentEquiv`は両local groups全体との相互逆であり、像だけを比較対象にしない。

`CoverObstruction.differenceCycle`は`z=hV|−hU|`を同じd1のcycleとして構成する。全overlap gaugeの存在はそのH1 class零と同値である。`localImages`は両local H1 restriction rangeの和そのものであり、`Omega`はその商である。全局所案変更の差cycleから`omega_independent`を証明する。ω零から両local classの代表を取り、局所案を補正してseamを作り、既存のfull closed-cover gluingから元Kの解を復元する。逆方向は任意の大域解の同じ制限から得る。

`connecting`は元KのCPcomplexを始点とする`originalCoverShortComplex`のmathlib `ShortExact.δ`である。`native_difference_h1`は同じfirst−second差分を全原値classで検証し、そのrangeが両local image和と一致する。native LESのexactnessから接続kernelとH2制限kernelへの全rangeを得る。`omegaKernelEquiv`はこの同じΩから全kernelへのAddEquivで、両逆を持つ。`restriction_original_class`は元のH2制限が全classに対して同じU/V制限に一致することを証明する。

`negative_plan_lift`は`(-hU,-hV)`がzの実liftであること、`negative_plan_differential`はその微分が同じ元δであることを全cochainで証明する。`connecting_class`はfree cyclic groupの原値評価からnative δの値を導く。`connecting_plan_class`はこれを同じcover SESへ適用し、正符号の`∂[z]=[δ]`を得る。

`NativeCoverObstruction`の局所対象は制限された実towerの独立修復である。`overlapArrowEquiv`は同じ二局所対象間の全overlap gauge arrowsの双方向対応で、両方向の全vertex label値を保存する。`specified_plans_glue_iff`、`omega_eq_zero_iff_original_repair`は元K実修復の存在と同じ対象・射へ接続する。実defect cycleは元のauthored3cell条件を`ActualRelative.obstructionCocycle`へ適用して生成し、`connecting_actual_difference`と`omega_kernel_actual_class`が同じ元実δの正のclass値を与える。

### Material premise と使用

| premise | 分類 | 生成・使用 |
| --- | --- | --- |
| 一般original towerと全実核/生成輸送/元comparators | 本文由来 | GOAL A/Bの同じTを既存の全actual/native座標対応へ適用 |
| 同じ閉P/U/Vと全0–3-cell cover | 本文由来 | 元制限/d交換、cover SES生成、native exactness |
| P上の元基準実面整合 | 本文由来 | 同じ実δの相対所属を生成 |
| 同じ元authored3cell conditions | 本文由来 | 同じ実δのcocycle生成、native H2 classと正符号へ |
| 全local修復R/Qと全overlap arrows | 定理の量化対象 | 全対象・全labelを保つ対応、全案非依存 |
| 一般cycle c / 一般ShortExact S | 一般APIの方向仮定、実適用で放電済み | 実cはActualRelative.obstructionCocycle、実Sはoriginal_cover_short_exactが生成 |
| differential零合成・全native class比較・pair product・接続kernel/range | 放電済み | 同じ原値d/既存complex、class_naturality、native LESから構成 |
| Ωの零性・元K修復の存在・全H2 kernel同型 | 結論 | 両方向gluing、native exactness、全商AddEquiv |

### 全宣言と検証

`CoverCohomology.lean` (30明示宣言):

`CohomologyClass.classHom`, `CohomologyClass.class_quotient`, `CohomologyClass.class_eq_zero_iff`, `CohomologyClass.class_surjective`, `CoverCohomology.Z1`, `CoverCohomology.Z2`, `CoverCohomology.boundary1`, `CoverCohomology.boundary2`, `CoverCohomology.H1`, `CoverCohomology.H2`, `CoverCohomology.h1_eq_zero_iff`, `CoverCohomology.h2_eq_zero_iff`, `CoverCohomology.firstShortComplex`, `CoverCohomology.secondShortComplex`, `CoverCohomology.first_eq_sc`, `CoverCohomology.second_eq_sc`, `CoverCohomology.firstNormalizedIso`, `CoverCohomology.firstShortIso`, `CoverCohomology.firstHomologyIso`, `CoverCohomology.secondNormalizedIso`, `CoverCohomology.secondShortIso`, `CoverCohomology.secondHomologyIso`, `CoverCohomology.restrictZ1`, `CoverCohomology.restrict_boundary1`, `CoverCohomology.restrictH1`, `CoverCohomology.restrict_h1_mk`, `CoverCohomology.restrictZ2`, `CoverCohomology.restrict_boundary2`, `CoverCohomology.restrictH2`, `CoverCohomology.restrict_h2_mk`。

`CoverConnecting.lean` (12明示宣言):

`CohomologyClass.point`, `CohomologyClass.point_one`, `CohomologyClass.point_comp`, `CohomologyClass.point_zero`, `CohomologyClass.point_cycle`, `CohomologyClass.lift_point_value`, `CohomologyClass.class_point_value`, `CohomologyClass.cycleMap`, `CohomologyClass.cycles_map_value`, `CohomologyClass.class_naturality`, `CohomologyClass.complex_class_point`, `CoverConnecting.connecting_class`。

`CoverObstruction.lean` (12明示宣言):

`CoverObstruction.differenceCycle`, `CoverObstruction.difference_cycle_value`, `CoverObstruction.seam_exists_iff`, `CoverObstruction.localImages`, `CoverObstruction.Omega`, `CoverObstruction.omega`, `CoverObstruction.shiftSolution`, `CoverObstruction.planChange`, `CoverObstruction.shift_plan_change`, `CoverObstruction.difference_cycle_change`, `CoverObstruction.omega_independent`, `CoverObstruction.omega_eq_zero_iff_global`。

`CoverPairCohomology.lean` (38明示宣言):

`CoverPairCohomology.Z1`, `CoverPairCohomology.boundary1`, `CoverPairCohomology.H1`, `CoverPairCohomology.cycleLeft`, `CoverPairCohomology.cycleRight`, `CoverPairCohomology.cycleClasses`, `CoverPairCohomology.cycle_classes_boundary`, `CoverPairCohomology.componentH1`, `CoverPairCohomology.component_h1_mk`, `CoverPairCohomology.component_h1_surjective`, `CoverPairCohomology.component_h1_kernel`, `CoverPairCohomology.component_h1_injective`, `CoverPairCohomology.componentEquiv`, `CoverPairCohomology.firstShortComplex`, `CoverPairCohomology.first_eq_sc`, `CoverPairCohomology.firstNormalizedIso`, `CoverPairCohomology.firstShortIso`, `CoverPairCohomology.firstHomologyIso`, `CoverPairCohomology.nativeFirstProductIso`, `CoverPairCohomology.Z2`, `CoverPairCohomology.boundary2`, `CoverPairCohomology.H2`, `CoverPairCohomology.cycleLeft2`, `CoverPairCohomology.cycleRight2`, `CoverPairCohomology.cycleClasses2`, `CoverPairCohomology.cycle_classes_boundary2`, `CoverPairCohomology.componentH2`, `CoverPairCohomology.component_h2_mk`, `CoverPairCohomology.component_h2_surjective`, `CoverPairCohomology.component_h2_kernel`, `CoverPairCohomology.component_h2_injective`, `CoverPairCohomology.secondComponentEquiv`, `CoverPairCohomology.secondShortComplex`, `CoverPairCohomology.second_eq_sc`, `CoverPairCohomology.secondNormalizedIso`, `CoverPairCohomology.secondShortIso`, `CoverPairCohomology.secondHomologyIso`, `CoverPairCohomology.nativeSecondProductIso`。

`CoverNativeCohomology.lean` (22明示宣言):

`CoverCohomology.nativeCycle1`, `CoverCohomology.native_cycle1_value`, `CoverCohomology.native_h1_class`, `CoverCohomology.nativeCycle2`, `CoverCohomology.native_cycle2_value`, `CoverCohomology.native_h2_class`, `CoverCohomology.nativeFirstIso`, `CoverCohomology.nativeSecondIso`, `CoverCohomology.originalFirstIso`, `CoverCohomology.originalSecondIso`, `CoverPairCohomology.nativeCycle1`, `CoverPairCohomology.native_h1_class`, `CoverPairCohomology.nativeCycle2`, `CoverPairCohomology.native_h2_class`, `OriginalCohomology.secondNormalizedIso`, `OriginalCohomology.secondShortIso`, `OriginalCohomology.secondHomologyIso`, `OriginalCohomology.nativeCycle2`, `OriginalCohomology.native_h2_class`, `OriginalCohomology.familyCycle2`, `OriginalCohomology.familySecondIso`, `OriginalCohomology.family_h2_class`。

`CoverCohomologyMaps.lean` (13明示宣言):

`CoverCohomology.restrictionComponent`, `CoverCohomology.restriction_component_comm`, `CoverCohomology.restrictionMap`, `CoverCohomology.native_h1_inverse_class`, `CoverCohomology.native_h2_inverse_class`, `CoverCohomology.restriction_h1_class`, `CoverCohomology.restriction_h2_class`, `CoverCohomology.restriction_h1`, `CoverCohomology.restriction_h2`, `CoverCohomologyMaps.differenceH1`, `CoverCohomologyMaps.native_difference_h1`, `CoverCohomologyMaps.diagonalH2`, `CoverCohomologyMaps.native_diagonal_h2`。

`CoverObstructionKernel.lean` (10明示宣言):

`CoverObstructionKernel.difference_range`, `CoverObstructionKernel.connecting`, `CoverObstructionKernel.restriction`, `CoverObstructionKernel.connecting_difference`, `CoverObstructionKernel.connecting_kernel`, `CoverObstructionKernel.restriction_connecting`, `CoverObstructionKernel.connecting_range`, `CoverObstructionKernel.omegaKernelEquiv`, `CoverObstructionKernel.omega_kernel_value`, `CoverObstructionKernel.restriction_original_class`。

`CoverPlanConnecting.lean` (4明示宣言):

`CoverPlanConnecting.defectFamily`, `CoverPlanConnecting.negative_plan_lift`, `CoverPlanConnecting.negative_plan_differential`, `CoverPlanConnecting.connecting_plan_class`。

`NativeCoverObstruction.lean` (13明示宣言):

`NativeCoverObstruction.localCoordinate`, `NativeCoverObstruction.differenceCycle`, `NativeCoverObstruction.differenceClass`, `NativeCoverObstruction.omega`, `NativeCoverObstruction.overlapArrowEquiv`, `NativeCoverObstruction.overlap_arrow_inverse_value`, `NativeCoverObstruction.overlap_arrow_value`, `NativeCoverObstruction.specified_plans_glue_iff`, `NativeCoverObstruction.omega_independent`, `NativeCoverObstruction.omega_eq_zero_iff_original_repair`, `NativeCoverObstruction.authored_defect_family`, `NativeCoverObstruction.connecting_actual_difference`, `NativeCoverObstruction.omega_kernel_actual_class`。

全154明示宣言と生成APIを含む全155宣言の個別公理監査、対象sourceのfocused検査、placeholder/hidden-BiDi/privacy/import方向/diff checkを用いる。Research全体/aggregate/全file loopおよびsubagent lake buildは実行しない。最終PR headの正式査読とCIは独立の受理証拠とする。C–FとW1–W5は未達であり、全GOAL completion candidateとはしない。

9登録sourceのfocused elaborationと必要な単一module依存確認はexit0。正確な全9source本体のimport行だけを除いた単一auditで全155宣言を個別`#print axioms`し、標準公理のみ。公理log SHA256 `30c96f33c1b7613006effbe3c875c0cce21330e908cb26af6609286625f7d42d`。


## Cycle 10：実相対微分からの一回の有限局所生成

```yaml
ledger_type: target_cycle_result
goal: G-130-aat-relative-repair-composition
cycle: 10
goal_blob_sha: 8da0fb4eb75d1cb5c37a9d4ddf5e03c18c0bb8a2
base_oid: 84515a192f065b8a3f68a9f9a4b75a7b4707ab80
tracking_issue: 5132
report_path: research/reports/G-130-aat-relative-repair-composition.md
selection:
  proof_state_ref: "受理済A/Bの元相対cochain・実修復/全label対応、GOAL C・n1017 §3.1・design §4"
  proof_dag_predecessors: [RelativeComplex, RelativeCover.original1, RelativeCover.original2, ActualEquation.nativeRepairEquiv, ActualEquation.nativeGaugeEquiv]
  milestone: "Cの有限入力から、共有辺と全候補を保持する局所公開関係・全内部自由度・線形section・全label作用・元実修復への両逆を一回生成する"
  proof_obligations: ["実全核の有限体基底と元cellを保存する全座標化", "非共有常時許容辺だけをX、全共有/候補をZとする分解", "同じ実d1/d0/defectからD,F,r,a,cとDa+Fc=0を生成", "有限初等行列の行/列消去から商・像基底・線形sectionを生成", "有限計算の停止・正確性とrhs/S非依存", "R×kerDと全局所解の相互逆coord/rec", "元0-cochain全labelを保持する作用と相互逆native関手", "共有原値制限はZのみで決まる", "非空公開関係の高々dimZ独立方程式"]
  exit_criteria: ["有限体/有限添字/全核基底/実輸送座標だけが入力", "求める修復・section・商/像/核の正確性certificateを入力しない", "実際の有限計算出力から線形sectionと全両逆を生成", "全rhs・全candidate名/値・全内部自由度・全gauge labels", "元の独立actual repairsと同じdifferentialsへ接続", "全宣言focused/公理/scanと独立PR監査"]
  selection_reason: "Bの非計算descentからCの入力生成手続きと全修復局所座標へ進む"
  expected_result_type: proof-obligation-discharged
  lean_targets: [FiniteElimination, LinearInterface, FiniteNativeCoordinates, NativeLocalInterface]
  risks: ["有限解列挙や非計算sectionで生成済み表現を代替しない", "初等行/列操作の有限探索はDだけを消去しrhs/Sを使わない", "共有/候補を消去しない", "basis入力は実全核全体の同型", "orbit/pi0で全射を代替しない", "全S大域strictglue/比較は後続到達点で未達を保持"]
  unchecked: ["実装・検証・PR査読前"]
```

実装経路：有限状態の飽和探索で初等行列積とその逆を生成し、正方拡張した実Dを対角化する行/列操作を探索する。Mathlibの全行列対角化定理からその探索の成功を証明する。出力を元の長方形Dへ戻し、像・核・商・線形sectionを計算する。これは局所修復やrhsの先行探索ではなく、同じDの一回の有限消去である。各局所関係・作用・復元はn1017の式(C)/(A)に従う。全S strict大域glueと表示変更、D–F、W1–W5はこのselectionの完了に含めず、固定GOALの後続要求として保持する。終了条件は実装の難しさに合わせて縮めない。

### 同じ原始入力からの局所生成

`FiniteFamily.Bases`は各元vertexの**実全核全体**と有限座標空間との線形同型であり、選択した部分核ではない。`Index0`–`Index3`、`coordinate0`–`coordinate3`、`enum0`–`enum3`は元のcell名とそのtargetの全基底を保つ。元輸送の線形性から全typed pathの線形性、元のd0/d1の線形性を証明し、閉領域上で計算する同じ微分と受理済相対微分との原値等号を与える。

`privateAlwaysEdges`は領域内・P外・候補外・他領域との非共有という四条件で計算する。`edgeSplit`はこの集合と完全な補集合との両逆である。候補と共有辺は全て補集合に残り、parallelな元辺も別の添字を保つ。`D`/`F`は同じ元d1のprivate/public columns、`a`/`c`は同じ元d0の両成分、`rhs`は同じ元実defectの負の制限である。`D_a_add_F_c`は元零合成から生成する。

`FiniteElimination.saturate`は実List上の有限飽和で、補集合のcardinalityを停止量にする。初等行列と逆を同時に生成し、全出力の両逆条件を証明する。`diagonal_exists`は全行列のMathlib対角化定理の全transvection wordを同じ生成Listへ埋め、`diagonalize`の有限探索成功を放電する。`reduce`のrow/column/inverse/pivotと全正確性fieldはその探索結果から生成される。rhs・candidate subset・修復は探索入力にない。

`generatedElimination`は同じ元private matrixの正方拡張を一回消去したデータである。`generatedSection`と`generatedPrivateImageCoordinates`/`generatedPrivateImageBasisValue`はこの同じデータを読む。正方拡張の像は元長方形行列の全像と両逆で同一視する。像基底の原値は計算可能で、native Basis packagingの値・独立性・全像のspanを証明する。sectionの全像上の右逆条件は同じ行列から生成され、一般APIのsection lawを実適用で放電する。

完全cokerは元`range D`によるnative module quotientである。実行可能な`projection=id-Dσ`の等号とnative class等号の同値、projection像と全native cokerとのLinearEquivを示す。`kernelProjection=id-σD`の像は元`ker D`全体と等しい。したがって商・核を選択済み部分像や零空間へ縮小していない。

公開関係は`qFz=qr`と同じ`projection(Fz)=projection(r)`である。`rec`/`coord`はn1017式の全R×kerDと独立な元方程式を相互に復元する。元全zero-cochain labelから`gamma=a-σDa`を生成し、`(z,k)↦(z+cb,k+gamma b)`が同じ元微分と交換することを示す。labelの効果が同じでも異なる射を残す。

`NativeRepairInterface.repairEquiv`と`equivalence`は同じoriginal Tの制限に対する独立なactual repair全体を始域とする。元実defectはTから生成し、全対象の両合成、全頂点label値、全元辺のactual morphismの復元を証明する。`native_functor_inverse`/`native_inverse_functor`は全射を含む両関手合成そのものが恒等関手である等号である。`public_value`は各非private元辺の全基底座標を保つ。

`FiniteCoverInterfaces.localEquivalence`は上のactual correspondenceを正確な`privateAlwaysEdges`へ適用する。共有部分上の原値制限はpublic zだけで決まり、全private vector、したがって全内部kernel自由度に依存しない。`candidate_retained`と`shared_restriction_public_only`は同じ元cover/候補集合でこの条件を放電する。

公開条件の圧縮では全`projection∘F`像の計算されたpivot座標を使う。`publicRow`はその座標functionalを元zへ合成した計算可能なrowである。元zから全像座標への全射性からrowsの線形独立性を示し、全像のfinrank boundから本数≤dimZを得る。非空公開関係の各z0に対し同じrowsのaffine右辺を更新するだけで元公開関係と同値になる。z0はこの**条件付き表示定理の量化対象**であり、局所generatorや修復存在判定への先行修復入力ではない。

### Material premise と生成経路

| premise/data | 分類 | 生成・使用 |
| --- | --- | --- |
| 一般original tower、全実核、元辺/core/comparatorと生成輸送 | 本文由来 | 同じTからactual/native coefficient/repair/gauge対応を使用 |
| 同一有限体、有限cell添字の列挙、実全核の有限基底、輸送線形性 | Cの本文由来の有限入力 | 全0–3-cell座標、元d0/d1行列、初等操作の有限計算 |
| 閉P/各領域とP上の実face coherence | 本文由来 | 同じ実defectの相対所属、同じ元微分との交換 |
| 同じ全候補集合と元領域family | 本文由来 | private判定、候補保持、共有原値制限 |
| 一般APIのsection law | 実適用で放電済み | generatedElimination/sectionMatrix_regular/同じDmatrix_correct |
| reduction validity/対角化成功・商/像/核の正確性・零合成 | 放電済み | 有限飽和の停止/全word所属、Mathlib全行列対角化、same-row逆条件、元d1d0=0 |
| full image Basis packaging / quotient LinearEquiv | 出力の構造化 | 計算済みimage coordinate/原値vectorsと全両逆から生成。計算出力を外部choiceで選ばない |
| arbitrary local repair、interface value、full gauge label | 定理の量化対象 | 全対象/全内部自由度/全labelの両逆・原値保存 |
| nonempty relationのz0 | 表示定理の条件付き量化対象 | 同じ独立rowsのaffine右辺。generator/existenceへの入力にしない |

```yaml
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "Cの有限全核/元cell座標から一回のprivate消去、完全商/像/核/section、全局所actual repair/labelのstrict両逆、共有public制限、独立公開方程式boundを構成"
  exit_criteria_status: ["有限入力だけから生成", "修復/section/正確性certificateの外部入力なし", "全rhsと全元public名前/値/内部自由度/label", "同じoriginal towerのactual repairsと元微分へ接続", "focused/公理/scansおよびPR独立監査で受理する"]
  split_reason: none
  completion_candidate: no
  lean_artifacts: [FiniteElimination.reduce, FiniteNative.generatedElimination, FiniteNative.generatedSection_regular, NativeRepairInterface.equivalence, NativeRepairInterface.native_functor_inverse, NativeRepairInterface.native_inverse_functor, FiniteCoverInterfaces.shared_restriction_public_only, FiniteNative.generated_public_row_count, FiniteNative.generated_public_affine_relation]
  claim_mapping:
    source_labels: ["GOAL Cの局所有限生成/作用/両逆/制限/方程式bound", "n1017 §3.1", "design §4"]
    undischarged_assumptions: []
    acceptance_point: "選定した全局所到達点のみ。全S strict大域glue・表示比較は後続要求"
    port_status: not-applicable
  next_obligation: "全Sの候補零条件と共有辺/頂点のstrict合成、全大域actual修復/全射の両逆、各表示比較。D–F/W1–W5と別全GOAL completion reviewも未達"
```

### 全宣言の監査対象

`FiniteSaturation.lean` (8明示宣言):

`FiniteElimination.expand`, `FiniteElimination.mem_expand`, `FiniteElimination.subset_expand`, `FiniteElimination.saturate`, `FiniteElimination.subset_saturate`, `FiniteElimination.saturate_closed`, `FiniteElimination.saturate_invariant`, `FiniteElimination.foldr_mem_saturate`。

`FiniteElimination.lean` (28明示宣言):

`FiniteElimination.Enumeration`, `FiniteElimination.Operation`, `FiniteElimination.compose`, `FiniteElimination.identity`, `FiniteElimination.elementary`, `FiniteElimination.generators`, `FiniteElimination.transvection_mem`, `FiniteElimination.Valid`, `FiniteElimination.valid_identity`, `FiniteElimination.valid_elementary`, `FiniteElimination.valid_compose`, `FiniteElimination.operations`, `FiniteElimination.operations_valid`, `FiniteElimination.foldr_matrix`, `FiniteElimination.word_mem_operations`, `FiniteElimination.diagonal_exists`, `FiniteElimination.diagonalize`, `FiniteElimination.Reduction`, `FiniteElimination.reduce`, `FiniteElimination.diagonal_regular`, `FiniteElimination.sectionMatrix`, `FiniteElimination.sectionMatrix_regular`, `FiniteElimination.mem_valid`, `FiniteElimination.not_valid_zero`, `FiniteElimination.sumEnumeration`, `FiniteElimination.squareExtension`, `FiniteElimination.rectangularSection`, `FiniteElimination.rectangularSection_regular`。

`LinearInterface.lean` (23明示宣言):

`LinearInterface.projection`, `LinearInterface.projection_D`, `LinearInterface.projection_eq_zero_iff`, `LinearInterface.q`, `LinearInterface.q_eq_iff_projection_eq`, `LinearInterface.kernelProjection`, `LinearInterface.kernel_projection_mem`, `LinearInterface.kernel_projection_fixed`, `LinearInterface.kernel_projection_range`, `LinearInterface.Relation`, `LinearInterface.mem_relation_projection`, `LinearInterface.mem_relation`, `LinearInterface.Solution`, `LinearInterface.Coordinates`, `LinearInterface.section_residual`, `LinearInterface.rec`, `LinearInterface.coord`, `LinearInterface.rec_coord`, `LinearInterface.coord_rec`, `LinearInterface.coordinateEquiv`, `LinearInterface.solution_nonempty_iff`, `LinearInterface.relation_zero_nonempty`, `LinearInterface.relation_empty`。

`InterfaceQuotient.lean` (5明示宣言):

`LinearInterface.quotientProjection`, `LinearInterface.quotient_projection_mk`, `LinearInterface.quotient_projection_injective`, `LinearInterface.quotient_projection_surjective`, `LinearInterface.quotientEquivalence`。

`LinearInterfaceAction.lean` (16明示宣言):

`LinearInterface.gamma`, `LinearInterface.projection_c`, `LinearInterface.Objects`, `LinearInterface.gauge`, `LinearInterface.interfaceAddAction`, `LinearInterface.rec_gauge`, `LinearInterface.Groupoid`, `LinearInterface.differential`, `LinearInterface.coboundary`, `LinearInterface.differential_coboundary`, `LinearInterface.EquationObjects`, `LinearInterface.equationCoordinateEquiv`, `LinearInterface.equation_coordinate_equivariant`, `LinearInterface.equationEquivalence`, `LinearInterface.equation_functor_label`, `LinearInterface.equation_inverse_label`。

`FiniteMatrixInterface.lean` (2明示宣言):

`FiniteMatrixInterface.linearSection`, `FiniteMatrixInterface.section_regular`。

`FiniteFamilyCoordinates.lean` (12明示宣言):

`FiniteFamily.Bases`, `FiniteFamily.Bases.comap`, `FiniteFamily.Index`, `FiniteFamily.relativeSMul`, `FiniteFamily.relativeModule`, `FiniteFamily.coordinate`, `FiniteFamily.restore`, `FiniteFamily.restore_coordinate`, `FiniteFamily.coordinate_restore`, `FiniteFamily.equivalence`, `FiniteFamily.coordinate_value`, `FiniteFamily.restore_value`。

`FiniteCoefficientDifferentials.lean` (19明示宣言):

`FiniteFamily.extend`, `FiniteFamily.restrict_extend`, `FiniteCoefficients.edgeModules`, `FiniteCoefficients.faceModules`, `FiniteCoefficients.pathTransport_smul`, `FiniteCoefficients.pathCorrection_smul`, `FiniteCoefficients.d0_smul`, `FiniteCoefficients.d1_smul`, `FiniteCoefficients.relative0Module`, `FiniteCoefficients.relative1Module`, `FiniteCoefficients.relative2Module`, `FiniteCoefficients.relative3Module`, `FiniteCoefficients.restrict_extend0`, `FiniteCoefficients.restrict_extend1`, `FiniteCoefficients.differential0`, `FiniteCoefficients.differential1`, `FiniteCoefficients.differential0_eq`, `FiniteCoefficients.differential1_eq`, `FiniteCoefficients.differential1_differential0`。

`FiniteCoordinatePartition.lean` (18明示宣言):

`FinitePartition.split`, `FinitePartition.join`, `FinitePartition.join_split`, `FinitePartition.split_join`, `FinitePartition.equivalence`, `FinitePartition.join_public`, `ClosedRegion.sharedEdges`, `ClosedRegion.privateAlwaysEdges`, `ClosedRegion.sharedEdgesDecidable`, `ClosedRegion.privateAlwaysEdgesDecidable`, `ClosedRegion.mem_sharedEdges`, `ClosedRegion.shared_of_other`, `ClosedRegion.not_shared_subsingleton`, `ClosedRegion.mem_privateAlwaysEdges`, `ClosedRegion.candidate_not_private`, `ClosedRegion.shared_not_private`, `ClosedRegion.private_of_nonshared`, `ClosedRegion.overlap_not_private`。

`FiniteNativeCoordinates.lean` (25明示宣言):

`FiniteNative.Index0`, `FiniteNative.Index1`, `FiniteNative.Index2`, `FiniteNative.Index3`, `FiniteNative.coordinate0`, `FiniteNative.coordinate1`, `FiniteNative.coordinate2`, `FiniteNative.coordinate3`, `FiniteNative.privateIndex`, `FiniteNative.privateIndexDecidable`, `FiniteNative.XIndex`, `FiniteNative.ZIndex`, `FiniteNative.edgeSplit`, `FiniteNative.public_edge_value`, `FiniteNative.public_edge_private_independent`, `FiniteNative.faceMap`, `FiniteNative.faceMap_apply`, `FiniteNative.D`, `FiniteNative.F`, `FiniteNative.labelMap`, `FiniteNative.a`, `FiniteNative.c`, `FiniteNative.a_c_eq_edgeSplit_differential0`, `FiniteNative.D_add_F`, `FiniteNative.D_a_add_F_c`。

`FiniteCoordinateEnumerations.lean` (3明示宣言):

`FiniteElimination.Enumeration.fintype`, `FiniteElimination.Enumeration.subtype`, `FiniteFamily.indexEnumeration`。

`FiniteNativeMatrices.lean` (13明示宣言):

`FiniteNative.enum0`, `FiniteNative.enum3`, `FiniteNative.enum1`, `FiniteNative.enum2`, `FiniteNative.enumX`, `FiniteNative.enumZ`, `FiniteNative.Dmatrix`, `FiniteNative.Fmatrix`, `FiniteNative.Dmatrix_correct`, `FiniteNative.Fmatrix_correct`, `FiniteNative.generatedElimination`, `FiniteNative.generatedSection`, `FiniteNative.generatedSection_regular`。

`FiniteImageBasis.lean` (15明示宣言):

`FiniteElimination.Active`, `FiniteElimination.activeExtend`, `FiniteElimination.matrix_factor`, `FiniteElimination.row_factor`, `FiniteElimination.imageCoordinate`, `FiniteElimination.inactive_image_zero`, `FiniteElimination.imageRestore`, `FiniteElimination.image_coordinate_restore`, `FiniteElimination.image_restore_coordinate`, `FiniteElimination.imageEquivalence`, `FiniteElimination.imageBasisValue`, `FiniteElimination.imageBasis`, `FiniteElimination.image_basis_value`, `FiniteElimination.image_basis_independent`, `FiniteElimination.image_basis_span`。

`FiniteRectangularImage.lean` (10明示宣言):

`FiniteElimination.squareExtension_mulVec`, `FiniteElimination.rectangleImageToSquare`, `FiniteElimination.squareImageToRectangle`, `FiniteElimination.rectangleImageEquivalence`, `FiniteElimination.rectangularReduction`, `FiniteElimination.RectangularActive`, `FiniteElimination.rectangularImageEquivalence`, `FiniteElimination.rectangularBasisValue`, `FiniteElimination.rectangularBasis`, `FiniteElimination.rectangular_basis_value`。

`GeneratedRelationRows.lean` (8明示宣言):

`FiniteElimination.publicImageCoordinates`, `FiniteElimination.public_image_coordinates_surjective`, `FiniteElimination.public_image_coordinates_eq_iff`, `FiniteElimination.publicRow`, `FiniteElimination.public_rows_independent`, `FiniteElimination.public_row_value`, `FiniteElimination.public_row_count`, `FiniteElimination.public_affine_relation`。

`GeneratedNativeRelation.lean` (10明示宣言):

`FiniteNative.generatedPrivateImageCoordinates`, `FiniteNative.generatedPrivateImageBasisValue`, `FiniteNative.generatedQuotientEquivalence`, `FiniteNative.generated_kernel_projection_range`, `FiniteNative.publicMatrix`, `FiniteNative.public_matrix_correct`, `FiniteNative.generatedPublicRows`, `FiniteNative.generated_public_rows_independent`, `FiniteNative.generated_public_row_count`, `FiniteNative.generated_public_affine_relation`。

`NativeLocalInterface.lean` (16明示宣言):

`FiniteNative.rhs`, `FiniteNative.CoordinateEquation`, `FiniteNative.solutionCoordinateEquiv`, `FiniteNative.solution_coordinate_equivariant`, `FiniteNative.coordinateEquationEquivalence`, `FiniteNative.publicRestriction`, `FiniteNative.restriction_public_only`, `FiniteNative.GeneratedObjects`, `FiniteNative.generatedSolutionEquiv`, `FiniteNative.generated_solution_equivariant`, `FiniteNative.GeneratedGroupoid`, `FiniteNative.generatedEquationEquivalence`, `FiniteNative.generated_functor_label`, `FiniteNative.generated_inverse_label`, `FiniteNative.generated_left_obj`, `FiniteNative.generated_right_obj`。

`NativeRepairInterface.lean` (10明示宣言):

`NativeRepairInterface.Objects`, `NativeRepairInterface.repairEquiv`, `NativeRepairInterface.repair_equivariant`, `NativeRepairInterface.equivalence`, `NativeRepairInterface.left_obj`, `NativeRepairInterface.right_obj`, `NativeRepairInterface.functor_label_value`, `NativeRepairInterface.inverse_label_value`, `NativeRepairInterface.inverse_choice`, `NativeRepairInterface.public_value`。

`InterfaceFunctorInverses.lean` (4明示宣言):

`changed_label_functor_inverse`, `changed_label_inverse_functor`, `NativeRepairInterface.native_functor_inverse`, `NativeRepairInterface.native_inverse_functor`。

`FiniteCoverInterfaces.lean` (3明示宣言):

`FiniteCoverInterfaces.localEquivalence`, `FiniteCoverInterfaces.shared_restriction_public_only`, `FiniteCoverInterfaces.candidate_retained`。

全248明示宣言と生成APIを含む全sourceの個別公理監査を用いる。各監査対象sourceのimport行だけを除いた単一のexact-source focused auditはこのcycleの依存した到達点だけを検査し、Research全体/aggregate/全file loopをelaborateしない。全GOAL completion candidateではない。

20 sourceのfocused exact-source監査と必要な単一 concrete module確認はexit0。248明示宣言と生成APIを含む全305宣言を個別 `#print axioms`し標準公理のみ。axiom log SHA256 `a626f904823383199ef1bc59c42cab27346ccecc71224144f874c0e3ab912ac7`。全20 sourceの末尾にstandard axiom gateを置く。小さいF₂の非零/零行列で公開rows `[1]` / `[]` とsection値 `1` / `0` を実評価した。公開artifact/placeholder/hidden-BiDi/privacy/import方向/diff scanを確認する。

## Cycle 11 — 全変更範囲の厳密な有限被覆復元

```yaml
ledger_type: target_cycle_result
goal: G-130-aat-relative-repair-composition
cycle: 11
goal_blob_sha: 8da0fb4eb75d1cb5c37a9d4ddf5e03c18c0bb8a2
base_oid: a9f21e8a4eb434d35e7f8c4691cefc2cbfeb51fa
tracking_issue: 5132
report_path: research/reports/G-130-aat-relative-repair-composition.md
selection:
  proof_state_ref: "Issue #5132 Cycle10受理 comment5924491180 / report Cycle10 / PR5146 acceptance5924477748"
  proof_dag_predecessors: ["C1/A supported原実修復・全labels", "C4/A 全範囲包含", "C6/C8 同じ元cell相対族・全被覆/微分制限", "C7 元K actual/原値方程式bridge", "C10 原始有限入力の一回局所生成・全解/全labels strict両逆・public制限"]
  milestone: "GOAL Cの全Sに共通なstrict Glue_Sを、同じ候補零条件と共有元辺値/元頂点labelsから定め、有限原値glueと局所復元で元Kの独立全actual修復・全射へstrict相互逆functorsを構成。存在をpublic関係/共有/候補零だけで判定し、全内部自由度・全候補名/値・範囲包含を保つ"
  proof_obligations:
    - "全元0–3cellのfinite cover selectorをList.find?から生成し、適合族glueの停止・全原値・両逆を証明。既存非計算glueとの原値比較"
    - "原始supported actual repairsと独立supported原値方程式、全allowed元vertex gauge subgroupの同型/作用交換"
    - "元edge strict適合+全forbidden候補零の全局所objectsと、元vertex strict適合+forbidden coboundary零の全labelsからstrict groupoid生成"
    - "同じC10生成R_i×全kerD_iへ候補零/共有public条件を移し、full局所gaugeと共有vertex labelを保持するGlue_S"
    - "全global coord/recと全gauge labelsの相互逆、元actual辺choice/候補全値の復元、両functor合成そのもののidentity等号"
    - "存在iff public関係+shared値+forbidden候補零、任意内部自由度による全repair/arrow復元、全S⊆T functorsと同じcoord/recの交換"
  exit_criteria:
    - "同じ有限入力だけから構成し、S別のrepair先行列挙/消去/section/compatibility certificateを入力にしない"
    - "共有辺と共有頂点を別のstrict原値条件として全量化し、seam gauge/orbit/π0で置換しない"
    - "独立な元K actual修復とfull gauge arrowsを始域/終域にして全計算成分・原値・labelsの両逆を証明"
    - "候補名/禁止候補零条件、allS存在条件とrange relaxationが同じ生成データで成立"
    - "対象focused/個別全宣言axioms/scansと到達点全体の独立PR査読で受理"
  selection_reason: "C10で一回局所生成が閉じた。未達Cの実大域復元へ最短で接続し、Dの全範囲分類・Eの比較更新・W2のstrict性の共通前提を作る"
  expected_result_type: proof-obligation-discharged
  lean_targets: [FiniteIndexedGluing, SupportedEquation, SupportedNativeEquation, StrictSupportedCover, StrictCoverAction, GeneratedStrictCover, GeneratedCoverRestoration, GeneratedCoverRanges]
  risks: ["全labelsを効果商へ縮小しない", "共有値が全内部自由度から独立であること", "P/禁止候補と物理原辺固定の同一性", "label subgroupを結論fieldで供給しない", "zero extensionをchain-mapとして仮定しない", "computed selectorとnoncomputable actual bridgeの責務区別"]
  unchecked: ["本到達点の全実装・接続はこれから構成", "Cの表示比較とD–F/W1–W5/最終別completionは後続要求"]
```

このselectionは実装前の固定提案。全Cの表示比較（細分化、組立て/括弧づけ、基底/section/参照）は後続の独立到達点として残す。固定GOAL/終了条件の変更・縮小は行わない。終了条件前に分割が必要なら元条件と具体的split_reasonを保持する。

### 元の全cochainと全実修復の厳密復元

`FiniteFamilyGlue.selector`は完全な有限領域Listの`find?`から元cellを含む領域を選ぶ。被覆条件から検索成功を示し、`glue`はその元の値を読む。全原値、restrictionとの両逆、既存一般glueとの等号、領域List変更からの独立性を証明する。`FiniteCoverGlue.glue0`–`glue3`は同じ元0–3-cellの相対族へ適用する。zero extensionをchain mapと仮定しない。

`SupportedEquation.Objects`は独立な元face方程式の全解に禁止候補補正零を課したもの、`Labels`は元relative zero-cochainの全ラベルのうち禁止候補上のd0が零な全群である。`SupportedNativeEquation.repairEquiv`/`gaugeEquiv`は、同じ元Tの独立実修復と全supportedラベルへ双方向に対応させる。元辺の物理的固定と補正零の同値、同じ元d0との等号を受理済みの実対応から適用する。全元actual choices、全vertex labels、両functor合成そのもののidentity等号を保持する。

`StrictSupportedCover.Objects`は局所補正の**元共有辺の値**を全て比較する。`Labels`はこれとは別に全局所ラベルの**元共有頂点の値**を比較する。ラベルを辺への効果やorbitに置き換えない。`StrictCoverRestoration`は同じ有限selectorで全global元cochainを組み立て、face-coverのinjectivityと元restriction/d1交換から大域face方程式を、edge-coverから禁止候補零を導く。全labelsについても元d0交換と同じcandidate条件を導く。全object/labelの両逆・作用交換とstrict両逆functorを構成する。

`GeneratedStrictCover.LocalObject`はCycle10で同じprivate setから生成した`R_i × ker D_i`そのものである。`restored_value_public`は全非private元辺値がpublic zだけで決まることを示し、候補・共有辺についてprivate排除条件を元の定義から放電する。`PublicCompatible`はpublic上の禁止候補零と全共有元辺値一致だけを課す。全内部kernelを保持した`Objects`と独立なstrict局所方程式の間のcoord/recの両逆を証明する。公開条件の適合を外部certificateとして受け取って存在を仮定せず、この適合条件そのものを全量化対象と存在判定の右辺にする。

`GeneratedCoverAction.gauge`はCycle10の同じ元zero-cochainによる局所作用を各componentに適用する。strict元vertex labelsの全群を射に使い、作用後の適合・零/加法則・同じ原値復元との交換を証明する。全labelsを保つnative equivalenceと両functor恒等等号を与える。

`GeneratedPublicRelations.publicKernelEquiv`はstrict全objectを、可解なpublic関係族と各領域の**全**kernel族との積へ同型にする。任意のkernel値から全objectを構成し、零kernelで存在の逆方向を作る。`GeneratedCoverRestoration.objectEquiv`/`labelEquiv`はこの同じ構成を元Tの独立実修復と全ラベルへ接続する。`repair_nonempty_iff_public`は全Sについて元実修復の存在と、R_i所属・共有元値一致・禁止候補零の条件だけの可解性を同値にする。全元edge correctionとactual morphism choice、全元vertex labelの値、全射を含む両functor合成を証明する。

`GeneratedRangeInclusion`ではSを広げたとき候補条件だけを緩め、同じrelation/section/kernel・全原値/labelを保持する。`GeneratedCoverRanges.coordinate_functor_inclusion`/`reconstruction_functor_inclusion`は、受理済みの元actual rangeFunctorと、全object/arrowを含む関手そのものの等号で交換を証明する。Sごとに修復や消去を先行選択しない。

正の適合例は`SupportedEquation.zeroObject`から`StrictCoverZeroCases`の全rangeの元zero corrections・全generated/public objectを構成し、全public座標零を証明する。`StrictCoverNegativeCases`は2原頂点・4本の名前付き原辺・全1次元F₂係数・空の面/3-cellから入力を作る。`forbidden_correction`/`forbidden_label`は非零補正と非零d0を、`shared_edge`/`shared_label`は共有原辺/原頂点上の実際の不一致を構成する。`generated_forbidden_public`/`generated_shared_public`は同じ局所解を一回生成済みの関係へ送り、全generated適合とpublic関係の可解対象の双方から排除する。`zero_accepted`は同じ非自明な原表示で正の実例を構成する。実評価では原補正、原ラベル、同じgenerated public値がそれぞれ `[0,1]`。これはW1–W5の代替ではなく、各新述語の正負の入力である。固定指定例の実アフィン入力・評価は後続要求に残す。

`StrictCoverSupportAPIs`は元defectの零保存、元/相対d0の端点評価、既存の全生成同値の逆のpublic保存を公開する。`zeroObject`と`restored_public`はこのAPIを用い、foreign定義の下流展開に依存しない。既存の査読済みstatementと全計算値を保持する。

### Material premise とproof-use

| premise/data | 分類・状態 | 同じ原始入力からの生成・使用 |
| --- | --- | --- |
| 一般元T、実全核、strong opcartesian性、元core/lift/comparatorと生成輸送 | ambient-boundary / 本文由来 | 元actual equation correspondenceの現在のstatementと同じTへの適用。旧修復groupoidの全objects/labelsを始域にする |
| 閉Pと各U、P上の実face coherence、全元0–3-cell閉被覆 | ambient-boundary / 本文由来 | 元defectのrelative所属、有限selector成功、face-cover injectivity、全0–3原値glueと元restriction交換 |
| 同一有限体、実全核全体の有限基底、線形輸送、有限元edge/face/領域の完全列挙と所属判定 | ambient-boundary / Cの有限入力 | Cycle10の同じD/F/section/全kernelを使用。有限selectorとprivate判定。allowed Sを生成入力にしない |
| 全候補集合と全allowed S、全S⊆T | ambient-boundary / 本文の量化対象 | 同じcandidate名前の零条件だけを全量化し、full functor inclusion交換 |
| 一般glue・restrictionの両逆、global face equation、forbidden edge条件 | discharge-required / 放電済み | finite search、全元値比較、元r_d1とcover injectivity、元r_d0と局所labels条件から構成 |
| 局所generated全解・full gauge作用・section law・非private原値復元 | discharge-required / 受理済みpredecessorを同じ入力で使用 | Cycle10 PR #5146 final head0617f3b65b0c374d73153da495c5f7cc8e1f5fd3 / acceptance5924477748。現在のGeneratedObjects、generatedSolutionEquiv、generated_solution_equivariant、private/public APIsへ適用 |
| actual辺固定↔元補正零、全actual↔原値equation/全label | discharge-required / 受理済みpredecessorを同じ入力で使用 | Cycle1/7の現在のsolution_correction_zero_iff_edge、originalRepairEquiv/originalGaugeEquiv、original_d0と原値/actual choice APIs |
| public適合、独立actual repair、全private vector、全compatible label | 定理の全量化対象 / 存在判定の右辺 | object/labelの構成と両逆を証明し、Nonemptyを入力にしてglobal存在を仮定しない |
| zero defect | direction-hypothesis / 正の構成例だけ | 元zero correctionsから全rangeの適合objectを具体的に作る。一般復元・存在同値には追加しない |

一般actual/native category bridgeは非計算的な数学対応である。有限selectorとcochain assembly、生成済み有限座標のrec/gaugeの計算内容とは区別する。Fの実アフィン演算の評価証拠、Cの表示比較、D–F、W1–W5はこのcycleの完了申告に含めない。

```yaml
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "全Sに共通なstrict公開適合・全内部自由度・全共有vertex labelsから、元Kの独立actual修復/全射へのstrict相互逆functors、存在iff public条件、全範囲包含交換を構成"
  exit_criteria_status: ["同じ有限入力からselectorと一回生成済み局所表現を使用", "共有元辺値と全元vertex labelsを別々にstrict比較", "独立actual groupoidへの全値/choice/labels両逆と恒等関手等号", "全Sのpublic存在条件とrangeFunctor交換", "focused全宣言公理/scans。PR独立査読の最終受理はPR監査へ置く"]
  split_reason: none
  completion_candidate: no
  lean_artifacts: [FiniteFamilyGlue.equivalence, FiniteCoverGlue.glue0, FiniteCoverGlue.glue3, SupportedNativeEquation.equivalence, StrictCoverRestoration.equivalence, GeneratedStrictCover.objectEquiv, GeneratedPublicRelations.publicKernelEquiv, GeneratedCoverRestoration.equivalence, GeneratedCoverRestoration.functor_inverse, GeneratedCoverRestoration.inverse_functor, GeneratedCoverRestoration.repair_nonempty_iff_public, GeneratedCoverRanges.coordinate_functor_inclusion, GeneratedCoverRanges.reconstruction_functor_inclusion]
  claim_mapping:
    source_labels: ["GOAL Cの全S strict Glueと元全actual修復/全射の相互逆・全内部自由度・public存在条件・range包含", "n1017 §3.1", "design §4"]
    undischarged_assumptions: []
    acceptance_point: "選定したstrict全範囲復元の到達点。全GOAL completion candidateではない"
    port_status: not-applicable
  next_obligation: "Cの細分化/順序/括弧づけ/基底/section/参照の比較、D–F、W1–W5と別全GOAL completion review"
audits:
  premise_delta:
    discharged: ["finite selector検索成功と全元glue", "global face/support条件", "full strict labels作用と復元", "private自由度からのpublic独立性", "actualとの全functor両逆とallS包含交換"]
    remaining: []
  certificate_provenance:
    discharged: ["同じ元閉被覆/有限リストからglue", "同じ元d0/d1/defectと受理済み局所generatorから全対象/射復元"]
    unresolved: []
  proof_use:
    used: ["cover各次数の全原値復元/face injectivity", "元r_d0/r_d1と同じactual correction唯一性", "同じgeneratedSolutionEquiv/full label action/public不変性", "同じ原始range inclusion"]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: ["15 exact-source単一focused監査exit0/errors0/warnings0", "186明示宣言の全個別公理は標準のみ", "axiom log SHA2566f406d1f1e974a6b10b51a5d33840182dec8343a93e48e81450ecd4dbf8543b6"]
  blocking_findings: []
  next_obligation: "Cの各表示比較とD–F/W1–W5。PR査読・root受理・CI・merge/Issue同期を経て次到達点へ進む"
```

### 全宣言の監査対象

`FiniteIndexedGluing.lean` (9明示宣言):

`FiniteFamilyGlue.selector`, `FiniteFamilyGlue.selector_mem`, `FiniteFamilyGlue.glue`, `FiniteFamilyGlue.glue_value`, `FiniteFamilyGlue.glue_restriction`, `FiniteFamilyGlue.restriction_glue`, `FiniteFamilyGlue.equivalence`, `FiniteFamilyGlue.glue_eq_general`, `FiniteFamilyGlue.glue_enum_independent`。

`FiniteCoverGluing.lean` (20明示宣言):

`FiniteCoverGlue.glue0`, `FiniteCoverGlue.glue0_value`, `FiniteCoverGlue.glue_restriction0`, `FiniteCoverGlue.restrict_glue0`, `FiniteCoverGlue.glue0_eq_general`, `FiniteCoverGlue.glue1`, `FiniteCoverGlue.glue1_value`, `FiniteCoverGlue.glue_restriction1`, `FiniteCoverGlue.restrict_glue1`, `FiniteCoverGlue.glue1_eq_general`, `FiniteCoverGlue.glue2`, `FiniteCoverGlue.glue2_value`, `FiniteCoverGlue.glue_restriction2`, `FiniteCoverGlue.restrict_glue2`, `FiniteCoverGlue.glue2_eq_general`, `FiniteCoverGlue.glue3`, `FiniteCoverGlue.glue3_value`, `FiniteCoverGlue.glue_restriction3`, `FiniteCoverGlue.restrict_glue3`, `FiniteCoverGlue.glue3_eq_general`。

`SupportedEquation.lean` (14明示宣言):

`SupportedEquation.Labels`, `SupportedEquation.mem_labels`, `SupportedEquation.not_mem_labels_of_ne`, `SupportedEquation.labels_all`, `SupportedEquation.Objects`, `SupportedEquation.object_zero`, `SupportedEquation.not_supported_of_ne`, `SupportedEquation.gauge`, `SupportedEquation.gauge_zero`, `SupportedEquation.gauge_add`, `SupportedEquation.addAction`, `SupportedEquation.Groupoid`, `SupportedEquation.gauge_value`, `SupportedEquation.zeroObject`。

`SupportedNativeEquation.lean` (15明示宣言):

`SupportedNativeEquation.baseRepair`, `SupportedNativeEquation.baseGauge`, `SupportedNativeEquation.gaugeEquiv`, `SupportedNativeEquation.gauge_value`, `SupportedNativeEquation.gauge_inverse_value`, `SupportedNativeEquation.repairEquiv`, `SupportedNativeEquation.repair_equivariant`, `SupportedNativeEquation.equivalence`, `SupportedNativeEquation.repair_value`, `SupportedNativeEquation.repair_inverse_value`, `SupportedNativeEquation.inverse_choice`, `SupportedNativeEquation.functor_inverse`, `SupportedNativeEquation.inverse_functor`, `SupportedNativeEquation.functor_label_value`, `SupportedNativeEquation.inverse_label_value`。

`StrictSupportedCover.lean` (13明示宣言):

`StrictSupportedCover.Labels`, `StrictSupportedCover.mem_labels`, `StrictSupportedCover.not_mem_labels_of_ne`, `StrictSupportedCover.localLabels`, `StrictSupportedCover.label_overlap`, `StrictSupportedCover.Objects`, `StrictSupportedCover.localEdges`, `StrictSupportedCover.not_strict_of_ne`, `StrictSupportedCover.gauge`, `StrictSupportedCover.gauge_zero`, `StrictSupportedCover.gauge_add`, `StrictSupportedCover.addAction`, `StrictSupportedCover.Groupoid`。

`StrictCoverRestoration.lean` (14明示宣言):

`StrictCoverRestoration.restrictLabels`, `StrictCoverRestoration.restrictObjects`, `StrictCoverRestoration.glueLabels`, `StrictCoverRestoration.restrict_glue_labels`, `StrictCoverRestoration.glue_restrict_labels`, `StrictCoverRestoration.labelEquiv`, `StrictCoverRestoration.glueObjects`, `StrictCoverRestoration.restrict_glue_objects`, `StrictCoverRestoration.glue_restrict_objects`, `StrictCoverRestoration.objectEquiv`, `StrictCoverRestoration.restrict_equivariant`, `StrictCoverRestoration.equivalence`, `StrictCoverRestoration.functor_inverse`, `StrictCoverRestoration.inverse_functor`。

`GeneratedStrictCover.lean` (12明示宣言):

`GeneratedStrictCover.LocalObject`, `GeneratedStrictCover.publicValue`, `GeneratedStrictCover.restored_public`, `GeneratedStrictCover.restored_value_public`, `GeneratedStrictCover.PublicCompatible`, `GeneratedStrictCover.Objects`, `GeneratedStrictCover.coordinate`, `GeneratedStrictCover.coordinate_public`, `GeneratedStrictCover.restore`, `GeneratedStrictCover.restore_coordinate`, `GeneratedStrictCover.coordinate_restore`, `GeneratedStrictCover.objectEquiv`。

`GeneratedPublicRelations.lean` (8明示宣言):

`GeneratedPublicRelations.LocalRelation`, `GeneratedPublicRelations.Objects`, `GeneratedPublicRelations.publicCoordinates`, `GeneratedPublicRelations.assemble`, `GeneratedPublicRelations.publicKernelEquiv`, `GeneratedPublicRelations.nonempty_iff_public`, `GeneratedPublicRelations.not_supported_of_ne`, `GeneratedPublicRelations.not_shared_of_ne`。

`GeneratedCoverAction.lean` (12明示宣言):

`GeneratedCoverAction.coordinate_equivariant`, `GeneratedCoverAction.gauge`, `GeneratedCoverAction.gauge_zero`, `GeneratedCoverAction.gauge_add`, `GeneratedCoverAction.addAction`, `GeneratedCoverAction.Groupoid`, `GeneratedCoverAction.equivariant`, `GeneratedCoverAction.equivalence`, `GeneratedCoverAction.functor_inverse`, `GeneratedCoverAction.inverse_functor`, `GeneratedCoverAction.functor_label`, `GeneratedCoverAction.inverse_label`。

`GeneratedRangeInclusion.lean` (9明示宣言):

`GeneratedRangeInclusion.labelsInclusion`, `GeneratedRangeInclusion.objectsInclusion`, `GeneratedRangeInclusion.publicInclusion`, `GeneratedRangeInclusion.equivariant`, `GeneratedRangeInclusion.functor`, `GeneratedRangeInclusion.functor_obj_values`, `GeneratedRangeInclusion.functor_label_value`, `GeneratedRangeInclusion.functor_comp`, `GeneratedRangeInclusion.public_inclusion_comm`。

`GeneratedCoverRestoration.lean` (14明示宣言):

`GeneratedCoverRestoration.labelEquiv`, `GeneratedCoverRestoration.objectEquiv`, `GeneratedCoverRestoration.equivariant`, `GeneratedCoverRestoration.equivalence`, `GeneratedCoverRestoration.functor_inverse`, `GeneratedCoverRestoration.inverse_functor`, `GeneratedCoverRestoration.inverse_edge_value`, `GeneratedCoverRestoration.forward_edge_value`, `GeneratedCoverRestoration.inverse_choice`, `GeneratedCoverRestoration.label_value`, `GeneratedCoverRestoration.label_inverse_value`, `GeneratedCoverRestoration.functor_label_value`, `GeneratedCoverRestoration.inverse_label_value`, `GeneratedCoverRestoration.repair_nonempty_iff_public`。

`GeneratedCoverRanges.lean` (6明示宣言):

`GeneratedCoverRanges.coordinate_inclusion`, `GeneratedCoverRanges.reconstruction_inclusion`, `GeneratedCoverRanges.label_inclusion`, `GeneratedCoverRanges.label_reconstruction_inclusion`, `GeneratedCoverRanges.coordinate_functor_inclusion`, `GeneratedCoverRanges.reconstruction_functor_inclusion`。

`StrictCoverZeroCases.lean` (4明示宣言):

`StrictCoverZeroCases.originalZero`, `StrictCoverZeroCases.generatedZero`, `StrictCoverZeroCases.publicZero`, `StrictCoverZeroCases.public_zero_values`。


`StrictCoverSupportAPIs.lean` (4明示宣言):

`CoverEquation.defect_zero`, `ClosedRegion.d0Hom_edge_value`, `RelativeCover.d0_edge_value`, `FiniteNative.generated_solution_inverse_public`。

`StrictCoverNegativeCases.lean` (32明示宣言):

`StrictCoverNegativeCases.geometry`, `StrictCoverNegativeCases.coefficients`, `StrictCoverNegativeCases.coefficientModule`, `StrictCoverNegativeCases.bases`, `StrictCoverNegativeCases.regions`, `StrictCoverNegativeCases.edge`, `StrictCoverNegativeCases.vertexDecidable`, `StrictCoverNegativeCases.edgeDecidable`, `StrictCoverNegativeCases.pEdgesDecidable`, `StrictCoverNegativeCases.pFacesDecidable`, `StrictCoverNegativeCases.regionVerticesDecidable`, `StrictCoverNegativeCases.regionEdgesDecidable`, `StrictCoverNegativeCases.regionFacesDecidable`, `StrictCoverNegativeCases.faceDecidable`, `StrictCoverNegativeCases.linear`, `StrictCoverNegativeCases.fieldEnum`, `StrictCoverNegativeCases.edgeEnum`, `StrictCoverNegativeCases.faceEnum`, `StrictCoverNegativeCases.solution`, `StrictCoverNegativeCases.label`, `StrictCoverNegativeCases.label_d0`, `StrictCoverNegativeCases.forbidden_correction`, `StrictCoverNegativeCases.forbidden_label`, `StrictCoverNegativeCases.localObjects`, `StrictCoverNegativeCases.shared_edge`, `StrictCoverNegativeCases.localLabels`, `StrictCoverNegativeCases.shared_label`, `StrictCoverNegativeCases.generated`, `StrictCoverNegativeCases.generated_value`, `StrictCoverNegativeCases.generated_forbidden_public`, `StrictCoverNegativeCases.generated_shared_public`, `StrictCoverNegativeCases.zero_accepted`。

15 source全186明示宣言を個別に`#print axioms`し、標準公理だけであることを確認した。初回の遅延生成r2 APIは零保存APIの使用で発生しなくなり、最終logの対象集合は全186明示宣言と完全一致する。全15 source末尾にstandard axiom gateを置く。exact-source focused監査はこの依存した到達点のbodyだけを一回検査し、Research全体/aggregate/全file loopをelaborateしない。axiom log SHA256 `6f406d1f1e974a6b10b51a5d33840182dec8343a93e48e81450ecd4dbf8543b6`、exit0/errors0/warnings0。必要な単一concrete module `StrictCoverNegativeCases` の確認はexit0。2セル・2領域の有限被覆をF₃値で実評価し、selector `[0,1]`、元全値 `[1,2]`、逆順Listでの元全値 `[1,2]` を得た。上記F₂原表示の原補正/原ラベル/generated public実評価は全て `[0,1]`（W1–W5の代替ではない）。placeholder/hidden-BiDi/privacy/import方向/diff scanはclean。PR内容の受理・CI・merge evidenceはPR/Issueへ置く。


## Cycle 12 — 表示変更と同じ実復元の比較

```yaml
ledger_type: target_cycle_result
goal: G-130-aat-relative-repair-composition
cycle: 12
goal_blob_sha: 8da0fb4eb75d1cb5c37a9d4ddf5e03c18c0bb8a2
base_oid: 593a04203d84c23a90d525fd95193fa3302f2ebb
tracking_issue: 5132
report_path: research/reports/G-130-aat-relative-repair-composition.md
selection:
  proof_state_ref: "Issue #5132 Cycle11受理5925586476 / PR5147 acceptance5925577749 / report Cycle11"
  proof_dag_predecessors: ["C4 元physical anchorを保つ参照変更/全範囲包含", "C5–8 全原cell restriction/finite cover/assembly geometry", "C10 全実核の一回局所generator/full inverse", "C11 全S strict有限glue/元actual全functor両逆"]
  milestone: "GOAL Cの全表示変更（有限被覆細分化・組立て順/括弧・全基底・section・実参照lift）について元Kの全実修復/全射へ同じ復元を与える具体比較を構成し、比較合成・全S包含・元候補名/値/full vertex labelsの保存を証明する"
  proof_obligations:
    - "同じD/F/rの任意regular sections間の(z,n)↦(z,n+(σ−σ′)(r−Fz))、全ker所属/両逆/三比較合成/rec交換/full gaugeを証明。原finite generatorの各sectionへ適用し法則を放電"
    - "元全0–3cellの任意full基底間の線形座標比較、原値/differential/private-public/全kernel/全labelの輸送と同じ局所generated rec交換を証明"
    - "原入力有限表示からcover coord′recの全objects/labels/native functorsを構成。全両逆/三被覆比較合成/同じ元actual choice復元/allS包含交換を証明"
    - "細分比較をfinite原値glue→元region restriction→生成coordsとして明示。有限二項組立てのflatten/unflattenは全shared原edgeとvertex label条件を保ち、全順序/括弧で同じ全原値を復元。中間再消去を行う場合は全候補/未組立領域共有辺を保持"
    - "任意実alternative liftからa/shifted actual defectを構成。独立raw anchored equationsはh′=-aの固定条件を保持、h′+aの正規化で同じfinite生成/全glueへ接続。h′=h−a/δ′=δ+d1a、全actual choices/full gauge/native比較/合成とallS交換を証明"
    - "一般比較の全向きと原入力への適用、構成法則/原名・物理値/全射・自由度保持をfocused全宣言axioms/scans・到達点独立PR監査で固定"
  exit_criteria:
    - "上記全表示変更とその複合を扱い、比較/rec法則をcertificate fieldやglobal repair列挙へ移さない"
    - "元K/full kernels/全0–3cells/all actual choices/full labels/全候補名・物理固定条件/allSを保つ"
    - "比較の相互逆・合成・同じ実復元/全arrowとの可換性を構成し、忘却後object equalityだけへ弱めない"
    - "参照aはP/candidates上で零と仮定せず、物理anchorを−aへ運ぶ"
    - "対象全宣言focused/個別axioms/scans、登録/台帳、標準独立PR gateとroot受理を閉じる"
  selection_reason: "C11でstrict全S復元が閉じた。全表示比較を同じ復元軸に統合しCを閉じ、D/Eの再利用と指定Wの基盤を直接作る"
  expected_result_type: proof-obligation-discharged
  lean_targets: [SectionComparison, FullBasisComparison, FiniteCoverDisplay, GeneratedDisplayComparison, StrictBinaryAssembly, AnchoredFiniteDisplay]
  risks: ["generic Equiv改名だけで具体比較を代替しない", "section法則/cover同値を入力certificateにしない", "full kernel/labelsを縮めない", "組立てのshared original条件を全保持", "shiftでP上δ零を仮定しない", "native totalFunctor/transportとallS交換"]
  unchecked: ["本到達点全実装・接続はこれから構成", "D–F/W1–W5と別全GOAL completionは後続要求"]
```

実装前の固定selection。終了条件前の分割は元条件と具体的split_reason・未完obligationを保持する。Cだけの受理を全GOAL completionとは呼ばない。

```yaml
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta:
    - "SectionComparisonは任意regular sectionの具体的な全核座標式/両逆/三比較/full gaugeを証明し、GeneratedSectionComparisonが原生成sectionのregular法則を放電して適用"
    - "FullBasisComparisonは原全0–3cell/d0–d2とprivate-public座標を全基底間で輸送し、GeneratedLocalComparisonが同じ原局所補正/全射への生成比較を構成"
    - "GeneratedDisplayComparisonは原actual source経由で任意原有限被覆表示のcoord/rec、全両逆/三比較、原辺値・全actual choice/full vertex label/allSを保存"
    - "StrictBinary/StrictFiniteAssemblyは全shared原edge/vertex条件を保持した独立nested tuplesのflatten/unflattenを構成。GeneratedFiniteAssemblyは同じ一回生成へ接続し全順序/括弧/allSの全functor可換性を証明"
    - "AnchoredLocal/AnchoredFinite/AnchoredActualは実alternative liftのa/shifted defectと独立raw固定条件を構成し、h′+aで原有限glueへ正規化。AnchoredDisplayComparisonはlift・原cover・全基底の同時変更、三比較/全両逆/allSを同じphysical actual repairへ戻す"
    - "16新sourceと所有2 sourceの新API2件、全266明示宣言と50生成宣言を個別公理監査。非零核section/全basis/3葉括弧/empty familyの実計算とshared原edge/full labelの正負入力を検証。標準PR監査による受理はPR/Issueに固定"
  exit_criteria_status:
    - "全選定表示変更・複合: explicit section式、原basis/private-public値式、raw h′+a−a′、actual source経由の全native functor比較/rec/三合成"
    - "全実核/0–3cell/候補/固定/射/allS: full coordinate conjugacy、privateに共有辺/候補を入れない同じ原generator、full label群と値保存、物理anchor−a、全range functor等式"
    - "全両逆: 各object/labelの全逆とfunctor_inverse/inverse_functor。flattenは全cross条件を利用。stabilizerを含む元labelを保持"
    - "任意参照: aのP/candidates上零を追加せず、独立raw Objectsの固定値を−aと定義しactual defect_shiftから正規化の補正方程式を導く"
    - "検証/登録/台帳: 全明示・生成宣言focused公理監査、有限実計算・原型negative predicate、16新module登録、機械scan。標準独立PR gate/root受理は固定PR headのコメントへ記録"
  split_reason: none
  completion_candidate: no
  lean_artifacts: [C12AnchoredRegression, FinitePartition.join_private, FiniteNative.private_edge_value, SectionComparison, FullBasisComparison, StrictFunctorComparison, FiniteCoverDisplay, GeneratedSectionComparison, GeneratedLocalComparison, GeneratedDisplayComparison, StrictBinaryAssembly, FiniteBinaryTuples, StrictFiniteAssembly, GeneratedFiniteAssembly, AnchoredLocalEquation, AnchoredFiniteCover, AnchoredActualCover, AnchoredDisplayComparison]
  evidence: ["下記18 source対応/266明示宣言と各full inverse/value/range theorem", "先行C4/C10/C11の実入力・生成・全復元への直接適用"]
  claim_mapping:
    theorem_names: ["LinearInterface.section_comparison_kernel", "FiniteFamily.restore_basis_comparison", "GeneratedDisplay.comparison_rec", "GeneratedDisplay.comparison_comp", "GeneratedFiniteAssembly.comparison_generated", "AnchoredDisplay.comparison_value", "AnchoredDisplay.comparison_range"]
    source_labels: ["GOAL C末段の全表示比較", "GOAL A物理的な参照座標変更", "GOAL C全範囲/full actual objects/full arrows"]
    conjuncts: ["section/basis: 原局所generatedSolutionEquivへ接続", "finite refinement/order/bracket: 原0–3cell/glue/full labelsへ接続", "actual lift shift: raw equation/actual repair/full arrow/allSへ接続"]
    undischarged_assumptions: []
    acceptance_point: "選定した全表示比較の具体構成を同じ原actual復元へ接続したproposal。標準独立監査とroot受理は固定PR headで行う"
    port_status: unported
  remaining_goal_obligations: ["D全変更範囲/双対不能証拠/極小分類", "E記号的更新/実一点環境/全原表示内部分割", "F任意有限体の全実アフィン塔と各仮定放電", "W1–W5原指定実例の全要求", "別全GOAL completion packet/独立4本最終監査"]
audits:
  premise_delta:
    discharged: ["σ/τのregular性を原finite generatorのgeneratedSection_regularで放電", "native object/label比較はC11生成された全actual両逆を利用", "raw δ′=δ+d1aを実alternative liftから導く", "nested/共有edge/full vertex compatibilityは独立objects/labelsをflattenして実構成", "全comparison法則は構成されたfull functor inverseから導く"]
    remaining: ["上記remaining_goal_obligations。C12を全G-130 completionとして昇格しない"]
  certificate_provenance:
    discharged: ["FiniteCoverDisplayのfieldは原有限入力/0–3cell closed cover/full bases/全列挙のみ。比較・復元・零障害をfieldへ供給しない", "原生成section/full image/full kernelはC10実消去の出力", "shiftは実other liftのsolutionCorrection、defectは同じ実辺の合成", "treeとleaf bijectionは入力assembly shape/order。共有補正/全label/作用/比較は構成する"]
    unresolved: []
  proof_use:
    used: ["regular性→section差のker所属/rec/作用", "full原basis逆→元値/private-public/differential輸送", "全actual/kernel逆→有限表示比較の全obj/arrow/choice保存", "原edge closure/全cross compatibility→binary/finite flatten", "実correctedDefect/closed r_d1→raw補正方程式", "同一actual aと原full labels→raw共有値/作用/allS交換"]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: ["16 exact-source bodiesと新API2件の単一milestone focused監査exit0/errors0/warnings0", "266明示+50生成=316全個別標準公理", "axiom log SHA256 2bfeca8532c0acd125d64ac19313b73bcb556acfabe8c212259dcbf7df4fc848", "有限原値section/basis/bracket/emptyと共有拒否/零受理、actual非零anchorのraw受理/拒否の検証", "単一concrete endpoint AnchoredDisplayComparisonのtargeted module確認"]
  blocking_findings: []
  next_obligation: "C12固定headの標準review-pr/math-lean-review受理後、Dの同じ原大域微分/局所公開関係/双対証拠/全S極小分類へ進む"
```

### C12 — 構成と受理spine

全宣言のnamespace prefixは `AAT.AG.RelativeRepairComposition.`。各sourceは同名Research moduleとして登録する。
当初selectionの `AnchoredFiniteDisplay` は、独立raw局所方程式・有限strict族・actual接続・全表示比較の4 source (`AnchoredLocalEquation` / `AnchoredFiniteCover` / `AnchoredActualCover` / `AnchoredDisplayComparison`) で構成する。終了条件は固定selectionのままである。

| proof obligation | 構成・直接の原入力適用 | 全実対象・射の確認 |
| --- | --- | --- |
| 任意regular section | `LinearInterface.sectionComparison` の $(z,n+(σ−τ)(r−Fz))$、`FiniteNative.generated_section_*` | full kernel差、原rec、全gauge、全native両逆・三比較 |
| full basis | `FiniteFamily.basisComparison` / `FiniteNative.splitBasisComparison`、`FiniteNative.basis_comparison_d0` / `basis_comparison_d1` / `basis_comparison_d2` / `local_object_value` | 原全0–3cellの値・微分・private/public・元頂点全label |
| finite display | `GeneratedDisplay.objectComparison` / `comparison` / `refinement_*_value` | 原actual全choices・元辺値・全射・両逆・合成・allS |
| binary/finite order・bracket | `StrictBinary.objectEquiv` / `labelEquiv`、`StrictFiniteAssembly.objectEquiv`、`GeneratedFiniteAssembly.*` | 全shared原edgeと原vertex label、各独立leaf補正、全kernel・full functor/allS |
| actual lift / 物理anchor | `AnchoredLocal.defect_shift` / `objectEquiv`、`AnchoredFinite.equivalence`、`AnchoredActualCover.equivalence`、`AnchoredDisplay.*` | raw h′=-a固定、元choice/全label、同時cover/basis/reference比較と三合成、allS |

同じD/F/rについてsectionだけを変えると、公開zは固定で内部全核成分だけが差だけ動く。
全原basis変更は原cell値を復元して新basisで読み直し、各実微分と輸送される。
有限表示比較は旧表示の元actual repairを復元して新表示へcoordinateする。
細分された原cell値と原vertex labelは、その親領域の同じ原cellへのliteral restrictionと一致する。
二項・有限組立ては全独立leafの補正をnested productに保持し、内部・crossの全shared条件を利用してflatten/unflattenする。
同じ全leaf領域から一度生成されたinterfaceへ接続するため、途中の新たな消去でshared候補や残りの共有辺を落とさない。

raw参照表示は、other liftの実defectを使い、固定原辺でh′=-aを満たす独立方程式である。
P上のaの零性を仮定せず、h′+aによる正規化を元相対補正へ戻す。
全full labelsのraw gaugeは直接の元d0作用として定義する。
複数の参照・basis・coverの同時比較は同じ元actual repairの復元を介し、raw値がh′+a−a′となる。
raw対象だけでなく全functorの両逆、元choice、全vertex labels、三比較、allS包含との交換を証明する。

`SectionComparison.lean` (16明示宣言、source SHA256 `25318bccbff93a4f913c05deb3b1daf97b7bdc04e03aac083a1bda47605fc868`):

`LinearInterface.relation_section_iff`、`LinearInterface.sectionComparison`、`LinearInterface.section_comparison_public`、`LinearInterface.section_comparison_kernel`、`LinearInterface.section_difference_mem`、`LinearInterface.rec_section_comparison`、`LinearInterface.coord_section_comparison`、`LinearInterface.section_comparison_inverse`、`LinearInterface.section_comparison_comp`、`LinearInterface.section_comparison_self`、`LinearInterface.section_comparison_gauge`、`LinearInterface.sectionEquivalence`、`LinearInterface.section_functor_label`、`LinearInterface.section_inverse_label`、`LinearInterface.section_functor_inverse`、`LinearInterface.section_inverse_functor`。

`FullBasisComparison.lean` (21明示宣言、source SHA256 `6f507d8e82d38d8c58e7f322779ef9ed694cafe33810471452eeb67a84f33b20`):

`FiniteFamily.basisComparison`、`FiniteFamily.restore_basis_comparison`、`FiniteFamily.basis_comparison_value`、`FiniteFamily.basis_comparison_inverse`、`FiniteFamily.basis_comparison_comp`、`FiniteFamily.basis_comparison_self`、`FiniteNative.basisComparison0`、`FiniteNative.basisComparison1`、`FiniteNative.basisComparison2`、`FiniteNative.basisComparison3`、`FiniteNative.restore_basis0`、`FiniteNative.restore_basis1`、`FiniteNative.restore_basis2`、`FiniteNative.restore_basis3`、`FiniteNative.basis_comparison_d0`、`FiniteNative.basis_comparison_d1`、`FiniteNative.basis_comparison_d2`、`FiniteNative.splitBasisComparison`、`FiniteNative.restore_split_basis`、`FiniteNative.split_basis_public`、`FiniteNative.split_basis_private`。

`StrictFunctorComparison.lean` (8明示宣言、source SHA256 `e815e4f243c0103a717b27560537000925dd43574752ff5cb9b56d4161721d46`):

`strictComparison`、`strict_comparison_rec`、`strict_comparison_coord`、`strict_comparison_comp`、`strict_comparison_inverse`、`strict_inverse_comparison`、`strict_trans_functor_inverse`、`strict_trans_inverse_functor`。

`FiniteCoverDisplay.lean` (9明示宣言、source SHA256 `f053a4a65d11ed83cf46c6daf2b7bccdcb4a9d7f3c8c6e3f91c574c86462a37f`):

`FiniteCoverDisplay`、`FiniteCoverDisplay.indexFinite`、`FiniteCoverDisplay.indexEquality`、`FiniteCoverDisplay.regionVertexDecision`、`FiniteCoverDisplay.regionEdgeDecision`、`FiniteCoverDisplay.regionFaceDecision`、`FiniteCoverDisplay.Objects`、`FiniteCoverDisplay.Labels`、`FiniteCoverDisplay.Groupoid`。

`GeneratedSectionComparison.lean` (11明示宣言、source SHA256 `4113a5f411d512f74880a712d4af8decfa5d4be0a89c49d6442dc08ac6545854`):

`FiniteNative.generatedSectionComparison`、`FiniteNative.generated_section_public`、`FiniteNative.generated_section_kernel`、`FiniteNative.generated_section_difference_mem`、`FiniteNative.generated_section_coord`、`FiniteNative.generated_section_rec`、`FiniteNative.generated_section_edge`、`FiniteNative.generated_section_gauge`、`FiniteNative.generatedSectionEquivalence`、`FiniteNative.generated_section_functor_inverse`、`FiniteNative.generated_section_inverse_functor`。

`GeneratedLocalComparison.lean` (11明示宣言、source SHA256 `85f5b9bf19f821cec743f5e8af682d2023cac6fb7fb9d05a1db681044396fc64`):

`FiniteNative.generated_equation_functor_inverse`、`FiniteNative.generated_equation_inverse_functor`、`FiniteNative.localObjectComparison`、`FiniteNative.local_object_rec`、`FiniteNative.local_object_value`、`FiniteNative.localComparison`、`FiniteNative.local_comparison_rec`、`FiniteNative.local_comparison_comp`、`FiniteNative.local_comparison_inverse`、`FiniteNative.local_inverse_comparison`、`FiniteNative.local_comparison_label`。

`GeneratedDisplayComparison.lean` (23明示宣言、source SHA256 `ce32c72410fa6ef51a3ecee044977e062e357ed26f70b0dbae61c9cb0f44d13b`):

`GeneratedDisplay.objectEquiv`、`GeneratedDisplay.labelEquiv`、`GeneratedDisplay.equivalence`、`GeneratedDisplay.functor_inverse`、`GeneratedDisplay.inverse_functor`、`GeneratedDisplay.objectComparison`、`GeneratedDisplay.labelComparison`、`GeneratedDisplay.comparison`、`GeneratedDisplay.comparison_obj`、`GeneratedDisplay.comparison_rec`、`GeneratedDisplay.comparison_coord`、`GeneratedDisplay.comparison_comp`、`GeneratedDisplay.comparison_inverse`、`GeneratedDisplay.inverse_comparison`、`GeneratedDisplay.comparison_edge_value`、`GeneratedDisplay.object_comparison_rec`、`GeneratedDisplay.comparison_choice`、`GeneratedDisplay.comparison_label_value`、`GeneratedDisplay.comparison_map_label`、`GeneratedDisplay.refinement_edge_value`、`GeneratedDisplay.refinement_label_value`、`GeneratedDisplay.rangeFunctor`、`GeneratedDisplay.comparison_range`。

`StrictBinaryAssembly.lean` (20明示宣言、source SHA256 `971ca2068b2847da2bc603cb57986adbaa997c2e1ebf316a7d1cb0725c30fd8a`):

`StrictBinary.regions`、`StrictBinary.Labels`、`StrictBinary.flattenLabels`、`StrictBinary.unflattenLabels`、`StrictBinary.labelEquiv`、`StrictBinary.Objects`、`StrictBinary.flattenObjects`、`StrictBinary.unflattenObjects`、`StrictBinary.objectEquiv`、`StrictBinary.gauge`、`StrictBinary.gauge_left`、`StrictBinary.gauge_right`、`StrictBinary.gauge_zero`、`StrictBinary.gauge_add`、`StrictBinary.addAction`、`StrictBinary.Groupoid`、`StrictBinary.equivariant`、`StrictBinary.equivalence`、`StrictBinary.functor_inverse`、`StrictBinary.inverse_functor`。

`FiniteBinaryTuples.lean` (10明示宣言、source SHA256 `77bc7165a30a2b789a797248a11c4834b15ede4c650f1515156bd79571c1071b`):

`FiniteBinary.Tree`、`FiniteBinary.Leaves`、`FiniteBinary.leafFintype`、`FiniteBinary.leafEquality`、`FiniteBinary.Tuple`、`FiniteBinary.tupleEquiv`、`FiniteBinary.tuple_restore`、`FiniteBinary.tuple_read`、`FiniteBinary.tuple_left`、`FiniteBinary.tuple_right`。

`StrictFiniteAssembly.lean` (22明示宣言、source SHA256 `a917525e83db1a113cc0b6904c502291fc59e4188dea68819feb342568fc4578`):

`StrictFiniteAssembly.Nested`、`StrictFiniteAssembly.leafEquiv`、`StrictFiniteAssembly.tupleEquiv`、`StrictFiniteAssembly.tuple_leaf`、`StrictFiniteAssembly.Objects`、`StrictFiniteAssembly.flatten`、`StrictFiniteAssembly.unflatten`、`StrictFiniteAssembly.objectEquiv`、`StrictFiniteAssembly.gauge`、`StrictFiniteAssembly.gauge_flatten`、`StrictFiniteAssembly.gauge_leaf`、`StrictFiniteAssembly.gauge_zero`、`StrictFiniteAssembly.gauge_add`、`StrictFiniteAssembly.addAction`、`StrictFiniteAssembly.Groupoid`、`StrictFiniteAssembly.equivariant`、`StrictFiniteAssembly.equivalence`、`StrictFiniteAssembly.functor_inverse`、`StrictFiniteAssembly.inverse_functor`、`StrictFiniteAssembly.comparison`、`StrictFiniteAssembly.comparison_rec`、`StrictFiniteAssembly.comparison_comp`。

`GeneratedFiniteAssembly.lean` (15明示宣言、source SHA256 `0f978d9e456573ac1adb07f8bc1e9c9dd8c004c159401b609efbee3f92d7617f`):

`GeneratedFiniteAssembly.objectEquiv`、`GeneratedFiniteAssembly.restore_objects`、`GeneratedFiniteAssembly.restore_leaf_value`、`GeneratedFiniteAssembly.equivalence`、`GeneratedFiniteAssembly.functor_inverse`、`GeneratedFiniteAssembly.inverse_functor`、`GeneratedFiniteAssembly.reconstruction_functor`、`GeneratedFiniteAssembly.functor_label`、`GeneratedFiniteAssembly.comparison_generation`、`GeneratedFiniteAssembly.rangeFunctor`、`GeneratedFiniteAssembly.range_generation`、`GeneratedFiniteAssembly.range_leaf_value`、`GeneratedFiniteAssembly.range_label_value`、`GeneratedFiniteAssembly.comparison_generated`、`GeneratedFiniteAssembly.comparison_range`。

`AnchoredLocalEquation.lean` (19明示宣言、source SHA256 `96385b005c999d6fb080619991f9881a2185cba98a881c9ceb16588a0d931a64`):

`AnchoredLocal.shift`、`AnchoredLocal.defect`、`AnchoredLocal.defect_shift`、`AnchoredLocal.Objects`、`AnchoredLocal.normalize`、`AnchoredLocal.denormalize`、`AnchoredLocal.objectEquiv`、`AnchoredLocal.normalize_value`、`AnchoredLocal.denormalize_value`、`AnchoredLocal.fixed_value`、`AnchoredLocal.gauge`、`AnchoredLocal.gauge_zero`、`AnchoredLocal.gauge_add`、`AnchoredLocal.addAction`、`AnchoredLocal.Groupoid`、`AnchoredLocal.equivariant`、`AnchoredLocal.equivalence`、`AnchoredLocal.functor_inverse`、`AnchoredLocal.inverse_functor`。

`AnchoredFiniteCover.lean` (22明示宣言、source SHA256 `f8549f24ed96d272d8b55b7e385ca8145f6a8b56d5a404297221b01feaf48f0c`):

`AnchoredFinite.Objects`、`AnchoredFinite.normalize`、`AnchoredFinite.denormalize`、`AnchoredFinite.objectEquiv`、`AnchoredFinite.gauge`、`AnchoredFinite.gauge_normalize`、`AnchoredFinite.gauge_local`、`AnchoredFinite.addAction`、`AnchoredFinite.vadd_eq`、`AnchoredFinite.Groupoid`、`AnchoredFinite.equivalence`、`AnchoredFinite.functor_inverse`、`AnchoredFinite.inverse_functor`、`AnchoredFinite.generatedEquivalence`、`AnchoredFinite.generated_inverse_value`、`AnchoredFinite.generated_functor_inverse`、`AnchoredFinite.generated_inverse_functor`、`AnchoredFinite.objectsInclusion`、`AnchoredFinite.inclusion_equivariant`、`AnchoredFinite.rangeFunctor`、`AnchoredFinite.generated_range`、`AnchoredFinite.generated_inverse_range`。

`AnchoredActualCover.lean` (10明示宣言、source SHA256 `55f0cd7755c938ba787e1818ba2344d19a276ad7677b672ba17a018cf5927d6f`):

`AnchoredActualCover.reference_functor_inverse`、`AnchoredActualCover.reference_inverse_functor`、`AnchoredActualCover.originalEquivalence`、`AnchoredActualCover.original_functor_inverse`、`AnchoredActualCover.original_inverse_functor`、`AnchoredActualCover.equivalence`、`AnchoredActualCover.functor_inverse`、`AnchoredActualCover.inverse_functor`、`AnchoredActualCover.forward_value`、`AnchoredActualCover.inverse_value`。

`AnchoredDisplayComparison.lean` (21明示宣言、source SHA256 `7315002ab6415bc43c5a7d14ec4bb1b85d759f35762f70a7244a162327e84346`):

`AnchoredDisplay.generatedEquivalence`、`AnchoredDisplay.sourceEquivalence`、`AnchoredDisplay.source_functor_inverse`、`AnchoredDisplay.source_inverse_functor`、`AnchoredDisplay.source_value`、`AnchoredDisplay.source_inverse_value`、`AnchoredDisplay.comparison`、`AnchoredDisplay.comparison_rec`、`AnchoredDisplay.comparison_comp`、`AnchoredDisplay.comparison_inverse`、`AnchoredDisplay.comparison_value`、`AnchoredDisplay.refinement_value`、`AnchoredDisplay.inverse_comparison`、`AnchoredDisplay.comparison_choice`、`AnchoredDisplay.source_label_value`、`AnchoredDisplay.source_inverse_label_value`、`AnchoredDisplay.comparison_label_value`、`AnchoredDisplay.refinement_label_value`、`AnchoredDisplay.source_range`、`AnchoredDisplay.source_inverse_range`、`AnchoredDisplay.comparison_range`。

`C12AnchoredRegression.lean` (26明示宣言、source SHA256 `c636b3f1b6fd4de4b024eca1aad09d1f4036f2bb54126582224e36239849595e`):

`C12AnchoredRegression.geometry`、`C12AnchoredRegression.edgeEquality`、`C12AnchoredRegression.E`、`C12AnchoredRegression.projection`、`C12AnchoredRegression.kernel_comm`、`C12AnchoredRegression.core`、`C12AnchoredRegression.reference`、`C12AnchoredRegression.projects`、`C12AnchoredRegression.relations`、`C12AnchoredRegression.tower`、`C12AnchoredRegression.other`、`C12AnchoredRegression.other_projects`、`C12AnchoredRegression.fixed`、`C12AnchoredRegression.region`、`C12AnchoredRegression.regions`、`C12AnchoredRegression.fixedEdge`、`C12AnchoredRegression.freeEdge`、`C12AnchoredRegression.shift`、`C12AnchoredRegression.shift_fixed_nonzero`、`C12AnchoredRegression.raw`、`C12AnchoredRegression.raw_valid`、`C12AnchoredRegression.rawLocal`、`C12AnchoredRegression.raw_fixed_accept`、`C12AnchoredRegression.raw_fixed_reject`、`C12AnchoredRegression.raw_shared_accept`、`C12AnchoredRegression.raw_shared_reject`。

`FiniteCoordinatePartition.lean` (新API1宣言。所有sourceの既存宣言はC10受理依存として保持、source SHA256 `6d456c045716381d407a3acbbfbda216b1bea7e4105241794f1d09e3a94e3b39`):

`FinitePartition.join_private`。

`FiniteNativeCoordinates.lean` (新API1宣言。所有sourceの既存宣言はC10受理依存として保持、source SHA256 `80c7b8164d1dbdf288926659e419855dc11f6ccfea9276ba92b81f9a6f07216d`):

`FiniteNative.private_edge_value`。

### C12 — focused実行証拠

対象16新sourceの正確なbodyと所有sourceの新API2件を対象にした単一milestone focused checkはexit0/errors0/warnings0。
266明示宣言と50生成宣言の全316を個別に公理監査し、対象集合を16新sourceの全宣言と所有sourceの新API2件へ機械突合した。
全件が標準公理のみであり、source hashが監査時と一致する。
axiom log SHA256 `2bfeca8532c0acd125d64ac19313b73bcb556acfabe8c212259dcbf7df4fc848`。
必要な単一concrete endpoint `ResearchLean.AG.RelativeRepairComposition.AnchoredDisplayComparison` のtargeted checkはexit0。

F₂のD=第1成分、F=恒等、σ(r)=(r,0)、τ(r)=(r,r)を実計算した。
同じoriginal solution ((1,1),0)の核座標は旧(0,1)から新(0,0)へ変わり、両方のrecは((1,1),0)へ戻る。
非零labelによるgauge後もsection比較の両経路が同じ全核値(0,1)を返す。
3葉の左右の括弧は全leaf値[1,0,1]を保持し、逆構成は((1,0),1)へ戻る。
full二次元basisの入替えは座標[1,0]を[0,1]へ写し、元cell値[1,0]へ復元する。
empty familyのinverseはPUnit.unitを返し、有限被覆に空のindexも許す。

C11の2頂点・4原辺・F₂全係数を用い、0と1の独立local補正が共有原edgeで異なるbinary/nested組を拒否する。
0と1のfull vertex labelは局所の作用が同じでもbinary共有label条件に反する。
同じ原型に零のsupported correctionを与えるbinary/nested入力は実際に構成できる。
これら5 predicate証拠の個別公理も全て標準公理のみ。

`C12AnchoredRegression` はF₂の全translation kernelを持つ実塔と同一coreのalternative liftを構成する。
1頂点・2原loop・空のfaces/triplesを保ち、固定原loopで実shift≠0を証明する。
`raw_valid` はraw固定値−aと実new defect方程式を直接証明する。
`raw_fixed_accept` / `raw_fixed_reject` は同じ非零anchorの受理とraw零の拒否を示す。
`raw_shared_accept` / `raw_shared_reject` は各局所raw方程式が成立する族を使い、共有原free loopの一致/不一致を判定する。
この原型はC12新述語の正負証拠であり、指定W/Fの完了へ数えない。

所有API `FinitePartition.join_private` / `FiniteNative.private_edge_value` は同じ元private値を読む。
`split_basis_private` はその公開APIを使い、所有join定義の再展開を避ける。
所有2 sourceの既存43宣言はC10受理依存であり、今回の新266明示宣言には数えない。
指定W1–W5の実アフィン例と各完了条件は後続obligationとして保持する。

regression log SHA256 `1997c9feabc5dcb9d98fe98c02bc98347fbc31adc9364ac23442d315dc1bc71d`、targeted endpoint log SHA256 `66b2f54b80b2b0daff9d2f8d06e3e92c9002738f86327855fbd90360bc63350b`。

独立import経路の確認として、`GeneratedLocalComparison` / `GeneratedFiniteAssembly` / `GeneratedSectionComparison` の各単一concrete endpointを順にtargeted checkし、いずれもexit0。`AnchoredActualCover.lean` / `StrictBinaryAssembly.lean` の各単一source focused checkもexit0。targeted logには既存依存のreplayed warning（本体Coreのsimpa、受理済みRelativeCoverComplexの旧API）が含まれる。C12新sourceにwarningはない。各log SHA256:

- `c12-generated-local-build.log`: `982561cc0f8ec420b2da3690cbe4d5414ced1ecb1ce3608122ff29d2f4e87fa7`
- `c12-generated-finite-build.log`: `74ea36bd1fc1fcc4b74d312653ee3d5ebd50300737fe233900ecef905dc5e944`
- `c12-generated-section-build.log`: `fb15f7f8dd09f684e8e3f07f28d059e280ddf39a4b05b4698d4e481557f5da5a`
- `c12-anchored-actual-focused.log`: `36e94019e810abf11794cb5dfd2a7afcf382a511b007848a73cede1ffd1cb00d`
- `c12-strict-binary-focused.log`: `4c4da063b55af963778a045bd5d7de8824a757d6d47c4c1f92fca8f0735757c6`

単一target `FullBasisComparison` の所有APIを含むproduction確認はexit0。
単一source `C12AnchoredRegression.lean` のfocused確認はexit0/errors0/warnings0、26宣言のstandard axiom gateが通る。
この2 source所有APIは現在production bodyを検査し、個別公理結果を同じmilestone監査へ収載する。
- `c12r1-private-api-build.log` SHA256 `941ad0c9fcfbad64e82ce30f21d485e160a2d612ea9565a6e89df0ddca2dda49`。
- `c12r1-raw-focused.log` SHA256 `f81812c9c6bb7b7f32b994e9128e757315d1df441a0cc4dfdf63373c1c8aef91`。
### Cycle 13 selection — 原always商と全変更範囲の双対分類

```yaml
ledger_type: target_cycle_result
goal: G-130-aat-relative-repair-composition
cycle: 13
goal_blob_sha: 8da0fb4eb75d1cb5c37a9d4ddf5e03c18c0bb8a2
base_oid: 16d982ddc96084afbdfddfc21d63d58040d2c2d2
tracking_issue: 5132
report_path: research/reports/G-130-aat-relative-repair-composition.md
selection:
  proof_state_ref: "Issue #5132 C12受理5927913126 / PR5148 root acceptance5927896427 / report Cycle12"
  proof_dag_predecessors: ["C1–4 原実修復/全補正/全label/相対障害", "C10 原全0–3 full有限座標/一回generator/全kernel復元", "C11 strict finite全S public復元", "C12 全表示変更/同じactual復元比較"]
  milestone: "GOAL Dを同じ原大域微分から構成したalways D/coker O/o/全元candidate B_eに適用し、全Sの実修復/public条件/membership/双対hittingと極小範囲、失敗証拠/成功全復元、原相対障害への商対応を閉じる"
  proof_obligations:
    - "一般の名前付き全columnについてR_SとE_lambdaを独立定義し、range annihilator/双対分離からmembership iff全dual hittingを証明。包含極小性、o零唯一empty、全候補不能のempty dual supportを同一定義で導く"
    - "同じ原全kernel/module/full基底/固定P/元候補分割からglobal always D、q、o=q(-delta)、元candidate full核column E_e/B_eを生成。元微分はDx+sumE_e y_eであることを全原値で証明"
    - "全Sの独立actual supported repairの非空とo in R_Sを全方向で接続し、C11の独立全finite public relationと同じ判定へ対応させる。生成dataはS/rhs非依存"
    - "失敗Sには具体的有限列挙からquotient dual排除証拠、成功Sには同じ原辺への全補正/kernel自由度/full labelsの復元を構成。純choice存在でfinite constructionを代替しない"
    - "原global d1 range=always range+全candidate rangeを証明しO/R_allを同じCP2/range原d1へ全同型で運ぶ。元d2の線形性/zero compositionと誘導d2、同じoと原[-delta]/relative obstructionの値対応を構成"
    - "一般定理の各方向を原入力へ適用し、空候補/空族/o零/不能/非零dualの正負例、対象全宣言focused/個別公理/scans/登録/独立PR監査を固定"
  exit_criteria:
    - "原K/T/p/q/core/lifts/full kernels/全0–3 cellと元candidate名/全S/full labelsを保持"
    - "exactness/dual completeness/repair/range separation/quotient iso/復元法則を結論certificateとして受け取らず原入力または標準field APIから放電"
    - "独立actual repairsとCの同じ一回local public生成に接続、全成功自由度/射と失敗dualを構成"
    - "極小分類の両方向・o零/全候補不能・原d2と同じ障害classまで全向き/値を証明"
    - "対象全decl focused/axioms/scans、登録/台帳と標準4独立PR gate/root受理"
  selection_reason: "Cの一回生成/全S復元/表示比較が受理済み。Dの商は同じ原座標微分の次nodeであり、Eの記号的再利用と指定Wの全範囲分類へ直接接続する"
  expected_result_type: proof-obligation-discharged
  lean_targets: [NamedDualRanges, OriginalCandidateColumns, OriginalRangeClassification, FiniteDualWitness, OriginalRangeObstruction]
  risks: ["candidate名をeffective subsetへ付替えない", "actual/public↔rangeの橋を一般補題名だけで済ませない", "finite dual証拠をchoiceへ縮めない", "成功の全kernel/full labelsを存在一件へ縮めない", "CP2 quotientとnative H2を混同しない"]
  unchecked: ["C13全実装/接続/検証/独立監査はこれから構成", "E/F/W1–W5/別全GOAL completionは後続"]
```

実装前に固定したCycle13の全終了条件。分割する場合はこの元条件と具体的理由・未完obligationを保持する。D受理も全GOAL completionとは呼ばない。

### C13 — 構成と受理spine

GOAL Dの原always商・全候補範囲・双対支持・極小分類を、同じ原実修復とCの公開関係へ接続する。
`OriginalColumns.alwaysSpace` は相対原辺の全係数族のうち、全候補で零のものそのもの。
`D` はこの源の元d1制限であり、各 `column e` は同じ元候補名の全target kernelからの元d1列。
`decompose` / `differential_named_sum` は元の全辺値でalways成分と全候補成分の分解を証明する。
商Oとo=q(-delta)はこの同じDと実defectから構成する。

`NamedDual.ranges` は全選択列の像の和、`support` は全列との双対合成が非零となる名前の集合。
`annihilates_iff` とfieldの `Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff` が全Sのmembership iff Hitsを証明する。
`minimal_iff` は両向きの包含極小性、`minimal_zero_iff` は零で空集合だけ、`impossible_empty_support` / `no_transversal_of_empty_support` は全候補でも不能な場合を扱う。

`OriginalRanges.objects_nonempty_iff_equation` は独立 `SupportedEquation.Objects` の禁止候補零条件と元微分方程式から、分解・選択・復元を構成する。
`OriginalRangeClassification` が同じ実塔の独立 `SupportedRepair` へ全Sのrange/dual/minimal判定を運ぶ。
`OriginalPublicRanges.public_nonempty_iff_range` はC11の独立public relationと同じ障害判定を接続する。
`publicKernelEquiv` は任意の成功public入力と全local ker Dの積から全actual修復を相互に対応させる。
`restore_edge_value` は同じ原辺の全kernel値を保つ。C11の `GeneratedCoverRestoration.equivalence`、両functor逆、full label値保存を受理依存として使い、成功一件だけに全自由度・再同定を縮めない。

`FiniteDual.find` は完全な有限field/face列挙から全行ベクトルを生成し、原always基底の全列・許可候補の全kernel基底列・同じrhsへの非零値を直接検査する。
`OriginalFiniteDual.alwaysMatrixMap` は元全CP1座標をalways maskへ戻して同じDを評価する。`mask_always` が全always入力を取り落とさないことを証明する。
`candidateMatrixMap` は各元候補の全kernel basisの逆から元columnを評価する。
`quotientDual` は実際にfindが返した行を原全face座標に引き戻して元Oへ降ろす。
`valid_excludes_range` / `find_isSome_iff` は検査のsoundness/completenessを両向きに証明する。
field双対の存在は完全性証明だけに使い、出力functionalは有限find行から構成する。

成功側 `OriginalFiniteCorrection.find` は元全CP1の有限座標族を列挙し、同じ元face方程式と全禁止候補値を独立に検査する。
`restoreFound` はfind=someという計算結果から全方程式・零条件を生成する。
`find_isSome_iff`、実塔の `OriginalFiniteRepair.success_decision_iff` / `failure_decision_iff` により、いずれの判定も修復・分離証拠を入力に取らず有限探索の結果と独立actual述語を対応させる。
`computedObject` / `computedRepair` / `computedDual` の成功・失敗仮定はfind.getの全域性証明だけに使う。探索はこれらの証明項からanswerを取り出さない。
有限リストは生成された完全入力列挙からのList.piとList.find?で停止し、空index族でも同じ構成を使う。
成功後の全kernel自由度・全射は上記publicKernelEquivとC11のfull native equivalenceで保持する。

`OriginalRangeQuotient.range_differential` は元d1の全像がalways像と全候補像の和であることを、元cochainの分解から証明する。
`CokernelAllColumns.secondQuotient` と同じ元像の等式が O/R_all ≃ CP2/im d1 を構成し、`equivalence_value` は同じ全face代表を保持する。
`FiniteCoefficients.differential2` は元の全typed whiskering/pastingに対するスカラー法則から線形化し、元d2d1=0により `inducedD2` を構成する。
`OriginalRangeCohomology.equivalence` / `OriginalNativeRangeCohomology.equivalence` は誘導d2の核と同じ原Kのfull H2を相互に同定する。
`OriginalRangeObstruction.obstruction_H2` は同じ o の像を元actual [-delta] に運ぶ。
実3-cellの authored syzygy から作った元obstructionCocycleを使用し、CP2/im d1全体をH2と呼ばない。

全宣言のprefixは `AAT.AG.RelativeRepairComposition.`。以下の22 sourceと明示宣言を登録する。各sourceの生成宣言も個別公理監査の対象。

`NamedDualRanges.lean` (11明示宣言、source SHA256 `6f3a2bbadcd3fb3598583f0f5bbe670876d3aec782263f3e06e710efa9c8ac4d`):

`NamedDual.ranges`、`NamedDual.support`、`NamedDual.range_le`、`NamedDual.annihilates_iff`、`NamedDual.Hits`、`NamedDual.mem_ranges_iff_hits`、`NamedDual.failure_witness`、`NamedDual.minimal_iff`、`NamedDual.minimal_zero_iff`、`NamedDual.impossible_empty_support`、`NamedDual.no_transversal_of_empty_support`。

`NamedColumnSum.lean` (12明示宣言、source SHA256 `1a0dc4ee811b254584990fd65f4a12640e92679f42bebbae5da49cbfbd891ae0`):

`NamedDual.sumSelected`、`NamedDual.sumSelected_apply`、`NamedDual.sumSelected_single`、`NamedDual.range_sumSelected`、`NamedDual.mem_ranges_iff_sum`、`NamedDual.extendSelected`、`NamedDual.extend_value`、`NamedDual.extend_zero`、`NamedDual.extend_single`、`NamedDual.extend_read`、`NamedDual.sum_extend`、`NamedDual.map_sumSelected`。

`OriginalCandidateColumns.lean` (17明示宣言、source SHA256 `bdbae82998a588405f948b6e9d15c05092d9485316c12e2871ae1a60aae1d3f3`):

`OriginalColumns.allEdgesDecidable`、`OriginalColumns.allVerticesDecidable`、`OriginalColumns.CandidateValues`、`OriginalColumns.alwaysSpace`、`OriginalColumns.candidateRead`、`OriginalColumns.candidateCochain`、`OriginalColumns.candidate_value`、`OriginalColumns.noncandidate_value`、`OriginalColumns.read_candidate`、`OriginalColumns.alwaysRead`、`OriginalColumns.decompose`、`OriginalColumns.D`、`OriginalColumns.candidateMap`、`OriginalColumns.differential_decompose`、`OriginalColumns.column`、`OriginalColumns.sum_columns`、`OriginalColumns.differential_named_sum`。

`FiniteCoefficientSecondDifferential.lean` (7明示宣言、source SHA256 `361c7ede1e280295e6172556494272545418dcd0fbc6cf3a54d3622d845527fc`):

`FiniteCoefficients.faceCorrection_smul`、`FiniteCoefficients.pastingCorrection_smul`、`FiniteCoefficients.d2_smul`、`FiniteCoefficients.restrict_extend2`、`FiniteCoefficients.differential2`、`FiniteCoefficients.differential2_eq`、`FiniteCoefficients.differential2_differential1`。

`CokernelNamedRanges.lean` (4明示宣言、source SHA256 `180324960e7ef25e94496bb9a9179682df2f81da63730c34e1763fa4a085008d`):

`CokernelNamed.column`、`CokernelNamed.quotient_sum`、`CokernelNamed.mem_iff_equation`、`CokernelNamed.equation_iff_hits`。

`OriginalRangeEquations.lean` (13明示宣言、source SHA256 `71b0eef9873529b95f62c3a652ce6efe89e711f3992a919991797c2c94db8b1d`):

`OriginalRanges.allEdgesDecidable`、`OriginalRanges.allVerticesDecidable`、`OriginalRanges.ObstructionSpace`、`OriginalRanges.column`、`OriginalRanges.allowed`、`OriginalRanges.allowed_iff`、`OriginalRanges.selectedCorrection`、`OriginalRanges.selected_differential`、`OriginalRanges.selected_zero`、`OriginalRanges.restore`、`OriginalRanges.objects_nonempty_iff_equation`、`OriginalRanges.objects_nonempty_iff_range`、`OriginalRanges.objects_nonempty_iff_hits`。

`OriginalRangeClassification.lean` (9明示宣言、source SHA256 `1dad72e637d30de7f65cd60210cbb866aa3b12d0dd36eca19f773526f0930725`):

`OriginalRangeClassification.obstruction`、`OriginalRangeClassification.repair_nonempty_iff_range`、`OriginalRangeClassification.repair_nonempty_iff_hits`、`OriginalRangeClassification.minimal_repair_iff`、`OriginalRangeClassification.minimal_repair_iff_range`、`OriginalRangeClassification.minimal_zero_iff`、`OriginalRangeClassification.failed_repair_dual`、`OriginalRangeClassification.impossible_dual_empty`、`OriginalRangeClassification.impossible_no_transversal`。

`FiniteFunctionEnumeration.lean` (1明示宣言、source SHA256 `ac5790b80a7ebc59ca39a9c460e4ebbd502457f28a81ce7056ec7485288ca312`):

`FiniteElimination.Enumeration.pi`。

`FiniteDualWitness.lean` (13明示宣言、source SHA256 `725f47ae7358224657ec438061de317252e623f54be0a3e5bad8af0b1982aeb1`):

`FiniteDual.row`、`FiniteDual.annihilates_iff`、`FiniteDual.Valid`、`FiniteDual.validDecidable`、`FiniteDual.rows`、`FiniteDual.find`、`FiniteDual.valid_of_failure`、`FiniteDual.find_isSome`、`FiniteDual.rowWitness`、`FiniteDual.quotientDual`、`FiniteDual.quotientDual_value`、`FiniteDual.quotientDual_spec`、`FiniteDual.computedDual`。

`OriginalPublicRanges.lean` (3明示宣言、source SHA256 `d34d9cc95982374efc4e3d2349f0d82d0806b14183eb26ce5293a828df18c86e`):

`OriginalPublicRanges.public_nonempty_iff_range`、`OriginalPublicRanges.publicKernelEquiv`、`OriginalPublicRanges.restore_edge_value`。

`CokernelAllColumns.lean` (5明示宣言、source SHA256 `8f9b8e124a3243be2f95ac79a71487feca5a618260caa50a9c6d19e99f5a5b7a`):

`CokernelNamed.fullMap`、`CokernelNamed.sum_univ`、`CokernelNamed.all_ranges_eq`、`CokernelNamed.secondQuotient`、`CokernelNamed.secondQuotient_value`。

`OriginalRangeQuotient.lean` (10明示宣言、source SHA256 `32dea7c5fe1d088d7176cfe0d3e5956db82007cd44700d6071b7d8c2e23e6183`):

`OriginalRangeQuotient.allEdgesDecidable`、`OriginalRangeQuotient.allVerticesDecidable`、`OriginalRangeQuotient.allFacesDecidable`、`OriginalRangeQuotient.full_candidates_eq`、`OriginalRangeQuotient.range_differential`、`OriginalRangeQuotient.equivalence`、`OriginalRangeQuotient.equivalence_value`、`OriginalRangeQuotient.inducedD2`、`OriginalRangeQuotient.inducedD2_value`、`OriginalRangeQuotient.obstruction_image_cycle`。

`OriginalRangeCohomology.lean` (11明示宣言、source SHA256 `31b417cf56593c47896f39ccca10bc3af35225d9e5ef30fb3349a8df2aceb53d`):

`OriginalRangeCohomology.allEdgesDecidable`、`OriginalRangeCohomology.allVerticesDecidable`、`OriginalRangeCohomology.allFacesDecidable`、`OriginalRangeCohomology.cycleMap`、`OriginalRangeCohomology.cycleMap_boundary`、`OriginalRangeCohomology.classMap`、`OriginalRangeCohomology.classMap_value`、`OriginalRangeCohomology.classMap_injective`、`OriginalRangeCohomology.classMap_surjective`、`OriginalRangeCohomology.equivalence`、`OriginalRangeCohomology.equivalence_value`。

`OriginalFiniteDual.lean` (18明示宣言、source SHA256 `3e839e668ff393cbbaaf53b055f51bd809254582079678e23516fec5f766a2b8`):

`OriginalFiniteDual.allEdgesDecidable`、`OriginalFiniteDual.allVerticesDecidable`、`OriginalFiniteDual.allFacesDecidable`、`OriginalFiniteDual.alwaysMatrixMap`、`OriginalFiniteDual.candidateMatrixMap`、`OriginalFiniteDual.mask_always`、`OriginalFiniteDual.always_value`、`OriginalFiniteDual.candidate_value`、`OriginalFiniteDual.find`、`OriginalFiniteDual.valid_of_failure`、`OriginalFiniteDual.find_isSome`、`OriginalFiniteDual.rowWitness`、`OriginalFiniteDual.quotientDual`、`OriginalFiniteDual.quotientDual_value`、`OriginalFiniteDual.quotientDual_spec`、`OriginalFiniteDual.valid_excludes_range`、`OriginalFiniteDual.find_isSome_iff`、`OriginalFiniteDual.computedDual`。

`OriginalNativeRangeCohomology.lean` (9明示宣言、source SHA256 `de33d5e1360dbd22115db643f56e46352dbd94a7b1e510e16cb960b3e12c5f25`):

`OriginalNativeRangeCohomology.allEdgesDecidable`、`OriginalNativeRangeCohomology.allVerticesDecidable`、`OriginalNativeRangeCohomology.allFacesDecidable`、`OriginalNativeRangeCohomology.classMap`、`OriginalNativeRangeCohomology.familyCycle`、`OriginalNativeRangeCohomology.familyCycle_eq`、`OriginalNativeRangeCohomology.classMap_value`、`OriginalNativeRangeCohomology.classMap_bijective`、`OriginalNativeRangeCohomology.equivalence`。

`OriginalRangeObstruction.lean` (5明示宣言、source SHA256 `f9110a93e200058c5d151ad233db922e6e3f3401234da8b0a7a1cee3e0372f5a`):

`OriginalRangeObstruction.allEdgesDecidable`、`OriginalRangeObstruction.allVerticesDecidable`、`OriginalRangeObstruction.allFacesDecidable`、`OriginalRangeObstruction.obstruction_H2`、`OriginalRangeObstruction.obstruction_image_cycle`。

`OriginalFiniteCorrection.lean` (14明示宣言、source SHA256 `565e1104aba802b1f21c66d89ae24027dfe80c5526aad6fc18efd4c1f392ae98`):

`OriginalFiniteCorrection.allEdgesDecidable`、`OriginalFiniteCorrection.allVerticesDecidable`、`OriginalFiniteCorrection.allFacesDecidable`、`OriginalFiniteCorrection.Valid`、`OriginalFiniteCorrection.validDecidable`、`OriginalFiniteCorrection.coordinates`、`OriginalFiniteCorrection.find`、`OriginalFiniteCorrection.valid_of_object`、`OriginalFiniteCorrection.restore`、`OriginalFiniteCorrection.find_isSome`、`OriginalFiniteCorrection.restoreFound`、`OriginalFiniteCorrection.find_isSome_iff`、`OriginalFiniteCorrection.computedObject`、`OriginalFiniteCorrection.restore_value`。

`OriginalFiniteRepair.lean` (5明示宣言、source SHA256 `04ce511d62257c987359199f5195f991a5393381b4873218cea4fa9139a95762`):

`OriginalFiniteRepair.success_decision_iff`、`OriginalFiniteRepair.failure_decision_iff`、`OriginalFiniteRepair.restoreFound`、`OriginalFiniteRepair.computedDual`、`OriginalFiniteRepair.computedRepair`。

`C13RangeInput.lean` (19明示宣言、source SHA256 `b51c24eda0dbf6600cf124db787c07a6c81c087d6d99bf8572b5e6b13afa6f79`):

`C13RangeInput.geometry`、`C13RangeInput.edgeEquality`、`C13RangeInput.E`、`C13RangeInput.projection`、`C13RangeInput.kernel_comm`、`C13RangeInput.core`、`C13RangeInput.reference`、`C13RangeInput.projects`、`C13RangeInput.relations`、`C13RangeInput.tower`、`C13RangeInput.fullKernel`、`C13RangeInput.coefficient`、`C13RangeInput.originalModule`、`C13RangeInput.edge_identity`、`C13RangeInput.linear`、`C13RangeInput.fixed`、`C13RangeInput.candidates`、`C13RangeInput.outside`、`C13RangeInput.fixed_coherent`。

`C13FiniteDualRegression.lean` (22明示宣言、source SHA256 `6cb9b3bbd4d97151558633ad5c16d3144d9a4e5bb50b4725e4b286616784d140`):

`C13FiniteDualRegression.k`、`C13FiniteDualRegression.fieldValues`、`C13FiniteDualRegression.faceValues`、`C13FiniteDualRegression.D`、`C13FiniteDualRegression.C`、`C13FiniteDualRegression.rhs`、`C13FiniteDualRegression.forbidden`、`C13FiniteDualRegression.forbiddenDecidable`、`C13FiniteDualRegression.valid_nonzero`、`C13FiniteDualRegression.invalid_zero`、`C13FiniteDualRegression.no_failure_all`、`C13FiniteDualRegression.find_failed`、`C13FiniteDualRegression.find_success`、`C13FiniteDualRegression.find_zero_rhs`、`C13FiniteDualRegression.noCandidates`、`C13FiniteDualRegression.find_empty_candidates`、`C13FiniteDualRegression.dual_nonzero`、`C13FiniteDualRegression.dual_allowed_zero`、`C13FiniteDualRegression.zero_minimal_iff`、`C13FiniteDualRegression.emptyDual`、`C13FiniteDualRegression.empty_dual_support`、`C13FiniteDualRegression.empty_no_transversal`。

`C13ActualRangeRegression.lean` (26明示宣言、source SHA256 `27f9f96da9a7da9e2fb70e50b45de16a7fc6b63c5248cc44404f28165663a49b`):

`C13ActualRangeRegression.k`、`C13ActualRangeRegression.M`、`C13ActualRangeRegression.originalEdgeEquality`、`C13ActualRangeRegression.candidatesDecidable`、`C13ActualRangeRegression.fixedEdgesDecidable`、`C13ActualRangeRegression.fixedFacesDecidable`、`C13ActualRangeRegression.linearCoefficient`、`C13ActualRangeRegression.scalarCoordinate`、`C13ActualRangeRegression.basis`、`C13ActualRangeRegression.groupSolution`、`C13ActualRangeRegression.solution`、`C13ActualRangeRegression.Repair`、`C13ActualRangeRegression.allRepair`、`C13ActualRangeRegression.empty_no_repair`、`C13ActualRangeRegression.obstruction_nonzero`、`C13ActualRangeRegression.all_range_member`、`C13ActualRangeRegression.empty_range_reject`、`C13ActualRangeRegression.all_hits`、`C13ActualRangeRegression.empty_hits_reject`、`C13ActualRangeRegression.allFixed`、`C13ActualRangeRegression.noCandidates`、`C13ActualRangeRegression.noCandidatesDecidable`、`C13ActualRangeRegression.noCandidates_outside`、`C13ActualRangeRegression.allFixed_coherent`、`C13ActualRangeRegression.allFixed_no_repair`、`C13ActualRangeRegression.impossible_empty_support`。

`C13ActualComputedWitness.lean` (7明示宣言、source SHA256 `7b183280ab602e2fd9cba721f96736428263b5731769fb5c0bbfc123c061c64f`):

`C13ActualComputedWitness.originalFaceEquality`、`C13ActualComputedWitness.edgeValues`、`C13ActualComputedWitness.faceValues`、`C13ActualComputedWitness.failedDual`、`C13ActualComputedWitness.failed_dual_nonzero`、`C13ActualComputedWitness.successfulRepair`、`C13ActualComputedWitness.successful_fixed`。

### C13 — premise / proof-use / scope

| material premise | 出所・放電 | proof-use |
| --- | --- | --- |
| 元K/T/p/q/core/lifts/全kernel/輸送 | Aの原入力、C1–4受理API | 実delta、原支持方程式、actual往復 |
| P閉包・候補がP外 | 原入力、C13RangeInput.outsideでconcrete放電 | candidateCochainのP零、全support往復 |
| field/full有限kernel bases/完全列挙 | Cの許された原入力。concreteはF2/fullKernel/coefficient/basisと全原edge/faceリスト | 全列線形性、双対分離、全行/全補正の有限生成 |
| 双対分離・完全性 | field dual annihilatorの標準theorem。有限出力は完全行列挙のfind | 全S iff/hittingとfind完全性 |
| 成功・失敗判定 | 無条件findと独立元述語の両向きiff | raw find結果から全原補正/元O双対を構成 |
| 原d1の全像分解・商同型 | 全元cochainのalways/candidate分解と第三同型定理 | O/R_all、代表値、原誘導d2 |
| 元d2線形性・zero composition | full authored typed pastingのscalar帰納、受理原d2d1 | H2核へのfull同値 |
| relative actual cocycle | Aの原authored syzygy + Pの実固定整合 | 同じ[-delta]の商/H2対応 |
| Cの公開関係・full自由度・full gauge | C11のinput-generated local dataとnative all-S両逆 | public非空判定/全local kerの復元/元label保存 |

結論のexactness、repair、分離dual、比較同型、復元法則をstructureの入力fieldへ追加しない。
有限生成のS/rhs非依存データは全kernel bases/元列と行・全補正の列挙。S/rhsは検査述語と復元のaffine項にだけ入る。
C13はGOAL Dの到達点候補であり、E/F/W1–W5および全GOALの別completion gateを後続とする。

### C13 — 回帰scenarioと検証

`C13RangeInput` はF2の全translation kernelを持つ実塔、二つの元loop、一つの非零defect face、空のtriplesを構成する。
false loopの基準translationは1、true loopは0。false loopを物理固定し、true loopを候補とする。
`C13ActualRangeRegression.empty_no_repair` は独立actual face方程式と両fixed実射から1=0を導き拒否する。
`allRepair` は同じ元loop双方をtranslation1とするactual修復を直接構成する。
その同じ入力で `obstruction_nonzero`、rangeの正負、全dual hittingの正負を検査する。
原全native kernelのModuleは完全なkernel equivalenceでF2から輸送し、`edge_identity` / `linear` は原translationの可換性から導く。
`basis` はその全kernelの一次元basisであり、`C13ActualComputedWitness` が同じ非零actual入力に有限failedDualとsuccessfulRepairを適用する。
`successful_fixed` は有限復元が同じ元fixed実射を保持することを検査する。

`C13FiniteDualRegression` は全二元fieldリストと一面座標、空always列、二つの元candidate列(identity/zero)、非零rhsを直接評価する。
零columnだけの許可でfindは行1を返し、identityを含む許可と零rhsではnone。
行0は同じ失敗入力を排除できず、全候補を許可した入力は全行のfailure testを拒否する。
返したdualは同じquotient rhsで非零、全許可columnで零。空候補族でも非零rhsに行1を返し、empty supportにより全横断集合を拒否する。
zero obstructionの極小範囲がemptyだけである同じ述語を適用する。
これらはC13の述語・有限生成の回帰証拠であり、指定Wの実アフィン全要求は後続に保持する。

`allFixed_no_repair` は同じ原非零faceを持つ実塔で全原loopを固定し、空候補族の全候補許可でも不能であることを直接示す。
`impossible_empty_support` はこの独立actual不能入力を一般の空支持定理へ適用する。

単一の選定milestone exact-source focused検証はexit0/errors0/warnings0。
22 sourceの全241明示宣言と5生成APIの全246を個別に `#print axioms` し、対象明示集合と機械突合して欠落0。全件が標準公理のみ。
axiom log SHA256 `c619fb67a7e822f228d7fa2c39344da21198539d0e65d77b9304c4706fb4b8e8`。
個々の登録sourceも直接必要な順に単一file focusedで確認した。Research全体/aggregate/全fileloopは実行していない。
全22登録行はそれぞれ一意でsource hashが監査時と一致する。Lean placeholder/hidden-BiDi/privacy scanとdiff checkはclean。
productionの単一endpoint `C13ActualComputedWitness` のfocused確認を行い、実塔の有限構成を検査する。
選定milestoneのscratch検証は同じsource bodyを再現し、型class探索の上限100000を使用する。productionの一般数学宣言の条件・証明は変更しない。

```yaml
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta:
    - "全named ranges/dual支持を独立定義し、field dual annihilatorから全S iff、極小両向き、零empty唯一、全候補不能empty支持を構成"
    - "原always source/full candidate target kernelからD/q/o/B_eと全元cochainの分解、原微分Dx+sumEを構成"
    - "全Sの独立actual修復と原支持方程式、原商membership/dual hitting、C11独立public関係を同じ全原値で接続"
    - "完全有限行/全補正列挙のfindから、失敗dualと成功full原補正を構成。無条件findのsoundness/completenessを独立actual述語へ全方向で接続。全成功自由度/full labelsは同じC11全復元で保持"
    - "原全d1像分解と第三同型からO/R_all≃CP2/im d1、原typed d2線形化/誘導、原K full H2≃kernelと同じoの[-delta]対応を構成"
    - "原実塔の非零actual修復/不能/range/hitting、all-fixed空候補不能、有限行正負/empty/零/全候補成功を検査。全22source/241明示+5生成APIの個別標準公理、登録/機械scanを確認"
  exit_criteria_status:
    - "元K/T/p/q/core/reference/full kernel/full0–3/candidate名/allS/full labels: 原differentialと支持群、全値逆、C11全native functor受理依存を保持"
    - "結論certificate不使用: 分解・双対完全性・同型・復元の法則はinputとfield標準APIから構成。findは修復/dualを入力に取らず、返した計算結果からtest法則を生成"
    - "C/全成功/不能: publicKernelEquivは全local kerの全積、full gaugesはC11の同じlabel群。有限findは正確な独立actual存在/不能と同値"
    - "極小/零/不能/原障害: 全方向のMinimal/Hits、空支持、原d2核のH2同値、同じ[-actual defect]代表の値対応"
    - "検証/登録/台帳: 全22 exact bodies focused/246全公理/正負原入力/22登録/scans。標準独立4本PR gateとroot受理は固定PR headの監査コメントへ記録"
  split_reason: none
  completion_candidate: no
  lean_artifacts: [NamedDualRanges, NamedColumnSum, OriginalCandidateColumns, OriginalRangeEquations, OriginalRangeClassification, FiniteDualWitness, OriginalFiniteDual, OriginalFiniteCorrection, OriginalFiniteRepair, OriginalPublicRanges, CokernelAllColumns, OriginalRangeQuotient, OriginalRangeCohomology, OriginalNativeRangeCohomology, OriginalRangeObstruction, C13RangeInput, C13ActualRangeRegression, C13FiniteDualRegression, C13ActualComputedWitness]
  claim_mapping:
    source_labels: ["GOAL D全文", "C11の同じ生成public関係/full native復元"]
    theorem_names: ["NamedDual.mem_ranges_iff_hits", "OriginalColumns.differential_named_sum", "OriginalRangeClassification.minimal_repair_iff", "OriginalPublicRanges.public_nonempty_iff_range", "OriginalFiniteRepair.success_decision_iff", "OriginalFiniteRepair.failure_decision_iff", "OriginalRangeObstruction.obstruction_H2"]
    undischarged_assumptions: []
    acceptance_point: "固定C13選定の原always商/全S双対分類/有限出力/原障害対応の到達点候補。独立PR監査とroot受理は固定headのコメントで行う"
    port_status: unported
  remaining_goal_obligations: ["E記号的生成/値更新/実一点試験環境/全typed内部分割と全復元", "F任意有限体の全実アフィン塔・全核・中央化・輸送・原始仮定放電", "W1–W5の全指定実アフィン構成と各対応・決定", "別の全GOAL completion packetと独立4本最終監査"]
audits:
  premise_delta:
    discharged: ["全always/candidate像分解は元cochain maskの両向きから生成", "全S双対完全性はfield標準dual annihilatorから証明", "有限test/出力は完全原field/coordinate列挙から構成", "原誘導d2/同じH2代表は元typed微分とaccepted原complex比較から構成", "actual非零正負とall-fixed空候補不能は原実group値から直接証明"]
    remaining: ["上記remaining_goal_obligations"]
  certificate_provenance:
    discharged: ["find入力は原有限列挙/full basis/実微分/rhs/Sのみ", "出力rowはList.find?結果、原Odualはrow引戻し/liftQ", "成功find=someから全方程式/禁止零を生成して原actual repairへ戻す", "全success fiberと全labelsは同じC11 input-generated public復元", "原H2同型は代表を保持したcycles/boundaries quotient比較"]
    unresolved: []
  proof_use:
    used: ["P閉包とoutside→原full candidate cochain", "元分解→全支持方程式/同じDの商と全像", "full basis逆と全列評価→有限dualのsoundness/completeness", "完全列挙→有限原補正のsoundness/completeness", "元typed scalar法則/zero composition→誘導d2/H2核", "原authored syzygy/P固定→actual obstructionCocycleと[-delta]値", "C11全local kernel/full native inverse→全success freedom/full arrow保持"]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: ["単一選定22 exact-source bodies focused exit0/errors0/warnings0", "241明示+5生成API=246全個別公理標準のみ/集合欠落0", "axiom log SHA256 c619fb67a7e822f228d7fa2c39344da21198539d0e65d77b9304c4706fb4b8e8", "原実F2非零face正負/全fixed空候補不能、有限行正負/empty/零/全候補成功", "22一意module登録/placeholder/Unicode/privacy/diff確認"]
  blocking_findings: []
  next_obligation: "C13固定headの標準review-pr/math-lean-reviewとroot受理を経て、Eの同じ原generatorの記号的rhs更新へ進む"
```

### Cycle 14 selection — 全アフィン実操作から元辺を保つ実修復と有限座標へ

```yaml
ledger_type: target_cycle_result
goal: G-130-aat-relative-repair-composition
cycle: 14
goal_blob_sha: 8da0fb4eb75d1cb5c37a9d4ddf5e03c18c0bb8a2
base_oid: 8fbeaa309abbc51764c6605980d99b1d975036ce
tracking_issue: 5132
report_path: research/reports/G-130-aat-relative-repair-composition.md
selection:
  proof_state_ref: "Issue #5132 C13受理5929767836 / PR5149 root acceptance5929751165 / report Cycle13"
  proof_dag_predecessors: ["C1–5 原実塔/独立supported repair/full gauge/元部分表示制限", "C10–12 全finite座標/一回local生成/strict全S復元/表示比較", "C13 原全candidate範囲/dual分類/finite修復と障害"]
  milestone: "GOAL Fの任意有限体kとA=k^dのnative全Aff→GL→1を原始実操作から構成し、任意の元辺と基準辺/指定translation比較/実3-cell整合を保持したAの入力、独立実アフィン修復・全射との両方向、A–Dの同じ原計算と有限座標への接続を閉じる"
  proof_obligations:
    - "native AffineEquivの全可逆アフィン操作とLinearEquiv射影、全実核≃translations A、全射影の全射性、全核を中央化する比較 iff translationを構成。proper subgroup/選択済みactionを入力にしない"
    - "任意の元実アフィン辺L_eと基準辺R_eを保持し、原lift=R_e L_e^-1/core射影からOriginalTowerPresentationを生成。strong/lower strong/full核可換/核輸送全同型/指定translation比較中央化を実群射から放電。全原0–3 geometryとtyped paths/whiskering/pastingsを保持"
    - "実合成から原path値、核輸送=M_e、defectとd0/d1/d2座標、指定実3-cell比較からauthored syzygyを導く。core alignmentだけを許す入力と実3-cell条件を区別し、一般結論相当のcertificateへ置換しない"
    - "独立に定義した原実アフィン修復と全translation vertex gaugesを、元塔のsupported objects/full arrowsへ相互に運ぶ。全S/元固定条件/候補名/元実辺値/部分表示制限を保つ両逆関手と値法則を構成"
    - "A–Dの同じ原入力/相対障害/strict finite public全復元/range-dual分類へ一般接続を固定。全kernelの標準k^d基底と有限実写像評価・合成からCのcoordinate入力/微分/defectを生成する手順を構成"
    - "非恒等linear輸送、任意の非恒等元辺と別の基準辺、translation比較、全核の正負中央化、独立actual正負修復のconcrete回帰を一般構成へ適用し、対象全decl focused/個別公理/scans/登録/標準PR gateを固定"
  exit_criteria:
    - "任意有限体/任意d（零次元を含む）の全native affine group・実射影全核を保ち、全射/全核比較/中央化の全方向を証明"
    - "元辺恒等の特殊inputに縮めず同じL/R/core/comparator/元全typed0–3を保持、Aの条件と実核輸送/defect/全微分を原始操作から生成"
    - "独立actual affine objects/full gaugesとnative supported repairに全Sで両逆、元値/固定/候補/制限の保持、同じ受理A–Dへの接続"
    - "全標準基底と有限field/cell入力から実評価によるcoordinate生成、非自明な正負回帰と全宣言/axioms/登録/scan整合"
    - "root実装の全終了条件を満たしてからPRを固定し、新規独立4lane標準review-pr→math-lean-review、root受理とCI"
  selection_reason: "Dを受理済み。Eの実singleton環境とW1–W5は全アフィンprimitive入力を必要とするため、全F実現とA–D接続を先に原辺非恒等のまま作る。E固有保存定理へのF適用はその一般構成の後に閉じる"
  expected_result_type: proof-obligation-discharged
  lean_targets: [NativeAffineKernel, NativeAffineTower, NativeAffineRepair, NativeAffineCoordinates, NativeAffineRegression]
  risks: ["native全affineをcustom有効部分群へ縮めない", "GroupExtension.inputの恒等元辺で任意L_eを失わない", "centralizerの逆向き/全核/零次元を落とさない", "実3cell条件を一般authored certificateとして供給するだけにしない", "full arrows/全S/同じ制限とfinite入力生成を落とさない"]
  unchecked: ["C14構成/証明/有限入力接続/回帰/独立監査はこれから実装", "E固有の記号更新/文脈tester/内部splitとFへの適用、指定W1–W5、別累積completion gateは後続"]
```

このselectionは実装前の固定提案。Fの実現と受理済みA–Dへの接続を一つの数学的到達点とし、E固有の一般構成・その実アフィン適用とW1–W5は後続に保持する。全F/全GOAL完成とはまだ表示しない。途中分割が必要なら元終了条件と具体的split_reason・達成済み部分・未完obligationを保持する。

### C14 — 構成と受理spine

全native `AffineEquiv` を操作群とし、実 `linearHom` を full `LinearEquiv` への射影とする。
`projection_surjective` は任意の線形同型のnative affine liftを構成する。
`kernelEquiv` はこの射影の核全体と全translation vectorの乗法群の両逆であり、
`centralizes_kernel_iff` は全核を中央化する実操作がtranslationであることを両方向で証明する。
一般のfield/moduleで証明し、有限体と `Fin d → k` は零次元を含めてそのまま適用する。

元の実操作 `L_e` と別のreference `R_e` は任意のまま保持する。
`original` は同じ元typed Kの `L_e` を持つLiftData、`referenceLift` は `R_e L_e^-1` のactual upper lift、coreはその実linear射影。
`selected_edge_value` / `selected_path_value` はreselectionが同じ `R_e` とordered wordを保つことを証明する。
`comparator` は指定translationであり、strong/lower strong/full kernel可換/輸送全同型/全核中央化を同じ実群射から構成する。
face入力はreference wordのlinear一致だけであり、実修復face equalityを仮定しない。

`coefficient` / `linearCoefficient` は全actual categorical kernelを全実vectorへ同定する。
`edge_coefficient` / `path_coefficient` は核輸送を同じreferenceのlinear componentへ運ぶ。
`faceOperation` / `pastingOperation` は元orientation、outgoing word、すべてのtyped pasting occurrenceの実合成を独立に評価する。
`authored_syzygy` はこの実3-cell route operationの一致からAの条件を導く。
`defect_value` は指定translationとleft/right reference word quotientの実値、
`d0_value` / `d1_value` / `d2_value` は元辺・元face両word・元3-cell両pastingの全occurrenceを保つ実vector評価。

`Repair` は全実affine辺、同じreference linear component、指定translationを含む実face equality、物理fixed辺の実値から独立定義する。
`repairEquivalence` は同じ任意の元辺Lを保持した `SupportedRepair` との両逆。
`gaugeLabels` は元fixed vertexで零かつ元fixed edge上でreference linear transportを保つ全vector labelである。
`gaugeLabelEquivalence`、各実辺上の `native_gauge_value` / `gauge_value`、独立pointwise `Arrow` と `arrowEquivalence` により、full labelを作用結果で同一視しない。
`groupoid_functor_inverse` / `groupoid_inverse_functor` は同じ元実操作・全射上で両functor合成が恒等であることを証明する。
全Sは `fixedEdgesForRange` を同じ原名前で代入する。`affineRangeFunctor` はその範囲緩和の全対象・全射を保持する。
`restricted_tower_eq`、独立実修復/全label制限、`affine_restriction_functors` はclosed presentationの同じ元全0–3 geometry上で両経路を一致させる。

`standardBases` は同じ元全kernelのd標準座標であり、proper subgroup基底ではない。
`vertexMatrix` / `edgeMatrix` / `faceMatrix` / `defectCoordinates` は原実referenceのlinear評価・全word・全typed pasting・実defect値から直接構成し、native元微分/defectへの値法則を持つ。
`finiteObjectEquivalence` はこの全基底、元完全列挙、同じ元linear輸送/実defectをC11の一回local生成へ渡し、全public値とfull private kernel積を持つstrict生成対象へ運ぶ。
`finiteGroupoidEquivalence` と両functor逆はfull compatible gauge labelsを保持する。
`finite_forward_edge_value` / `finite_inverse_edge_value` は元同じedgeの実correctionと実operationを保持し、`finite_forward_label_value` は各元vertexの全vectorを保持する。
`affine_repair_iff_public` はこの同じ生成public関係への全S判定。
`affine_repair_iff_obstruction_zero` は実3-cell整合から得た元relative H2障害、
`affine_repair_iff_range` / `affine_repair_iff_hits` / `affine_minimal_repair_iff` はDの同じalways quotient/全候補列のrange・dual・極小transversalへ接続する。

以下の14 sourceを登録し、明示宣言および同じsourceの生成APIを個別公理監査の対象とする。

`NativeAffineKernel.lean` (15明示宣言、source SHA256 `dbc8336db27b30ad9f49c8651692e5fe23b0d32ef04a487a0484024495bde686`):

`NativeAffine.Operations`、`NativeAffine.projection`、`NativeAffine.projection_surjective`、`NativeAffine.translation`、`NativeAffine.translation_apply`、`NativeAffine.projection_translation`、`NativeAffine.operation_apply`、`NativeAffine.projection_eq_one_iff`、`NativeAffine.translationKernel`、`NativeAffine.kernelEquiv`、`NativeAffine.kernelEquiv_symm_val`、`NativeAffine.kernel_comm`、`NativeAffine.conjugation_translation`、`NativeAffine.centralizes_translations_iff`、`NativeAffine.centralizes_kernel_iff`。

`NativeAffineTower.lean` (14明示宣言、source SHA256 `747d4a8f68c7957b5675bbe4a054a1499c34755efec6d12d58e0a0a4610d44ad`):

`NativeAffine.original`、`NativeAffine.original_path_value`、`NativeAffine.referenceLift`、`NativeAffine.core`、`NativeAffine.referenceLift_core`、`NativeAffine.selected_edge_value`、`NativeAffine.selected_path_value`、`NativeAffine.original_lower_strong`、`NativeAffine.comparator`、`NativeAffine.comparator_centralizes`、`NativeAffine.core_alignment`、`NativeAffine.tower`、`NativeAffine.tower_original_edge`、`NativeAffine.tower_reference_edge`。

`NativeAffineCoefficients.lean` (7明示宣言、source SHA256 `1e35973c81534691a223ff1a785f5ca10d2ee421d387a901b8521203cd287c04`):

`NativeAffine.coefficient`、`NativeAffine.coefficientModule`、`NativeAffine.linearCoefficient`、`NativeAffine.coefficient_inverse_value`、`NativeAffine.coefficient_inclusion`、`NativeAffine.edge_coefficient`、`NativeAffine.edge_linear`。

`NativeAffineEvaluation.lean` (9明示宣言、source SHA256 `103438be05a0d2e40b0918fb89d0c67d562ade333a5898b842364544fcdd05e1`):

`NativeAffine.tower_path_value`、`NativeAffine.faceOperation`、`NativeAffine.pastingOperation`、`NativeAffine.whisker_value`、`NativeAffine.authored_face_value`、`NativeAffine.authored_pasting_value`、`NativeAffine.authored_syzygy`、`NativeAffine.canonical_face_value`、`NativeAffine.defect_value`。

`NativeAffineRepairs.lean` (10明示宣言、source SHA256 `5f1356b80428dcab8695340a5a0e73b5d6cf598aa35f70f75ace451cc8fc2510`):

`NativeAffine.Repair`、`NativeAffine.Repair.ext`、`NativeAffine.chosenOperation`、`NativeAffine.chosen_edge_value`、`NativeAffine.chosen_path_value`、`NativeAffine.toRepair`、`NativeAffine.fromRepair`、`NativeAffine.repairEquivalence`、`NativeAffine.repairEquivalence_value`、`NativeAffine.repairEquivalence_inverse_value`。

`NativeAffineGaugeLabels.lean` (5明示宣言、source SHA256 `889bf96928d11b4819edc2492a032e0b5aa3ae4c5416736b3550661392078b03`):

`NativeAffine.gaugeLabels`、`NativeAffine.gauge_label_conditions`、`NativeAffine.gaugeLabelEquivalence`、`NativeAffine.gaugeLabelEquivalence_value`、`NativeAffine.gaugeLabelEquivalence_inverse_value`。

`NativeAffineGroupoid.lean` (14明示宣言、source SHA256 `994a5800d3fc012d758a8db696ae35260339f4b0560d7a27d3f03b31007ea148`):

`NativeAffine.native_gauge_value`、`NativeAffine.gauge`、`NativeAffine.gauge_value`、`NativeAffine.gaugeAddAction`、`NativeAffine.Arrow`、`NativeAffine.gauge_eq_iff`、`NativeAffine.Groupoid`、`NativeAffine.repair_equivariant`、`NativeAffine.groupoidEquivalence`、`NativeAffine.arrowEquivalence`、`NativeAffine.groupoid_forward_label`、`NativeAffine.groupoid_inverse_label`、`NativeAffine.groupoid_functor_inverse`、`NativeAffine.groupoid_inverse_functor`。

`NativeAffineDifferentials.lean` (10明示宣言、source SHA256 `8838d39a6eeef0ccbce9e099f2dc17abb6777a152ec9af471012bc6572d62c9a`):

`NativeAffine.path_coefficient`、`NativeAffine.vectorPath`、`NativeAffine.path_correction_value`、`NativeAffine.d0_value`、`NativeAffine.d1_value`、`NativeAffine.vectorFace`、`NativeAffine.vectorPasting`、`NativeAffine.face_correction_value`、`NativeAffine.pasting_correction_value`、`NativeAffine.d2_value`。

`NativeAffineRanges.lean` (11明示宣言、source SHA256 `1529d2b9aed05da545fdb01f2bf52d6a42e72e50ee3d70b5f5c7c9242f7329cb`):

`NativeAffine.fixed_native`、`NativeAffine.repairInclude`、`NativeAffine.repair_include_value`、`NativeAffine.repair_include_native`、`NativeAffine.labelInclude`、`NativeAffine.repair_include_gauge`、`NativeAffine.affineRangeFunctor`、`NativeAffine.affine_repair_iff_obstruction_zero`、`NativeAffine.affine_repair_iff_range`、`NativeAffine.affine_repair_iff_hits`、`NativeAffine.affine_minimal_repair_iff`。

`NativeAffineFiniteInput.lean` (14明示宣言、source SHA256 `9c8f07bfec1b7d4204eba70bf6ea8ecb2e9c18a5803f153b367bfd451f94231f`):

`NativeAffine.standardBases`、`NativeAffine.standard_basis_value`、`NativeAffine.standard_basis_inverse`、`NativeAffine.vertexColumn`、`NativeAffine.edgeColumn`、`NativeAffine.faceColumn`、`NativeAffine.vertexMatrix`、`NativeAffine.edgeMatrix`、`NativeAffine.faceMatrix`、`NativeAffine.defectCoordinates`、`NativeAffine.vertex_matrix_value`、`NativeAffine.edge_matrix_value`、`NativeAffine.face_matrix_value`、`NativeAffine.defect_coordinate_value`。

`NativeAffineCorrection.lean` (4明示宣言、source SHA256 `c6329349c601d9c7784bd33c2a8a34233396182a84af4b941f5c964eebacd62c`):

`NativeAffine.native_repair_correction_value`、`NativeAffine.realCorrection`、`NativeAffine.real_correction_native`、`NativeAffine.real_correction_restore`。

`NativeAffineRestriction.lean` (12明示宣言、source SHA256 `7b97ba55b365233d72fd8a9b052c2bb8ac57b9989a0ddb77703cdb741db66138`):

`NativeAffine.restrictOperations`、`NativeAffine.restricted_path_value`、`NativeAffine.restricted_faces`、`NativeAffine.restricted_tower_eq`、`NativeAffine.restrictAffineRepair`、`NativeAffine.affine_restriction_value`、`NativeAffine.affine_restriction_native`、`NativeAffine.restrictAffineLabels`、`NativeAffine.affine_label_restriction_native`、`NativeAffine.affine_restriction_gauge`、`NativeAffine.affineRestrictionFunctor`、`NativeAffine.affine_restriction_functors`。

`NativeAffineFiniteCover.lean` (10明示宣言、source SHA256 `fc83929d67a921180caaa0f59b08d0c6380c6a800a9ad15f6f9ad6e1191858c0`):

`NativeAffine.finiteObjectEquivalence`、`NativeAffine.finiteLabelEquivalence`、`NativeAffine.finite_equivariant`、`NativeAffine.finiteGroupoidEquivalence`、`NativeAffine.finite_functor_inverse`、`NativeAffine.finite_inverse_functor`、`NativeAffine.affine_repair_iff_public`、`NativeAffine.finite_forward_edge_value`、`NativeAffine.finite_inverse_edge_value`、`NativeAffine.finite_forward_label_value`。

`C14AffineRegression.lean` (30明示宣言、source SHA256 `6691c81d081e71e7cf0c4a243630291bcdf0996a2f7730238eaf2156ede32fda`):

`C14AffineRegression.V`、`C14AffineRegression.K`、`C14AffineRegression.edgeNameEquality`、`C14AffineRegression.x`、`C14AffineRegression.y`、`C14AffineRegression.shear`、`C14AffineRegression.reference`、`C14AffineRegression.original`、`C14AffineRegression.comparisons`、`C14AffineRegression.aligned`、`C14AffineRegression.actualTower`、`C14AffineRegression.authored_three`、`C14AffineRegression.original_false_value`、`C14AffineRegression.tower_original_false`、`C14AffineRegression.original_reference_distinct`、`C14AffineRegression.native_transport_nonidentity`、`C14AffineRegression.gauge_label_x_allowed`、`C14AffineRegression.gauge_label_y_forbidden`、`C14AffineRegression.full_kernel_vector`、`C14AffineRegression.comparator_full_centralizer`、`C14AffineRegression.shear_not_full_centralizer`、`C14AffineRegression.repaired`、`C14AffineRegression.positive`、`C14AffineRegression.positive_native`、`C14AffineRegression.all_fixed_impossible`、`C14AffineRegression.all_fixed_native_impossible`、`C14AffineRegression.actual_matrix_positive`、`C14AffineRegression.actual_matrix_negative`、`C14AffineRegression.actual_defect_first`、`C14AffineRegression.actual_defect_second`。

### C14 — material premiseとproof-use

| material premise | 原始出所・放電 | proof-use |
| --- | --- | --- |
| full affine operation/linear projection | native AffineEquiv/LinearEquiv、全射と全核両逆を構成 | 全強辺/full核/centralizer/whole translation module |
| 任意の元L・reference R | 原実辺入力、referenceLift=R L^-1 | 元実choice保持、selected辺/path、実修復両逆 |
| 指定comparison translations | 元vector c、whole-kernel中央化を実射影から証明 | facecore整合/元defect/全核輸送 |
| reference face linear一致 | 許された原core alignment、実wordのlinear一致 | 同じtyped KのOriginalTowerPresentation |
| 元実3-cell route一致 | orientation/outgoing word/full pasting実操作一致 | authored syzygyと相対障害cocycle |
| P閉包・実固定face整合 | 元closed regionと原実word equality | 同じfixed native条件、全Sの相対obstruction/range |
| field/d/full有限座標・完全列挙 | native full kernel standardBases、元cell/fieldリスト | 0–3実微分/defect値、Cの一回local生成/full復元 |
| C/D一般受理API | C11の同じ元生成full public/private/full labels、C13の全元quotient/dual | 全実affine修復へのstrict両逆と全S/極小判定 |

実修復・dual・public復元・H2消滅・全射対応を入力certificate fieldにしない。
実3-cell仮定は元typed primitive operationの等号に固定し、それからAの一般条件を生成する。
`NativeAffineFiniteCover` の検証上限はそのfull generated型の展開に対してmaxHeartbeats4000000、synthInstance100000であり、数学の仮定・対象・結論を変更しない。

### C14 — concrete回帰

`C14AffineRegression` はF3²の全native affine group、元Bool二loop、一つの元face、元Empty triplesを使う。
実referenceは非恒等shearと別のterminal translations、元Lはtranslationとshearの逆/二重合成であり、元Lを恒等へ固定しない。
`original_false_value` / `original_reference_distinct` と `tower_original_false` が元操作の独立値と保持を確認する。
`native_transport_nonidentity` は第二標準vectorが両標準vectorの和へ輸送されることを全actual核で確認する。
`comparator_full_centralizer` / `shear_not_full_centralizer` は同じwhole native射影核に対する正負の中央化。
`gauge_label_x_allowed` / `gauge_label_y_forbidden` は空固定頂点集合と同じ固定false shear loopで、非零の定数xが許可され、定数yが拒否されることを証明する。
`positive` はfalse原loopを物理固定し、true候補を指定comparisonに一致させた独立実修復を構成する。
`positive_native` は同じ元入力へ戻す。
`all_fixed_impossible` は両元referenceの実値と元face equalityから1=0を導き、`all_fixed_native_impossible` は同じ独立native対象の不能へ運ぶ。
これらはC14の非自明なprimitive実現の回帰であり、指定W1–W5の全条件を代替しない。
E固有の一般保存定理とその実affine適用、指定W1–W5、別累積completion gateは後続に保持する。

`actual_matrix_positive` / `actual_matrix_negative` は同じ実入力の元full edge列の正負係数、`actual_defect_first` / `actual_defect_second` は元実defectの両標準座標(1,-1)を直接評価する。

### C14 — 到達点と検証

rootの固定選定14 exact-source bodyのfocused確認はexit0/errors0/warnings0。
最初の163明示+22生成=185新APIと、使用先で生成された受理dependency補助1宣言の計186件を個別に `#print axioms` で検査し、欠落0・標準公理のみ。既存のstatement/実行本文は同じで、source内設計説明と名指しgauge正負補助定理2件を含む現在の明示集合は165、新API187、依存補助を含む総監査集合は188。追加2件の個別公理log SHA256 `9cd81039ac5c6d113edffd97b203531e4af24c04662c576958812e1e465b8c7f`、単一production回帰focusedは30宣言guard/exit0/errors0/warnings0。
公理log SHA256 `8925040604ccb45d52b6bcb046a0c4a92490c4f3b40265e068a892ba39470c56`。全14 sourceのSHA256と一意登録を照合する。
原実F3²の非恒等輸送、元/referenceの独立値、全核中央化正負、実修復正負、元full matrix正負係数と実defect両座標を検査する。
placeholder/hidden-BiDi/privacy/diff/import方向scanはclean。Research全体/aggregate/全file loopを実行しない。
C14の標準独立PR gateとroot受理・CIは固定headの監査コメントで行う。

```yaml
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta:
    - "全native affine operation/linear射影全射/全actual核≃全translations/whole kernel centralizer iffを構成"
    - "任意の元Lを保ち、同じreference R/core/指定translation comparator/full原typed0–3の実塔を原始群射から生成"
    - "実輸送/path/defect/d0/d1/d2評価とfull typed実3route equality→authored syzygyを構成"
    - "独立実affine repairs/full vertex labels/独立pointwise arrowsとnative actual repairs/full arrowsの両逆関手、全S緩和とclosed原部分表示の同じ値・関手比較を構成"
    - "全d標準kernel basesと元実評価から有限0–3微分/defect座標を生成。同じCのstrict全public/private/full label復元とD全range/dual/minimal、A相対H2障害へ接続"
    - "F3²非恒等linear/任意非恒等元辺・別reference/comparator/full centralizer正負/独立actual正負/full列・defect実値を確認"
  exit_criteria_status:
    - "任意有限体・任意d包括零次元のfull native groups/projection/whole kernel/centralizer両方向: 一般field/moduleの証明を全標準vectorへ適用"
    - "同じ元L/R/core/comparator/full0–3を保持、strong/全核可換/輸送全同型を生成、実3cell原始条件から一般syzygyを導出"
    - "独立real対象/全labels/pointwise実射とnative full gauge groupoidの両逆、全S/同じfixed名前/元実値/closed制限と関手比較"
    - "全standard basis/実微分・defect評価/C同じfull復元/D全候補分類/A障害、非自明回帰と全187新API+受理依存補助1公理/登録/scan"
    - "標準独立4lane PR監査とroot受理/CIはこの固定到達点のPR headで判定"
  split_reason: none
  completion_candidate: no
  lean_artifacts: [NativeAffineKernel, NativeAffineTower, NativeAffineCoefficients, NativeAffineEvaluation, NativeAffineRepairs, NativeAffineGaugeLabels, NativeAffineGroupoid, NativeAffineDifferentials, NativeAffineRanges, NativeAffineFiniteInput, NativeAffineCorrection, NativeAffineRestriction, NativeAffineFiniteCover, C14AffineRegression]
  claim_mapping:
    source_labels: ["GOAL F full Aff→GL→1の原始実現/元辺保持/A–D接続", "GOAL A–Dの同じ受理原入力と全S/full復元"]
    theorem_names: ["NativeAffine.kernelEquiv", "NativeAffine.centralizes_kernel_iff", "NativeAffine.tower", "NativeAffine.authored_syzygy", "NativeAffine.d0_value", "NativeAffine.d1_value", "NativeAffine.d2_value", "NativeAffine.groupoidEquivalence", "NativeAffine.affine_restriction_functors", "NativeAffine.finiteGroupoidEquivalence", "NativeAffine.finite_inverse_edge_value", "NativeAffine.affine_repair_iff_hits"]
    undischarged_assumptions: []
    acceptance_point: "全F primitive実現と受理A–Dへの接続の候補。E固有の一般構成とその全affine適用は後続。全F/全GOAL completionを表示しない"
    port_status: unported
  remaining_goal_obligations: ["E記号的同じgenerator/rhs値更新/全S再利用", "E実singleton文脈試験と全許容external環境iff", "E全typed内部辺分割/full groupoid・複体・障害・holonomy・公開/双対保存とFへの適用", "W1–W5全指定実affine構成/対応/決定", "別累積completion packetとfresh Math2/Lean2全target最終監査"]
audits:
  premise_delta:
    discharged: ["native full射影の全射/全核/中央化 iff", "任意元L/Rからのstrong/full kernel可換/全核輸送同型/comparator中央化", "実3-cell route equalityから原authored syzygy", "全native kernel standard d coordinates/原実微分・defect評価", "独立実修復/全label・射と元supported repairsの全方向"]
    remaining: ["上記remaining_goal_obligations"]
  certificate_provenance:
    discharged: ["full kernelは実linearHomの核全体", "元実辺L/referenceRのquotientから同じ元lift/coreを生成", "comparatorは指定translation、full centralizerから実中央化を放電", "実operation routeからsyzygy生成", "全標準basesと実微分/defectから同じC11生成入力を作り全復元へ接続"]
    unresolved: []
  proof_use:
    used: ["全射影/全translations→元実塔/full核/中央化", "任意Lの保持→native実choices/独立修復両逆", "reference R linear→全輸送/各元微分", "orientation/outgoing/full occurrence→実pastingとauthored syzygy", "全original fixed名前/vertex条件→全S actual/full labels/制限", "全kernel d basisと元完全列挙→C public/private/full labels", "実fixedfaceと実3route→同じ相対障害", "同じ元D/全候補→dual/range/minimal"]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: ["選定14 exact-body focused exit0/errors0/warnings0", "165明示+22生成=187新APIと受理依存補助1の188全個別公理標準のみ/欠落0", "axiom log SHA256 8925040604ccb45d52b6bcb046a0c4a92490c4f3b40265e068a892ba39470c56", "原F3²全核・非恒等輸送/元L-reference独立/実修復正負/元finite列正負・defect両座標", "14source exact hashes/14一意登録/placeholder/Unicode/privacy/import方向/diff scan"]
  blocking_findings: []
  next_obligation: "C14固定headの標準review-pr/math-lean-reviewとroot受理後、Eの同じ原generatorの記号的値更新へ進む"
```


### Cycle 15 selection — 原始値から同じ全S生成器へ記号的更新を接続

```yaml
ledger_type: target_cycle_result
goal: G-130-aat-relative-repair-composition
cycle: 15
goal_blob_sha: 8da0fb4eb75d1cb5c37a9d4ddf5e03c18c0bb8a2
base_oid: 134ed790586c12f03313eab9dfe94f370946c97d
tracking_issue: 5132
report_path: research/reports/G-130-aat-relative-repair-composition.md
selection:
  proof_state_ref: "Issue #5132 C14受理5931648237 / PR5150 root acceptance5931624166 / report Cycle14"
  proof_dag_predecessors: ["C10–12 同じ原full有限座標/一回生成/strict全S復元/表示比較", "C13 同じ原D/全範囲/dual/finite決定", "C14 任意全native affine原始実現/元typed微分・defect/独立real repair全射"]
  milestone: "固定GOAL E記号生成・値更新とFの同じ実適用。固定typed K/full kernel/linear輸送/基底/閉被覆/候補名の実入力族から全parameterの原始操作とr0+Bvを生成し、取得前の記号public/fullprivate復元・全labelsと取得後の同じ生成器による全S判定/復元/実操作対応を交換させる"
  proof_obligations:
    - "任意元L0・reference R0と線形parameterから辺translation θL/θR、comparison変化Cを作り全vのL(v)/R(v)/c(v)をreal Operationsとして実現。全typed wordの翻訳項、linear輸送不変、元実δ(v)=δ0+C(v)+d1_vector θR(v)を実合成から導く"
    - "baseと全parameterの線形条件から元full3-route equalityと固定P face整合を全vで生成。全parameter実現と入力族の法則を別に示し、原0–3/任意L/候補名/full kernelを保持、一般cohomology/成功certificateに置換しない"
    - "同じ全native coefficients/原d0–d2/full matrices D/F/public/private coordinatesと基底の固定を証明し、生成elimination/kernel/image/section/public rows/full-label作用の線形部分をv/rhs/Sに依存しない同じdataから作る"
    - "固定D/F/生成σと生成B/r0から(z,v)の記号的関係q(Fz−Bv)=q r0とfull internal kernel復元を取得前に作る。各v評価fiberと具体relation/solution/full coordinatesの両逆、rec=σ(r0+Bv−Fz)+kの評価交換を証明。異なるvのfiber非空同値を主張しない"
    - "同じ各local原RHS/bases/generatorへ適用し、strictshared edges/fullvertices/glue、候補零条件/全S、fullprivate kernel/全labelsの復元を評価と交換。値差時のrhs/affine復元項だけの更新・同じ消去/作用再利用を証明、受理C11と独立実affine対象・全射の元値へ接続"
    - "値代入で成功/失敗が変わる非零finite族とfull kernel自由度/full labels/候補零条件の具体回帰を一般APIへ接続。全宣言focused/個別公理/登録/scans、root実装終了後の標準新規4lane PR gate/root受理/CIを固定"
  exit_criteria:
    - "全parameterの元原始実操作・全typed word/defect評価・入力族face/3-cell法則を構成"
    - "同じ原native M/bases/D/F/generator/full label作用の保持を証明"
    - "記号relation/fullrecの評価fiber両逆、rhs/affine項の値差更新を構成"
    - "strictcover/allS/独立real objects/full arrowsの元値への評価交換を接続"
    - "非自明成功失敗・full自由度回帰と全集合証拠/標準PR gateを固定"
  selection_reason: "C14の全primitive実現を受理。Eの第一条項を原始値から同じ生成器/全Sまで閉じ、後続のsingleton環境とsplitに使う値再利用の証明距離を直接縮める"
  expected_result_type: proof-obligation-discharged
  lean_targets: [AffinePrimitiveFamily, SymbolicInterface, SymbolicCover, NativeSymbolicRestoration, C15SymbolicRegression]
  risks: ["r0+Bvを結論fieldにしない", "全parameter実現/3-cell条件を省かない", "異なるv間の無条件解同値に弱めない", "同じfull kernel/σ/labels/shared候補値/allSを保持", "一般式だけで実元操作との接続を消さない"]
  unchecked: ["C15構成/全接続/回帰/査読はこれから実装", "E文脈同値/全typed内部split/Fへの適用、W1–W5、累積completionは後続"]
```

このselectionは実装前の固定提案。上の終了条件に必要な構成と補題、具体例、全S接続を同じcycle内で反復する。全E/全F/全GOAL完成とは表示しない。

### C15 — 原始実操作から記号的右辺と同じ全範囲復元へ

固定GOAL E「記号的生成と値更新」、Fの同じ実入力への適用、n1017 §3.5とdesign §5に対応する。
`AffinePrimitiveFamily` は任意元Lとreference Rを保ち、各辺へのtranslation θL(v)/θR(v)、比較c+η(v)を全vで実Operationsとして構成する。
元typed pathの全出現の翻訳項を実合成から評価し、全linear輸送は同じで、実defectはδ0+η(v)+d1_vector(θR(v))となる。
`AffineComparisonWords` / `AffineFamilyLaws` は完全な両pastingについて、baseline実3-route整合とvector d2η=0から全vの実3-route整合を生成する。
閉P上のbaseline実face整合と生成parameter項の零条件から、全vの同じ物理固定face整合を導く。成功修復やH2零性は供給しない。

`AffineConstantCoefficients` は全native実核・演算・edge equivalenceを含む同じbundled Mを同定する。
`AffineFamilyFiniteInput` は全standard核のdimension、coordinate、inverseを各元頂点で同定し、元d0/d1/d2の全matrixを同じtyped列と全pastingで同定する。
`AffineFamilyDifferentials` は相対全d0/d1を同定する。`AffineFamilyLabels` と `AffineFamilyEquationCoordinates` は全実頂点ラベルと全supportedラベル部分群を同定する。
この同じM/bases/列と有限完全enumerationから受理C10–11のD/F、像basis、full kernel、生成section、public rowと作用を一度作る。
それらの入力にv、rhs、Sは入らず、vは生成した原始defectの右辺だけへ入り、Sは候補零述語へ入る。

`SymbolicInterface` は固定D/F/B/r0と既に入力から生成されたσから、取得前の関係q(Fz−Bv)=q(r0)と全kerD座標を構成する。
各vのevaluation fibreとr0+Bvの関係、全solution/public/private座標に両逆を構成し、復元はσ(r0+Bv−Fz)+kである。
`SymbolicInterfaceUpdates` は右辺の差B(w−v)、復元のアフィン差σB(w−v)、元gauge増分のv非依存を証明する。
異なるvでの可否は、`C15SymbolicAffineRegression.empty_range_iff` がv≠0で失敗する同じ実入力を含めて扱う。

`SymbolicNativeLocal` は生成Bを原relative defectの同じlocal制限・basisによる負座標から作り、同じD/F/σのlocal復元へ接続する。
`SymbolicStrictCover` / `SymbolicCoverAction` は全Sの候補零、元共有edge値、共有full vertex labelsの厳密適合を保持し、取得前の全kerD自由度を各vの元cochainへ復元する。
`SymbolicGlobalRestoration` / `SymbolicGlobalValues` は独立に定義された大域supported方程式との全対象・全射のstrict両逆を構成し、local評価、元edge補正、全vertex label値を交換させる。
`SymbolicCoverRanges` は全S⊆Tの同じpublic/private/full-label値を保持する包含と評価を交換させる。

`AffineFamilyRelativeDefect` はprimitive実δ(v)をbase Mの全relative kernelへ運んだδ0+Δvと全faceで同定する。
`AffineFamilyEquationCoordinates` / `AffineFamilyEquationBridge` は同じ全cochain/全gaugeでnative parameter方程式をbase方程式へ同定する。
`AffineFamilyNativeEquation` / `AffineFamilySymbolicCover` は独立real Repair、native SupportedRepair、base supported equation、記号的strictcoverの間に全arrowを含む両逆関手を構成する。
元実choice/全edge補正、全labelを保存し、`AffineFamilySymbolicRanges.family_symbolic_range_square` は独立actual range包含関手との全関手可換を証明する。
`AffineFamilyDualClassification` は同じ原always D/cokerと原candidate列B_eについて、全v・全Sの実修復可否iff span iff dual hitting、failed dual、minimal hittingを接続する。
同じ商の値はo(v)=q(-δ0)-q(Δv)で、candidate列とそのsupportは共用する。

### C15 — material premiseと受理依存の使用

| premise | 分類・生成元 | 使用先 |
| --- | --- | --- |
| Field/Module、有限typed K、任意元L/reference R/c、θL/θR/η | GOALの実入力・値更新の入力条件。translationと実word評価はAffinePrimitiveFamilyから生成 | 全parameter実原始操作/linear不変/δ(v) |
| 元reference両face pathのlinear alignment hf | 原始入力のface線形条件、parameterでもtranslated_linear/translated_vector_pathで保持 | same core/familyTower/原defect/全cochain |
| baseline実3-route整合、vector d2η=0 | 入力族が全3-cell lawを保つためのdirection-hypothesis | family_three_lawで全vの実3-route整合を生成、受理Fのnative syzygyへ |
| 閉P、baseline実fixed face、生成ΔvのP零 hB | GOALの閉固定部分と値更新族の条件 | family_fixed_face/familyRelativeLinear/relativeδと全S復元 |
| 閉finite cover、原候補名、全核basis/完全finite enumeration | GOAL C–Fの同じ入力条件 | 同じ原D/F、有限section/kernel/strict共有/glue/全S |
| finite elimination、σ/right inverse、public/private/action | 構成・放電済みpredecessor C10–11の同じ元M/bases/enumから生成 | SymbolicNativeLocal、SymbolicCoverAction、元全復元 |
| equation/action/strict compatibility/native-real equivalence | 今回の構成または受理C11/C14。成功certificateは入力にしない | evaluation fibre両逆、原全ラベル、actual包含可換 |
| original quotient/full-dual classification | 受理C13の現在のstatementを同じM/P/原候補/linear/δ(v)へ適用 | 全v・全S iff、不能証拠、極小範囲 |

受理C10–12はPR5146–5148のreport/受理コメント、C13はPR5149 root #issuecomment-5929751165、C14はPR5150 root #issuecomment-5931624166で固定する。
現在の使用宣言・必要な定義・同じ適用引数・proof-useを確認した受理依存は、共通acceptance contractの追跡完了条件で止める。
Repair/Solution/Coordinatesのfieldは独立に分類する対象と座標の条件であり、入力から成功を供給するfieldではない。
一般のσ/right inverse/action equalityを引数で扱う補題は、適用箇所で同じ有限入力から生成し、単なるcertificate転送を成功証拠にしない。

### C15 — 同じ実入力の非零回帰

`C15AffineFamilyRegression` は受理C14のF3²全実核、異なる元L/reference R、非恒等shear、非零comparisonを保つ。
全原始値vに対し、実defect=v、全matrix固定、全loop固定時の独立real可否iff v=0、元true候補の許可では全vで実修復を構成する。
同じ物理固定shear edgeで非零x gaugeが全vで許可され、非零y gaugeは全vで拒否される。
`C15SymbolicAffineRegression.correspondence` は同じ実K/L/R/θ族・全元finite列を一般familyRealSymbolicEquivalenceへ渡す。
その取得前に固定された同じgenerated fibreは、空許可で可否iff v=0、元true候補を許可した範囲では全vで可解となる。
`C15SymbolicKernelRegression` は実finite matrix[1,0]の同じgenerated section/full unused-column kernelを保持する。
非零のprivate核値、effectを持つ非零full labelと非零stabilizer label、parameter1の非恒等native arrowを検査する。
これらは今回の値更新・全自由度・full labelsの発火証拠。指定W1–W5の全要求は同じ固定GOALで後続とする。

### C15 — 受理spine declaration list

全名の共通prefixは `AAT.AG.RelativeRepairComposition.`。各sourceの明示宣言を以下で固定する。

`AffineTranslationWords.lean` (8明示宣言、source SHA256 `45b54882210424b002121adfcc6a85d4dbd99c3d8d96117d7337caa81a9b8619`):

- `NativeAffine.translation_mul`
- `NativeAffine.translation_zero`
- `NativeAffine.translation_inv`
- `NativeAffine.operation_mul_translation`
- `NativeAffine.translatedOperations`
- `NativeAffine.translated_linear`
- `NativeAffine.translated_word_linear`
- `NativeAffine.translated_word`

`AffinePrimitiveDefect.lean` (5明示宣言、source SHA256 `07a9417b55f3fc6d1213879d19c6d5044986e4353312ab1944df83a881b9bfdf`):

- `NativeAffine.realDefectVector`
- `NativeAffine.reference_word_quotient`
- `NativeAffine.real_defect_residual`
- `NativeAffine.translated_defect`
- `NativeAffine.real_defect_native`

`AffineVectorLinear.lean` (7明示宣言、source SHA256 `7c028cd899abcbddc1a01f7a5b92486e2b22a3531eec85b6ec9953e176a65a0b`):

- `NativeAffine.vectorPathLinear`
- `NativeAffine.vectorFaceDifferential`
- `NativeAffine.vectorFaceLinear`
- `NativeAffine.vector_face_linear_value`
- `NativeAffine.vectorPastingLinear`
- `NativeAffine.vector_pasting_linear_value`
- `NativeAffine.vectorPastingDifferential`

`AffinePrimitiveFamily.lean` (14明示宣言、source SHA256 `f4040f631098f438b546b200438d06486d42ab0345fc770247ce5d6866f82b02`):

- `NativeAffine.familyOriginal`
- `NativeAffine.familyReference`
- `NativeAffine.familyComparisons`
- `NativeAffine.family_original_zero`
- `NativeAffine.family_reference_zero`
- `NativeAffine.family_comparisons_zero`
- `NativeAffine.family_aligned`
- `NativeAffine.familyTower`
- `NativeAffine.family_tower_original`
- `NativeAffine.family_tower_reference`
- `NativeAffine.family_core`
- `NativeAffine.familyDefectLinear`
- `NativeAffine.family_defect_affine`
- `NativeAffine.family_defect_native`

`AffineComparisonWords.lean` (7明示宣言、source SHA256 `18855ae2773c04f98df2b62b88cfb54eca7bb730cc1b25d5c5d1d848af354169`):

- `NativeAffine.translated_vector_path`
- `NativeAffine.face_operation_translation`
- `NativeAffine.pasting_operation_translation`
- `NativeAffine.three_operation_iff`
- `NativeAffine.translated_vector_face`
- `NativeAffine.translated_vector_pasting`
- `NativeAffine.translated_pasting_differential`

`AffineFamilyLaws.lean` (4明示宣言、source SHA256 `f40c5486a2f566e758f19951350c8d81984a565db54084d519d27ff061591d89`):

- `NativeAffine.face_residual_translation`
- `NativeAffine.face_coherent_iff_defect_zero`
- `NativeAffine.family_three_law`
- `NativeAffine.family_fixed_face`

`AffineConstantCoefficients.lean` (3明示宣言、source SHA256 `a15ace9cf8257cf277278e93fb9436ac7b92807ca99feb604becd2ac7ba04c5b`):

- `NativeAffine.same_linear_edge`
- `NativeAffine.same_linear_coefficients`
- `NativeAffine.family_local_coefficients`

`AffineFamilyLabels.lean` (1明示宣言、source SHA256 `3617b16b27a8e0c3dee1e5117db87583244c2857a1ac89af5bbac5723e4dfc43`):

- `NativeAffine.translated_gauge_labels`

`AffineFamilyFiniteInput.lean` (8明示宣言、source SHA256 `7b1b3029f1627ce4510203944442fcd1636f5f1041d3b886dab4343ccdb7af56`):

- `NativeAffine.family_coefficients`
- `NativeAffine.family_standard_dimension`
- `NativeAffine.family_standard_coordinate`
- `NativeAffine.family_standard_inverse`
- `NativeAffine.family_vertex_matrix`
- `NativeAffine.family_edge_matrix`
- `NativeAffine.family_face_matrix`
- `NativeAffine.family_defect_coordinates`

`SymbolicInterface.lean` (11明示宣言、source SHA256 `2c50b3dad2721b882397c20fd2b262819ab3d6520262f7f929b3cdc327c088dd`):

- `SymbolicInterface.publicMap`
- `SymbolicInterface.rhs`
- `SymbolicInterface.relation_evaluation`
- `SymbolicInterface.RelationFiber`
- `SymbolicInterface.relationFiberEquiv`
- `SymbolicInterface.coordinateFiberEquiv`
- `SymbolicInterface.SolutionFiber`
- `SymbolicInterface.solutionFiberEquiv`
- `SymbolicInterface.section_residual_evaluation`
- `SymbolicInterface.reconstruction_evaluation`
- `SymbolicInterface.kernel_coordinate_evaluation`

`SymbolicInterfaceAction.lean` (12明示宣言、source SHA256 `ba8e3bcc02399de81932b4f08830a5e5aa5cae0623cbe6e635032bc97de2d9f3`):

- `SymbolicInterface.publicCoboundary`
- `SymbolicInterface.symbolic_coboundary_zero`
- `SymbolicInterface.FiberObjects`
- `SymbolicInterface.fiberGauge`
- `SymbolicInterface.fiberAddAction`
- `SymbolicInterface.fiber_evaluation_equivariant`
- `SymbolicInterface.FiberGroupoid`
- `SymbolicInterface.fiberEquivalence`
- `SymbolicInterface.fiber_functor_inverse`
- `SymbolicInterface.fiber_inverse_functor`
- `SymbolicInterface.fiber_functor_label`
- `SymbolicInterface.fiber_inverse_label`

`SymbolicInterfaceUpdates.lean` (5明示宣言、source SHA256 `489e2be434c6a66632dff44a7e0d7c77fa9f5c129f0893fbe5cd279caae10549`):

- `SymbolicInterface.rhs_difference`
- `SymbolicInterface.section_update`
- `SymbolicInterface.reconstruction_update`
- `SymbolicInterface.gauge_public_increment`
- `SymbolicInterface.gauge_kernel_increment`

`SymbolicNativeLocal.lean` (9明示宣言、source SHA256 `2d28b0818d16772b6ac2c90a227d82c04153319eb8dd9a6218b48dcaf8de2126`):

- `SymbolicNativeLocal.defectFamily`
- `SymbolicNativeLocal.rhsMap`
- `SymbolicNativeLocal.rhsLinear`
- `SymbolicNativeLocal.rhs_affine`
- `SymbolicNativeLocal.Fiber`
- `SymbolicNativeLocal.fiberEquiv`
- `SymbolicNativeLocal.originalEquationEquiv`
- `SymbolicNativeLocal.fiber_public`
- `SymbolicNativeLocal.fiber_private`

`SymbolicStrictCover.lean` (8明示宣言、source SHA256 `dca8bec8c7b6d02d68b3bf476f3f7e3d1bb14c4f5d59dab44911d8c45c7e945c`):

- `SymbolicStrictCover.LocalFiber`
- `SymbolicStrictCover.PublicCompatible`
- `SymbolicStrictCover.Objects`
- `SymbolicStrictCover.compatibility_evaluation`
- `SymbolicStrictCover.objectEquiv`
- `SymbolicStrictCover.originalObjectEquiv`
- `SymbolicStrictCover.evaluated_public_value`
- `SymbolicStrictCover.evaluated_private_value`

`AffineFamilyRelativeDefect.lean` (3明示宣言、source SHA256 `d7a0a42571b0fff76060e6726dcd75fa22031d06e1200a78977116d77ddaa138`):

- `NativeAffine.familyRelativeLinear`
- `NativeAffine.family_relative_linear_value`
- `NativeAffine.family_native_relative_defect`

`SymbolicCoverAction.lean` (13明示宣言、source SHA256 `d87d4bef9fb5793d7076324632e495e75e7f04dfbafd26c0f9a287e34396984b`):

- `SymbolicCoverAction.gauge`
- `SymbolicCoverAction.gauge_component`
- `SymbolicCoverAction.evaluation_gauge`
- `SymbolicCoverAction.gauge_zero`
- `SymbolicCoverAction.gauge_add`
- `SymbolicCoverAction.addAction`
- `SymbolicCoverAction.Groupoid`
- `SymbolicCoverAction.evaluation_equivariant`
- `SymbolicCoverAction.equivalence`
- `SymbolicCoverAction.functor_inverse`
- `SymbolicCoverAction.inverse_functor`
- `SymbolicCoverAction.functor_label`
- `SymbolicCoverAction.inverse_label`

`SymbolicCoverRanges.lean` (6明示宣言、source SHA256 `e87fe855f7c3176f787c05e9d9bf220e6fd3ba04d74ea4843b28f6b1df688924`):

- `SymbolicCoverRanges.functor`
- `SymbolicCoverRanges.evaluation_range`
- `SymbolicCoverRanges.public_value`
- `SymbolicCoverRanges.private_value`
- `SymbolicCoverRanges.label_value`
- `SymbolicCoverRanges.functor_comp`

`SymbolicGlobalRestoration.lean` (5明示宣言、source SHA256 `2b74ed688b2661b8ea8d05ea8a9890468823813ab8df3838c43d8e37a5decdf5`):

- `SymbolicGlobalRestoration.objectEquiv`
- `SymbolicGlobalRestoration.equivalence`
- `SymbolicGlobalRestoration.functor_inverse`
- `SymbolicGlobalRestoration.inverse_functor`
- `SymbolicGlobalRestoration.evaluation_global`

`SymbolicGlobalValues.lean` (5明示宣言、source SHA256 `19217b2c4376cad95c586ad8edd2249634412ea261151623ddb17d05336b0ed1`):

- `SymbolicGlobalRestoration.original_local_evaluation`
- `SymbolicGlobalRestoration.forward_edge_value`
- `SymbolicGlobalRestoration.inverse_edge_value`
- `SymbolicGlobalRestoration.forward_label_value`
- `SymbolicGlobalRestoration.inverse_label_value`

`C15AffineFamilyRegression.lean` (21明示宣言、source SHA256 `9304eb6e28f829ff6db29bf839e7b19a7ac58ac4e35403301f0244d255e446bb`):

- `C15AffineFamilyRegression.originalTranslations`
- `C15AffineFamilyRegression.referenceTranslations`
- `C15AffineFamilyRegression.baseComparison`
- `C15AffineFamilyRegression.input`
- `C15AffineFamilyRegression.refs`
- `C15AffineFamilyRegression.reference_false`
- `C15AffineFamilyRegression.reference_true`
- `C15AffineFamilyRegression.original_false_parameter`
- `C15AffineFamilyRegression.base_coherent`
- `C15AffineFamilyRegression.base_defect_zero`
- `C15AffineFamilyRegression.generated_parameter_value`
- `C15AffineFamilyRegression.actual_parameter_defect`
- `C15AffineFamilyRegression.matrix_reused`
- `C15AffineFamilyRegression.all_fixed_iff`
- `C15AffineFamilyRegression.nonzero_all_fixed_failure`
- `C15AffineFamilyRegression.allowedRepair`
- `C15AffineFamilyRegression.nonzero_allowed_success`
- `C15AffineFamilyRegression.positive_native`
- `C15AffineFamilyRegression.full_gauge_labels_reused`
- `C15AffineFamilyRegression.gauge_x_allowed_every_value`
- `C15AffineFamilyRegression.gauge_y_forbidden_every_value`

`C15SymbolicKernelRegression.lean` (28明示宣言、source SHA256 `6039322e8322a93d9a7af9f29f1d0fa419eda170f5cc9a1647e047c61de4f983`):

- `C15SymbolicKernelRegression.k`
- `C15SymbolicKernelRegression.fieldValues`
- `C15SymbolicKernelRegression.rows`
- `C15SymbolicKernelRegression.columns`
- `C15SymbolicKernelRegression.matrix`
- `C15SymbolicKernelRegression.D`
- `C15SymbolicKernelRegression.generatedSection`
- `C15SymbolicKernelRegression.regular`
- `C15SymbolicKernelRegression.kernelVector`
- `C15SymbolicKernelRegression.kernel_mem`
- `C15SymbolicKernelRegression.kernel_nonzero`
- `C15SymbolicKernelRegression.F`
- `C15SymbolicKernelRegression.B`
- `C15SymbolicKernelRegression.a`
- `C15SymbolicKernelRegression.c`
- `C15SymbolicKernelRegression.label_zero`
- `C15SymbolicKernelRegression.nonzeroObject`
- `C15SymbolicKernelRegression.zeroObject`
- `C15SymbolicKernelRegression.nonzero_evaluation`
- `C15SymbolicKernelRegression.nonzero_reconstruction`
- `C15SymbolicKernelRegression.nonzero_stabilizer`
- `C15SymbolicKernelRegression.nonzero_effect`
- `C15SymbolicKernelRegression.NativeGroupoid`
- `C15SymbolicKernelRegression.nativeCategory`
- `C15SymbolicKernelRegression.zeroNative`
- `C15SymbolicKernelRegression.stabilizerArrow`
- `C15SymbolicKernelRegression.evaluated_stabilizer_label`
- `C15SymbolicKernelRegression.stabilizer_not_identity`

`AffineFamilyDifferentials.lean` (2明示宣言、source SHA256 `ef5d3fe0c35b4d77f30e7461bcf8a661a53126ca1cfbfc4604dbe822f087e53f`):

- `NativeAffine.family_relative_d0`
- `NativeAffine.family_relative_d1`

`AffineFamilyEquationCoordinates.lean` (7明示宣言、source SHA256 `819d0f3591bdbf0969435a46da5da47d97b4a4ab31d3dce38c7ab1c808a4f1ad`):

- `NativeAffine.family_equation_iff`
- `NativeAffine.familyEquationSolutions`
- `NativeAffine.familyEquationObjects`
- `NativeAffine.family_equation_labels_eq`
- `NativeAffine.familyEquationLabels`
- `NativeAffine.family_equation_edge_value`
- `NativeAffine.family_equation_label_value`

`AffineFamilyEquationBridge.lean` (2明示宣言、source SHA256 `7739433d86fd31dc802771aa01d25d064537cbd9fc06cbf7cff6c4e0982c1654`):

- `NativeAffine.family_equation_equivariant`
- `NativeAffine.familyEquationEquivalence`

`AffineFamilyNativeEquation.lean` (7明示宣言、source SHA256 `c8c035732c75656822226c89aec711e6b18f6e3c327902ac19e1680cf3af727e`):

- `NativeAffine.family_equation_functor_inverse`
- `NativeAffine.family_equation_inverse_functor`
- `NativeAffine.familyNativeEquationEquivalence`
- `NativeAffine.family_native_equation_functor_inverse`
- `NativeAffine.family_native_equation_inverse_functor`
- `NativeAffine.family_native_equation_edge_value`
- `NativeAffine.family_native_equation_label_value`

`AffineFamilySymbolicCover.lean` (10明示宣言、source SHA256 `c80d3f00b96da33f70c8b57aa7ac38abea8e89d13414a0b0c7ff3d3f1d918241`):

- `NativeAffine.familyNativeSymbolicEquivalence`
- `NativeAffine.family_native_symbolic_functor_inverse`
- `NativeAffine.family_native_symbolic_inverse_functor`
- `NativeAffine.familyRealSymbolicEquivalence`
- `NativeAffine.family_real_symbolic_functor_inverse`
- `NativeAffine.family_real_symbolic_inverse_functor`
- `NativeAffine.familySymbolicObjects`
- `NativeAffine.family_symbolic_forward_edge_value`
- `NativeAffine.family_symbolic_inverse_edge_value`
- `NativeAffine.family_symbolic_forward_label_value`

`AffineFamilySymbolicRanges.lean` (3明示宣言、source SHA256 `51ee0ecdd22940b69c9a33876a3f0fb0ed7f830ae590725146213318e833e4c7`):

- `strict_inverse_evaluation_square`
- `NativeAffine.family_generated_range_square`
- `NativeAffine.family_symbolic_range_square`

`C15SymbolicAffineRegression.lean` (21明示宣言、source SHA256 `4eee6b56504cf26aa78d8d3ac2a5f35ffbeb77ba97d47fdb538073816eb98258`):

- `C15SymbolicAffineRegression.candidates`
- `C15SymbolicAffineRegression.allowed`
- `C15SymbolicAffineRegression.P`
- `C15SymbolicAffineRegression.U`
- `C15SymbolicAffineRegression.edges`
- `C15SymbolicAffineRegression.units`
- `C15SymbolicAffineRegression.faceEquality`
- `C15SymbolicAffineRegression.candidateDecidable`
- `C15SymbolicAffineRegression.emptyEdgesDecidable`
- `C15SymbolicAffineRegression.emptyFacesDecidable`
- `C15SymbolicAffineRegression.regionVerticesDecidable`
- `C15SymbolicAffineRegression.regionEdgesDecidable`
- `C15SymbolicAffineRegression.regionFacesDecidable`
- `C15SymbolicAffineRegression.fixed_parameter`
- `C15SymbolicAffineRegression.fixed_face`
- `C15SymbolicAffineRegression.correspondence`
- `C15SymbolicAffineRegression.Fibre`
- `C15SymbolicAffineRegression.fixed_empty`
- `C15SymbolicAffineRegression.fixed_allowed`
- `C15SymbolicAffineRegression.empty_range_iff`
- `C15SymbolicAffineRegression.allowed_range_success`

`AffineFamilyDualClassification.lean` (5明示宣言、source SHA256 `5ffdbd443367b044db0feee0117eb62ba0ce12e3d9afe67722d353f534f3cd95`):

- `NativeAffine.family_obstruction_affine`
- `NativeAffine.family_repair_nonempty_iff_range`
- `NativeAffine.family_repair_nonempty_iff_hits`
- `NativeAffine.family_failed_repair_dual`
- `NativeAffine.family_minimal_repair_iff`

### C15 — 到達点と検証

29選定sourceの同じ実行本体を再現した単一のnamed milestone focused確認はexit0/errors0/warnings0。
240明示宣言に対する個別 `#print axioms` は欠落0、標準公理のみ。
今回の新生成補助は `NativeAffine.familyRelativeLinear.congr_simp` / `NativeAffine.familyTower.congr_simp` の2件。
受理依存の使用先で生成された補助は `ClosedRegion.mk.congr_simp`、`NativeAffine.tower.congr_simp`、`NativeAffine.vectorPath.eq_def`、`NativeAffine.vectorPasting.eq_def`、`StrictCoverRestoration.objectEquiv.congr_simp` の5件。
したがって新API242、使用先の補助込み247件の全個別公理を監査した。log SHA256 `87a975074140d40f932e7f8cd48912ab7b57d8ed95ede56e48071549c5006bac`。
各production sourceも必要な依存順でrootの単一file focused確認を行い、最終実内容で全29が通過した。
査読で名指しされた回帰instance7件のdocstringを追加した。変更は2sourceのコメントと上の2hashだけで、全statement/value/proof/import/guard/宣言集合と台帳statusは不変。元exact-source監査の数学的実行本体を保ち、247個別結果の対応も同じである。
全29source/hash/一意registry行が一致、placeholder/hidden-BiDi/privacy/語彙/import方向/保護領域/diff scanはclean。
Research全体、aggregate root、全file/module loopのelaborationは実行していない。
固定GOAL、数学本文、Formal、共通基準、CI設定は変更しない。

```yaml
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta:
    - "任意元L/reference Rから全vのprimitive実操作、全typedword/linear保持/実δ0+Δvを構成"
    - "完全pastingのbaseline3 law+linear annihilator、baseline固定face+生成P零から全vのlawを生成"
    - "同じ全native M/standard kernel coordinate/inverse/原d0–d2全matrix/full label部分群を同定、同じ原D/F/kernel/生成σを共用"
    - "取得前q(Fz−Bv)=qr0とfullker座標、各v評価fibre/solution/coordinatesの両逆とaffine項の更新を構成"
    - "strictcover/全S/原候補零/full private/全labels、独立native/real修復strict両逆・元値・actual範囲包含との評価交換を接続"
    - "同じ原quotient/candidate列の全v全S span/dual/minimalとactual可否、非零実primitive族/ker自由度/fulllabel/stabilizer回帰を接続"
  exit_criteria_status: ["全parameter実操作/全typed評価/入力law: AffinePrimitiveFamily/ComparisonWords/FamilyLaws", "同じ全M/bases/matrices/labelsと一回生成: ConstantCoefficients/FiniteInput/FamilyLabels/SymbolicNativeLocal", "記号的fullrec/両逆/更新: SymbolicInterface/Action/Updates", "strict全S/実復元/全arrows/元値/包含交換: SymbolicGlobalRestoration/Values/FamilySymbolicCover/Ranges", "非零実success/failure/full自由度: C15AffineFamilyRegression/SymbolicKernelRegression/SymbolicAffineRegression; 標準PR gateはPR作成後に判定"]
  split_reason: none
  completion_candidate: no
  lean_artifacts: ["上記29source/全240明示spine/2新生成補助/5受理使用先補助"]
  evidence: ["全247個別標準公理/29source focused", "全S actual/native/real/symbolic strict両逆とvalue/range APIs", "同じF3²原実入力のempty iff v=0/allowed全v成功", "fullprivate非零/非恒等効果label/非零stabilizer"]
  claim_mapping:
    theorem_names: [family_defect_affine, family_three_law, family_fixed_face, family_local_coefficients, family_vertex_matrix, family_edge_matrix, family_face_matrix, familyNativeSymbolicEquivalence, familyRealSymbolicEquivalence, family_symbolic_range_square, family_repair_nonempty_iff_hits, family_minimal_repair_iff]
    source_labels: ["GOAL E記号的生成と値更新", "GOAL Fの同じ全実affine値更新への適用", "n1017 3.5", "design5"]
    conjuncts: ["上記対応・premise表・spineの全S/同じ元操作/fullkernels/fulllabels/両逆/値差更新"]
    undischarged_assumptions: []
    acceptance_point: "原始実評価から同じgenerator/全S/fullrecまで六義務の構成・接続を閉じた候補。正式PRレビュー/root受理/CIは外部記録で判定"
    port_status: unported
audits:
  premise_delta:
    discharged: ["原始からδ0+Δ/全linear保持/全3lawとP整合", "同じM/bases/full matrices/labels/生成σ", "全evaluation fibre/strictcover/allS/actual objects/full arrows/元値/包含可換", "samequotient/dual/minimalとactual値回帰"]
    remaining: ["固定GOAL E実一点環境/全許容外部文脈iffと内部split、Fの残るE適用、W1–W5、全target別completion gate"]
  certificate_provenance:
    discharged: ["θ族→primitive操作/word実評価→δ0+Δ", "全原M/bases/complete列→受理C11同じgenerated D/F/kernel/σ", "独立real/native repairs→同じbase equation→symbolic全復元", "same original quotient→受理C13 dual/minimal"]
    unresolved: []
  proof_use:
    used: ["hf→family core/alignment/tower", "hthreeとd2η→全parameter実3law", "baselinefixedと生成P零→relative defect", "same original linear transport/basis/finite enums→generator/strict allS/fullrec", "full native value/action laws→strictinverse/range square/real regression"]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: ["29選定exact-source focused exit0/errors0/warnings0", "240明示+2新生成=242新API/5使用補助込み247個別標準公理/欠落0", "axiom log SHA256 87a975074140d40f932e7f8cd48912ab7b57d8ed95ede56e48071549c5006bac", "29原source/hash/registry/placeholder/Unicode/privacy/語彙/import方向/保護/diff整合"]
  blocking_findings: []
  next_obligation: "C15固定headの標準review-pr/math-lean-review/root受理/CI後、Eの実singleton試験と全許容環境の文脈同値へ進む"
```

全GOALの累積完了判定とtracking Issueの全完了checkboxは未達のまま保持し、次の固定義務へ進む。
