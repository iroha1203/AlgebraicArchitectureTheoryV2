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

## 後続の構成義務

Aの部分表示と全次数の制限、相対複体・H0/H1/H2分類、参照座標変更、Bのdescentと
統合障害、Cの有限生成と局所厳密合成、Dの双対分類、Eの更新・文脈同値・分割、
Fの全アフィン実現、W1–W5の全要求と一般定理への接続が必要である。
G-130全体の判定には固定GOALの全完了条件と独立最終査読を用いる。
