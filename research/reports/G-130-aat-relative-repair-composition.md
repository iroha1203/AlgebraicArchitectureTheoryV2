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
