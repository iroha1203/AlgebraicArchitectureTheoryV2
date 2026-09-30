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
