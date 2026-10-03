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

### Cycle 16 selection — 実一点試験から全許容外部文脈の存在同値へ

```yaml
ledger_type: target_cycle_result
goal: G-130-aat-relative-repair-composition
cycle: 16
goal_blob_sha: 8da0fb4eb75d1cb5c37a9d4ddf5e03c18c0bb8a2
base_oid: eecc4443f7b018cf00f6629f43304332dcd2e1ce
tracking_issue: 5132
report_path: research/reports/G-130-aat-relative-repair-composition.md
selection:
  proof_state_ref: "C15 symbolic strict全S復元とC14の独立actual affine修復、Issue5132のC15受理"
  proof_dag_predecessors: ["C11 actual/full-label strict復元", "C14 whole affine primitive/full核座標", "C15 同じ生成器/全S symbolic actual評価", "C13 全候補零と成功復元"]
  milestone: "GOAL E文脈同値とFへの適用: 元Wの全0–3-cellと実操作を保つ禁止平行候補の実一点環境を生成し、Cの候補零/内部候補消去後共有関係の等号 iff 全許容外部環境でのactual修復存在一致を構成"
  proof_obligations:
    - "元有限Wの全typed paths/faces/3-cell contextsを保つ平行辺/恒等face追加と元P embedding、名前・禁止条件を構成"
    - "任意original Lとreference Rから新pin reference τ_t R/core/実transportを生成し、原3 law・全入力条件を保持"
    - "actual affine操作の新face等式とpin禁止から共有補正=tを双方向に証明し、全label/stabilizerを残す"
    - "Cの同じ生成公開関係に候補零を先に課し内部候補を消去した共有関係と独立actual region修復のrangeを同定"
    - "全許容actual外部環境にstrict共有値で貼る存在iffを構成し、actual一点環境の閉包からCtx逆方向を導く"
    - "非零実tester/不能入力と共有label非自明性、内部候補消去の回帰を同じ一般定理へ接続"
  exit_criteria: ["全元0–3 geometry/実L,R/P保持と新禁止pinの由来", "actual singleton共有relationの両方向/fulllabelsを保持", "generated Cとactual range同一・候補零/内部消去の順序", "全S/all actual許容envのCtx iff、閉包を結論certificateとして受け取らない", "具体非零success/failureと標準focused/axiom/PR audit"]
  selection_reason: "記号的実復元の次に固定Eの外部置換判定を閉じる。入力をactual有限affine族に保ち、任意集合testersの仮定で実現義務を消さない"
  expected_result_type: proof-obligation-discharged
  lean_targets: [ParallelPinGeometry, AffineSingletonEnvironment, GeneratedBoundaryRelation, AffineContextEquivalence, C16AffineContextRegression]
  risks: ["全3-cell文脈の脱落", "任意relation testerを仮定するfield逃避", "共有labelの固定/削減", "内部候補値の直接観測", "全許容環境をsingleton族へ縮小", "generic statementだけでnative生成との接続を省略"]
  unchecked: ["C16構成・接続・回帰・レビューはこれから実装", "元internal split/full categorical/complex/holonomy/public-dual保存、指定W1–W5、累積completionは後続"]
```

### C16 — 全元表示の実一点環境と候補消去後の文脈同値

C16の対象は固定GOAL Eの文脈同値とFの有限アフィン族への適用である。
元の全0–3-cell、typed wordの全出現と順序、両pastingの全prefix/suffix/方向/bookends、任意の元Lと基準Rを保持する。
`ParallelPinGeometry`は各元edgeに平行な新candidateと恒等比較のfaceを加え、新しい頂点・3-cellは加えない。
新candidateは全試験で禁止する。旧Pは全cellの埋め込みで保持し、共有頂点を追加で固定しない。
`AffinePinOperations`は元Lを新pinでも用い、基準をτ_tR、linear transportを同じR.linear、coreをπ(RL⁻¹)として実操作から生成する。
元の全face alignmentと完全な3-cell lawから新入力のlawを導く。

`AffineSingletonEnvironment`は独立に指定された元の実修復tから全pin修復を作る。
任意の新環境の実修復では、禁止pinの実値と恒等比較の新face等式から元edgeの実操作がτ_tRに等しくなる。
したがって共有補正rangeは正確に{t}であり、逆向きの実修復も明示する。
`AffinePinLabels`の全label部分群は、旧共有辺の全zero-coboundary条件を満たす元の全頂点vectorである。
非零で効果のないlabelも区別したまま、実conjugation arrowを構成する。

`FinitePresentationEmbedding`は全元cellと全typed word/step/routeの幾何的incidenceを保持する。
`AffineContextInput`は任意の有限な実領域、任意original/reference affine操作、authored比較、元P、全candidate、全共有0–3-cellの厳密な埋め込みを指定する。
そのfieldに修復、relation、singleton、gluing、vanishingを受け取らない。
`AffineSharedLaws`は共有Wのalignment、完全3 law、物理固定face lawを実入力の元word/routeから導く。
従って文脈同値の逆方向で一点環境を生成する際に、それらを追加certificateとして仮定しない。
全環境を表す`Environments S`は任意のこの実領域と全ての整合したwhole候補許可条件の組であり、singleton族への限定ではない。

`GeneratedBoundaryRelation` / `AffineGeneratedBoundary`は受理済みCの同じ生成D/F/kernel/sectionに接続する。
privateは非共有かつ非物理固定かつ非candidateの常時補正辺だけであり、内部candidateも公開座標に保持する。
全candidate零条件を先に課してから、共有座標への射影で内部candidateを消去する。
`AffineSharedCoordinates.sharedEdgeEquiv` / `pull_shared_bijective`により、共有native辺subtypeから元Wの全edge名・全translation方向への引き戻しは全単射である。
`generated_shared_actual`は同じ生成Cが独立actual修復の全共有rangeに正確に等しいことを全許可条件で示す。
生成器と列挙はSの前に固定されている。

`StrictRepairs`は両元領域の独立した全実修復と、全共有edgeの実affine操作の文字通りの等号である。
`boundary_eq_iff` / `strictRepairEquiv`はこの実等号と全共有補正の等号を保存・反映する。
`contextual_generated_strict`は全actual外部環境に対するそのstrict修復存在一致 iff 同じ生成Cの等号を証明する。
`AdmitsPins`は明示した実pin入力とその候補許可条件が環境族に属するという原始追加の許容条件であり、singleton relationの存在はfieldに入れない。
`pin_environment_range`で実singletonを導き、`contextual_generated_family_all`はこの原始追加を許す各族の全実環境と全Sに同じ判定を適用する。
C16の文脈claimは共有補正の実現可能集合による存在判定である。

| Material premise | 種類・生成元 | 実使用と到達先 |
| --- | --- | --- |
| 任意finite全元表示/実L,R/全translation核/全W共有 | ambient-boundary、既存Fとfull typed embedding | 元word実評価、実修復制限、whole環境量化とfull pullback |
| authored全face alignment/完全3 law/元P-fixed law | 元入力の条件。共有lawはAffineSharedLawsで導出 | primitive pin referenceのlaw、元W修復、一点環境の全入力成立 |
| actual一点環境/共有relation={t} | discharge-required、ParallelPinsの実新操作と恒等faceから構成 | contextual_rangesの逆方向。任意Setのtesterを仮定しない |
| 新pin禁止/元candidate名/全候補零 | primitive許可条件と元incidenceから導出 | actual強制等式、same generatorのBoundaryPublicZero、内部candidate消去 |
| 同じ生成Cとactual共有rangeの一致 | discharge-required、受理Cの生成section/全kernelとwhole actual equation equivalence | generated_boundary_actual→generated_shared_actual→全Ctx |
| strict共有実操作の等号 | 実貼り合わせの定義。correctionとの対応はboundary_eq_iffで証明 | strictRepairEquiv、strict存在とrange交差、全外部存在iff |
| 環境族の原始有限pin追加許容 | direction-hypothesis、AdmitsPinsは明示inputの所属だけ | hfは構成したpinEnvironmentの所属に使用、range lawは別証明 |
| 全labels/stabilizersの保持 | discharge-required、pinLabelEquivalence/wholeLabelArrow | 各元vertex値・実conjugation。共有頂点を追加固定しない |

C16の具体入力は二系統である。
`C16AffinePinRegression` / `C16AffineContextRegression`は元F3²の非恒等shear、異なる元L/R、非零共有値x、元faceの正・逆両出現を含む非空3-cellを保持する。
実whole環境の非零修復、零共有値の不能、非零full stabilizer arrowを示し、全actual環境型と一般Ctx定理へ接続する。
`C16CandidateGeometry` / `Repairs` / `ContextRegression` / `Generated`はF3の元共有辺zと内部candidate yにz=yまたはz=2yという異なる実wordを指定する。
candidate禁止後は両共有関係が{0}、解禁後は全共有vectorとなる。内部値1を保持すると共有値1と2で異なることも証明する。
同じ原生成器によるCの一致と、全actual外部環境のstrict存在一致を一般定理へ接続する。
これらは指定W1–W5の代替ではない。

### C16 — 受理spine declaration list

全名の共通prefixは `AAT.AG.RelativeRepairComposition.`。各sourceの明示宣言と元source hashを固定する。

`ParallelPinGeometry.lean` (15明示宣言、source SHA256 `cc03f9a9c9669bfe62805ec04439bc6fbf8e7a4e796ff89ff21823142685daa9`):

- `ParallelPinGeometry.Edge`
- `ParallelPinGeometry.includePath`
- `ParallelPinGeometry.include_append`
- `ParallelPinGeometry.skeleton`
- `ParallelPinGeometry.includeFace`
- `ParallelPinGeometry.include_local_before`
- `ParallelPinGeometry.include_local_after`
- `ParallelPinGeometry.include_before`
- `ParallelPinGeometry.include_after`
- `ParallelPinGeometry.includeStep`
- `ParallelPinGeometry.includePasting`
- `ParallelPinGeometry.presentation`
- `ParallelPinGeometry.oldEdgeName`
- `ParallelPinGeometry.pinEdgeName`
- `ParallelPinGeometry.old_ne_pin`

`ParallelPinIncidence.lean` (6明示宣言、source SHA256 `1bcf874c71de12aa2071c9c9bfdbe2f8f72b85a96c4cec2f6c9a780a18aefe65`):

- `ParallelPinGeometry.included_path_edges`
- `ParallelPinGeometry.included_pasting_faces`
- `ParallelPinGeometry.included_pasting_context`
- `ParallelPinGeometry.oldRegion`
- `ParallelPinGeometry.pin_not_fixed`
- `ParallelPinGeometry.old_fixed_vertices`

`AffinePinOperations.lean` (12明示宣言、source SHA256 `74e6ed5f9ae5f945f1aba478a498090ce10f72a5d5e912a9281ed25b2d1b76f4`):

- `NativeAffine.ParallelPins.extendOperation`
- `NativeAffine.ParallelPins.oldOperation`
- `NativeAffine.ParallelPins.included_word_value`
- `NativeAffine.ParallelPins.comparison`
- `NativeAffine.ParallelPins.reference`
- `NativeAffine.ParallelPins.original`
- `NativeAffine.ParallelPins.pin_linear`
- `NativeAffine.ParallelPins.pin_core_projection`
- `NativeAffine.ParallelPins.reference_faces`
- `NativeAffine.ParallelPins.included_face_value`
- `NativeAffine.ParallelPins.included_pasting_value`
- `NativeAffine.ParallelPins.reference_three_law`

`AffineSingletonEnvironment.lean` (7明示宣言、source SHA256 `e103183eae99782b5a73da7884554f0a0bd8c72467f81a6ee3d5d9d0bc79675b`):

- `NativeAffine.ParallelPins.forbidden`
- `NativeAffine.ParallelPins.restrictRepair`
- `NativeAffine.ParallelPins.singletonRepair`
- `NativeAffine.ParallelPins.forced_old_operation`
- `NativeAffine.ParallelPins.singleton_correction`
- `NativeAffine.ParallelPins.singleton_boundary`
- `NativeAffine.ParallelPins.restrict_singleton`

`AffinePinLabels.lean` (7明示宣言、source SHA256 `bdc9902d4fc2ff93fbf38d1c497507c762736e683a46ffe7787c512990a47ccf`):

- `NativeAffine.ParallelPins.pin_label_conditions`
- `NativeAffine.ParallelPins.pin_label_subgroup`
- `NativeAffine.ParallelPins.pinLabelEquivalence`
- `NativeAffine.ParallelPins.pin_label_value`
- `NativeAffine.ParallelPins.whole_label_stabilizes`
- `NativeAffine.ParallelPins.wholeLabelArrow`
- `NativeAffine.ParallelPins.whole_label_arrow_value`

`GeneratedBoundaryRelation.lean` (7明示宣言、source SHA256 `7a1fedaa0db10a87c44c3285fdb79a8ea2d9f6a07370ca63823445e3ba6f9153`):

- `FiniteNative.boundaryPublicValue`
- `FiniteNative.restored_boundary_value`
- `FiniteNative.BoundaryPublicZero`
- `FiniteNative.BoundaryRelation`
- `FiniteNative.supportedBoundary`
- `FiniteNative.boundary_relation_range`

`AffinePinCandidates.lean` (6明示宣言、source SHA256 `1e15bf11928c6141a8cf5df68302155948b29c261bad873e1e730566e2ed2449`):

- `NativeAffine.ParallelPins.candidates`
- `NativeAffine.ParallelPins.allowed`
- `NativeAffine.ParallelPins.old_name_injective`
- `NativeAffine.ParallelPins.pin_never_allowed`
- `NativeAffine.ParallelPins.fixed_range_eq`
- `NativeAffine.ParallelPins.allowed_mono`

`AffineGeneratedBoundary.lean` (12明示宣言、source SHA256 `c5b3a6d9e954e6d38520b88395751e0ee36fe1f828c8bf52e5912aef7c1a6fe7`):

- `NativeAffine.privateNonshared`
- `NativeAffine.allVerticesDecidable`
- `NativeAffine.allEdgesDecidable`
- `NativeAffine.allFacesDecidable`
- `NativeAffine.privateEdgesDecidable`
- `NativeAffine.boundaryVector`
- `NativeAffine.generatedBoundary`
- `NativeAffine.boundaryEquationEquiv`
- `NativeAffine.boundary_equation_value`
- `NativeAffine.boundary_equation_inverse_value`
- `NativeAffine.actualBoundary`
- `NativeAffine.generated_boundary_actual`

`C16AffinePinRegression.lean` (23明示宣言、source SHA256 `93a17ff92dc6d8087e6cec76265b3571ebf9d7702ca844b158336efbd4c61383`):

- `C16AffinePinRegression.forwardFace`
- `C16AffinePinRegression.backwardFace`
- `C16AffinePinRegression.geometry`
- `C16AffinePinRegression.references`
- `C16AffinePinRegression.originals`
- `C16AffinePinRegression.comparisons`
- `C16AffinePinRegression.fixed`
- `C16AffinePinRegression.sharedRepair`
- `C16AffinePinRegression.original_three`
- `C16AffinePinRegression.aligned`
- `C16AffinePinRegression.false_correction`
- `C16AffinePinRegression.true_repaired_value`
- `C16AffinePinRegression.true_correction`
- `C16AffinePinRegression.testRepair`
- `C16AffinePinRegression.test_three`
- `C16AffinePinRegression.every_test_true`
- `C16AffinePinRegression.zero_boundary_failure`
- `C16AffinePinRegression.whole_label_x`
- `C16AffinePinRegression.nonzeroTestLabel`
- `C16AffinePinRegression.test_label_not_zero`
- `C16AffinePinRegression.test_label_y_forbidden`
- `C16AffinePinRegression.nonzeroSharedArrow`
- `C16AffinePinRegression.shared_arrow_not_zero`

`ContextRelations.lean` (5明示宣言、source SHA256 `d8e1a3d058730dd1e7ee852d949e85e0795006c674edbb7986098598abecb628`):

- `ContextRelations.StrictJoin`
- `ContextRelations.strict_join_nonempty`
- `ContextRelations.equal_relations_context`
- `ContextRelations.contextual_iff_equal`
- `ContextRelations.contextual_ranges`

`FinitePresentationEmbedding.lean` (5明示宣言、source SHA256 `4dc3625c65c7f3450df1be3557d8b69981884673b2fb8a853c22d52c0d0276bf`):

- `embeddedPath`
- `FinitePresentationEmbedding`
- `FinitePresentationEmbedding.edgeName`
- `FinitePresentationEmbedding.path_computed`
- `FinitePresentationEmbedding.path_map_append`

`ParallelPinEmbedding.lean` (1明示宣言、source SHA256 `c8355a9601532c1cbaabbeba373c96019abbd6ef0a2f1d045591363acd41fe36`):

- `ParallelPinGeometry.embedding`

`AffineEmbeddedValues.lean` (5明示宣言、source SHA256 `3687f4b6b27d35015f13c94d04313c5b71a5e18d44641a8220da81e8415cabf1`):

- `NativeAffine.embeddedOperation`
- `NativeAffine.embedded_word_value`
- `NativeAffine.word_value_heq`
- `NativeAffine.restrictEmbeddedRepair`
- `NativeAffine.embedded_correction_value`

`AffineContextInput.lean` (7明示宣言、source SHA256 `2c9c3a2af458f12516990735f328d2b295538517ff2b11e957ddb4291d21b2d6`):

- `NativeAffine.AffineContextInput`
- `NativeAffine.AffineContextInput.Range`
- `NativeAffine.AffineContextInput.Repairs`
- `NativeAffine.AffineContextInput.shared_forbidden`
- `NativeAffine.AffineContextInput.sharedRepair`
- `NativeAffine.AffineContextInput.boundary`
- `NativeAffine.AffineContextInput.boundary_value`

`AffineEmbeddedPastings.lean` (6明示宣言、source SHA256 `cf10f05b9843e83180c8d7317b98a06ca2efed24152ead59edc16ce8f7f16649`):

- `NativeAffine.embedded_reference_family`
- `NativeAffine.embedded_reference_word`
- `NativeAffine.embedded_step_comparison`
- `NativeAffine.embedded_pasting_value`
- `NativeAffine.pasting_value_heq`
- `NativeAffine.embedded_three_law`

`AffinePinContextInput.lean` (8明示宣言、source SHA256 `7c0ffc008ff881f5da6950d396ecb1cf6705d02bb59704b6e7d51a2905d5a7cc`):

- `NativeAffine.ParallelPins.contextInput`
- `NativeAffine.ParallelPins.contextRange`
- `NativeAffine.ParallelPins.context_fixed_set`
- `NativeAffine.ParallelPins.rawContextRepair`
- `NativeAffine.ParallelPins.contextRepair`
- `NativeAffine.ParallelPins.context_shared_operation`
- `NativeAffine.ParallelPins.context_shared_repair`
- `NativeAffine.ParallelPins.context_singleton_range`

`AffineSharedLaws.lean` (3明示宣言、source SHA256 `9ac9d6868aa9ae052eab8603d09bd5a158655138434c07fa0bf4648b3844acc4`):

- `NativeAffine.AffineContextInput.shared_aligned`
- `NativeAffine.AffineContextInput.shared_three_law`
- `NativeAffine.AffineContextInput.shared_fixed_law`

`AffineContextEquivalence.lean` (4明示宣言、source SHA256 `df3b5f305321f05f1bddc866ddb02d29e3f5abcf0bdc350ee47da667a6c3d246`):

- `NativeAffine.AffineContextInput.Environments`
- `NativeAffine.AffineContextInput.actual_singleton_context`
- `NativeAffine.AffineContextInput.contextual_actual_ranges`
- `NativeAffine.AffineContextInput.contextual_all_ranges`

`AffineSharedCoordinates.lean` (4明示宣言、source SHA256 `2a95a7cbafd828bf6c15d336d8a1467b5705753773a60ea20572c4c12815ddd2`):

- `FinitePresentationEmbedding.edge_name_injective`
- `NativeAffine.AffineContextInput.sharedEdgeEquiv`
- `NativeAffine.AffineContextInput.pullShared`
- `NativeAffine.AffineContextInput.pull_shared_bijective`

`AffineContextGenerated.lean` (4明示宣言、source SHA256 `415b49b77daead19cfc4aaae4e9ca59b7d030fc268c64b4b8136f77e9a098035`):

- `NativeAffine.AffineContextInput.generatedShared`
- `NativeAffine.AffineContextInput.generated_shared_actual`
- `NativeAffine.AffineContextInput.contextual_generated`
- `NativeAffine.AffineContextInput.contextual_generated_all`

`AffineStrictContexts.lean` (5明示宣言、source SHA256 `ead4df72973f44fb5016c1d74cb9a54df7b938f62d132b41c64b2cfe5d1e2618`):

- `NativeAffine.AffineContextInput.StrictRepairs`
- `NativeAffine.AffineContextInput.boundary_eq_iff`
- `NativeAffine.AffineContextInput.strictRepairEquiv`
- `NativeAffine.AffineContextInput.strict_repairs_nonempty`
- `NativeAffine.AffineContextInput.contextual_strict_actual`

`AffineContextFamilies.lean` (7明示宣言、source SHA256 `f9b47955921e2d7d98ab269173f08498d0e7630a4b1dbe5b8d25952c92cf2f4e`):

- `NativeAffine.AffineContextInput.pinEnvironment`
- `NativeAffine.AffineContextInput.pin_environment_range`
- `NativeAffine.AffineContextInput.AdmitsPins`
- `NativeAffine.AffineContextInput.all_admits_pins`
- `NativeAffine.AffineContextInput.contextual_family_ranges`
- `NativeAffine.AffineContextInput.contextual_family_strict`

`C16CandidateGeometry.lean` (14明示宣言、source SHA256 `a4ab330f2b42b8c0920aae39f718bba9bfe0a33e4a013f5cc6a1f051333522ba`):

- `C16CandidateGeometry.boundaryGeometry`
- `C16CandidateGeometry.geometry`
- `C16CandidateGeometry.edgeEquality`
- `C16CandidateGeometry.includePath`
- `C16CandidateGeometry.includeRoute`
- `C16CandidateGeometry.embedding`
- `C16CandidateGeometry.shared`
- `C16CandidateGeometry.candidates`
- `C16CandidateGeometry.V`
- `C16CandidateGeometry.boundaryReference`
- `C16CandidateGeometry.reference`
- `C16CandidateGeometry.aligned`
- `C16CandidateGeometry.input`
- `C16CandidateGeometry.permissions`

`C16CandidateRepairs.lean` (8明示宣言、source SHA256 `85f3bf490f70df62adab1217443c2f95920c7cb5acb5f2a2fc1a394e055aeb44`):

- `C16CandidateRepairs.scale`
- `C16CandidateRepairs.scaled`
- `C16CandidateRepairs.scaled_inverse`
- `C16CandidateRepairs.operations`
- `C16CandidateRepairs.forbidden`
- `C16CandidateRepairs.repair`
- `C16CandidateRepairs.repair_internal`
- `C16CandidateRepairs.repair_boundary`

`C16CandidateContextRegression.lean` (8明示宣言、source SHA256 `cab10937f0e388178c0b29a75c3209ec66d064658b99b509bd223cdc368d0e43`):

- `C16CandidateContextRegression.forbidden_shared_operation`
- `C16CandidateContextRegression.forbidden_boundary`
- `C16CandidateContextRegression.forbidden_range`
- `C16CandidateContextRegression.allowed_range`
- `C16CandidateContextRegression.boundary_ranges_equal`
- `C16CandidateContextRegression.every_actual_context`
- `C16CandidateContextRegression.internal_one_retained`
- `C16CandidateContextRegression.internal_relations_different`

`C16AffineContextRegression.lean` (17明示宣言、source SHA256 `2b334cb368634da76e8478dd7cf790f5109231bd2da602c190b1dabb915cdfeb`):

- `C16AffineContextRegression.allowed`
- `C16AffineContextRegression.fixed_condition`
- `C16AffineContextRegression.baseRepair`
- `C16AffineContextRegression.fixed_law`
- `C16AffineContextRegression.input`
- `C16AffineContextRegression.permissions`
- `C16AffineContextRegression.actualRepair`
- `C16AffineContextRegression.actual_true`
- `C16AffineContextRegression.actual_zero_failure`
- `C16AffineContextRegression.actual_label_conditions`
- `C16AffineContextRegression.actualLabel`
- `C16AffineContextRegression.actual_label_nonzero`
- `C16AffineContextRegression.actualArrow`
- `C16AffineContextRegression.actual_arrow_nonzero`
- `C16AffineContextRegression.environment`
- `C16AffineContextRegression.actual_contextual`

`AffineContextConclusion.lean` (3明示宣言、source SHA256 `2ec675e509cf120d31e9bf676707266d5122e202bfb9195a8d9825b827bc6be8`):

- `NativeAffine.AffineContextInput.contextual_generated_strict`
- `NativeAffine.AffineContextInput.contextual_generated_family`
- `NativeAffine.AffineContextInput.contextual_generated_family_all`

`C16CandidateGenerated.lean` (15明示宣言、source SHA256 `09b7bce08fddac7bd045e6ff0a787620c7e8bca6e41952562fe6a80f8c00d8f2`):

- `C16CandidateGenerated.edgeEquality`
- `C16CandidateGenerated.faceEquality`
- `C16CandidateGenerated.fixedEdgesDecidable`
- `C16CandidateGenerated.fixedFacesDecidable`
- `C16CandidateGenerated.sharedDecidable`
- `C16CandidateGenerated.candidateDecidable`
- `C16CandidateGenerated.fieldValues`
- `C16CandidateGenerated.edges`
- `C16CandidateGenerated.faces`
- `C16CandidateGenerated.relation`
- `C16CandidateGenerated.relation_actual`
- `C16CandidateGenerated.relations_equal`
- `C16CandidateGenerated.generated_contextual`

査読で名指しされた公開API・正負例として、次の6補助宣言を追加する。

- `NativeAffine.real_correction_value`
- `FiniteNative.boundary_public_zero_zero`
- `NativeAffine.AffineContextInput.not_admits_pins_empty_of_repair`
- `C16AffineContextRegression.not_admits_pins_empty`
- `C16CandidateGenerated.boundary_public_zero_zero`
- `C16CandidateGenerated.boundary_public_zero_rejects_internal_one`

既存所有source `NativeAffineCorrection.lean` (5明示宣言、source SHA256 `4bd3a03107254b859a6586aeafbd3bf2d929fa0ae499fb49c8fc5eb4dab9430a`) では、raw評価APIを追加し、C16の三箇所は同じ評価APIを使用する。元4受理宣言も同じ選定監査本体に含める。

- `NativeAffine.native_repair_correction_value`
- `NativeAffine.realCorrection`
- `NativeAffine.real_correction_native`
- `NativeAffine.real_correction_restore`

追加の個別公理対象は次の93件である。型付きembedding/actual入力/permissionの全structure生成APIと新word再帰補助91件、受理依存の使用先補助2件を含む。

- `ClosedRegion.mk.congr_simp`
- `FinitePresentationEmbedding.casesOn`
- `FinitePresentationEmbedding.ctorIdx`
- `FinitePresentationEmbedding.edge`
- `FinitePresentationEmbedding.edge_injective`
- `FinitePresentationEmbedding.face`
- `FinitePresentationEmbedding.face_injective`
- `FinitePresentationEmbedding.face_left`
- `FinitePresentationEmbedding.face_right`
- `FinitePresentationEmbedding.face_source`
- `FinitePresentationEmbedding.face_target`
- `FinitePresentationEmbedding.mk`
- `FinitePresentationEmbedding.mk.inj`
- `FinitePresentationEmbedding.mk.injEq`
- `FinitePresentationEmbedding.mk.noConfusion`
- `FinitePresentationEmbedding.mk.sizeOf_spec`
- `FinitePresentationEmbedding.noConfusion`
- `FinitePresentationEmbedding.noConfusionType`
- `FinitePresentationEmbedding.path`
- `FinitePresentationEmbedding.path_cons`
- `FinitePresentationEmbedding.path_nil`
- `FinitePresentationEmbedding.rec`
- `FinitePresentationEmbedding.recOn`
- `FinitePresentationEmbedding.route`
- `FinitePresentationEmbedding.route_cons`
- `FinitePresentationEmbedding.route_nil`
- `FinitePresentationEmbedding.step`
- `FinitePresentationEmbedding.step_face`
- `FinitePresentationEmbedding.step_incoming`
- `FinitePresentationEmbedding.step_orientation`
- `FinitePresentationEmbedding.step_outgoing`
- `FinitePresentationEmbedding.triple`
- `FinitePresentationEmbedding.triple_finish`
- `FinitePresentationEmbedding.triple_injective`
- `FinitePresentationEmbedding.triple_left`
- `FinitePresentationEmbedding.triple_right`
- `FinitePresentationEmbedding.triple_source`
- `FinitePresentationEmbedding.triple_start`
- `FinitePresentationEmbedding.triple_target`
- `FinitePresentationEmbedding.vertex`
- `FinitePresentationEmbedding.vertex_injective`
- `NativeAffine.AffineContextInput.Range.allowed`
- `NativeAffine.AffineContextInput.Range.casesOn`
- `NativeAffine.AffineContextInput.Range.ctorIdx`
- `NativeAffine.AffineContextInput.Range.mk`
- `NativeAffine.AffineContextInput.Range.mk.congr_simp`
- `NativeAffine.AffineContextInput.Range.mk.inj`
- `NativeAffine.AffineContextInput.Range.mk.injEq`
- `NativeAffine.AffineContextInput.Range.mk.noConfusion`
- `NativeAffine.AffineContextInput.Range.mk.sizeOf_spec`
- `NativeAffine.AffineContextInput.Range.noConfusion`
- `NativeAffine.AffineContextInput.Range.noConfusionType`
- `NativeAffine.AffineContextInput.Range.rec`
- `NativeAffine.AffineContextInput.Range.recOn`
- `NativeAffine.AffineContextInput.Range.shared_allowed`
- `NativeAffine.AffineContextInput.aligned`
- `NativeAffine.AffineContextInput.candidates`
- `NativeAffine.AffineContextInput.casesOn`
- `NativeAffine.AffineContextInput.comparisons`
- `NativeAffine.AffineContextInput.ctorIdx`
- `NativeAffine.AffineContextInput.embedding`
- `NativeAffine.AffineContextInput.fixed`
- `NativeAffine.AffineContextInput.fixed_faces`
- `NativeAffine.AffineContextInput.geometry`
- `NativeAffine.AffineContextInput.mk`
- `NativeAffine.AffineContextInput.mk.inj`
- `NativeAffine.AffineContextInput.mk.injEq`
- `NativeAffine.AffineContextInput.mk.noConfusion`
- `NativeAffine.AffineContextInput.mk.sizeOf_spec`
- `NativeAffine.AffineContextInput.noConfusion`
- `NativeAffine.AffineContextInput.noConfusionType`
- `NativeAffine.AffineContextInput.originals`
- `NativeAffine.AffineContextInput.rec`
- `NativeAffine.AffineContextInput.recOn`
- `NativeAffine.AffineContextInput.references`
- `NativeAffine.AffineContextInput.shared`
- `NativeAffine.AffineContextInput.shared_candidates`
- `NativeAffine.AffineContextInput.shared_comparison`
- `NativeAffine.AffineContextInput.shared_core`
- `NativeAffine.AffineContextInput.shared_edges`
- `NativeAffine.AffineContextInput.shared_faces`
- `NativeAffine.AffineContextInput.shared_fixed_edges`
- `NativeAffine.AffineContextInput.shared_fixed_faces`
- `NativeAffine.AffineContextInput.shared_fixed_triples`
- `NativeAffine.AffineContextInput.shared_fixed_vertices`
- `NativeAffine.AffineContextInput.shared_reference`
- `NativeAffine.AffineContextInput.shared_triples`
- `NativeAffine.AffineContextInput.shared_vertices`
- `NativeAffine.AffineContextInput.three_law`
- `ParallelPinGeometry.includePasting.eq_def`
- `ParallelPinGeometry.includePath.eq_def`
- `embeddedPath.eq_def`
- `pathEdges.eq_def`

### C16 — 到達点と検証

28新productionと評価APIの既存所有sourceのroot単一file focused確認は、現在のsource hashで全29がexit0/errors0/warnings0。
それらの同じ元実行本体を再現した単一named milestone focused確認もexit0/errors0/warnings0。
225新明示宣言と91新生成API、既存所有sourceの4受理宣言と2使用先補助の計322件の個別 `#print axioms` は欠落0・標準公理のみ。
公理log SHA256 `f7fdf0022da13b82c481aec8e1b02502c728ffa70d3cf1df36707e9eb945bd27`、再現source SHA256 `c0d437e4e7fd63d4eb4b2be26193ad5e932c134be453010eb5301bedba37a805`。
29原source/hash/一意registry行、placeholder/hidden-BiDi/privacy/語彙(imported identifierと数学座標語を区別し、新規地の文のAAT hard ruleも含む)/import方向/保護領域/diff scanは一致・clean。
Research全体、aggregate root、全file/module loopのelaborationは実行していない。
固定GOAL、数学本文、Formal、共通基準、CI設定は変更しない。

```yaml
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta:
    - "全元0–3-cell/typed word/両完全route/P/nameを保つ原始parallel pin追加を構成"
    - "任意元L/Rから新reference τ_tR/同じcore/fulltransportと全新入力lawを導出"
    - "actual恒等face/pin禁止からsingleton range両方向を構成、元full labels/実stabilizerを保持"
    - "同じ生成D/F/kernel/sectionで全候補零→内部候補消去→full共有C=独立actual rangeを全Sで証明"
    - "全actual env/whole compatible permissionsの元実操作strict存在一致 iff C等号、原始pin追加許容族/全Sへ接続"
    - "F3²非零shear/非空3-cell/実不能/full stabilizer、F3内部candidate関係差と生成C/全Ctx回帰を構成"
  exit_criteria_status: ["元全geometry/任意L,R/P/name/新pin由来: ParallelPinGeometry/Incidence/Operations", "actual singleton両方向/全labels: AffineSingletonEnvironment/PinContextInput/PinLabels", "同じ生成C/候補零と内部消去: GeneratedBoundaryRelation/AffineGeneratedBoundary/ContextGenerated", "全S/全actual env iffとprimitive許容族: AffineContextEquivalence/Families/StrictContexts/Conclusion", "非零success/failure/非空3/full stabilizer/内部消去: C16の両actual回帰、29focused/322個別公理; 正式PR gateはPR作成後に判定"]
  split_reason: none
  completion_candidate: no
  lean_artifacts: ["28新sourceと既存所有source/225新明示/91新生成/6受理宣言・使用先補助"]
  evidence: ["全322個別標準公理/29source focused", "原新pin実operation/restoration/alllabels", "same generator candidatezero-before-projection/full shared actualrange", "全actual envとprimitive追加許容族の全S strict existence iff", "F3²非零shear/full3/stabilizerとF3 candidate elimination"]
  claim_mapping:
    theorem_names: [reference_three_law, singleton_correction, pinLabelEquivalence, context_singleton_range, shared_three_law, generated_boundary_actual, generated_shared_actual, pull_shared_bijective, boundary_eq_iff, strictRepairEquiv, contextual_generated_strict, contextual_generated_family_all, every_actual_context, generated_contextual]
    source_labels: ["固定GOAL E文脈同値", "固定GOAL Fの同じ有限affine族へのE文脈適用", "n1017 3.2", "design5"]
    conjuncts: ["全元実操作/全cell/名前/元P/全S/候補零先行/内部消去/全環境/実singleton/原始許容閉包/全labels"]
    undischarged_assumptions: []
    acceptance_point: "C16六義務と五終了条件の構成・接続を閉じた候補。正式PRレビュー/root受理/CIは外部記録で判定"
    port_status: unported
audits:
  premise_delta:
    discharged: ["原始pin追加から全実入力lawとactual singleton", "全0–3共有/実制限/全label値", "same generated C候補零/内部消去/fullactualrange", "全actualenv/原始許容族/全S iffと非零・内部候補回帰"]
    remaining: ["固定GOAL E内部splitの全一般可換核/categorical/fullcomplex/holonomy/public-dual保存", "Fの残る内部split適用", "指定W1–W5", "全target累積completion packetと別四本監査"]
  certificate_provenance:
    discharged: ["元typedcell/原L,R→pin操作/全law", "元actual修復→新全actual修復とsingleton評価", "same original wholematrix/section→candidatezero→sharedprojection", "fulltyped embedding→whole actual制限と共有laws", "actualsingleton→任意外部存在逆方向"]
    unresolved: []
  proof_use:
    used: ["元hf/hthree→pin全law", "P閉性とfixedlaw→新元P/actualrange", "同じgenσ/complete kernel→boundary restoration", "全Wreference/cmp/incidence→actual restriction/operation equality", "原始pin許容→constructed actualEnv membership→Ctx逆方向"]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: ["29選定production/同じnamed milestone focused exit0/errors0/warnings0", "全322個別標準公理/欠落0", "axiom log SHA256 f7fdf0022da13b82c481aec8e1b02502c728ffa70d3cf1df36707e9eb945bd27", "全source/hash/registry/static scans"]
  blocking_findings: []
  next_obligation: "C16固定headの標準review-pr/math-lean-review/root受理/CI後、Eの内部always辺分割を元一般可換核/全geometry/実補正から構成"
```

全GOALの累積完了判定とtracking Issueの全完了checkboxは未達のまま保持し、固定義務の続きを扱う。

### Cycle 17 selection — 元の実分割から全範囲の修復同値とW4へ

```yaml
ledger_type: target_cycle_result
goal: G-130-aat-relative-repair-composition
cycle: 17
goal_blob_sha: 8da0fb4eb75d1cb5c37a9d4ddf5e03c18c0bb8a2
base_oid: ba04a598195b5d85f11a19938a7e8be14ed0b4c0
tracking_issue: 5132
report_path: research/reports/G-130-aat-relative-repair-composition.md
selection:
  proof_state_ref: "C16全actual文脈とC1–C15の原全核/全label修復、Issue5132のC16受理"
  proof_dag_predecessors: ["C1–C3 原修復/候補/相対分類", "C4–C5 全元閉表示とstrict制限", "C11 全label原実復元", "C14–C16 whole affine実現/原始環境", "G129 原塔と実核輸送合成"]
  milestone: "固定GOAL Eの可換群入力で、常時補正可能な元内部辺の実二因子からK'を生成し、全Sで元全label実修復の関手・逆・自然同型と全復元を構成する。厳密W/包含/外部strict合成を保持し、指定W4の自由新頂点と固定新頂点の差へ接続する"
  proof_obligations:
    - "元全typed path/face/3-cell上下文・両routeの全出現を置換し、名前/P/W/candidate保持を生成"
    - "同じ実塔の中間対象/二因子と許された原始strong/bijective条件から新original塔を生成し、実核輸送rho=rho2rho1/新核可換性/全入力lawを導出"
    - "実合成からhe=h2+rho2h1、全置換語と修復条件の双方向、旧original Lに対する実choice復元と任意h1による全分割補正を構成"
    - "全object/全arrowのcollapseと逆、newlabel=h1の自然同型、Homの一意liftを生成し、全Sで同じ式/厳密W/範囲包含/外部strict合成を証明"
    - "指定F3 W4へ適用し実修復3→9、同型類3/自明Aut、全(u,v)復元と新頂点固定時の別入力9同型類を構成"
  exit_criteria: ["元全0–3 geometry/P/W/candidateの計算構成", "実因子から全新核/transport/原lawの生成", "原全label categorical同値/逆/自然性/Hom両方向", "全S/厳密W/包含/外部strict/全分割復元", "同じ一般定理へのW4実値・個数・再同定接続とfocused/個別axiom/PR gate"]
  selection_reason: "C16の外部置換判定を受理したので、Eのもう一つの原構造置換を閉じる。complex/全H/障害/旧holonomy/公開双対/極小範囲の保存はこの同じ構成を入力とする後続到達点に残す"
  expected_result_type: proof-obligation-discharged
  lean_targets: [SubdivisionGeometry, SubdivisionOriginalTower, SubdivisionRepairEquivalence, C17SplitRegression]
  risks: ["端点付き名前の脱落", "任意oldLをreferenceと同一視", "原3-cell上下文の欠落", "新核可換性の追加仮定", "Homを自分の像へ縮小", "新頂点の固定", "同値結論のinput field化"]
  unchecked: ["C17構成/接続/回帰/監査はこれから実装", "同じ分割の複体/障害/全H/旧holonomy/公開双対/極小保存、残F適用と指定W1–W5、累積completionは後続"]
```

### C17 — 元の実二因子から全修復・全再同定を構成

`Subdivision.Factorization` は同じ元塔の中間対象・二実射・実積と、GOAL Eが課すstrong条件・全核輸送の全単射性だけを受け取る。
第一輸送の全射性から新対象の全核の可換性を導き、実transport squareの一意性から `transport_comp` を証明した。
`presentation` は元の完全な辺名を新しい型付き辺へ保持し、選んだ辺の全出現を二辺へ置換する。
全2-cell名・全経路、全3-cell名・両route・各faceのincoming/outgoing wordを保持する。
閉じた元P/Wは `oldRegion` へ移し、新頂点も両因子も固定部分・候補集合へ追加しない。
任意の元original Lとreference Rを区別したまま、新原塔の全fieldを実射から構成する。

| 固定義務 | 構成・両方向の証拠 | 対象・量化 |
| --- | --- | --- |
| 元全geometry/実核輸送/新入力law | `presentation`, `oldRegion`, `middle_kernel_comm`, `transport_comp`, `originalTower`, `three_laws`, `fixed_face_laws` | 任意元可換全核、同じ実塔、全型付き経路と全0–3-cell |
| 実補正縮約と任意第一補正の全復元 | `corrected_factor_product`, `collapseCorrection_chosen`, `correctionEquiv`, `solutionEquiv`, `supportedSolutionEquiv`, `solution_path_substitute` | 全新独立actual修復、全旧actual修復、全新対象核値、任意original L |
| 全label圏同値/逆/自然同型 | `collapseHomEquiv`, `expandFunctor`, `collapseFunctor`, `unitIso`, `counitIso`, `equivalence` | 全actual objectsと全actual morphisms、全old labels、forced fresh labelの一意lift |
| 全S/包含/共有W/外部strict合成 | `rangeEquivalence`, `collapse_supported_inclusion`, `expand_supported_inclusion`, `collapse_label_inclusion`, `zero_section_inclusion`, `shared_collapse`, `shared_expand`, `externalObjectEquiv`, `externalHomEquiv`, `native_external_counit_shared`, `native_external_unit_shared` | 同じ全Sの式、全元W実choice、任意外部objects/arrowsと全共有label一致 |
| 同じ一般定理への指定W4接続 | `C17SubdivisionInput.splitRepairEquiv`, `restore_pair_coordinates`, `old_repair_card`, `new_repair_card`, `old_class_card`, `new_class_card`, `old_aut_identity`, `new_aut_identity`, `closed_fixed_new_class_card` | F3の指定flip辺/比較−1/二指定因子、全独立修復、全同型類、全Aut |

共有値 `sharedNew` は新actual修復から保持された元辺のchoiceを直接読む。
縮約による共有値の定義で結論を埋めず、両方向のliteral equalityを証明する。
外部objectsのstrict貼合せは元strict objectsと新対象の全核との積に相互に対応し、全compatible arrowsの一意liftは外部arrowをそのまま保つ。
unit/counitの全旧vertex labelは零であり、任意native external identityのlabel零を実群oidから導く。

W4の元full affine operationは `a(x)=-x+h, b(x)=x+1` と独立に定義・分類した。
元修復3件、新修復9件、両方の全同型類3件、全Autが恒等である。
同じ実核輸送で縮約は `h=v-u`、全復元は任意 `h,r` に対し `(u,v)=(r,h+r)` となる。
同じ元候補bを禁止した範囲は元・新とも不能である。
新頂点も固定する別入力は `fixedBothRegion` の全閉包条件から定義し、同じ9件の修復が9同型類となる。

```yaml
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta:
    - "任意元全geometry/全上下文から実K'と元P/W/candidate保持を構成"
    - "原始二実因子から新全核可換性/合成輸送/全新原塔field/実3-law/固定lawを生成"
    - "実he=h2+rho2h1と任意full h1の全actual修復/元L choice/全語の相互復元"
    - "全native labels/Hom一意liftから両関手・unit/counit自然性・圏同値を構成"
    - "全S同じ式/全包含/共有W literal一致/全actual external strict objectとarrowを保持"
    - "同じ一般構成でW4の3→9修復/3同型類/恒等Aut/全(r,h+r)復元、別closed固定新頂点入力9同型類"
  exit_criteria_status: ["全0–3 geometry/P/W/candidates: SubdivisionGeometry/Incidence", "実因子→全核/transport/原law: Factors/OriginalTower/ThreeLaws/FixedLaws", "全label圏同値/逆/naturality/wholeHom: HomLift/CollapseFunctor/ExpandFunctor/Unit/Counit/Equivalence", "全S/strictW/includes/external/全復元: Permissions/RetainedChoices/SolutionWords/SharedValues/ExternalRestoration", "W4値/修復/全同型類/Aut/固定新頂点別入力: C17七source、focused/個別axiom; 正式PR gateはPR作成後に判定"]
  split_reason: none
  completion_candidate: no
  lean_artifacts: ["39新production source、327明示宣言、24新生成API、4受理使用先補助"]
  evidence: ["実primitive factors→same tower/full kernel/typed K'", "全actual supported repair≃旧修復×full Aw", "full native categorical equivalence/whole Hom", "allS/includes/strictW/actual external objects and arrows", "指定W4 actual counts/classes/Aut/full correction coordinates"]
  claim_mapping:
    theorem_names: [transport_comp, originalTower, three_laws, fixed_face_laws, correctionEquiv, supportedSolutionEquiv, collapseHomEquiv, equivalence, rangeEquivalence, solution_path_substitute, externalObjectEquiv, externalHomEquiv, splitRepairEquiv, restore_pair_coordinates, old_repair_card, new_repair_card, old_class_card, new_class_card, old_aut_identity, new_aut_identity, closed_fixed_new_class_card]
    source_labels: ["固定GOAL E内部辺分割の実修復/圏/全S/strictW/外部合成/全復元", "固定GOAL Fの同じwhole affine族への分割適用", "指定W4", "n1017内部辺分割", "design6"]
    conjuncts: ["任意元可換全核/全0–3型付き構造/任意oldL/R", "実因子由来/newfullkernel/actual rho2rho1", "同じhe式/全独立actualrepair/whole freshkernel復元", "全nativeHom/oldlabel保持/逆/unit/counit", "全S/候補/strictW/includes/external", "W4 all repairs/classes/Aut/全(r,h+r)/固定newvertex別closed入力"]
    undischarged_assumptions: []
    acceptance_point: "C17選定五義務と五終了条件の候補。正式PR review/root受理/CIは外部記録で判定"
    port_status: unported
audits:
  premise_delta:
    discharged: ["実Factorizationから新核可換性とactualtransportcomp", "全新LiftData/reference/core/comparatorと全2/3 law", "actualfaceiff→全修復逆/fullHomforcedfresh→categoricalequivalence", "chosen外P/W/candidate→allS/includes/strict共有保持", "W4全primitive条件・実核座標・実修復/全同型類/Aut"]
    remaining: ["同じE分割の全相対複体分解/全H/障害/旧holonomy保存", "同じ有限体C公開関係/DのO,o,Be,証拠支持/極小範囲保存", "指定W1–W3/W5の残構成・接続", "累積全target final packetと別四本completion査読"]
  certificate_provenance:
    discharged: ["旧originalT+二実factor→新originalT全field", "実輸送square→rhocomp→全補正逆", "元fullgauge→forcedfresh全Hom逆→自然同型", "独立新actualchoice→strictW一致→全externalobjects/arrows", "独立W4realrepair→同じ一般定理→actualclasses/Aut/全coords"]
    unresolved: []
  proof_use:
    used: ["oldkernelcomm+firstBijective→freshkernelcomm", "actualstrong/lower/primitivecomposite→rhocomp", "oldreference/core/comparison→全path/face/3law", "P/W閉包/chosen非所属→retainedclosedpart/fixedlaw/strictshared", "fullsupportlabel/gauge→forcedfreshunique/unit/counit", "W4actualface/flip/translation/fullnativekernel→counts/coords/全Aut"]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: ["39productionの初回単一focused、変更6sourceの再focused、現在39本体named milestone focused", "全355個別標準公理/欠落0", "公理log SHA256 caa605954f46379bd52936de0f840a458e3afdf2d3fb803064be80d75adb5271", "再現source SHA256 bd2b4f3c86ea7281b2ac90a73706936b487a4bc47abaf5b6b3156a6cda5b8240", "39source/hash/registry/placeholder/Unicode/privacy/語彙/import方向/保護領域/diff"]
  blocking_findings: []
  next_obligation: "C17最終headの標準PR review/root受理/CI後、同じ原分割の全相対複体・全H・障害・旧holonomy・公開双対/極小保存"
```

前提の申告は次の通り。一般条件と指定W4での放電を区別する。

| 前提 | 三分類と固定条項 | 構成・使用先 |
| --- | --- | --- |
| 任意元有限表示/同じp,q/元L,R/core/指定比較/元全核可換性とstrong・全単射輸送 | 本文由来、GOAL A・E | 元 `OriginalTowerPresentation`、新原塔の各fieldとtransport/actual修復 |
| 中間対象と二実因子/実積/両因子strong・lowerStrong・fullBijective | 本文由来、GOAL E内部分割 | `Factorization`、`middle_kernel_comm`・`transport_comp`・`originalTower` |
| chosenが固定部分/W/candidateに属さないこと、閉じたP/W | 本文由来、GOAL E | `oldRegion`、全S保持、`fixed_face_laws`、shared literal equality |
| 旧3-lawと旧固定face law | 本文由来、GOAL A・E、指定実現では放電済み | `three_laws`・`fixed_face_laws`で新lawを構成。W4のUnit face/空ThreeCellでは実affine値から証明 |
| new核可換性/新transportcomp/新LiftData/core/全labelsの逆とnaturality | 放電済み | `middle_kernel_comm`, `transport_comp`, `originalTower`, `collapseHomEquiv`, `unitIso`, `counitIso` |
| 汎用外部labelのidentity零 | 一般補題の方向仮定、actual native external適用で放電済み | `native_external_identity_zero` が任意actual external identityから導く。実適用は `native_external_counit_shared`・`native_external_unit_shared` |
| W4 whole affine/actual factorsの全primitive条件と指定比較 | 放電済み | `C17SubdivisionInput.originalTower`・`factors`・`factor_product`・`linear_faces`、実flip/translation評価とaccepted whole native kernel |
| W4全修復/全同型類/全Aut/任意新補正復元 | 放電済みの結論 | 独立RealRepairsから `realRepairEquiv`・`oldRepairEquiv`、同じ一般定理から `splitRepairEquiv`、actual isIsomorphicSetoidからclasses、actual fullHomからAut |

未放電の追加前提はC17選定五義務には残さない。固定GOALの後続条項は上記remainingとして未達のまま扱う。

39新productionの初回単一file focused、APIと証明内部を修正した6sourceの再focused、現在の39実行本体のnamed milestone focusedはexit0/errors0/warnings0。
327明示宣言・24新生成API・4受理使用先補助、全355件の個別 `#print axioms` は標準公理のみ・欠落0。
公理log SHA256 `caa605954f46379bd52936de0f840a458e3afdf2d3fb803064be80d75adb5271`、再現source SHA256 `bd2b4f3c86ea7281b2ac90a73706936b487a4bc47abaf5b6b3156a6cda5b8240`。
現在の39ソースと検証した実行本体は一致する。9個の辺値APIを含む全宣言を個別に監査した。
各source/hashと一意registry、保護領域、placeholder/hidden-BiDi/privacy/語彙/import方向/diff scanはclean。
Research全体・aggregate root・全file/module loopのelaborationは実行していない。
全GOALの完了判定とtracking Issueの全完了checkboxは未達のまま保持する。

### Cycle 18 selection — 同じ実分割の相対複体・障害・全コホモロジー

```yaml
ledger_type: target_cycle_result
goal: G-130-aat-relative-repair-composition
cycle: 18
goal_blob_sha: 8da0fb4eb75d1cb5c37a9d4ddf5e03c18c0bb8a2
base_oid: 9b6a5282099933b531df05b6c8bdb4a46f5e5923
tracking_issue: 5132
report_path: research/reports/G-130-aat-relative-repair-composition.md
selection:
  proof_state_ref: "C17原始実二因子からの全修復/全Hom/全S/strictW/実W4、受理PR5157/root5943284656/Issue5943297968"
  proof_dag_predecessors: ["C17 originalTower/collapseCorrection/collapseVertex/全実語/全label同値", "C1–C3 actual support/相対複体/実障害", "C4–C6 全閉geometry/制限/relative complex", "G129 full local coefficients/経路補正/実defect", "C14 whole affine tower/kernel/translation/実修復"]
  milestone: "固定GOAL Eの同じ元実分割から全Sの元相対支持複体をnative旧複体と全新対象核の恒等二項複体へ分解し、同じ縮約/零第一補正sectionで全次数H、H0/H1/H2原代表、実障害と旧閉路holonomyを保存する。任意whole affine実因子へのF適用と同じ指定W4へ接続する"
  proof_obligations:
    - "全元typed wordで実全核輸送/経路補正の置換等式を生成し、全faceと全三cell両routeのd1/d2および同じ実defectを比較"
    - "元Pを保持しchosenをP/candidateから除いた全SのC0/C1とrelativeC2/C3で、同じcollapseにより新複体≅旧複体⊕[fullAw→idfullAw]をnative Mathlib complexとして構成"
    - "全supplement identityの実chain contractionと同じcollapse/zero-firstsectionのnative chain homotopy equivalenceから全nのnative homology isomorphismを構成し、H0全label/H1全cycle/H2全cycle quotientへの原代表値を証明"
    - "元actual reference paths/comparator/fullkernelから実defect等式とrelative obstruction cocycle/classの対応を導き、独立new actual修復の全旧閉路holonomyを同じcollapseで保持"
    - "任意finitefield全affine元L/Rの二実factor条件をGroupExtensionから放電して同じ構成へ適用し、指定W4の非零fullAw/identity differential/非零comparisonと原実補正への接続を検証"
  exit_criteria: ["全word/fullkernel/d0–d2/actualdefect比較", "全S元native supported-relative complexのfullAw二項biprod分解", "native contraction/同じmaps/allnH/H0–H2原代表値", "実obstruction cocycle/classと全旧閉路actual holonomy保存", "whole affine原始因子生成と指定W4同じmapsへの非零接続/focused/全個別axiom/PR gate"]
  selection_reason: "C17で同じ分割の全実修復・射と全新核復元を受理した。残るEの原微分と障害・全Hへの距離を直接閉じる。有限体C公開関係/D全商・双対支持/極小保存は、この同じ微分比較と復元を用いる後続到達点に残す"
  expected_result_type: proof-obligation-discharged
  lean_targets: [SubdivisionCoefficientPaths, SubdivisionComplexIso, SubdivisionHomotopy, SubdivisionObstruction, NativeAffineSubdivision, C18SubdivisionRegression]
  risks: ["係数targetを定数群へ縮小", "d2の完全route/符号を省略", "defect保存を入力fieldにする", "単なるobject分解をnativecomplex同型とする", "新頂点変位bFresh-rho1bSourceの欠落", "全nをH0–H2だけに縮小", "nativeHomology名だけで原代表対応を代替", "修復存在を複体比較の前提に加える"]
  unchecked: ["C18構成と監査はこれから実装", "有限体C公開関係/DのO,o,Be,H_o/極小範囲保存、残W1–W3/W5と累積whole-target completionは後続"]
```

### Cycle 18 result proposal — 同じ実分割のnative全複体と原代表

全Sで、元のC0/C1を同じ実collapseで旧群と新対象の全核へ分解する。
C0の新座標は `bFresh-rho1(bSource)`、C1の新座標は全第一補正である。
元d0は旧d0と全核の恒等写像、元d1は旧collapseの微分、元d2は同じ完全な両routeとなる。
この分解をnative Mathlib complexのbiproductへ接続し、全核のchain contractionを構成する。
同じcollapseとzero-first sectionによるhomotopy equivalenceは全自然数次数のnative homologyを保つ。
H0の全label、H1/H2の全cycle quotientに原代表値を与え、実deltaとその符号付きクラスを保つ。

| 固定条項と構成責務 | 一次宣言と使用先 |
| --- | --- |
| E全typed word/全実核輸送/全補正/完全3-cell両route | `kernel_path_substitute`, `coefficient_path_substitute`, `pathCorrection_substitute`, `faceCorrection_substitute`, `pastingCorrection_substitute`, `d1_collapse`, `d2_substitute` |
| E実canonical比較と全核defectの生成比較 | `canonical_face_fac`, `canonical_face_substitute`, `faceDefect_substitute`, `defect_substitute` |
| E元P/candidatesを保持する全Sの同じ相対複体 | `cochain0Equiv`, `cochain1Equiv`, `relative0Equiv`, `relative1Equiv`, `relative_d0`, `relative_d1`, `relative_d2`, `relativeProductIso`, `relativeBiprodIso` |
| E全新対象核の恒等二項複体と同じchain maps | `NativeIdentityComplex.contraction`, `freshContraction`, `NativeProductComplex.contractionEquiv`, `relativeHomotopyEquiv`, `relativeCollapse_zero/one/two/three`, `relativeSection_zero/one` |
| E全次数HとH0/H1/H2原代表 | `relativeHomologyIso`, `relativeHomologyIso_hom`, `relativeH0Equiv`, `relativeH0Equiv_label`, `relativeH0Equiv_inverse_label`, `relativeH1Iso_class`, `relativeH2Iso_class`。native class比較の中間cochainを `RelativeCohomologyValues` で固定 |
| E元実障害と旧閉路holonomy | `obstruction_cocycle_collapse`, `obstruction_class_collapse`, `signed_obstruction_class_collapse`, `old_closed_holonomy` |
| F任意whole affine元L/Rからの実因子生成 | `NativeAffine.subdivisionFactors` が全strong/lowerStrong/fullBijectiveを生成。任意field/moduleに成立し、任意有限体のk^dを含む |
| 指定W4の同じ一般構成・非零fullAw・実delta・実補正 | `C18SubdivisionRegression.factors_generated`, `freshOne_ne_zero`, `fresh_identity_value`, `fresh_contraction_value`, `fresh_label_d0_nonzero`, `old_defect_coordinate`, `new_defect_coordinate`, `native_collapse_coordinate`, `native_section_first`, `allHomologyIso` |

新しい全核は、cochain族と同じuniverseに置くためだけに `ULift` する。
そのdown値は元の全実核の値であり、恒等微分とcontractionは全元に作用する。
指定W4ではcoordinate oneの全実核元が非零で、実d0の第一値も同じ非零元になる。
実deltaの座標は元・分割後ともminus one、native collapseの元a値は全独立補正に対してv-uである。
指定W4の空ThreeCellを、一般の完全route比較の代替として用いない。

| Material premise | 分類・一次生成・使用 |
| --- | --- |
| 元有限typed表示、同じp/q、元originalL/reference/core/指定比較、全核可換性とstrong/fullBijective | 本文由来 `ambient-boundary`。受理C17/G129の現在の型と適用引数から全輸送・微分・実defect比較へ使用 |
| 原始中間対象・二実因子・実積・strong/lowerStrong/fullBijective | 本文由来 `ambient-boundary`。一般Eは同じ `Factorization`、F適用はwhole affine primitive operationsから `subdivisionFactors` で放電 |
| 閉じた元P、chosen外P/candidates、全allowed S | 本文由来 `direction-hypothesis`。retained元群と同じ全labelsへ使用。W4ではempty fixed edgesと異なるBool候補から放電 |
| old fixed reference face lawsとold authored three-cell laws | 本文由来 `direction-hypothesis`。`fixed_face_laws` / `three_laws` でnew lawsを生成し、同じactual cocycle/classへ使用 |
| 同じ新微分・canonical/defect比較・全複体分解・contractibility・H同型・原代表対応 | `discharge-required` 放電済み。新sourceの入力からの構成・全称証明。結論fieldをFactorizationへ追加していない |
| 一般product補題のsecond native contraction | 一般補題では `direction-hypothesis`、実分割適用では `NativeIdentityComplex.contraction` / `freshContraction` で放電。任意のsupplied equivalenceで置き換えていない |
| 指定W4のwhole kernel非零・実identity微分・非零delta・元実補正との同じmap | `discharge-required` 放電済み。元C17実入力と全kernel equivalence、現在のactual cochain/defect値から構成 |

受理spineは次の15sourceに固定する。全宣言のfull namespaceは各sourceのnamespaceと以下の名前の連結である。

- `SubdivisionCoefficientPaths.lean` (`AAT.AG.RelativeRepairComposition.Subdivision`): `kernel_path_substitute`, `coefficient_path_substitute`, `correction_edge_word`, `pathCorrection_substitute`, `d1_collapse`, `faceCorrection_substitute`, `pastingCorrection_substitute`, `d2_substitute`。
- `SubdivisionActualDefect.lean` (`AAT.AG.RelativeRepairComposition.Subdivision`): `canonical_face_fac`, `canonical_face_substitute`, `faceDefect_substitute`, `defect_substitute`。
- `SubdivisionCochainDecomposition.lean` (`AAT.AG.RelativeRepairComposition.Subdivision`): `collapseC1Hom`, `collapseC1Hom_apply`, `cochain1Equiv`, `cochain1Equiv_collapse`, `cochain1Equiv_first`, `cochain1Equiv_inverse`, `cochain0Equiv`, `cochain0Equiv_old`, `cochain0Equiv_fresh`, `cochain0Equiv_inverse`, `d0_first`, `cochain1Equiv_d0`, `cochain1Equiv_d1`。
- `SubdivisionSupportedCochains.lean` (`AAT.AG.RelativeRepairComposition.Subdivision`): `supported1Equiv`, `supported0Equiv`, `chosen_not_fixed_range`, `retained_supported1_eq`, `retained_supported0_eq`, `relative1Equiv`, `relative0Equiv`, `relative0Equiv_values`, `relative1Equiv_values`, `relative_d0`, `relative_d1`, `relative_d2`。
- `NativeProductComplex.lean` (`AAT.AG.RelativeRepairComposition.NativeProductComplex`): `complex`, `complex_d`, `fst`, `snd`, `inl`, `inr`, `iso`, `iso_fst`, `iso_snd`。
- `NativeIdentityComplex.lean` (`AAT.AG.RelativeRepairComposition.NativeIdentityComplex`): `object`, `differential`, `complex`, `complex_d_zero`, `d_zero_one`, `contractionComponent`, `contraction_shape`, `contraction`, `contraction_value`。
- `SubdivisionComplexIso.lean` (`AAT.AG.RelativeRepairComposition.Subdivision`): `freshComplex`, `freshContraction`, `splitComplex`, `zeroProductEquiv`, `relativeComponentIso`, `relative_component_comm`, `relativeProductIso`, `relativeBiprodIso`。
- `NativeProductContraction.lean` (`AAT.AG.RelativeRepairComposition.NativeProductComplex`): `inl_fst`, `projector_sum`, `contractionEquiv`, `homologyIso`, `homologyIso_hom`。
- `SubdivisionHomotopy.lean` (`AAT.AG.RelativeRepairComposition.Subdivision`): `relativeHomotopyEquiv`, `relativeCollapse`, `relativeSection`, `relativeCollapse_zero`, `relativeCollapse_one`, `relativeCollapse_two`, `relativeCollapse_three`, `relativeSection_zero`, `relativeSection_one`, `relativeHomologyIso`, `relativeHomologyIso_hom`。
- `RelativeCohomologyValues.lean` (`AAT.AG.RelativeRepairComposition.RelativeCohomologyValues`): `firstNormalizedIso`, `firstShortIso`, `firstHomologyIso`, `secondNormalizedIso`, `secondShortIso`, `secondHomologyIso`, `nativeCycle1`, `native_cycle1_value`, `native_h1_class`, `nativeCycle2`, `native_cycle2_value`, `native_h2_class`, `native_h1_inverse_class`, `native_h2_inverse_class`。
- `SubdivisionZeroCohomology.lean` (`AAT.AG.RelativeRepairComposition.Subdivision`): `h0_fresh_zero`, `relativeH0Equiv`, `relativeH0Equiv_label`, `relativeH0Equiv_inverse_label`。
- `SubdivisionCohomologyClasses.lean` (`AAT.AG.RelativeRepairComposition.Subdivision`): `collapseZ1`, `collapseZ2`, `collapseZ1_value`, `collapseZ2_value`, `relativeH1Iso`, `relativeH2Iso`, `relativeH1Iso_class`, `relativeH2Iso_class`。
- `SubdivisionObstruction.lean` (`AAT.AG.RelativeRepairComposition.Subdivision`): `obstruction_cocycle_collapse`, `obstruction_class_collapse`, `signed_obstruction_class_collapse`, `old_closed_holonomy`。
- `NativeAffineSubdivision.lean` (`AAT.AG.RelativeRepairComposition.NativeAffine`): `subdivisionFactors`, `subdivisionFactors_first`, `subdivisionFactors_second`, `subdivisionFactors_product`。
- `C18SubdivisionRegression.lean` (`AAT.AG.RelativeRepairComposition.C18SubdivisionRegression`): `chosen_not_candidate`, `factors_generated`, `freshOne`, `freshOne_ne_zero`, `fresh_identity_value`, `fresh_contraction_value`, `freshLabel`, `fresh_label_d0`, `fresh_label_d0_nonzero`, `reference_face_word`, `old_defect_coordinate`, `new_defect_coordinate`, `relativeComplexIso`, `allHomologyIso`, `native_collapse_coordinate`, `native_section_first`。

`RelativeComplex.lean` の基本API `ActualRelative.obstructionClass_eq_mk` は、同じactual相対cocycleの商代表を公開する。
このAPIを障害クラス比較へ、`NativeProductComplex.complex_d` を複体の微分比較へ、
`NativeIdentityComplex.d_zero_one` を指定W4の実恒等微分へ使用する。
既存の定義値・定理statement・元群は同じである。

```yaml
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: ["全typed wordの全核輸送/補正、d0–d2全比較、実defect等式", "全Sの元supported-relative native複体とfullAw恒等summandのbiprod同型", "生成contraction/同じcollapseとsection/allnH/H0–H2原代表", "同じactual obstruction cocycle/classと[-delta]/全旧閉語holonomy", "whole affine primitive factors生成と同じW4の非零fullkernel/actuald0/defect/原補正接続"]
  exit_criteria_status: ["全word/fullkernel/d0–d2/defect: CoefficientPaths/ActualDefect", "全S/native分解: SupportedCochains/ComplexIso/NativeProductComplex", "contractibility/allnH/原代表: IdentityComplex/ProductContraction/Homotopy/ZeroCohomology/CohomologyValues/CohomologyClasses", "actual obstruction/holonomy: SubdivisionObstruction", "whole affine/W4: NativeAffineSubdivision/C18SubdivisionRegression。正式PR gateはPR作成後に判定"]
  split_reason: none
  completion_candidate: no
  lean_artifacts: ["15新source/129明示宣言、既存RelativeComplexの1基本API、4生成API"]
  evidence: ["fullAw identityのnative chain contraction", "同じactual d0–d2からのnative decomposition", "native homology mapの全cycle代表値", "実deltaと[-delta]classの対応", "same W4非零fullkernelと実微分/defect/補正"]
  claim_mapping:
    source_labels: ["固定GOAL E内部辺分割の全相対複体/H/障害/holonomy", "固定GOAL F whole affine族への同じE適用", "指定W4の同じ実分割", "n1017内部分割", "design6"]
    undischarged_assumptions: []
    acceptance_point: "C18固定五義務と五終了条件の候補。正式PR review/root受理/CIは外部監査記録で判定"
    port_status: unported
    theorem_names: [relativeBiprodIso, relativeHomotopyEquiv, relativeHomologyIso, relativeH0Equiv, relativeH1Iso_class, relativeH2Iso_class, obstruction_cocycle_collapse, obstruction_class_collapse, signed_obstruction_class_collapse, old_closed_holonomy, subdivisionFactors, fresh_identity_value, fresh_label_d0_nonzero, new_defect_coordinate, native_collapse_coordinate]
audits:
  premise_delta:
    discharged: ["全実語→全核係数/補正→d1/d2", "actual strong uniqueness→canonical/defect", "元P/candidate保持→full support groups", "同じ微分→native full kernel contraction/全H/原代表", "原law生成→actual signed class", "whole affine originalL/referenceR/factors→全primitive条件", "same W4full Aw/非零実微分/実delta/元補正"]
    remaining: ["有限体C公開関係とDのO,o,Be,全双対支持/極小範囲の同じ分割での保存", "指定W1–W3/W5の残構成・一般定理への接続", "累積全target final packetと別四本completion査読"]
  certificate_provenance:
    discharged: ["same actual coefficients/full paths→native decomposition", "whole fresh identity→native contraction", "same maps→alln native H and all cycle classes", "actual canonical/defect→signed obstruction class", "primitive whole affine operation→factor fields"]
    unresolved: []
  proof_use:
    used: ["actual path factorization/strong uniqueness/full kernel inclusion", "same actual d0/d1/d2 and old support names", "native full contraction and class naturality", "same actual reference/fixed and three-cell laws", "same W4 primitive operations/full kernel inverse/actual defect and collapse"]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  blocking_findings: []
  next_obligation: "C18最終headの標準PR review/root受理/CI後、同じ全元分割のC公開関係/D商・双対支持/極小保存、指定W1–W3/W5と累積completion"
```

15productionと既存定義元の単一file focused、現在の同じ15実行本体と基本APIのnamed milestone focusedはexit0/errors0/warnings0。
15新sourceの129明示宣言、既存定義元の1基本APIと4生成宣言、全134件の個別 `#print axioms` は標準公理のみ・欠落0。
公理log SHA256 `8fdf9ec2ac948a5bd90a2ab000c767d13ce85b736979268b82002f24137459d1`、再現source SHA256 `89ebeac41f9d889ad5fc6ad1207fceedc28d5364cd1b09c6ed76ca2e495cf57d`。
全15sourceと既存定義元のhash/一意registry、placeholder/hidden-BiDi/privacy/語彙/import方向/保護領域/diff scanを照合する。Research全体・aggregate root・全file/module loopのelaborationは実行していない。
全GOALの完了判定とtracking Issueの全完了checkboxは未達のまま保持する。

### Cycle 19 selection — 同じ実内部分割の原always商と全双対支持

```yaml
ledger_type: target_cycle_result
goal: G-130-aat-relative-repair-composition
cycle: 19
goal_blob_sha: 8da0fb4eb75d1cb5c37a9d4ddf5e03c18c0bb8a2
base_oid: 1a051892c1d505e7b9f92a14f75f4216a497ce83
tracking_issue: 5132
report_path: research/reports/G-130-aat-relative-repair-composition.md
selection:
  proof_state_ref: "Issue5132/C18受理PR5158・root5944039699/current SubdivisionCochainDecomposition/SupportedCochains/Obstruction、C13原always商と全双対分類"
  proof_dag_predecessors: ["C17同じ原実分割・全修復/全Hom/全S", "C18原微分/defect/全相対複体/全H/原代表", "C13 original D/O/o/B_e/全dual/極小分類/原H2接続", "C14 whole affine native全核/線形座標"]
  milestone: "GOAL E有限体分割のD保存。原始実因子と同じactual collapseから線形商比較を生成し、全候補名・全核列・実障害・全双対支持・全変更範囲の極小分類を保存する"
  proof_obligations:
    - "元全核の線形構造をfull actual rho1で新全核へ移し、元頂点と原射を保持する全new modules・全rho線形性、同じcollapse/expandの線形性を生成する"
    - "独立に定義したnew/old OriginalColumns.alwaysSpaceと全relative face群を同じ実値で比較し、new always sourceをold always source×fullAwへ分解。両方向の実d1値と全range Dの一致を証明する"
    - "独立new coker Dとold coker Dの線形同値を生成し、全face商代表q、actual o=q(-delta)、元名の各full B_eと全Sの列rangeを同じmapで保存する"
    - "全商双対の往復、全nonzero-obstruction dual支持族、全S hitting・包含極小・零/全候補不能条件を元候補名で保存し、同じactual修復の分類へ接続する"
    - "同じ商比較を全候補後のCP2/range d1・原d2/相対H2障害の値対応へ接続し、受理済same whole affine W4で非零o・full候補列・dual支持と極小範囲を実評価する"
  exit_criteria:
    - "full新核上のmodule/全実核輸送の線形性と同じcochain collapse/expandの線形原値APIを入力から生成。線形保存/商同値をFactorization fieldや別certificateとして受け取らない"
    - "new alwaysの全自由度をold always×fullAwへ両逆で保持し、任意new alwaysからのd1と任意old alwaysの復元d1を同じ原face値で比較。全range Dが同じface比較で一致"
    - "Oの両逆線形同値が任意q代表・同じactual signed defect・各original候補whole kernel column・任意Sのrangeを保存。存在/零性だけの同値で代替しない"
    - "任意dualを往復し、支持集合/支持族を全原候補名で比較。全S hitting/極小、zero空範囲、全候補不能空支持をsame actual全範囲分類へ接続"
    - "全候補商と原CP2/range d1/誘導d2・same相対signed obstructionの比較が商代表で交換。same W4のactual oと候補B、非零dual支持、極小範囲を同じ一般構成に接続"
  selection_reason: "C18が固定した同じactual d1 collapseとdefect等式を、Dの独立全商・全候補列・全dualへの保存へ伸ばす。Cの領域別private/public分割比較に先立つ再利用可能な線形不変量の到達点であり、全target completionへは昇格しない"
  expected_result_type: proof-obligation-discharged
  lean_targets: ["SubdivisionLinearCoefficients", "SubdivisionLinearCochains", "SubdivisionAlwaysSpace", "SubdivisionAlwaysDifferential", "SubdivisionRangeQuotient", "SubdivisionCandidateColumns", "SubdivisionDualSupports", "SubdivisionMinimalRanges", "SubdivisionRangeCohomology", "C19SubdivisionRangeRegression"]
  risks: ["new fullkernelをvector carrierへ取り替える", "linear iso/defect保存を入力にする", "new alwaysの全fresh自由度を除去", "O比較をfeasibility iffだけで代替", "candidateの全kernel列を有限生成像へ狭める", "全dualを選択basisだけにする", "全S/原候補名の比較を落とす", "Cの各local公開関係保存まで済んだと過大表示"]
  unchecked: ["C19構成・検証はこれから実装", "Cの同じlocal private/public関係と全復元の分割比較、残W1–W3/W5、累積completionは後続"]
```

### Cycle 19 result proposal — 原always商と全候補・全双対の同じ実値

原始の実因子を保った同じ分割について、新しい全実核のmoduleを `rho1AddEquiv` から生成し、元全核のmoduleを保持した。`rho2` と全新辺の線形性は元辺との実合成から導出する。元の実collapse/expandを全degree 0/1に線形化し、独立に定義した `OriginalColumns.alwaysSpace` を元always空間と新頂点の全核へ両逆で分解した。新しいalways空間を元空間の像として定義していない。

独立な新旧 `D` は全face値で交換し、任意new alwaysからのcollapseと任意old always・任意full新核値からの復元の両方向が同じ原d1値を持つ。全range Dの等号から独立coker Dの線形同値を生成し、すべてのface代表qとactual `o=q(-δ)` を保存した。元候補名の全単射、各候補の全原核の線形同値、独立の候補maskに対する実collapse、同じ原d1と商によるfull `B_e` の値比較を接続する。

全候補部分集合のrange、商の全双対の往復、各whole-column支持、actual障害に非零な全支持族、hittingと包含極小を同じmapで比較した。同じ独立actual repairの全範囲と全新核自由度にも接続し、zeroでの唯一の空極小範囲、全候補許容時のactual repair存在、非零障害dualの空支持族、transversal皆無条件を比較する。双対basisや標本への制限はない。

全候補後の商比較は、独立に定義した `OriginalRangeQuotient.equivalence` の新旧両側を通る。任意全face代表を保存し、全range d1の等号と全誘導d2の交換を導出する。空候補indexの等号transportは同じC18 native H2 isoに施し、すべてのnative cycle classと全face商のsquareを証明した。C18のactual signed obstruction class比較と、本cycleの `defectFamily_eq` / `obstruction_eq` / 全商代表保存を同じ原classへ適用できる。

同じ指定W4の独立always空間では、全原d1が実b値を読むためalways像は零になる。実商は全F3核と線形同値で、原actual signed障害と独立split障害はいずれも座標1で非零。原candidate全核列と同じsplit列は商全体へ全射である。非零商dualのfull支持は全singleton bで、全独立actual repairの極小範囲は新旧とも同じbである。C17の実因子、全修復と全label、C18のactual defectを保持して適用した。

```yaml
ledger_type: target_cycle_result
goal: G-130-aat-relative-repair-composition
cycle: 19
goal_blob_sha: 8da0fb4eb75d1cb5c37a9d4ddf5e03c18c0bb8a2
base_oid: 1a051892c1d505e7b9f92a14f75f4216a497ce83
tracking_issue: 5132
report_path: research/reports/G-130-aat-relative-repair-composition.md
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "選定した五義務を同じ実因子/full kernelsから放電。一般named列transportと全候補不能の直接比較は同じ終了条件を支える追加依存sourceとして収録"
  exit_criteria_status:
    - "full modules/全rho線形/同じcollapseとexpand: LinearCoefficients/LinearCochains。W4 original_linearはwhole affine原入力から生成"
    - "独立always/両逆/full新核/両方向d1/全range D: AlwaysSpace.linearEquiv、AlwaysDifferential.D_collapse/D_restore/range_D"
    - "独立O/任意q/actual o/元候補fullkernel列/全S: RangeQuotient.equivalence/equivalence_q/obstruction_eq、CandidateColumns.candidate_collapse/column_collapse/quotient_column、DualSupports.range_map"
    - "全dual/full支持族/hits/極小/actual全範囲/zero空/全候補不能: NamedColumnEquivalence、DualSupports、MinimalRanges、ImpossibleRangesの全API"
    - "全候補商/CP2/range d1/原d2/native H2原classと同じW4非零障害/全列/dual支持/actual極小: RangeCohomology、C19SubdivisionRangeRegression。正式PR gateはPR作成後に判定"
  split_reason: none
  completion_candidate: no
  lean_artifacts: ["SubdivisionLinearCoefficients", "SubdivisionLinearCochains", "SubdivisionAlwaysSpace", "SubdivisionAlwaysDifferential", "SubdivisionRangeQuotient", "SubdivisionCandidateColumns", "NamedColumnEquivalence", "SubdivisionDualSupports", "SubdivisionMinimalRanges", "SubdivisionImpossibleRanges", "SubdivisionRangeCohomology", "C19SubdivisionRangeRegression", "OriginalColumns.D_apply/D_value/column_applyとOriginalRanges.column_applyの定義元基本API"]
  claim_mapping:
    theorem_names: ["AlwaysDifferential.range_D", "RangeQuotient.obstruction_eq", "CandidateColumns.quotient_column", "DualSupports.obstruction_support_family", "MinimalRanges.minimal_actual_repair_iff", "ImpossibleRanges.empty_support_duals_iff", "RangeCohomology.faceQuotientEquiv_value", "RangeCohomology.inducedD2_commute", "RangeCohomology.nativeH2_commute", "C19SubdivisionRangeRegression.split_obstruction_coordinate", "C19SubdivisionRangeRegression.split_column_surjective", "C19SubdivisionRangeRegression.split_minimal_actual_repair_iff"]
    source_labels: ["GOAL Eの同じ実分割によるD商・全dual・全変更範囲保存", "GOAL Dの全原商/全候補後のH2接続", "GOAL Fの同じwhole affine適用", "W4の同じ指定実入力"]
    conjuncts: ["選定五終了条件を上記各値APIと両逆構成に対応", "全A–F/W1–W5の完了に昇格しない"]
    undischarged_assumptions: []
    acceptance_point: "五終了条件の一次Lean構成・同じW4適用・現source検証を揃えたproposal。受理判定は固定headの標準PR reviewとrootによる検査基準の適用に置く"
    port_status: unported
  evidence: ["現12 productionの各単一focused＋定義元OriginalCandidateColumns/OriginalRangeEquationsの各単一focused", "同じ選定12 exact bodyを持つnamed milestone focused、errors0/warnings0", "132新明示＋定義元API4＋生成6=142個別公理出力、標準のみ・欠落0"]
audits:
  premise_delta:
    discharged: ["新全核module: full実rho1AddEquivのmodule transport", "rho2/new辺の線形性: 実factor compositeと原hlinear", "always・O・全S保存: 独立空間からの同じcollapse/expandと全d1値", "generic whole列条件hcolumns: CandidateColumns.quotient_columnで放電", "index transportのclass条件hi: C18 relativeH2Iso_classの同じ全cycle値で放電", "W4原module/linearity: NativeAffine.coefficientModule/edge_linear、actual fixed lawは指定Pの空faceから放電"]
    remaining: ["GOAL EのC local private/public関係・全公開Ri/全復元の同じ分割保存", "指定W1–W3/W5の残接続", "累積completion packetと別fresh Math2/Lean2最終判定"]
  certificate_provenance:
    discharged: ["Factorizationにはprimitive actual因子と受理C17/C18由来full transportのみ。線形同値/商/支持保存fieldなし", "Submodule商同値は両方向range Dから、全列/双対比較は原mask/d1/qから生成", "全候補商は新旧C13原bridgeを同じ代表で比較し、native H2はC18同じcollapseを使用"]
    unresolved: []
  proof_use:
    used: ["rho1全核surjectivity/module transfer→rho2 scalar/全new辺→実collapse線形", "chosen除外/P閉条件→same always/full新核の両逆→実d1/全range D→実q/o", "原候補fullmaskとwholekernel/namebijection→全B_e→全S range/dual family/極小/不能条件", "C13全候補bridgeの原代表→全d1商/誘導d2→C18同じnative classのsquare", "同じW4の原whole affine d1/δ=-1→actual o=1/full B surj/非零dual/actual極小"]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: ["132新明示＋API4＋生成6=142個別公理が標準のみ", "named source sha256=a2dfa5c71a8192821ef2e8df78d1f5f30d8ccc15538b42e5b426ebc66391b2a6 / log sha256=a247f0817b23cb9005d3763d3ce5aab0c96a34760bc01353ade8a943aabd4fe7", "一意registry12/現source hash/placeholder/hidden-BiDi/privacy/import方向/保護領域/diff clean。Research full/aggregate/allfile/allmoduleなし"]
  blocking_findings: []
  next_obligation: "同じ実内部分割についてCの独立各local private/public Ri、全public family、全内部自由度、全actual復元とstrict full labelsを比較する。残W1–W3/W5と累積completionはその後に接続"
```

受理predecessorの追跡は、C18 PR #5158/root #5944039699、C17 PR #5157/root #5943284656、C13 PR #5149/root #5929751165、C14 PR #5150/root #5931624166の現在の必要statement・定義・適用引数・proof-useで完了する。原入力と今回の追加四つの定義元APIを確認し、受理済み内部DAGを再帰的に再認証しない。toolchainはLean 4.28と固定mathlib `8f9d9cff6bd728b17a24e163c9402775d9e6a365`。共通監査基準 `dbed043cb514e8c964589d2e12e982750c87ae83` と固定GOAL blobは不変である。

### Cycle 20 selection — 全閉被覆の実分割とprivate/public原名の保存

```yaml
ledger_type: target_cycle_result
goal: G-130-aat-relative-repair-composition
cycle: 20
goal_blob_sha: 8da0fb4eb75d1cb5c37a9d4ddf5e03c18c0bb8a2
base_oid: 5ab51676dd7299667d83aaf0928703b0f8bb24bd
tracking_issue: 5132
report_path: research/reports/G-130-aat-relative-repair-composition.md
selection:
  proof_state_ref: "Issue5132/C19受理PR5159・root5945142965、C17実分割全geometry/C18同じ微分/C19線形全核、C10–12有限local interface"
  proof_dag_predecessors: ["C17 actual全typed分割/元W厳密", "C18原actual微分", "C19同じfull核線形構造", "C10–12元閉有限被覆/private public定義"]
  milestone: "GOAL E有限体C保存へ接続する入力側の全閉被覆輸送。分割辺を含む領域も元0–3全incidenceから生成し、元被覆/共有部分/全private public原名と候補maskを同じ置換で保持する"
  proof_obligations:
    - "任意原edge setの全出現を置換し、選択辺を含む任意閉領域を同じ原vertices/faces/triplesと必要なfresh vertex/両factorから独立生成。全面両path・全3cell両route/prefix/suffixを閉じる"
    - "任意領域包含/交差と全0–3 indexed coverを輸送。選択辺の唯一leaf所属から異なるleaf overlapにfresh vertex/factorが無いことと元retained overlapを証明"
    - "元定義から再生成したsharedEdges/privateAlwaysEdgesの全original名・両factor membershipを比較。選択private辺の両factorは同じleafでprivate、全候補/全共有/全fixed edgeをpublicに保持し、public edge subtypeを全単射で比較"
    - "同じ指定whole affine W4のactual chosen a・candidate b・全face wordに一般構成を適用し、両factor private/public b保持、選択辺含有面の全typed閉包と全S禁止candidate mask保存を実評価"
  exit_criteria:
    - "任意領域の新ClosedRegionを入力から生成し、全path/route contextの置換edge set等号と全0–3 membership APIを証明。選択辺を避ける旧oldRegionだけで代替しない"
    - "任意indexed coverの全0–3 coverage、包含と交差の同じcell比較が成立。唯一leaf条件は原chosen非共有性の入力で、overlap保存を別certificateで受け取らない"
    - "独立new private/shared定義の全名を比較し、旧private chosen一名が両factorへ移る。public全単射は全旧public名を含み両inverse/元candidate値・maskに接続する"
    - "same W4原actual幾何を変更せず一般定理に接続。非自明face wordのa置換/両factor private/whole candidate b保持と任意Sの禁止条件を同じmapで確認"
  selection_reason: "C19で原商/全双対保存を受理済み。Cの独立局所生成を同じK'へ適用するため、全閉被覆とprivate/public入力の輸送を独立の再利用可能な一般定理として先に固定する。生成R_i/全kernel section復元比較はこの入力比較を使用する次到達点で、今回終了条件へ含めない"
  expected_result_type: proof-obligation-discharged
  lean_targets: ["SubdivisionRegionIncidence", "SubdivisionClosedCovers", "SubdivisionPrivatePartition", "SubdivisionPublicNames", "C20SubdivisionCoverRegression"]
  risks: ["選択辺を含む領域を除外", "3cell全文脈を省略", "freshを共有/fixedへ追加", "private分類を新規fieldから受取る", "public原名を候補だけへ縮小", "Cの全生成R_i/全復元まで完了と表示"]
  unchecked: ["C20の構成・検証はこれから実装", "同じ新旧local D/F/R_i/N_i/生成section/全label・strict glue復元比較は後続", "残W1–W3/W5・累積whole completionは後続"]
```

### Cycle 20 result — 全閉被覆と原private/public名の分割比較

任意の元complete edge name集合を、retained edgeは自身、両factorはchosenへ読む `edgeOrigin` の逆像で置換した。各typed pathの全出現と、3-cellの両routeの全prefix/suffixに対して、この置換集合との等号を証明した。選択辺を含む閉領域も独立に生成し、元vertices/faces/triplesと、選択辺が属する場合だけfresh vertex/両factorを保持する。

領域包含、交差、合併、indexed assembly、全領域を同じcell集合で比較し、任意0–3 indexed coverを新presentationの全coverへ構成した。選択辺がprivateである元条件から所属leafの一意性を導き、異なるleafの全overlapは元retained regionそのものとなる。新cover/overlap保存certificateを入力として受け取っていない。

生成されたnew regionsに既存 `sharedEdges/privateAlwaysEdges` を適用した独立集合は、元集合の `edgeOrigin` 逆像と一致する。両factorは元chosenのprivate条件と同値、retained edgeは同じ原名の条件と同値である。各leafの全nonfixed・nonprivate補集合をpublic名として定め、その独立new補集合と旧補集合の両逆な全名同値を構成した。全public原名に付随する実射影の全核の族も相互逆に対応し、任意full値の前後の読み取りAPIを持つ。候補集合だけや列像へ縮小していない。さらに各leafの全nonprivate辺を `CompletePublic.publicEdges` として独立に生成し、全fixed・shared・candidate原名を含む族の全単射と各名の全actual kernel族の両逆を構成した。固定辺の実補正を零とする新旧の独立 `fixedZero` 条件を同値で比較し、その条件を満たす全physical public族を `physicalFamilyEquiv` で相互逆に対応させる。元の相対局所補正から `relativePublic` が同じ全原名・全核値を読み、固定零条件を放電する。既存の自由public座標は全public族のnonfixed部分に正確に一致し、fixed原名を自由変数として追加しない。

同じ指定W4の原geometry/whole affine towerと実因子を使用し、全領域と固定vertex regionの二member coverへ適用した。元faceのtyped語b,a,aをb,e1,e2,e1,e2の同じ順で置換し、両factorがprivate、candidate bがpublic、その全実核値・任意Sの禁止maskが同じ値で保存されることを確認した。freshは固定overlapに含まれない。追加の入力では同じ原geometry・full affine塔・actual因子のままbを固定し候補集合を空にした。全public b原名と零補正を保持し、零族は新旧のfixed条件を満たす一方、whole kernelのtranslation by one族は新旧とも拒否される。追加入力の法則を満たす修復の存在は主張していない。

```yaml
ledger_type: target_cycle_result
goal: G-130-aat-relative-repair-composition
cycle: 20
goal_blob_sha: 8da0fb4eb75d1cb5c37a9d4ddf5e03c18c0bb8a2
base_oid: 5ab51676dd7299667d83aaf0928703b0f8bb24bd
tracking_issue: 5132
report_path: research/reports/G-130-aat-relative-repair-composition.md
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "選定四義務を元全geometry/既存private定義/同じ実塔から構成。全public名だけでなく各名の全actual kernel familyも両逆で保持"
  exit_criteria_status:
    - "任意領域と全typed incidence: edgeWord_edges/expanded_path_edges/expanded_pasting_context/expandedRegion。全face/全triple closureを入力から生成"
    - "全0–3 coverと包含/交差/assembly: expanded_indexed_cover/expanded_inclusion/expanded_inter/expanded_indexed_union。private_chosen_uniqueからexpanded_overlap_retainedを適用"
    - "独立private/shared/publicと全名/全核値/mask: expanded_private_edges/expanded_shared_edges/expanded_public_edges/publicNameEquiv/PublicKernels.familyEquiv/public_forbidden_mask、CompletePublic.fixed_public/candidate_public/shared_public/nonfixed_public/publicNameEquiv/PublicKernels.fixedZero_iff/physicalFamilyEquiv/relativePublic、C20FixedPublicRegressionの零/非零両方向"
    - "same actual W4: C20SubdivisionCoverRegressionのregions_cover/split_regions_cover/first_private/second_private/full_face_word/candidate_name_value/candidate_coefficient_value/candidate_mask/actual_factor_origin。正式PR gateはPR作成後に判定"
  split_reason: none
  completion_candidate: no
  lean_artifacts: ["SubdivisionRegionIncidence", "SubdivisionClosedCovers", "SubdivisionPrivatePartition", "SubdivisionPublicNames", "C20SubdivisionCoverRegression", "SubdivisionFixedPublicValues", "C20FixedPublicRegression"]
  evidence: ["元complete名の逆像から新閉領域とcoverを独立構成", "既存private/shared定義からの全membership比較", "全public実核族の両逆・任意値・全S原candidate mask", "same W4 full authored wordと実whole affine factors"]
  claim_mapping:
    theorem_names: ["expanded_path_edges", "expanded_pasting_context", "expandedRegion", "expanded_indexed_cover", "expanded_overlap_retained", "expanded_private_edges", "private_chosen_unique", "publicNameEquiv", "PublicKernels.familyEquiv", "CompletePublic.publicNameEquiv", "CompletePublic.PublicKernels.physicalFamilyEquiv", "CompletePublic.PublicKernels.relativePublic", "C20FixedPublicRegression.nonzero_not_physical", "C20FixedPublicRegression.split_nonzero_not_physical", "public_forbidden_mask", "C20SubdivisionCoverRegression.full_face_word", "C20SubdivisionCoverRegression.candidate_coefficient_value"]
    source_labels: ["GOAL E有限体C保存の同じ閉被覆/原private public入力比較", "GOAL Cの元private/shared/candidate定義", "GOAL F/W4同じ実操作と指定幾何"]
    conjuncts: ["選定四終了条件と上記原値/全集合/両逆APIを対応", "生成済みR_i・N_i・section・作用/strict glue復元の比較は後続。全C保存完了へ昇格しない"]
    undischarged_assumptions: []
    acceptance_point: "四終了条件の構成とsame W4適用・検証を揃えたproposal。受理は固定headの標準PRレビューとrootによる検査基準の適用で判定"
    port_status: unported
audits:
  premise_delta:
    discharged: ["全新閉包/cover: 元全incidence・original coverから生成", "選択leaf唯一性: 原privateAlwaysEdgesの非共有条件から導出", "public名の両逆: 選択辺が全leafで非publicなことから生成", "全public実核族: retained targetの同じ実投影核から構成。全fixed名を含むphysical族と固定零条件の両方向/actual相対局所補正の読み取りも構成", "W4条件: accepted C17/C18の元実geometry/factorsへ適用し、private/cover/public/maskを今回評価"]
    remaining: ["同じ新旧local D/F/R_i/N_i/生成section/全label・strict glue復元比較", "残W1–W3/W5", "累積final packetと別fresh全target最終査読"]
  certificate_provenance:
    discharged: ["expandedRegionの全fieldsは元ClosedRegionのclosureと全path/route置換から生成", "expanded_indexed_coverは元IndexedCoverから生成。新被覆fieldを供給しない", "新private/shared/public集合は既存の各定義で独立に作成してから比較", "public kernel comparisonは同じretained actual target/kernel。像への全射や選択basisで代替しない"]
    unresolved: []
  proof_use:
    used: ["元edge closure→new factor endpoints/fresh membership", "元face/full3cell closure→full substituted incidence", "元coverage全0–3→fresh/chosen/retained全coverage", "原private非共有→唯一leaf/retained overlaps/全public名からchosen排除", "chosen非candidate→独立new private/publicと全S mask", "actualT/Fの元target→whole public coefficient types/全値", "same W4原faceとactual factors→全typed置換/原値とmask"]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: ["116明示＋生成3=119個別標準公理・欠落0・errors0/warnings0", "選定義務を実装する7 current production単一focusedと同じ7 exact-body named milestone focused", "audit sha256=fec0e21b7abf23d5bb9285ceb61d745738c2c308725df6197c1588326f0aaefc / log sha256=09a61b9bde82849b334eca3e7ebde6512370d10fb49f4f8249d7c63485b054c8", "current hash/registry/placeholder/hidden-BiDi/privacy/import方向/保護領域/diff scan整合。Research全体/aggregate/全file/module elaborationなし"]
  blocking_findings: []
  next_obligation: "今回生成した同じ閉被覆/private public全名・全核値から、独立新旧local D/F/rhs/一回生成R_i/N_i/section/元全labelsを比較し、全S strict glueとsame actual復元へ接続する。その後残W1–W3/W5と累積completionを進める"
```

受理済predecessorはC17 PR #5157/root #5943284656、C18 PR #5158/root #5944039699、C10–12 PR #5146–5148の受理記録とcurrent必要statement/definition/適用引数/proof-useで追跡を完了する。今回の全public actual kernelはC17のoriginalTower/Factorizationを直接使用し、内部DAGの再帰再認証は行わない。Lean 4.28/mathlib `8f9d9cff6bd728b17a24e163c9402775d9e6a365`、固定GOAL blobと適用基準 `dbed043cb514e8c964589d2e12e982750c87ae83` は不変。

### Cycle 21 selection — 任意局所領域の元相対複体と全補足核

```yaml
ledger_type: target_cycle_result
goal: G-130-aat-relative-repair-composition
cycle: 21
goal_blob_sha: 8da0fb4eb75d1cb5c37a9d4ddf5e03c18c0bb8a2
base_oid: 35f32cf4d3861a1482fcb45fe1e60cf6fa8c67b7
tracking_issue: 5132
report_path: research/reports/G-130-aat-relative-repair-composition.md
selection:
  proof_state_ref: "Issue5132/C20受理PR5160/root5945772253、C18全actual cochain分解、C11原RelativeCover複体"
  proof_dag_predecessors: ["C20任意expandedRegion/全private public名", "C18同じactual collapse/d0/d1/d2", "C11独立原RelativeCover C0–C3/微分", "C17/C18 whole affine W4"]
  milestone: "GOAL EのC局所生成保存を支える、任意閉領域Uの独立new/old相対C0–C3複体の全値比較。chosenを含む領域には全fresh核のidentity二項複体、含まない領域には零補足を構成し、全labels・補正・微分・実RHSを保持する"
  proof_obligations:
    - "任意U・chosenを避ける元Pに対して、new RelativeCover C0/C1をold C0/C1×補足群へ相互逆に構成。補足群はchosen∉U.edgesなら零、所属ならfull実fresh核。new局所族を旧像で定義しない"
    - "全旧vertex labels/retained辺値、fresh label displacementと両factor補正を同じactual rho1/rho2で読み/任意値から復元。C0はchosenを含まないleafのglobal零延長による偽fresh自由度を作らない"
    - "独立new/old C2/C3の全original名・核値を保持し、d0=old d0×identity、d1=old d1∘projection、d2=old d2を証明。閉領域の元全incidenceを使用し、零延長をchain mapとして仮定しない"
    - "同じactual faceDefect/記号的rhsを全所属faceで保存し、任意local方程式の全解がold全解×補足群に対応する両逆を構成。解存在だけへ弱化しない"
    - "任意元相対vertex labelのd0作用が同じ座標でold作用×補足加法となることを全値で証明し、全local自由度/labelsを後続独立生成器へ渡せる形に固定"
    - "同じW4元全領域とchosenを含まない固定vertex領域の双方に適用し、full任意first correction/old値/全label displacement・微分・実rhsと零補足条件を評価"
  exit_criteria:
    - "各任意領域で独立new C0/C1の両逆と全計算値API、chosen所属/非所属双方の補足空間が入力から生成される"
    - "全0–3の同じ名前/値と三微分の比較が成立。領域内のfactor/path閉条件から証明し、global extensionをchain mapと扱わない"
    - "任意全rhsに対するlocal全解の両逆および全label d0作用の全成分等号。同じactual defectのrhs比較へ接続"
    - "same W4 actualT/Fを変更せず全領域と固定vertex領域で非零自由値と零補足の両方を検証"
  selection_reason: "C20入力保存から独立生成器比較へ進む際、任意領域に局所化したactual複体分解が必要。全局所方程式/全labelを比較する再利用可能な一般到達点を固定する。独立一回elimination/R_i/N_i/section/全S strict glueの比較はこの定理を使用する次到達点"
  expected_result_type: proof-obligation-discharged
  lean_targets: ["LocalizedRelativeFamilies", "SubdivisionLocalCorrections", "SubdivisionLocalLabels", "SubdivisionLocalDifferentials", "SubdivisionLocalEquations", "C21LocalSubdivisionRegression"]
  risks: ["global零延長をchain mapと誤認", "chosen非所属でfresh displacementを残す", "全核をzero-first sectionへ縮小", "local複体を旧像として定義", "微分/RHS比較fieldを入力化", "局所解だけでR_i/strict glue保存まで完了表示"]
  unchecked: ["C21の実装とfocused監査をこれから実行", "独立new/old R_i/N_i/生成sectionと全S strict glue/actual復元比較は後続", "W1–W3/W5・全targetcompletionは後続"]
```

### Cycle 21 result — 全局所相対値と三微分・全解・全label作用

各元閉領域Uに独立に定義された新旧RelativeCover C0–C3を比較する。局所族のdegreewise零延長と元support/fixed条件を持つ全global族の同値を構成し、C1は同じactual collapseと全first値を読み取る。選択辺を含まない領域では両factorの零条件から補足群が零、含む領域ではfull実fresh核の任意値を保持する。C0は全旧labelsと、選択辺が属する領域でだけfresh値から実rho1(source label)を引くdisplacementを読む。逆写像は任意旧label/補足値から全新labelを復元し、元固定条件も保持する。

C0からC1への局所微分は元端点閉包と実rho2∘rho1からold d0×identityへ比較する。C1の旧零延長は新零延長のactual collapseと同じ全族であるため、独立local d1はold d1を読む。C2/C3の全名前とwhole核はliteralに同じで、両routeのactual d2比較を同じ局所face族へ適用する。零延長をchain mapとして仮定していない。元actual defectとsigned rhsは全所属faceで同じ値を保つ。

任意relative rhsに対する独立new equationの全解はold全解×全補足群と相互逆に対応する。全relative vertex labelのd0作用は、同じ全cochain座標でold label作用と補足加法に等しい。これは各側の生成section/R_i/N_iをcopy定義する構成ではなく、後続の独立生成器比較へ渡す元全方程式・全labelの定理である。

同じW4のindependent whole affine旧repairから実correctionを取り、任意旧h・任意rを全local方程式へ接続した。復元される両factorは(r,h+r)、retained各旧補正は同じ実値、全新local解は元actual signed defectを満たす。actual rhs座標は1である。固定旧vertex labelsは元入力通り零、fresh labelの任意displacement rは同じfirst coboundary値rとなる。元固定vertex領域ではC0/C1とも補足が零で、同じ実freshOneは補足条件を満たさないことを評価した。

```yaml
ledger_type: target_cycle_result
goal: G-130-aat-relative-repair-composition
cycle: 21
goal_blob_sha: 8da0fb4eb75d1cb5c37a9d4ddf5e03c18c0bb8a2
base_oid: 35f32cf4d3861a1482fcb45fe1e60cf6fa8c67b7
tracking_issue: 5132
report_path: research/reports/G-130-aat-relative-repair-composition.md
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "任意独立局所relative複体の全0–3値、d0/d1/d2、actual defect/rhs、任意rhs全解と全label作用を元actual分割から比較。chosen所属時full supplement/非所属時zeroを両逆で生成"
  exit_criteria_status:
    - "全独立local C0/C1両逆: Family.localizedEquiv、localSupplement、local0Equiv/local1Equiv。retained全値/fresh displacement/両factor/任意inverse値API"
    - "同じ全0–3名・値と三微分: local2Equiv/local3Equiv、local_d0/local_d1/local_d2。端点閉包、actual rho2∘rho1、local1Equiv_extend、full route d2を実使用"
    - "任意rhs全解/全label成分: local_equation_iff/localEquationEquivの両逆、local_label_action、local_actual_equation_iff/local_defect/local_rhs"
    - "same W4: oldLocal_equationは独立actual repairのsolutionCorrection_d1へ接続、newLocal_first/second_coordinate/retained/actual_equation、localFreshLabel_d0/first_coordinate、excluded_label/correction_supplement/excluded_nonzero_rejected"
  split_reason: none
  completion_candidate: no
  lean_artifacts: ["LocalizedRelativeFamilies", "SubdivisionLocalCorrections", "SubdivisionLocalLabels", "SubdivisionLocalDifferentials", "SubdivisionLocalEquations", "C21LocalSubdivisionRegression"]
  evidence: ["独立RelativeCover族/微分からの構成", "全actual原核/実輸送/complete辺名と両逆", "同じW4 actual修復・全任意パラメータと零補足の正負"]
  claim_mapping:
    theorem_names: ["Family.localizedEquiv", "localSupplement", "local0Equiv", "local1Equiv", "local1Equiv_extend", "local1Equiv_inverse_first", "local1Equiv_inverse_second", "local_d0", "local_d1", "local_d2", "localEquationEquiv", "local_label_action", "local_actual_equation_iff", "C21LocalSubdivisionRegression.newLocal_second_coordinate", "C21LocalSubdivisionRegression.excluded_nonzero_rejected"]
    source_labels: ["GOAL E有限体C保存の元局所複体/全label/全方程式比較", "GOAL C独立生成器へ渡す全local入力", "GOAL F/W4同じwhole affine原操作"]
    conjuncts: ["任意領域の独立局所複体と全解/全label作用を同じ実分割で比較", "独立一回生成R_i/N_i/sectionと全S strict glue/actual復元保存は後続。全C/E保存完了へ昇格しない"]
    undischarged_assumptions: []
    acceptance_point: "固定四終了条件の元dataからのconstruction/一般定理/具体適用とfocused監査を揃えたproposal。受理は固定head標準PR gateとroot acceptance検査"
    port_status: unported
audits:
  premise_delta:
    discharged: ["full/zero supplementはchosen原所属のみから生成", "局所固定値は元Pと新expandedPの独立relative条件から導出", "d0比較は原閉包とC17実factor輸送、d1/d2はC18現actual微分比較から生成", "任意方程式比較fieldを受け取らず同じlocal_d1から全解の両逆を構成", "具体oldLocalは同じW4 independent OldRepairsからactual correctionと式を生成"]
    remaining: ["独立new/old有限local D/F/R_i/N_i/生成sectionと全S strict glue/actual復元比較", "残W1–W3/W5", "累積final packetと別fresh全target最終査読"]
  certificate_provenance:
    discharged: ["new local C0–C3は受理C11 RelativeCover定義をC20 expandedRegionへ独立適用", "localSupplementは原chosen所属predicateのみで保存結論fieldなし", "old/new solution subtypeは独立d1と指定rhs。全逆を実actual mapから生成"]
    unresolved: []
  proof_use:
    used: ["原edge閉包→fresh所属source label→displacement/d0", "chosen∉P→全局所fixed零値→C0/C1逆復元", "actual rho2∘rho1→両factord0cancel", "原full cochain collapse+d1→同じ局所d1/全解", "全route d2→局所triples", "actual W4 independent repair→旧correction式→新任意(h,r)解", "原fixedRegion chosen非所属→零補足/非零拒否"]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: ["6 production単一focused＋6 exact-current-body named milestone focused exit0/errors0/warnings0", "71明示＋生成1=72個別標準公理/欠落0", "audit sha256=e23154f6b7e953de70356e2cec058eee5056eee21e2feaa13c9df06db4c80611 / log sha256=f93df8a147d88f368eeb9279b66abc688cf9cf363bbd8f2acc1e79aa00a5cc3d", "一意registry6/current hash/placeholder/Unicode/privacy/import方向/保護領域/diff整合。Research full/aggregate/allfile/allmoduleなし"]
  blocking_findings: []
  next_obligation: "同じ任意局所複体/全label方程式比較から、独立new/old一回生成D/F/R_i/N_i/sectionと全kernel復元を比較。全S strict generated glue/actual復元、W1–W3/W5、累積completionを続行"
```

受理済C20 PR #5160/root #5945772253、C18 PR #5158/root #5944039699、C17 PR #5157/root #5943284656、C11 PR #5147/root #5925577749は、current必要statement/defs/引数/proof-useと受理refまで追跡する。今回局所構成の全premiseと全補足自由度は今回sourceで監査し、受理済内部DAGの再帰再認証は行わない。Lean4.28/mathlib `8f9d9cff6bd728b17a24e163c9402775d9e6a365`、固定GOAL blob/基準 `dbed043cb514e8c964589d2e12e982750c87ae83` は不変。

### Cycle 22 selection — 独立有限局所生成器の全公開関係・全内部自由度・全復元

```yaml
ledger_type: target_cycle_result
goal: G-130-aat-relative-repair-composition
cycle: 22
goal_blob_sha: 8da0fb4eb75d1cb5c37a9d4ddf5e03c18c0bb8a2
base_oid: 7e69ad26663a68fef08a2b8f206c1d32c02f7dad
tracking_issue: 5132
report_path: research/reports/G-130-aat-relative-repair-composition.md
selection:
  proof_state_ref: "Issue5132/C21受理PR5161/root5946287875、C20全public名/固定実値、C19実full kernel線形構造、C10/C11有限生成・全label"
  proof_dag_predecessors: ["C21独立全local C0–C3/微分/全rhs解/全label作用", "C20独立private/public名とphysical固定値", "C19同じactual fresh module/rho線形性", "C10/C11一回生成section/全R_i/N_i/復元と全labels", "C17/C18/C21 same W4"]
  milestone: "GOAL EのC保存: 各側の元全実微分から独立に一回生成する局所公開関係R_i・全私的核N_i・生成sectionの全復元を比較。全原公開名・基底成分・固定実値と全labelsを保持し、chosen所属時の全補足を落とさない"
  proof_obligations:
    - "原全実核の基底から新全基底を生成し、fresh基底はactual rho1の逆で原source基底へ接続。local C0/C1比較を同じactual scalar構造で線形化し、所属時full/非所属時zero補足を保持"
    - "任意indexed閉領域族とprivate chosenから独立new/oldの全public座標indexを相互逆に比較。元全辺名と各全核基底index、physical固定零値を保持。candidate名だけ/列像だけへ縮小しない"
    - "各側の独立FiniteNative D/Fから全private空間、実d1・range D・N_i=ker Dを同じlocal collapseで比較。新private自由度は旧全private自由度×補足であり、全核を零sectionに置換しない"
    - "各側で独立に生成section/elimination/公開関係を得て、任意rhsと任意全public値についてR_i membershipの双方を同じ元全局所解で比較。新R_i/sectionを旧出力からcopy定義せず、sectionが異なっていても全復元を比較"
    - "独立generated局所objectsの全両逆を旧generated全objects×補足と構成し、全public値、元retained補正、両factor全値、全生成private自由度を復元。全相対vertex labelsの作用を同じlocal0比較で全成分について証明し、native action groupoidの全label射へ接続"
    - "同じwhole affine W4で独立new/old生成器を適用。actual rhs、全public b、任意旧/補足値、両factor(r,h+r)、全fresh labelsを評価し、chosen非所属の固定vertex領域ではzero補足を確認"
  exit_criteria:
    - "元全基底・whole actual輸送から新基底/線形local比較/全public座標両逆を構成し、全名・全基底・physical固定値を保持"
    - "独立private Dのwhole rangeと全N_iを比較。両所属枝と全補足を保持し、独立一回生成出力のR_i membership双方が任意rhs/全public値で一致"
    - "独立generated objectsの全両逆、同じ全public値・実補正復元・全private自由度、および全元labels作用/native射比較を構成。sectionの同一性を仮定しない"
    - "same W4 full actual inputsから独立生成器へ接続し、任意全値と非所属zero補足の双方を評価"
  selection_reason: "C21全局所方程式の比較から、Eが要求するCの一回生成R_i/N_i/section保存へ直接進む。比較対象を各側で独立生成し、全S strict glue/actual復元との比較はこの一般局所到達点を使用する次到達点に残す"
  expected_result_type: proof-obligation-discharged
  lean_targets: ["SubdivisionLocalLinearCoordinates", "SubdivisionFiniteBases", "FiniteNativePublicCoordinates", "FiniteNativeArbitraryEquation", "SubdivisionGeneratedPrivate", "SubdivisionGeneratedRelations", "SubdivisionGeneratedInterfaces", "C22GeneratedSubdivisionRegression"]
  risks: ["生成出力copyから同一性を作る", "fresh基底/実核を座標に置換", "全public基底成分/固定値を失う", "section同一性を追加前提化", "全Nをzero-firstへ縮小", "全labelsを効果商へ置換", "局所保存だけで全S strict glue/completion完了表示"]
  unchecked: ["C22実装とfocused/全個別公理監査をこれから実行", "全S strict generated glue/actual復元・外部/包含比較は後続", "残W1–W3/W5と累積completion gateは後続"]
```

### Cycle 22 result — 独立局所生成出力の全関係・全核・全復元・全label射

旧全実核の各基底をretained vertexでそのまま保ち、fresh vertexの全基底はactual rho1の逆と原source基底から構成する。独立new/oldのlocal C0/C1比較を同じactual scalar構造で線形化し、選択辺に属するleafにはfull実fresh核、属さないleafには零補足を保持する。有限辺列挙は原complete辺列挙から選択辺以外と両factorの和として生成し、全new complete辺を覆うことを証明する。

新旧のprivate/public集合を既存定義で別々に作る。各nonfixed public名と全target-kernel基底成分の両逆を構成し、全public座標の読み取りがactual local collapseと可換であることを証明する。固定public名を含む全physical familyも別に比較し、指定された固定零値を保持する。固定名を除いた有限行列座標と、固定名を含む実値の族を区別して対応させる。

各側のFiniteNative D/Fは、その側の独立actual differential、full bases、private/public分解から生成する。全private空間の両逆はactual collapseから構成し、new D = old D ∘ private collapseを全private値で証明する。whole range Dは同じ原face座標で一致し、new ker Dはold全ker D×全補足群と線形同値になる。一般restriction/kernel APIが受け取る方向仮定は、今回の適用ではpublic reading identityと実d1比較から証明し、結論fieldとして供給しない。

有限体上の各側のsection/elimination/R_iは、独立入力へ同じ有限生成器を適用して得る。任意rhsと全public値について、R_i membershipが同じactual local equationの全解を介して双方向に一致する。逆方向の存在証明で零補足を使う場合も、generated objectの比較はold全object×全補足の両逆であり、private kernelやfresh自由度を零へ縮小しない。new sectionとold sectionが同じであるという仮定はない。

generated objectsの全復元は、new generated restoration → actual local cochain comparison → old independent extractionで構成する。任意old generated objectと任意補足から全new補正が復元されること、全public値が保持されることを証明する。全相対vertex labelsと全fresh displacementの比較で作用を保存し、native action groupoidの全label射と逆射へ接続する。

同じwhole affine W4へ独立生成器を適用する。actual signed rhsの座標は1、独立new/old R_iは全public b座標が1である条件と同値で、全零public vectorを拒否する。任意h,rから新生成対象を取り、完全なactual local solution、両factor(r,h+r)、各retained原補正、old生成対象と全補足rを復元する。任意fresh labelと全new生成対象についてnative作用を評価する。選択辺が属さない固定vertex領域の全生成対象では補足が零で、同じ実freshOneは拒否される。

```yaml
ledger_type: target_cycle_result
goal: G-130-aat-relative-repair-composition
cycle: 22
goal_blob_sha: 8da0fb4eb75d1cb5c37a9d4ddf5e03c18c0bb8a2
base_oid: 7e69ad26663a68fef08a2b8f206c1d32c02f7dad
tracking_issue: 5132
report_path: research/reports/G-130-aat-relative-repair-composition.md
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "各側の独立finite D/F、full基底、private/public分解、一回生成section/R_i/ker Dから、任意rhs/全public membershipと全generated objects/全native labelsの対応をactual local比較で構成"
  exit_criteria_status:
    - "全基底/linear local/public両逆とphysical固定値: LocalLinear.local0LinearEquiv/local1LinearEquiv、FiniteBases.expandedBases、GeneratedPublic.publicIndexEquiv/publicCoordinateEquiv、GeneratedPublicReadings.physical_reading_collapse"
    - "独立全private D/range/N_iと全R_i: GeneratedPrivate.privateEquiv、PrivateDifferential.private_differential/private_range/privateKernelEquiv、GeneratedRelations.newRelation/relation_iff。任意rhs/全public値とchosen所属/非所属の全補足"
    - "全generated objects/actual復元と全labels/native射: GeneratedInterfaces.objectsEquiv/objectsEquiv_inverse_correction/objectsEquiv_public/objects_equivariant/groupoidEquivalence/groupoid_functor_label/groupoid_inverse_label"
    - "same whole W4: actual_rhs_coordinate、old/new_relation_iff、old/new_zero_public_rejected、generated_coordinates/first_coordinate/second_coordinate/retained/label_action、excluded_generated_supplement/nonzero_rejected。current production focused exit0で全50宣言を確認"
  split_reason: none
  completion_candidate: no
  lean_artifacts: ["SubdivisionLocalLinearCoordinates", "SubdivisionFiniteBases", "FiniteNativeArbitraryEquation", "FiniteNativePublicCoordinates", "SubdivisionFiniteIncidence", "SubdivisionGeneratedPublicReadings", "LinearPrivateComparison", "SubdivisionGeneratedPrivate", "LinearPrivateKernel", "SubdivisionPrivateDifferential", "SubdivisionFiniteEnumerations", "SubdivisionGeneratedRelations", "SupplementalAction", "SubdivisionGeneratedInterfaces", "C22GeneratedSubdivisionRegression"]
  evidence: ["同じ元actual全核・実rho1/rho2からfull基底とlocal線形両逆", "各側の独立全private/public分解とactual D/Fから一回有限生成", "任意rhs/全public関係の双方と全kernel自由度", "同じwhole W4 actual入力から全生成修復・全復元・native作用と非所属zero補足"]
  claim_mapping:
    theorem_names: ["LocalLinear.local0LinearEquiv", "LocalLinear.local1LinearEquiv", "FiniteBases.expandedBases", "FiniteBases.expanded_coordinate_fresh_inverse", "GeneratedPublic.publicIndexEquiv", "GeneratedPublic.publicCoordinateEquiv", "GeneratedPublicReadings.public_reading_collapse", "GeneratedPublicReadings.physical_reading_collapse", "GeneratedPrivate.privateEquiv", "GeneratedPrivate.private_cochain_collapse", "PrivateDifferential.private_differential", "PrivateDifferential.private_range", "PrivateDifferential.privateKernelEquiv", "FiniteEnumerations.edgeEnumeration", "FiniteEnumerations.edgeEnumeration_complete", "FiniteNative.generatedRelativeEquiv", "FiniteNative.generated_relation_iff_relative", "GeneratedRelations.newGeneratedEquiv", "GeneratedRelations.relation_iff", "GeneratedInterfaces.objectsEquiv", "GeneratedInterfaces.objectsEquiv_inverse_correction", "GeneratedInterfaces.objectsEquiv_public", "GeneratedInterfaces.objects_equivariant", "GeneratedInterfaces.groupoidEquivalence", "GeneratedInterfaces.groupoid_functor_label", "GeneratedInterfaces.groupoid_inverse_label", "C22GeneratedSubdivisionRegression.new_relation_iff", "C22GeneratedSubdivisionRegression.generated_coordinates", "C22GeneratedSubdivisionRegression.generated_second_coordinate", "C22GeneratedSubdivisionRegression.generated_label_action", "C22GeneratedSubdivisionRegression.excluded_generated_nonzero_rejected"]
    source_labels: ["GOAL E内部辺分割の有限体C保存", "GOAL C同じ全private/shared/candidate・一回生成R_i/N_i/section/全復元", "GOAL F/W4同じ原whole affine geometry・実操作・指定factors"]
    conjuncts: ["選定六義務/四終了条件の一般構成と同じW4への適用", "全S strict generated glue/actual復元・包含・外部比較は後続。局所保存を全C/Eまたは全target完了へ昇格しない"]
    undischarged_assumptions: []
    acceptance_point: "固定六義務・四終了条件の一般構成/具体適用とcurrent production・個別公理監査を揃えたproposal。受理は固定head標準PR gateとroot acceptance検査"
    port_status: unported
audits:
  premise_delta:
    discharged: ["新full基底/Module: actual rho1の全核同型と元full基底から構成", "有限new complete辺列挙/判定: 原complete列挙と元membershipから生成", "全private comparison law: 原全public読み取りidentityから証明", "whole private D comparison: independent実d1とactual local collapseから証明", "独立new/old R_i/section: 各側の実行列と原有限生成器から生成。section等号fieldなし", "全label equivariance: 実local d0比較と各独立native extraction作用から証明", "W4全入力条件: accepted同じwhole affine原操作/geometry/factorsに今回生成器を適用"]
    remaining: ["全S strict generated glue/actual復元と同じ包含・外部比較", "残W1–W3/W5", "累積final packetと別fresh全target最終査読"]
  certificate_provenance:
    discharged: ["FiniteBases.expandedBasesのfresh座標はactual rho1 inverse、retainedは元基底", "new D/F/section/R_i/kernelは独立new full微分と座標分解から生成。old出力copyなし", "general private comparison/kernel direction hypothesesは今回actual public/d1 identityで放電", "W4のold/newExtractionは同じactual全入力へ各側の生成器を具体化。全parameter/全inverse/全labelsを保持"]
    unresolved: []
  proof_use:
    used: ["元全basis/actual rho1→新全basis/補足scalar", "原private非共有/chosen非candidate→全public名/全基底対応/独立new membership", "actual全local C1両逆とpublic law→whole private線形両逆", "actual local_d1とwhole private collapse→独立D/range/kerD", "各側complete列挙/actual D/F→独立section/R_i→任意全rhs/local解の双方", "全local0/d0比較→native作用/全label射の両方向", "同じactual W4 signed defect/全修復→public b=1/零拒否/任意(h,r)全復元", "原固定leaf chosen非所属→全生成対象の零補足/同じ非零fresh拒否"]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: ["15 current production単一非aggregate focused exit0/errors0/warnings0・source/log hash一致。W4同じ全50宣言/native作用も確認", "167明示＋生成1=168個別#print axioms・欠落0/非標準公理0/errors0/warnings0。実本体elaborationは各production focused、個別公理はcurrent compiled moduleから別に確認。audit sha256=a8db1b5882777fb5e023abe1a50b66b4faaecd0af601a16ef120ba1cbfef8fb8 / log sha256=d50aad4f1f2cb62445f4468cfc4faa665a822ec86b2bd6b50389aae88917e709", "registry/current hash/placeholder/Unicode/privacy/import方向/保護領域/diff整合。Research full/aggregate/allfile/allmodule elaborationなし"]
  blocking_findings: []
  next_obligation: "今回の独立全local R_i/N_i/section/全label/actual復元比較から、全S strict generated glueと同じactual全修復・包含・外部比較へ接続する。その後残W1–W3/W5と累積completion gateを続行"
```

受理済C21 PR #5161/root #5946287875、C20 PR #5160/root #5945772253、C19 PR #5159/root #5945142965、C11 PR #5147/root #5925577749は、current必要statement/defs/適用引数/proof-useと各受理source版まで追跡する。今回構成する全new生成器・全private comparison・全label actionとsame W4適用は今回の監査対象であり、受理済内部DAGの再帰再認証は行わない。Lean4.28/mathlib `8f9d9cff6bd728b17a24e163c9402775d9e6a365`、固定GOAL blob/基準 `dbed043cb514e8c964589d2e12e982750c87ae83` は不変。

<details>
<summary>C22の固定宣言spine（167明示宣言）</summary>

`SubdivisionLocalLinearCoordinates.lean`（10）：

```text
AAT.AG.RelativeRepairComposition.Family.extend_smul
AAT.AG.RelativeRepairComposition.Subdivision.LocalLinear.supplementSMul
AAT.AG.RelativeRepairComposition.Subdivision.LocalLinear.supplementModule
AAT.AG.RelativeRepairComposition.Subdivision.LocalLinear.supplement_smul_value
AAT.AG.RelativeRepairComposition.Subdivision.LocalLinear.local1_smul
AAT.AG.RelativeRepairComposition.Subdivision.LocalLinear.local1LinearEquiv
AAT.AG.RelativeRepairComposition.Subdivision.LocalLinear.local1LinearEquiv_value
AAT.AG.RelativeRepairComposition.Subdivision.LocalLinear.local0_smul
AAT.AG.RelativeRepairComposition.Subdivision.LocalLinear.local0LinearEquiv
AAT.AG.RelativeRepairComposition.Subdivision.LocalLinear.local0LinearEquiv_value
```

`SubdivisionFiniteBases.lean`（7）：

```text
AAT.AG.RelativeRepairComposition.Subdivision.FiniteBases.expandedBases
AAT.AG.RelativeRepairComposition.Subdivision.FiniteBases.expanded_dimension_old
AAT.AG.RelativeRepairComposition.Subdivision.FiniteBases.expanded_dimension_fresh
AAT.AG.RelativeRepairComposition.Subdivision.FiniteBases.expanded_coordinate_old
AAT.AG.RelativeRepairComposition.Subdivision.FiniteBases.expanded_coordinate_fresh
AAT.AG.RelativeRepairComposition.Subdivision.FiniteBases.expanded_coordinate_fresh_inverse
AAT.AG.RelativeRepairComposition.Subdivision.FiniteBases.expanded_fresh_roundtrip
```

`FiniteNativeArbitraryEquation.lean`（14）：

```text
AAT.AG.RelativeRepairComposition.FiniteNative.RelativeEquation
AAT.AG.RelativeRepairComposition.FiniteNative.ArbitraryMatrixEquation
AAT.AG.RelativeRepairComposition.FiniteNative.relativeEquationCoordinates
AAT.AG.RelativeRepairComposition.FiniteNative.relativeEquationCoordinates_value
AAT.AG.RelativeRepairComposition.FiniteNative.relative_equation_coordinates_equivariant
AAT.AG.RelativeRepairComposition.FiniteNative.GeneratedRelativeObjects
AAT.AG.RelativeRepairComposition.FiniteNative.generatedRelativeEquiv
AAT.AG.RelativeRepairComposition.FiniteNative.generatedRelativeEquiv_public
AAT.AG.RelativeRepairComposition.FiniteNative.generatedRelativeEquiv_inverse_public
AAT.AG.RelativeRepairComposition.FiniteNative.generated_relative_equivariant
AAT.AG.RelativeRepairComposition.FiniteNative.generatedRelation
AAT.AG.RelativeRepairComposition.FiniteNative.generated_relation_iff_relative
AAT.AG.RelativeRepairComposition.FiniteNative.GeneratedRelativeGroupoid
AAT.AG.RelativeRepairComposition.FiniteNative.generatedRelativeEquationEquivalence
```

`FiniteNativePublicCoordinates.lean`（10）：

```text
AAT.AG.RelativeRepairComposition.FiniteNative.publicIndexEquiv
AAT.AG.RelativeRepairComposition.FiniteNative.publicIndexEquiv_name
AAT.AG.RelativeRepairComposition.FiniteNative.publicIndexEquiv_basis
AAT.AG.RelativeRepairComposition.FiniteNative.publicIndexEquiv_inverse
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedPublic.publicIndexEquiv
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedPublic.publicIndexEquiv_name
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedPublic.publicIndexEquiv_inverse_basis
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedPublic.publicCoordinateEquiv
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedPublic.publicCoordinateEquiv_value
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedPublic.publicCoordinateEquiv_inverse_value
```

`SubdivisionFiniteIncidence.lean`（6）：

```text
AAT.AG.RelativeRepairComposition.Subdivision.FiniteIncidence.expandedVerticesDecidable
AAT.AG.RelativeRepairComposition.Subdivision.FiniteIncidence.expandedEdgesDecidable
AAT.AG.RelativeRepairComposition.Subdivision.FiniteIncidence.expandedFacesDecidable
AAT.AG.RelativeRepairComposition.Subdivision.FiniteIncidence.expandedTriplesDecidable
AAT.AG.RelativeRepairComposition.Subdivision.FiniteIncidence.retainedSetDecidable
AAT.AG.RelativeRepairComposition.Subdivision.FiniteIncidence.retained_set_test
```

`SubdivisionGeneratedPublicReadings.lean`（5）：

```text
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedPublicReadings.retainedCandidatesDecidable
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedPublicReadings.oldPublic
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedPublicReadings.newPublic
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedPublicReadings.public_reading_collapse
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedPublicReadings.physical_reading_collapse
```

`LinearPrivateComparison.lean`（11）：

```text
AAT.AG.RelativeRepairComposition.LinearPrivateComparison.forward_public_zero
AAT.AG.RelativeRepairComposition.LinearPrivateComparison.inverse_public_zero
AAT.AG.RelativeRepairComposition.LinearPrivateComparison.forward
AAT.AG.RelativeRepairComposition.LinearPrivateComparison.restore
AAT.AG.RelativeRepairComposition.LinearPrivateComparison.forward_value
AAT.AG.RelativeRepairComposition.LinearPrivateComparison.restore_value
AAT.AG.RelativeRepairComposition.LinearPrivateComparison.forward_insert
AAT.AG.RelativeRepairComposition.LinearPrivateComparison.restore_insert
AAT.AG.RelativeRepairComposition.LinearPrivateComparison.equivalence
AAT.AG.RelativeRepairComposition.LinearPrivateComparison.equivalence_value
AAT.AG.RelativeRepairComposition.LinearPrivateComparison.equivalence_inverse_value
```

`SubdivisionGeneratedPrivate.lean`（9）：

```text
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedPrivate.newSplit
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedPrivate.newSplit_public
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedPrivate.fullComparison
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedPrivate.fullComparison_value
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedPrivate.fullComparison_public
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedPrivate.privateEquiv
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedPrivate.privateEquiv_value
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedPrivate.privateEquiv_inverse_value
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedPrivate.private_cochain_collapse
```

`LinearPrivateKernel.lean`（4）：

```text
AAT.AG.RelativeRepairComposition.LinearPrivateKernel.range_eq
AAT.AG.RelativeRepairComposition.LinearPrivateKernel.equivalence
AAT.AG.RelativeRepairComposition.LinearPrivateKernel.equivalence_value
AAT.AG.RelativeRepairComposition.LinearPrivateKernel.equivalence_inverse_value
```

`SubdivisionPrivateDifferential.lean`（9）：

```text
AAT.AG.RelativeRepairComposition.FiniteNative.D_value
AAT.AG.RelativeRepairComposition.Subdivision.PrivateDifferential.newD
AAT.AG.RelativeRepairComposition.Subdivision.PrivateDifferential.newD_value
AAT.AG.RelativeRepairComposition.Subdivision.PrivateDifferential.face_coordinates
AAT.AG.RelativeRepairComposition.Subdivision.PrivateDifferential.private_differential
AAT.AG.RelativeRepairComposition.Subdivision.PrivateDifferential.private_range
AAT.AG.RelativeRepairComposition.Subdivision.PrivateDifferential.privateKernelEquiv
AAT.AG.RelativeRepairComposition.Subdivision.PrivateDifferential.privateKernelEquiv_value
AAT.AG.RelativeRepairComposition.Subdivision.PrivateDifferential.privateKernelEquiv_inverse_value
```

`SubdivisionFiniteEnumerations.lean`（8）：

```text
AAT.AG.RelativeRepairComposition.FiniteElimination.Enumeration.mapEquiv
AAT.AG.RelativeRepairComposition.FiniteElimination.Enumeration.mapEquiv_values
AAT.AG.RelativeRepairComposition.FiniteElimination.Enumeration.sum
AAT.AG.RelativeRepairComposition.Subdivision.FiniteEnumerations.factorEnumeration
AAT.AG.RelativeRepairComposition.Subdivision.FiniteEnumerations.edgeDecidableEq
AAT.AG.RelativeRepairComposition.Subdivision.FiniteEnumerations.edgeEnumeration
AAT.AG.RelativeRepairComposition.Subdivision.FiniteEnumerations.edgeEnumeration_complete
AAT.AG.RelativeRepairComposition.Subdivision.FiniteEnumerations.edgeFintype
```

`SubdivisionGeneratedRelations.lean`（8）：

```text
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedRelations.newGeneratedObjects
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedRelations.newRelation
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedRelations.newGeneratedEquiv
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedRelations.newGeneratedEquiv_inverse_apply
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedRelations.newGeneratedEquiv_public
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedRelations.newGeneratedEquiv_inverse_public
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedRelations.new_relation_iff_relative
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedRelations.relation_iff
```

`SupplementalAction.lean`（2）：

```text
AAT.AG.RelativeRepairComposition.SupplementalAction.productAddAction
AAT.AG.RelativeRepairComposition.SupplementalAction.product_action_value
```

`SubdivisionGeneratedInterfaces.lean`（14）：

```text
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedInterfaces.labelsEquiv
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedInterfaces.labelsEquiv_value
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedInterfaces.newGeneratedAddAction
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedInterfaces.new_generated_equivariant
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedInterfaces.objectsEquiv
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedInterfaces.objectsEquiv_value
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedInterfaces.objectsEquiv_coordinates
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedInterfaces.objectsEquiv_inverse_coordinates
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedInterfaces.objects_equivariant
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedInterfaces.groupoidEquivalence
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedInterfaces.groupoid_functor_label
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedInterfaces.groupoid_inverse_label
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedInterfaces.objectsEquiv_public
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedInterfaces.objectsEquiv_inverse_correction
```

`C22GeneratedSubdivisionRegression.lean`（50）：

```text
AAT.AG.RelativeRepairComposition.C22GeneratedSubdivisionRegression.edgeDecidableEq
AAT.AG.RelativeRepairComposition.C22GeneratedSubdivisionRegression.faceDecidableEq
AAT.AG.RelativeRepairComposition.C22GeneratedSubdivisionRegression.allVerticesDecidable
AAT.AG.RelativeRepairComposition.C22GeneratedSubdivisionRegression.allEdgesDecidable
AAT.AG.RelativeRepairComposition.C22GeneratedSubdivisionRegression.allFacesDecidable
AAT.AG.RelativeRepairComposition.C22GeneratedSubdivisionRegression.regionsVerticesDecidable
AAT.AG.RelativeRepairComposition.C22GeneratedSubdivisionRegression.regionsEdgesDecidable
AAT.AG.RelativeRepairComposition.C22GeneratedSubdivisionRegression.regionsFacesDecidable
AAT.AG.RelativeRepairComposition.C22GeneratedSubdivisionRegression.fixedEdgesDecidable
AAT.AG.RelativeRepairComposition.C22GeneratedSubdivisionRegression.fixedFacesDecidable
AAT.AG.RelativeRepairComposition.C22GeneratedSubdivisionRegression.bases
AAT.AG.RelativeRepairComposition.C22GeneratedSubdivisionRegression.enumK
AAT.AG.RelativeRepairComposition.C22GeneratedSubdivisionRegression.enumEdges
AAT.AG.RelativeRepairComposition.C22GeneratedSubdivisionRegression.enumFaces
AAT.AG.RelativeRepairComposition.C22GeneratedSubdivisionRegression.basisIndex
AAT.AG.RelativeRepairComposition.C22GeneratedSubdivisionRegression.basis_value
AAT.AG.RelativeRepairComposition.C22GeneratedSubdivisionRegression.OldPublicIndex
AAT.AG.RelativeRepairComposition.C22GeneratedSubdivisionRegression.publicIndex
AAT.AG.RelativeRepairComposition.C22GeneratedSubdivisionRegression.publicIndex_unique
AAT.AG.RelativeRepairComposition.C22GeneratedSubdivisionRegression.actual_rhs_coordinate
AAT.AG.RelativeRepairComposition.C22GeneratedSubdivisionRegression.old_solution_candidate
AAT.AG.RelativeRepairComposition.C22GeneratedSubdivisionRegression.old_solution_public
AAT.AG.RelativeRepairComposition.C22GeneratedSubdivisionRegression.old_relation_iff
AAT.AG.RelativeRepairComposition.C22GeneratedSubdivisionRegression.NewPublicIndex
AAT.AG.RelativeRepairComposition.C22GeneratedSubdivisionRegression.newPublicIndex
AAT.AG.RelativeRepairComposition.C22GeneratedSubdivisionRegression.new_relation_iff
AAT.AG.RelativeRepairComposition.C22GeneratedSubdivisionRegression.old_zero_public_rejected
AAT.AG.RelativeRepairComposition.C22GeneratedSubdivisionRegression.new_zero_public_rejected
AAT.AG.RelativeRepairComposition.C22GeneratedSubdivisionRegression.oldExtraction
AAT.AG.RelativeRepairComposition.C22GeneratedSubdivisionRegression.newExtraction
AAT.AG.RelativeRepairComposition.C22GeneratedSubdivisionRegression.interfaceComparison
AAT.AG.RelativeRepairComposition.C22GeneratedSubdivisionRegression.interfaceComparison_value
AAT.AG.RelativeRepairComposition.C22GeneratedSubdivisionRegression.oldGenerated
AAT.AG.RelativeRepairComposition.C22GeneratedSubdivisionRegression.newGenerated
AAT.AG.RelativeRepairComposition.C22GeneratedSubdivisionRegression.old_generated_public
AAT.AG.RelativeRepairComposition.C22GeneratedSubdivisionRegression.new_generated_public
AAT.AG.RelativeRepairComposition.C22GeneratedSubdivisionRegression.newGenerated_restore
AAT.AG.RelativeRepairComposition.C22GeneratedSubdivisionRegression.generated_coordinates
AAT.AG.RelativeRepairComposition.C22GeneratedSubdivisionRegression.generated_first_coordinate
AAT.AG.RelativeRepairComposition.C22GeneratedSubdivisionRegression.generated_second_coordinate
AAT.AG.RelativeRepairComposition.C22GeneratedSubdivisionRegression.generated_retained
AAT.AG.RelativeRepairComposition.C22GeneratedSubdivisionRegression.labelsComparison
AAT.AG.RelativeRepairComposition.C22GeneratedSubdivisionRegression.generated_label_coordinates
AAT.AG.RelativeRepairComposition.C22GeneratedSubdivisionRegression.labelsComparison_fresh
AAT.AG.RelativeRepairComposition.C22GeneratedSubdivisionRegression.newInterfaceAction
AAT.AG.RelativeRepairComposition.C22GeneratedSubdivisionRegression.oldInterfaceAction
AAT.AG.RelativeRepairComposition.C22GeneratedSubdivisionRegression.productInterfaceAction
AAT.AG.RelativeRepairComposition.C22GeneratedSubdivisionRegression.generated_label_action
AAT.AG.RelativeRepairComposition.C22GeneratedSubdivisionRegression.excluded_generated_supplement
AAT.AG.RelativeRepairComposition.C22GeneratedSubdivisionRegression.excluded_generated_nonzero_rejected
```

</details>

生成された `FiniteCoefficients.differential1.congr_simp` も、今回のproduction module所属から選定して個別公理監査に含めた。上記全明示宣言と合わせて168件である。

### Cycle 23 selection — 独立生成局所出力の全範囲strict貼り合わせと実修復

```yaml
ledger_type: target_cycle_result
goal: G-130-aat-relative-repair-composition
cycle: 23
goal_blob_sha: 8da0fb4eb75d1cb5c37a9d4ddf5e03c18c0bb8a2
base_oid: 9c17b108dab644d58e2ae564eb32430fffc58aef
tracking_issue: 5132
report_path: research/reports/G-130-aat-relative-repair-composition.md
selection:
  proof_state_ref: "C22 PR #5162/root #5950334454、Issue #5132、current GeneratedInterfaces/GeneratedCoverRestoration/SubdivisionPermissions"
  proof_dag_predecessors: ["C22独立local R_i/N_i/section/全objects/全labels", "C21actual任意local複体/方程式/全補足", "C20全closed cover/private/public/physical固定値", "C17同じactual全S分割/厳密W/外部/包含", "C11全S generated strict coverと全actual復元"]
  milestone: "GOAL E有限体で各側の独立C出力を全Sのstrict公開条件で貼り合わせ、全private自由度・実修復・全native射・範囲包含・外部との合成を同じ縮約/全復元で保存"
  proof_obligations:
    - "各側の独立生成局所objects/public readingに、元候補零条件と全共有実値等号を独立に課す。全SでC22 local比較が同じstrict述語を双方へ輸送"
    - "全局所補足族はprivate ownerの全actual fresh核と両逆。非所属leaf零を導出し、旧全strict対象と全補足から新全対象を復元"
    - "全strict局所vertex labelsとfresh displacement、全生成対象の作用、native全label射を比較し、contractible fresh作用を介して旧全groupoidとの同値を構成"
    - "独立new/old全actual修復と生成strict objectsの両逆を接続。C22の各局所objectsEquivと同じ縮約/両factor全復元・retained値を全成分で比較"
    - "全Sの同じ生成器・section/関係/核を共用し、全S⊆Vの包含と座標/復元・全native射、厳密W値と全actual外部合成が可換"
    - "同じwhole affine W4の両許可範囲について、候補b=1の成功/禁止時失敗、全(h,r)の全生成復元、full fresh native作用と元実修復への比較を具体評価"
  exit_criteria:
    - "独立new/old strict公開述語のiffと全object両逆、全public/physical固定値/全private核/補足を保存"
    - "全native labels・射・逆・自然同型を保持するstrict groupoid比較と同じ全actual修復への全方向接続"
    - "全範囲包含・strict W・全actual外部へのobject/arrow/composition比較とC22 local比較の全成分一致"
    - "sameW4全S正負例・全補正/復元/native作用を現行focusedと全対象個別公理で確認。標準PRゲート/root受入を実施"
  selection_reason: "C22の独立局所保存をGOAL C/Eの全S strict計算・実修復に接続し、有限体分割保存の残る大域gapを閉じる"
  expected_result_type: proof-obligation-discharged
  lean_targets: ["SubdivisionGeneratedStrictConditions", "SubdivisionSupplementFamilies", "SubdivisionGeneratedStrictObjects", "SubdivisionGeneratedCoverRestoration", "SubdivisionGeneratedCoverLabels", "SubdivisionGeneratedCoverRanges", "SubdivisionGeneratedExternal", "C23GeneratedStrictRegression"]
  risks: ["独立new述語をold述語から定義してしまう", "全補足を零へ制限", "strict共有全label射の欠落", "actual修復と局所生成比較の接続不足", "全Sと包含を固定一範囲へ縮める", "sameW4を局所だけの検証に留める"]
  unchecked: ["上記六義務の現在未実装部分。completion candidateにはしない"]
```

### Cycle 23 result — 全範囲strict独立生成・全native射・元の実修復への対応

```yaml
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta:
    - "独立new/oldの全local objectsへ元候補零条件と全共有実値等号を独立に課し、同じlocal比較でstrict述語のiffを構成"
    - "全SupplementFamilyとprivate ownerの全actual fresh核を両逆で比較。非owner零はincidenceから導出"
    - "全strict labels/fresh displacement/全native作用・射を比較し、contractible fresh translation作用の自然同型から全groupoid同値を構成"
    - "独立全actual修復と全generated strict対象の両逆・全local比較・両factorと全retained実値を接続"
    - "同じgenerator/section/relation/kernelを全Sで共用し、全S包含の関手等号とstrict W・全actual外部のobject/arrow/identity/compositionを比較"
    - "同じwhole affine W4の全Sについてb許可iff、全h/rの生成数3/9、全復元(r,h+r)、全strict fresh labelsと作用(r↦r+t)、元のnative実修復への対応を評価"
  exit_criteria_status:
    - "独立strict述語と全対象/全補足の両逆: RelativeGeneratedStrictCover.compatibility_iff、GeneratedStrictConditions.compatibility_iff、SupplementFamilies.equivalence、GeneratedStrictObjects.objectsEquiv"
    - "全native labels/射/自然同型と全actual修復: GeneratedCoverLabels.equivalence、GeneratedGroupoidEquivalence.equivalence/fullRestoreIso、GeneratedCoverRestoration.newObjectEquiv、GeneratedActualNative.equivalence"
    - "全包含/strict W/全actual外部とlocal比較: GeneratedNativeRanges.comparison_functor、GeneratedActualRanges.native_extraction_include、GeneratedExternal.shared_comparison、GeneratedNativeExternal.nativeHomEquiv、GeneratedLocalCorrectionBridge.component_heq_of_rhs_eq"
    - "same W4全S/全値/全labels: C23GeneratedStrictParameters、C23ActualLocalCorrection、C23GeneratedStrictRegression、C23GeneratedStrictNativeRegressionの全41宣言とgeneric bridge2。30 production focusedと236個別公理監査は完了。受理判定は固定head標準PR gateとroot acceptance"
  split_reason: none
  completion_candidate: no
  lean_artifacts: ["下記30source・233明示宣言と3生成補助を含む236個別宣言spine"]
  evidence: ["独立strict公開述語の双方", "全private owner補足と非owner零の導出", "全object/label両逆とnative自然同型", "全actual修復・全辺実値との比較", "同じ全S generatorと包含/外部の全関手比較", "同じwhole affine W4の全許可範囲と全h/r/t"]
  claim_mapping:
    theorem_names: ["GeneratedStrictObjects.objectsEquiv", "GeneratedCoverLabels.equivalence", "GeneratedCoverAction.objects_equivariant", "GeneratedGroupoidEquivalence.equivalence", "GeneratedCoverRestoration.newObjectEquiv", "GeneratedActualComparison.comparison_actual_restore", "GeneratedActualNative.equivalence", "GeneratedNativeRanges.comparison_functor", "GeneratedActualRanges.native_extraction_include", "GeneratedNativeExternal.nativeHomEquiv", "C23GeneratedStrictParameters.new_nonempty_iff", "C23GeneratedStrictRegression.new_owner_component", "C23GeneratedStrictNativeRegression.native_label_action"]
    source_labels: ["GOAL C全S strict生成・全実修復", "GOAL E内部辺分割のC保存と全native射・strict W・全actual外部", "GOAL F/W4同じwhole affine原操作・全核・指定factors"]
    conjuncts: ["固定六義務と四終了条件の一般構成および同じW4への適用"]
    undischarged_assumptions: []
    acceptance_point: "同じ独立生成器の全対象と全labelsを元の実修復へ接続した到達点proposal。受理は固定headの標準PRレビューとroot検査"
    port_status: unported
audits:
  premise_delta:
    discharged: ["新旧strict述語は各側で独立生成しactual full cochain比較からiffを証明", "nonowner補足零はprivate chosenの非共有incidenceから導出", "全label比較/作用/自然同型はactual d0と全fresh translationから構成", "全actual逆・包含・外部比較は同じ元操作とnative labelから導出", "W4のrhs等号・全local correctionはowner_rhs/actual_local_correctionで導出。target前提への追加なし"]
    remaining: ["固定W1–W3/W5の全指定実入力・具体判定・一般定理との接続", "累積全target final packetと別fresh Math2/Lean2 completion gate"]
  certificate_provenance:
    discharged: ["独立new/old全local D/FとC22 full生成器から全strict対象を構成", "全SupplementFamily/全strict labelsは元full核とincidenceから構成", "standard action categoryの全carrier/全labelsと原fresh translationからnative比較を構成", "W4は同じ受理済whole affine塔・baa面・元P・候補b・両指定factorsへ今回生成器を適用"]
    unresolved: []
  proof_use:
    used: ["private owner/非共有→nonowner零と全補足両逆", "独立public読み取り→strict iffと全対象両逆", "全local d0/labels→native作用・自然同型・全射比較", "元actual修復/local C1→各辺等号→C22全local出力の一致", "同じ全S関係→包含全関手等号", "strict Wの元実値/元環境vertex-kernel map→全actual外部のidentity/composition", "W4原signed defect/全h,r→生成成功/禁止失敗/全復元、全t→native作用"]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: ["30 selected production sourceのfocused exit0/errors0/warnings0・現source/log hash一致。明示namespace233宣言", "185+8+43=236全個別#print axioms、非標準公理0・欠落0。下記source/spineと監査hashを固定", "registry/placeholder/Unicode/privacy/import方向/diff整合。Research full/aggregate/allfile/allmodule elaborationなし"]
  blocking_findings: []
  next_obligation: "固定W1–W3/W5を元whole affine操作・元geometry・全native修復/全固定条件で構成し、一般A–Fへの具体接続と全指定判定を閉じる。その後累積completion packetと別四本最終査読"
```

受理済C22 PR #5162/root #5950334454、C21 PR #5161/root #5946287875、C20 PR #5160/root #5945772253、C17 PR #5157/root #5943284656、C11 PR #5147/root #5925577749は、current必要statement/defs/適用引数/proof-useと各受理source版まで追跡する。今回の独立strict生成・全native作用・全actual比較とW4適用を今回の監査対象とする。Lean4.28/mathlib `8f9d9cff6bd728b17a24e163c9402775d9e6a365`、固定GOAL blob/基準 `dbed043cb514e8c964589d2e12e982750c87ae83` は不変。

### 独立生成・strict条件・全実修復への対応

宣言は `AAT.AG.RelativeRepairComposition` 以下に置く。
旧側と新側は、それぞれの全局所微分・実全核の基底・列挙・同じ実signed defectから独立に生成する。
`GeneratedStrictObjects.NewObjects` は新側の独立 `GeneratedRelations.newGeneratedObjects` を各成分にそのまま保持し、同じ新側の `PublicCompatible` を課す。
`RelativeGeneratedStrictCover.PublicCompatible` は禁止候補の実公開値零と共有辺の全実値等号を独立に課す。
`Subdivision.GeneratedStrictConditions.compatibility_iff` がこの条件を全補正族へ輸送し、
`GeneratedStrictObjects.objectsEquiv` が新側の全strict対象と旧側の全strict対象×全fresh核を相互に復元する。
非所有領域の補足零はprivate incidenceから導き、所有領域の補足は零に限定しない。

全局所vertex labelsは `GeneratedCoverLabels.equivalence` により旧全strict labelsとfresh displacementへ対応する。
`GeneratedCoverAction.objects_equivariant` は元の実d0作用を同じ比較へ接続する。
`SupplementalGroupoidContraction.counitIso` は全fresh値を保ったtranslation作用から自然同型を与え、
`GeneratedGroupoidEquivalence.equivalence/fullRestoreIso` は全対象・異なる全ラベル射・逆関手と復元比較を保持する。

`RelativeActualGeneratedCover.objectEquiv` と `GeneratedCoverRestoration.newObjectEquiv` は、
独立に定めた元の実修復と独立生成strict対象を両方向へ戻す。
`GeneratedActualComparison.comparison_actual_restore/comparison_restore_edge_value` は両因子と全retained辺の元の実値を比較し、
`GeneratedActualNative.equivalence` は元の頂点核自己同型を全射へ対応させる。
`GeneratedLocalCorrectionBridge.component_eq` は全局所余鎖の各辺等号から独立生成の成分等号を導く。
`component_heq_of_rhs_eq` は同じ実右辺の等号を明示して依存する局所解を輸送し、W4では `owner_rhs` でその等号を放電して元の成分等号へ戻す。`generated_owner_equality` と両端の等号は、この独立生成の等号を元の3つのstatementへ合成するproof supportである。C22で使用した `RingHomInvPair` / `NeZero` の証明引数を局所的に再利用し、生成器の数学的入力は同一に保つ。
W4への適用で受け取る各辺等号は `C23ActualLocalCorrection.actual_local_correction` が全S・全h/r・全新辺について証明し、
固定targetの前提として追加しない。

全Sでは同じ局所関係・kernel・sectionを使う。
`GeneratedNativeRanges.comparison_functor` と `GeneratedActualRanges.native_extraction_include` は全S⊆Vの全関手等号を証明する。
`GeneratedExternal.shared_comparison` は双方を元の実W値から独立に読み、
`GeneratedExternalArrows.externalHomEquiv` と `GeneratedNativeExternal.nativeHomEquiv` は外部の元の実頂点核写像による全compatible射を対応させる。
恒等と合成は同じ元の実ラベルで比較する。

### 同じwhole affine W4と前提の使用

`C23GeneratedStrictParameters` は、受理済みの同じwhole affine塔、指定baa面、元の固定頂点領域、候補b、実二因子を使う。
`old_nonempty_iff/new_nonempty_iff` は全Sで元のb許可と全独立生成対象の存在を同値にする。
許可時の `oldGeneratedEquiv/newGeneratedEquiv` は全hと全(h,r)を回復し、全対象数は3と9になる。
所有領域の三宣言はこの全大域出力をC22の独立局所出力と同じ値で比較する。
native回帰の全ラベル対応は、fresh displacement tによる(h,r)↦(h,r+t)を元の実再同定として保持する。
両実因子の復元値は(r,h+r)である。`rangeGroupoid` は同じ全strictラベルと全独立生成対象の標準作用圏であり、`generatedObj` は生成族全体をその標準対象へ入れる。`freshArrow` はこの作用圏の元の全ラベルtを保持する射として構成する。
同じ元の実修復への全対応を介して、受理済みC17の同型類3・自明自己同型、および新頂点を固定した別入力の同型類9へ接続する。

| material premise | 出所・分類 | 使用先・放電 |
| --- | --- | --- |
| 元の一般塔・全核・輸送・実微分・比較 | GOAL A/Eの原始入力・direction hypothesis | 全補正とnative作用を同じ型付き実辺から生成 |
| 閉被覆・private owner・固定P・候補名 | GOAL C/Eの入力条件 | 非owner零と独立public条件、全補足復元、strict W比較 |
| 有限体・実全核の有限基底・列挙・線形輸送 | GOAL Cの入力条件 | 元の0〜3セルの独立局所生成器、同じ全S relation/kernel/section |
| 同じ実右辺の等号と全局所補正の各辺等号 | 一般の依存等号輸送APIへの量化仮定 | W4適用ではowner_rhsとactual_local_correctionにより元のsigned defectと実展開から全て導出 |
| 新旧strict比較・全射・包含・外部合成 | discharge-required | 全object両逆、全label両逆、native作用・自然同型・関手等号で構成 |
| W4の強さ・全核・指定実因子 | 同じ受理済みC17入力 | 全h/r・成功/禁止・両因子・全fresh displacementの具体対応 |

これはC/Eの当該六義務の証拠対応であり、G-130全体の完了判定ではない。


### Cycle 23 primary evidence mapping

| source | source SHA256 | focused log SHA256 | namespace declarations | individual declarations |
| --- | --- | --- | ---: | ---: |
| `SubdivisionGeneratedActualComparison.lean` | `42944c801f0c019e5908fa7563f9ca5610ab50dc55bbeea41011e4d28cd96e0c` | `5a94787c04240bd4c873b8c4c8642745ae4c28bdd2daefe52bf53dae56a2fee3` | 10 | 10 |
| `SubdivisionGeneratedActualNative.lean` | `155623000064651c29562f7ba45237fad76a9961eaf21f1af52a6f50aa154dee` | `e18e59745c7ff6ff870a7e76f5ae520c571370b8b97a6da6eb5040cf9b252f6b` | 7 | 7 |
| `SubdivisionGeneratedActualRanges.lean` | `3bf0b0322466c5df0b0bc3a48dfefd9add355292ae50fdd8c1253207f33f60e9` | `25a60c506c5aab8d59527965c1ac0af370810c607f1a763f012e358e4eb60dae` | 7 | 7 |
| `SubdivisionGeneratedCoverAction.lean` | `a4f9bdb69c07b736caca0adf0250539b022480bfce9d21a2e7012c369b0651c8` | `f238baf8e30b70cbfeca0927b9e95837480dcd9e26021104ff8b1584b3705943` | 12 | 12 |
| `SubdivisionGeneratedCoverLabels.lean` | `409a32e17b1b164ac5c995a1c9b48bcb491b8a7862b475a79aeb43baafb40706` | `f1e0580eddf22312e2b778ab2e7790a14f6ad2bfbb7965c3ff2a9547cbc8b30d` | 7 | 8 |
| `SubdivisionGeneratedCoverRanges.lean` | `c80e6f1b492801f3d2e84ff5bd4470073d60198a57f3d3d889e867843c1014e4` | `aa930a83bf171582d1d3fdf53444b70bfa140c84136e5b70e121fa4c3766426b` | 5 | 5 |
| `SubdivisionGeneratedCoverRestoration.lean` | `4382d0d55cc4837203a32ef9401bf4829a611c3a1fd87d6af12a46e933dc03bb` | `79546befa0414972c2daf244a50772db69a403531ec93c513923fd6553cf9e83` | 7 | 7 |
| `RelativeGeneratedDefectCover.lean` | `724eb654967ea82198f417634d273e6eca47dccf33f5fc31a88ccc699ac6b6e2` | `e89c9c4c24f2bdd3f72a3aeb843c304f1832702486c1903088c5c9fe8c3edc1c` | 6 | 6 |
| `SubdivisionGeneratedExternalArrows.lean` | `0468998260cc5f990a20efd1794b2d9b56b4cd2e131aa8551e14032f896f42f9` | `e0e7b3a575d2fa142388248571ae55cd67b02920560a9b8b8c92cdabe71e7cd7` | 10 | 10 |
| `SubdivisionGeneratedExternal.lean` | `ad66f5fd018f3de8638ccc3bb29c69529892329ee5b6b0814e7674cd4d171401` | `5df1b1aa4d86298e0af6b75931db10fafb42cbf72194f79b3ec6eba23b72c0e7` | 6 | 6 |
| `SubdivisionGeneratedGroupoidEquivalence.lean` | `23a4f9445f6576b46fe2395b9e0d7f886bef59696168639aa1c88ace56940de9` | `a3d67f4de126f0d88323e664ffe2f49c5cca115b341633d8d757eb34593a0b96` | 5 | 5 |
| `SubdivisionGeneratedNativeRanges.lean` | `2045b7fad17608ca075e04c85e79c44ccebbfe491f7640bd7d85ef57e5a310e1` | `2d9a28fbf89a1a2371257e75673c8e3a5520f0ad68ec804ed309512acb34d888` | 8 | 8 |
| `RelativeGeneratedStrictAction.lean` | `5e0b3d78a1c0a12b4b676d2932b7301d2403f82b9b165d84da3f670cede471a7` | `242db9e6ce857c924f4532eceaf8979e3619250d0bcf99d5eabf3615db7619a8` | 11 | 11 |
| `SubdivisionGeneratedStrictObjects.lean` | `f37c34414b724e6e6148ffc122b360b8a03cfe5bc3399feb28ef91a7e0e5742c` | `678fe730f4ae7e8427cd711f2dff2724bc8a448f5bcd08c7b7a4d8e5587bdbbb` | 10 | 10 |
| `RelativeGeneratedPublicReadings.lean` | `f535081350bf202c10f915b3a16bda83bde0be3ec84f8d9bf85cce5eea9828d7` | `744f8ec0da2214b463874409974e8000184616bc3d74fbb0aed371fa0e7a324d` | 3 | 4 |
| `RelativeActualGeneratedCover.lean` | `bdaa33e0a836fe9d6719bfad5e65e92105347f252e9fb5d29ecd42e96604ea5b` | `29b05fbfb397f9a74f2f6ac1bb92b3072a04630c40e78428733e5816d593662e` | 7 | 7 |
| `RelativeGeneratedNativeRanges.lean` | `416a24844d2a747d76eb6ab86d9911ec76836a7ad6b97b4967807538eaf61f23` | `a4755d29d93543f8d31085615730680641cc903a51bf68d6acc978b45a38b247` | 6 | 6 |
| `RelativeGeneratedCoverRanges.lean` | `cd1a26697dab2e7da69f819994028d3ff1e12d9e5bf35c31b0393cdee02a3ff4` | `084a18366cf146a869a60330fa5911f566f8911c6127310ad37cd860f39f3452` | 6 | 6 |
| `RelativeGeneratedStrictCover.lean` | `972708ddcbed6006dbda294f2930a189106f1732c9556a8e5a8e10976e0a796f` | `e0e2a0fda4acc14d0722ec967db64b434c5e38e50a49a26be929dd7814c54e52` | 9 | 9 |
| `SubdivisionGeneratedStrictConditions.lean` | `d44c68e24b57174c564f581a9c8b5a7ded8aa1f6dd9d01efd6b1639c1a080627` | `532db1d4b635d5ff54bc5c53567c40300d4ea4995b92f8a9b8149c482ced4b54` | 3 | 3 |
| `RelativeStrictEquationAction.lean` | `78ae0a83a51a20e8bddad2ec2679ea6edaa559ed8dbb622d43ad309a592c0089` | `38cecb4413368ddc2e9a684172d35455f1ce6fbd50a7f963a9fe2e4aff0495bb` | 5 | 5 |
| `SubdivisionStrictEquationObjects.lean` | `2b714bf503a5344b165426691177b95803c3cfdeb7a48de38b105ea8bcdcbc88` | `55ff449b0a0a93750942ecb4fee6925855d679cf89b1755a987639961231b8c4` | 14 | 14 |
| `SubdivisionSupplementFamilies.lean` | `a805ce6693671eb7aa999dc2e17144f182e7c41f3332181886573d0192195677` | `9e6205ba1967f91030ab594a773680ab3c13473b4ef82620b5fcadfeb7c1fde0` | 9 | 10 |
| `SupplementalGroupoidContraction.lean` | `1913d4b4532425e432679b2a22a8c7753a212c3357fc66b9f2f38a55673ea659` | `52f9a3299dab86990a5e831947747bdfedfc2e0c706f4bb203ba35cf224ce65b` | 9 | 9 |
| `SubdivisionGeneratedNativeExternal.lean` | `f95aa24165426bf508c10d4aa3405c03d76e67808adba1f973b764db8dd9b7d6` | `a152be19595b0c062f2afafbc020c10df0b4b71881a80a1a852ada1f21789d31` | 8 | 8 |
| `C23GeneratedStrictParameters.lean` | `4ae2ac3b92c7314ab4494e007b229ccbdc68e77ff2c269988e99a0193e4ba620` | `b6b24d59828b19422e19defd51ce737e80d44340f59cf50c933418589023765b` | 20 | 20 |
| `C23ActualLocalCorrection.lean` | `b21419644c632910c10e58f8225aafd2d2791e2116a114f589f4961345234ab0` | `317fbfd203b89bcbfad0a581b30a9a3b77b0ddcd92c9c0f232a55d6341e339fc` | 1 | 1 |
| `SubdivisionGeneratedLocalCorrectionBridge.lean` | `b22779fb23b1fe631fe2ca5338b4f03763afcc758306fb3d429b0947df515eb3` | `dbcd925205760b0d9951c7033caa3e927afbb452d54234d3336c42a059071a7a` | 2 | 2 |
| `C23GeneratedStrictRegression.lean` | `726c1a74782ecd1fc530a6c12df3d813ee638aa34837b64686c18ff36b0d49d9` | `248132ded3fdba4451866a3aaf22a46378bc9acfc86dddb374989a75ec141d4b` | 6 | 6 |
| `C23GeneratedStrictNativeRegression.lean` | `4ce59a372f33b1c33affe2f3966adbc2ff7a5c3718a658e421b4d627f165128e` | `a2954b5b021874efebd44ee93196e08921a04866969d933f07ddfe55c56f0365` | 14 | 14 |

<details>
<summary>C23 selected production module declarations</summary>

```text
AAT.AG.RelativeRepairComposition.C23ActualLocalCorrection.actual_local_correction
AAT.AG.RelativeRepairComposition.C23GeneratedStrictNativeRegression.actual_first_coordinate
AAT.AG.RelativeRepairComposition.C23GeneratedStrictNativeRegression.actual_restore
AAT.AG.RelativeRepairComposition.C23GeneratedStrictNativeRegression.actual_second_coordinate
AAT.AG.RelativeRepairComposition.C23GeneratedStrictNativeRegression.freshArrow
AAT.AG.RelativeRepairComposition.C23GeneratedStrictNativeRegression.freshLabel
AAT.AG.RelativeRepairComposition.C23GeneratedStrictNativeRegression.fresh_label_comparison
AAT.AG.RelativeRepairComposition.C23GeneratedStrictNativeRegression.fresh_labels_complete
AAT.AG.RelativeRepairComposition.C23GeneratedStrictNativeRegression.generatedObj
AAT.AG.RelativeRepairComposition.C23GeneratedStrictNativeRegression.generated_factor_coordinates
AAT.AG.RelativeRepairComposition.C23GeneratedStrictNativeRegression.native_fresh_action
AAT.AG.RelativeRepairComposition.C23GeneratedStrictNativeRegression.native_label_action
AAT.AG.RelativeRepairComposition.C23GeneratedStrictNativeRegression.old_label_zero
AAT.AG.RelativeRepairComposition.C23GeneratedStrictNativeRegression.rangeGroupoid
AAT.AG.RelativeRepairComposition.C23GeneratedStrictNativeRegression.rangeGroupoidCategory
AAT.AG.RelativeRepairComposition.C23GeneratedStrictParameters.compared_parameters
AAT.AG.RelativeRepairComposition.C23GeneratedStrictParameters.comparison
AAT.AG.RelativeRepairComposition.C23GeneratedStrictParameters.enumRegions
AAT.AG.RelativeRepairComposition.C23GeneratedStrictParameters.newActual
AAT.AG.RelativeRepairComposition.C23GeneratedStrictParameters.newExtraction
AAT.AG.RelativeRepairComposition.C23GeneratedStrictParameters.newGenerated
AAT.AG.RelativeRepairComposition.C23GeneratedStrictParameters.newGeneratedEquiv
AAT.AG.RelativeRepairComposition.C23GeneratedStrictParameters.new_generated_count
AAT.AG.RelativeRepairComposition.C23GeneratedStrictParameters.new_nonempty_iff
AAT.AG.RelativeRepairComposition.C23GeneratedStrictParameters.new_parameters_value
AAT.AG.RelativeRepairComposition.C23GeneratedStrictParameters.oldActual
AAT.AG.RelativeRepairComposition.C23GeneratedStrictParameters.oldActualEquiv
AAT.AG.RelativeRepairComposition.C23GeneratedStrictParameters.oldExtraction
AAT.AG.RelativeRepairComposition.C23GeneratedStrictParameters.oldGenerated
AAT.AG.RelativeRepairComposition.C23GeneratedStrictParameters.oldGeneratedEquiv
AAT.AG.RelativeRepairComposition.C23GeneratedStrictParameters.old_generated_count
AAT.AG.RelativeRepairComposition.C23GeneratedStrictParameters.old_nonempty_iff
AAT.AG.RelativeRepairComposition.C23GeneratedStrictParameters.old_owner_component
AAT.AG.RelativeRepairComposition.C23GeneratedStrictParameters.old_parameters_value
AAT.AG.RelativeRepairComposition.C23GeneratedStrictParameters.owner_rhs
AAT.AG.RelativeRepairComposition.C23GeneratedStrictRegression.generated_owner_equality
AAT.AG.RelativeRepairComposition.C23GeneratedStrictRegression.generated_public_one
AAT.AG.RelativeRepairComposition.C23GeneratedStrictRegression.new_owner_comparison
AAT.AG.RelativeRepairComposition.C23GeneratedStrictRegression.new_owner_component
AAT.AG.RelativeRepairComposition.C23GeneratedStrictRegression.owner_extraction_value
AAT.AG.RelativeRepairComposition.C23GeneratedStrictRegression.owner_local_generation_value
AAT.AG.RelativeRepairComposition.RelativeActualGeneratedCover.equivalence
AAT.AG.RelativeRepairComposition.RelativeActualGeneratedCover.forward_component
AAT.AG.RelativeRepairComposition.RelativeActualGeneratedCover.forward_edge_value
AAT.AG.RelativeRepairComposition.RelativeActualGeneratedCover.functor_label
AAT.AG.RelativeRepairComposition.RelativeActualGeneratedCover.inverse_edge_value
AAT.AG.RelativeRepairComposition.RelativeActualGeneratedCover.inverse_label
AAT.AG.RelativeRepairComposition.RelativeActualGeneratedCover.objectEquiv
AAT.AG.RelativeRepairComposition.RelativeGeneratedCoverRanges.coordinate_include
AAT.AG.RelativeRepairComposition.RelativeGeneratedCoverRanges.includeEquations
AAT.AG.RelativeRepairComposition.RelativeGeneratedCoverRanges.includeObjects
AAT.AG.RelativeRepairComposition.RelativeGeneratedCoverRanges.include_comp
AAT.AG.RelativeRepairComposition.RelativeGeneratedCoverRanges.include_component
AAT.AG.RelativeRepairComposition.RelativeGeneratedCoverRanges.restore_include
AAT.AG.RelativeRepairComposition.RelativeGeneratedDefectCover.component
AAT.AG.RelativeRepairComposition.RelativeGeneratedDefectCover.equivalence
AAT.AG.RelativeRepairComposition.RelativeGeneratedDefectCover.equivariant
AAT.AG.RelativeRepairComposition.RelativeGeneratedDefectCover.functor_label
AAT.AG.RelativeRepairComposition.RelativeGeneratedDefectCover.inverse_label
AAT.AG.RelativeRepairComposition.RelativeGeneratedDefectCover.objectsEquiv
AAT.AG.RelativeRepairComposition.RelativeGeneratedNativeRanges.equivariant
AAT.AG.RelativeRepairComposition.RelativeGeneratedNativeRanges.functor
AAT.AG.RelativeRepairComposition.RelativeGeneratedNativeRanges.functor_comp
AAT.AG.RelativeRepairComposition.RelativeGeneratedNativeRanges.functor_label
AAT.AG.RelativeRepairComposition.RelativeGeneratedNativeRanges.functor_object
AAT.AG.RelativeRepairComposition.RelativeGeneratedNativeRanges.labelsInclusion
AAT.AG.RelativeRepairComposition.RelativeGeneratedPublicReadings.publicValue
AAT.AG.RelativeRepairComposition.RelativeGeneratedPublicReadings.publicValue.congr_simp
AAT.AG.RelativeRepairComposition.RelativeGeneratedPublicReadings.restored_public
AAT.AG.RelativeRepairComposition.RelativeGeneratedPublicReadings.restored_value_public
AAT.AG.RelativeRepairComposition.RelativeGeneratedStrictAction.action_component
AAT.AG.RelativeRepairComposition.RelativeGeneratedStrictAction.addAction
AAT.AG.RelativeRepairComposition.RelativeGeneratedStrictAction.equivalence
AAT.AG.RelativeRepairComposition.RelativeGeneratedStrictAction.equivariant
AAT.AG.RelativeRepairComposition.RelativeGeneratedStrictAction.functor_inverse
AAT.AG.RelativeRepairComposition.RelativeGeneratedStrictAction.functor_label
AAT.AG.RelativeRepairComposition.RelativeGeneratedStrictAction.gauge
AAT.AG.RelativeRepairComposition.RelativeGeneratedStrictAction.gauge_add
AAT.AG.RelativeRepairComposition.RelativeGeneratedStrictAction.gauge_zero
AAT.AG.RelativeRepairComposition.RelativeGeneratedStrictAction.inverse_functor
AAT.AG.RelativeRepairComposition.RelativeGeneratedStrictAction.inverse_label
AAT.AG.RelativeRepairComposition.RelativeGeneratedStrictCover.EquationFamily
AAT.AG.RelativeRepairComposition.RelativeGeneratedStrictCover.EquationObjects
AAT.AG.RelativeRepairComposition.RelativeGeneratedStrictCover.LocalObject
AAT.AG.RelativeRepairComposition.RelativeGeneratedStrictCover.Objects
AAT.AG.RelativeRepairComposition.RelativeGeneratedStrictCover.PublicCompatible
AAT.AG.RelativeRepairComposition.RelativeGeneratedStrictCover.compatibility_iff
AAT.AG.RelativeRepairComposition.RelativeGeneratedStrictCover.familyEquiv
AAT.AG.RelativeRepairComposition.RelativeGeneratedStrictCover.objectEquiv
AAT.AG.RelativeRepairComposition.RelativeGeneratedStrictCover.same_public_compatibility
AAT.AG.RelativeRepairComposition.RelativeStrictEquationAction.action_component
AAT.AG.RelativeRepairComposition.RelativeStrictEquationAction.addAction
AAT.AG.RelativeRepairComposition.RelativeStrictEquationAction.gauge
AAT.AG.RelativeRepairComposition.RelativeStrictEquationAction.gauge_add
AAT.AG.RelativeRepairComposition.RelativeStrictEquationAction.gauge_zero
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedActualComparison.chosen_not_fixed
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedActualComparison.collapsed_local_value
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedActualComparison.compared_old_value
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedActualComparison.comparison_actual
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedActualComparison.comparison_actual_restore
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedActualComparison.comparison_fresh_actual
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedActualComparison.comparison_old_actual
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedActualComparison.comparison_restore_edge_value
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedActualComparison.restoredLocal
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedActualComparison.restoredLocal_value
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedActualNative.equivalence
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedActualNative.equivariant
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedActualNative.functor_label
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedActualNative.inverse_label
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedActualNative.labelEquiv
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedActualNative.label_comparison
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedActualNative.old_equivariant
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedActualRanges.actualFunctor
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedActualRanges.actual_label
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedActualRanges.native_extraction_include
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedActualRanges.new_extraction_include
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedActualRanges.new_restore_include
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedActualRanges.old_extraction_include
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedActualRanges.old_restore_include
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedCoverAction.action_component
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedCoverAction.actualGauge
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedCoverAction.addAction
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedCoverAction.equivalence
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedCoverAction.freshComm
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedCoverAction.functor_label
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedCoverAction.gauge
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedCoverAction.gauge_add
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedCoverAction.gauge_component
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedCoverAction.gauge_zero
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedCoverAction.inverse_label
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedCoverAction.objects_equivariant
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedCoverLabels.collapse
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedCoverLabels.displacements
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedCoverLabels.equivalence
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedCoverLabels.equivalence.congr_simp
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedCoverLabels.equivalence_component
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedCoverLabels.expand
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedCoverLabels.forbidden_retained
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedCoverLabels.oldLocal
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedCoverRanges.comparison_include
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedCoverRanges.includeNew
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedCoverRanges.includeNew_comp
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedCoverRanges.includeNew_component
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedCoverRanges.restoration_include
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedCoverRestoration.actual_rhs
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedCoverRestoration.newActualEquations
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedCoverRestoration.newObjectEquiv
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedCoverRestoration.new_equation_component
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedCoverRestoration.new_fixed_laws
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedCoverRestoration.new_forward_edge_value
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedCoverRestoration.oldObjectEquiv
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedExternal.external_object_value
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedExternal.objectEquiv
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedExternal.restored_actual
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedExternal.sharedNew
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedExternal.sharedOld
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedExternal.shared_comparison
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedExternalArrows.collapseActualFunctor
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedExternalArrows.collapseActual_object
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedExternalArrows.externalHomEquiv
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedExternalArrows.external_arrow_value
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedExternalArrows.external_composition
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedExternalArrows.external_identity
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedExternalArrows.homEquiv
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedExternalArrows.homEquiv_value
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedExternalArrows.mapped_shared_label
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedExternalArrows.newSharedLabel
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedGroupoidEquivalence.equivalence
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedGroupoidEquivalence.fullRestoreIso
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedGroupoidEquivalence.functor_label
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedGroupoidEquivalence.functor_object
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedGroupoidEquivalence.inverse_label
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedLocalCorrectionBridge.component_eq
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedLocalCorrectionBridge.component_heq_of_rhs_eq
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedNativeExternal.compatible_composition
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedNativeExternal.compatible_identity
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedNativeExternal.environmentLabel
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedNativeExternal.environment_composition
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedNativeExternal.environment_identity
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedNativeExternal.generated_composition
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedNativeExternal.generated_identity
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedNativeExternal.nativeHomEquiv
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedNativeRanges.comparison_functor
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedNativeRanges.equivariant
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedNativeRanges.functor
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedNativeRanges.functor_comp
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedNativeRanges.functor_label
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedNativeRanges.functor_object
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedNativeRanges.labelsInclusion
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedNativeRanges.labels_comparison
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedStrictConditions.Compatible
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedStrictConditions.compatibility_iff
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedStrictConditions.shared_ne_chosen
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedStrictObjects.NewObjects
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedStrictObjects.OldObjects
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedStrictObjects.newExtraction
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedStrictObjects.newExtraction_component
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedStrictObjects.newRestoration_component
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedStrictObjects.objectsEquiv
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedStrictObjects.objectsEquiv_component
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedStrictObjects.objectsEquiv_inverse_correction
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedStrictObjects.objectsEquiv_public
AAT.AG.RelativeRepairComposition.Subdivision.GeneratedStrictObjects.rangeObjectsEquiv
AAT.AG.RelativeRepairComposition.Subdivision.StrictEquationObjects.NewFamily
AAT.AG.RelativeRepairComposition.Subdivision.StrictEquationObjects.NewObjects
AAT.AG.RelativeRepairComposition.Subdivision.StrictEquationObjects.OldFamily
AAT.AG.RelativeRepairComposition.Subdivision.StrictEquationObjects.OldObjects
AAT.AG.RelativeRepairComposition.Subdivision.StrictEquationObjects.familyEquiv
AAT.AG.RelativeRepairComposition.Subdivision.StrictEquationObjects.family_compatibility
AAT.AG.RelativeRepairComposition.Subdivision.StrictEquationObjects.family_coordinates
AAT.AG.RelativeRepairComposition.Subdivision.StrictEquationObjects.objectsEquiv
AAT.AG.RelativeRepairComposition.Subdivision.StrictEquationObjects.objectsEquiv_fresh_value
AAT.AG.RelativeRepairComposition.Subdivision.StrictEquationObjects.objectsEquiv_inverse_coordinates
AAT.AG.RelativeRepairComposition.Subdivision.StrictEquationObjects.objectsEquiv_inverse_correction
AAT.AG.RelativeRepairComposition.Subdivision.StrictEquationObjects.objectsEquiv_old_value
AAT.AG.RelativeRepairComposition.Subdivision.StrictEquationObjects.rangeObjectsEquiv
AAT.AG.RelativeRepairComposition.Subdivision.StrictEquationObjects.strictFamilyEquiv
AAT.AG.RelativeRepairComposition.Subdivision.SupplementFamilies.Family
AAT.AG.RelativeRepairComposition.Subdivision.SupplementFamilies.equivalence
AAT.AG.RelativeRepairComposition.Subdivision.SupplementFamilies.equivalence_inverse_value
AAT.AG.RelativeRepairComposition.Subdivision.SupplementFamilies.equivalence_value
AAT.AG.RelativeRepairComposition.Subdivision.SupplementFamilies.nonowner_zero
AAT.AG.RelativeRepairComposition.Subdivision.SupplementFamilies.restore
AAT.AG.RelativeRepairComposition.Subdivision.SupplementFamilies.restore.congr_simp
AAT.AG.RelativeRepairComposition.Subdivision.SupplementFamilies.restore_owner
AAT.AG.RelativeRepairComposition.Subdivision.SupplementFamilies.restore_read
AAT.AG.RelativeRepairComposition.Subdivision.SupplementFamilies.restore_value
AAT.AG.RelativeRepairComposition.SupplementalGroupoidContraction.counitComponent
AAT.AG.RelativeRepairComposition.SupplementalGroupoidContraction.counitIso
AAT.AG.RelativeRepairComposition.SupplementalGroupoidContraction.counit_label
AAT.AG.RelativeRepairComposition.SupplementalGroupoidContraction.equivalence
AAT.AG.RelativeRepairComposition.SupplementalGroupoidContraction.labelProjection
AAT.AG.RelativeRepairComposition.SupplementalGroupoidContraction.labelSection
AAT.AG.RelativeRepairComposition.SupplementalGroupoidContraction.projection
AAT.AG.RelativeRepairComposition.SupplementalGroupoidContraction.sectionFunctor
AAT.AG.RelativeRepairComposition.SupplementalGroupoidContraction.unitIso
```

</details>

### C23 individual axiom evidence

- audit SHA256 `87f9a2803f983e3b53ee01e3370da186f5ac11dbafa810cc39c104912cf0a914` / log SHA256 `41217b9c0f7ba09d0cd6865a00f3f218205001eac6bd47a20459425aafdbc868`: 185 declarations, standard axioms only.
- audit SHA256 `955f95e71be7d141cbc051e8a9dc40b1f90b857fe0f5d7845d5900a2ec9389fa` / log SHA256 `600053d380d3b6c495b7d6e62c4020c1fd2e04dfc0a26dd47d6ab596671cec25`: 8 declarations, standard axioms only.
- audit SHA256 `98867fdc99116ff6ba9c327d773ddfeb1e6c5bb3a907899340c9ccc4b7d38c8d` / log SHA256 `143887c72a309a93eb129a34dcf1757a23226a68ab8444b4cd3a54315759661e`: 43 declarations, standard axioms only.

### Cycle 24 selection — W1の同じ全アフィン変換網と全要求

```yaml
ledger_type: target_cycle_result
goal: G-130-aat-relative-repair-composition
cycle: 24
goal_blob_sha: 8da0fb4eb75d1cb5c37a9d4ddf5e03c18c0bb8a2
base_oid: a0949e737797b35ad3cfa1145abcffdb8f49d0de
tracking_issue: 5132
report_path: research/reports/G-130-aat-relative-repair-composition.md
selection:
  proof_state_ref: "C23 PR #5169/root #5961945784、Issue #5132/comment #5961971718、固定W1/n1017 §5.8"
  proof_dag_predecessors: ["C23 strict独立生成・全actual/native比較", "C22 独立局所生成と全補足", "C17–C21 実分割・相対複体・全範囲商保存", "C1–C16 A–Fの受理済み一般API"]
  milestone: "W1の同じ六原辺・二指定面・固定p/rx/ry・全Aff(F3)から、全入力値/全範囲の全実修復・全native射・独立局所生成・双対極小分類・値更新・指定内部分割を接続する"
  proof_obligations:
    - "原geometryの一頂点・六名前付きloop・二指定Law・3-cellなし、同じP/E0/候補/U/V/W、全(x,y)、a=-Iとa=I、whole affine原射/core/比較/全核とtower条件・閉包・被覆を構成"
    - "実関数合成から指定方程式を導出し、全Sの独立actual修復を全(u,h,z,v)へ両逆で対応。元六操作・固定値・全頂点核labelsを保持し、一般Aと同じ複体/signed defectへ接続"
    - "同じU/Vの実微分/defectから一回ずつ全局所関係・section・private h・shared u,z/候補z,vを独立生成し、全S strict合成と全actual/native復元を一般Cから構成"
    - "同じ実大域D/coker/候補列からq(r1,r2)=r2-r1、o=y-x、Bb=Bc=1を導き、局所消去/H2と接続。全4範囲の全修復数/同型類/自己同型、不能双対証拠、d=0/非零の極小範囲、a=Iの同条件で空極小を証明"
    - "全(x,y)に同じ構造行列・生成器/sectionと元実復元を共用して値更新を比較。(0,0)から(0,1)の指定両単独候補修復と非零不能評価を元実操作で評価。観測回数は本GOALへ追加しない"
    - "private aを自由新頂点のt+1と-t+1へ実分割し、第二Lawの二出現とも一般置換で保持。全分割補正(r,h+r)、全fresh作用、三倍の全修復数と全同型類/自己同型保存、独立C/実復元/全S D/H2/極小/Wの比較を同じ入力に接続"
  exit_criteria:
    - "指定原入力の全条件を構成し、全入力値/全Sで独立actual修復の全パラメータ・元操作・数・全labelsを一般A/Fと双方向接続"
    - "独立局所生成・同じ商/双対/極小・identity holonomy比較を元入力と一般C/Dへ双方向接続"
    - "同じ値更新と指定内部分割の全actual/local/native復元・全S分類・共有値保存を構成し、全自由度と全射を保持"
    - "選定productionの単一focused本体・全個別公理・scans・source/hash対応を固定し、標準PR reviewとroot受入を通す"
  selection_reason: "一般A–Fと同じ非退化指定例との残る接続を、W1の全要求を一到達点として閉じる。fileや補題単位でcycleを閉じない"
  expected_result_type: proof-obligation-discharged
  lean_targets: ["W1AffineInput", "W1ActualRepairs", "W1PermissionClassification", "W1NativeLabels", "W1FiniteCoefficients", "W1LocalInterfaces", "W1StrictGeneratedCover", "W1OriginalObstruction", "W1DualMinimalRanges", "W1SymbolicUpdates", "W1InternalSubdivision"]
  risks: ["右から適用する二Lawの元経路/符号/候補名の保持", "全private h/共有値/全native labelsを捨てない", "旧像からの出力定義を避け各側の実D/Fから独立生成", "方向仮定を具体入力で放電", "a=I比較の同じ許可条件", "二箇所のa置換と全factor復元", "現行source版/受理済み依存の追跡"]
  unchecked: ["上記六義務のW1全構成と全接続は未実装。C23受理をW1の証明としない", "全GOAL completionは残W2/W3/W5と別最終四本gateを要する"]
```

### Cycle 24 — W1の全アフィン修復・独立生成・範囲分類・再利用

W1の原表示は一頂点、六loop `e,a,b,c,rx,ry`、二面、3-cellなしである。
第一面の原経路は `b,e` 対 `rx`、第二面は `c,a,b,a,e` 対 `ry`。
操作の合成は右から適用する。物理的固定部分は頂点と `rx,ry`、
常時辺は `e,a`、候補は原名 `b,c`。係数は全 `Aff(F3)` の実射影の全平行移動核である。

| 固定義務 | 入力からの構成と同じ元実操作への使用先 |
| --- | --- |
| 原表示・全条件 | `W1AffineInput` / `W1AuthoredOperations` が全実アフィン原射・core・比較・全核・強さ・輸送を構成する。`W1Regions` / `W1IndexedCover` が原0〜3セルの閉包・固定部分・二領域被覆とprivate/public分割を構成する。|
| 全実修復・全射 | `W1ActualRepairs` が実合成から全六操作を読む両逆を構成し、`W1PermissionClassification.negativeActualEquiv` と `negativeNativeEquiv` が全Sの全パラメータを保持する。`W1NativeLabels.wholeAffineEquivalence` は全nativeラベルと実アフィンgroupoidを対応させる。|
| 一度生成・厳密合成 | `W1FiniteCoefficients` / `W1RelativeCoefficients` が全実微分と符号付きdefectを計算する。`W1LocalInterfaces` の各D/F・消去・section・relationは各領域の実入力から生成され、Sを引数に持たない。`W1PrivateMatrixZero` / `W1LocalPrivateFreedom` はprivate全hを保持する。`W1GeneratedRelations` と `W1StrictGeneratedCover.actualEquivalence` / `actualObjectEquiv` が全公開関係・共有値・禁止候補・全射から元修復へ両逆で復元する。|
| 商・証拠・極小範囲 | `W1OriginalObstruction` / `W1CandidateColumns` は同じ大域Dから商座標q、実o、全原候補列を計算する。`W1DualMinimalRanges.actual_range_iff` / `actual_dual_iff` / `minimal_actual_iff_dual` は全named範囲を実修復へ接続する。`W1GlobalCohomology` は同じ元相対複体の障害商と接続する。`W1IdentityClassification` / `W1IdentityMinimal` は同じ固定・候補条件でa=Iの比較を与える。|
| 全値更新 | `W1SymbolicPublicStructure` / `W1SymbolicPublicMatrices` / `W1SymbolicLocalStructure` / `W1SymbolicGeneratedRows` は元の全名前付き座標・全基底成分・全列挙・実D/F・消去・section・独立公開行を共用する。`W1SymbolicActualUpdates` は実defectと全元操作への復元、および(0,0)→(0,1)の両単独候補修復と空範囲不能評価を与える。|
| 内部分割の全自由度 | `W1SubdivisionInput` / `W1SubdivisionWords` が実因子t+1,−t+1と第二面の両a出現を保持する。`W1SubdivisionRepairs` / `W1SubdivisionCoordinates` は全(r,h+r)を復元する。`W1SubdivisionSupportedGauge.labels_complete` / `first_supported_shift` / `second_supported_shift` は任意の全Sで全freshラベルと両補正の(s,s)作用を保持する。`W1SubdivisionClasses` / `W1SubdivisionPreservation` は全同型類・Aut・全相対コホモロジー・障害・旧holonomyとfresh恒等収縮を比較する。独立新旧局所生成・全actual復元は `W1SubdivisionGeneratedInterfaces` / `W1SubdivisionGeneratedRestoration`、全候補商・双対・極小は `W1SubdivisionRanges` / `W1SubdivisionMinimalRanges`、同じWと任意外部環境は `W1SubdivisionSharedBoundary` で接続する。|

全(x,y)において、a=−Iの二式は `u+z=x`、`u−z+v=y`。
`d=y−x` とすると、空範囲の全修復数と同型類数はd=0で3、非零で0、
単独b・単独cは各3、全候補は9。物理的頂点が固定されるため全元自己同型は恒等。
同じ大域Dは(u,h)↦(u,u)、q(r1,r2)=r2−r1、o=d、全原候補列の像はBb=Bc=1。
非零dの双対支持は両原候補であり、極小範囲は{b}と{c}。d=0では空集合が唯一の極小範囲。
a=Iでは第二式が `u+2h+z+v=y` となり、全値で空範囲が可解で唯一の極小範囲となる。
分割後は自由fresh値の分だけ全修復数が三倍となり、同型類数とAutを保つ。

生成データの比較は、元セル名と全 `Fin 1` 基底添字を明示した同じ座標型上で行う。
この座標型は元全核の基底座標と定義的に同じである。行列、有限列挙、消去、sectionの
各比較には実入力側の生成データそのものを使用する。消去の型は入力行列に依存するため、
同じ行列の等式に沿った全Reductionの一致はHEqとして保持する。

受理依存はC1〜C23の対応する一般APIに接続する。受理済み証拠はその原始入力、
必要仮定、結論、実際の使用箇所を照合して追跡完了とする。
W1の到達点を全GOALの完了としない。W2・W3・W5の指定実例と別最終completion gateを要する。

### C24 前提の出所と使用

| 前提 | 分類・入力からの放電 | 使用先 |
| --- | --- | --- |
| 全Aff(F3)、全実射影、原表示・core・原六辺と比較、全(x,y)/S | 本文由来: 固定W1/F、n1017 §5.8。全実射影の核を用いる | 独立RealRepairsと全native/kernel座標の往復 |
| 強さ・可換全核・全単射輸送・線形性・固定面整合 | 一般A/C/Eではdirection-hypothesis、W1では放電済み: W1AffineInput / W1AuthoredOperations / W1FiniteCoefficients / W1RelativeCoefficients | 実方程式・生成・全射・相対障害 |
| 原0〜3セルの閉包・全被覆・候補全public・private a・W外・新頂点自由 | 放電済み: W1Regions / W1IndexedCover / W1SubdivisionInput | strict全S合成、任意private/fresh復元と外部比較 |
| 有限体・全実核の全基底・全セル列挙 | 本文由来のF3と放電済みのW1FiniteCoefficients.bases、W1AffineInputの原有限列挙 | actual D/F、停止する有限生成、全座標への復元 |
| 消去・section・公開relation/rows・private kernel・strict復元 | 放電済み: W1LocalInterfaces / W1GeneratedRelations / W1PrivateMatrixZero / W1LocalPrivateFreedom / W1StrictGeneratedCover | 全Sで同じ局所生成器から全actual/native修復へ両逆 |
| 値更新比較の行列・全列挙の一致 | 放電済み: W1SymbolicLocalStructure.private_matrix_same / enumeration_same、W1SymbolicPublicMatrices.public_matrix_same、W1SymbolicGeneratedRows.projected_matrix_same / public_enumeration_same | reduction_congr / section_congr / rows_congrの等式入力を放電し、実際の全生成結果の一致へ使用 |
| 分割因子・全新旧補正・全fresh作用と全射 | 放電済み: W1SubdivisionInput / W1SubdivisionCoordinates / W1SubdivisionSupportedGauge / W1SubdivisionGeneratedRestoration | 新旧実修復・独立局所生成・商・障害・全外部環境の比較 |
| d=0/非零、指定修復や失敗双対 | 本文由来の判定枝。W1PermissionClassification / W1DualMinimalRanges / W1SymbolicActualUpdates が同じ元実操作で構成・評価 | 四範囲の全数、成功復元、非零失敗、極小範囲 |

前提申告は査読対象であり、標準PRレビューが実際のstatementとproof-useを独立に照合する。
一般補題の入力等式を全W1の結論仮定に残さず、同じ実入力の行列・列挙の一致から放電する。

```yaml
ledger_type: target_cycle_result
goal: G-130-aat-relative-repair-composition
cycle: 24
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "固定六義務の同じW1全入力・全S・元全操作・全射・全独立生成・商/双対/極小・identity比較・値更新・指定分割を構成"
  exit_criteria_status:
    - "原全入力・独立actual両逆・全パラメータ/数/labels: Lean構成と全個別公理確認済み"
    - "独立Cと同じD/dual/minimal/identity: Lean構成と全個別公理確認済み"
    - "全値更新・全指定分割・全自由度/射・同じW: Lean構成と全個別公理確認済み"
    - "43単一production本体と456所有宣言の個別公理確認済み。標準PRレビューとroot受入はPRで判定"
  split_reason: none
  completion_candidate: no
  claim_mapping:
    source_labels: ["固定GOAL W1", "A/C/D/E/F", "n1017 §5.8"]
    undischarged_assumptions: []
    acceptance_point: "六義務・四終了条件の同じ到達点。標準レビューとroot受入を要する"
    port_status: unported
audits:
  premise_delta:
    discharged: ["上表の同じ実入力からのW1全条件・両逆・独立生成・全範囲分類・全再利用比較"]
    remaining: ["全GOALの残W2/W3/W5と別最終完了判定"]
  certificate_provenance:
    discharged: ["原全Aff入力/実D/F/defect/全基底/列挙からの生成", "同じ原入力からの全分割条件・実復元"]
    unresolved: []
  proof_use:
    used: ["実合成→全方程式/微分", "実D/F/全列挙→有限生成→strict/actual両逆", "同じ大域D/coker→dual/minimal", "実因子/全fresh→全補正/全射/全障害比較"]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  blocking_findings: []
  next_obligation: "W2、W3、W5の固定実例・全指定判定と一般A–F接続、その後別全target最終四本レビュー"
```

### C24 productionと個別公理の一次検証対応

43単一fileの本体を各々focused checkし、所有moduleを選択した個別`#print axioms`は
全456宣言を被覆する。namespace監査は448宣言、namespace外の自動生成helperは8宣言。
本体検証とimport後の個別公理検査は別の証拠である。各本体・個別公理のactual exitは0、
現行sourceとlogのSHA256を対応させた。標準公理はpropext、Classical.choice、Quot.sound。
単一fileのコマンドは `cd research/lean && lake env lean -s4096 -D Elab.async=false -o .lake/build/lib/lean/<module path>.olean <source path>`。
Research全体、aggregate、全module/file loopのelaborationは実行しない。

| Production module | namespace宣言数 | source SHA256 | 本体log SHA256 |
| --- | ---: | --- | --- |
| W1ActualCorrections | 4 | `806f123456be93c1242ce2a2d36bca81e326adb78d0f7df469e613cfe163a457` | `e97e93281e0db9f4f0a1205ee01b74634b2f19e8f7aa85555092e195f6277e3c` |
| W1ActualRepairs | 35 | `593285de275df236cbf4614f5ff176905ff0a46c4f3877ecc4549d833f06a29a` | `fdff78d98120e524bb2185b5039cd7d2668346386546e70ede1218e6793ddb1c` |
| W1AffineInput | 22 | `6a715b939e4bc07cf798b18fdec679b2c9558bfa32a4fa0525ab88b027d4218e` | `8d07f55856d62f3a9931d45ada99472946751b0786311a005e6260273204b59a` |
| W1AuthoredOperations | 16 | `f946d9d9f476ea2480991b4669834c2f71ce3daf16b7f6dc37a62042809b2038` | `489aa8d7bb06951c58a18bfb49062bdd3d8058f8e0df12a07fef042fef7ddad3` |
| W1CandidateColumns | 12 | `f3d633669f7e7f5dff32fdc3d94ac779d2967e29732be5a715e799faa461f004` | `2e38db8bc158350a920e2e6a57fdfdc7cc85ba0e507fa80064b394ab124acb6f` |
| W1DualMinimalRanges | 17 | `4097f04d6309711d7b544cc516881cf4971ea563de88a2dcd819d55f5ca69294` | `414d32c3798491833e6f5f998e2cf1b654895c147cc32ea048c204c3a70d8d42` |
| W1FiniteCoefficients | 18 | `baec4afc9dbf0b6a012ed1266ab251b492158ff8b0c7a828739268558cb97f8b` | `ea751c655bd4e5eaca15978ea0e1cb72ceb55411d423beb0bb9da7eba8109e80` |
| W1GeneratedRelations | 5 | `a34273e9c883d09a6648116afb9501dd26857f3a420a6294d419a621c041cb6d` | `f633ef29c4a98846814a2b3068f701aa0aeaf55345df9dbc30ebc19f9c638971` |
| W1GlobalCohomology | 7 | `23fd796e19438105b095654176c8917667caf5b21d44fc95757094d4dbfa0d2a` | `050a7246963ee659378735e29f0087e5d8f216b299f9e8f7dab937710a941a23` |
| W1IdentityClassification | 14 | `190e2b9524cb1f8323418adea0d1cd17bed21cc6a7fdd337d0a83cad4ed74a46` | `eef244271d774c426004a6cd7e080db923be57508523cfeaeb9266414525c578` |
| W1IdentityMinimal | 3 | `a55474c9856f5d332e736fc66cfc11c5f1909c5ee9a4cf63dd4abfa1401ea6fd` | `9b41607060e0174e3800433c9e3df7898e53ed6b10a2dc424b7cadcc8df19c1d` |
| W1IndexedCover | 7 | `93db604422c562ca8eb2ab7353bc5084a9839ed687708ff6e6599718741e2e87` | `06ffafbd046d740bac140f6d5802ecd36b643a2637b4ca46c107073b46ccd83e` |
| W1LocalDifferentials | 6 | `b1bf5f652ca158ee3be662b3796dd546b61a8edc4bf11c009367572fbdad7284` | `a02f2a2b6b9f47186d8ac572d5d7d782b44e398d857896625c853c08624c7966` |
| W1LocalEquationCriteria | 4 | `79e962534e7c12ff20ca38044360e57ab1c1ce2f36546311b11dd8027207cabb` | `c3d18759283d82bebdfbc2daee1f7cd23cae426750997e99819932bbb327dca3` |
| W1LocalInterfaces | 10 | `c00c799aa0750abd17f57096bb262e02b1f880778f27710c6731e2ebb5542ec3` | `ed1c43ad1346f831b571ba81a0e03c7951c951f0e5f7e807ed25e2837ab92949` |
| W1LocalPrivateFreedom | 6 | `ec4bf2941652f6698a611cf846d74eaf877aa47d530f677d05f300b6d90ce244` | `8b99070a4003aa572ae0265bdbf0c1ceef3e083fe87ea39d38c8f1fc706b31fe` |
| W1LocalPublicValues | 3 | `0d29d995c81c666ae16124abf1f7c45898610468a4830edd836b16da5a22518a` | `b12332639527315fe30164a5e231b4f82760b929b2b94239541540c585e4dd48` |
| W1NativeLabels | 10 | `0e46cabf1ec5ac5c591e7a90099b0a018b48aa09ed7e1c8eaaded39003600e60` | `1f890420610b56f9e3826cdd76992cab9a2ce2f9e0809331b8cd29a36da21dcf` |
| W1OriginalObstruction | 16 | `2370498b609e9ade2b5102e055641c835e8d51fc2612de503bc970d7e779f0a5` | `3b433f78cd505fd04f930f85a6a299b37cfd76267dd05b7d5c23c4c7ff26c8dc` |
| W1PermissionClassification | 14 | `38fd89e51818418b33119e270bd80e72803a3653aaec92a19ed565c01e929902` | `6cf674de358915e5b556305dcc79494e5baab6696eb2b44e73fb6b0b45f04332` |
| W1PrivateMatrixZero | 4 | `26828bec71b28ed6116c1ac10d904a9badd6ca6bbbb60f98f4c4fa98681a0730` | `ba34ec352a1221724bd27bb630dfab1424dff5541fa525af6f82c7a82cfad9c1` |
| W1Regions | 16 | `93c4128dfddf5e4a6bd30c6cb60af5625e6a75ea490a44e19d6822d27b932373` | `0ee415a3c651d561021c16733f13affe9d2858e852587ed1514303f2aea91ebe` |
| W1RelativeCoefficients | 15 | `06f8b847f1e917ff51c91adc02be82cc3d0e55df01260b31ba92becc3631d74e` | `824bcb80adbb4cf7ccff0316bf7acb9eda82b4fe5e027c982cbb5df0dc910124` |
| W1RepairCounts | 14 | `ebd0c09178fb18953e28048af492c5faca6b71334dd0c3cc45ab3567e355aaaa` | `732140201a69b3eb3a3fd2f479fadb60f9bb49395a53b30acc96d4beb5076af0` |
| W1StrictGeneratedCover | 9 | `058d322d9bdb50d4399aee1a1f7da512993dd392e380da454ad69d49772bed41` | `9e42e615ceee15f9e0c48a75bb966979f2dab61b52feeea53aa723cf15a4ebee` |
| W1SubdivisionClasses | 6 | `312e73fb5c43e83e866493e793ecd0b6ae6358bac171ae6507f6c39fbf78d548` | `2fb894f969146a0f61060b130c4b83176044ab1ff7245285f7eeaa4bddc609fd` |
| W1SubdivisionCoordinates | 8 | `1c784525db3e61568de90c7bf336567f5ff6d4289ad1569ee961032f999a56a9` | `2579805e5e2223ee174b91cc0f267add018fb4e6dbf54f6aecbdcb95d301c381` |
| W1SubdivisionFreshGauge | 5 | `7102ff8b69b364e79fa1047278abfe2921ae29440e956e52a104a3177cac63f7` | `270a0ba047321745fd65468d29a264708a452b3bd92d30a79e1f696ebca10893` |
| W1SubdivisionGeneratedInterfaces | 8 | `5566d20a17fbbe3e463bb9accd54e51d05b2f5667231af26ca41db064aef7b43` | `b3883b9b16def26d5aaad8280ea1f4f2ae18830dcd5191075c6665773f23b27d` |
| W1SubdivisionGeneratedRestoration | 4 | `9199aae7d17293c6178fc5a5a41cf2fc7aa86e51e9f62f472bc5375bd56b071b` | `e8371053a35fbbae6e9a1e8a6f99a08f1c8b481619b14db87f47d08a41c6ffab` |
| W1SubdivisionInput | 19 | `d74b6df04b72b11b71177f8db086019bc3dc5c98ba0e004d8fae994ddd7bb515` | `3465a0d9c932a13b8550f25a1f5c6fb18fbaad450f48ee8233df563f61f688d0` |
| W1SubdivisionMinimalRanges | 4 | `99d16724dac3b576eae4ce6e002accdc380b8176ccccd0d7259e3dab22e2a0b8` | `699d0cd6e36bc237bf8084c94a7ba749f016786a844d3eea8bbdd4ed22cfd125` |
| W1SubdivisionPreservation | 9 | `4b42fba193656143c6bb6110ef088df08ac1ca6e8e499b6ba25e41c000d239ac` | `37d541dec58e3bb95baae621b037ad24ec932e53f15e179034f7a5b54f85cbb9` |
| W1SubdivisionRanges | 10 | `fa79b58772468186fbc6ab87d36f69be00875afa38b1f86723f60e75e3fdb190` | `52c82627e4c87c3ed0d1fe752e96d6d8377f60ebee54b6a22d300a7433cf3038` |
| W1SubdivisionRepairs | 13 | `126653257357afe1c3e0a0350db30046a64dfa76606d52567f5b7135a3c3ede3` | `732ba2a15ff0ab9b6355e6949cfbe422fada36ca282066432c295280712414fe` |
| W1SubdivisionSharedBoundary | 4 | `e58b4c118ba8942ba637bb5391e8f99ef58abce691e48d7220bbf1391122c8fe` | `3012dd395afbfdac09ce04f117c04aed497c2a0851f2256b33304dfa79e229b1` |
| W1SubdivisionSupportedGauge | 5 | `1d0dc06a5b75cc2a2d27043afe2fbe0311dc4a7d947c409d1297dc1c0da43b65` | `ad3ae721063decdeb84b4d87c3d7a13598583a5a9cae0f2965267a5141bd2930` |
| W1SubdivisionWords | 6 | `46a92d4c6c2d16b1be470b84fd3fef30f8e3af4fdbad33537d08d03ac3ee2512` | `31111b5afff166974ceacd04c4d8fb29372ae04bd5e6af322538091e9c4e78da` |
| W1SymbolicActualUpdates | 11 | `af10b71f6209677699751b71568eb11af4e188f4672c668de1ef07896ac7cbed` | `33f807bed627d75226d52bf1e9dd164b4d6c8df523055ee894a28dbbe13638cf` |
| W1SymbolicGeneratedRows | 8 | `39136f226ba71b1acb847c97de170cc1d0ca98e57beded05c7ced9b5a800fbd2` | `b087127c8ab9682b25283c3f09021bc07d223fa3ba59ad82c4965f462a048735` |
| W1SymbolicLocalStructure | 25 | `da07cb86c5b12a240dac69e45cd4e7d926b177410bafa6cb824f8209494cdd05` | `7a6e5125dac013b12e7510921b5de1e89504b3e5e07e795f26b4e1f3fbe0803e` |
| W1SymbolicPublicMatrices | 11 | `0aba4d1ee6e450535d8b0d4edb49888a7072d44cc9dd8b9c23f20dd274aa74ec` | `103fa6a3b76b9f29290ba61d2a90c8dfb1695c92b5af10ed09486b5afd9cab49` |
| W1SymbolicPublicStructure | 5 | `cb7fbe643a9544240925e9b3230103074c56f2abfa606900a359afde045db620` | `e3eb442bc8cf50bab646cdbc931d759fd1570bec5ae3932aa4b8002c808cd9b2` |

| 個別公理audit module群 | 所有宣言数 | audit SHA256 | log SHA256 |
| --- | ---: | --- | --- |
| W1ActualCorrections | 4 | `0505d635c5684882a781a032f11fe1b27b47c05beab277eb90e217fc8e5b2797` | `9c3b41ca925032b9676d389345e303b53f5fec3db9ce8b180bc0eb9823920979` |
| W1ActualRepairs | 36 | `ac2743dd2dc96cf59f3f171f8ade47963c33453ecd27f7f464b58dc26d8fc7c0` | `8b5b7d39d7456e6c75a2d97a5dc00c79fb497f961afc7feb78b839e7f935d9b2` |
| W1AuthoredOperations | 17 | `2ef58d1cafa7db38f2c716482ce03d3e17510a0b5c8f282dd0ea670eccfe3e0a` | `ca07fedce98105e9c97183190a890489a5d03df3941d97022605686c4f1f3320` |
| W1CandidateColumns | 12 | `9729eaa8f8b6f77f7e5588625e60cebe4a887e01331b32b4738008cf5eee9045` | `e90ab40d5afcff3c4beb94d8b97c2ed161dd9250cce937219bfd44f641050012` |
| W1PermissionClassification, W1NativeLabels | 24 | `6fec2b5faa56cce3aebbb8903d6034a9e4627e2fcdc8b0a7343a681390720b84` | `4a8dfb7b8dc855adfb6099eab178d40a9b0780c334da7f8c5b2cf80a61f9bc13` |
| W1RepairCounts, W1IdentityClassification | 28 | `608efc94a4b81342c49b6bc38d811897e8086622c9c739aad21f9f2228b5327f` | `acd30b1c01c6eede4a686b52cabda001d37a043875d74f3f0fe64b006cc0a258` |
| W1DualMinimalRanges, W1IdentityMinimal | 20 | `444054ed2b234826f6b4b8c6e69e9ee4f263d72e3af21a3fe78ead02cbfefe13` | `8af416ca22841662e9fe29d00b02cfdc636ffc050f25d8f5069a6d90f6f2b3a3` |
| W1FiniteCoefficients | 19 | `e1df5d81ed8cf488b2c83cbef46275ff93bc3263a3e01dde24bc54379d953b0a` | `62f22e879091f272314c73d6edca42e86f2311f830cf671a07c3c30c9ba047b1` |
| W1GeneratedRelations | 5 | `286dde78f8f67ed832ca11c870d4273464ddb25983a9f1158d21f6b9a63cabc9` | `90b202a69aeb9b5f960c6b964ed3363973f607435e921f508799666044ee7bfb` |
| W1GlobalCohomology, W1IndexedCover | 14 | `76de26243c450f59247281844e25d610cf870d1cbc3fa5947fb6d7d106638f5f` | `fd9455bba787038f1c58b639e907d16450b8f92182de1b42fc1466cd81bb2405` |
| W1AffineInput | 23 | `858a97b1a0bdb33587e1968aae783ff9b08d18ffd0b6de114b9c71823d8af924` | `aac55f02cf9f03591f00ace17cb9a63f8eb845c1df63845b1d258342e4d40ebd` |
| W1LocalDifferentials | 6 | `e03722098479137343e7fb55ed1e21c4ecb272c3af50387263f5e1bae6dcb40d` | `2071c894a917b666259e70974602042102584b52190bd10531fb93cbeac49d69` |
| W1LocalEquationCriteria | 5 | `27ebf19e2563dcd95dc408845ae91da348fa947cdb24c0f6ea38930f29d75ddc` | `7a68c232fa887557399c7ddc74797d0082f1c8c7ddb6a8dfa5474b360c67c552` |
| W1LocalInterfaces | 10 | `baab18c5d0736d6ae93bfba49107bcad1a8c2bf8fc7846b0699f69930a0c62d6` | `c910ea5329db31a5a4a4e971c1c470a433dd384f48fdf5b499085147134d32c5` |
| W1LocalPublicValues | 3 | `4478da51ee1ca2e2f57afc55031d634e82d6be28febbc3927520257804a2645b` | `e352bac8b05405154cf956398d6aa1e0cceeba53a552a8529f8953636e6c94f5` |
| W1OriginalObstruction | 16 | `7105d8f1d42027aad71f221998e28bf3238e6248981b011d5a751e52fbb8c88a` | `1509dd7dd84b65bb06d835e2a78d39be18c6bc701112c2a8112df0027ac283d8` |
| W1PrivateMatrixZero | 4 | `551546340c862055526584f536934c521e955f19500446ef39dadb660e06168f` | `1d2e88e5446b06788225d62223977b292ee488bd1d13a3940a739e2654cc4bbb` |
| W1LocalPrivateFreedom, W1SubdivisionSupportedGauge | 11 | `d57a6bdfee697f203764230df459e15e5cb646569dd62c35673e581a5ff5f9b0` | `31eb833e555854c451ccaeace7d1af62ab3d0310092f669bf4e6b02e5fa29d44` |
| W1SymbolicPublicStructure, W1SubdivisionGeneratedRestoration | 9 | `11eb2b530e882b695fb308de296b0dde1789fb1a6ac764527dbcf3ba472f9280` | `846feedcbc7bf413d6a9a5e170f19edc9974fc9c3fde23cc41b9d0aa1a835e37` |
| W1SubdivisionRanges, W1SubdivisionMinimalRanges | 14 | `c15da2843a10653e7094cbdd8a480e4f15cdefeb4e90b9754527fa484373fe1d` | `eda9f380ddec39c5c4b88cad2e2e467c4589f0bb0ee61fa02831ac0b68b1b3b4` |
| W1Regions | 18 | `2f2b7215ad91e73df942f0b111750f3fb0ef105fca726f581a174e49b9d53d66` | `7e5ca4089c55b9c06c369fa1109acd0bb7bff1fb981e833e6fc14ef6438f6508` |
| W1RelativeCoefficients | 15 | `04ef03d0d478ca76198546461a0c9ee0bcdfd54829720ab34ed7d586aeeb6650` | `504d34c0b4ef16e3ebc88fb8e0e0ff91ecb775ae9c77161fdbcbdcb52812fb5a` |
| W1SubdivisionSharedBoundary, W1SubdivisionFreshGauge | 9 | `addb856e665af4fb67c432e60ad121d0c59e5d1542872c35b018e642a5e0f537` | `bb94ac96cd74bff1116c070759d5dc2498f19cf4d8ac998be92f8e909dd7cd3d` |
| W1StrictGeneratedCover | 9 | `9692e5cb18c7637fd080faea5f91ecbcd1bede970dae1b1a2bb101d28b65b526` | `3417675dd392f915c3526e3ad6b6c31d4372c15df209d24176a9f47df4ceb8f8` |
| W1SubdivisionClasses | 6 | `7efd1f379265a63154cad406fbf8926e1538624068b26a6aed8279b16336c1c0` | `b7c237e03ef031e206514c4e380d15edf6afe67d8379a56b99a5050cebc4880e` |
| W1SubdivisionCoordinates | 8 | `a8345f04faf5765221a6ead1ef3cf3875fef4f7328b0610d2e942a8c8c6f3fb3` | `3b70992970ae86305d5f4e1022e9356bff3634803df14d64ef99a13ddb61312f` |
| W1SubdivisionGeneratedInterfaces | 8 | `0b929c80ba02fccbda14c6d0369511c6475d4d4614f466b07baf883285d6e018` | `d311da9cdfc0f68f396094ba1e771b0ae39543b41eff944f0945d1a004d176e7` |
| W1SubdivisionInput | 19 | `d9ee1e5c82250c1d8e201b4c9e81492b8a9871eab127f26e123c54bab7186322` | `c21213c1660d2e675c4f6836e2441a4b498ea4b80cb16a8eda473f2f9ed136e9` |
| W1SubdivisionPreservation | 9 | `4518c60f137a50caf11be36df5e4c92f86fd94ab6ab97b3c8fe440a2b43fbe3d` | `460989bbb6f894f9a3f27c03c054a17ca03f3c8187225e12b871949337d8b439` |
| W1SubdivisionRepairs | 13 | `84000a53cd78f1ebd9398dbf35206afd15d6cc7469681b55661cec9e7e57655a` | `2a8dbba0dc8c9cccc8ddda36351828ea6424f5eeec852e9317a29ab7a9bf143b` |
| W1SubdivisionWords | 6 | `64f27687d0a7491762abeb57a4190e01f812586bbb8cf3d84ef2a66a8a85bfd2` | `a3195dfabe9410b48556d75e4d9d9fdc9441baaf93302a9d2ccf5882610db608` |
| W1SymbolicActualUpdates | 11 | `be951f01c27e31fa60dd8e1d85f7ce51f217c781ae3b2ad4ce8ffe348e06d13e` | `6e2af498338f058df6e9416f24b1e44e47ce10365a79342a363057212020bc10` |
| W1SymbolicLocalStructure, W1SymbolicPublicMatrices, W1SymbolicGeneratedRows | 45 | `547400d5d1e78a40948e03acfea4029e6be387214b7387515f4819e822d14809` | `9820e99d94aab706604bcb4eba16915a5b183672467fdc0b8e852ae0df093829` |

<details>
<summary>C24 所有moduleで選択した全456宣言</summary>

```text
AAT.AG.AbelianLiftingObstruction.GroupExtension.pathValue.eq_def
AAT.AG.RelativeRepairComposition.ClosedRegion.mk.congr_simp
AAT.AG.RelativeRepairComposition.FiniteElimination.Enumeration.mk.congr_simp
AAT.AG.RelativeRepairComposition.NativeAffine.Repair.mk.congr_simp
AAT.AG.RelativeRepairComposition.NativeAffine.vectorPath.eq_def
AAT.AG.RelativeRepairComposition.RelativeCover.r2.congr_simp
AAT.AG.RelativeRepairComposition.W1ActualCorrections.actualRepair_real_correction
AAT.AG.RelativeRepairComposition.W1ActualCorrections.native_correction_parameters
AAT.AG.RelativeRepairComposition.W1ActualCorrections.native_inverse_correction
AAT.AG.RelativeRepairComposition.W1ActualCorrections.parameters_real_correction
AAT.AG.RelativeRepairComposition.W1ActualRepairs.Allowed
AAT.AG.RelativeRepairComposition.W1ActualRepairs.Equations
AAT.AG.RelativeRepairComposition.W1ActualRepairs.Parameters
AAT.AG.RelativeRepairComposition.W1ActualRepairs.Parameters.casesOn
AAT.AG.RelativeRepairComposition.W1ActualRepairs.Parameters.ctorIdx
AAT.AG.RelativeRepairComposition.W1ActualRepairs.Parameters.h
AAT.AG.RelativeRepairComposition.W1ActualRepairs.Parameters.mk
AAT.AG.RelativeRepairComposition.W1ActualRepairs.Parameters.mk.inj
AAT.AG.RelativeRepairComposition.W1ActualRepairs.Parameters.mk.injEq
AAT.AG.RelativeRepairComposition.W1ActualRepairs.Parameters.mk.noConfusion
AAT.AG.RelativeRepairComposition.W1ActualRepairs.Parameters.mk.sizeOf_spec
AAT.AG.RelativeRepairComposition.W1ActualRepairs.Parameters.noConfusion
AAT.AG.RelativeRepairComposition.W1ActualRepairs.Parameters.noConfusionType
AAT.AG.RelativeRepairComposition.W1ActualRepairs.Parameters.rec
AAT.AG.RelativeRepairComposition.W1ActualRepairs.Parameters.recOn
AAT.AG.RelativeRepairComposition.W1ActualRepairs.Parameters.u
AAT.AG.RelativeRepairComposition.W1ActualRepairs.Parameters.v
AAT.AG.RelativeRepairComposition.W1ActualRepairs.Parameters.z
AAT.AG.RelativeRepairComposition.W1ActualRepairs.RealRepairs
AAT.AG.RelativeRepairComposition.W1ActualRepairs.actualParametersEquiv
AAT.AG.RelativeRepairComposition.W1ActualRepairs.actualRepair
AAT.AG.RelativeRepairComposition.W1ActualRepairs.actualRepair_parameters
AAT.AG.RelativeRepairComposition.W1ActualRepairs.actual_operation_apply
AAT.AG.RelativeRepairComposition.W1ActualRepairs.instDecidableEqParameters
AAT.AG.RelativeRepairComposition.W1ActualRepairs.instDecidableEqParameters.decEq
AAT.AG.RelativeRepairComposition.W1ActualRepairs.nativeParametersEquiv
AAT.AG.RelativeRepairComposition.W1ActualRepairs.operation_faces
AAT.AG.RelativeRepairComposition.W1ActualRepairs.operation_fixed
AAT.AG.RelativeRepairComposition.W1ActualRepairs.operation_linear
AAT.AG.RelativeRepairComposition.W1ActualRepairs.parameters
AAT.AG.RelativeRepairComposition.W1ActualRepairs.parameters_actualRepair
AAT.AG.RelativeRepairComposition.W1ActualRepairs.parameters_allowed
AAT.AG.RelativeRepairComposition.W1ActualRepairs.parameters_equations
AAT.AG.RelativeRepairComposition.W1ActualRepairs.parameters_operations
AAT.AG.RelativeRepairComposition.W1ActualRepairs.zero_translation
AAT.AG.RelativeRepairComposition.W1AffineInput.Op
AAT.AG.RelativeRepairComposition.W1AffineInput.comparison
AAT.AG.RelativeRepairComposition.W1AffineInput.edgeA
AAT.AG.RelativeRepairComposition.W1AffineInput.edgeB
AAT.AG.RelativeRepairComposition.W1AffineInput.edgeC
AAT.AG.RelativeRepairComposition.W1AffineInput.edgeDecidableEq
AAT.AG.RelativeRepairComposition.W1AffineInput.edgeE
AAT.AG.RelativeRepairComposition.W1AffineInput.edgeRx
AAT.AG.RelativeRepairComposition.W1AffineInput.edgeRy
AAT.AG.RelativeRepairComposition.W1AffineInput.faceDecidableEq
AAT.AG.RelativeRepairComposition.W1AffineInput.flip
AAT.AG.RelativeRepairComposition.W1AffineInput.flip_apply
AAT.AG.RelativeRepairComposition.W1AffineInput.flip_square
AAT.AG.RelativeRepairComposition.W1AffineInput.geometry
AAT.AG.RelativeRepairComposition.W1AffineInput.linearA
AAT.AG.RelativeRepairComposition.W1AffineInput.linearA_square
AAT.AG.RelativeRepairComposition.W1AffineInput.linear_faces
AAT.AG.RelativeRepairComposition.W1AffineInput.originalTower
AAT.AG.RelativeRepairComposition.W1AffineInput.primeThree
AAT.AG.RelativeRepairComposition.W1AffineInput.reference
AAT.AG.RelativeRepairComposition.W1AffineInput.reference_left_path
AAT.AG.RelativeRepairComposition.W1AffineInput.reference_right_path
AAT.AG.RelativeRepairComposition.W1AuthoredOperations.correctionValue
AAT.AG.RelativeRepairComposition.W1AuthoredOperations.first_law_iff
AAT.AG.RelativeRepairComposition.W1AuthoredOperations.first_left_apply
AAT.AG.RelativeRepairComposition.W1AuthoredOperations.linearA_apply
AAT.AG.RelativeRepairComposition.W1AuthoredOperations.operation
AAT.AG.RelativeRepairComposition.W1AuthoredOperations.operation_a_apply
AAT.AG.RelativeRepairComposition.W1AuthoredOperations.operation_b_apply
AAT.AG.RelativeRepairComposition.W1AuthoredOperations.operation_c_apply
AAT.AG.RelativeRepairComposition.W1AuthoredOperations.operation_e_apply
AAT.AG.RelativeRepairComposition.W1AuthoredOperations.operation_rx_apply
AAT.AG.RelativeRepairComposition.W1AuthoredOperations.operation_ry_apply
AAT.AG.RelativeRepairComposition.W1AuthoredOperations.right_apply
AAT.AG.RelativeRepairComposition.W1AuthoredOperations.second_identity_apply
AAT.AG.RelativeRepairComposition.W1AuthoredOperations.second_identity_law_iff
AAT.AG.RelativeRepairComposition.W1AuthoredOperations.second_negative_apply
AAT.AG.RelativeRepairComposition.W1AuthoredOperations.second_negative_law_iff
AAT.AG.RelativeRepairComposition.W1CandidateColumns.b_column_coordinate
AAT.AG.RelativeRepairComposition.W1CandidateColumns.b_column_surjective
AAT.AG.RelativeRepairComposition.W1CandidateColumns.c_column_coordinate
AAT.AG.RelativeRepairComposition.W1CandidateColumns.c_column_surjective
AAT.AG.RelativeRepairComposition.W1CandidateColumns.candidateB
AAT.AG.RelativeRepairComposition.W1CandidateColumns.candidateB_ne_candidateC
AAT.AG.RelativeRepairComposition.W1CandidateColumns.candidateC
AAT.AG.RelativeRepairComposition.W1CandidateColumns.candidate_coordinate
AAT.AG.RelativeRepairComposition.W1CandidateColumns.candidate_d1_first
AAT.AG.RelativeRepairComposition.W1CandidateColumns.candidate_d1_second
AAT.AG.RelativeRepairComposition.W1CandidateColumns.column_reading
AAT.AG.RelativeRepairComposition.W1CandidateColumns.noncandidate_coordinate
AAT.AG.RelativeRepairComposition.W1DualMinimalRanges.actual_dual_iff
AAT.AG.RelativeRepairComposition.W1DualMinimalRanges.actual_range_iff
AAT.AG.RelativeRepairComposition.W1DualMinimalRanges.candidate_cases
AAT.AG.RelativeRepairComposition.W1DualMinimalRanges.column_surjective
AAT.AG.RelativeRepairComposition.W1DualMinimalRanges.dualCoordinate
AAT.AG.RelativeRepairComposition.W1DualMinimalRanges.dualCoordinate_obstruction
AAT.AG.RelativeRepairComposition.W1DualMinimalRanges.empty_failure_dual
AAT.AG.RelativeRepairComposition.W1DualMinimalRanges.empty_range_zero
AAT.AG.RelativeRepairComposition.W1DualMinimalRanges.minimal_actual_iff_dual
AAT.AG.RelativeRepairComposition.W1DualMinimalRanges.minimal_actual_iff_range
AAT.AG.RelativeRepairComposition.W1DualMinimalRanges.minimal_nonempty_iff_singleton
AAT.AG.RelativeRepairComposition.W1DualMinimalRanges.minimal_nonzero_iff
AAT.AG.RelativeRepairComposition.W1DualMinimalRanges.minimal_zero_iff
AAT.AG.RelativeRepairComposition.W1DualMinimalRanges.native_range_iff
AAT.AG.RelativeRepairComposition.W1DualMinimalRanges.nonempty_range_top
AAT.AG.RelativeRepairComposition.W1DualMinimalRanges.nonzero_dual_support
AAT.AG.RelativeRepairComposition.W1DualMinimalRanges.range_contains_iff
AAT.AG.RelativeRepairComposition.W1FiniteCoefficients.bases
AAT.AG.RelativeRepairComposition.W1FiniteCoefficients.basisIndex
AAT.AG.RelativeRepairComposition.W1FiniteCoefficients.basis_value
AAT.AG.RelativeRepairComposition.W1FiniteCoefficients.d1_first
AAT.AG.RelativeRepairComposition.W1FiniteCoefficients.d1_second_identity
AAT.AG.RelativeRepairComposition.W1FiniteCoefficients.d1_second_negative
AAT.AG.RelativeRepairComposition.W1FiniteCoefficients.d2_zero
AAT.AG.RelativeRepairComposition.W1FiniteCoefficients.defect_coordinate
AAT.AG.RelativeRepairComposition.W1FiniteCoefficients.enumEdges
AAT.AG.RelativeRepairComposition.W1FiniteCoefficients.enumFaces
AAT.AG.RelativeRepairComposition.W1FiniteCoefficients.enumK
AAT.AG.RelativeRepairComposition.W1FiniteCoefficients.kernelCoordinate
AAT.AG.RelativeRepairComposition.W1FiniteCoefficients.kernel_inverse_value
AAT.AG.RelativeRepairComposition.W1FiniteCoefficients.original_linear
AAT.AG.RelativeRepairComposition.W1FiniteCoefficients.reference_a
AAT.AG.RelativeRepairComposition.W1FiniteCoefficients.reference_b
AAT.AG.RelativeRepairComposition.W1FiniteCoefficients.reference_e
AAT.AG.RelativeRepairComposition.W1FiniteCoefficients.translation_inverse_apply
AAT.AG.RelativeRepairComposition.W1GeneratedRelations.left_relation
AAT.AG.RelativeRepairComposition.W1GeneratedRelations.projection_identity
AAT.AG.RelativeRepairComposition.W1GeneratedRelations.publicCochain
AAT.AG.RelativeRepairComposition.W1GeneratedRelations.relation_iff_equation
AAT.AG.RelativeRepairComposition.W1GeneratedRelations.right_relation
AAT.AG.RelativeRepairComposition.W1GlobalCohomology.all_candidate_face_class_zero
AAT.AG.RelativeRepairComposition.W1GlobalCohomology.differential_range_top
AAT.AG.RelativeRepairComposition.W1GlobalCohomology.differential_surjective
AAT.AG.RelativeRepairComposition.W1GlobalCohomology.h2_zero
AAT.AG.RelativeRepairComposition.W1GlobalCohomology.original_h2_zero
AAT.AG.RelativeRepairComposition.W1GlobalCohomology.secondQuotientEquivalence
AAT.AG.RelativeRepairComposition.W1GlobalCohomology.secondQuotient_value
AAT.AG.RelativeRepairComposition.W1IdentityClassification.IdentityChoices
AAT.AG.RelativeRepairComposition.W1IdentityClassification.identityActualEquiv
AAT.AG.RelativeRepairComposition.W1IdentityClassification.identityBChoiceEquiv
AAT.AG.RelativeRepairComposition.W1IdentityClassification.identityCChoiceEquiv
AAT.AG.RelativeRepairComposition.W1IdentityClassification.identityEmptyChoiceEquiv
AAT.AG.RelativeRepairComposition.W1IdentityClassification.identityFullChoiceEquiv
AAT.AG.RelativeRepairComposition.W1IdentityClassification.identityParametersEquiv
AAT.AG.RelativeRepairComposition.W1IdentityClassification.identity_b_card
AAT.AG.RelativeRepairComposition.W1IdentityClassification.identity_c_card
AAT.AG.RelativeRepairComposition.W1IdentityClassification.identity_class_counts
AAT.AG.RelativeRepairComposition.W1IdentityClassification.identity_empty_card
AAT.AG.RelativeRepairComposition.W1IdentityClassification.identity_full_card
AAT.AG.RelativeRepairComposition.W1IdentityClassification.twice_eq_iff
AAT.AG.RelativeRepairComposition.W1IdentityClassification.twice_twice
AAT.AG.RelativeRepairComposition.W1IdentityMinimal.actual_exists
AAT.AG.RelativeRepairComposition.W1IdentityMinimal.minimal_iff_empty
AAT.AG.RelativeRepairComposition.W1IdentityMinimal.named_minimal_iff_empty
AAT.AG.RelativeRepairComposition.W1IndexedCover.candidates_public
AAT.AG.RelativeRepairComposition.W1IndexedCover.enumRegions
AAT.AG.RelativeRepairComposition.W1IndexedCover.indexed_cover
AAT.AG.RelativeRepairComposition.W1IndexedCover.private_left
AAT.AG.RelativeRepairComposition.W1IndexedCover.private_right
AAT.AG.RelativeRepairComposition.W1IndexedCover.regions
AAT.AG.RelativeRepairComposition.W1IndexedCover.shared_e_public
AAT.AG.RelativeRepairComposition.W1LocalDifferentials.extension_named
AAT.AG.RelativeRepairComposition.W1LocalDifferentials.extension_value
AAT.AG.RelativeRepairComposition.W1LocalDifferentials.fixed_value
AAT.AG.RelativeRepairComposition.W1LocalDifferentials.left_differential
AAT.AG.RelativeRepairComposition.W1LocalDifferentials.right_differential
AAT.AG.RelativeRepairComposition.W1LocalDifferentials.value
AAT.AG.RelativeRepairComposition.W1LocalEquationCriteria.left_equation_iff
AAT.AG.RelativeRepairComposition.W1LocalEquationCriteria.left_rhs
AAT.AG.RelativeRepairComposition.W1LocalEquationCriteria.right_equation_iff
AAT.AG.RelativeRepairComposition.W1LocalEquationCriteria.right_rhs
AAT.AG.RelativeRepairComposition.W1LocalInterfaces.elimination
AAT.AG.RelativeRepairComposition.W1LocalInterfaces.equationEquiv
AAT.AG.RelativeRepairComposition.W1LocalInterfaces.generatedSection
AAT.AG.RelativeRepairComposition.W1LocalInterfaces.nativeEquivalence
AAT.AG.RelativeRepairComposition.W1LocalInterfaces.privateMatrix
AAT.AG.RelativeRepairComposition.W1LocalInterfaces.publicMatrix
AAT.AG.RelativeRepairComposition.W1LocalInterfaces.public_row_count
AAT.AG.RelativeRepairComposition.W1LocalInterfaces.public_rows_independent
AAT.AG.RelativeRepairComposition.W1LocalInterfaces.relation
AAT.AG.RelativeRepairComposition.W1LocalInterfaces.section_regular
AAT.AG.RelativeRepairComposition.W1LocalPrivateFreedom.aIndex
AAT.AG.RelativeRepairComposition.W1LocalPrivateFreedom.aIndex_unique
AAT.AG.RelativeRepairComposition.W1LocalPrivateFreedom.left_private_empty
AAT.AG.RelativeRepairComposition.W1LocalPrivateFreedom.private_h_mem
AAT.AG.RelativeRepairComposition.W1LocalPrivateFreedom.private_vector_complete
AAT.AG.RelativeRepairComposition.W1LocalPrivateFreedom.restored_a_value
AAT.AG.RelativeRepairComposition.W1LocalPublicValues.face_coordinate
AAT.AG.RelativeRepairComposition.W1LocalPublicValues.publicIndex
AAT.AG.RelativeRepairComposition.W1LocalPublicValues.public_value
AAT.AG.RelativeRepairComposition.W1NativeLabels.NativeCategory
AAT.AG.RelativeRepairComposition.W1NativeLabels.aut_identity
AAT.AG.RelativeRepairComposition.W1NativeLabels.classParametersEquiv
AAT.AG.RelativeRepairComposition.W1NativeLabels.class_card_eq_actual_card
AAT.AG.RelativeRepairComposition.W1NativeLabels.hom_iff
AAT.AG.RelativeRepairComposition.W1NativeLabels.hom_label_zero
AAT.AG.RelativeRepairComposition.W1NativeLabels.hom_unique
AAT.AG.RelativeRepairComposition.W1NativeLabels.label_zero
AAT.AG.RelativeRepairComposition.W1NativeLabels.objectParametersEquiv
AAT.AG.RelativeRepairComposition.W1NativeLabels.wholeAffineEquivalence
AAT.AG.RelativeRepairComposition.W1OriginalObstruction.allEdgesDecidable
AAT.AG.RelativeRepairComposition.W1OriginalObstruction.alwaysCochain
AAT.AG.RelativeRepairComposition.W1OriginalObstruction.alwaysCochain_first
AAT.AG.RelativeRepairComposition.W1OriginalObstruction.alwaysCochain_second
AAT.AG.RelativeRepairComposition.W1OriginalObstruction.always_first_value
AAT.AG.RelativeRepairComposition.W1OriginalObstruction.always_range_eq_kernel
AAT.AG.RelativeRepairComposition.W1OriginalObstruction.always_second_value
AAT.AG.RelativeRepairComposition.W1OriginalObstruction.edgeNameDecidableEq
AAT.AG.RelativeRepairComposition.W1OriginalObstruction.obstruction
AAT.AG.RelativeRepairComposition.W1OriginalObstruction.obstructionCoordinate
AAT.AG.RelativeRepairComposition.W1OriginalObstruction.obstructionCoordinate_q
AAT.AG.RelativeRepairComposition.W1OriginalObstruction.obstructionReading
AAT.AG.RelativeRepairComposition.W1OriginalObstruction.obstructionReading_surjective
AAT.AG.RelativeRepairComposition.W1OriginalObstruction.obstructionReading_value
AAT.AG.RelativeRepairComposition.W1OriginalObstruction.obstruction_coordinate
AAT.AG.RelativeRepairComposition.W1OriginalObstruction.obstruction_eq_zero_iff
AAT.AG.RelativeRepairComposition.W1PermissionClassification.NegativeChoices
AAT.AG.RelativeRepairComposition.W1PermissionClassification.forbidden_b_fail
AAT.AG.RelativeRepairComposition.W1PermissionClassification.identity_empty_exists
AAT.AG.RelativeRepairComposition.W1PermissionClassification.identity_equations_iff
AAT.AG.RelativeRepairComposition.W1PermissionClassification.negativeActualEquiv
AAT.AG.RelativeRepairComposition.W1PermissionClassification.negativeFullEquiv
AAT.AG.RelativeRepairComposition.W1PermissionClassification.negativeNativeEquiv
AAT.AG.RelativeRepairComposition.W1PermissionClassification.negativeParametersEquiv
AAT.AG.RelativeRepairComposition.W1PermissionClassification.negative_b_exists
AAT.AG.RelativeRepairComposition.W1PermissionClassification.negative_c_exists
AAT.AG.RelativeRepairComposition.W1PermissionClassification.negative_empty_exists_iff
AAT.AG.RelativeRepairComposition.W1PermissionClassification.negative_equations_iff
AAT.AG.RelativeRepairComposition.W1PermissionClassification.nonzero_equations_fail
AAT.AG.RelativeRepairComposition.W1PermissionClassification.zero_instance
AAT.AG.RelativeRepairComposition.W1PrivateMatrixZero.private_d_zero
AAT.AG.RelativeRepairComposition.W1PrivateMatrixZero.private_kernel_top
AAT.AG.RelativeRepairComposition.W1PrivateMatrixZero.private_matrix_zero
AAT.AG.RelativeRepairComposition.W1PrivateMatrixZero.zero_public_value
AAT.AG.RelativeRepairComposition.W1Regions.always_not_fixed
AAT.AG.RelativeRepairComposition.W1Regions.b_fixed_iff
AAT.AG.RelativeRepairComposition.W1Regions.c_fixed_iff
AAT.AG.RelativeRepairComposition.W1Regions.candidates
AAT.AG.RelativeRepairComposition.W1Regions.fixedEdges
AAT.AG.RelativeRepairComposition.W1Regions.fixedRegion
AAT.AG.RelativeRepairComposition.W1Regions.leftRegion
AAT.AG.RelativeRepairComposition.W1Regions.name
AAT.AG.RelativeRepairComposition.W1Regions.name_edge
AAT.AG.RelativeRepairComposition.W1Regions.overlap
AAT.AG.RelativeRepairComposition.W1Regions.overlap_edges
AAT.AG.RelativeRepairComposition.W1Regions.overlap_vertices
AAT.AG.RelativeRepairComposition.W1Regions.regions_cover
AAT.AG.RelativeRepairComposition.W1Regions.rightRegion
AAT.AG.RelativeRepairComposition.W1Regions.rx_fixed
AAT.AG.RelativeRepairComposition.W1Regions.ry_fixed
AAT.AG.RelativeRepairComposition.W1RelativeCoefficients.actualDefect
AAT.AG.RelativeRepairComposition.W1RelativeCoefficients.actualDefect_coordinates
AAT.AG.RelativeRepairComposition.W1RelativeCoefficients.candidates_outside
AAT.AG.RelativeRepairComposition.W1RelativeCoefficients.edgeCoordinate
AAT.AG.RelativeRepairComposition.W1RelativeCoefficients.faceCoordinates
AAT.AG.RelativeRepairComposition.W1RelativeCoefficients.faceCoordinates_value
AAT.AG.RelativeRepairComposition.W1RelativeCoefficients.fixed_edge_coordinate
AAT.AG.RelativeRepairComposition.W1RelativeCoefficients.fixed_faces
AAT.AG.RelativeRepairComposition.W1RelativeCoefficients.relativeCochain
AAT.AG.RelativeRepairComposition.W1RelativeCoefficients.relativeCochain_value
AAT.AG.RelativeRepairComposition.W1RelativeCoefficients.relative_d1_first
AAT.AG.RelativeRepairComposition.W1RelativeCoefficients.relative_d1_second_identity
AAT.AG.RelativeRepairComposition.W1RelativeCoefficients.relative_d1_second_negative
AAT.AG.RelativeRepairComposition.W1RelativeCoefficients.relative_differential_value
AAT.AG.RelativeRepairComposition.W1RelativeCoefficients.signedDefect_coordinates
AAT.AG.RelativeRepairComposition.W1RepairCounts.negativeBActualEquiv
AAT.AG.RelativeRepairComposition.W1RepairCounts.negativeBChoiceEquiv
AAT.AG.RelativeRepairComposition.W1RepairCounts.negativeCActualEquiv
AAT.AG.RelativeRepairComposition.W1RepairCounts.negativeCChoiceEquiv
AAT.AG.RelativeRepairComposition.W1RepairCounts.negativeEmptyActualEquiv
AAT.AG.RelativeRepairComposition.W1RepairCounts.negativeEmptyChoiceEquiv
AAT.AG.RelativeRepairComposition.W1RepairCounts.negative_b_card
AAT.AG.RelativeRepairComposition.W1RepairCounts.negative_b_class_card
AAT.AG.RelativeRepairComposition.W1RepairCounts.negative_c_card
AAT.AG.RelativeRepairComposition.W1RepairCounts.negative_c_class_card
AAT.AG.RelativeRepairComposition.W1RepairCounts.negative_empty_card
AAT.AG.RelativeRepairComposition.W1RepairCounts.negative_empty_class_card
AAT.AG.RelativeRepairComposition.W1RepairCounts.negative_full_card
AAT.AG.RelativeRepairComposition.W1RepairCounts.negative_full_class_card
AAT.AG.RelativeRepairComposition.W1StrictGeneratedCover.Groupoid
AAT.AG.RelativeRepairComposition.W1StrictGeneratedCover.Objects
AAT.AG.RelativeRepairComposition.W1StrictGeneratedCover.actualEquivalence
AAT.AG.RelativeRepairComposition.W1StrictGeneratedCover.actualObjectEquiv
AAT.AG.RelativeRepairComposition.W1StrictGeneratedCover.extract_restore
AAT.AG.RelativeRepairComposition.W1StrictGeneratedCover.generated_feasible_iff
AAT.AG.RelativeRepairComposition.W1StrictGeneratedCover.nativeEquivalence
AAT.AG.RelativeRepairComposition.W1StrictGeneratedCover.restore_extract
AAT.AG.RelativeRepairComposition.W1StrictGeneratedCover.restore_operation
AAT.AG.RelativeRepairComposition.W1SubdivisionClasses.b_class_card
AAT.AG.RelativeRepairComposition.W1SubdivisionClasses.c_class_card
AAT.AG.RelativeRepairComposition.W1SubdivisionClasses.classEquiv
AAT.AG.RelativeRepairComposition.W1SubdivisionClasses.class_card
AAT.AG.RelativeRepairComposition.W1SubdivisionClasses.empty_class_card
AAT.AG.RelativeRepairComposition.W1SubdivisionClasses.full_class_card
AAT.AG.RelativeRepairComposition.W1SubdivisionCoordinates.all_pairs
AAT.AG.RelativeRepairComposition.W1SubdivisionCoordinates.collapse_coordinate
AAT.AG.RelativeRepairComposition.W1SubdivisionCoordinates.middle_inclusion
AAT.AG.RelativeRepairComposition.W1SubdivisionCoordinates.old_a_coordinate
AAT.AG.RelativeRepairComposition.W1SubdivisionCoordinates.restore_first
AAT.AG.RelativeRepairComposition.W1SubdivisionCoordinates.restore_second
AAT.AG.RelativeRepairComposition.W1SubdivisionCoordinates.rho2_coordinate
AAT.AG.RelativeRepairComposition.W1SubdivisionCoordinates.second_linear
AAT.AG.RelativeRepairComposition.W1SubdivisionFreshGauge.first_d0
AAT.AG.RelativeRepairComposition.W1SubdivisionFreshGauge.first_shift
AAT.AG.RelativeRepairComposition.W1SubdivisionFreshGauge.freshLabel
AAT.AG.RelativeRepairComposition.W1SubdivisionFreshGauge.second_d0
AAT.AG.RelativeRepairComposition.W1SubdivisionFreshGauge.second_shift
AAT.AG.RelativeRepairComposition.W1SubdivisionGeneratedInterfaces.actualObjectEquiv
AAT.AG.RelativeRepairComposition.W1SubdivisionGeneratedInterfaces.comparison
AAT.AG.RelativeRepairComposition.W1SubdivisionGeneratedInterfaces.local_restore
AAT.AG.RelativeRepairComposition.W1SubdivisionGeneratedInterfaces.newExtraction
AAT.AG.RelativeRepairComposition.W1SubdivisionGeneratedInterfaces.oldExtraction
AAT.AG.RelativeRepairComposition.W1SubdivisionGeneratedInterfaces.public_relation_iff
AAT.AG.RelativeRepairComposition.W1SubdivisionGeneratedInterfaces.strictEquivalence
AAT.AG.RelativeRepairComposition.W1SubdivisionGeneratedInterfaces.values
AAT.AG.RelativeRepairComposition.W1SubdivisionGeneratedRestoration.actualNativeEquivalence
AAT.AG.RelativeRepairComposition.W1SubdivisionGeneratedRestoration.actual_restore
AAT.AG.RelativeRepairComposition.W1SubdivisionGeneratedRestoration.extracted_correction
AAT.AG.RelativeRepairComposition.W1SubdivisionGeneratedRestoration.generated_restore
AAT.AG.RelativeRepairComposition.W1SubdivisionInput.chosen
AAT.AG.RelativeRepairComposition.W1SubdivisionInput.chosen_not_P
AAT.AG.RelativeRepairComposition.W1SubdivisionInput.chosen_not_W
AAT.AG.RelativeRepairComposition.W1SubdivisionInput.chosen_not_candidate
AAT.AG.RelativeRepairComposition.W1SubdivisionInput.chosen_not_fixed
AAT.AG.RelativeRepairComposition.W1SubdivisionInput.chosen_private
AAT.AG.RelativeRepairComposition.W1SubdivisionInput.factor_product
AAT.AG.RelativeRepairComposition.W1SubdivisionInput.factor_reference
AAT.AG.RelativeRepairComposition.W1SubdivisionInput.factors
AAT.AG.RelativeRepairComposition.W1SubdivisionInput.first
AAT.AG.RelativeRepairComposition.W1SubdivisionInput.first_apply
AAT.AG.RelativeRepairComposition.W1SubdivisionInput.first_private
AAT.AG.RelativeRepairComposition.W1SubdivisionInput.fresh_not_P
AAT.AG.RelativeRepairComposition.W1SubdivisionInput.fresh_not_W
AAT.AG.RelativeRepairComposition.W1SubdivisionInput.second
AAT.AG.RelativeRepairComposition.W1SubdivisionInput.second_apply
AAT.AG.RelativeRepairComposition.W1SubdivisionInput.second_private
AAT.AG.RelativeRepairComposition.W1SubdivisionInput.splitTower
AAT.AG.RelativeRepairComposition.W1SubdivisionInput.split_cover
AAT.AG.RelativeRepairComposition.W1SubdivisionMinimalRanges.feasibility
AAT.AG.RelativeRepairComposition.W1SubdivisionMinimalRanges.minimal_iff_old_actual
AAT.AG.RelativeRepairComposition.W1SubdivisionMinimalRanges.minimal_nonzero
AAT.AG.RelativeRepairComposition.W1SubdivisionMinimalRanges.minimal_zero
AAT.AG.RelativeRepairComposition.W1SubdivisionPreservation.allHomologyIso
AAT.AG.RelativeRepairComposition.W1SubdivisionPreservation.complexIso
AAT.AG.RelativeRepairComposition.W1SubdivisionPreservation.defect_value
AAT.AG.RelativeRepairComposition.W1SubdivisionPreservation.fresh_contraction
AAT.AG.RelativeRepairComposition.W1SubdivisionPreservation.fresh_identity
AAT.AG.RelativeRepairComposition.W1SubdivisionPreservation.h0Equiv
AAT.AG.RelativeRepairComposition.W1SubdivisionPreservation.obstruction_class
AAT.AG.RelativeRepairComposition.W1SubdivisionPreservation.old_holonomy
AAT.AG.RelativeRepairComposition.W1SubdivisionPreservation.original_syzygy
AAT.AG.RelativeRepairComposition.W1SubdivisionRanges.candidateNames
AAT.AG.RelativeRepairComposition.W1SubdivisionRanges.candidate_column
AAT.AG.RelativeRepairComposition.W1SubdivisionRanges.newDual
AAT.AG.RelativeRepairComposition.W1SubdivisionRanges.newObstruction
AAT.AG.RelativeRepairComposition.W1SubdivisionRanges.new_column_surjective
AAT.AG.RelativeRepairComposition.W1SubdivisionRanges.new_dual_value
AAT.AG.RelativeRepairComposition.W1SubdivisionRanges.new_empty_failure_dual
AAT.AG.RelativeRepairComposition.W1SubdivisionRanges.new_nonzero_dual_support
AAT.AG.RelativeRepairComposition.W1SubdivisionRanges.new_obstruction_coordinate
AAT.AG.RelativeRepairComposition.W1SubdivisionRanges.quotientCoordinate
AAT.AG.RelativeRepairComposition.W1SubdivisionRepairs.NewCategory
AAT.AG.RelativeRepairComposition.W1SubdivisionRepairs.NewRepairs
AAT.AG.RelativeRepairComposition.W1SubdivisionRepairs.aut_identity
AAT.AG.RelativeRepairComposition.W1SubdivisionRepairs.b_card
AAT.AG.RelativeRepairComposition.W1SubdivisionRepairs.c_card
AAT.AG.RelativeRepairComposition.W1SubdivisionRepairs.counit_full_label
AAT.AG.RelativeRepairComposition.W1SubdivisionRepairs.empty_card
AAT.AG.RelativeRepairComposition.W1SubdivisionRepairs.full_card
AAT.AG.RelativeRepairComposition.W1SubdivisionRepairs.hom_unique
AAT.AG.RelativeRepairComposition.W1SubdivisionRepairs.middleCoefficient
AAT.AG.RelativeRepairComposition.W1SubdivisionRepairs.nativeEquivalence
AAT.AG.RelativeRepairComposition.W1SubdivisionRepairs.repairEquiv
AAT.AG.RelativeRepairComposition.W1SubdivisionRepairs.repair_card
AAT.AG.RelativeRepairComposition.W1SubdivisionSharedBoundary.collapse_shared
AAT.AG.RelativeRepairComposition.W1SubdivisionSharedBoundary.external_join
AAT.AG.RelativeRepairComposition.W1SubdivisionSharedBoundary.restore_shared
AAT.AG.RelativeRepairComposition.W1SubdivisionSharedBoundary.shared_relation
AAT.AG.RelativeRepairComposition.W1SubdivisionSupportedGauge.first_supported_shift
AAT.AG.RelativeRepairComposition.W1SubdivisionSupportedGauge.fullLabel
AAT.AG.RelativeRepairComposition.W1SubdivisionSupportedGauge.fullLabel_value
AAT.AG.RelativeRepairComposition.W1SubdivisionSupportedGauge.labels_complete
AAT.AG.RelativeRepairComposition.W1SubdivisionSupportedGauge.second_supported_shift
AAT.AG.RelativeRepairComposition.W1SubdivisionWords.first_word
AAT.AG.RelativeRepairComposition.W1SubdivisionWords.name_ne_chosen
AAT.AG.RelativeRepairComposition.W1SubdivisionWords.retainedB
AAT.AG.RelativeRepairComposition.W1SubdivisionWords.retainedC
AAT.AG.RelativeRepairComposition.W1SubdivisionWords.retainedE
AAT.AG.RelativeRepairComposition.W1SubdivisionWords.second_word
AAT.AG.RelativeRepairComposition.W1SymbolicActualUpdates.bUpdated
AAT.AG.RelativeRepairComposition.W1SymbolicActualUpdates.b_corrections
AAT.AG.RelativeRepairComposition.W1SymbolicActualUpdates.b_operations
AAT.AG.RelativeRepairComposition.W1SymbolicActualUpdates.b_parameters
AAT.AG.RelativeRepairComposition.W1SymbolicActualUpdates.cUpdated
AAT.AG.RelativeRepairComposition.W1SymbolicActualUpdates.c_corrections
AAT.AG.RelativeRepairComposition.W1SymbolicActualUpdates.c_operations
AAT.AG.RelativeRepairComposition.W1SymbolicActualUpdates.c_parameters
AAT.AG.RelativeRepairComposition.W1SymbolicActualUpdates.symbolic_signed_rhs
AAT.AG.RelativeRepairComposition.W1SymbolicActualUpdates.updated_failure_dual
AAT.AG.RelativeRepairComposition.W1SymbolicActualUpdates.zero_to_nonzero_empty
AAT.AG.RelativeRepairComposition.W1SymbolicGeneratedRows.actualPublic
AAT.AG.RelativeRepairComposition.W1SymbolicGeneratedRows.generated_rows_same
AAT.AG.RelativeRepairComposition.W1SymbolicGeneratedRows.projected_eq_public
AAT.AG.RelativeRepairComposition.W1SymbolicGeneratedRows.projected_matrix_same
AAT.AG.RelativeRepairComposition.W1SymbolicGeneratedRows.public_enumeration_same
AAT.AG.RelativeRepairComposition.W1SymbolicGeneratedRows.rowsFor
AAT.AG.RelativeRepairComposition.W1SymbolicGeneratedRows.rows_congr
AAT.AG.RelativeRepairComposition.W1SymbolicGeneratedRows.structuralProjectedMatrix
AAT.AG.RelativeRepairComposition.W1SymbolicLocalStructure.actualEdges
AAT.AG.RelativeRepairComposition.W1SymbolicLocalStructure.actualEnum
AAT.AG.RelativeRepairComposition.W1SymbolicLocalStructure.actualFaces
AAT.AG.RelativeRepairComposition.W1SymbolicLocalStructure.actualPrivate
AAT.AG.RelativeRepairComposition.W1SymbolicLocalStructure.basis_dimension_same
AAT.AG.RelativeRepairComposition.W1SymbolicLocalStructure.edgeIndex
AAT.AG.RelativeRepairComposition.W1SymbolicLocalStructure.edges_same
AAT.AG.RelativeRepairComposition.W1SymbolicLocalStructure.elimination_same
AAT.AG.RelativeRepairComposition.W1SymbolicLocalStructure.enumeration_same
AAT.AG.RelativeRepairComposition.W1SymbolicLocalStructure.enumeration_subtype_congr
AAT.AG.RelativeRepairComposition.W1SymbolicLocalStructure.faceIndex
AAT.AG.RelativeRepairComposition.W1SymbolicLocalStructure.faces_same
AAT.AG.RelativeRepairComposition.W1SymbolicLocalStructure.privateIndex
AAT.AG.RelativeRepairComposition.W1SymbolicLocalStructure.private_matrix_same
AAT.AG.RelativeRepairComposition.W1SymbolicLocalStructure.private_same
AAT.AG.RelativeRepairComposition.W1SymbolicLocalStructure.publicIndex
AAT.AG.RelativeRepairComposition.W1SymbolicLocalStructure.reduction_congr
AAT.AG.RelativeRepairComposition.W1SymbolicLocalStructure.sectionFor
AAT.AG.RelativeRepairComposition.W1SymbolicLocalStructure.section_congr
AAT.AG.RelativeRepairComposition.W1SymbolicLocalStructure.section_same
AAT.AG.RelativeRepairComposition.W1SymbolicLocalStructure.structuralEdges
AAT.AG.RelativeRepairComposition.W1SymbolicLocalStructure.structuralFaces
AAT.AG.RelativeRepairComposition.W1SymbolicLocalStructure.structuralPrivateMatrix
AAT.AG.RelativeRepairComposition.W1SymbolicLocalStructure.structuralSection
AAT.AG.RelativeRepairComposition.W1SymbolicLocalStructure.structural_private_matrix_zero
AAT.AG.RelativeRepairComposition.W1SymbolicPublicMatrices.commonPublicMatrix
AAT.AG.RelativeRepairComposition.W1SymbolicPublicMatrices.edgeIndex
AAT.AG.RelativeRepairComposition.W1SymbolicPublicMatrices.faceIndex
AAT.AG.RelativeRepairComposition.W1SymbolicPublicMatrices.namedPublicIndex
AAT.AG.RelativeRepairComposition.W1SymbolicPublicMatrices.publicIndex
AAT.AG.RelativeRepairComposition.W1SymbolicPublicMatrices.public_matrix_eq_common
AAT.AG.RelativeRepairComposition.W1SymbolicPublicMatrices.public_matrix_same
AAT.AG.RelativeRepairComposition.W1SymbolicPublicMatrices.structuralB
AAT.AG.RelativeRepairComposition.W1SymbolicPublicMatrices.structuralC
AAT.AG.RelativeRepairComposition.W1SymbolicPublicMatrices.structuralE
AAT.AG.RelativeRepairComposition.W1SymbolicPublicMatrices.structuralPublicMatrix
AAT.AG.RelativeRepairComposition.W1SymbolicPublicStructure.bIndex
AAT.AG.RelativeRepairComposition.W1SymbolicPublicStructure.cIndex
AAT.AG.RelativeRepairComposition.W1SymbolicPublicStructure.eIndex
AAT.AG.RelativeRepairComposition.W1SymbolicPublicStructure.left_public
AAT.AG.RelativeRepairComposition.W1SymbolicPublicStructure.right_public
AAT.AG.RelativeRepairComposition.pathEdges.eq_def
ZMod.instField.congr_simp
```

</details>


### C25 selection — W2の元二辺経路・通常descentの不一致と厳密回復

```yaml
ledger_type: target_cycle_result
goal: G-130-aat-relative-repair-composition
cycle: 25
goal_blob_sha: 8da0fb4eb75d1cb5c37a9d4ddf5e03c18c0bb8a2
base_oid: 24da1df64adc8e6e04384b6f4b96fbb747d5061b
tracking_issue: 5132
report_path: research/reports/G-130-aat-relative-repair-composition.md
selection:
  proof_state_ref: "C24 PR5172/root5964429341/Issue5964441086; fixed GOAL W2/F/B/C; n1017 2.5; current accepted generic actual descent and strict generated APIs"
  proof_dag_predecessors: ["C1-C4 original supported actual repairs/full labels/unrestricted B", "C5-C7 independent finite strict C", "C11-C15 whole affine input/actual restriction/generated restoration", "C24 W1 full-affine milestone"]
  milestone: "Complete W2 on the original two-edge full-affine path: restricted global and local points, whole overlap BA, actual ordinary homotopy pullback discrete F3, mismatch and full strict generated recovery"
  proof_obligations:
    - "Construct original p→w→q typed finite geometry with exactly e1/e2, no faces/3cells, whole Aff(F3)→GL→1, identity references, full actual kernels/transports/core/comparisons. Construct original closed physical P={p,q}, U=e1/V=e2/W={w}, finite full cover, always empty/candidates both, and discharge all generic input conditions. Forbidden candidate fixing must not close P to include w."
    - "Define independent original full affine repairs and full actual gauge arrows for S empty globally, both original restricted patches and overlap. Prove global/U/V each equivalent to point, all overlap objects unique and its full label group exactly F3, giving whole BA. Preserve every original operation, every physical endpoint and all actual label restrictions."
    - "Use the actual full restriction functors to construct ordinary binary comma/homotopy pullback. Prove its equivalence to discrete F3 on seam labels and all compatible arrows, evaluate three isomorphism classes versus one global class and prove no equivalence. Connect accepted unrestricted B on this same original tower/P; restricted counterexample must remain the actual restriction diagram."
    - "Construct full original finite coefficient bases and all cell enumerations. Generate each local D/F, elimination, section and relation once from actual input before S, with full public candidate values and no private always edge. Instantiate independent strict generated cover for all S and show full object/arrow equivalence with the original actual repairs, including both inverses and every original edge/vertex label."
    - "Evaluate S empty strict generated recovery as point with exactly the original unchanged e1/e2 and zero full global label. Show strict shared vertex matching accounts for the lost ordinary seam freedom; preserve the original overlap and complete actual restriction data. No Nonempty-only replacement or objects-only gluing."
  exit_criteria:
    - "All original geometry/full affine/input/closed cover conditions and the global/U/V/overlap full groupoid comparisons are constructed from the original input."
    - "The actual ordinary restriction diagram has full comma equivalence to discrete F3 and the explicit 3-versus-1 non-equivalence; unrestricted B is connected with all required conditions discharged."
    - "Each actual local generator is independent of S and full strict C restores the same original actual objects/arrows, both inverses and all S; S empty evaluation recovers the global point."
    - "Current root single-body focused checks, every owned individual axiom result, exact hashes/registry/scans, fixed GOAL/criteria and standard review-pr/math-lean-review plus root acceptance and exact final CI all pass."
  selection_reason: "Closes one of the three remaining fixed witness obligations and directly validates why B remains unrestricted while C retains candidate coordinates and full shared labels."
  expected_result_type: proof-obligation-discharged
  lean_targets: ["W2AffineInput", "W2Regions", "W2ActualRepairs", "W2GaugeLabels", "W2RestrictionDiagram", "W2OrdinaryComma", "W2FiniteCoefficients", "W2LocalInterfaces", "W2StrictGeneratedCover"]
  risks: ["original endpoints and full affine operations", "candidate fixed-edge support does not fix w", "full BA arrows and actual restriction functors", "whole comma seam not a chosen object", "S-before-generator order", "full original object/arrow restoration", "unrestricted B input discharge"]
  unchecked: ["five W2 obligations not yet implemented", "whole-target W3/W5 and separate final completion audit remain"]
```

### Cycle 25 — 元二辺経路での通常descentの不一致と厳密回復

**到達点:** 固定W2の元経路p→w→qを全Aff(F3)の実操作として構成した。
物理的な固定頂点はp,qで、e1/e2の禁止はwを固定頂点へ追加しない。
空の許可集合で大域・U・Vの全groupoidはpoint、元の重なりの全groupoidはBF3となる。
同じ実制限関手の通常commaは全対象・全射について離散F3に同値であり、
同型類は大域の1個に対して3個である。大域修復との非同値を証明した。
候補全許可では同じ原表示・P・被覆に無制限Bを適用し、全実辺・全頂点ラベルを保持する。

各パッチのD/F・消去・section・relationは元の全核基底、全原セル列挙、
同じ実defectからSに先立って生成される。私有always辺は空で、全選択候補がpublicに残る。
任意Sの独立全実修復と厳密生成groupoidに、全対象・全射で相互逆な関手を構成した。
空Sの厳密生成はpointを回復し、復元e1/e2は元の参照実操作そのもの、全ラベルは零となる。
厳密な共有頂点一致は同じ元wの全核値を比較する。通常commaで残る別の重なり同型を、
厳密生成の対象へ追加しない。

このcycleはW2の五義務と四終了条件に対応する。全GOALのW3/W5と別の全target最終判定は残る。

| 固定W2の要求 | 今回の構成・全方向 | 一般定理への接続・使用 |
| --- | --- | --- |
| 原p,w,q、型付きe1/e2、全Aff(F3)→GL→1、原core/比較/全核・輸送 | W2AffineInput.geometry / originalTower / edgeNameEquiv、W2FiniteCoefficients.kernelCoordinate / kernel_inverse_value / original_linear | NativeAffine.towerと全実射影の核座標を、独立実修復とCの元微分へ使用 |
| P={p,q}、U/Vの元閉被覆、W={w}、全候補、E0空 | W2Regions.fixedRegion / internal_not_fixed / overlap_vertices / overlap_edges / regions_cover / indexed_cover / candidates_all / private_empty | 閉包・全被覆・固定面・全候補public条件を入力から放電 |
| S空で全大域/U/Vがpoint、重なり全BF3 | W2ActualRepairsの独立Repair/LocalRepairs・empty_unique / local_empty_unique、W2GaugeLabelsの全零/全F3両逆、W2EmptyGroupoidsの四全圏同値 | 全実操作と異なる全ラベルを保持したNativeAffine.groupoidEquivalence / W2SingletonCoordinates |
| 実制限から通常hpb、離散F3、3対1非同値 | W2RestrictionDiagram.leftRestriction / rightRestrictionの元実辺と全wラベル、W2OrdinarySeams.seam_restore / hom_iff / hom_unique / discreteEquivalence、W2OrdinaryClasses.ordinaryClassEquiv / ordinary_class_card / global_class_card / global_not_equivalent | 実commaの全対象と全compatible射を解析し、実isomorphism setoidの全商を評価 |
| 同じ原表示/Pの無制限B | W2UnrestrictedDescent.unrestricted_fixed / nativeEquivalence / actualEquivalence / left_choice / right_choice / left_label / right_label / seam_label | NativeDescent.equivalenceへ同じfixed_faces・regions_coverを渡し、原辺と全頂点の保持を評価 |
| Sに先立つ全局所生成と候補保持 | W2FiniteCoefficients.basesと全列挙、W2LocalInterfaces.privateMatrix / publicMatrix / elimination / generatedSection / relation / equationEquiv / nativeEquivalence、W2LocalMatrixValues.private_matrix_zero / public_matrix_zero / generated_section_zero / publicIndex | 実D/F/defectからFiniteNative生成を実行する構成。section法則・公開row独立性・row数の条件を放電 |
| 任意Sの全対象・全射・元値の厳密回復 | W2StrictGeneratedCover.actualObjectEquiv / nativeEquivalence / actualEquivalence / restore_extract / extract_restore / restore_operation、W2StrictInverseChecks.actual_forward_inverse / actual_inverse_forward | SupportedNativeEquation→StrictCoverRestoration→GeneratedCoverActionに全Affine対応を接続、関手合成そのものを両方向の恒等とする |
| 空Sでpoint・同じe1/e2・全零label、共有w | W2StrictGeneratedCover.emptyPointEquivalence / empty_restored_operation、W2StrictLabels.actualLabelEquiv / restore_original_vertex / extract_restored_label / shared_w_value / shared_w_coordinate / empty_label_zero / empty_arrow_label | 全許可ラベル対応と元頂点値の厳密一致を通して、同じ実大域修復・全射を回復 |

### C25 前提の出所と使用

| 前提 | 分類・入力からの放電 | 使用先 |
| --- | --- | --- |
| 元二辺経路、F3、全Aff操作、物理両端・全候補・空S | 本文由来: 固定GOAL W2/F、n1017 §2.5。W2AffineInput / W2Regionsで同じ型付き入力を構成 | 全実修復・実制限・全F3重なり・指定の非同値 |
| 強さ・全実可換核・核輸送・core/比較・線形性 | 一般A/B/Cではdirection-hypothesis、W2では放電済み: 全NativeAffine.tower、同じ実核のkernelCoordinate / kernel_inverse_value / original_linear | 全実修復/ラベル対応・元微分・生成 |
| 閉包・固定面整合・有限全被覆・候補分割 | 放電済み: W2Regions全fieldとcover、W2FiniteCoefficients.fixed_faces、W2Regions.private_empty | 原制限、無制限B、Sより前の独立C生成 |
| 全基底・完全原セル列挙・全有限体列挙 | 放電済み: W2FiniteCoefficients.bases / enumK / enumEdges / enumFaces / enumRegions | 同じ全実D/Fから有限消去・section・relationを生成 |
| point/BF3と離散F3の全対応、同型類の保存 | 放電済み: 独立実operation/label条件からの全両逆、実comma squareと全ラベルからのseam/hom解析、equivalenceClasses | 3対1非同値の具体的評価。既製のpoint/離散F3を実図式の定義へ入れない |
| section/公開relation/strict復元の完全性 | 放電済み: W2LocalInterfacesとW2StrictGeneratedCoverの実入力による一般構成、W2StrictInverseChecksの全関手恒等 | 全Sの同じ原実辺と全射への復元。結論certificateを受け取らない |
| 全ラベルの共有元頂点一致・空S零性 | 放電済み: W2StrictLabels.actualLabelEquiv / shared_w_value / empty_label_zero、独立実gauge条件によるglobal_empty_zero | 対象だけの貼り合わせを排し、全原頂点ラベルと全射を保持 |

```yaml
ledger_type: target_cycle_result
goal: G-130-aat-relative-repair-composition
cycle: 25
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "固定W2の同じ原二辺全Aff入力、実制限、point/BF3、通常comma離散F3と3対1非同値、同じ無制限B、独立全局所生成と全Sの厳密全対象/全射回復"
  exit_criteria_status:
    - "原全入力・閉被覆・point/BF3: Lean構成と個別公理確認"
    - "実commaの離散F3・3対1非同値・無制限B: Lean構成と個別公理確認"
    - "S前の独立生成・全S/全実辺/全頂点/全射の両逆・空S回復: Lean構成と個別公理確認"
    - "単一production本体・全所有宣言の個別公理・現行hash/registry/scan対応。標準PRレビューとroot受入はPRで判定"
  split_reason: none
  completion_candidate: no
  claim_mapping:
    source_labels: ["固定GOAL W2", "A/B/C/F", "n1017 §2.5"]
    undischarged_assumptions: []
    acceptance_point: "五義務・四終了条件の同じ到達点。標準レビューとroot受入を要する"
    port_status: unported
audits:
  premise_delta:
    discharged: ["上表の同じ実入力からのW2全条件・実制限・全comma解析・独立生成・全S厳密両逆"]
    remaining: ["全GOALの残W3/W5と別最終完了判定"]
  certificate_provenance:
    discharged: ["元全Aff入力・全実核・同じ実D/F/defect/全基底/全列挙からの生成", "独立実修復と全ラベルからのpoint/BF3/実comma解析"]
    unresolved: []
  proof_use:
    used: ["元型付き入力→全実修復/制限", "実制限square/全wラベル→全comma離散F3→3対1非同値", "元全入力/被覆→無制限B", "実D/F/全列挙→生成→全S厳密両逆", "全原頂点labels→厳密共有w/空S全零"]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  blocking_findings: []
  next_obligation: "W3、W5の固定実例・全指定判定と一般A–F接続、その後別全target最終四本レビュー"
```

### C25 productionと個別公理の一次検証対応

全16単一production本体を各々focused checkし、所有moduleの個別`#print axioms`は
全195宣言を被覆する。namespace監査は194宣言、namespace外の自動生成helperは1宣言。
本体検証とimport-onlyの個別公理確認は別の証拠である。各本体・個別公理のactual exitは0、
現行sourceとlogのSHA256を対応させる。標準公理はpropext、Classical.choice、Quot.sound。
単一fileコマンドは `cd research/lean && lake env lean -s4096 -D Elab.async=false -o .lake/build/lib/lean/<module path>.olean <source path>`。
Research全体、aggregate、全module/file loopのelaborationは実行しない。

| Production module | namespace宣言数 | source SHA256 | 本体log SHA256 |
| --- | ---: | --- | --- |
| W2ActualRepairs | 17 | `38aff6fe714c9c11bba9c427a7a2f53249be0f1796ac89aa3fabb46d21b50d25` | `4bbe7443c1249f3ed4b26a325acdf5fc0e7e691a886e20f5e95310765a1dc68b` |
| W2AffineInput | 19 | `2ceca95e274b46c1c1d24776e4addca7e4144954f7dea770dc52321c5040d643` | `5007843230ed6abca8a19c77d1862698154fe6042d861a9bd6f161eba2f5e275` |
| W2EmptyGroupoids | 9 | `6dbc544cbe30a08055e17e41d6ecf1dd8857bf723af6adfabcff7dbb2953f983` | `986ee8b35ed81c4afffec87fb5a5a5cbf99d0e9773f7c7a2ba7f8061fb6f1213` |
| W2FiniteCoefficients | 13 | `de0a2d58e988c2f00c548baf08511cfb0604cd22e86f906c42676d72a1dc170c` | `a4c101426f8ef52287a1f916db0eb878423e2a68f18881d2e7401a1269a308b7` |
| W2GaugeLabels | 26 | `2b0d1d8a40600a2efd7350bc8199cd296f6a8b2413cee2f5b1c000cdb25418af` | `cedfa906230e20732500c531a6e043482d55bedbad4bb671852181f9dac3317b` |
| W2LocalInterfaces | 10 | `9d3451eec84c0121b674e0521abae3436cf2a56d34cae1de1ef3ac8903e9cd2f` | `1d73cabf5502070b63bf7300bcdbf8e2268bdab2ccb8d1f1efadffdd0acb9c07` |
| W2LocalMatrixValues | 6 | `9a9f1e304c68d5845636cc4ab9810a080bc380c44d7defedec831224adac45ca` | `8ed8c8b361be802005f869fa7b42cbd6eca30f65aa8024f567addf34f6f633e2` |
| W2OrdinaryClasses | 10 | `074be98a5d74a1165a06017df1a3af981d8fafbbe7264fc845105138860506eb` | `fb9ef0aff96b4a3bea8f96e53a5a6f0dc65ecdc31729910d8fe842fcaf931676` |
| W2OrdinarySeams | 16 | `400dcd749313029a87a6be5c0cb21df052df0b7caf900b3118713904d2317af4` | `abd76104c926e1b8ca8b51c00bbf4b7181501a4029f5b6270bb708e0d10978b0` |
| W2Regions | 16 | `e1421d1fb5cec0c95ee396da2f49a90eab6a4a07a84a3f0f2afe014d21bfd114` | `a9ed6ae6d3b4fdc57926ffd8dbf6ab757391f271c8b955c7af40f3d2421c8552` |
| W2RestrictionDiagram | 15 | `e0f57a6eef147b001c42935debbb9429e0c9849fddf738c603507f471a12a748` | `8686bd0e091a469a1625fcb0e41f1fa71f714fbecabee31b4b100066b40c6a6b` |
| W2SingletonCoordinates | 3 | `816cdddd9d587142ea62d7e5ea184fd1e1d0ee169d4ffb50d1f63851bcb43a8d` | `ca818801ab343d5a11fe0614740fef7709e2dac4e8bc113cdab762a82681978f` |
| W2StrictGeneratedCover | 10 | `c00a17a3a6a682cda9e2f29b13429f4d421e33ca094cc4f370d57cad040ec93c` | `23af2900e9d5e14ba50dd7714a1a70063d5c8a23740669459b0ef8d7c5a9c77f` |
| W2StrictInverseChecks | 6 | `9cd66d8d3913b2663063fd8cd11e256630390f3ddafbc5c0ec5726380dc54233` | `3371d19383a31bbd8cbcd0b053830090726c32a983bb995d526484d773274280` |
| W2StrictLabels | 8 | `daa5d66867ffc90fb056ea44a40df1e7c2e551fffa37e41b775166bbf0610e21` | `df1f0614a9064712d3497e23111444e811fc08e61d9e5f4e918787b85dd96a53` |
| W2UnrestrictedDescent | 10 | `c1495afaa19b92639f05262d6ec148483709a08d0da0e7ce58b4feaa692702b8` | `867a53be8fc79ab8ced981916219f931d20e67bbb920296d0c93440922a19ef5` |

| 個別公理audit module群 | 所有宣言数 | audit SHA256 | log SHA256 |
| --- | ---: | --- | --- |
| W2AffineInput, W2Regions, W2ActualRepairs, W2GaugeLabels, W2SingletonCoordinates, W2EmptyGroupoids, W2RestrictionDiagram | 106 | `60540568c65f6c63bf7e524f7d27912e426b4fa6bb4258ccf1eb8834971696a6` | `96c69e367ff3bc75ef001521608ec5f88fc9b470ce3bdee4947b9a7ac8385880` |
| W2OrdinarySeams, W2OrdinaryClasses, W2FiniteCoefficients, W2LocalInterfaces, W2LocalMatrixValues, W2UnrestrictedDescent, W2StrictGeneratedCover, W2StrictInverseChecks, W2StrictLabels | 89 | `81c1aaa0a6599551afdcbc48c8ccb5dbdaa9c49fe8919da44176a21186c3a584` | `6c2b939f6a4ab44abaf0c240b24073ead64e2bf2b84a995ef0e832d3b4cef32d` |

<details>
<summary>C25 所有moduleで選択した全195宣言</summary>

```text
AAT.AG.RelativeRepairComposition.ClosedRegion.mk.congr_simp
AAT.AG.RelativeRepairComposition.W2ActualRepairs.ActualCategory
AAT.AG.RelativeRepairComposition.W2ActualRepairs.LocalCategory
AAT.AG.RelativeRepairComposition.W2ActualRepairs.LocalRepairs
AAT.AG.RelativeRepairComposition.W2ActualRepairs.NativeCategory
AAT.AG.RelativeRepairComposition.W2ActualRepairs.RealRepairs
AAT.AG.RelativeRepairComposition.W2ActualRepairs.actualRestriction
AAT.AG.RelativeRepairComposition.W2ActualRepairs.emptyObjectEquiv
AAT.AG.RelativeRepairComposition.W2ActualRepairs.empty_operation
AAT.AG.RelativeRepairComposition.W2ActualRepairs.empty_unique
AAT.AG.RelativeRepairComposition.W2ActualRepairs.localEmptyObjectEquiv
AAT.AG.RelativeRepairComposition.W2ActualRepairs.localReferenceRepair
AAT.AG.RelativeRepairComposition.W2ActualRepairs.local_empty_operation
AAT.AG.RelativeRepairComposition.W2ActualRepairs.local_empty_unique
AAT.AG.RelativeRepairComposition.W2ActualRepairs.local_fixed_all
AAT.AG.RelativeRepairComposition.W2ActualRepairs.referenceRepair
AAT.AG.RelativeRepairComposition.W2ActualRepairs.restriction_operation
AAT.AG.RelativeRepairComposition.W2ActualRepairs.wholeAffineEquivalence
AAT.AG.RelativeRepairComposition.W2AffineInput.Op
AAT.AG.RelativeRepairComposition.W2AffineInput.comparison
AAT.AG.RelativeRepairComposition.W2AffineInput.edgeDecidableEq
AAT.AG.RelativeRepairComposition.W2AffineInput.edgeNameEquiv
AAT.AG.RelativeRepairComposition.W2AffineInput.edgeOne
AAT.AG.RelativeRepairComposition.W2AffineInput.edgeSource
AAT.AG.RelativeRepairComposition.W2AffineInput.edgeTarget
AAT.AG.RelativeRepairComposition.W2AffineInput.edgeTwo
AAT.AG.RelativeRepairComposition.W2AffineInput.faceDecidableEq
AAT.AG.RelativeRepairComposition.W2AffineInput.geometry
AAT.AG.RelativeRepairComposition.W2AffineInput.linear_faces
AAT.AG.RelativeRepairComposition.W2AffineInput.name
AAT.AG.RelativeRepairComposition.W2AffineInput.name_edge
AAT.AG.RelativeRepairComposition.W2AffineInput.originalTower
AAT.AG.RelativeRepairComposition.W2AffineInput.primeThree
AAT.AG.RelativeRepairComposition.W2AffineInput.reference
AAT.AG.RelativeRepairComposition.W2AffineInput.vertexP
AAT.AG.RelativeRepairComposition.W2AffineInput.vertexQ
AAT.AG.RelativeRepairComposition.W2AffineInput.vertexW
AAT.AG.RelativeRepairComposition.W2EmptyGroupoids.BA
AAT.AG.RelativeRepairComposition.W2EmptyGroupoids.Point
AAT.AG.RelativeRepairComposition.W2EmptyGroupoids.globalPointEquivalence
AAT.AG.RelativeRepairComposition.W2EmptyGroupoids.leftLabelEquiv
AAT.AG.RelativeRepairComposition.W2EmptyGroupoids.leftPointEquivalence
AAT.AG.RelativeRepairComposition.W2EmptyGroupoids.overlapBAEquivalence
AAT.AG.RelativeRepairComposition.W2EmptyGroupoids.overlap_forward_label
AAT.AG.RelativeRepairComposition.W2EmptyGroupoids.rightLabelEquiv
AAT.AG.RelativeRepairComposition.W2EmptyGroupoids.rightPointEquivalence
AAT.AG.RelativeRepairComposition.W2FiniteCoefficients.actualDefect
AAT.AG.RelativeRepairComposition.W2FiniteCoefficients.actual_defect_zero
AAT.AG.RelativeRepairComposition.W2FiniteCoefficients.bases
AAT.AG.RelativeRepairComposition.W2FiniteCoefficients.basisIndex
AAT.AG.RelativeRepairComposition.W2FiniteCoefficients.basis_value
AAT.AG.RelativeRepairComposition.W2FiniteCoefficients.enumEdges
AAT.AG.RelativeRepairComposition.W2FiniteCoefficients.enumFaces
AAT.AG.RelativeRepairComposition.W2FiniteCoefficients.enumK
AAT.AG.RelativeRepairComposition.W2FiniteCoefficients.enumRegions
AAT.AG.RelativeRepairComposition.W2FiniteCoefficients.fixed_faces
AAT.AG.RelativeRepairComposition.W2FiniteCoefficients.kernelCoordinate
AAT.AG.RelativeRepairComposition.W2FiniteCoefficients.kernel_inverse_value
AAT.AG.RelativeRepairComposition.W2FiniteCoefficients.original_linear
AAT.AG.RelativeRepairComposition.W2GaugeLabels.GlobalLabels
AAT.AG.RelativeRepairComposition.W2GaugeLabels.LocalLabels
AAT.AG.RelativeRepairComposition.W2GaugeLabels.globalEmptyLabelEquiv
AAT.AG.RelativeRepairComposition.W2GaugeLabels.global_edge
AAT.AG.RelativeRepairComposition.W2GaugeLabels.global_empty_w
AAT.AG.RelativeRepairComposition.W2GaugeLabels.global_empty_zero
AAT.AG.RelativeRepairComposition.W2GaugeLabels.global_fixed
AAT.AG.RelativeRepairComposition.W2GaugeLabels.leftEdge
AAT.AG.RelativeRepairComposition.W2GaugeLabels.leftP
AAT.AG.RelativeRepairComposition.W2GaugeLabels.leftW
AAT.AG.RelativeRepairComposition.W2GaugeLabels.left_empty_w
AAT.AG.RelativeRepairComposition.W2GaugeLabels.left_empty_zero
AAT.AG.RelativeRepairComposition.W2GaugeLabels.local_edge
AAT.AG.RelativeRepairComposition.W2GaugeLabels.local_fixed
AAT.AG.RelativeRepairComposition.W2GaugeLabels.overlapLabel
AAT.AG.RelativeRepairComposition.W2GaugeLabels.overlapLabelEquiv
AAT.AG.RelativeRepairComposition.W2GaugeLabels.overlapW
AAT.AG.RelativeRepairComposition.W2GaugeLabels.overlap_label_value
AAT.AG.RelativeRepairComposition.W2GaugeLabels.overlap_no_edge
AAT.AG.RelativeRepairComposition.W2GaugeLabels.overlap_not_fixed
AAT.AG.RelativeRepairComposition.W2GaugeLabels.overlap_vertex
AAT.AG.RelativeRepairComposition.W2GaugeLabels.rightEdge
AAT.AG.RelativeRepairComposition.W2GaugeLabels.rightQ
AAT.AG.RelativeRepairComposition.W2GaugeLabels.rightW
AAT.AG.RelativeRepairComposition.W2GaugeLabels.right_empty_w
AAT.AG.RelativeRepairComposition.W2GaugeLabels.right_empty_zero
AAT.AG.RelativeRepairComposition.W2LocalInterfaces.elimination
AAT.AG.RelativeRepairComposition.W2LocalInterfaces.equationEquiv
AAT.AG.RelativeRepairComposition.W2LocalInterfaces.generatedSection
AAT.AG.RelativeRepairComposition.W2LocalInterfaces.nativeEquivalence
AAT.AG.RelativeRepairComposition.W2LocalInterfaces.privateMatrix
AAT.AG.RelativeRepairComposition.W2LocalInterfaces.publicMatrix
AAT.AG.RelativeRepairComposition.W2LocalInterfaces.public_row_count
AAT.AG.RelativeRepairComposition.W2LocalInterfaces.public_rows_independent
AAT.AG.RelativeRepairComposition.W2LocalInterfaces.relation
AAT.AG.RelativeRepairComposition.W2LocalInterfaces.section_regular
AAT.AG.RelativeRepairComposition.W2LocalMatrixValues.generated_section_zero
AAT.AG.RelativeRepairComposition.W2LocalMatrixValues.no_private_coordinate
AAT.AG.RelativeRepairComposition.W2LocalMatrixValues.private_matrix_zero
AAT.AG.RelativeRepairComposition.W2LocalMatrixValues.publicIndex
AAT.AG.RelativeRepairComposition.W2LocalMatrixValues.public_matrix_zero
AAT.AG.RelativeRepairComposition.W2LocalMatrixValues.public_original_edge
AAT.AG.RelativeRepairComposition.W2OrdinaryClasses.equivalenceClasses
AAT.AG.RelativeRepairComposition.W2OrdinaryClasses.globalClassEquiv
AAT.AG.RelativeRepairComposition.W2OrdinaryClasses.globalObject
AAT.AG.RelativeRepairComposition.W2OrdinaryClasses.global_class_card
AAT.AG.RelativeRepairComposition.W2OrdinaryClasses.global_not_equivalent
AAT.AG.RelativeRepairComposition.W2OrdinaryClasses.global_object_eq
AAT.AG.RelativeRepairComposition.W2OrdinaryClasses.ordinaryClassEquiv
AAT.AG.RelativeRepairComposition.W2OrdinaryClasses.ordinary_class_card
AAT.AG.RelativeRepairComposition.W2OrdinaryClasses.ordinary_object_card
AAT.AG.RelativeRepairComposition.W2OrdinaryClasses.zero_one_not_isomorphic
AAT.AG.RelativeRepairComposition.W2OrdinarySeams.discreteEquivalence
AAT.AG.RelativeRepairComposition.W2OrdinarySeams.hom_iff
AAT.AG.RelativeRepairComposition.W2OrdinarySeams.hom_unique
AAT.AG.RelativeRepairComposition.W2OrdinarySeams.leftObject
AAT.AG.RelativeRepairComposition.W2OrdinarySeams.left_map_identity
AAT.AG.RelativeRepairComposition.W2OrdinarySeams.left_object_eq
AAT.AG.RelativeRepairComposition.W2OrdinarySeams.objectEquiv
AAT.AG.RelativeRepairComposition.W2OrdinarySeams.rightObject
AAT.AG.RelativeRepairComposition.W2OrdinarySeams.right_map_identity
AAT.AG.RelativeRepairComposition.W2OrdinarySeams.right_object_eq
AAT.AG.RelativeRepairComposition.W2OrdinarySeams.seam
AAT.AG.RelativeRepairComposition.W2OrdinarySeams.seamFunctor
AAT.AG.RelativeRepairComposition.W2OrdinarySeams.seamObject
AAT.AG.RelativeRepairComposition.W2OrdinarySeams.seam_equal_of_hom
AAT.AG.RelativeRepairComposition.W2OrdinarySeams.seam_object
AAT.AG.RelativeRepairComposition.W2OrdinarySeams.seam_restore
AAT.AG.RelativeRepairComposition.W2Regions.candidates
AAT.AG.RelativeRepairComposition.W2Regions.candidates_all
AAT.AG.RelativeRepairComposition.W2Regions.candidates_outside
AAT.AG.RelativeRepairComposition.W2Regions.fixedEdges
AAT.AG.RelativeRepairComposition.W2Regions.fixedRegion
AAT.AG.RelativeRepairComposition.W2Regions.fixed_empty
AAT.AG.RelativeRepairComposition.W2Regions.indexed_cover
AAT.AG.RelativeRepairComposition.W2Regions.internal_not_fixed
AAT.AG.RelativeRepairComposition.W2Regions.leftRegion
AAT.AG.RelativeRepairComposition.W2Regions.overlap
AAT.AG.RelativeRepairComposition.W2Regions.overlap_edges
AAT.AG.RelativeRepairComposition.W2Regions.overlap_vertices
AAT.AG.RelativeRepairComposition.W2Regions.private_empty
AAT.AG.RelativeRepairComposition.W2Regions.regions
AAT.AG.RelativeRepairComposition.W2Regions.regions_cover
AAT.AG.RelativeRepairComposition.W2Regions.rightRegion
AAT.AG.RelativeRepairComposition.W2RestrictionDiagram.Ordinary
AAT.AG.RelativeRepairComposition.W2RestrictionDiagram.leftAction
AAT.AG.RelativeRepairComposition.W2RestrictionDiagram.leftLabelRestriction
AAT.AG.RelativeRepairComposition.W2RestrictionDiagram.leftRestriction
AAT.AG.RelativeRepairComposition.W2RestrictionDiagram.left_label_value
AAT.AG.RelativeRepairComposition.W2RestrictionDiagram.left_map_value
AAT.AG.RelativeRepairComposition.W2RestrictionDiagram.left_operation_restriction
AAT.AG.RelativeRepairComposition.W2RestrictionDiagram.ordinary_is_groupoid
AAT.AG.RelativeRepairComposition.W2RestrictionDiagram.overlapAction
AAT.AG.RelativeRepairComposition.W2RestrictionDiagram.rightAction
AAT.AG.RelativeRepairComposition.W2RestrictionDiagram.rightLabelRestriction
AAT.AG.RelativeRepairComposition.W2RestrictionDiagram.rightRestriction
AAT.AG.RelativeRepairComposition.W2RestrictionDiagram.right_label_value
AAT.AG.RelativeRepairComposition.W2RestrictionDiagram.right_map_value
AAT.AG.RelativeRepairComposition.W2RestrictionDiagram.right_operation_restriction
AAT.AG.RelativeRepairComposition.W2SingletonCoordinates.equivalence
AAT.AG.RelativeRepairComposition.W2SingletonCoordinates.forward_label
AAT.AG.RelativeRepairComposition.W2SingletonCoordinates.labelFunctor
AAT.AG.RelativeRepairComposition.W2StrictGeneratedCover.Groupoid
AAT.AG.RelativeRepairComposition.W2StrictGeneratedCover.Objects
AAT.AG.RelativeRepairComposition.W2StrictGeneratedCover.actualEquivalence
AAT.AG.RelativeRepairComposition.W2StrictGeneratedCover.actualObjectEquiv
AAT.AG.RelativeRepairComposition.W2StrictGeneratedCover.emptyPointEquivalence
AAT.AG.RelativeRepairComposition.W2StrictGeneratedCover.empty_restored_operation
AAT.AG.RelativeRepairComposition.W2StrictGeneratedCover.extract_restore
AAT.AG.RelativeRepairComposition.W2StrictGeneratedCover.nativeEquivalence
AAT.AG.RelativeRepairComposition.W2StrictGeneratedCover.restore_extract
AAT.AG.RelativeRepairComposition.W2StrictGeneratedCover.restore_operation
AAT.AG.RelativeRepairComposition.W2StrictInverseChecks.actual_forward_inverse
AAT.AG.RelativeRepairComposition.W2StrictInverseChecks.actual_inverse_forward
AAT.AG.RelativeRepairComposition.W2StrictInverseChecks.native_forward_inverse
AAT.AG.RelativeRepairComposition.W2StrictInverseChecks.native_inverse_forward
AAT.AG.RelativeRepairComposition.W2StrictInverseChecks.trans_forward_inverse
AAT.AG.RelativeRepairComposition.W2StrictInverseChecks.trans_inverse_forward
AAT.AG.RelativeRepairComposition.W2StrictLabels.Labels
AAT.AG.RelativeRepairComposition.W2StrictLabels.actualLabelEquiv
AAT.AG.RelativeRepairComposition.W2StrictLabels.empty_arrow_label
AAT.AG.RelativeRepairComposition.W2StrictLabels.empty_label_zero
AAT.AG.RelativeRepairComposition.W2StrictLabels.extract_restored_label
AAT.AG.RelativeRepairComposition.W2StrictLabels.restore_original_vertex
AAT.AG.RelativeRepairComposition.W2StrictLabels.shared_w_coordinate
AAT.AG.RelativeRepairComposition.W2StrictLabels.shared_w_value
AAT.AG.RelativeRepairComposition.W2UnrestrictedDescent.Descent
AAT.AG.RelativeRepairComposition.W2UnrestrictedDescent.actualEquivalence
AAT.AG.RelativeRepairComposition.W2UnrestrictedDescent.descent_is_groupoid
AAT.AG.RelativeRepairComposition.W2UnrestrictedDescent.left_choice
AAT.AG.RelativeRepairComposition.W2UnrestrictedDescent.left_label
AAT.AG.RelativeRepairComposition.W2UnrestrictedDescent.nativeEquivalence
AAT.AG.RelativeRepairComposition.W2UnrestrictedDescent.right_choice
AAT.AG.RelativeRepairComposition.W2UnrestrictedDescent.right_label
AAT.AG.RelativeRepairComposition.W2UnrestrictedDescent.seam_label
AAT.AG.RelativeRepairComposition.W2UnrestrictedDescent.unrestricted_fixed
```

</details>


### C26 selection — W3の同じ全修復span・同型類と自己同型・元descentの比較

```yaml
ledger_type: target_cycle_result
goal: G-130-aat-relative-repair-composition
cycle: 26
goal_blob_sha: 8da0fb4eb75d1cb5c37a9d4ddf5e03c18c0bb8a2
base_oid: 15e0169e3a6f2c4487dbf265c06c235e1b2a6dac
tracking_issue: 5132
report_path: research/reports/G-130-aat-relative-repair-composition.md
selection:
  proof_state_ref: "C25 PR5173/root5965160198/Issue5965170441; fixed GOAL W3/A/B/C/F; n1017 §5.6; current accepted full-affine/kernel/actual groupoid/descent/generated strict APIs"
  proof_dag_predecessors: ["C1-C7 full supported actual repairs/labels/classification/B", "C10-C11 finite generated interfaces and strict whole restoration", "C14 full native affine input/kernel/operation/label correspondence", "C25 actual ordinary comma/full quotient/singleton label helper and exact composite inverse helper"]
  milestone: "固定W3の元二辺閉路で、shearと恒等の同じ全実修復spanに対する全同型類・自己同型を分類し、π0先行と候補禁止後の通常descentの不一致、同じ独立生成strict Cの全回復を証明する。"
  proof_obligations:
    - "元 s,t と逆向き e:s→t,f:t→s、面/3-cell 空、P空、E0空、両辺候補、A=F3²、全 Aff(A)→GL(A)→1 を保持する。f の実線形成分は shear または恒等、e は恒等。同じ full categorical kernel/transport を構成し、全条件を入力から放電する。"
    - "全 independent actual repairs を全 (u,v)∈A² と両逆対応させ、全81組を保持する。全 actual gauge labels を全 (bs,bt)∈A² と対応させ、実操作への作用を (u+bt−bs,v+bs−Tbt)、元 loop を w=v+Tu、その作用を w+(I−T)bs と評価する。shear と恒等で同じ solution span を用いる。"
    - "元 actual category の全 isomorphism quotient を shear の F3、恒等の A と両逆対応させ、類数3/9を求める。任意 actual repair の全 Aut を shear の F3、恒等の A と群同型で対応させ、各 stabilizer 3/9と元全labelsを保持する。全81操作と全射の範囲を保持する。"
    - "元 U={e,s,t},V={f,s,t},W={s,t} の全閉被覆と実制限関手を構成する。無制限局所類各1、全 Aut A、Wの全 Aut A² と元 (s,t) の境界写像 b↦(b,b)、b↦(Tb,b) を評価する。無制限 B の同値を同じ actual tower/cover へ接続し、先に局所 π0 を取ると一点になり、大域3/9類とAutを失うことを示す。"
    - "S空では独立 actual global/local object 各1、global Aut は F3/A、local全AutはA。元 restricted restriction comma 全体が3/9類と各F3/AのAutを持つことを全対象/全射から導き、restricted global1類との非同値を示す。restricted local inclusion の全圏同値・Comma.map を用いる場合も元制限との自然な可換性と全ラベルを保持する。"
    - "全実核basesと完全列挙から各局所 D/F/elimination/section/relation を Sより前に一度生成する。任意Sで independent actual全体とgenerated strict全体の関手両逆を接続し、S空の唯一対象と full Aut F3/A、元e/f操作・全元頂点labels・厳密共有一致を回復する。"
  exit_criteria:
    - "同じ全affine入力・81全操作/全labels・作用/閉路評価・full quotient3/9・全Aut F3/Aが放電されている。"
    - "元局所制限とboundary map、π0先行の情報損失、無制限Bとrestricted通常descent不一致を全対象/全射で証明している。"
    - "全有限構成がS前で、任意Sのstrict C両逆とS空の同じ元値/全Aut回復を接続している。"
    - "必要なcurrent body/owned axiom/hash/registry/common scan、固定GOAL/適用基準、標準独立四査読とroot受理、exact-final-head CIが揃う。"
  selection_reason: "残る固定witnessの一つを閉じ、同じ全実解spanでも閉路輸送が類と全Autを変え、元制限ではfull arrows/strict共有値が必要なことを直接検査する。"
  expected_result_type: proof-obligation-discharged
  lean_targets: ["W3LinearAction", "W3AffineInput", "W3Regions", "W3ActualRepairs", "W3GaugeAction", "W3Classes", "W3Automorphisms", "W3LocalRestrictions", "W3OrdinaryDescent", "W3FiniteCoefficients", "W3LocalInterfaces", "W3StrictGeneratedCover"]
  risks: ["全Aff(F3²)と全categorical kernel", "同じ81実修復span/全gauge labels", "原loopの実合成とshear非恒等", "全isomorphism quotientと全Aut", "元(s,t)境界写像と全comma square", "π0先行と候補禁止の別条件", "S前の有限生成と全関手両逆"]
  unchecked: ["六W3義務は実装前", "W5と累積全target completion gateは残る"]
```

### C26 W3: 同じ全実修復spanと閉路輸送、全射を保つ局所合成

元の二頂点s,t、逆向きのe:s→t、f:t→s、空の面と3-cell、P空、E0空、
両辺候補、A=F3²、全Aff(A)→GL(A)→1を保持する。eの参照実操作は恒等、
fはTであり、Tをshear (x,y)↦(x+y,y)と恒等の両方で評価する。
独立に定義した全実修復の元実操作を(u,v)∈A²と両逆に対応させる。
両入力とも全81修復、全81頂点ラベル(bs,bt)を持つ。同じ元閉路e,fの合成は
Tx+w、w=v+Tuであり、実ゲージは(u+bt−bs,v+bs−Tbt)、閉路は
w+(I−T)bsへ変わる。元全圏の同型類はshearでF3、恒等でAと両逆に対応し、
類数は3/9となる。任意の実修復の全Autをker(I−T)と群同型に対応させ、
shearでF3、恒等でA、全原頂点ラベルの定数値を回復する。

元のU={e,s,t}、V={f,s,t}、W={s,t}を全閉被覆として用いる。
無制限の独立局所全圏はU/VでBA、WでBA²と同値となる。
各同型類は一点だが、全局所自己同型はA/A/A²を保持する。
元の実制限の全頂点値を評価し、参照対象の境界写像はb↦(b,b)、b↦(Tb,b)となる。
同じ元tower/coverを無制限のNativeDescent.equivalenceへ接続し、Bの全対象・全射を得る。
実制限から誘導した全isomorphism quotientの写像で局所π₀のpullbackを構成すると一点になる。
この一点の離散圏では大域の3/9同型類と各3/9自己同型を失う。

S空では独立の大域/U/V/W実操作は各一つになる。全大域AutはF3/A、
全局所AutはA/A/A²であり、元実制限の通常commaは3/9同型類と各F3/AのAutを持つ。
通常commaの全81対象と全squareを直接解析し、無制限の大域全圏から通常comma全体へ
充満・忠実・本質的全射な関手を構成する。全射の元bs,btは元U/Vラベル−bs,−btへ対応する。
この通常commaはS空の大域一同型類と同値にならない。

全実核の二次元基底、元typed cell、F3と被覆の完全列挙から、局所D/F、消去、section、
公開relationをSに先立って一度生成する。同じ独立実修復から生成strict全圏への関手を
任意Sで構成し、全対象・全射の関手合成を両方向で恒等と証明する。
元e/f操作と全原頂点ラベルを復元し、共有s,tで実核値と全座標が厳密に一致する。
S空のstrict全対象は一つ、全AutはF3/Aとなり、同じ大域の値と射を回復する。

| 固定W3の要求 | 構成・全方向 | 一般定理への接続と使用 |
| --- | --- | --- |
| 元二辺閉路、同じ全Aff入力・全核・輸送 | W3LinearAction.shear / shear_ne_one、W3AffineInput.geometry / originalTower / reference_e / reference_f、W3FiniteCoefficients.kernelCoordinate / kernel_inverse_value / original_linear | NativeAffine.towerの全実射影と可換核、原型付き操作を実修復と元D/Fへ使用 |
| P空、全候補、元全閉被覆 | W3Regions.fixedRegion / candidates_all / regions_cover / indexed_cover / overlap_vertices / overlap_edges / private_empty | 全条件を入力から放電し、同じ元制限と有限生成へ渡す |
| 同じ81実修復と81全ラベル・閉路評価 | W3ActualRepairs.actualParametersEquiv / unrestrictedParametersEquiv / unrestricted_repair_card、W3GaugeLabels.unrestrictedLabelEquiv、W3AuthoredOperations.loop_apply、W3GaugeAction.gauge_first / gauge_second / gauge_loop | 独立NativeAffine.Repairと全許可ゲージを用い、全ベクトル上の実Affine操作を比較 |
| 全同型類3/9と任意対象の全Aut3/9 | W3LoopIsomorphisms.isomorphic_iff_loop / shear_isomorphic_iff / identity_isomorphic_iff、W3Classes.shearClassEquiv / identityClassEquiv、W3Automorphisms.autFixedEquiv / autFixedEquiv_label / shearAutEquiv / identityAutEquiv | 元isIsomorphicSetoidの全商・元全ゲージ射から両逆と群演算を構成 |
| 無制限局所一類、全Aut A/A/A²、原境界 | W3UnrestrictedLocalEquivalences.leftEquivalence / rightEquivalence、W3UnrestrictedLocalClasses.overlapEquivalence / leftClassEquiv / rightClassEquiv / overlapClassEquiv / leftAutEquiv / rightAutEquiv / overlapAutEquiv、W3UnrestrictedRestrictions.left_map_value / right_map_value | 任意独立局所repairへの実ゲージを構成し、全元頂点ラベルを保持 |
| 同じ無制限Bとπ₀先行の情報損失 | W3UnrestrictedDescent.actualEquivalence / left_choice / right_choice / left_label / right_label、W3Pi0Loss.leftClassRestriction / rightClassRestriction / pullbackEquiv / global_class_count_lost / global_aut_count_lost | NativeDescent.equivalenceへ同じfixed_facesとregions_cover、π₀は同じ実制限からQuotient.mapで誘導 |
| S空の全実操作一対象・大域全Aut F3/A・局所全Aut A | W3ActualRepairs.emptyObjectEquiv、W3LocalRepairs.localEmptyObjectEquiv、W3EmptyGroupoids.globalEquivalence / leftEquivalence / rightEquivalence / overlapEquivalence、W3LocalLabels.left_relation / right_relation | 独立全修復・全許可ラベルの両逆からfull singleton groupoidを導く |
| 元restricted制限の通常comma全体3/9類と各F3/A Aut、1類との非同値 | W3RestrictionDiagram.leftRestriction / rightRestriction / left_original_value / right_original_value、W3OrdinarySeams.objectEquiv / square_iff、W3OrdinaryComparison.comparisonEquivalence / comparison_source / comparison_target、W3OrdinaryClasses.restricted_global_not_equivalent | 元全seamと全comma squareから全関手を構成。W2OrdinaryClasses.equivalenceClassesで全商を移す |
| S前の独立全生成、全Sのstrict両逆 | W3FiniteCoefficients.bases / enumK / enumEdges / enumFaces / enumRegions、W3LocalInterfaces.equationEquiv / nativeEquivalence、W3StrictGeneratedCover.actualEquivalence、W3StrictInverseChecks.actual_forward_inverse / actual_inverse_forward | 同じ全実D/F/defectからFiniteNative→SupportedNativeEquation→StrictCoverRestoration→GeneratedCoverActionへ接続 |
| 空Sの同じ元操作・全Aut回復、s,tの厳密共有値 | W3StrictGeneratedCover.empty_restored_operation、W3StrictLabels.restore_original_vertex / shared_s_value / shared_t_value / forward_patch_value / actual_forward_label、W3StrictConsequences.actual_inverse_label / emptyObjectEquiv / autFixedEquiv / shearAutEquiv / identityAutEquiv | 全元labelsの両逆を実関手のmapへ接続し、全S・任意strict対象のAutを分類 |

### C26 前提の出所と使用

| 前提 | 分類と入力からの放電 | 使用先 |
| --- | --- | --- |
| 元s,t,e/f、F3²、全Aff、P空・全候補、Tの二入力 | 本文由来: 固定GOAL W3/F、n1017 §5.6。W3LinearAction / W3AffineInput / W3Regionsで構成 | 同じ全実操作span、閉路の元輸送、非恒等shear、指定類とAut |
| 全実核・強さ・可換性・原core/比較・核輸送/線形性 | 一般A/B/Cではdirection-hypothesis、W3では放電済み: 全NativeAffine.towerとkernelCoordinate / kernel_inverse_value / original_linear | 実修復/全ラベル対応、元微分・全基底・有限生成 |
| 閉包・全被覆・固定面整合・候補分割 | 放電済み: W3Regionsの各全fieldと全cover、W3FiniteCoefficients.fixed_faces / W3Regions.private_empty | 原実制限、無制限B、S前の局所生成 |
| 完全な修復/ラベル/全局所射/全comma square | 放電済み: independent Repairと元gauge条件から全座標を両逆構成。W3ActualArrows / W3LocalGauge / W3OrdinarySeams / W3OrdinaryComparison | 全商と全Aut、元制限の情報損失とrestricted非同値 |
| 完全有限基底・原セルと係数と被覆の全列挙 | 放電済み: W3FiniteCoefficientsの二次元全実核と各Enumeration | 同じ全D/Fからelimination/section/relationをS前に生成 |
| strict section/relation・復元の完全性 | 放電済み: W3LocalInterfaces、W3StrictGeneratedCover / W3StrictInverseChecksの実入力による一般構成と全関手恒等 | 全S・全対象・全射の元操作/全頂点値の復元 |
| 全原頂点の厳密共有・空S全ラベル | 放電済み: W3StrictLabelsの全許可ラベル両逆とshared_s/t、W3StrictConsequencesの全Aut同型 | 同じ元s,tの実核値を比較し、大域F3/Aを回復 |

```yaml
ledger_type: target_cycle_result
goal: G-130-aat-relative-repair-composition
cycle: 26
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "六固定W3義務: 元全入力、同じ81実修復/全ラベルと実閉路作用、全商3/9と全Aut、原局所制限/無制限B/π0損失、空S通常commaの不一致、S前生成/全Sstrict両逆"
  exit_criteria_status:
    - "同じ全入力・81全修復/ラベル・閉路評価・全商/全Aut: Lean構成と個別公理確認"
    - "原全制限/境界・無制限B・π0損失・restricted通常comma非同値: Lean構成と個別公理確認"
    - "S前独立生成・全Sstrict全関手両逆・原全操作/全labels/空S回復: Lean構成と個別公理確認"
    - "現行単一production本体/全所有宣言/registry/hash/common scan。標準PR査読・root受入・exact-head CIはPRで判定"
  split_reason: none
  completion_candidate: no
  claim_mapping:
    source_labels: ["固定GOAL W3", "A/B/C/F", "n1017 §5.6"]
    undischarged_assumptions: []
    acceptance_point: "六義務と四終了条件。標準レビューとroot受入を要する"
    port_status: unported
audits:
  premise_delta:
    discharged: ["上表の同じ全実入力・全修復/全射・全局所制限・独立生成と全S両逆"]
    remaining: ["W5と別の累積全target最終完了判定"]
  certificate_provenance:
    discharged: ["元全Aff/全実核と同じD/F/defect/全基底/全列挙から生成", "独立全実修復・全gauge条件から商/Aut/全comma/全局所圏を構成"]
    unresolved: []
  proof_use:
    used: ["元全操作/ラベル→実閉路作用→全商/全Aut", "元全局所制限→π0損失とrestricted全comma非同値", "同じ全tower/cover→無制限B", "同じD/F/defect/全列挙→S前生成→全Sstrict関手両逆", "全原s,tラベル→厳密共有値と空S全Aut回復"]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  blocking_findings: []
  next_obligation: "固定W5の全指定判定と一般A–F接続、その後別の累積全target最終四本査読"
```

### C26 productionと個別公理の一次検証対応

全33単一production本体のactual exitは0、error/warningは各0。
namespaceの352宣言に対し、所有moduleから選択した個別 `#print axioms` は全354宣言を被覆する。
namespace外の自動生成helperはClosedRegion.mk.congr_simpとZMod.instField.congr_simpの二つである。
本体検証とimport-onlyの個別公理確認は別の証拠で、各source/logの現行SHA256を対応させる。
標準公理はpropext、Classical.choice、Quot.sound。
単一fileコマンドは `cd research/lean && lake env lean -s4096 -D Elab.async=false -o .lake/build/lib/lean/<module path>.olean <source path>`。
Research全体、aggregate、全module/file loopのelaborationは実行しない。

| Production module | namespace宣言数 | source SHA256 | 本体log SHA256 |
| --- | ---: | --- | --- |
| W3ActualArrows | 6 | `8146a40b9482c1831d8bbc5fdcbc1748a8361544b5ddc5cb62a418f3c0dfb72f` | `22f03f3974bf7614bd7b3b371ec25f50e094a24bef81f8d7cbc2380979e4812b` |
| W3ActualRepairs | 20 | `473f07d2de79b853331b272509771dda0d2bfd3ef2634e894b68e6a856e433b0` | `8f9b99f590b492e81dbeae811a38cbd21e82703ad843387468cfa8fb4f59f44c` |
| W3AffineInput | 21 | `a2b2af9f1cbc7272818f8f51d101287e602d9bcadecaef20c161a56711693fe4` | `13fa2cab99987ad5b14cb52a0036f4f9ea6779b4b99664ce64af418d688767dd` |
| W3AuthoredOperations | 11 | `291602b7cd4b688fd7d29eaa194df1c592f17adb2da7c1720d0bf1c622f9ebc8` | `9d71a34e609ac29ab8f1475c8df6b657e32ef0f27e64983fe6178b38e9e1e9ac` |
| W3Automorphisms | 12 | `c26d4bc0734eda297795ebe156a54195f9a32f447881bba85e280805c4c8ef9c` | `fcd39516e596ef080a29f8faac722635cef6b2bec278664f88f4adb254d349ac` |
| W3Classes | 12 | `f2667dbe8332391a338e59f36b791178a7db9abe7b0e0e208d53d6c3312d451e` | `39dad4548421a6d4de8866ee29325547381636ba43a09e8fc4440d9e1d22fb0a` |
| W3EmptyGroupoids | 14 | `89da0dfa0de51947f752d7b3096434fcb1d6e142d56de3c76339b0b6a3410e6d` | `847a556fde7fb349dc82f256e585dcd906bbc628ee4803ec98121d7c553f559c` |
| W3FiniteCoefficients | 13 | `b7bce61b26b49470a98ba26e50f31d3e840d9a2c61ae3c01ba2c3ab8f48dc576` | `ebda8f9398759594f385c5017f76227f20b60f64a20a036b1627c400fe340df3` |
| W3GaugeAction | 4 | `42c6bd9e6c6807a186ece76347467574003828552c0ca31c2ba40ffc3e450cd0` | `b7c587943ca8fa8cabb72d95b3c2632111274e853fb60836061f03db88e2f0ce` |
| W3GaugeLabels | 13 | `d46e0e1aba3210eec8e852da2c0f9018d42e28a8aca38ac48ab5b39dba7cb84d` | `be33ca5616f743e45b633bd1012e784984e8cd3acd302b02e70e5e084da344e6` |
| W3LinearAction | 11 | `d47d1caf10dd99c677fb026d13e03dd9583d70a656d8b9b9576483ee2c75b602` | `f3eed85ab4329efaa435f6e313f459f6d15c41475f4548ed981df272454c9c4c` |
| W3LocalFullLabels | 9 | `ebd84d2085f9959dbefda0da6824c7117713837810b900e236ab4b2360b9c59e` | `fd06b2a51cb4aacf65eee7440b96d2dec62d3e322637fc1c94e122fec9d3d552` |
| W3LocalGauge | 5 | `efb0f3d384887dcf8bffea205a39889a712cef20c001ac41cb7dc78ac5e873eb` | `9170bc3bffa2bcf6752c64c10d077c791872d1b8d01a846daf76a33ae7c96f43` |
| W3LocalInterfaces | 10 | `57e6d6284384cb48c2a0ff6670bf688aafbd5a00810af40d57245876bc59ab9d` | `f1e4d30711269dd4e04df2e849c3680394aa63c44dfc30579478da5b054dcf49` |
| W3LocalLabels | 17 | `56f6b14f77382c0860c08b596adae0e0f70c94e2e3c3d0323a81b3a4cdb13acc` | `f4a0d4df00ef92f49a7c3f16e63b245aa2a1bd67ed3130983fe5dda4c875a2c3` |
| W3LocalOperationCoordinates | 8 | `b6732866a9f9fad2aafc018ca160bb511c0a81ebeec1823aacd4b04e93dc964d` | `38e10b3b481998b705846dfbde78f0ec97296dc678931a95ccaae74344df2b4e` |
| W3LocalRepairs | 12 | `747383a5f65edee941063f4658236eb9eeb19320f7e7032baf668819efaadc63` | `9a9acf57def63c73d39c95844d044bad4fedd4d1396235ed82046ed3a94530ee` |
| W3LoopIsomorphisms | 5 | `bb6c089dd0b5540a2604a72f4e9ad6063f4a24dfbf18e0f019310090743e92b7` | `9dd0c1eaf53c374806a54e65138fe10cba662ff4b2e6897729ce45bb4e911e1e` |
| W3OrdinaryClasses | 9 | `811fd45b5f56549f51ded98e8f497c02a4dec513c9b0f28d300c6c28a9ff1cc6` | `b52ce9fdf5842aaa4efee14737188db6b6ee1816007380d82fb6905eea38177f` |
| W3OrdinaryComparison | 8 | `cd77df068624f82317acbd0142113f049cee2d1ba60303b5e84bb47d997c4b1f` | `f80c6515ce2709f14a131a4c5c51e392d2b66e40c2d86494949cb352fe3864cd` |
| W3OrdinarySeams | 14 | `170fdc2d2f00230b17abddb342f544610989e6ae47a83e39965af84ca9649db2` | `86bf809a62756aa3ea8a4ef8248360fc07437132a395be88c392eed213b1612e` |
| W3Pi0Loss | 12 | `e0ea1c59fbacd60fdee2d74816154e43f436fadccc2cf91d2a067f6659ac9b23` | `ee43334020bb6b7b307577f3d402221171d1f75179ad202d2f477ab80e7333a7` |
| W3Regions | 16 | `32469d6a4dd39bb9ab42cfbbc258b6adf7b65d40751630606e3c6fcb458ff806` | `a35332c3595f351873cb44f581b87ea7ca4ee0e73ec493112a7cb68108a96f03` |
| W3RestrictionDiagram | 12 | `eb88b06c4be48ef79fe862658b3cfc6e58efeea372ef44fb251426337da21dd4` | `a06bf865d4eb6d21f32d417c76784116674d8730d51bdd2d70d1d47258e00ce2` |
| W3StrictConsequences | 10 | `a392c62d202bf5ee30bda29008795f4d02ef924ada03e4864fb3897647739083` | `01fbaac812b4ebb50d9a9ff85c4b54a9bae9672c3eb67d3243c01e5beb4d838e` |
| W3StrictGeneratedCover | 10 | `1168bd6f61e3a190e57c378ec8b47d2ec54c970f232713a49dfd99ec17c2d284` | `6876cd4935f28151593467daa7db3641d65028cbf35fa5649c74feedebff77a6` |
| W3StrictInverseChecks | 4 | `53c264a9b34883d77c3f91c30aa61a681a7b7ba35791bc45334cb0454255849e` | `dd15c7ac32c42d9adb6257aaf5c820089bfb2d3c513dbae8396f2aad8f795e49` |
| W3StrictLabels | 14 | `d91280a27850844e520a327406fdacdde9aebfa6c81e433696ff183d31e8d2ed` | `4b295f429263c6eea89b8dbd10cabc96c1f805c2dff2339483c0ad8e47a8e155` |
| W3UnrestrictedDescent | 10 | `1c491a111cbecb17d70cd93bada37f73eb1fa5b399637cf57da896c2d6c8136b` | `ffda4bcfe5a52e466ad9ef602d2e57ec480698f961ab71bcf9d557b2ecf93d23` |
| W3UnrestrictedLocalClasses | 12 | `029e5175cb4d58f540c3d6924dbc3c53b20d6e14bc91377eda3d053df6aa2e90` | `ecc986bd684ef0798998a9b2fc6bac5ce640809958676e8402a0d764ef661ea2` |
| W3UnrestrictedLocalEquivalences | 2 | `18834087465ddcdc2d6d0ab9317e42a3ec0f6a42f3ef941c58986f9c7c2df328` | `29c493256141ee20020292ace5f7a269497a594d8049a96d9647a6b0a795c6e0` |
| W3UnrestrictedLocalFunctors | 8 | `4f45978e37ff2030e7a5b4851c2be5d8675d82f7d87139eeade3792b7197b8c8` | `33edb2888aa195748b1d4053e99158ddedcf3e2be0610245584298c6c8cd4a13` |
| W3UnrestrictedRestrictions | 8 | `fde29b075fcdaeba502c47c92e5f8f2765d6a31ba2429d3fedbfa594bb6ef621` | `ee0b934d002d99a2221a9767ca7979235446ecd9af41c88f23ea3fedf77cc10f` |

| 個別公理audit module群 | 所有宣言数 | audit SHA256 | log SHA256 |
| --- | ---: | --- | --- |
| W3LinearAction, W3AffineInput, W3Regions | 50 | `cfb4e5d30f539ff56d2ef5e7cc9b068aa8f4b180a10b5fa57d9ea01b4fbd58ac` | `d5e9f330ffc90ab77e9452548acaf1303cae37721b1fc2ba97fe97d98ed33633` |
| W3AuthoredOperations, W3ActualRepairs, W3GaugeLabels, W3GaugeAction, W3ActualArrows, W3LoopIsomorphisms, W3Classes, W3Automorphisms | 83 | `3b852d2df60622b2947bbc2cb65a0a7eabe08b102d6cc5f38367e2c104e07723` | `1b3b408aba82da042b9b7f0c16073aed1c900eca048bf6fdd02ff5e80e018829` |
| W3LocalRepairs, W3LocalLabels, W3EmptyGroupoids, W3RestrictionDiagram, W3OrdinarySeams, W3OrdinaryComparison, W3OrdinaryClasses, W3FiniteCoefficients, W3LocalInterfaces, W3StrictGeneratedCover, W3StrictInverseChecks, W3UnrestrictedDescent | 133 | `b808ad88ced6b169c8cfe9d0b38e7b690f8a3e4dbae767aefbb0faa24ee3ff5c` | `3b330aa9bebd68ef0f780cf4682d5a63d8b98ac47c86c71a8184657d4318b682` |
| W3StrictLabels, W3StrictConsequences, W3LocalOperationCoordinates, W3LocalFullLabels, W3LocalGauge, W3UnrestrictedLocalFunctors, W3UnrestrictedLocalEquivalences, W3UnrestrictedRestrictions, W3UnrestrictedLocalClasses, W3Pi0Loss | 88 | `b5689a91267edc5fff67d705862d1a008f529a2a3879a85f849e629490caa7bc` | `74b2edf5f4151aa2273b5a94f367a9798dfedcb8c744226d49a44de6523d01de` |

<details>
<summary>C26 所有moduleで選択した全354宣言</summary>

```text
AAT.AG.RelativeRepairComposition.ClosedRegion.mk.congr_simp
AAT.AG.RelativeRepairComposition.W3ActualArrows.actualAction
AAT.AG.RelativeRepairComposition.W3ActualArrows.gauge_eq_iff_parameters
AAT.AG.RelativeRepairComposition.W3ActualArrows.hom_first
AAT.AG.RelativeRepairComposition.W3ActualArrows.hom_loop
AAT.AG.RelativeRepairComposition.W3ActualArrows.hom_second
AAT.AG.RelativeRepairComposition.W3ActualArrows.parameters_injective
AAT.AG.RelativeRepairComposition.W3ActualRepairs.ActualCategory
AAT.AG.RelativeRepairComposition.W3ActualRepairs.Allowed
AAT.AG.RelativeRepairComposition.W3ActualRepairs.NativeCategory
AAT.AG.RelativeRepairComposition.W3ActualRepairs.Parameters
AAT.AG.RelativeRepairComposition.W3ActualRepairs.RealRepairs
AAT.AG.RelativeRepairComposition.W3ActualRepairs.actualParametersEquiv
AAT.AG.RelativeRepairComposition.W3ActualRepairs.actual_operation_apply
AAT.AG.RelativeRepairComposition.W3ActualRepairs.correction_fixed
AAT.AG.RelativeRepairComposition.W3ActualRepairs.emptyObjectEquiv
AAT.AG.RelativeRepairComposition.W3ActualRepairs.empty_unique
AAT.AG.RelativeRepairComposition.W3ActualRepairs.fromParameters
AAT.AG.RelativeRepairComposition.W3ActualRepairs.nonzero_forward_not_allowed
AAT.AG.RelativeRepairComposition.W3ActualRepairs.parameters
AAT.AG.RelativeRepairComposition.W3ActualRepairs.parameters_allowed
AAT.AG.RelativeRepairComposition.W3ActualRepairs.parameters_from
AAT.AG.RelativeRepairComposition.W3ActualRepairs.parameters_operations
AAT.AG.RelativeRepairComposition.W3ActualRepairs.referenceRepair
AAT.AG.RelativeRepairComposition.W3ActualRepairs.unrestrictedParametersEquiv
AAT.AG.RelativeRepairComposition.W3ActualRepairs.unrestricted_repair_card
AAT.AG.RelativeRepairComposition.W3ActualRepairs.wholeAffineEquivalence
AAT.AG.RelativeRepairComposition.W3AffineInput.Op
AAT.AG.RelativeRepairComposition.W3AffineInput.comparison
AAT.AG.RelativeRepairComposition.W3AffineInput.edgeDecidableEq
AAT.AG.RelativeRepairComposition.W3AffineInput.edgeE
AAT.AG.RelativeRepairComposition.W3AffineInput.edgeF
AAT.AG.RelativeRepairComposition.W3AffineInput.edgeNameEquiv
AAT.AG.RelativeRepairComposition.W3AffineInput.edgeSource
AAT.AG.RelativeRepairComposition.W3AffineInput.edgeTarget
AAT.AG.RelativeRepairComposition.W3AffineInput.faceDecidableEq
AAT.AG.RelativeRepairComposition.W3AffineInput.geometry
AAT.AG.RelativeRepairComposition.W3AffineInput.linear_faces
AAT.AG.RelativeRepairComposition.W3AffineInput.name
AAT.AG.RelativeRepairComposition.W3AffineInput.name_edge
AAT.AG.RelativeRepairComposition.W3AffineInput.originalTower
AAT.AG.RelativeRepairComposition.W3AffineInput.reference
AAT.AG.RelativeRepairComposition.W3AffineInput.reference_e
AAT.AG.RelativeRepairComposition.W3AffineInput.reference_f
AAT.AG.RelativeRepairComposition.W3AffineInput.returnLinear
AAT.AG.RelativeRepairComposition.W3AffineInput.return_apply
AAT.AG.RelativeRepairComposition.W3AffineInput.vertexS
AAT.AG.RelativeRepairComposition.W3AffineInput.vertexT
AAT.AG.RelativeRepairComposition.W3AuthoredOperations.correctionValue
AAT.AG.RelativeRepairComposition.W3AuthoredOperations.loopPath
AAT.AG.RelativeRepairComposition.W3AuthoredOperations.loopValue
AAT.AG.RelativeRepairComposition.W3AuthoredOperations.loop_apply
AAT.AG.RelativeRepairComposition.W3AuthoredOperations.operation
AAT.AG.RelativeRepairComposition.W3AuthoredOperations.operation_e_apply
AAT.AG.RelativeRepairComposition.W3AuthoredOperations.operation_f_apply
AAT.AG.RelativeRepairComposition.W3AuthoredOperations.operation_linear
AAT.AG.RelativeRepairComposition.W3AuthoredOperations.operation_zero
AAT.AG.RelativeRepairComposition.W3AuthoredOperations.reference_apply
AAT.AG.RelativeRepairComposition.W3AuthoredOperations.reference_zero
AAT.AG.RelativeRepairComposition.W3Automorphisms.autFixedEquiv
AAT.AG.RelativeRepairComposition.W3Automorphisms.autFixedEquiv_label
AAT.AG.RelativeRepairComposition.W3Automorphisms.aut_labels
AAT.AG.RelativeRepairComposition.W3Automorphisms.constantLabel
AAT.AG.RelativeRepairComposition.W3Automorphisms.constant_fixes
AAT.AG.RelativeRepairComposition.W3Automorphisms.gauge_self_iff
AAT.AG.RelativeRepairComposition.W3Automorphisms.identityAutEquiv
AAT.AG.RelativeRepairComposition.W3Automorphisms.identity_aut_card
AAT.AG.RelativeRepairComposition.W3Automorphisms.shearAutEquiv
AAT.AG.RelativeRepairComposition.W3Automorphisms.shear_aut_card
AAT.AG.RelativeRepairComposition.W3Automorphisms.unrestricted_label_card
AAT.AG.RelativeRepairComposition.W3Automorphisms.vectorAut
AAT.AG.RelativeRepairComposition.W3Classes.emptyClassEquiv
AAT.AG.RelativeRepairComposition.W3Classes.emptyObject
AAT.AG.RelativeRepairComposition.W3Classes.empty_class_card
AAT.AG.RelativeRepairComposition.W3Classes.empty_object_eq
AAT.AG.RelativeRepairComposition.W3Classes.identityClassEquiv
AAT.AG.RelativeRepairComposition.W3Classes.identity_class_card
AAT.AG.RelativeRepairComposition.W3Classes.loop_normal
AAT.AG.RelativeRepairComposition.W3Classes.normalObject
AAT.AG.RelativeRepairComposition.W3Classes.shearClassEquiv
AAT.AG.RelativeRepairComposition.W3Classes.shearObject
AAT.AG.RelativeRepairComposition.W3Classes.shear_class_card
AAT.AG.RelativeRepairComposition.W3Classes.shear_object
AAT.AG.RelativeRepairComposition.W3EmptyGroupoids.BA
AAT.AG.RelativeRepairComposition.W3EmptyGroupoids.BA2
AAT.AG.RelativeRepairComposition.W3EmptyGroupoids.BFixed
AAT.AG.RelativeRepairComposition.W3EmptyGroupoids.globalEquivalence
AAT.AG.RelativeRepairComposition.W3EmptyGroupoids.leftAutEquiv
AAT.AG.RelativeRepairComposition.W3EmptyGroupoids.leftAutEquiv_label
AAT.AG.RelativeRepairComposition.W3EmptyGroupoids.leftEquivalence
AAT.AG.RelativeRepairComposition.W3EmptyGroupoids.overlapAutEquiv
AAT.AG.RelativeRepairComposition.W3EmptyGroupoids.overlapAutEquiv_label
AAT.AG.RelativeRepairComposition.W3EmptyGroupoids.overlapEquivalence
AAT.AG.RelativeRepairComposition.W3EmptyGroupoids.rightAutEquiv
AAT.AG.RelativeRepairComposition.W3EmptyGroupoids.rightAutEquiv_label
AAT.AG.RelativeRepairComposition.W3EmptyGroupoids.rightEquivalence
AAT.AG.RelativeRepairComposition.W3EmptyGroupoids.singletonAutEquiv
AAT.AG.RelativeRepairComposition.W3FiniteCoefficients.actualDefect
AAT.AG.RelativeRepairComposition.W3FiniteCoefficients.actual_defect_zero
AAT.AG.RelativeRepairComposition.W3FiniteCoefficients.bases
AAT.AG.RelativeRepairComposition.W3FiniteCoefficients.basisIndex
AAT.AG.RelativeRepairComposition.W3FiniteCoefficients.basis_value
AAT.AG.RelativeRepairComposition.W3FiniteCoefficients.enumEdges
AAT.AG.RelativeRepairComposition.W3FiniteCoefficients.enumFaces
AAT.AG.RelativeRepairComposition.W3FiniteCoefficients.enumK
AAT.AG.RelativeRepairComposition.W3FiniteCoefficients.enumRegions
AAT.AG.RelativeRepairComposition.W3FiniteCoefficients.fixed_faces
AAT.AG.RelativeRepairComposition.W3FiniteCoefficients.kernelCoordinate
AAT.AG.RelativeRepairComposition.W3FiniteCoefficients.kernel_inverse_value
AAT.AG.RelativeRepairComposition.W3FiniteCoefficients.original_linear
AAT.AG.RelativeRepairComposition.W3GaugeAction.gauge_first
AAT.AG.RelativeRepairComposition.W3GaugeAction.gauge_loop
AAT.AG.RelativeRepairComposition.W3GaugeAction.gauge_second
AAT.AG.RelativeRepairComposition.W3GaugeAction.unrestricted_normal_parameters
AAT.AG.RelativeRepairComposition.W3GaugeLabels.FixedVectors
AAT.AG.RelativeRepairComposition.W3GaugeLabels.GlobalLabels
AAT.AG.RelativeRepairComposition.W3GaugeLabels.emptyLabel
AAT.AG.RelativeRepairComposition.W3GaugeLabels.emptyLabelEquiv
AAT.AG.RelativeRepairComposition.W3GaugeLabels.emptyLabelEquiv_inverse_value
AAT.AG.RelativeRepairComposition.W3GaugeLabels.empty_forward
AAT.AG.RelativeRepairComposition.W3GaugeLabels.empty_return
AAT.AG.RelativeRepairComposition.W3GaugeLabels.identityFixedEquiv
AAT.AG.RelativeRepairComposition.W3GaugeLabels.shearFixedEquiv
AAT.AG.RelativeRepairComposition.W3GaugeLabels.unrestrictedLabel
AAT.AG.RelativeRepairComposition.W3GaugeLabels.unrestrictedLabelEquiv
AAT.AG.RelativeRepairComposition.W3GaugeLabels.unrestricted_source
AAT.AG.RelativeRepairComposition.W3GaugeLabels.unrestricted_target
AAT.AG.RelativeRepairComposition.W3LinearAction.A
AAT.AG.RelativeRepairComposition.W3LinearAction.identity_apply
AAT.AG.RelativeRepairComposition.W3LinearAction.identity_minus_shear
AAT.AG.RelativeRepairComposition.W3LinearAction.linearAction
AAT.AG.RelativeRepairComposition.W3LinearAction.primeThree
AAT.AG.RelativeRepairComposition.W3LinearAction.shear
AAT.AG.RelativeRepairComposition.W3LinearAction.shear_apply
AAT.AG.RelativeRepairComposition.W3LinearAction.shear_first
AAT.AG.RelativeRepairComposition.W3LinearAction.shear_fixed_iff
AAT.AG.RelativeRepairComposition.W3LinearAction.shear_ne_one
AAT.AG.RelativeRepairComposition.W3LinearAction.shear_second
AAT.AG.RelativeRepairComposition.W3LocalFullLabels.freeLabel
AAT.AG.RelativeRepairComposition.W3LocalFullLabels.leftFullLabelEquiv
AAT.AG.RelativeRepairComposition.W3LocalFullLabels.left_label_card
AAT.AG.RelativeRepairComposition.W3LocalFullLabels.left_source
AAT.AG.RelativeRepairComposition.W3LocalFullLabels.left_target
AAT.AG.RelativeRepairComposition.W3LocalFullLabels.rightFullLabelEquiv
AAT.AG.RelativeRepairComposition.W3LocalFullLabels.right_label_card
AAT.AG.RelativeRepairComposition.W3LocalFullLabels.right_source
AAT.AG.RelativeRepairComposition.W3LocalFullLabels.right_target
AAT.AG.RelativeRepairComposition.W3LocalGauge.left_gauge_eq
AAT.AG.RelativeRepairComposition.W3LocalGauge.left_gauge_zero
AAT.AG.RelativeRepairComposition.W3LocalGauge.local_reference_zero
AAT.AG.RelativeRepairComposition.W3LocalGauge.right_gauge_eq
AAT.AG.RelativeRepairComposition.W3LocalGauge.right_gauge_zero
AAT.AG.RelativeRepairComposition.W3LocalInterfaces.elimination
AAT.AG.RelativeRepairComposition.W3LocalInterfaces.equationEquiv
AAT.AG.RelativeRepairComposition.W3LocalInterfaces.generatedSection
AAT.AG.RelativeRepairComposition.W3LocalInterfaces.nativeEquivalence
AAT.AG.RelativeRepairComposition.W3LocalInterfaces.privateMatrix
AAT.AG.RelativeRepairComposition.W3LocalInterfaces.publicMatrix
AAT.AG.RelativeRepairComposition.W3LocalInterfaces.public_row_count
AAT.AG.RelativeRepairComposition.W3LocalInterfaces.public_rows_independent
AAT.AG.RelativeRepairComposition.W3LocalInterfaces.relation
AAT.AG.RelativeRepairComposition.W3LocalInterfaces.section_regular
AAT.AG.RelativeRepairComposition.W3LocalLabels.leftEdge
AAT.AG.RelativeRepairComposition.W3LocalLabels.leftLabel
AAT.AG.RelativeRepairComposition.W3LocalLabels.leftLabelEquiv
AAT.AG.RelativeRepairComposition.W3LocalLabels.leftS
AAT.AG.RelativeRepairComposition.W3LocalLabels.leftT
AAT.AG.RelativeRepairComposition.W3LocalLabels.left_relation
AAT.AG.RelativeRepairComposition.W3LocalLabels.overlapLabel
AAT.AG.RelativeRepairComposition.W3LocalLabels.overlapLabelEquiv
AAT.AG.RelativeRepairComposition.W3LocalLabels.overlapS
AAT.AG.RelativeRepairComposition.W3LocalLabels.overlapT
AAT.AG.RelativeRepairComposition.W3LocalLabels.overlap_no_edge
AAT.AG.RelativeRepairComposition.W3LocalLabels.rightEdge
AAT.AG.RelativeRepairComposition.W3LocalLabels.rightLabel
AAT.AG.RelativeRepairComposition.W3LocalLabels.rightLabelEquiv
AAT.AG.RelativeRepairComposition.W3LocalLabels.rightS
AAT.AG.RelativeRepairComposition.W3LocalLabels.rightT
AAT.AG.RelativeRepairComposition.W3LocalLabels.right_relation
AAT.AG.RelativeRepairComposition.W3LocalOperationCoordinates.left_name
AAT.AG.RelativeRepairComposition.W3LocalOperationCoordinates.left_operation_apply
AAT.AG.RelativeRepairComposition.W3LocalOperationCoordinates.left_typed_name
AAT.AG.RelativeRepairComposition.W3LocalOperationCoordinates.overlapObjectEquiv
AAT.AG.RelativeRepairComposition.W3LocalOperationCoordinates.overlap_unique
AAT.AG.RelativeRepairComposition.W3LocalOperationCoordinates.right_name
AAT.AG.RelativeRepairComposition.W3LocalOperationCoordinates.right_operation_apply
AAT.AG.RelativeRepairComposition.W3LocalOperationCoordinates.right_typed_name
AAT.AG.RelativeRepairComposition.W3LocalRepairs.LocalCategory
AAT.AG.RelativeRepairComposition.W3LocalRepairs.LocalLabels
AAT.AG.RelativeRepairComposition.W3LocalRepairs.LocalRepairs
AAT.AG.RelativeRepairComposition.W3LocalRepairs.actualRestriction
AAT.AG.RelativeRepairComposition.W3LocalRepairs.localAction
AAT.AG.RelativeRepairComposition.W3LocalRepairs.localEmptyObjectEquiv
AAT.AG.RelativeRepairComposition.W3LocalRepairs.localReferenceRepair
AAT.AG.RelativeRepairComposition.W3LocalRepairs.local_empty_operation
AAT.AG.RelativeRepairComposition.W3LocalRepairs.local_empty_unique
AAT.AG.RelativeRepairComposition.W3LocalRepairs.local_fixed_all
AAT.AG.RelativeRepairComposition.W3LocalRepairs.restriction_label
AAT.AG.RelativeRepairComposition.W3LocalRepairs.restriction_operation
AAT.AG.RelativeRepairComposition.W3LoopIsomorphisms.identity_isomorphic_iff
AAT.AG.RelativeRepairComposition.W3LoopIsomorphisms.isomorphic_iff_loop
AAT.AG.RelativeRepairComposition.W3LoopIsomorphisms.loopCoordinate
AAT.AG.RelativeRepairComposition.W3LoopIsomorphisms.shearInvariant
AAT.AG.RelativeRepairComposition.W3LoopIsomorphisms.shear_isomorphic_iff
AAT.AG.RelativeRepairComposition.W3OrdinaryClasses.identityOrdinaryAutEquiv
AAT.AG.RelativeRepairComposition.W3OrdinaryClasses.identityOrdinaryClassEquiv
AAT.AG.RelativeRepairComposition.W3OrdinaryClasses.ordinary_identity_aut_card
AAT.AG.RelativeRepairComposition.W3OrdinaryClasses.ordinary_identity_class_card
AAT.AG.RelativeRepairComposition.W3OrdinaryClasses.ordinary_shear_aut_card
AAT.AG.RelativeRepairComposition.W3OrdinaryClasses.ordinary_shear_class_card
AAT.AG.RelativeRepairComposition.W3OrdinaryClasses.restricted_global_not_equivalent
AAT.AG.RelativeRepairComposition.W3OrdinaryClasses.shearOrdinaryAutEquiv
AAT.AG.RelativeRepairComposition.W3OrdinaryClasses.shearOrdinaryClassEquiv
AAT.AG.RelativeRepairComposition.W3OrdinaryComparison.comparisonEquivalence
AAT.AG.RelativeRepairComposition.W3OrdinaryComparison.comparisonFunctor
AAT.AG.RelativeRepairComposition.W3OrdinaryComparison.comparisonMap
AAT.AG.RelativeRepairComposition.W3OrdinaryComparison.comparisonObject
AAT.AG.RelativeRepairComposition.W3OrdinaryComparison.comparison_faithful
AAT.AG.RelativeRepairComposition.W3OrdinaryComparison.comparison_full
AAT.AG.RelativeRepairComposition.W3OrdinaryComparison.comparison_source
AAT.AG.RelativeRepairComposition.W3OrdinaryComparison.comparison_target
AAT.AG.RelativeRepairComposition.W3OrdinarySeams.hom_square
AAT.AG.RelativeRepairComposition.W3OrdinarySeams.leftArrow
AAT.AG.RelativeRepairComposition.W3OrdinarySeams.leftObject
AAT.AG.RelativeRepairComposition.W3OrdinarySeams.left_object_eq
AAT.AG.RelativeRepairComposition.W3OrdinarySeams.objectEquiv
AAT.AG.RelativeRepairComposition.W3OrdinarySeams.ordinary_object_card
AAT.AG.RelativeRepairComposition.W3OrdinarySeams.rightArrow
AAT.AG.RelativeRepairComposition.W3OrdinarySeams.rightObject
AAT.AG.RelativeRepairComposition.W3OrdinarySeams.right_object_eq
AAT.AG.RelativeRepairComposition.W3OrdinarySeams.seam
AAT.AG.RelativeRepairComposition.W3OrdinarySeams.seamObject
AAT.AG.RelativeRepairComposition.W3OrdinarySeams.seam_object
AAT.AG.RelativeRepairComposition.W3OrdinarySeams.seam_restore
AAT.AG.RelativeRepairComposition.W3OrdinarySeams.square_iff
AAT.AG.RelativeRepairComposition.W3Pi0Loss.LeftClasses
AAT.AG.RelativeRepairComposition.W3Pi0Loss.OverlapClasses
AAT.AG.RelativeRepairComposition.W3Pi0Loss.Pi0Pullback
AAT.AG.RelativeRepairComposition.W3Pi0Loss.RightClasses
AAT.AG.RelativeRepairComposition.W3Pi0Loss.global_aut_count_lost
AAT.AG.RelativeRepairComposition.W3Pi0Loss.global_class_count_lost
AAT.AG.RelativeRepairComposition.W3Pi0Loss.leftClassRestriction
AAT.AG.RelativeRepairComposition.W3Pi0Loss.pi0_aut_card
AAT.AG.RelativeRepairComposition.W3Pi0Loss.pullbackEquiv
AAT.AG.RelativeRepairComposition.W3Pi0Loss.pullback_card
AAT.AG.RelativeRepairComposition.W3Pi0Loss.referencePair
AAT.AG.RelativeRepairComposition.W3Pi0Loss.rightClassRestriction
AAT.AG.RelativeRepairComposition.W3Regions.candidates
AAT.AG.RelativeRepairComposition.W3Regions.candidates_all
AAT.AG.RelativeRepairComposition.W3Regions.candidates_outside
AAT.AG.RelativeRepairComposition.W3Regions.fixedEdges
AAT.AG.RelativeRepairComposition.W3Regions.fixedRegion
AAT.AG.RelativeRepairComposition.W3Regions.fixed_all
AAT.AG.RelativeRepairComposition.W3Regions.fixed_empty
AAT.AG.RelativeRepairComposition.W3Regions.indexed_cover
AAT.AG.RelativeRepairComposition.W3Regions.leftRegion
AAT.AG.RelativeRepairComposition.W3Regions.overlap
AAT.AG.RelativeRepairComposition.W3Regions.overlap_edges
AAT.AG.RelativeRepairComposition.W3Regions.overlap_vertices
AAT.AG.RelativeRepairComposition.W3Regions.private_empty
AAT.AG.RelativeRepairComposition.W3Regions.regions
AAT.AG.RelativeRepairComposition.W3Regions.regions_cover
AAT.AG.RelativeRepairComposition.W3Regions.rightRegion
AAT.AG.RelativeRepairComposition.W3RestrictionDiagram.Ordinary
AAT.AG.RelativeRepairComposition.W3RestrictionDiagram.leftLabelRestriction
AAT.AG.RelativeRepairComposition.W3RestrictionDiagram.leftRestriction
AAT.AG.RelativeRepairComposition.W3RestrictionDiagram.left_boundary
AAT.AG.RelativeRepairComposition.W3RestrictionDiagram.left_map_value
AAT.AG.RelativeRepairComposition.W3RestrictionDiagram.left_original_value
AAT.AG.RelativeRepairComposition.W3RestrictionDiagram.ordinary_is_groupoid
AAT.AG.RelativeRepairComposition.W3RestrictionDiagram.rightLabelRestriction
AAT.AG.RelativeRepairComposition.W3RestrictionDiagram.rightRestriction
AAT.AG.RelativeRepairComposition.W3RestrictionDiagram.right_boundary
AAT.AG.RelativeRepairComposition.W3RestrictionDiagram.right_map_value
AAT.AG.RelativeRepairComposition.W3RestrictionDiagram.right_original_value
AAT.AG.RelativeRepairComposition.W3StrictConsequences.actual_inverse_label
AAT.AG.RelativeRepairComposition.W3StrictConsequences.autFixedEquiv
AAT.AG.RelativeRepairComposition.W3StrictConsequences.emptyClassEquiv
AAT.AG.RelativeRepairComposition.W3StrictConsequences.emptyObjectEquiv
AAT.AG.RelativeRepairComposition.W3StrictConsequences.empty_class_card
AAT.AG.RelativeRepairComposition.W3StrictConsequences.empty_object_card
AAT.AG.RelativeRepairComposition.W3StrictConsequences.identityAutEquiv
AAT.AG.RelativeRepairComposition.W3StrictConsequences.identity_aut_card
AAT.AG.RelativeRepairComposition.W3StrictConsequences.shearAutEquiv
AAT.AG.RelativeRepairComposition.W3StrictConsequences.shear_aut_card
AAT.AG.RelativeRepairComposition.W3StrictGeneratedCover.Groupoid
AAT.AG.RelativeRepairComposition.W3StrictGeneratedCover.Objects
AAT.AG.RelativeRepairComposition.W3StrictGeneratedCover.actualEquivalence
AAT.AG.RelativeRepairComposition.W3StrictGeneratedCover.actualObjectEquiv
AAT.AG.RelativeRepairComposition.W3StrictGeneratedCover.emptyEquivalence
AAT.AG.RelativeRepairComposition.W3StrictGeneratedCover.empty_restored_operation
AAT.AG.RelativeRepairComposition.W3StrictGeneratedCover.extract_restore
AAT.AG.RelativeRepairComposition.W3StrictGeneratedCover.nativeEquivalence
AAT.AG.RelativeRepairComposition.W3StrictGeneratedCover.restore_extract
AAT.AG.RelativeRepairComposition.W3StrictGeneratedCover.restore_operation
AAT.AG.RelativeRepairComposition.W3StrictInverseChecks.actual_forward_inverse
AAT.AG.RelativeRepairComposition.W3StrictInverseChecks.actual_inverse_forward
AAT.AG.RelativeRepairComposition.W3StrictInverseChecks.native_forward_inverse
AAT.AG.RelativeRepairComposition.W3StrictInverseChecks.native_inverse_forward
AAT.AG.RelativeRepairComposition.W3StrictLabels.Labels
AAT.AG.RelativeRepairComposition.W3StrictLabels.actualLabelEquiv
AAT.AG.RelativeRepairComposition.W3StrictLabels.actual_forward_label
AAT.AG.RelativeRepairComposition.W3StrictLabels.emptyLabelsEquiv
AAT.AG.RelativeRepairComposition.W3StrictLabels.empty_label_vector
AAT.AG.RelativeRepairComposition.W3StrictLabels.extract_restored_label
AAT.AG.RelativeRepairComposition.W3StrictLabels.forward_patch_value
AAT.AG.RelativeRepairComposition.W3StrictLabels.identityLabelsEquiv
AAT.AG.RelativeRepairComposition.W3StrictLabels.restore_original_vertex
AAT.AG.RelativeRepairComposition.W3StrictLabels.shared_s_coordinate
AAT.AG.RelativeRepairComposition.W3StrictLabels.shared_s_value
AAT.AG.RelativeRepairComposition.W3StrictLabels.shared_t_coordinate
AAT.AG.RelativeRepairComposition.W3StrictLabels.shared_t_value
AAT.AG.RelativeRepairComposition.W3StrictLabels.shearLabelsEquiv
AAT.AG.RelativeRepairComposition.W3UnrestrictedDescent.Descent
AAT.AG.RelativeRepairComposition.W3UnrestrictedDescent.actualEquivalence
AAT.AG.RelativeRepairComposition.W3UnrestrictedDescent.descent_is_groupoid
AAT.AG.RelativeRepairComposition.W3UnrestrictedDescent.left_choice
AAT.AG.RelativeRepairComposition.W3UnrestrictedDescent.left_label
AAT.AG.RelativeRepairComposition.W3UnrestrictedDescent.nativeEquivalence
AAT.AG.RelativeRepairComposition.W3UnrestrictedDescent.right_choice
AAT.AG.RelativeRepairComposition.W3UnrestrictedDescent.right_label
AAT.AG.RelativeRepairComposition.W3UnrestrictedDescent.seam_label
AAT.AG.RelativeRepairComposition.W3UnrestrictedDescent.unrestricted_fixed
AAT.AG.RelativeRepairComposition.W3UnrestrictedLocalClasses.leftAutEquiv
AAT.AG.RelativeRepairComposition.W3UnrestrictedLocalClasses.leftClassEquiv
AAT.AG.RelativeRepairComposition.W3UnrestrictedLocalClasses.left_class_card
AAT.AG.RelativeRepairComposition.W3UnrestrictedLocalClasses.overlapAutEquiv
AAT.AG.RelativeRepairComposition.W3UnrestrictedLocalClasses.overlapClassEquiv
AAT.AG.RelativeRepairComposition.W3UnrestrictedLocalClasses.overlapEquivalence
AAT.AG.RelativeRepairComposition.W3UnrestrictedLocalClasses.overlap_class_card
AAT.AG.RelativeRepairComposition.W3UnrestrictedLocalClasses.rightAutEquiv
AAT.AG.RelativeRepairComposition.W3UnrestrictedLocalClasses.rightClassEquiv
AAT.AG.RelativeRepairComposition.W3UnrestrictedLocalClasses.right_class_card
AAT.AG.RelativeRepairComposition.W3UnrestrictedLocalClasses.singleAutEquiv
AAT.AG.RelativeRepairComposition.W3UnrestrictedLocalClasses.singleClassEquiv
AAT.AG.RelativeRepairComposition.W3UnrestrictedLocalEquivalences.leftEquivalence
AAT.AG.RelativeRepairComposition.W3UnrestrictedLocalEquivalences.rightEquivalence
AAT.AG.RelativeRepairComposition.W3UnrestrictedLocalFunctors.leftFunctor
AAT.AG.RelativeRepairComposition.W3UnrestrictedLocalFunctors.leftReference
AAT.AG.RelativeRepairComposition.W3UnrestrictedLocalFunctors.leftReferenceArrow
AAT.AG.RelativeRepairComposition.W3UnrestrictedLocalFunctors.left_reference_labels
AAT.AG.RelativeRepairComposition.W3UnrestrictedLocalFunctors.rightFunctor
AAT.AG.RelativeRepairComposition.W3UnrestrictedLocalFunctors.rightReference
AAT.AG.RelativeRepairComposition.W3UnrestrictedLocalFunctors.rightReferenceArrow
AAT.AG.RelativeRepairComposition.W3UnrestrictedLocalFunctors.right_reference_labels
AAT.AG.RelativeRepairComposition.W3UnrestrictedRestrictions.leftLabelRestriction
AAT.AG.RelativeRepairComposition.W3UnrestrictedRestrictions.leftRestriction
AAT.AG.RelativeRepairComposition.W3UnrestrictedRestrictions.left_map_value
AAT.AG.RelativeRepairComposition.W3UnrestrictedRestrictions.left_original_value
AAT.AG.RelativeRepairComposition.W3UnrestrictedRestrictions.rightLabelRestriction
AAT.AG.RelativeRepairComposition.W3UnrestrictedRestrictions.rightRestriction
AAT.AG.RelativeRepairComposition.W3UnrestrictedRestrictions.right_map_value
AAT.AG.RelativeRepairComposition.W3UnrestrictedRestrictions.right_original_value
ZMod.instField.congr_simp
```

</details>

### Cycle 27 selection — W5の同じ実入力・相対障害・局所案の統合

```yaml
ledger_type: target_cycle_result
goal: G-130-aat-relative-repair-composition
cycle: 27
goal_blob_sha: 8da0fb4eb75d1cb5c37a9d4ddf5e03c18c0bb8a2
base_oid: d547cba2c2a9c11416f053851a5908ad186d3356
tracking_issue: 5132
report_path: research/reports/G-130-aat-relative-repair-composition.md
selection:
  proof_state_ref: "Issue5132 C26受理、PR5176 root受理、report C1–C26"
  proof_dag_predecessors: ["C2/C3/C5 相対actual repair", "C6/C7/C9 全relative cover/Bと正符号接続写像", "C14 全NativeAffine実核と実操作", "C24 original cochain/defect評価API", "C26 W3受理はW5開始状態"]
  milestone: "固定W5の全(b1,b2): 同じ原全Aff(F2)の相対H2とBの商Ωでb2−b1を計算し、全独立局所修復・大域可解性・原絶対H2=0を接続する"
  proof_obligations:
    - "元s,t、三平行e,a,b:s→t、原二面e⇒a/e⇒b、空3cells、原全Aff→GL→1/全実核、refe=I/refa=τb1/refb=τb2、恒等core/比較、P両頂点とa,b、always共有e、候補空、元閉U/V/Wと全coverを構成し全方向条件を放電"
    - "独立whole実global/local repairsと全元labelsからu=b1/u=b2を両方向で導き、全局所構成・元制限/arrow・同じNativeDescent Bを接続。固定頂点labelsを全保持し、重なりの実修復値をF2へ両逆対応"
    - "同じ元全核/輸送/ordered face wordsから全相対C0=0/C1=F2/C2=F2²/d1u=(u,u)/d2=0/actualδ=(-b1,-b2)を同定。whole相対H2=F2²/diagF2をF2へ両逆、原actual obstruction classをb2−b1へ送る"
    - "全localH1/H2=0、全overlapH1=F2、元restriction-induced local images=0からwholeΩ=F2を同定。任意独立actual局所案のdifference class/ωをb2−b1と評価し、選び直し独立性、正符号∂[z]=actual[δ]、原H2kernel同型を同じ一般Bから接続"
    - "全(b1,b2)でlocalは常時可解、actualglobal可解iff b1=b2 iff相対障害/ω零を原操作/一般A/Bに接続。全四指定入力の修復値と非対角二入力の局所可解・相対/商障害非零・大域不能を明示"
    - "固定を外した同じ原全辺/二面微分d1(u,a,b)=(u−a,u−b)の全射性を元cochainsから構成し、whole絶対nativeH2=0を証明。同じ原表示/全係数/defectとP相対障害の非零性を比較し、F実現への同じ原入力対応を保つ"
  exit_criteria:
    - "全指定入力/元geometry/全kernels/固定条件/閉coverと全独立actualglobal/local/元全labels/重なり/一般A/B/Fの対応を同じ入力で構成"
    - "元whole相対complex/actualδ/wholeH2とwholelocal/overlapH1,H2/Ω/actualω/正符号接続を同じ元制限から両方向に同定"
    - "全入力local常時可解/globaliff同値と全四指定値/非零例、同じ原absolutewholeH2零を証明し相対との比較を閉じる"
    - "各変更単一production本体/報告全所有宣言個別公理/hash/登録/common scan/固定targetと適用版、標準四本PR査読とroot受理、exact-head CIを確認"
  selection_reason: "残る指定例W5の全要求を一到達点で閉じ、既受理一般A–FとW1–W4に対する累積全target完了判定へ進む。file単位でcycleを分割しない"
  expected_result_type: proof-obligation-discharged
  lean_targets: ["W5AffineInput/Regions/ActualRepairs/LocalRepairs", "W5OriginalDifferentials/RelativeCoefficients/RelativeObstruction", "W5LocalCohomology/OverlapCohomology/IntegrationObstruction", "W5NativeDescent/ActualSolvability/AbsoluteCohomology"]
  risks: ["relativezeroを供給fieldにしない", "独立actual対象/全arrowを座標の像へ縮めない", "δとlocaldifferenceの符号", "whole商/原nativeH2をchosenimageで代替しない", "元P固定を重なりの自由頂点へ変えない", "原absolutecomplexを別行列で代替しない"]
  unchecked: ["上記六義務は実装前。達成は結果packetで個別対応", "累積A–F/W1–W5の最終完了判定は別fresh四本gate"]
```

### C27 W5の元実操作と全相対障害

元表示は頂点s,t、三平行辺e,a,b:s→t、二面e⇒aとe⇒b、空の3-cellを持つ。
係数はF2で、操作群は全Aff(F2)、線形射影は全GL(F2)への元の射影である。
入力(b1,b2)は全F2²を動き、元参照操作はe=I、a=τb1、b=τb2、比較は恒等である。
物理的固定部分Pは両頂点とa,bを持つ。共有eはalwaysで、候補集合は空である。
UとVは各元の面とその全辺を保持し、重なりWは両頂点とeを保持する。

独立実修復の型は元の全アフィン操作・元線形成分・元二面等号・元P固定条件から定義する。
共有操作の零での値uを読むと、全三辺操作がuから復元される。
元の実写像の面等号はu=b1、u=b2とそれぞれ同値で、双方から全実修復を構成する。
局所では元の一面からそれぞれu=b1、u=b2となり、全入力で独立局所案が存在する。
重なりでは二つの面がないため全u∈F2を保持するが、全頂点ラベルは元Pの固定条件から零となる。
元の全対象・全射と離散F2の対応、元の制限の辺値・ラベル値、同じNativeDescent Bとの同値を対応させる。

元の全核を各頂点のF2へ両逆に座標化し、元の輸送は恒等となる。
元のordered face wordsから全d1(u,a,b)=(u-a,u-b)を導く。
同じP相対複体ではC0=0、C1=F2、C2=F2²、d1(u)=(u,u)、d2=0である。
元の実欠陥δ=(-b1,-b2)は実参照操作の逆合成から生成する。
全相対H2=F2²/diag(F2)を、第一面から第二面を引く読みでF2へ両逆に同定する。
この読みの核は元の全d1境界像と一致し、元KのH2との比較は同じ全コチェイン値を保持する。
元のactual obstruction classはb2-b1へ送られる。

各局所の全d1は全一面係数への同型となり、全局所H1とH2は零である。
重なりの全C0とd1は零で、全H1は同じ共有辺F2となる。
元のrestriction-induced H1像の両方は零であり、Bで指定された和を分母とする全ΩもF2へ両逆に同定する。
任意の独立実局所案の差は同じ元e上で第二案から第一案を引き、その全H1類と全Ω類はb2-b1となる。
局所案の選び直し独立性、正符号∂[z]=[δ]、全Ωから元H2制限核への同型は同じ一般Bに接続する。
両局所H2が零なので、その核は元の全相対H2である。

全入力で大域実修復の存在はb1=b2と同値であり、同じAの元相対障害零・Bの元Ω零と一致する。
(0,0)と(1,1)の修復はそれぞれ元eの値0と1を保持する。
(0,1)と(1,0)では両局所案が存在し、両方の実障害類の値は1で、大域実修復は存在しない。
固定を外した同じ元表示の全微分は、u=0、a=-r1、b=-r2という全辺補正で任意の二面値を復元する。
したがって同じ元の全絶対H2は零である。物理的Pを保つ相対障害との比較でも、二面・全核・実欠陥の元の値を保持する。

### C27 前提の生成と使用

| Premise/structure | role on W5 | input construction | actual proof use |
| --- | --- | --- | --- |
| 全F2の体構造、全Aff/GL射影と全実核 | discharge-required | primeTwo、Op、originalTower；同じC14 NativeAffine.tower/linearCoefficient | 実線形条件、全核cochainの相互逆、actual/native対象と全labels |
| 元Fin2頂点、元Fin3三平行辺、元Bool二面、全(b1,b2) | justified ambient-boundary | geometry、name/edgeNameEquiv、reference、comparison | 全実面等号、全cochain値、各入力修復と不能 |
| 元辺・射影像の強さ、全核可換、輸送全単射、比較中央化 | discharge-required for this input | 同じC14 tower(original=reference, reference=reference, comparison=0, linear_faces)の生成field、現在の全kernels | Native actual repairs/補正/gauge、全微分/実defect/一般A/B |
| 原参照core整合、指定3cell条件 | discharge-required | linear_facesで原実wordの射影一致、original_syzygyで原Empty 3cells | originalTowerとactual original obstructionCocycle/positive connecting |
| 物理Pの閉包とP上面整合、always/candidate分割 | discharge-required | fixedRegion、fixed_faces、edge_partition、shared_not_fixed、candidates=empty | 独立全修復fixed_value、全相対C0/C1、全ラベル零、一般A |
| 元閉U/V/W、full cells coverと原制限 | discharge-required | leftRegion/rightRegion/overlap、regions_cover、region_edges、overlap_edges/faces/vertices | 共通native repair restriction、一般B、元relative short exact/cohomology maps |
| 全独立global/local actual repairsと全labels | construction, conclusion-equivalent-risk audit | NativeAffine.Repair/Groupoidを原全操作・面・Pで独立定義；fromValue/localFromValueは元値条件から全実操作を生成 | value_operations/from_value、localValue_operations/local_unique、overlapValueEquiv、全Discrete/groupoid同値 |
| 元全相対cochains/実delta | construction, discharge-required | 元全kernelCoordinate、whole cochain/faceCoordinates両逆、原d1/d2、actualDefect原生成 | 原wholeH2のboundary range=reading kernel、actualCycle_originalとactual_class_comparison |
| 全H2/全local images/Ω/正符号 | construction, discharge-required | h2Coordinate、local_d1_surjective/local_cycles、overlap wholeH1、両画像和零、元generic B kernel | 任意actual localCoordinateとdifferenceCycle、omega_value、connecting_actual_difference、omega_original_class |
| actual global/obstruction zero condition | conclusion, never supplied as premise | 元修復分類と全商の読み、general_a/general_b | 全(b1,b2)のiff、全4入力の実構成と非対角非零/不能 |
| 同じ原absolute全cochainsとH2 | construction, discharge-required | 原全d1のabsoluteCochain全逆像、original native absolute supported d1 onto | whole absolute_h2_zero、forgetPhysicalFace/actualDefect値、相対非零との同入力比較 |

一般A/Bの条件は本文由来のdirection-hypothesisであり、W5での適用条件は同じ入力から放電する。上表の構成は放電済みの申告であり、独立査読がsourceと使用を照合する。未放電の追加仮定は置かない。成果の位置づけは `unported (Research-proved)`。

### C27 使用する先行宣言の版

受理版と現在のsourceは一致する。表の各moduleでは使用するstatement・必要な定義・同じ原入力の適用引数を確認する。受理記録は再利用の資格、現在のsourceは適用の数学的な証拠である。

| Module | source SHA256 | 受理source commit | root review comment ID |
| --- | --- | --- | --- |
| NativeAffineTower | `747d4a8f68c7957b5675bbe4a054a1499c34755efec6d12d58e0a0a4610d44ad` | `a185e8d0a505999f24cb540bc28cbd26ff69162e` | 5931624166 |
| NativeAffineCoefficients | `1e35973c81534691a223ff1a785f5ca10d2ee421d387a901b8521203cd287c04` | `a185e8d0a505999f24cb540bc28cbd26ff69162e` | 5931624166 |
| NativeAffineDifferentials | `8838d39a6eeef0ccbce9e099f2dc17abb6777a152ec9af471012bc6572d62c9a` | `a185e8d0a505999f24cb540bc28cbd26ff69162e` | 5931624166 |
| NativeAffineRestriction | `7b97ba55b365233d72fd8a9b052c2bb8ac57b9989a0ddb77703cdb741db66138` | `a185e8d0a505999f24cb540bc28cbd26ff69162e` | 5931624166 |
| NativeAffineGroupoid | `994a5800d3fc012d758a8db696ae35260339f4b0560d7a27d3f03b31007ea148` | `a185e8d0a505999f24cb540bc28cbd26ff69162e` | 5931624166 |
| NativeAffineCorrection | `4bd3a03107254b859a6586aeafbd3bf2d929fa0ae499fb49c8fc5eb4dab9430a` | `f55004f3a83a16ad7b741e9980ac307c6e9712e9` | 5940657055 |
| CoverCohomology | `545e02b2fb76bae9731546f1aa5f1b3fb5b488a6a34821149f8e40d849206d4e` | `13e1c0d8f9221ba65025431ad5ec6b32ebe61829` | 5923198060 |
| CoverNativeCohomology | `b524527bb821a2a056d02f42ec8b268df0b308872e59eb9f2dd75f9c22cc5d82` | `13e1c0d8f9221ba65025431ad5ec6b32ebe61829` | 5923198060 |
| CoverObstructionKernel | `2b36c08868e4539232f898e7dc95877df2ac0d288ebb2b03058e83f033e60db3` | `13e1c0d8f9221ba65025431ad5ec6b32ebe61829` | 5923198060 |
| NativeCoverObstruction | `8d06c6846f1aad4a50e2dc51d064fcfd42f51affd9e2c9200be82f978e449051` | `13e1c0d8f9221ba65025431ad5ec6b32ebe61829` | 5923198060 |
| NativeDescent | `96f50a9f9315809de40321f62b8a7110d1ce9f812e18878c81a62b5ba1a0fd99` | `c38f8f6150e4e8643b1d0547feb1580f9c3dc0a7` | 5921438709 |
| NativeEquationBridge | `5ebf7fb1c1283cda059ea23477fdd573f31d332b0cbb4ce77805cd544c7b3874` | `c38f8f6150e4e8643b1d0547feb1580f9c3dc0a7` | 5921438709 |

### Cycle 27 result proposal

```yaml
ledger_type: target_cycle_result
goal: G-130-aat-relative-repair-composition
cycle: 27
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "固定六義務の全入力・独立全実修復/全射・元相対複体/実delta・全H2/Ω・任意局所案/正符号・全四値・元絶対H2比較を構成"
  exit_criteria_status:
    - "原全Aff/全核/三辺二面/P/always/空候補/全閉cover、全actual/local/全labels/元制限/同じB/Fを構成"
    - "原全相対cochains/d1/d2/actualδ、whole relative H2/local H1,H2/overlap H1/Ω/positive connectingを両逆と元微分から導出"
    - "全(b1,b2)のlocal常時可解、global iff/実障害 iff、全四値/実修復/非零不能、同じ原absolute全H2零を証明"
    - "単一本体15と全所有個別公理208/hash/登録/common scanを対応。標準四本PR査読/root受理/同head CIはPR監査記録へ固定"
  split_reason: none
  completion_candidate: yes
  lean_artifacts: ["W5AffineInput/Regions/AuthoredOperations/ActualRepairs/LocalRepairs/ActualArrows", "W5OriginalDifferentials/RelativeCoefficients/RelativeObstruction/LocalCohomology/OverlapCohomology", "W5NativeDescent/IntegrationObstruction/AbsoluteCohomology/ActualSolvability"]
  evidence: ["actualValueEquiv/from_value", "overlapDiscreteEquivalence/nativeEquivalence/actualEquivalence", "originalH2Coordinate/actual_obstruction_value", "omegaCoordinate/omega_value/connecting_actual_difference/omega_original_class", "global_iff/general_a/general_b/four_relative_values/four_integration_values", "absolute_h2_zero/absolute_relative_comparison"]
  claim_mapping:
    theorem_names: ["W5ActualSolvability.global_iff/general_a/general_b", "W5IntegrationObstruction.omega_value/connecting_actual_difference", "W5AbsoluteCohomology.absolute_h2_zero"]
    source_labels: ["固定G-130 W5/A/B/F", "n1017 §5.2"]
    conjuncts: ["原全対象/全射/制限", "whole相対障害とwholeΩ=b2−b1", "全局所可解/global iff b1=b2/全四値", "同じ原絶対H2零と相対非零"]
    undischarged_assumptions: []
    acceptance_point: "同じ原入力上のW5六義務。累積全GOALは固定headの別四本completion gateで照合する"
    port_status: unported
audits:
  premise_delta:
    discharged: ["原whole affine towerの全条件", "P/cover/原制限/原syzygy", "独立全修復/元labels/元native B", "全原cochains/wholequotients/actualclasses/全指定値/absolute比較"]
    remaining: []
  certificate_provenance:
    discharged: ["元typed geometry/reference/comparison→originalTower", "原fullkernel/differential→cochains/actualδ/wholeH2", "任意独立actual localCoordinate→difference/wholeΩ", "原全絶対cochains→d1 onto/H2 zero"]
    unresolved: []
  proof_use:
    used: ["原全実Affine equality→u=b1/u=b2→whole実修復", "物理P全頂点/固定辺→全label零/relative C0=0", "original ordered words/full kernel transport→d1/delta/whole boundary range", "原fullcover/generic B→all descent/omega independent/positive connecting", "wholequotient both inverses→actual zero iff/非対角", "原全d1の全逆像→absolute H2 zero"]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: ["下記15 current source/body logsと4 selected-owned individual audits", "全所有宣言リスト", "PRのraw command/hash/common scan evidence"]
  blocking_findings: []
  next_obligation: "同固定headの標準PR review/root受理後、累積A–F/W1–W5と全material premiseのfinal packetをPRコメントへ置き、別fresh Math2/Lean2の全target completion gate"
```

### C27 productionと個別公理の一次検証対応

全15単一production本体のactual exitは0、error/warningは各0。
namespaceの202宣言と、所有moduleで生成されたnamespace外helper6を含む全208宣言を個別 `#print axioms` で被覆する。
本体elaborationと、既検証本体をimportする個別公理監査を分け、source/helper/raw logのSHA256を対応させる。
標準公理はpropext、Classical.choice、Quot.sound。
本体コマンドは `cd research/lean && lake env lean -s4096 -D Elab.async=false -o .lake/build/lib/lean/<module path>.olean <source path>`。
個別公理コマンドは `cd research/lean && lake env lean -s4096 -D Elab.async=false ../../.tmp/g130/<selected-owned helper>.lean`。
Research全体・aggregate・全module/file loopのelaborationは実行しない。

| Production module | namespace宣言数 | source SHA256 | 本体log SHA256 |
| --- | ---: | --- | --- |
| W5AbsoluteCohomology | 8 | `231b0402293aedf9bab0c516daf9c145138fdc9a70d7645db3e59e15a2813b92` | `1388335446af4d46a4ab938edd1febe5acd4880d032904c4a8d10991aaa3026c` |
| W5ActualArrows | 9 | `96d44ad63d93ac1448feda8eecca45e014c108a0ced3e29b6fef225f247843a1` | `d55ed42a10710dbe81a4d83416e522337c3d4584d3721ec2d0f519ace67ccc0e` |
| W5ActualRepairs | 15 | `5f0c8e687a6009003288946ecbbebd6d20bb1e435b923ac5e84c4643697f6645` | `dcccee0f9f638931349b51aaf971d674c3718ada37f341607607b14eca2f76dc` |
| W5ActualSolvability | 19 | `39e3a7d46bcbec77f564290c7dfa54862dcfa8d06c3207d793686ca9f7d61887` | `166bd4ba4fcd976c83059f2649a6015f87233a00a6180cd124a5ef2057510dc1` |
| W5AffineInput | 19 | `de8f0c11a8099a36ac552e087e699627b8a6e7de0d6820410e6c86d3effa271c` | `5a5fbaf16645b42e7821db0216e9f3757a94cb6d8f5b243ee94e37e12acc329b` |
| W5AuthoredOperations | 12 | `22d5261ca73f4ca2849b8b6f16f65b5ff9285f9e636e722392b2bb8cde0a7a44` | `fbcd12b6e44a2cab88a4fe3eabb48d5a580149451892b67b6d564bcf74088c98` |
| W5IntegrationObstruction | 9 | `254e5fa07608d34b6b59fb2b409267ca8ba3bbe39ece28f67238bd985061328b` | `8d5f988930c6486ada7193feb4ac6e175952862588771665f52722d7d7714b8e` |
| W5LocalCohomology | 6 | `c8bd565554fd6da9ffbb403036923c54f147a9372a1dd2c45e92795d1b73df36` | `8af2904d95d2a4547adbab95ea8c11c00b379da527473e5fd987d377e385c574` |
| W5LocalRepairs | 24 | `a7a44ea30a8eb2a267b6ada7493b18d7ec00c5ca559bc023b4f05f073ec07317` | `c5d2abcb5daf66e3c5b1be44445852876ee0c9b24677f3c9d031bcfdc03eea83` |
| W5NativeDescent | 14 | `95b4e6749a5ff9a85c08a3779267f0594eaea9708b65ed96955e197d610c3049` | `e3ef4d103411fb7309ec1ac90cd9402cb2be6abbb928ecdb8dbcd3114eeb54ad` |
| W5OriginalDifferentials | 9 | `b610140feebf26b42f1a038a9a5970705ccf2e5173c0defc7a3375e45ef236f3` | `06a612a3ee8cdbb731dd7a465880264c60c1478382e01fd46486faa5e4534bc6` |
| W5OverlapCohomology | 12 | `f917e74be1aa67f953e14817237c1d3e9873859fd676b4d29fd3fe67c850d148` | `854fc4e89662d62932ff59f1f2eee245e9a15d84c695269e92f8f0c56bf9ae0f` |
| W5Regions | 18 | `eae5e67497e6ca48ce7cc2746cff025059fe7eeed445292d1d7d0671de4a4980` | `457fb85b0a9fe41f357d5382a142be2cdbcef4913573b28881e6d69a24fc6665` |
| W5RelativeCoefficients | 15 | `c3bf01ad93c4d94e7116ed028487c0f86f959d38560fd7fa10b9e33118761ed3` | `e325894d90d916fbd9b5f5f222721e06f9f8f1be21ea8e92123e382dd0a897e6` |
| W5RelativeObstruction | 13 | `50be3c18b85362dcd9a53dbac0052008493df2175bac6489d80337ea3c9dc2dc` | `44b96377c873e154b2e17f192750bf1e17b1417d96dde08b53beff6bbc33110a` |

| 個別公理audit module群 | 所有宣言数 | helper SHA256 | raw log SHA256 |
| --- | ---: | --- | --- |
| W5AffineInput, W5Regions, W5AuthoredOperations | 52 | `6107051298401cb8fee1469ca99edbd034ea7870c8c430d7147a5394538b7b97` | `9ff9545391a47e23949baa6d3706668d7eebc3d5fbf765634adc3080aab6caad` |
| W5ActualRepairs, W5LocalRepairs, W5ActualArrows | 48 | `8e4e825e17c9841f029b38fe0537e2651c66c716fa27e9344c2708edffe8d80a` | `2d811bf12bbaef87000f6c0c4e37c003e686f2fbef51602f5a6ae1fa149a2251` |
| W5OriginalDifferentials, W5RelativeCoefficients, W5RelativeObstruction, W5LocalCohomology, W5OverlapCohomology | 56 | `ee5753b2e86503eebd7d0ea3ea16937e21f365e26e71c86edbb27fb82d9e11bc` | `7d09811a92c2b923f636fb886279d1ab62a7bdbc8ca1eee6d788b8cab7c6aa05` |
| W5NativeDescent, W5IntegrationObstruction, W5AbsoluteCohomology, W5ActualSolvability | 52 | `823e9c0aca12cb9b981340dafa0b632a3794dd04c4e687c1258fbd4467ee7d59` | `2bab19c02b65818b38f879944bdde714c267765bf156e5693821bc173e6a4cd0` |

<details>
<summary>C27 全所有宣言208</summary>

```text
AAT.AG.AbelianLiftingObstruction.GroupExtension.pathValue.eq_def
AAT.AG.RelativeRepairComposition.ActualRelative.obstructionClass.congr_simp
AAT.AG.RelativeRepairComposition.ClosedRegion.mk.congr_simp
AAT.AG.RelativeRepairComposition.NativeAffine.vectorPath.eq_def
AAT.AG.RelativeRepairComposition.NativeCoverObstruction.omega.congr_simp
AAT.AG.RelativeRepairComposition.W5AbsoluteCohomology.absoluteCochain
AAT.AG.RelativeRepairComposition.W5AbsoluteCohomology.absoluteSupported
AAT.AG.RelativeRepairComposition.W5AbsoluteCohomology.absolute_d1_surjective
AAT.AG.RelativeRepairComposition.W5AbsoluteCohomology.absolute_d1_value
AAT.AG.RelativeRepairComposition.W5AbsoluteCohomology.absolute_h2_zero
AAT.AG.RelativeRepairComposition.W5AbsoluteCohomology.absolute_supported_surjective
AAT.AG.RelativeRepairComposition.W5AbsoluteCohomology.forgetPhysicalFace
AAT.AG.RelativeRepairComposition.W5AbsoluteCohomology.forget_actual_defect
AAT.AG.RelativeRepairComposition.W5ActualArrows.discreteValueFunctor
AAT.AG.RelativeRepairComposition.W5ActualArrows.global_label_zero
AAT.AG.RelativeRepairComposition.W5ActualArrows.local_arrow_label
AAT.AG.RelativeRepairComposition.W5ActualArrows.local_hom_unique
AAT.AG.RelativeRepairComposition.W5ActualArrows.local_object_eq
AAT.AG.RelativeRepairComposition.W5ActualArrows.overlapDiscreteEquivalence
AAT.AG.RelativeRepairComposition.W5ActualArrows.overlapFunctor
AAT.AG.RelativeRepairComposition.W5ActualArrows.overlapObjectEquiv
AAT.AG.RelativeRepairComposition.W5ActualArrows.overlap_hom_iff
AAT.AG.RelativeRepairComposition.W5ActualRepairs.ActualCategory
AAT.AG.RelativeRepairComposition.W5ActualRepairs.NativeCategory
AAT.AG.RelativeRepairComposition.W5ActualRepairs.RealRepairs
AAT.AG.RelativeRepairComposition.W5ActualRepairs.actualValueEquiv
AAT.AG.RelativeRepairComposition.W5ActualRepairs.actual_operation_apply
AAT.AG.RelativeRepairComposition.W5ActualRepairs.fromValue
AAT.AG.RelativeRepairComposition.W5ActualRepairs.from_value
AAT.AG.RelativeRepairComposition.W5ActualRepairs.nativeValueEquiv
AAT.AG.RelativeRepairComposition.W5ActualRepairs.operation_fixed
AAT.AG.RelativeRepairComposition.W5ActualRepairs.value
AAT.AG.RelativeRepairComposition.W5ActualRepairs.value_face
AAT.AG.RelativeRepairComposition.W5ActualRepairs.value_from
AAT.AG.RelativeRepairComposition.W5ActualRepairs.value_inputs
AAT.AG.RelativeRepairComposition.W5ActualRepairs.value_operations
AAT.AG.RelativeRepairComposition.W5ActualRepairs.wholeAffineEquivalence
AAT.AG.RelativeRepairComposition.W5ActualSolvability.absolute_relative_comparison
AAT.AG.RelativeRepairComposition.W5ActualSolvability.diagonal_values
AAT.AG.RelativeRepairComposition.W5ActualSolvability.four_integration_values
AAT.AG.RelativeRepairComposition.W5ActualSolvability.four_relative_values
AAT.AG.RelativeRepairComposition.W5ActualSolvability.general_a
AAT.AG.RelativeRepairComposition.W5ActualSolvability.general_b
AAT.AG.RelativeRepairComposition.W5ActualSolvability.global_iff
AAT.AG.RelativeRepairComposition.W5ActualSolvability.integrationObstruction
AAT.AG.RelativeRepairComposition.W5ActualSolvability.integration_off_diagonal
AAT.AG.RelativeRepairComposition.W5ActualSolvability.local_always
AAT.AG.RelativeRepairComposition.W5ActualSolvability.native_global_iff
AAT.AG.RelativeRepairComposition.W5ActualSolvability.off_diagonal01
AAT.AG.RelativeRepairComposition.W5ActualSolvability.off_diagonal10
AAT.AG.RelativeRepairComposition.W5ActualSolvability.omega_zero_iff
AAT.AG.RelativeRepairComposition.W5ActualSolvability.relativeObstruction
AAT.AG.RelativeRepairComposition.W5ActualSolvability.relative_off_diagonal
AAT.AG.RelativeRepairComposition.W5ActualSolvability.relative_zero_iff
AAT.AG.RelativeRepairComposition.W5ActualSolvability.repair00
AAT.AG.RelativeRepairComposition.W5ActualSolvability.repair11
AAT.AG.RelativeRepairComposition.W5AffineInput.Op
AAT.AG.RelativeRepairComposition.W5AffineInput.comparison
AAT.AG.RelativeRepairComposition.W5AffineInput.edgeA
AAT.AG.RelativeRepairComposition.W5AffineInput.edgeB
AAT.AG.RelativeRepairComposition.W5AffineInput.edgeDecidableEq
AAT.AG.RelativeRepairComposition.W5AffineInput.edgeE
AAT.AG.RelativeRepairComposition.W5AffineInput.edgeNameEquiv
AAT.AG.RelativeRepairComposition.W5AffineInput.faceDecidableEq
AAT.AG.RelativeRepairComposition.W5AffineInput.geometry
AAT.AG.RelativeRepairComposition.W5AffineInput.linear_faces
AAT.AG.RelativeRepairComposition.W5AffineInput.name
AAT.AG.RelativeRepairComposition.W5AffineInput.name_edge
AAT.AG.RelativeRepairComposition.W5AffineInput.originalTower
AAT.AG.RelativeRepairComposition.W5AffineInput.primeTwo
AAT.AG.RelativeRepairComposition.W5AffineInput.reference
AAT.AG.RelativeRepairComposition.W5AffineInput.reference_left_path
AAT.AG.RelativeRepairComposition.W5AffineInput.reference_right_path
AAT.AG.RelativeRepairComposition.W5AffineInput.vertexS
AAT.AG.RelativeRepairComposition.W5AffineInput.vertexT
AAT.AG.RelativeRepairComposition.W5AuthoredOperations.correctionValue
AAT.AG.RelativeRepairComposition.W5AuthoredOperations.face_iff
AAT.AG.RelativeRepairComposition.W5AuthoredOperations.inputValue
AAT.AG.RelativeRepairComposition.W5AuthoredOperations.left_apply
AAT.AG.RelativeRepairComposition.W5AuthoredOperations.operation
AAT.AG.RelativeRepairComposition.W5AuthoredOperations.operation_a_apply
AAT.AG.RelativeRepairComposition.W5AuthoredOperations.operation_b_apply
AAT.AG.RelativeRepairComposition.W5AuthoredOperations.operation_e_apply
AAT.AG.RelativeRepairComposition.W5AuthoredOperations.operation_linear
AAT.AG.RelativeRepairComposition.W5AuthoredOperations.reference_linear
AAT.AG.RelativeRepairComposition.W5AuthoredOperations.right_apply
AAT.AG.RelativeRepairComposition.W5AuthoredOperations.zero_translation
AAT.AG.RelativeRepairComposition.W5IntegrationObstruction.connecting_actual_difference
AAT.AG.RelativeRepairComposition.W5IntegrationObstruction.difference_class_value
AAT.AG.RelativeRepairComposition.W5IntegrationObstruction.difference_cycle_value
AAT.AG.RelativeRepairComposition.W5IntegrationObstruction.omega_independent
AAT.AG.RelativeRepairComposition.W5IntegrationObstruction.omega_original_class
AAT.AG.RelativeRepairComposition.W5IntegrationObstruction.omega_value
AAT.AG.RelativeRepairComposition.W5IntegrationObstruction.planValue
AAT.AG.RelativeRepairComposition.W5IntegrationObstruction.planValue_actual
AAT.AG.RelativeRepairComposition.W5IntegrationObstruction.planValue_input
AAT.AG.RelativeRepairComposition.W5LocalCohomology.local_cycle_zero
AAT.AG.RelativeRepairComposition.W5LocalCohomology.local_d1_surjective
AAT.AG.RelativeRepairComposition.W5LocalCohomology.local_h1_zero
AAT.AG.RelativeRepairComposition.W5LocalCohomology.local_h2_zero
AAT.AG.RelativeRepairComposition.W5LocalCohomology.region_face
AAT.AG.RelativeRepairComposition.W5LocalCohomology.region_shared
AAT.AG.RelativeRepairComposition.W5LocalRepairs.LocalCategory
AAT.AG.RelativeRepairComposition.W5LocalRepairs.LocalLabels
AAT.AG.RelativeRepairComposition.W5LocalRepairs.LocalRepairs
AAT.AG.RelativeRepairComposition.W5LocalRepairs.actualRestriction
AAT.AG.RelativeRepairComposition.W5LocalRepairs.globalAction
AAT.AG.RelativeRepairComposition.W5LocalRepairs.labels_zero
AAT.AG.RelativeRepairComposition.W5LocalRepairs.localAction
AAT.AG.RelativeRepairComposition.W5LocalRepairs.localFromValue
AAT.AG.RelativeRepairComposition.W5LocalRepairs.localName
AAT.AG.RelativeRepairComposition.W5LocalRepairs.localPlan
AAT.AG.RelativeRepairComposition.W5LocalRepairs.localValue
AAT.AG.RelativeRepairComposition.W5LocalRepairs.localValue_face
AAT.AG.RelativeRepairComposition.W5LocalRepairs.localValue_from
AAT.AG.RelativeRepairComposition.W5LocalRepairs.localValue_input
AAT.AG.RelativeRepairComposition.W5LocalRepairs.localValue_operations
AAT.AG.RelativeRepairComposition.W5LocalRepairs.local_fixed_map
AAT.AG.RelativeRepairComposition.W5LocalRepairs.local_operation_apply
AAT.AG.RelativeRepairComposition.W5LocalRepairs.local_unique
AAT.AG.RelativeRepairComposition.W5LocalRepairs.overlapValueEquiv
AAT.AG.RelativeRepairComposition.W5LocalRepairs.overlap_has_shared
AAT.AG.RelativeRepairComposition.W5LocalRepairs.overlap_no_face
AAT.AG.RelativeRepairComposition.W5LocalRepairs.patch_shared
AAT.AG.RelativeRepairComposition.W5LocalRepairs.restriction_label
AAT.AG.RelativeRepairComposition.W5LocalRepairs.restriction_operation
AAT.AG.RelativeRepairComposition.W5NativeDescent.Descent
AAT.AG.RelativeRepairComposition.W5NativeDescent.actualEquivalence
AAT.AG.RelativeRepairComposition.W5NativeDescent.descent_is_groupoid
AAT.AG.RelativeRepairComposition.W5NativeDescent.left_choice
AAT.AG.RelativeRepairComposition.W5NativeDescent.left_label
AAT.AG.RelativeRepairComposition.W5NativeDescent.localAffineEquivalence
AAT.AG.RelativeRepairComposition.W5NativeDescent.localObjectEquiv
AAT.AG.RelativeRepairComposition.W5NativeDescent.nativeEquivalence
AAT.AG.RelativeRepairComposition.W5NativeDescent.nativeLocalPlan
AAT.AG.RelativeRepairComposition.W5NativeDescent.nativeOverlapDiscreteEquivalence
AAT.AG.RelativeRepairComposition.W5NativeDescent.native_local_label_zero
AAT.AG.RelativeRepairComposition.W5NativeDescent.right_choice
AAT.AG.RelativeRepairComposition.W5NativeDescent.right_label
AAT.AG.RelativeRepairComposition.W5NativeDescent.seam_label
AAT.AG.RelativeRepairComposition.W5OriginalDifferentials.d0_value
AAT.AG.RelativeRepairComposition.W5OriginalDifferentials.d1_value
AAT.AG.RelativeRepairComposition.W5OriginalDifferentials.d2_zero
AAT.AG.RelativeRepairComposition.W5OriginalDifferentials.defect_coordinate
AAT.AG.RelativeRepairComposition.W5OriginalDifferentials.kernelCoordinate
AAT.AG.RelativeRepairComposition.W5OriginalDifferentials.kernel_inverse_value
AAT.AG.RelativeRepairComposition.W5OriginalDifferentials.original_linear
AAT.AG.RelativeRepairComposition.W5OriginalDifferentials.original_transport
AAT.AG.RelativeRepairComposition.W5OriginalDifferentials.translation_inverse_apply
AAT.AG.RelativeRepairComposition.W5OverlapCohomology.boundary_range_bot
AAT.AG.RelativeRepairComposition.W5OverlapCohomology.cycleCoordinate
AAT.AG.RelativeRepairComposition.W5OverlapCohomology.h1Coordinate
AAT.AG.RelativeRepairComposition.W5OverlapCohomology.h1Coordinate_class
AAT.AG.RelativeRepairComposition.W5OverlapCohomology.localImages_bot
AAT.AG.RelativeRepairComposition.W5OverlapCohomology.omegaCoordinate
AAT.AG.RelativeRepairComposition.W5OverlapCohomology.omegaCoordinate_class
AAT.AG.RelativeRepairComposition.W5OverlapCohomology.omegaOriginalH2Equiv
AAT.AG.RelativeRepairComposition.W5OverlapCohomology.overlap_d1_zero
AAT.AG.RelativeRepairComposition.W5OverlapCohomology.overlap_shared
AAT.AG.RelativeRepairComposition.W5OverlapCohomology.restrictionKernelEquiv
AAT.AG.RelativeRepairComposition.W5OverlapCohomology.restriction_zero
AAT.AG.RelativeRepairComposition.W5Regions.alwaysEdges
AAT.AG.RelativeRepairComposition.W5Regions.candidates
AAT.AG.RelativeRepairComposition.W5Regions.edge_partition
AAT.AG.RelativeRepairComposition.W5Regions.face_in_region
AAT.AG.RelativeRepairComposition.W5Regions.fixedRegion
AAT.AG.RelativeRepairComposition.W5Regions.inputEdge
AAT.AG.RelativeRepairComposition.W5Regions.leftRegion
AAT.AG.RelativeRepairComposition.W5Regions.overlap
AAT.AG.RelativeRepairComposition.W5Regions.overlap_edges
AAT.AG.RelativeRepairComposition.W5Regions.overlap_faces
AAT.AG.RelativeRepairComposition.W5Regions.overlap_vertices
AAT.AG.RelativeRepairComposition.W5Regions.region
AAT.AG.RelativeRepairComposition.W5Regions.region_edges
AAT.AG.RelativeRepairComposition.W5Regions.region_vertices
AAT.AG.RelativeRepairComposition.W5Regions.regions_cover
AAT.AG.RelativeRepairComposition.W5Regions.rightRegion
AAT.AG.RelativeRepairComposition.W5Regions.shared_in_both
AAT.AG.RelativeRepairComposition.W5Regions.shared_not_fixed
AAT.AG.RelativeRepairComposition.W5RelativeCoefficients.actualDefect
AAT.AG.RelativeRepairComposition.W5RelativeCoefficients.actualDefect_value
AAT.AG.RelativeRepairComposition.W5RelativeCoefficients.cochain
AAT.AG.RelativeRepairComposition.W5RelativeCoefficients.cochain_d1_value
AAT.AG.RelativeRepairComposition.W5RelativeCoefficients.cochain_reconstruct
AAT.AG.RelativeRepairComposition.W5RelativeCoefficients.cochain_value
AAT.AG.RelativeRepairComposition.W5RelativeCoefficients.d1_value
AAT.AG.RelativeRepairComposition.W5RelativeCoefficients.d2_zero
AAT.AG.RelativeRepairComposition.W5RelativeCoefficients.edgeCoordinate
AAT.AG.RelativeRepairComposition.W5RelativeCoefficients.edgeCoordinates
AAT.AG.RelativeRepairComposition.W5RelativeCoefficients.faceCoordinates
AAT.AG.RelativeRepairComposition.W5RelativeCoefficients.fixed_coordinate
AAT.AG.RelativeRepairComposition.W5RelativeCoefficients.fixed_faces
AAT.AG.RelativeRepairComposition.W5RelativeCoefficients.fullCochain
AAT.AG.RelativeRepairComposition.W5RelativeCoefficients.vertex_zero
AAT.AG.RelativeRepairComposition.W5RelativeObstruction.actualCycle
AAT.AG.RelativeRepairComposition.W5RelativeObstruction.actualCycle_original
AAT.AG.RelativeRepairComposition.W5RelativeObstruction.actual_class_comparison
AAT.AG.RelativeRepairComposition.W5RelativeObstruction.actual_obstruction_value
AAT.AG.RelativeRepairComposition.W5RelativeObstruction.boundary_range_eq_kernel
AAT.AG.RelativeRepairComposition.W5RelativeObstruction.cycleOfFace
AAT.AG.RelativeRepairComposition.W5RelativeObstruction.h2Coordinate
AAT.AG.RelativeRepairComposition.W5RelativeObstruction.h2Coordinate_class
AAT.AG.RelativeRepairComposition.W5RelativeObstruction.originalH2Coordinate
AAT.AG.RelativeRepairComposition.W5RelativeObstruction.original_syzygy
AAT.AG.RelativeRepairComposition.W5RelativeObstruction.reading
AAT.AG.RelativeRepairComposition.W5RelativeObstruction.reading_surjective
AAT.AG.RelativeRepairComposition.W5RelativeObstruction.reading_value
AAT.AG.RelativeRepairComposition.pathEdges.eq_def
```

</details>
