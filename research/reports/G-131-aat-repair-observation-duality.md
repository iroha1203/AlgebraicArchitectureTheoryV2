# G-131：修復・観測双対性の証拠対応

固定入力は [GOAL](../goals/G-131-aat-repair-observation-duality.md) のA–Eと
n1017 §3.5・§6、構成方針は [設計](../designs/G-131-aat-repair-observation-duality/README.md)
および [G-130再利用対応](../designs/G-131-aat-repair-observation-duality/reuse-map.md) にある。
進行状態は [Issue #5133](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5133) に集約する。

## Cycle 1：同じ方程式の情報fiberと出力十分性

```yaml
ledger_type: target_cycle_result
goal: G-131-aat-repair-observation-duality
cycle: 1
goal_blob_sha: 054fea81b916c4d4a470b74af3e13c6cc5dde01c
base_oid: 5d62ddb3df87fd0ef55b4a8222692d7f19124258
tracking_issue: 5133
report_path: research/reports/G-131-aat-repair-observation-duality.md
selection:
  proof_state_ref: "Issue #5133の初期状態、A–E未着手"
  proof_dag_predecessors: [LinearInterface.q, Submodule.Quotient.mk_eq_zero]
  milestone: "Cの一般情報fiberと線形情報fiberにおける判定・数値出力の十分性の特徴づけ"
  proof_obligations: ["任意の情報fiberで観測同値と判定因子化を対応", "補正または不能という数値出力を独立定義し、各観測fiberの同一右辺条件と対応", "成功基準点からの平行移動で両出力の核包含を証明"]
  exit_criteria: ["一般情報fiberの判定・数値十分性を両方向証明", "非空線形fiberで同じDとBの核条件を両方向証明", "対象宣言のfocused check、公理、placeholder、Unicode、privacy、import方向確認"]
  selection_reason: "Cの数値出力の必要情報を同じ方程式から導き、適応的下限と値取得へ接続する"
  expected_result_type: proof-obligation-discharged
  lean_targets: [ResearchLean/AG/RepairObservationDuality/FiberSufficiency.lean]
  risks: ["出力hの全値を確定し、後評価式を混ぜない", "不能出力の正確性を存在の否定として定義", "成功基準点は一般定理の方向仮定、有限計画での生成は後続義務"]
  unchecked: ["実装・検証・査読前"]
```

全体判定は未完了。Aの実入力接続、Bの作用・双対・手続き対応、Cの適応的下限と最小達成、
Dの有限計画と不能証拠取得、Eの全指定例は後続義務である。

### 宣言と同じ方程式の対応

宣言は `AAT.AG.RepairObservationDuality`、sourceは
`research/lean/ResearchLean/AG/RepairObservationDuality/FiberSufficiency.lean`。

| 固定要求の部分 | 宣言と使用経路 |
| --- | --- |
| Cの一般情報fiber・判定可否一定 | `DecisionSufficient`, `decision_sufficient_iff`。等観測入力の可否一定から観測上の述語を生成 |
| Cの一般情報fiber・数値出力 | `ValidOutput`, `NumericalSufficient`, `numerical_sufficient_iff`。返却した同じ補正から同じ右辺を導き、逆は観測fiberの可解代表元の補正を選ぶ |
| 同じ線形方程式の商零判定 | `affineRhs`, `obstruction`, `solvable_iff_obstruction_zero`。native商の零と同じDの像所属を対応 |
| Cの線形情報と成功基準点 | `informationFiber`, `mem_fiber_sub`, `add_mem_fiber`, `solvable_add_iff`。全fiberと核方向の双方向を同じL・B・Dで扱う |
| Cの判定十分性の核条件 | `decision_sufficient_linear_iff`。成功基準点の可否と応答一致、逆は差の障害零 |
| Cの数値十分性の核条件 | `numerical_sufficient_linear_iff`。同じ補正の右辺一致からBn=0、逆は全右辺の一致 |
| 出力条件の非空虚性とinstanceペア | `decision_numerical_differ`。任意の体でD=B=id、全fiber・定数観測について、判定十分性と数値不十分性が同時成立。`decision_sufficient_fails`, `numerical_sufficient_identity`, `solvable_zero_not_one`, `valid_output_examples` で全新規述語の成立・不成立を提供 |

受理spine候補は `decision_sufficient_iff`, `numerical_sufficient_iff`,
`decision_sufficient_linear_iff`, `numerical_sufficient_linear_iff`。
残る宣言は上表の入力定義・API・発火例であり、cycle scaffoldはない。
`solvable_congr_rhs`, `affineRhs_sub`, `affineRhs_eq_iff`, `obstruction_sub` は
等号・差の基本APIであり、線形主定理は定義内部を展開せずこれらを用いる。

| material premise | 役割 | 出所・使用先 |
| --- | --- | --- |
| F、obs、D、rhs（一般部分） | ambient-boundary | Cの一般情報fiberと方程式の入力。等観測と出力の因子化へ |
| 体k、module構造、線形D/B/L/O、b₀/s（線形部分） | ambient-boundary | Cの線形方程式と既知情報。差・核・native商に使用。有限体・有限次元という対象の条件より一般的な補題 |
| wの情報fiber所属と可解性 | direction-hypothesis | Cの成功基準点がある場合という条件分け。核方向の入力の可解性、同じ数値出力の必要性へ。Dの有限計画での成功点生成は未着手 |
| 観測上の述語と完全な補正出力 | discharge-required、構成済み | 一般十分性の逆向き証明で生成。数値出力の生成には存在証明でのchoiceを使う。停止する有限計画は後続義務 |
| native商零と同じ方程式の可解性 | discharge-required、証明済み | `Submodule.Quotient.mk_eq_zero` とDの像定義 |
| 原始族からb₀/B/Dを生成し実操作へ復元 | discharge-required、未接続 | A・D・Eの後続義務。今回の線形補題では入力として与えられた同じ方程式を調べる |

標準基盤は固定Mathlib `8f9d9cff6bd728b17a24e163c9402775d9e6a365` の
`LinearAlgebra/Quotient/Defs.lean` の `Submodule.Quotient.mk_eq_zero`、
`LinearMap.range`、加法moduleとkernel API。
G-130・G-128のResearch宣言への依存はこのcycleにない。実操作との接続は後続義務として残す。

```yaml
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "Cの一般観測fiberの両出力条件と、成功基準点のある線形fiberの2種類の核条件を双方向証明"
  exit_criteria_status: ["一般判定・数値条件を双方向証明", "同じD/B/L/Oによる線形核条件を双方向証明", "24宣言のfocused checkと標準公理監査・scanを実行"]
  split_reason: none
  completion_candidate: no
  lean_artifacts: [FiberSufficiency.lean]
  evidence: [decision_sufficient_iff, numerical_sufficient_iff, decision_sufficient_linear_iff, numerical_sufficient_linear_iff, decision_numerical_differ]
  claim_mapping:
    theorem_names: [decision_sufficient_iff, numerical_sufficient_iff, solvable_iff_obstruction_zero, mem_fiber_sub, add_mem_fiber, solvable_add_iff, decision_sufficient_linear_iff, numerical_sufficient_linear_iff, decision_numerical_differ]
    source_labels: ["G-131 Cの一般情報fiberと成功点のある線形情報fiber", "n1017 §6.4・§6.5"]
    conjuncts: ["観測可否一定↔判定因子化", "可否一定・可解fiber右辺一定↔完全数値出力因子化", "判定十分性↔ker L∩ker O≤ker(qB)", "数値十分性↔ker L∩ker O≤ker B"]
    undischarged_assumptions: []
    acceptance_point: "Cの出力十分性という到達点。Cの最悪時最適値・有限達成は後続義務"
    port_status: unported
audits:
  premise_delta:
    discharged: ["一般fiberの観測述語・完全補正値出力", "線形fiberの成功点からの核方向条件"]
    remaining: ["Aの同じ実入力からの行列生成", "C/Dの成功点と最小計画の有限生成", "Bの作用・双対・回数対応", "Eの全指定入力"]
  certificate_provenance:
    discharged: ["観測上のp/outを一般条件から生成。結論相当fieldを導入しない"]
    unresolved: ["実操作への復元と有限計画は後続義務"]
  proof_use:
    used: ["同じ数値出力→同じD h→右辺一致", "wの成功→核方向の成功条件", "L/O線形性→fiber差と応答一致", "native商零→D像所属"]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: ["focused checkと24宣言#print axiomsのコマンド・出力hashをPRコメントへ固定"]
  blocking_findings: []
  next_obligation: "原始線形問い合わせ手続きの応答列再現、成功点実行からの2種類の下限、最小固定集合からの達成"
```

## Cycle 2：原始問い合わせの適応的下限と固定集合による最適値

```yaml
ledger_type: target_cycle_result
goal: G-131-aat-repair-observation-duality
cycle: 2
goal_blob_sha: 054fea81b916c4d4a470b74af3e13c6cc5dde01c
base_oid: e0da0c6cfc5b2761946de0cf945a27d00846b3c7
tracking_issue: 5133
report_path: research/reports/G-131-aat-repair-observation-duality.md
selection:
  proof_state_ref: "Cycle 1受理、Issue #5133 comment 5969041587"
  proof_dag_predecessors: [solvable_add_iff, decision_sufficient_linear_iff, numerical_sufficient_linear_iff]
  milestone: "Cの原始問い合わせモデルで、成功点の応答列再現と最小固定集合による判定/数値最悪時最適値"
  proof_obligations: ["履歴だけから次質問または完全出力を選ぶ決定的実行", "同じ応答列の再現と繰り返しを含む回数", "成功点実行から両核条件の下限", "十分固定集合から常時停止・正答・濃度回数の達成", "最悪時最適値と最小十分集合濃度の一致・無限大・全不能零回"]
  exit_criteria: ["同じ質問/応答/出力で下限・達成を証明", "2種類の線形核包含と正しいOptimumの同値", "十分集合がない場合の不存在と全不能の零回", "単一file focused checkと全宣言公理・scan"]
  selection_reason: "Cの十分性を適応的手続き全体の最適値へ進める"
  expected_result_type: proof-obligation-discharged
  lean_targets: [ResearchLean/AG/RepairObservationDuality/PrimitiveQueries.lean, ResearchLean/AG/RepairObservationDuality/QueryOptimum.lean]
  risks: ["質問以外で未知値を読まない", "数値出力の全hが確定する", "一般の存在最適値とDの有限計画生成の構成性を区別", "成功点を有限に探すDと実入力の全実現A/Eは後続"]
  unchecked: ["実装・検証・独立査読前"]
```

### Cycle 2の宣言・前提・構成経路

`PrimitiveQueries.lean` の名前空間は
`AAT.AG.RepairObservationDuality.PrimitiveQueries`、`QueryOptimum.lean` は
`AAT.AG.RepairObservationDuality`。

| 要求 | 宣言・証明経路 |
| --- | --- |
| Cの決定的な履歴だけの手続き | `History`, `Procedure`, `Run`, `Correct`。nextの入力は履歴だけ。出力型は判定ではBool、数値ではOption H。`Run.deterministic` が全出力と全質問列の一意性を証明 |
| 成功入力の応答列を再現する下限 | `Run.replay`, `decision_run_sufficient`, `numerical_run_sufficient`。w+nを同じL-fiberに構成し、全質問の応答一致から同じ完全出力を再現。前者は成功の一致、後者は同じD hの右辺一致を使う |
| 原始索引の十分性と最小値 | `observation`, `mem_ker_observation`, `observation_eq_iff`, `SufficientSet`, `minimum`。索引はJの有限部分集合であり、作用対象の点ではない |
| 繰り返しを含む全適応手続きの下限 | `run_le_worst`, `minimum_le_run`。distinct索引のcard≤実質問listのlength≤worst。totalnessから成功点の実行を取り出す |
| 最小固定集合と完全出力の生成・達成 | `finish_valid`, `fixed_run`, `fixed_correct`, `worst_fixed_le`, `decision_fixed_correct`, `numerical_fixed_correct`, `minimum_attained`, `decision_optimum_attained`, `numerical_optimum_attained`。応答fiber全体に正しい共通値を既知のモデルから選び、固定listのちょうどlength回で返す |
| Cの二種類の正確な最適値 | `decision_optimum`, `numerical_optimum`。独立定義した全correct procedureのworstのinfimumと、核包含を満たすFinsetのcardのinfimumの両方向を証明 |
| 十分集合がない場合 | `minimum_eq_top_iff`, `no_decision_procedure`, `no_numerical_procedure`。空infimum=∞と、total correct adaptive procedureそのものの不存在を証明。具体的な実操作の識別不能対はA・D・Eの後続接続 |
| 全不能fiber | `constant_run`, `constant_correct`, `worst_constant`, `optimum_zero_of_constant`, `all_impossible_optima_zero`。false/noneを完全出力として零回で返す |
| 新規述語の成立・不成立 | `run_examples`, `correct_examples`, `sufficient_set_examples`, `valid_decision_examples`。同じ非空入力集合で正答/誤答を区別し、恒等primitiveを持つ同じ体で全集合/空集合を区別 |

受理spine候補は `Run.replay`, `decision_run_sufficient`, `numerical_run_sufficient`,
`decision_optimum`, `numerical_optimum`, `decision_optimum_attained`,
`numerical_optimum_attained`, `no_decision_procedure`, `no_numerical_procedure`,
`all_impossible_optima_zero`。他の宣言は上表の同じ構成・基本API・例であり、
cycle scaffoldはない。最適値の主証明は手続き内部を展開せず基本APIを用いる。

| material premise | 分類と放電 | 出所・使用先 |
| --- | --- | --- |
| k/module/同じD,B,b₀,L,sと原始評価lam | ambient-boundary | Cの既知構造。有限体・有限次元・有限Jより一般的に証明。未知入力vはnextへの引数ではない |
| w∈F_sと同じ方程式の可解性 | direction-hypothesis | Cの成功入力がある場合。w+nの可否または全RHS一致へ。有限な成功点探索はDの後続義務 |
| 手続きの全入力停止・常時正答 | ambient-boundary（手続き全体を定義するモデル） | `optimum` の範囲。下限では成功点のrunと両入力の出力正答、上限では生成したfixedのcorrectnessを証明して範囲に入れる |
| 成功点の実行再現と核下限 | discharge-required、証明済み | 同じlamの線形性、Lの核、Cycle 1の`solvable_add_iff`、同じhからのRHS一致 |
| 最小固定集合と完全出力 | discharge-required、存在構成済み | ENatの非空infimum達成とCycle 1の両十分性。`finish`は既知モデル上の共通出力をchoiceで選ぶ存在手続き。有限データからの実行可能な列挙はDの後続義務 |
| 全実入力の実現・原始操作での実評価・修復復元 | discharge-required、未接続 | A・D・Eの後続義務。このcycleでは同じ線形方程式と原始線形評価上のquery modelを扱う |

G-128の最適値定理を単に呼ぶのではなく、Cの既知fiber・完全な数値出力を対象に
応答列再現を証明した。G-128への作用・観測手続き対応はBの後続義務である。
G-130の実微分・実現・復元への依存はまだない。標準基盤は固定Mathlibの
`Mathlib/Data/ENat/Lattice.lean` の `ENat.exists_eq_iInf` とcomplete lattice API。

```yaml
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "Cの同じ線形方程式・原始線形評価で、全適応手続きの両下限、最小固定集合からの達成、両最適値、∞と手続き不存在、全不能零回を証明"
  exit_criteria_status: ["成功点の同じ応答・全出力を再現", "distinct濃度とrepeatを含むlengthの下限", "最小固定集合・correct procedure・正確なworstの達成", "空計画族の∞とcorrect procedure不存在", "全不能false/noneの零回", "focused check・公理監査・scanをPRコメントへ固定"]
  split_reason: none
  completion_candidate: no
  lean_artifacts: [PrimitiveQueries.lean, QueryOptimum.lean]
  evidence: [Run.replay, decision_optimum, numerical_optimum, decision_optimum_attained, numerical_optimum_attained, no_decision_procedure, no_numerical_procedure, all_impossible_optima_zero]
  claim_mapping:
    theorem_names: [decision_run_sufficient, numerical_run_sufficient, decision_optimum, numerical_optimum, decision_optimum_attained, numerical_optimum_attained, no_decision_procedure, no_numerical_procedure, all_impossible_optima_zero]
    source_labels: ["G-131 Cの線形既知情報下の最悪時最適値", "n1017 §6.4・§6.5"]
    conjuncts: ["判定最適値=min N∩ker O≤ker(qB)", "数値最適値=min N∩ker O≤ker B", "有限値で最小固定集合が正確な最悪時回数を達成", "十分集合なしでは∞かつcorrect procedure不存在", "全不能なら両出力零回"]
    undischarged_assumptions: []
    acceptance_point: "線形query modelでのCの最適値という到達点。実操作の実現・Dの有限生成は後続"
    port_status: unported
audits:
  premise_delta:
    discharged: ["応答再現と両下限", "最小集合からの同じprimitiveの達成手続き", "∞と手続き不存在", "全不能零回"]
    remaining: ["Aの実入力と任意Sの商・同じG-130への接続", "Bの作用・双対・G-128の手続き対応", "Dの有限列挙・不能証拠の値取得・復元", "Eの全指定例と実操作への適用"]
  certificate_provenance:
    discharged: ["fixedの共通全出力はCycle 1の独立十分性から生成", "下限では外部certificateでなくwの実行を再現", "最小集合はcardのinfimum達成から生成"]
    unresolved: ["Dの実行可能な有限計画生成は後続義務"]
  proof_use:
    used: ["成功基準点", "同じlam応答", "全入力停止と正答", "同じ数値hが両方のD hを確定", "全repeatのlength"]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: ["コマンド・全明示宣言の#print axiomsと出力hashをPRコメントへ固定"]
  blocking_findings: []
  next_obligation: "Aの一般原始入力から同じD_S・負defect・修復の往復と任意Sの商同型"
```

全体判定は `target-proof-checkpoint`。A、B、D、EおよびCの実入力への接続は未完了。
`target-theorem-proved` としていない。
