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
`valid_decision_decide_iff` はBoolean値と独立な可解性を結ぶ基本APIであり、
`decision_fixed_correct` は同補題を使って判定validator内部の展開を避ける。

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

## Cycle 3：任意の元候補範囲の商と実修復方程式

```yaml
ledger_type: target_cycle_result
goal: G-131-aat-repair-observation-duality
cycle: 3
goal_blob_sha: 054fea81b916c4d4a470b74af3e13c6cc5dde01c
base_oid: 68565e9c8156fc3e15f4546b6cef11785efb3010
tracking_issue: 5133
report_path: research/reports/G-131-aat-repair-observation-duality.md
selection:
  proof_state_ref: "Cycle 2受理・merge、Issue #5133 comment 5969349037。限定確認中に別worktreeで選定後、受理mergeへfast-forward同期。今回の証明依存は受理済みG-130"
  proof_dag_predecessors: [OriginalRanges.objects_nonempty_iff_equation, SupportedNativeEquation.repairEquiv, NamedDual.sumSelected, CokernelNamed.quotient_sum]
  milestone: "Aの任意Sに対するD_S・native cokernelと同じ面代表元の残存商を構成し、G-130の同じ実修復方程式と往復を接続"
  proof_obligations: ["常時列とSの元名全列の線形D_S", "range D_Sと元列像和の一致", "coker D_S≃O/R_Sと同じ面代表元の保存", "独立な実修復可否↔同じD_S方程式↔商零", "同じ実辺値と禁止候補零を保つ復元"]
  exit_criteria: ["全Sで代表元保存を含む商同型", "一般のG-130原始塔と同じ係数で実可否の両方向", "全元辺値の復元と禁止値零", "focused checkと全明示宣言の公理・scan"]
  selection_reason: "再利用mapの全候補商と任意Sの差を閉じ、Cの同じDに実修復を接続する"
  expected_result_type: proof-obligation-discharged
  lean_targets: [SelectedCokernel.lean, NativeCorrectionEquation.lean]
  risks: ["全候補のsecondQuotientだけで任意Sを済ませない", "元名を別のeffective列へ改名しない", "係数は任意の頂点module", "一般族のアフィンdefect生成・基底座標・局所公開関係・全実現は別の未完義務として保持"]
  unchecked: ["構成・検証・独立査読前"]
```

### Cycle 3の同じ元座標・実操作への対応

| 固定Aの部分 | 宣言・構成と使用経路 |
| --- | --- |
| 全Sの元候補列のD_S | `SelectedCokernel.differential` はD₀と`NamedDual.sumSelected C S`のcoprod。domainはX×全selected係数。`differential_apply`, `range_differential`, `equation_iff` が元split equationと全像を同定 |
| 任意Sの商と同じ面代表元 | `selected_ranges_eq` がSの元列の像をalways quotientへ写す。`residualToNative`はこのSの像へthird isomorphismを適用し、`nativeToResidual`が指定方向。両`*_value`が同じrを保つ。全候補`secondQuotient`を任意Sへ読み替えていない |
| 一般の原始塔と同じ微分・商 | `NativeCorrectionEquation.Values`, `differential`, `cokernelEquiv`, `cokernelEquiv_value`。Tの各頂点の実核moduleを使う。共通moduleのアフィン自己同型だけに対象を縮小しない |
| 独立実修復↔同じD_S方程式↔商零 | `actual_equation_iff`, `actual_cokernel_iff`。G-130の独立なSupportedRepairとsupported原始方程式のequivから、元負defectで両方向を証明 |
| 全辺補正と元実操作へ復元 | `restore`, `restore_value`, `restore_forbidden_zero`, `restore_fixed_arrow`。常時cochainと元候補値をG-130のrestoreへ渡し、native repairEquivの逆で実操作へ戻す。全元辺で同じ補正、禁止候補零、P/禁止候補の実射等号を保つ |
| emptyとallを混同しない発火例 | `SelectedCokernel.empty_full_differ`。同じ非零体・同じ恒等元列で、空Sのq_S(1)≠0、全Sのq_S(1)=0を同時に証明 |

全新規宣言は名前空間 `AAT.AG.RepairObservationDuality.SelectedCokernel` と
`AAT.AG.RepairObservationDuality.NativeCorrectionEquation`、同名の2 sourceにある。
受理spine候補は `selected_ranges_eq`, `nativeToResidual_value`,
`cokernelEquiv_value`, `actual_equation_iff`, `actual_cokernel_iff`, `restore_value`,
`restore_forbidden_zero`, `restore_fixed_arrow`。他は同じ構成・基本API・発火例で、
cycle scaffoldなし。商比較は全クラスの線形同型であり、零判定だけの対応ではない。

| material premise | 役割・出所・proof-use |
| --- | --- |
| D₀、元名E、全係数Y_e、有限E、C_e（商の一般部） | ambient-boundary。Aの同じ常時列・元候補列。Sをdomainで制限し、像とquotientを構成 |
| 原始塔Tのcore/実射/強い辺/可換核/全単射輸送/比較中央化 | ambient-boundary。固定G-130の同じOriginalTowerPresentation入力。repairEquivによる元実射と独立方程式の接続に使用 |
| 全核module、線形核輸送、P外候補、有限元辺、P面整合 | ambient-boundary。Aの同じ線形化条件と固定部分。OriginalColumns、OriginalRangesとnative復元の適用に使用 |
| D_Sと任意Sの商同型 | discharge-required、構成済み。coprod/selected sum→像等式→第三同型→同じr保存を証明。結論相当fieldなし |
| 実修復可否と方程式の接続 | discharge-required、証明済み。G-130 repairEquiv→元split equation→同じD_S→range商零 |
| hが同じ方程式を満たすhh | direction-hypothesis（復元APIの入力）。h.1/h.2でsupported元方程式を構成後、同じ実修復へ復元。未知入力の正答が原始query引数になったものではない |
| 一般原始族のアフィン負defect、共通係数・基底座標、全実現/原始実評価、局所公開関係 | discharge-required、後続。今回のpointwise塔の方程式だけではA全体を完了にしない |

受理済みpredecessorはG-130最終head `549b7e3ccab1c9686a108530e1b0a4b4f38eee86`
（[最終監査](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5179#issuecomment-5966982329)）。
今回使用する同じsignature・条件・適用引数・proof-useをsourceで読み、以下のsourceは
その受理版から変更なしであることを確認した。

| source / 主な使用API | blob SHA |
| --- | --- |
| OriginalRangeEquations / objects_nonempty_iff_equation、restore、selected_zero | `6c5e76f679602d39361c1006014d6df6dbf48781` |
| SupportedNativeEquation / repairEquiv、repair_inverse_value | `36799438b8ada7112e94a6ef86ad188e965ee78a` |
| OriginalCandidateColumns / alwaysSpace、D、column | `a5e1175924288dad89b5c5bc63866f2b48022c8a` |
| CokernelNamedRanges / quotient_sum、column、mem_iff_equation | `8d1ee72b0bbb421cb0e4c2a67bde3972b44bdb74` |
| NamedColumnSum / sumSelected、mem_ranges_iff_sum | `42f243b3be690b2363bd0d81b112a29b5a2655f2` |

Mathlibは固定pin `8f9d9cff6bd728b17a24e163c9402775d9e6a365`。
`LinearMap.range_coprod`, `Submodule.quotEquivOfEq`,
`Submodule.quotientQuotientEquivQuotientSup`, `Submodule.Quotient.mk_eq_zero` を
同じmodule・像・分母に適用する。先行G-130の内部を再認定することではなく、
今回の同じ元名・原始係数・実復元への適用を確認した。

```yaml
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "Aの任意SのD_S・full native cokernelと元O/R_Sの同じ面代表元の同型を構成し、一般原始塔の実可否・全辺復元・禁止値零・固定実射へ接続"
  exit_criteria_status: ["全SでD_Sと全像を構成", "両向き商同型・同じr保存", "同じ原始塔の実可否↔方程式↔商零", "全元辺補正・禁止値零・固定実射を復元", "2filefocused・全明示宣言公理・scanをPRへ固定"]
  split_reason: none
  completion_candidate: no
  lean_artifacts: [SelectedCokernel.lean, NativeCorrectionEquation.lean]
  evidence: [nativeToResidual_value, actual_equation_iff, actual_cokernel_iff, restore_value, restore_forbidden_zero, restore_fixed_arrow, empty_full_differ]
  claim_mapping:
    theorem_names: [selected_ranges_eq, nativeToResidual_value, cokernelEquiv_value, actual_equation_iff, actual_cokernel_iff, restore_value, restore_forbidden_zero, restore_fixed_arrow]
    source_labels: ["G-131 Aの任意Sの商と元実修復方程式", "n1017 §3.5・§6.1"]
    conjuncts: ["同じ原始列のD_S", "coker D_S≃O/R_S、同じ面代表元", "全Sの独立実修復↔同じ負defectの方程式↔商零", "全辺値と禁止候補・固定射の復元"]
    undischarged_assumptions: []
    acceptance_point: "Aのpointwise原始塔から任意Sの同じ方程式・商・復元への接続という到達点。Aの一般入力族全体は後続"
    port_status: unported
audits:
  premise_delta:
    discharged: ["任意Sの商・同じ面代表元", "一般原始塔の同じ実修復可否", "全元辺補正・禁止候補・固定射の復元"]
    remaining: ["一般原始族のアフィン負defectと共通係数・基底座標", "全実現・原始実評価・局所公開関係", "Bの作用・双対・G-128手続き", "Dの有限計画・証拠取得", "Eの全指定例"]
  certificate_provenance:
    discharged: ["選択domainのcoprodからD_S生成", "selected元列像から第三商生成", "同じ元方程式からG-130実修復復元"]
    unresolved: ["有限計画からの観測取得済み数値h生成は後続"]
  proof_use:
    used: ["全元係数と候補名", "原始塔と線形条件", "P面整合", "同じhhから元split equation", "h.1/h.2から全元辺値"]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: ["focused・全明示#print axiomsとhash・scanをPRコメントへ固定"]
  blocking_findings: []
  next_obligation: "一般原始族の共通係数と実経路からのアフィン負defect、同じ基底座標・局所公開可否、Cへの入力接続"
```

全体は `target-proof-checkpoint`。Aの一般族と数値座標・局所関係、B、D、Eは未完了。

## Cycle 4：一般の実核における原始アフィンdefect生成

```yaml
ledger_type: target_cycle_result
goal: G-131-aat-repair-observation-duality
cycle: 4
goal_blob_sha: 054fea81b916c4d4a470b74af3e13c6cc5dde01c
base_oid: 9de2ec4efe0eb737b73b54512a2807e1413f705c
tracking_issue: 5133
report_path: research/reports/G-131-aat-repair-observation-duality.md
selection:
  proof_state_ref: "Cycle 3受理・merge、Issue #5133 comment5969577603"
  proof_dag_predecessors: [TowerPresentation.correctedDefect_eq, TowerPresentation.correctedFaceDefect_eq_raw, FiniteCoefficients.d1_smul]
  milestone: "Aの一般圏・頂点ごとの実核について、基準辺と比較のアフィン原始変化から同じ実経路のraw defectと負defectの線形項を生成"
  proof_obligations: ["同じ実基準辺を核で変化させる原始TransportData", "同じ比較の核変化", "実合成からdelta+eta+d1thetaの導出", "同じ全実核係数と線形輸送からB生成", "固定面での消失から同じ相対負defect生成", "実操作の元辺値・面値と生成cochainの対応"]
  exit_criteria: ["任意圏の原始塔・頂点ごとの実核でraw defect評価等式", "生成Bの線形性と同じ相対値", "全元辺・面の実操作への対応", "focused check・全明示宣言公理・scan"]
  selection_reason: "共通moduleのNativeAffineだけでは未放電だった一般実経路のアフィンdefect生成を閉じる"
  expected_result_type: proof-obligation-discharged
  lean_targets: [PrimitiveAffineDefect.lean, RelativeAffineDefect.lean]
  risks: ["defectのアフィン性そのものを入力fieldへ移さない", "全実核を共通moduleへ置換しない", "元原始族と構成モデルの対応・基底座標・局所公開可否は別の接続義務として保持"]
  unchecked: ["構成・検証・独立査読前"]
```

### Cycle 4の構成・証拠対応

このcycleの証拠は `PrimitiveAffineDefect` と `RelativeAffineDefect`。
任意圏の原始塔Tの各頂点にある全実核を使用する。原始変更θは元辺ごとの実核値、
ηは元面ごとの実核値への線形パラメータ写像であり、defectのアフィン性そのものを
fieldや仮定として受け取らない。物理的な基準辺の変化はTの選択実辺の後置核補正、
比較の変化は同じ面核の左積として与える。この表示と外部の元原始族F・各OriginalTower
の対応は後続接続義務であり、今回の構成モデルだけでA全体を完了としない。

| 到達点 | 宣言と生成・使用経路 |
| --- | --- |
| 元辺と比較の実操作 | `data`, `edge_value`, `comparison_value`。同じ対象・元辺・面を保持し、strongな変更後の実辺を生成 |
| 同じ実合成のraw defect | `canonical_eq` は変更後の実両経路のstrong一意性で同じcanonical比較を同定。`raw_defect`, `defect_inclusion` は同じraw値を全実核に戻す |
| ネイティブアフィンdefect | `defect_eq`, `faceDifferential`, `linearTerm`, `affine_defect`, `affine_inclusion`。実補正微分からδ₀+η+d¹θを導出し線形項を生成 |
| 固定面の消失 | `defect_zero_iff`, `fixed_defect_zero`, `base_defect_zero`, `linear_term_zero`。入力は各パラメータの実面等号。cochainの消失やBの相対所属を別certificateとして要求しない |
| 同じ相対負defect | `relativeDefect`, `relativeLinear`, `baseRhs`, `rhsLinear`, `negative_defect_affine`, `rhs_physical_value`。全元面値と負符号を保持 |

material premise ledger:

- `ambient-boundary / 本文由来 (A, n1017 §3.5/6.1)`: 任意圏のT、元セルと対象、strong/core/可換全核/全単射輸送/比較中央化、各全核のmoduleと輸送線形性、パラメータ空間・原始辺/比較の線形変化、閉P、各入力の固定面での実整合。
- `discharge-required / 放電済み`: 同じ実両経路のcanonical比較、raw defectの核値、アフィン式と線形B、原始実等号から相対所属、負defectの全元面対応。
- `direction-hypothesis`: 基本APIのh/aは実辺・比較の任意変更値。具体パラメータではθv/ηvを代入して生成する。
- `conclusion-equivalent-risk`: 固定面hfixedはP内の実整合という原始条件のみ。全面の修復存在・商零・defectのアフィン式・相対Bの所属はinput fieldにない。

主spineは `raw_defect`, `defect_inclusion`, `affine_defect`, `affine_inclusion`,
`defect_zero_iff`, `linear_term_zero`, `negative_defect_affine`, `rhs_physical_value`。
一般線形・相対構成のために有限性を追加しておらず、固定GOALの有限入力も全て含む。
新規Prop述語・certificate構造はない。新規dataは上表の既存API・実合成へ接続済み。

G-129の受理head `cbe70c4dc734a851a90c5030a736141f4352fcba` と
[最終受理](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5125#issuecomment-5902401268)、
G-130の受理head `549b7e3ccab1c9686a108530e1b0a4b4f38eee86` と
[最終受理](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5179#issuecomment-5966982329)
を再利用資格とする。Correctionおよび使用するraw/comparison APIはG-129受理版から変更なし、
FiniteCoefficientDifferentialsはG-130受理版から変更なし。現在のsignature・同じTと実核・
proof-useを確認。Correction blob `10668815b01c88f1be4da453988e6f586db34e9a`、
FiniteCoefficientDifferentials blob `66f7d6bf0822069e15bccfc7d054884bf2cd998d`。
G-129内部の全履歴・依存の再帰的再認定は行わない。

```yaml
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "一般の全実核で実経路のアフィンdefectを導出し、固定面の実等号から同じ相対負defectとBを生成"
  exit_criteria_status: ["raw physical defectの全面評価", "原始θ/ηから線形B生成", "実固定面等号から相対所属", "全元辺/面の保持", "focused2file・28個別公理・scanの証拠をPRコメントへ固定"]
  split_reason: none
  completion_candidate: no
  lean_artifacts: [PrimitiveAffineDefect.lean, RelativeAffineDefect.lean]
  evidence: [raw_defect, defect_inclusion, affine_defect, affine_inclusion, defect_zero_iff, linear_term_zero, negative_defect_affine, rhs_physical_value]
  claim_mapping:
    theorem_names: [raw_defect, affine_defect, affine_inclusion, negative_defect_affine, rhs_physical_value]
    source_labels: ["Aの実経路からアフィン負defect生成", "n1017 §3.5/6.1"]
    conjuncts: ["同じ原始実辺/比較を核でアフィンに変化", "同じ実合成からδ₀+η+d¹θ", "固定実面から相対cochain", "同じ負defect=b₀+Bv"]
    undischarged_assumptions: []
    acceptance_point: "一般実核の原始変更モデルから同じ実アフィンdefectを生成する到達点。外部原始族と各OriginalTowerへの対応は後続"
    port_status: unported
audits:
  premise_delta:
    discharged: ["一般実経路のアフィンdefect生成", "実固定面から相対B所属", "同じ元面値と負符号"]
    remaining: ["元原始族/各OriginalTowerとの同定と同じ全係数・微分", "基底座標/局所公開可否/実観測への接続", "B・D・E"]
  certificate_provenance:
    discharged: ["原始辺・比較からraw値", "実d1からB", "hfixedから相対所属"]
    unresolved: ["外部の全原始族との表示対応は後続"]
  proof_use:
    used: ["strong uniqueness", "G-129の実補正微分", "全実核と可換性・比較中央化", "原始θ/η・輸送線形性", "全パラメータのP実等号"]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: ["focused・28個別#print axioms・scanをPRコメントへ固定"]
  blocking_findings: []
  next_obligation: "元原始族/各OriginalTowerと同じ実経路モデルの対応、同じ全係数・基底座標・局所公開可否、Cへの入力接続"
```

G-131全体は `target-proof-checkpoint`。A全体・B・D・Eは未完了。

## Cycle 5：元の原始入力族と生成された同じ実修復方程式

```yaml
ledger_type: target_cycle_result
goal: G-131-aat-repair-observation-duality
cycle: 5
goal_blob_sha: 054fea81b916c4d4a470b74af3e13c6cc5dde01c
base_oid: abaa758fa5e87f49c3c80cc1662d27b3d402bdb5
tracking_issue: 5133
report_path: research/reports/G-131-aat-repair-observation-duality.md
selection:
  proof_state_ref: "Cycle 3/4受理済み。Cycle 4 PR #5203のmerge abaa758faへ同期済み。選定時は独立worktreeで固定head査読を待ち、その受理後に実装接続を継続"
  proof_dag_predecessors: [NativeCorrectionEquation.actual_equation_iff, PrimitiveAffineDefect.affine_inclusion, RelativeAffineDefect.negative_defect_affine]
  milestone: "Aの原始族の実基準辺/比較から、同じ全実核・微分・負defect・任意Sの方程式・独立実修復の往復へ接続"
  proof_obligations: ["原始変更モデルからstrong/core/核輸送/比較条件を満たす実塔生成", "同じ全核・輸送・微分の保存", "元原始族の実辺/比較との同定", "同じ原始実defectと相対アフィン右辺の一致", "任意Sで元の独立実修復との同値と全実辺復元"]
  exit_criteria: ["生成実塔の原始条件と全係数保存", "外部の元OriginalTowerの実操作とモデル対応", "同じb₀/B/D_Sから全S/Xの修復可否・商零", "禁止補正と元実辺の復元", "focused・全宣言公理・scan"]
  selection_reason: "Cycle 4の実合成をCycle 3の元独立実修復へ接続し、一般族をcommon-module模型に縮めるgapを閉じる"
  expected_result_type: proof-obligation-discharged
  lean_targets: [PrimitiveAffineTower.lean, CoefficientTransport.lean, ActualAffineFamily.lean]
  risks: ["結論相当のdefect式/修復/同値をfamily fieldへ移さない", "元のoriginal/selected辺の相違と固定規則を保持", "元全核と同じ輸送を証明", "基底数値座標/局所公開可否/実評価への接続は残る義務"]
  unchecked: ["構成・検証・独立査読前"]
```

Cycle 5実装時のAPI選定: 同じ全係数の等式でmodule・相対面・全split sourceと微分を運ぶ基本constructor APIを `CoefficientTransport.lean` に分離する。到達点と終了条件は維持する。

### Cycle 5の実装・前提・証拠対応

固定GOAL A / n1017 §3.5・§6.1の原始辺・比較のアフィン変更から、任意圏・頂点ごとの全実核で実塔を生成する。外部の各OriginalTowerの元操作・core lift・参照規則はその入力に保持する。`hdata`はその基準実辺と比較操作が同じ原始アフィン変更であるという入力表現等式であり、defect式・微分・可解性・修復同値は含まない。全係数の同定は`input_coefficients`で実操作から導出し、等式の入力として受け取らない。

全パラメータの実現`realize`とν∘realize=id、および各入力のP上の実経路等号から`model_fixed`を生成する。元defectを全相対面へ運んだ`commonDefect`は、実核値を保ち、同じb₀+Bν(X)へ等しい。有限性・非空性はこの線形生成へ追加せず、任意Sの実修復同値と復元で元辺の有限族を用いる。元操作のP固定は入力間の値の同一性ではなく、その入力の修復中の実操作の保持である。

宣言一覧（全39、namespaceはAAT.AG.RepairObservationDuality.<file名>）:

- `PrimitiveAffineTower.lean`: `lower_strong`, `edge_transport`, `core_alignment`, `centralizes`, `tower`, `tower_data`, `edge_coefficients`, `local_coefficients`, `tower_defect`, `tower_eq_of_data_eq`。
- `CoefficientTransport.lean`: `modules`, `faces`, `faces_value`, `faces_symm`, `linearity`, `values`, `values_always_value`, `values_selected_value`, `differential`, `equation_iff`。
- `ActualAffineFamily.lean`: `input_tower`, `input_coefficients`, `model_fixed`, `original_defect_coordinate`, `commonDefect`, `common_defect_value`, `common_defect_eq`, `negative_defect_affine`, `inputModules`, `input_linearity`, `actual_equation_iff`, `actual_affine_equation_iff`, `common_defect_inverse`, `solution_transport`, `actual_affine_cokernel_iff`, `restore`, `restore_value`, `restore_forbidden_zero`, `restore_fixed_arrow`。

主spineは `PrimitiveAffineTower.edge_transport` / `local_coefficients` / `tower_defect`、`CoefficientTransport.differential` / `equation_iff`、`ActualAffineFamily.input_coefficients` / `model_fixed` / `common_defect_value` / `negative_defect_affine` / `actual_affine_equation_iff` / `actual_affine_cokernel_iff` / `solution_transport` / `restore` / `restore_value` / `restore_forbidden_zero` / `restore_fixed_arrow`。全source・face・candidate値のcast APIは補助constructor APIである。新規Prop述語・certificate構造・instanceはない。

material premise ledger:

- `ambient-boundary / 本文由来`: 任意圏のTと全実核、G-129のtower入力条件、各全核のmoduleと輸送線形性、辺・比較の原始線形変化θ/η、外部OriginalTower族とν、原始実操作のアフィン表示等式hdata、全パラメータの実現とν値、閉Pでの各実入力の面整合、元候補名・P外所属。
- `discharge-required / 放電済み`: 変更後のstrong/core/全単射輸送/比較中央化、同じ全係数・輸送・微分、全元面のactual defectと同じ相対b₀/B、全S/Xの独立実修復⇔同じ全方程式⇔同じ商零、全数値成分を運ぶ復元・禁止補正零・固定実辺保持。
- `direction-hypothesis`: restoreのhhは取得済み全係数数値が同じ方程式を満たすという出力の正答条件。修復存在を仮定する可否定理はない。
- `conclusion-equivalent-risk`: hdataはprimitive reference transport dataだけ。係数の等式・defect式・微分等式・可解性・商零・修復証拠をfamily fieldに移していない。

受理済み先行成果の資格: G-129 head `cbe70c4dc734a851a90c5030a736141f4352fcba` [最終監査](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5125#issuecomment-5902401268)、G-130 head `549b7e3ccab1c9686a108530e1b0a4b4f38eee86` [最終監査](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5179#issuecomment-5966982329)、Cycle 3 head `0db94dc67b43ff24696c2f3664a8cf6797dbbc6b` [最終監査](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5200#issuecomment-5969565903)、Cycle 4 head `9937ee378ee26d75c798633c8d544fd4602ff9fe` [最終監査](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5203#issuecomment-5970002097)。現在のsignature・primitive値・G-130同じ元塔/P/candidates/S/hへの適用とproof-useを照合し、使用sourceをPR監査記録に固定する。先行成果の内部査読履歴は再帰的に再認定しない。

```yaml
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "原始族の同じ実辺/比較から全係数/微分/負defectと全S/Xの実修復方程式・商零・全成分復元を接続"
  exit_criteria_status: ["生成塔の全native条件", "実原始表示から元OriginalTowerの同定", "同じ全係数/輸送/微分", "全S/Xの同じb₀+Bνと実修復可否/商零", "全元辺の復元/禁止零/固定実辺", "3 focused・39個別公理監査・scan"]
  split_reason: none
  completion_candidate: no
  lean_artifacts: [PrimitiveAffineTower.lean, CoefficientTransport.lean, ActualAffineFamily.lean]
  evidence: [input_coefficients, model_fixed, negative_defect_affine, actual_affine_equation_iff, actual_affine_cokernel_iff, solution_transport, restore_value, restore_forbidden_zero, restore_fixed_arrow]
  claim_mapping:
    theorem_names: [input_coefficients, negative_defect_affine, actual_affine_equation_iff, actual_affine_cokernel_iff, restore_value]
    source_labels: ["G-131 A", "n1017 §3.5/6.1"]
    conjuncts: ["同じ原始実辺/比較から元塔", "同じ全係数・実微分", "同じ負defect=b₀+Bν", "全S/Xの実修復⇔全方程式⇔商零", "全元名と固定実操作を保持する復元"]
    undischarged_assumptions: []
    acceptance_point: "原始アフィン実表示の全OriginalTower族をCycle 3/4の同じ全方程式へ接続する到達点"
    port_status: unported
audits:
  premise_delta:
    discharged: ["原始実表示から元族との同定", "全実核/輸送/微分保存", "元族の同じ負defect", "全S/Xの実修復・商零", "全成分の元実操作復元"]
    remaining: ["全核基底の数値座標・局所公開可否・実観測との接続", "B・D・E"]
  certificate_provenance:
    discharged: ["原始変更からnative tower条件", "実辺/比較から全係数等式", "全実現/Pの実等号から相対family", "G-130から同じ元修復の復元"]
    unresolved: ["基底数値/局所公開可否/原始評価の後続接続"]
  proof_use:
    used: ["元strong/core/可換核/全単射/中央化", "原始θ/η・hdata・輸送線形性", "全実現のν値", "入力ごとのP実等号", "G-130 supported repairEquivと全成分restore"]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: ["3 focused・39個別#print axioms・scanのraw記録をPRへ固定"]
  blocking_findings: []
  next_obligation: "Aの基底数値・局所公開可否・原始評価をCの同じ問い合わせへ接続、B/D/E"
```

全体は `target-proof-checkpoint`。A全体・B・D・Eは未完了。独立査読前のCycle結果はproposalである。

## Cycle 6：全基底座標・生成局所可否・原始問い合わせの同じ入力への接続

```yaml
ledger_type: target_cycle_result
goal: G-131-aat-repair-observation-duality
cycle: 6
goal_blob_sha: 054fea81b916c4d4a470b74af3e13c6cc5dde01c
base_oid: ec23aefda427f94b29cb819cda0b3011619bd936
tracking_issue: 5133
report_path: research/reports/G-131-aat-repair-observation-duality.md
selection:
  proof_state_ref: "Cycle 5 PR #5204の4本No major findingsとCI successで受理・merge ec23aefdaへ同期済み。選定時は固定headの独立査読を待ち、別worktreeで準備"
  proof_dag_predecessors: [ActualAffineFamily.actual_affine_equation_iff, ActualAffineFamily.restore_value, FiniteFamily.equivalence, GeneratedStrictCover.objectEquiv, PrimitiveQueries.Run, QueryOptimum.decision_optimum]
  milestone: "Aの同じ全基底数値・局所記号的可否・原始評価を、元族の実修復とCの同じ問い合わせモデルへ接続"
  proof_obligations: ["固定全核基底で全always/selected/faceの線形座標を構成", "同じ実D_S/b₀/Bの数値方程式と全成分復元", "生成された局所公開関係の可否と同じ元全方程式", "原始評価の入力一致と全実現から全run/応答列/出力/回数/正答/最適値を往復"]
  exit_criteria: ["全元核基底の数値値と全sourceの両逆", "同じ実微分/負defectの座標式と禁止値/復元", "同じ元coverの生成局所可否と全方程式の同値", "全実入力の原始評価/全実現から同じrun列と費用を往復", "同じ実修復述語/全数値出力でCへ接続", "focused/全宣言公理/scan/独立査読"]
  selection_reason: "Cycle 5のnative方程式を固定基底の完全数値と取得原始値へ接続し、Aの残る入力生成とCの実手続き対応を閉じる"
  expected_result_type: proof-obligation-discharged
  lean_targets: [FullCorrectionCoordinates.lean, EquationCoordinates.lean, PrimitiveInputQueries.lean, ActualFamilyCoordinates.lean, ActualFamilyInterfaces.lean]
  risks: ["像や商の基底へ全補正値を縮めない", "取得前に未知右辺を参照しない", "同じ元候補・共通coverで局所生成を照合", "評価一致と全実現は一般族の許された入力条件、Eの具体構成は後続義務", "実runの再実行を回数から消さない"]
  unchecked: ["実装・検証・査読前"]
```


### 固定要求と証明経路

| 固定要求の部分 | 宣言と同じ入力への接続 |
| --- | --- |
| A/Cの完全な数値補正 | `FullCorrectionCoordinates.alwaysFamily` は全元辺のfamilyをPと候補だけで零にする。`alwaysCoordinate`, `selectedCoordinate`, `coordinate` は入力の全頂点核基底を使う両逆。`always_value`, `selected_value`, `always_restore_value`, `always_restore_zero`, `selected_restore_value` は元名と全値を保存 |
| 同じ全方程式と負defectの基底表示 | `EquationCoordinates.differential`, `parameter`, `affine_rhs`, `solution_iff`, `equation_iff`。`ActualFamilyCoordinates.actual_numerical_equation_iff` はCycle 5の同じ実族、全S、b₀/Bを完全数値へ接続 |
| 数値解から元実操作への復元 | `ActualFamilyCoordinates.solution_restore`, `restore`, `restore_value`, `restore_forbidden_zero`, `restore_fixed_arrow`。全座標を逆変換し、Cycle 5の元OriginalTowerへの復元で全辺値・禁止零・固定実辺を保持 |
| Cの同じ判定核・数値核 | `EquationCoordinates.parameter_ker`, `obstruction_ker` と `ActualFamilyCoordinates.numerical_parameter_ker`, `numerical_obstruction_ker`。完全基底変換の前後で同じBとq_SBの核を保存 |
| Aの生成局所公開可否 | `ActualFamilyInterfaces.generatedObjects`, `globalToGenerated`, `generated_equation_iff`, `actual_generated_iff`。G-130の全private/public値の局所生成と実coverの全値復元を同じ負defectへ適用し、独立元修復と同値 |
| A/Cの原始評価と全実行 | `PrimitiveInputQueries.run_iff`, `transcript_eq`, `correct_iff`, `worst_eq`, `optimum_eq`。νと全実現・原始評価一致から、同じ履歴のみの手続きについて全出力、応答列、重複質問列、正答・常時停止・最悪回数・最適値を往復 |
| 元実修復述語と完全数値出力 | `ActualFamilyCoordinates.valid_none_actual_iff`, `primitive_correct_iff`, `primitive_optimum_eq`。noneは元実修復非存在、someの完全値は`solution_restore`から元実修復へ。取得後評価する式を数値出力の型に追加しない |

受理spine候補は `actual_numerical_equation_iff`, `restore_value`, `actual_generated_iff`,
`run_iff`, `correct_iff`, `worst_eq`, `optimum_eq`, `primitive_optimum_eq`。
残る宣言は入力構成とその基本API。cycle scaffoldはない。新規Prop/certificateはなく、
C1/C2の独立出力・正答述語、G-130の独立全方程式・生成対象をそのまま使用する。

### 全対象宣言

- `FullCorrectionCoordinates.lean`: `alwaysRelativeModule`, `alwaysFamily`, `AlwaysIndex`, `alwaysCoordinate`, `always_value`, `SelectedValues`, `selectedCoordinate`, `selected_value`, `NumericalValues`, `coordinate`, `always_restore_value`, `always_restore_zero`, `selected_restore_value`。
- `EquationCoordinates.lean`: `differential`, `differential_apply`, `solution_iff`, `equation_iff`, `parameter`, `parameter_apply`, `affine_rhs`, `parameter_ker`, `obstruction_ker`, `valid_some`, `valid_none`, `valid_output_iff`。
- `PrimitiveInputQueries.lean`: `run_iff`, `transcript_eq`, `correct_iff`, `worst_eq`, `optimum_eq`。
- `ActualFamilyCoordinates.lean`: `numericalD`, `numericalB`, `numericalBase`, `numerical_parameter_ker`, `numerical_obstruction_ker`, `actual_numerical_equation_iff`, `solution_restore`, `restore`, `restore_value`, `restore_forbidden_zero`, `restore_fixed_arrow`, `valid_none_actual_iff`, `primitive_correct_iff`, `primitive_optimum_eq`。
- `ActualFamilyInterfaces.lean`: `generatedObjects`, `globalToGenerated`, `generated_equation_iff`, `actual_generated_iff`。

全48宣言を各sourceのnamespace公理監査と個別`#print axioms`の対象にする。

### material premise・provenance・proof-use

| material premise | 役割 | 構成と使用先 |
| --- | --- | --- |
| 元表示、native全係数/module、全頂点核基底、P、候補と全S | ambient-boundary | Aの固定入力。Pと候補の零条件からalways familyの両逆、全候補核からselected座標、全面の元核基底からface座標 |
| 基底による完全なeH/eW | discharge-required、構成済み | `FullCorrectionCoordinates.coordinate` と受理済み `FiniteNative.coordinate2`。全両逆と元値APIを `EquationCoordinates` および元実修復復元へ使用 |
| 原始θ/η、実reference表示hdata、全実現、Pの実等号、線形核輸送 | 一般族の入力条件と既存構成 | Cycle 5の同じprimitive実操作からb₀/B/Dと全実修復同値を導出。実現と評価一致は一般Aの明示条件、Eの全指定操作での生成は後続義務 |
| finite cover U・cover証拠・全元辺/面/体/cover列挙 | ambient-boundary | AのG-130入力。`StrictCoverRestoration.objectEquiv` と `GeneratedStrictCover.objectEquiv` を同じ元候補/P/全値/負defectへ適用 |
| 生成局所public compatibilityと全global解 | discharge-required、構成済み | 両既存全対象の両逆を `globalToGenerated` で合成。独立global方程式、全選択列式と元実修復を `generated_equation_iff` から接続 |
| 原始インデックスと線形評価・実評価一致 | 一般Aの入力条件 | `heval` をRun.askの実応答へ使用、両方向実行・完全transcript一致。全実現を逆向きの常時停止/正答・worst・optimumへ使用 |
| 履歴から次問/完全出力を選ぶ手続き、情報fiber | ambient-boundary | Cの同じモデル。元入力fiberはνの逆像、実行リストの全長を数える。任意手続きでworst同値、正しい手続き全体のinfを往復 |
| 出力の正確性・常時停止・最適値一致 | discharge-required、証明済み | 実応答からRunを往復、各実入力をνへ、各パラメータをrealizeへ写す。正しい手続きを与える条件を追加せず、その集合を両方向同定 |
| 不能出力と実修復非存在 | discharge-required、証明済み | 完全数値方程式と独立元実修復の同値を否定へ適用。不能判定を入力fieldに移さない |

先行成果の再利用資格は Cycle 1 PR #5193、Cycle 2 PR #5195、Cycle 5 head
`3e0423e1f590493d9d723b0af0e345b4700c7246`
[最終監査](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5204#issuecomment-5970294260)、
G-130 head `549b7e3ccab1c9686a108530e1b0a4b4f38eee86`
[最終監査](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5179#issuecomment-5966982329)。
現在のsource、signature、元名・全基底・全値・負defectの適用とproof-useを照合する。
標準基盤は固定Mathlib `8f9d9cff6bd728b17a24e163c9402775d9e6a365` のLinearEquiv/Pi、
native quotient零、ENatのiSup/iInf。同じ手続き全体のinfを比較し、入力族を像だけへ縮めない。

```yaml
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "同じ原始実族を全核基底の数値方程式・生成局所公開可否・全実runと最適値へ接続"
  exit_criteria_status: ["完全基底両逆/全元値", "同じD_S/b₀/Bの数値式と元実修復復元", "同じ元cover局所可否", "実評価/全実現から全応答と重複回数", "元不能述語/完全数値出力のquery model接続", "focused/48個別公理/scan/独立査読はPR記録"]
  split_reason: none
  completion_candidate: no
  lean_artifacts: [FullCorrectionCoordinates.lean, EquationCoordinates.lean, PrimitiveInputQueries.lean, ActualFamilyCoordinates.lean, ActualFamilyInterfaces.lean]
  evidence: [actual_numerical_equation_iff, restore_value, numerical_parameter_ker, numerical_obstruction_ker, actual_generated_iff, run_iff, transcript_eq, correct_iff, worst_eq, primitive_optimum_eq]
  claim_mapping:
    theorem_names: [actual_numerical_equation_iff, restore_value, actual_generated_iff, primitive_correct_iff, primitive_optimum_eq]
    source_labels: ["G-131 A/C", "n1017 §3.5/6"]
    conjuncts: ["全核基底の同じ方程式", "全元名/禁止零/固定実操作の復元", "生成局所公開可否と元修復", "原始評価から全応答/出力/重複回数/常時正答/最適値"]
    undischarged_assumptions: []
    acceptance_point: "Aの全基底・局所可否・評価条件とCの同じ実query modelの到達点。B/D/Eの指定接続は後続義務"
    port_status: unported
audits:
  premise_delta:
    discharged: ["全数値座標/同じDとRHS", "元実修復全値", "生成局所可否", "実run/応答列/正答/回数/最適値"]
    remaining: ["BのG-128作用/観測/双対", "Dの有限最小計画/不能値取得/更新", "Eの全実現/実評価/全指定表/分割/参照式"]
  certificate_provenance:
    discharged: ["固定全基底の両逆", "G-130全局所生成/全cover復元", "元原始実評価/全実現から実行対応"]
    unresolved: ["Eの元操作から全実現と実評価を構成"]
  proof_use:
    used: ["全核基底と元name", "原始負defectと同じD_S", "P/candidates/Sの全値復元", "同じ元cover生成", "実評価のRun.ask応答", "全実現のworst逆向き", "正しい手続き全体のinf"]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: ["5 scoped files・48個別#print axiomsのraw記録/scan/独立査読をPRへ固定"]
  blocking_findings: []
  next_obligation: "Bの加法群作用・G-128観測と述語・双対/商/点手続き回数の接続"
```

全体は `target-proof-checkpoint`。B/D/Eと最終A–E統合は未完了。独立査読前のCycle結果はproposalである。

## Cycle 7：同じ観測の双対・加法群作用・G-128点手続きへの接続

```yaml
ledger_type: target_cycle_result
goal: G-131-aat-repair-observation-duality
cycle: 7
goal_blob_sha: 054fea81b916c4d4a470b74af3e13c6cc5dde01c
base_oid: 2cef6cbecba6f7958c69032bc8cb81275b524413
tracking_issue: 5133
report_path: research/reports/G-131-aat-repair-observation-duality.md
selection:
  proof_state_ref: "Cycle 6 PR #5209の受理済みmerge 2cef6cbecba6f7958c69032bc8cb81275b524413"
  proof_dag_predecessors: [Solvable, solvable_add_iff, observation, mem_ker_observation, PrimitiveQueries.Run, MinimalCompatibilityObservations.observe, MinimalCompatibilityObservations.QueryRun]
  milestone: "Bの観測因子化・双対/商/残存像・加法群作用とG-128観測述語/実行/最適回数を同じ元修復入力へ接続"
  proof_obligations: ["同じ観測核の消滅空間と原始評価span・商双対を構成", "q_SBの商と残存障害像/包含を全値で対応", "加法群の全(j,a)への作用と点安定化群/観測表/元修復述語", "原始手続きと全点手続きの双方向応答/正答/重複回数対応", "重複原始indexを除く十分集合の最小値とG-128最適値/無限/零を接続"]
  exit_criteria: ["観測因子化/核包含/双対spanを全方向", "商双対と残存像の代表元保存", "全点作用の評価/安定化群と同じ元修復述語", "両history-only手続きの全run/正答/費用を往復", "G-128の最小点集合と原始最小集合を両方向・同じ最適値", "focused/全宣言公理/scan/独立査読"]
  selection_reason: "A/Cで同定した同じ元修復をG-128と双対へ移し、Dの評価取得に必要なspan条件を準備"
  expected_result_type: proof-obligation-discharged
  lean_targets: [LinearObservationDuality.lean, AdditiveObservationAction.lean, PointQuerySimulation.lean, PrimitiveReplyTranslation.lean, ActualObservationPredicate.lean, QueryOptimum.sufficientSet_zero_iff]
  risks: ["success shiftと元入力の定数応答を混同しない", "任意(j,a)は既知平行移動であり新しい原始方向を作らない", "同じjの複数点を一回として勝手に実行費用から消さない", "商の代表元と残存空間への包含を保持", "G-128の同じ観測/述語/全手続きを使用"]
  unchecked: ["実装・検証・査読前"]
```

### Cycle 7 の宣言と前提

Bの同じ原始観測表について、因子化をPropおよびBoolで構成し、観測核の消滅空間を
原始評価の線形包へ対応させる。商双対の正逆と商から残存障害像への正逆は全代表元の値を保存する。
加法群は `Multiplicative V` と表記してG-128の既存Group作用へ直接接続する。
全点 `(j,a)` を含め、応答の第2成分から既知 `a` を引いて元評価を回収する。
点安定化群・観測表・十分性は元primitive indexの表の核と同じである。
最小固定集合を比較するときにだけ重複indexを除き、実行列では重複を全て数える。

点手続きから原始手続きへの変換は、見える原始履歴を点手続き自身で再生して
次点の既知offsetを回収する。元入力も未来の応答も参照せず、全runを両方向へ対応させる。
zero-offset側と任意offset側の双方で、全出力・応答・各回数・常時停止と正答・worstを保存し、
正しい手続き全体のinfを比較する。G-128の既存最適値定理を同じ作用と述語へ適用する。

実入力との接続では、成功した元入力 `base` の `ν base` を引き、
元実修復の存在を同じ `ker(q_SB)` へ対応させる。
実評価の既知定数 `λ_j(ν base)` を履歴ごと変換する手続きと、全パラメータの実現を用い、
任意の元実入力に対する最適回数をG-128と最小原始集合へ対応させる。
十分集合がない場合は無限、全元入力が修復不能ならfalseを返す零回手続きを構成する。
成功点を有限に探すことはDの後続義務であり、Bでは指定の条件分けの仮定として使用する。

受理spineは次の69宣言（5新規moduleと既存観測moduleの基本API1本）。

`AAT.AG.RepairObservationDuality.LinearObservationDuality`: `predicate_iff`, `decision_iff`, `evaluationSpan`, `span_coannihilator`, `observation_annihilator`, `kernel_iff_dual`, `predicate_iff_dual`, `quotientDual`, `quotientDual_apply`, `quotientDual_symm_apply`, `quotientImage`, `quotientImage_apply`, `quotientImage_symm_apply`。

`AAT.AG.RepairObservationDuality.AdditiveObservationAction`: `action`, `action_apply`, `fixed_iff`, `compatible`, `mem_compatible`, `indices`, `stabilizer_iff`, `sufficient_iff`, `predicate_iff`, `observe_decode`, `zeroPoints`, `indices_zeroPoints`, `card_zeroPoints`, `card_indices_le`, `minimum_eq`。

`AAT.AG.RepairObservationDuality.PointQuerySimulation`: `evaluation`, `evaluation_apply`, `decode`, `toPoint`, `primitive_to_point`, `point_to_primitive`, `inflateStep`, `inflate`, `fromPoint`, `inflate_append`, `arbitrary_point_to_primitive`, `primitive_to_arbitrary_point`, `toPoint_correct_iff`, `fromPoint_correct_iff`, `toPoint_worst_eq`, `fromPoint_worst_eq`, `optimum_eq`, `optimum_eq_minimum`。

`AAT.AG.RepairObservationDuality.PrimitiveReplyTranslation`: `history`, `procedure`, `run_iff`, `correct_iff`, `worst_eq`, `optimum_le`, `optimum_eq`。

`AAT.AG.RepairObservationDuality.ActualObservationPredicate`: `repair_shift`, `repair_realize_shift`, `observation_predicate_iff`, `observation_decision_iff`, `observation_predicate_dual_iff`, `point_predicate_iff`, `repairQuotientDual`, `repairQuotientDual_apply`, `repairQuotientImage`, `repairQuotientImage_apply`, `repair_difference`, `actual_optimum_eq_point`, `actual_optimum_eq_minimum`, `actual_optimum_eq_top_iff`, `actual_optimum_zero`。

`AAT.AG.RepairObservationDuality.sufficientSet_zero_iff`: 同じSufficientSetの全入力用基本API。

| 前提・構成 | 分類 | 出所・証明での使用 |
| --- | --- | --- |
| 体、線形空間、元primitive indexとλ、有限次元V | ambient-boundary | G-131の係数と評価。一般補題は有限体を要求せず、双対のdouble annihilatorに有限次元を使用 |
| 同じ物理実入力族、共通核・候補・固定領域・全実現 | ambient-boundary、Aの入力条件 | 受理Cycle 5のactual affine equationへ適用。全実現を原始/点の全入力最適値の逆方向へ使用 |
| 成功した元入力base | direction-hypothesis | Bの指定条件分け。元実修復から同じDSの成功点を得てshift。成功判定・選択はDの後続義務 |
| 観測核とλの線形包、同じ商双対/残存像 | discharge-required、証明済み | 固定Mathlibのspan/double annihilator・quotient dual・first isomorphismから構成、全代表元評価の正逆 |
| 加法作用、全点の応答、点安定化群・十分性 | discharge-required、証明済み | λの加法性から作用を構成し、元jでの零条件へ同定。G-128の既存表/安定化群を直接使用 |
| point/primitiveの全手続きとvisible history | ambient-boundary | G-128/C2の同じ次stepと実行。任意offsetをvisible historyから回収し、反復回数を全保持 |
| 応答/正答/常時停止/worst/optimumの両方向 | discharge-required、証明済み | 両Run変換、両Correct、両worstを証明して全正答手続きのinfを比較。supplied solverを仮定せず |
| 同じ元実修復述語と実原始評価 | discharge-required、証明済み | C5の元実方程式、C1のsolvable_add_iff、C6の全実現/実評価橋と既知応答定数変換を使用 |
| 一般族の原始実評価=λν | ambient-boundary、Aの入力条件 | 実応答のshift/run、全入力のworst/optimumへ使用。Eで元操作から構成する追加義務を維持 |
| 無限/全不能零 | discharge-required、証明済み | 十分集合不存在⇔minimum=∞、実原始最適値同定、および実不能述語を満たすfalse常時停止手続き |

再利用資格：Cycle 1/2/5/6の受理済みsourceとPR記録を照合する。
Cycle 6 head `8ebd24ad893aac6f44cdcd76639dbabc83386389`、
[最終監査](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5209#issuecomment-5970703374)。
G-128 final head `313a6c9788238f0a6fc576b65ce253cd538cbf10`、
[全体完了監査](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5103#issuecomment-5880926353)、
[Issue #5075](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5075)。
G-128の現在のPointObservation/AdaptiveLowerBound/QueryOptimumのstatementと同じ作用への適用を実読する。
標準線形代数は固定Mathlib `8f9d9cff6bd728b17a24e163c9402775d9e6a365`。

```yaml
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "同じ実修復を線形観測双対・商双対/残存像・G-128の全点作用/全手続き/最適回数へ接続"
  exit_criteria_status: ["因子化/核/双対spanを全方向・Bool実出力", "商双対/残存像の正逆と代表元値", "全点作用/安定化群/表と元実述語", "両visible-history手続き/実応答/正答/重複回数", "最小原始集合/G-128最適値/∞/全不能零", "対象宣言focused/個別公理/scan/独立査読はPRへ固定"]
  split_reason: none
  completion_candidate: no
  lean_artifacts: [LinearObservationDuality.lean, AdditiveObservationAction.lean, PointQuerySimulation.lean, PrimitiveReplyTranslation.lean, ActualObservationPredicate.lean, QueryOptimum.sufficientSet_zero_iff]
  evidence: [kernel_iff_dual, quotientDual_apply, quotientImage_apply, stabilizer_iff, minimum_eq, primitive_to_point, arbitrary_point_to_primitive, primitive_to_arbitrary_point, fromPoint_worst_eq, actual_optimum_eq_point, actual_optimum_eq_minimum, actual_optimum_eq_top_iff, actual_optimum_zero]
  claim_mapping:
    theorem_names: [observation_predicate_dual_iff, point_predicate_iff, repairQuotientImage_apply, actual_optimum_eq_minimum, actual_optimum_eq_top_iff, actual_optimum_zero]
    source_labels: ["G-131 B", "n1017 §6"]
    conjuncts: ["因子化/核包含/原始span", "同じ実族の商双対/残存像/包含", "同じ実修復述語と全点応答", "全手続きと繰返し費用", "実primitive最適値/∞/不能零"]
    undischarged_assumptions: []
    acceptance_point: "Bの観測双対性とG-128への同じ実入力接続。D/Eと最終統合は後続義務"
    port_status: unported
audits:
  premise_delta:
    discharged: ["観測核の双対span", "同じ商双対と残存像", "全点作用/安定化群/観測表", "全手続き/応答/正答/費用", "元実入力の最適回数/∞/全不能零"]
    remaining: ["Dの双対値取得/有限最小計画/未知更新", "Eの全実現/実評価/全指定表/細分化/参照式", "最終A–E統合"]
  certificate_provenance:
    discharged: ["λの線形性から実作用", "spanとcanonical quotient maps", "visible historyから両手続き", "受理済み同じ元実方程式"]
    unresolved: ["Eの具体族の原始入力条件構成"]
  proof_use:
    used: ["原始λの線形性", "有限次元V", "同じDS/b₀/B", "成功元入力", "実評価", "全実現", "実history/反復質問", "G-128の同じ作用/表/述語/全手続きの最適値"]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: ["対象fileと69追加宣言のfocused/個別公理raw記録、scan、独立査読をPRへ固定"]
  blocking_findings: []
  next_obligation: "Dの同じ双対値取得・有限計画/solver/実復元と更新"
```

全体は `target-proof-checkpoint`。D/Eおよび最終A–E統合は未完了。独立査読前のCycle結果はproposal。

## Cycle 8：同じ不能証拠の残存双対値と取得条件

```yaml
ledger_type: target_cycle_result
goal: G-131-aat-repair-observation-duality
cycle: 8
goal_blob_sha: 054fea81b916c4d4a470b74af3e13c6cc5dde01c
base_oid: 37da48dce125ac1b495d04b43fc622a44a5bc551
tracking_issue: 5133
report_path: research/reports/G-131-aat-repair-observation-duality.md
selection:
  proof_state_ref: "Cycle 7 PR #5216受理・merge 37da48dce125ac1b495d04b43fc622a44a5bc551。初期selectionは261284a3c上に固定し、C7受理後にbaseを同期した"
  proof_dag_predecessors: [SelectedCokernel.nativeToResidual_value, NamedDual.annihilates_iff, NamedDual.failure_witness, LinearObservationDuality.span_coannihilator, LinearObservationDuality.observation_annihilator, informationFiber, ActualAffineFamily.actual_affine_equation_iff]
  milestone: "Dの同じ元不能証拠を残存障害双対へ値を保って移し、既知fiber上の値取得条件を原始評価spanとして全方向証明"
  proof_obligations: ["元全候補支持E_phiと任意Sの残存商への下降", "元実修復失敗から同じ非零残存双対値", "追加候補方向が同じ値を変える条件と元support", "ell q_S(b₀+Bv)の取得とN上の原始spanを全方向", "既知定数と更新後既知/通知値のfiberを保持"]
  exit_criteria: ["同じS/候補名/元RHSで下降と評価保存", "失敗実入力の非零検出値と追加候補支持の同値", "全非空known fiberの値取得⇔restricted spanと同じ評価式", "既知値/通知値の情報核を保持して値取得条件へ再適用", "focused/全宣言公理/scan/独立査読"]
  selection_reason: "不能証拠の代数的存在を指定原始観測の取得へ接続し、有限最小計画・更新計画に必要な条件を閉じる"
  expected_result_type: proof-obligation-discharged
  lean_targets: [ResidualDualWitness.lean, DualValueAcquisition.lean, ActualDualWitness.lean, KnownValueUpdates.lean, FiberSufficiency.mem_informationFiber, NamedDual.mem_support]
  risks: ["代数的φの存在と実問い合わせからの取得を混同しない", "全候補商を任意Sへ代用しない", "既知情報fiberは元全入力に対応", "更新で未受信値を既知へ入れない", "有限計画/solver/元修復出力は次の到達点へ残す"]
  unchecked: ["実装・検証・査読前"]
```

### Cycle 8 の宣言と前提

受理spine候補は22追加宣言（4新規module、既存2moduleの基本API各1本）。

- `ResidualDualWitness`: `residual`, `residual_value`, `native`, `native_value`, `candidate_changes_iff`, `candidate_change_value_iff`, `failure`。
- `DualValueAcquisition`: `acquisition_iff`, `restriction_iff`, `acquisition_iff_span`, `residual_value_affine`, `residual_acquisition_iff`。
- `KnownValueUpdates`: `information`, `information_apply`, `information_ker`, `fiber_iff`, `acquisition_after_update_iff`。
- `ActualDualWitness`: `actual_failure`, `actual_value`, `actual_acquisition_iff`。
- `AAT.AG.RepairObservationDuality.mem_informationFiber` と `AAT.AG.RelativeRepairComposition.NamedDual.mem_support` は既存構成の基本membership API。既存definition/signatureを変えず下流の定義展開を避ける。

最初の4namespaceは `AAT.AG.RepairObservationDuality.` を補う。新規述語/certificate構造は導入しない。

| 固定条項 | 宣言と同じ入力・値の対応 |
| --- | --- |
| DのG-130不能証拠と残存商 | `residual` は選択列を消す同じphiを商へ下降。`residual_value` と `native_value` は元RHSの評価を保存し、任意Sのselected native cokernelと同じ面を使用 |
| Dの候補名と証拠支持 | `candidate_changes_iff` は元全列compositeの非零と同じcandidate方向の検出値を同値化。`candidate_change_value_iff` は任意の元RHSで追加前後の値差へ対応 |
| Dの不能実入力 | `failure` は独立selected方程式の不能からG-130の `NamedDual.failure_witness` を生成。`actual_failure` は元SupportedRepairの不能から生成し、同じ物理負defectを非零検出。`actual_value` は元always商の同じphiの値を保存 |
| Dの任意known fiberと原始取得 | `acquisition_iff` は非空fiberの全等観測入力を使い核交差と同値化。`restriction_iff` とC7のannihilator/span同定から `acquisition_iff_span`。`residual_acquisition_iff` は指定ell q_S(b₀+Bv)そのものとrestricted spanを全方向対応 |
| Dの元全実入力での取得 | `actual_acquisition_iff` は全パラメータrealizeの正逆と同じ物理負defect式を使い、元入力のLν=s全体で指定した同じphiの評価取得を同値化 |
| Dの保持済み/通知済み値 | `information` は保持値と実通知のproduct。`information_ker` は両核の交差、`fiber_iff` は両指定値の全入力fiber。`acquisition_after_update_iff` はこの更新後未知核上の同じ取得条件へ再適用。追加問い合わせ最適値/有限計画への適用はC9の義務 |

| material premise・構成 | 分類 | 出所とproof-use |
| --- | --- | --- |
| 体k、線形D₀/C/B/L/λ、候補名、全列、b₀、有限候補 | ambient-boundary | G-131 A/Dの同じ元構造。一般補題は有限体より広い体を許す。native比較は既存SelectedCokernelのfinite sumを使用 |
| 有限次元V | ambient-boundary | C7のdouble annihilatorによる同じrestricted評価spanへ使用 |
| 元実入力族、全実現、共通係数、P面整合、線形核輸送 | ambient-boundary、Aの入力条件 | 受理C5の元実修復と方程式・負defect式に適用。realizeの右逆を全実入力取得同値の必要方向へ使用 |
| phiがSの全列を消す | direction-hypothesis（下降API）、`actual_failure`ではdischarge-required・生成済み | 一般下降では定義域条件、失敗生成ではNamedDual.failure_witnessの返却証明から得る。消滅証明だけを入力して不能を仮定しない |
| 原方程式/元修復の不能 | direction-hypothesis | Dの失敗時の分岐。`failure`で同じG-130phiと非零値を生成。有限分岐選択はC9で構成 |
| 非空known fiberのbaseとLνbase=s | direction-hypothesis | 任意fiber全入力の値取得条件で使用。空fiber/全不能判定/基準点探索はC9で生成 |
| 取得するf | discharge-required・両方向存在証明済み | 核交差条件から同じ観測fiber代表元を選び、指定アフィン値を作る。原入力を問い合わせ返信として追加しない。choice存在構成を有限実行計画とは扱わない |
| 商双対下降、元candidate支持、同じ実dual評価 | discharge-required・証明済み | canonical quotient dual、代表元保存native比較、NamedDual全列、C5実方程式から生成 |
| 更新後保持値/通知値 | ambient-boundary | 実際に保持/通知された線形値を指定し、両値のproduct情報と未知kernelを構成。古い未通知値をknownに追加しない |

依存資格：C3 [PR #5200](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5200#issuecomment-5969565903)、C5 [PR #5204](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5204#issuecomment-5970294260)、C7 head `e584b5c485ba09a92f8f48e8da32bb2e56672901` の [受理監査](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5216#issuecomment-5971319879)、G-130 final accepted head `549b7e3ccab1c9686a108530e1b0a4b4f38eee86` の [全体監査](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5179#issuecomment-5966982329)を照合する。G-130のNamedDualRangesの既存内容は同版と同じで、今回基本APIのみを追加。使用するstatement・入力・本proofへの適用をsourceで読む。標準線形代数は固定Mathlib `8f9d9cff6bd728b17a24e163c9402775d9e6a365` のquotient dualとlinear map/kernel API。

```yaml
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "同じG-130不能証拠の残存商下降/値/候補支持と、元全実入力known fiberでの指定評価取得⇔restricted primitive spanを証明"
  exit_criteria_status: ["元RHS/候補支持/任意Sを保持", "元不能入力の同じ非零値", "非空known fiberの取得⇔spanを全方向", "更新後保持/通知fiberと取得条件", "対象22宣言のfocused/個別公理とscan/独立査読をPRに固定"]
  split_reason: none
  completion_candidate: no
  lean_artifacts: [ResidualDualWitness.lean, DualValueAcquisition.lean, ActualDualWitness.lean, KnownValueUpdates.lean, mem_informationFiber, NamedDual.mem_support]
  evidence: [residual_value, native_value, candidate_change_value_iff, actual_failure, actual_value, residual_acquisition_iff, actual_acquisition_iff, acquisition_after_update_iff]
  claim_mapping:
    theorem_names: [actual_failure, candidate_change_value_iff, actual_acquisition_iff, acquisition_after_update_iff]
    source_labels: ["G-131 D", "n1017 §6.3–6.5・§3.5"]
    conjuncts: ["同じ不能証拠の非零残存値", "元追加候補名の同じ支持", "ell q_S(b₀+Bv)取得とrestricted span", "保持済み/通知済みの未知核"]
    undischarged_assumptions: []
    acceptance_point: "Dの同じ双対値取得条件。有限計画と更新最適値適用は次到達点"
    port_status: unported
audits:
  premise_delta:
    discharged: ["同じ不能証拠/任意Sの残存双対", "同じ値と候補支持", "原実入力取得⇔restricted span", "保持/通知更新fiber"]
    remaining: ["Dの有限最小集合生成/値取得/solver/元修復/更新最適値", "E全指定入力/実評価/表/分割/参照式", "最終A–E統合"]
  certificate_provenance:
    discharged: ["NamedDual.failure_witnessとcanonical dual下降", "C5同じ負defect/元修復", "全realizeから原入力fiber", "保持/通知product"]
    unresolved: ["有限停止する計画の生成は次到達点"]
  proof_use:
    used: ["同じD₀/C/S/RHS", "元candidate support", "失敗時非零G-130phi", "L/O差の核", "有限次元restricted span", "全実現と物理負defect", "保持/通知の両情報値"]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: ["対象22宣言のexact source-prefix focused/個別公理raw記録、scan、独立査読をPRへ固定"]
  blocking_findings: []
  next_obligation: "Dの有限最小計画/solver/元修復と更新後最適値"
```

全体は `target-proof-checkpoint`。Dの有限手続きとE、最終A–E統合は未完了。独立査読前のCycle結果はproposal。
