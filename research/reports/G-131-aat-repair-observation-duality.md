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


## Cycle 9：有限最小計画・数値求解と同じ元修復への復元

```yaml
ledger_type: target_cycle_result
goal: G-131-aat-repair-observation-duality
cycle: 9
goal_blob_sha: 054fea81b916c4d4a470b74af3e13c6cc5dde01c
base_oid: 7e45cecd592f4831613ee0e851a61dab41bd0268
tracking_issue: 5133
report_path: research/reports/G-131-aat-repair-observation-duality.md
selection:
  proof_state_ref: "C8 PR #5219受理・merge 7e45cecd592f4831613ee0e851a61dab41bd0268。selectionは初期3c6963454上に固定、受理後baseを同期"
  proof_dag_predecessors: [minimum, decision_optimum_eq, numerical_optimum_eq, PrimitiveQueries.Run.deterministic, FiniteElimination.Enumeration, FiniteMatrixInterface.linearSection, FiniteMatrixInterface.section_regular, ActualFamilyCoordinates.restore, KnownValueUpdates.information_ker]
  milestone: "Dのknown有限dataから値取得前に最小計画を生成し、停止する原始問い合わせ/判定/全数値求解/元修復への復元・更新最適値を接続"
  proof_obligations: ["完全な原始index/parameter列挙から核十分性と最小固定集合を有限探索", "G-130 finite sectionを同じ全DS行列からRHS非依存で生成", "既知情報とvisible返信だけを使う有限応答fiber/値回収", "生成した数値求解と判定を全入力正答/停止/最適値へ", "成功base/全不能/十分集合なしの分岐と識別不能実入力", "同じ元修復・全数値補正の復元と更新後未知核の最適値"]
  exit_criteria: ["有限計画が供給された十分集合/正答を受け取らず生成", "最小固定集合の十分性/最小費用/不能証拠", "全実行の停止/正答/重複を含む費用", "同じDS/B/b₀で元操作への復元", "未通知値を使わず更新最適値へ", "focused/全宣言公理/scan/独立査読"]
  selection_reason: "Cの自由計算での存在とDの取得条件を、同じ有限symbolic dataと元実出力へ接続"
  expected_result_type: proof-obligation-discharged
  lean_targets: [FiniteMinimumPlan.lean, FiniteMatrixSolver.lean, FinitePrimitiveProcedure.lean, FiniteObservedValues.lean, FinitePlanningFailures.lean, FiniteRepairPlanning.lean, FinitePlanningBranches.lean, FiniteFullCoordinates.lean, PrimitiveOutputEquivalence.lean, FiniteCoordinatePlanning.lean, ActualFinitePlanning.lean, UpdatedPlanning.lean, FiniteDualAcquisition.lean, FiniteModelEnumerations.lean, QueryOptimum.sufficientSet_iff, QueryOptimum.valid_decision_iff, QueryOptimum.le_minimum, PrimitiveQueries.transcript_nil, PrimitiveQueries.transcript_length, PrimitiveQueries.transcript_append, PrimitiveQueries.transcript_singleton, FiberSufficiency.validOutput_some_iff, FiberSufficiency.validOutput_none_iff, FiberSufficiency.affineRhs_apply]
  risks: ["未知v/rhsを実行手続きへ追加しない", "choice存在を実行finite searchと混同しない", "判定はqB、数値はBの核", "全数値を確定して元操作へ復元", "全不能零と十分集合なしを区別", "同じstructure行列/核輸送を再生成せず更新値だけを変える"]
  unchecked: ["実装・検証・査読前"]
```

### C9の宣言・生成経路

固定target D / n1017 §6.3–6.5、C / n1017 §6.1–6.2の有限構成を接続する。
新規14 moduleと既存基本API10宣言、明示宣言計132件を今回のspineとする。
名前は下表のnamespaceを補い、先行C1–C8の宣言を今回のdeltaに数えない。

| file・namespace | 今回の明示宣言 |
| --- | --- |
| `FiberSufficiency.lean` / `AAT.AG.RepairObservationDuality` | `validOutput_some_iff`, `validOutput_none_iff`, `affineRhs_apply` |
| `QueryOptimum.lean` / `AAT.AG.RepairObservationDuality` | `sufficientSet_iff`, `valid_decision_iff`, `le_minimum` |
| `PrimitiveQueries.lean` / `AAT.AG.RepairObservationDuality.PrimitiveQueries` | `transcript_nil`, `transcript_length`, `transcript_append`, `transcript_singleton` |
| `FiniteMinimumPlan.lean` / `AAT.AG.RepairObservationDuality.FiniteMinimumPlan` | `questions`, `mem_questions`, `questions_nodup`, `questions_toFinset`, `questions_length`, `sets`, `mem_sets`, `test`, `test_iff`, `sufficientSets`, `mem_sufficientSets`, `plan`, `plan_spec`, `plan_none_iff`, `plan_card` |
| `FiniteMatrixSolver.lean` / `AAT.AG.RepairObservationDuality.FiniteMatrixSolver` | `differential`, `differential_apply`, `generatedSection`, `section_regular`, `solve`, `solve_some_iff`, `solve_none_iff`, `solve_valid`, `residual`, `residual_zero_iff`, `residual_comp_ker` |
| `FinitePrimitiveProcedure.lean` / `AAT.AG.RepairObservationDuality.FinitePrimitiveProcedure` | `procedure`, `procedure_apply`, `run_aux`, `run`, `run_iff`, `correct`, `worst_le`, `worst_eq` |
| `FiniteObservedValues.lean` / `AAT.AG.RepairObservationDuality.FiniteObservedValues` | `findInput`, `findInput_spec`, `findInput_isSome`, `findInput_transcript`, `difference_ker`, `recovered_value`, `readAffine`, `readAffine_of_some`, `readAffine_transcript` |
| `FinitePlanningFailures.lean` / `AAT.AG.RepairObservationDuality.FinitePlanningFailures` | `findDirection`, `findDirection_spec`, `findDirection_isSome_iff`, `indistinguishable` |
| `FiniteRepairPlanning.lean` / `AAT.AG.RepairObservationDuality.FiniteRepairPlanning` | `findSuccess`, `findSuccess_spec`, `findSuccess_isSome_iff`, `findSuccess_none_iff`, `numericalFinish`, `numericalFinish_transcript`, `numericalProcedure`, `numericalProcedure_apply`, `numerical_correct`, `numerical_minimum`, `decisionFinish`, `decisionFinish_transcript`, `decisionProcedure`, `decisionProcedure_apply`, `decision_correct`, `decision_minimum` |
| `FinitePlanningBranches.lean` / `AAT.AG.RepairObservationDuality.FinitePlanningBranches` | `plan`, `plan_spec`, `ready_spec`, `impossible_spec`, `failure_spec`, `numerical_ready`, `decision_ready`, `numerical_failure`, `decision_failure`, `impossible_zero` |
| `FiniteFullCoordinates.lean` / `AAT.AG.RepairObservationDuality.FiniteFullCoordinates` | `Index`, `flatten`, `flatten_always`, `flatten_selected`, `inverse_always`, `inverse_selected` |
| `PrimitiveOutputEquivalence.lean` / `AAT.AG.RepairObservationDuality.PrimitiveOutputEquivalence` | `transport`, `transport_apply`, `run_forward`, `run_backward`, `run_iff`, `correct_iff`, `worst_eq`, `transport_symm`, `optimum_eq` |
| `FiniteCoordinatePlanning.lean` / `AAT.AG.RepairObservationDuality.FiniteCoordinatePlanning` | `valid_iff`, `optimum_eq`, `correct_iff`, `ready` |
| `ActualFinitePlanning.lean` / `AAT.AG.RepairObservationDuality.ActualFinitePlanning` | `matrix`, `matrix_differential`, `solve_some_original`, `restore`, `restore_forbidden_zero`, `restore_fixed_arrow`, `restore_value`, `matrix_actual_equation_iff`, `numericalProcedure`, `numericalProcedure_apply`, `numerical_ready`, `actual_failure_pair`, `no_actual_numerical_procedure`, `decision_ready`, `decision_failure_pair`, `no_actual_decision_procedure`, `actual_impossible_zero` |
| `UpdatedPlanning.lean` / `AAT.AG.RepairObservationDuality.UpdatedPlanning` | `sufficient_after_update_iff`, `numerical_ready`, `decision_ready` |
| `FiniteDualAcquisition.lean` / `AAT.AG.RepairObservationDuality.FiniteDualAcquisition` | `minimum_value`, `value_of_span` |
| `FiniteModelEnumerations.lean` / `AAT.AG.RepairObservationDuality.FiniteModelEnumerations` | `finEnumeration`, `finEnumeration_mem`, `parameterEnumeration`, `parameterEnumeration_mem`, `finiteDimensionalParameters`, `finiteDimensionalParameters_mem`, `fullSourceEnumeration`, `fullSourceEnumeration_mem` |

依存DAGは、完全列挙→全原始集合の十分性test/argmin→成功基準点・不能分岐→
visible履歴の有限parameter復元→同じRHSまたは残存値→G-130生成sectionで全数値求解→
全補正座標の両逆→同じ元実修復、の順。

- `FiniteMinimumPlan.plan` は全indexのdedup/sublistsと全parameterの核testを有限にfoldする。
  `plan_spec/plan_card/plan_none_iff` が同じC2の十分性・最小値・不存在へ接続する。
- `FiniteRepairPlanning.findSuccess` は、同じDS行列の生成残差を全known-fiber parameterへ試す。
  成功点、空fiberを含む全不能、十分集合なしを `FinitePlanningBranches.plan_spec` が分類する。
  非零方向を `findDirection` から返す。default零は到達しない分岐であり、そのことを有限探索の
  `isSome` と実返却値の検査から証明する。
- 各 `numericalFinish/decisionFinish` はknown symbolic model、L/sとvisible履歴だけを受け取る。
  未取得のv、物理defect、成功修復、取得済みRHSは実行引数にない。
  matching parameterは有限findで生成し、十分性により同じ全RHSまたは残存値を得る。
  判定は生成projection∘B、数値はBを使用し、商核との一致は `residual_comp_ker`。
- `FiniteMatrixSolver.generatedSection` はG-130 `FiniteMatrixInterface.linearSection` の同じDSを
  値取得前に使用する。全vectorを返し、`solve_some_iff/solve_none_iff/solve_valid` が原方程式に照合。
- `FinitePrimitiveProcedure` は実際のlist/history controllerで有限停止を構成し、全runの返却値・
  全問い合わせlistを一意にする。最悪時回数は全list長であり重複も数える。
  実際の最小listは原index名を保持し重複を除き、C2の全適応手順最適値を達成する。
- `FiniteFullCoordinates.flatten` はMathlibの `piCurry` と `sumArrowLequivProdArrow` を使用し、
  C6の全always/selected核基底座標を並べ替える。像や残存商への縮約をしない。
  `PrimitiveOutputEquivalence` と `FiniteCoordinatePlanning` が任意の全出力手順を往復し、
  正しさ・重複を含む費用・全手順最適値を保持する。
- `ActualFinitePlanning.matrix_differential` は同じC6の元DSを全basisに評価した行列との一致。
  `numerical_ready/decision_ready` はν/realizeと実評価から全実入力fiberの正答・停止・最適値へ接続。
  `restore/restore_value/restore_forbidden_zero/restore_fixed_arrow` は同じG-130/C6の実復元を使う。
  `actual_failure_pair/decision_failure_pair/no_actual_numerical_procedure` は生成pairの同じ実入力、
  全原始返信、異なる可否/数値目標、全正答手順不存在を保持する。`no_actual_decision_procedure` は元実修復述語の全判定手順不存在、
  `actual_impossible_zero` は全不能実fiberでの両最適値零を証明する。
- `FiniteDualAcquisition.minimum_value/value_of_span` は指定した同じell qS(b₀+Bv)をvisible履歴から
  有限に計算する。constantを落とさず、C8のrestricted span条件に接続する。
- 更新はC8のretained/notified productを同じplannerへ渡す。`UpdatedPlanning` は新未知核と
  更新後の実最小追加回数をC2に同定し、structure行列/生成sectionは同じDのまま使う。

### C9 material premise・既存証拠の使用

| material premise・構成 | 分類 | 出所・生成・proof-use |
| --- | --- | --- |
| 有限体k、有限次元V、有限原始J、same D/B/b₀/L/s | 本文由来・ambient-boundary | 固定GOAL A–Dのknown model。全matrix列挙・比較・核testへ使用 |
| 原セル/field/indexの完全列挙・等値/所属判定 | 本文由来・known有限data | G-130の既知列挙contract。`Enumeration.fintype` が明示リストから有限instanceを作る |
| 全parameter列挙 | 放電済み | `parameterEnumeration` はfull V基底とfield列挙から全値を生成。`finiteDimensionalParameters` は有限次元性からMathlib full basisを準備する。これはonline未知値や正答のchoiceではない |
| 全original source/face座標 | 放電済み | `fullSourceEnumeration` とG-130 `FiniteFamily.indexEnumeration`。元celllistと全頂点核基底/元Sの所属から生成。flatは全値の線形同型 |
| 十分な集合/有限minimum | 放電済み | 全subsetのfinite testとargminから `plan_spec/plan_card`。十分集合は手続きのinputでなく結果分岐のdirection-hypothesis |
| 修復可能な基準点・全不能・不能方向 | 放電済み | `findSuccess_spec/none_iff`、`findDirection_spec/isSome_iff` と `FinitePlanningBranches.plan_spec`。入力データから全分岐を判定・実pairを構成 |
| matching parameter・RHS/残存値 | 放電済み | finite findでknown/history consistencyを検査し、完全列挙と実transcriptの存在から取得。全runでの値一致はsufficient核から得る |
| image section・solver正確性 | 放電済み | 同じG-130生成 `linearSection/section_regular`、matrix multiplication検査からsuccess/noneを分類 |
| 元実族、全実現、実評価、P面整合、全核/線形輸送 | 本文由来・Aの入力条件 | C5/C6と同じ実入力/共通係数を使用。Eでの具体的全放電は次到達点 |
| 原DSと全finite matrixの同一性 | 放電済み | `matrix_differential` が同じC6 DSとinverse flattenを評価して生成。`FiniteCoordinatePlanning.hD` はこの証明から供給し、solverや答えの仮定を追加しない |
| 更新後保持/通知値 | 本文由来・ambient-boundary | C8のspecified retained/notified product、`sufficient_after_update_iff` の新未知核とupdated minimum。古い未通知値は入力なし |

依存資格はC2 [PR #5195](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5195#issuecomment-5969338956)、
C5 [PR #5204](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5204#issuecomment-5970294260)、
C6 [PR #5209](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5209#issuecomment-5970703374)、
C8 [PR #5219](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5219#issuecomment-5971628449)、
G-130 final accepted `549b7e3ccab1c9686a108530e1b0a4b4f38eee86` の
[監査](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5179#issuecomment-5966982329)。
今回の追加10基本API以外の先行本文・Lean signature/定義を変更しない。

### C9検証記録

rootで今回の17対象sourceのみをfocused checkし、各exact source-prefixの後に今回の全明示宣言の
`#print axioms` を追加した監査も実行した。計132件、全17source-prefixがexit 0・warningなし。
標準公理 `propext/Classical.choice/Quot.sound` のみ。
各行は source SHA-256 / 個別公理raw出力log SHA-256。実装者の結果申告は独立査読の代替ではない。

| source | source SHA-256 | raw audit log SHA-256 |
| --- | --- | --- |
| `FiberSufficiency.lean` | `4027b5c0be6a156e31a409b4fd001a6998d5bdba15aabc4cc88cdb867670c069` | `e5cc7a9f8a129716c585ddbca5e35f4ec045c0753fbf8dd92c893000f916c664` |
| `QueryOptimum.lean` | `5e4e0d22f38c6d737f243d2508e6b7ff342aa5210feab60532f7eb68ced4dbf3` | `e5576845c40de2aab1974f89600d8213945454f15fc9e821b5b69b185ed32f54` |
| `FiniteMinimumPlan.lean` | `8a4a1d60df2e3d2e65c857014f828fe931822ed706b98dd62d9a733454d6c7c8` | `3a1fbdd016db375c39a1b095f8dbe7dc4ae36d9df77592c26ce1afa1b5e4e04f` |
| `FiniteMatrixSolver.lean` | `094f0f87058b1d46a27ef51abe7a98a37f0bb46d07b7e40ce0a7a2b22111c504` | `cc10ed2d18fa23e3e1fe35cd374f61e8c42edcabc643f9dd2e3a6117c1422a29` |
| `FinitePrimitiveProcedure.lean` | `3e8243697ecb675f2a0e521f34ceed632dd7f0dc1d38567cf15f26e84eab763c` | `baeed31925531d3d908ae0d602378fb5cf9f91fa4093824648db80896b5c0acd` |
| `FiniteObservedValues.lean` | `5799c77f0811b1f1bf82d1cc78d8c9b2185cbe30767b6e277d7718aa0519e58b` | `0452d0432a0cb7702b58b99f6e8988ec5215017ccf41f98d31c373b4cee5ef50` |
| `FinitePlanningFailures.lean` | `a25ee7c1e19be2d170b26d54b10411641cd96e2b7f42d8e9b14f7d22e2127e44` | `992ab31ec6e990702ddb8649e5680d3609c82e968724851b30484b0b72ae6df6` |
| `FiniteRepairPlanning.lean` | `a1212ed76fcb183bc44e18ea90e44f8c1438aab424a6e6954109dc5438185f9a` | `d4cdcbad11eabe341f301dc3a245a60c6ae445948a16503ed99b0a47828c6115` |
| `FinitePlanningBranches.lean` | `3fb8bd4b4de03f3d4a549584c99c89bd909f9fde34b3045bb044bf76f37efe59` | `e4d0067a78468470739b90668c8ed0da0a4ff44e92ca249b6cdff5ba59ca7c33` |
| `FiniteFullCoordinates.lean` | `b44f0eb86e2db4717e60cf16837e9e10e1a7a4a0800a57ce00e4203fb6418fe6` | `0d6a27e13165405f7f642bd8b091822385818f00034d0c077f2bfc61fc81467a` |
| `PrimitiveOutputEquivalence.lean` | `86567433f8fd12f62c0113e2f1a550b747e5053fd9b9006db8b2af5f1a504683` | `bc3537533755fd018b90fac7e89a51d574d6e4ad89bb56a5bdebfa29f7c38363` |
| `FiniteCoordinatePlanning.lean` | `0b48e46c6ee162531aca73fe71db73b35e9e38c063e9fe8359b75b3d641b8bcd` | `a37dfb8947947ea0ff70fd0c73b9cd51e4e2c521d91a4db58ffccc47e1641a26` |
| `ActualFinitePlanning.lean` | `a19ae6090902fb2af9704582fb34187241a8657c16cb7ff16dd86996e0e2dd5e` | `75b6f4aec9ff0a08b15c3d4d761373c1ed2fe73e522a438d1da2e357db51cd39` |
| `UpdatedPlanning.lean` | `fa59fa761ebec9271f716f3968f690b461e6af0ea50de57125aa20f7ec6989b9` | `74685c46ab0890466acea8bf7d96b85b860dd217af6d6fb540092381c3a0c900` |
| `FiniteDualAcquisition.lean` | `8b14dccaf72e20a2c0464ee85694741bbb3b9cac37f930ac7d4d06582972a3fe` | `d8065e323dc18c07f97c301efaf0e9b080151a085e0db66a9ad4907edc2f5501` |
| `FiniteModelEnumerations.lean` | `6bb66d655174e71f8fca6281e821888c1d8dd22a272f8493ad80660302d6d70e` | `53bf25bb2a1af52b5085620687dd20eec3c5739f09922756c26226febbf9e0d3` |
| `PrimitiveQueries.lean` | `0de8fbb4d70aa189703965ac93c81eb2240ad7c88ae5075aea21f5d7ab842eaa` | `bbb38d74522f1acdfe8ee22469faf35e7a5de48d1aa685f5de9ea5b1538c1513` |

有限実行probeはsource-prefix監査とは別の観測として実行し、`some 1`（全数値の最小card）、
`some 0`（identity行列の判定最小card）、`failure base=0,direction=1`（零微分と問い合わせなし）、
`all impossible`（零微分/既知値1）、`some 1`（visible返信1から全solver値1）を返した。
exit 0、raw出力SHA-256 `78c9441ec6bda259515fd2e0a08fe91f852eab1fc9e6f43e35d49b15102fc5e2`。
これはEの指定族・最適値表の代替ではない。

```yaml
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "finite最小計画/known fiber分岐/visible返信取得/同じG-130section/判定・全数値/全実入力最適値/元修復/更新最適値を接続"
  exit_criteria_status: ["入力から全有限計画と最小cardを生成", "全不能/実pair/不存在を分類", "全controller runの停止/正答/費用", "全元数値/修復/固定辺保持", "同じsectionと保持/通知新kernel", "今回132宣言のfocused/個別公理、共通scan、独立査読はPRで固定"]
  split_reason: none
  completion_candidate: no
  lean_artifacts: ["上記14新moduleと10基本API、132明示宣言"]
  evidence: [plan_spec, plan_card, findSuccess_none_iff, readAffine_transcript, solve_valid, numerical_ready, decision_ready, restore_value, decision_failure_pair, no_actual_numerical_procedure, minimum_value, sufficient_after_update_iff]
  claim_mapping:
    theorem_names: [FinitePlanningBranches.plan_spec, ActualFinitePlanning.numerical_ready, ActualFinitePlanning.decision_ready, ActualFinitePlanning.restore_value, ActualFinitePlanning.decision_failure_pair, UpdatedPlanning.numerical_ready, UpdatedPlanning.decision_ready, FiniteDualAcquisition.minimum_value]
    source_labels: ["G-131 C/D", "n1017 §6.1–6.5・§3.5"]
    conjuncts: ["finite known-data plan", "visible history acquired same RHS", "same G-130 generated section", "full numerical/decision minimum over all procedures", "original repair and indistinguishable actual failure", "retained/notified updated minima"]
    undischarged_assumptions: []
    acceptance_point: "Dの有限構成とC2/C6の同じ実最適値への接続。Eの指定例と最終累積判定を残す"
    port_status: unported
audits:
  premise_delta:
    discharged: ["全parameter/source list生成", "finite sufficient argmin", "成功base/不能direction", "finite matching replies", "same matrix section", "whole coordinates and original repair", "actual minima", "updated unknown kernel/additional minima"]
    remaining: ["E全指定族/実評価/表/具体的局所関係/更新/分割/F2参照式", "最終A–E累積統合"]
  certificate_provenance:
    discharged: ["known finite modelからの全分岐と実failure pair", "same whole matrixからのG-130 section", "visible historyだけの実値", "same inverse full basesと元実修復"]
    unresolved: []
  proof_use:
    used: ["完全field/index/parameter list", "same structural D/B/b₀", "known L/s and original primitive lambda", "same RHS", "全source/face basis", "元族のν/realize/実評価/整合", "retained/notified値"]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: ["17 exact-source prefix、132個別公理、上記SHA", "共通scanと独立査読はPR auditで固定"]
  blocking_findings: []
  next_obligation: "Eの同じW1全族/primitive評価/全表/具体的関係/更新/分割、およびF2四辺K+"
```

全体は `target-proof-checkpoint`。Eと最終A–E累積判定は未完了。
今回Cycle結果は独立査読前のproposalであり、CI greenやmergeだけで全体完了とはしない。

### C9非中心findingへの直接対応

初回4本の査読は中心finding 0、非中心finding 2種類（重複1）を報告した。
`transcript_nil/length/append/singleton` と `le_minimum` を指摘された既存namespaceへ追加し、
`FinitePrimitiveProcedure.run_aux/run` と `FiniteMinimumPlan.plan_card` を基本API呼出しに置換した。
既存statement/def値/import方向/statusは不変。追加5補題は全てfindingで名指しされたAPIである。
修正4fileのexact-source個別公理監査はexit 0・warningなし・標準公理のみ。
rootは依存APIを同期する必要から `PrimitiveQueries` / `QueryOptimum` だけtargeted module checkを実行した。
一度の補題証明elaboration失敗は修正後の再検証で解消した。Research全体buildは未実行。
新規1本のfinding限定確認と最終head CI・統合受理はPR監査コメントへ固定する。

## C10 selection：同じ W1 の原始評価と全出力別最適値

```yaml
ledger_type: target_cycle_result
goal: G-131-aat-repair-observation-duality
cycle: 10
goal_blob_sha: 054fea81b916c4d4a470b74af3e13c6cc5dde01c
base_oid: 854c134166d0cca66bd6168f197b3b1a3580d5e4
tracking_issue: 5133
report_path: research/reports/G-131-aat-repair-observation-duality.md
selection:
  proof_state_ref: "C9受理 PR #5224 / Issue #5133"
  proof_dag_predecessors: ["C1–C9", "G-130 W1 の全核・実修復・元微分・生成局所関係・更新・内部分割"]
  milestone: "G-131 E の W1 指定例の全要求を同じ原始実操作から放電"
  proof_obligations: ["全実現と rx/ry 実評価", "全四補正と禁止元候補を保つ実方程式", "全既知情報ケースの判定/数値最適値と達成", "具体的局所関係の受領情報", "更新値未通知/通知の追加費用", "任意既知 r の分割全出力と同じ応答列・費用", "問い合わせ制限の実識別不能 pair"]
  exit_criteria: ["同じ全原始入力と元 native 微分/defect の同定", "表の全ケースを C/D 一般定理へ接続", "全数値出力から全実操作へ復元", "両局所関係から各値を一意に取得", "更新の1/0と分割の同費用", "成功/不能/nonvacuity と全宣言個別公理監査"]
  selection_reason: "C9の有限計画・取得・復元を指定例の実評価へ適用し、残る E の W1 を閉じる"
  expected_result_type: proof-obligation-discharged
  lean_targets: ["RepairObservationDuality/W1PhysicalInputs.lean", "W1 whole numerical coordinates / costs / relations / updates / subdivision"]
  risks: ["private h と元候補 b/c を省略しない", "関係受領を結論フィールドにしない", "実修復数と query cost を混同しない", "有限 matrix における元微分/支持制約の対応"]
  unchecked: ["W1 全指定要求の実装・検証・独立査読", "F2四辺 K+ は次の到達点", "最終累積照合"]
```

最新 main と tracking Issue に C10 の別担当または未完 PR の記録はなかった。
出所不明の別 worktree の未コミット実装は取り込まず、固有 branch で既受理 API から構成する。
この selection は実装前の proposal であり、全体完了を意味しない。

### C10 証拠と claim mapping

| GOAL / 一次仕様 | 入力からの構成と使用する宣言 | 放電する仕事 |
| --- | --- | --- |
| E 全原始入力 / A / §5.8 | `W1PhysicalInputs.values/realize/values_realize/realize_values/reference_rx/reference_ry/evaluate_values/run_iff` | 全アフィン射影の全核に属する任意の二操作から原始評価を読む。全九値の実現と全実入力の応答列一致 |
| E 同じ実方程式 / A | `W1NumericalEquation.original_differential/original_rhs/equation_iff/actual_iff/restore/restore_parameters/all_subsets` | G-130 の同じ native 相対微分と signed defect。元候補 b/c の全部分集合と零マスク、全 u,h,z,v の実操作への復元 |
| E 表 / C | `W1ObservationCosts.sufficient_numeric/numerical_minimum/numerical_table/sufficient_decision/empty_decision_table/nonempty_decision_cost` | 全九方向から十分条件を判定。一般 C の adaptive replay 下限で全手続き最適値を得る。完全既知・全不能も零回 |
| E 有限取得 / D | `W1GeneratedNumericalPlan.plan_points/points_card/correct/run/optimal/restoreAnswer`、`W1GeneratedDecisionPlan.sufficient/correct/table/optimal` | C9 の有限列挙・最小集合・visible history・G-130 generated section を同じ実入力で使用。全数値回答と停止・正答・正確な費用 |
| E 不能証拠 / D | `W1DualQueries.actual_value/acquisition_iff/read_actual` | G-130 同じ商の dual の実評価 y−x を全物理入力で取得。未知 kernel 上の primitive span と物理取得の同値 |
| E 両具体的関係 / §5.8 | `W1ReceivedRelations.left_iff/right_iff/nonempty/value_eq_of_received_eq/both_fiber_iff/physical_fiber/received_numerical` | 値に依存しない元公開全座標上の生成関係を使い、関係自体が非空で各定数値を一意に決める。両値既知の fiber と零回全数値手続き |
| E 更新 / D | `W1UpdatedQueries.retained_same/original_section_same/original_rows_same/unreceived/notified` | 旧 (0,0) の x=0 を保持。G-130 の全 section/rows を再利用し、y 未通知 1 回・通知済み 0 回を同じ実 controller で達成 |
| E 内部分割 / §5.8 | `PrimitiveOutputMap.run_forward/run_backward/correct/worst_eq/optimum_le`、`W1SubdivisionQueries.restore_factors/restore_old/original_rx/original_ry/actual_solvable_iff/decision_optimum/extend_run/collapse_run/optimum_eq/generated_correct/generated_optimal` | 任意既知 r で全五値 (u,z,v,r,h+r) を生成。任意の split 数値手続きから beta−alpha で元全四値へ戻す。元 rx/ry 実操作・繰返しを含む応答列・全手続き費用を両向きに保持 |
| E 分割全実修復 / §5.8 | `W1SubdivisionValues.old_parameters/collapse_values/split_valid/restore_values/actual_some_iff/actual_none_iff` | 独立に定義された任意の split repair から全五値を読み、全入力数値 validator と往復。none は独立 actual repair の不存在 |
| 完了条件2 rx-only | `W1RestrictedQueries.actual_pair/no_numerical_set/no_decision_set/no_actual_numerical/no_actual_decision` | 元 (0,0)/(0,1) の実現と同じ rx 返答・異なる実修復述語。両言語で全停止・正答 controller の不存在を C の replay 下限から証明 |

数値 solver の固定サイズ四行表示は、元二面の微分に元候補の零支持制約二行を付けた
完全座標の連立表示である。`equation_iff` が同じ元微分の二式と元 mask の全方向を同定し、
`actual_iff` と復元が独立な全実修復へ接続する。ここで最適値の判定に使うのは
`residual_kernel_iff` の同じ RHS からの引き戻し kernel であり、四行表示の全 cokernel を
G-130 の元二面の obstruction quotient と同一視しない。元二面の商と候補名の同型は
受理済み C3/C8 の選択微分と G-130 の同じ対象を使用する。

下限の proof-use は `QueryOptimum.decision_optimum/numerical_optimum` の成功実行 replay。
成功がない完全既知 fiber は `all_impossible_optima_zero` を使用する。
`success_or_both_known` は未既知方向がある各 fiber の成功実入力を入力から構成する。
有限 controller は選択済み成功修復を入力に取らず、構造・permission・L/s と visible 返信のみを読む。
全 private h は `private_values` と native 全座標の対応で保持される。
新しい `ValidSplit` は `valid_examples` で同じ入力の正しい private-h 全値と誤った u の全値を受理/拒否する。
追加の conclusion field、結論を含む structure、未放電 certificate はない。

### C10 material premise と predecessor

| premise | 分類 | 入力からの生成 / 使用先 |
| --- | --- | --- |
| 同じ六辺二面 W1 / P / distinct b,c / whole kernels・basis | 原始入力 / 放電済み predecessor | G-130 `W1AffineInput/W1Regions/W1FiniteCoefficients/W1RelativeCoefficients`。`original_differential/original_rhs/all_subsets` と全実修復へ |
| 全 rx/ry 原始実操作と全実現 | discharge-required | `Inputs` は全射影核。`projection_eq_one_iff/realize_values/values_realize/reference_rx/reference_ry` から全操作・全値を構成 |
| 原始評価一致と情報 fiber | discharge-required | `evaluate_values/run_iff`。`known_apply` の三 regime、`both_fiber_iff` の関係受領、`retained_same` の更新へ |
| 全四補正 / 同じ実微分・負 defect / 元候補支持 | discharge-required | `original_differential/original_rhs/equation_iff/actual_iff/restore_parameters`。全禁止補正・実 face equality は G-130 actualRepair から生成 |
| 成功 base / 全不能分岐 | direction-hypothesis / 構成 | `success_or_both_known`、有限 planner の全列挙と全入力の `numerical_table/empty_decision_table`。全不能を零回へ分岐 |
| 最小集合・全 reply・全出力確定・下限 | discharge-required | C2 exact adaptive optimum と C9 finite argmin/reader/generated section。`correct/run/optimal/points_card` が実 inputs に接続 |
| 具体的局所関係受領の情報 | discharge-required | G-130 generatedRelations/publicValue API から `left_iff/right_iff/nonempty/value_eq_of_received_eq/physical_fiber` |
| 更新時の section/rows 再利用 | discharge-required | G-130 `section_same/generated_rows_same`。保持/通知値を known maps へ渡し 1/0 回へ |
| 分割実操作・全補正・同じ query costs | discharge-required | G-130 expand/collapse と `old_parameters/collapse_values/actual_some_iff/actual_none_iff`。`original_rx/ry`、total output maps の両向き trace/Correct/worst/optimum |
| dual y−x の取得 | discharge-required | G-130 original quotient dual と C8 acquisition/span、C9 finite reader が同じ原始値へ接続 |
| rx-only 不存在 | discharge-required | 全実現の (0,0)/(0,1)、両 ker 失敗、C2 adaptive replay。C9 一般 failure generator の E 実入力条件を放電 |

G-130 の参照版・査読根拠は本 report C9 の固定 predecessor と同じ。
C2/C8/C9 の署名と必要な本文を同じ適用引数で照合した。
今回 status は `unported (Research-proved)` であり、最終全体判定は未実行。

### C10 明示 spine と検証

全12 source の exact source-prefix に、以下の全153公開宣言の `#print axioms` を付けて
root が focused check した。全12件 exit 0、warning なし、通常の
`propext/Classical.choice/Quot.sound` のみ。各行の名前は
`AAT.AG.RepairObservationDuality.<source stem>.` を補う。

| source | 明示 spine declarations | source SHA-256 | raw audit SHA-256 |
| --- | --- | --- | --- |
| `W1PhysicalInputs.lean` | `Inputs`, `Values`, `values`, `realize`, `values_realize`, `realize_values`, `tower`, `reference_rx`, `reference_ry`, `primitive`, `evaluate`, `evaluate_values`, `original_evaluation`, `run_iff` | `4f16b20763ca0c58eacaa3b72387a322c242e84b3c630c61840ac77be452771b` | `7b469e68d1813ae62ca5f4d4a0887106d7206ce531a47abbe07865307d96f87c` |
| `W1NumericalEquation.lean` | `Permissions`, `allowed`, `b_mem`, `c_mem`, `allowed_subset`, `allowed_nonempty_iff`, `all_subsets`, `Corrections`, `parameters`, `parameters_u`, `parameters_h`, `parameters_z`, `parameters_v`, `differential`, `rhsLinear`, `differential_apply`, `rhsLinear_apply`, `original_differential`, `original_rhs`, `equation_iff`, `solvable_iff`, `residual_kernel_iff`, `actual_iff`, `restore`, `restore_parameters`, `private_values`, `permission_examples`, `matrix`, `matrix_differential` | `1c87722229d424d3ac0199dfb7264bb2b90d2e2492480eeae9c1643a15dd2192` | `d3a0fb07a6220c27fe799e5e210e322b4397a26fa09c7571b38e6dccc754ab55` |
| `W1ObservationCosts.lean` | `known`, `known_apply`, `sufficient_numeric`, `sufficient_numeric_card`, `numerical_minimum`, `numerical_cost`, `actual_numerical_cost`, `sufficient_decision`, `empty_decision_minimum`, `nonempty_decision_minimum`, `empty_decision_cost`, `nonempty_decision_cost`, `success_or_both_known`, `numerical_table`, `empty_decision_table` | `4bbb30bbd33bde934be1bd2baad69b5d5b8a00609ce4d80dbdacaee2e4f3da9f` | `ea34233aeeebe0c05b3999ecbb257c30d72035f82975f2644b3fd1f141297b57` |
| `W1GeneratedNumericalPlan.lean` | `indices`, `inputs`, `coordinates`, `plan`, `points`, `plan_points`, `points_card`, `procedure`, `correct`, `run`, `optimal`, `restoreAnswer` | `a9e4f34e260d40e3292b2e7b76e7c0799f0ab37fdcdb35ce5ea991da0816d4d0` | `a551b1cedd756e9b4258fe3b3d41dd5a53c24d52c986705e5d63abfcc26b003e` |
| `W1GeneratedDecisionPlan.lean` | `points`, `points_apply`, `sufficient`, `points_card`, `procedure`, `correct`, `table`, `optimal` | `875f5ea8eea7d3cf005ecd05ae6561cd86cb5a089f929d2a366dac0395749dfa` | `74eb12266cfa6ef429ab686dc9a376f940328f55e59b794ef41d8bcc832a0868` |
| `W1ReceivedRelations.lean` | `received`, `left_iff`, `right_iff`, `e_ne_b`, `e_ne_c`, `nonempty`, `value_eq_of_received_eq`, `both_fiber_iff`, `physical_fiber`, `received_numerical` | `ff1e566a5e7ba49f328564ced7dcc33bfa86a60530e55476cfae88ac7bf60e4c` | `d9dfc98eb0d0a0d82a559ea4a3ec63c19382a4734f8572cf2b64edbf7862067e` |
| `W1RestrictedQueries.lean` | `primitiveRx`, `evaluateRx`, `evaluateRx_values`, `invisible`, `actual_pair`, `no_numerical_set`, `no_decision_set`, `no_actual_numerical`, `no_actual_decision` | `de151220515943f9c27c0bfc293dcb606a446defcc72d6afd12bb1babb0894c7` | `77e5daf4254113b28657b286429825ea3450053e3fecf3736886742f470ee078` |
| `PrimitiveOutputMap.lean` | `transport`, `transport_apply`, `run_forward`, `run_backward`, `correct`, `worst_eq`, `optimum_le` | `7c8831789408322b1b33682db74dc80c881566ea17814cb1d6e8c2a2db1bb880` | `c4d296b0125058fc471ef6218d2bd645dc8a8eade75e25ae026a888276c3631f` |
| `W1UpdatedQueries.lean` | `updated`, `retained_same`, `original_section_same`, `original_rows_same`, `unreceived`, `notified` | `618a965dfa9272bd15110aa6f6f9884716b2978fbd4a5d4921a4de9e46914540` | `0366ae19986e032cd7362d015c177e405261820ab959b1ec4f9004a802eebd1d` |
| `W1SubdivisionQueries.lean` | `SplitCorrections`, `collapse`, `collapse_zero`, `collapse_one`, `collapse_two`, `collapse_three`, `extend`, `collapse_extend`, `extend_collapse`, `ValidSplit`, `validSplit_iff`, `valid_extend_iff`, `valid_examples`, `restore`, `restore_factors`, `restore_old`, `original_rx`, `original_ry`, `actual_solvable_iff`, `decision_valid_iff`, `decision_optimum`, `extendProcedure`, `collapseProcedure`, `optimum_eq`, `extend_run`, `collapse_run`, `generated_correct`, `generated_optimal` | `b383f56a7bdc9fa9a8f716cae882d51368426bc686e782caba99af729fbe407c` | `3a32a8fd82a34e09459b96a4ce02c035c7f39a0f1d9ebaaade378e61167821eb` |
| `W1SubdivisionValues.lean` | `oldValues`, `old_parameters`, `old_valid`, `splitValues`, `collapse_values`, `split_valid`, `restore_values`, `actual_some_iff`, `actual_none_iff` | `f499e8b0e8158c9ce26858d945897b4891be7c30fd6a12c4e122dbc0bbe97f1a` | `f27a4822ccab92bfbb61ef3dc6352ea3360e408a006db1aeb43f0cedb73a522a` |
| `W1DualQueries.lean` | `pullback`, `pullback_apply`, `actual_value`, `acquisition_iff`, `sufficient`, `read_actual` | `490d6b106e484c9671aa75027390427169b2b76ea39b6c06726587d41a1e5db3` | `e6e70c628ab9d451319ab840fca2a3b17ac782ceccaf3d2f4596b9f6fbe92c36` |

個別 focused check では初期の型同定・API適用・有限証明の elaboration error と一度の
kernel timeout を修正し、全 source-prefix の最終検証で解消した。
Research 全体 build と本体の local full build は未実行。
新規 source の placeholder・hidden/BiDi Unicode・privacy、`git diff --check`、
Research import / package direction は PASS。差分 public artifact / legacy / CI は PR head に固定する。
`/goal` 専用の callable 実行機構は現ツールにないため、target theorem loop を直接継続する。

```yaml
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "同じ W1 の全物理入力・評価・元全補正/微分/defect・全表・finite actual controllers・関係受領・dual取得・更新・分割全数値/費用・rx-only不能を放電"
  exit_criteria_status: ["全原始操作/実現/評価", "全S・private h・元二面と全禁止mask", "全 regime の判定/数値表と全adaptive下限", "finite全出力/元実修復/停止/費用", "非空生成関係から両値", "更新1/0と元section/rows", "任意既知rの全split出力と両向きtrace/cost/全actual同定", "全153公開宣言個別公理clean"]
  split_reason: none
  completion_candidate: no
  lean_artifacts: ["上記12 source / 153明示公開宣言"]
  evidence: [actual_iff, numerical_table, empty_decision_table, optimal, physical_fiber, unreceived, notified, generated_optimal, actual_some_iff, actual_none_iff, actual_pair, no_actual_numerical, no_actual_decision]
  claim_mapping:
    theorem_names: [W1NumericalEquation.original_differential, W1PhysicalInputs.values_realize, W1GeneratedNumericalPlan.optimal, W1GeneratedDecisionPlan.optimal, W1ReceivedRelations.received_numerical, W1UpdatedQueries.unreceived, W1UpdatedQueries.notified, W1SubdivisionQueries.generated_optimal, W1SubdivisionValues.actual_some_iff, W1RestrictedQueries.no_actual_decision]
    source_labels: ["G-131 E W1 全要求 / 完了条件2 rx-only", "n1017 §5.8 / §6.3–6.5"]
    conjuncts: ["同じ物理族と全原始評価", "元四補正と native 実方程式", "全表/下限/達成/元実修復", "関係受領/更新/全split出力・trace・cost", "同じ原始入力の具体的不能"]
    undischarged_assumptions: []
    acceptance_point: "E の W1 全指定仕事を放電する proposal。F2 四辺 K+ と最終累積判定を残す"
    port_status: unported
audits:
  premise_delta:
    discharged: ["上記 C10 material premise の全 discharge-required 行"]
    remaining: ["E の F2 四辺 K+ 数値/参照式", "最終 A–E 累積照合"]
  certificate_provenance:
    discharged: ["元全核と実操作", "元微分/defect/同じ独立修復", "入力全列挙と finite argmin/visible reader/generated section", "独立全split修復の数値往復", "同じ原始入力不能 pair"]
    unresolved: []
  proof_use:
    used: ["元 geometry/P/candidates/full bases", "full physical ν/realize/eval", "全四/五補正と元 supports", "retained/notified L/s", "actual generated local relations", "same original quotient dual", "adaptive replay and same exact repeated traces"]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: ["上記12 exact source-prefix/153個別公理/各SHA", "共通scanと標準独立査読・CI は PR audit に固定"]
  blocking_findings: []
  next_obligation: "E の F2 四辺 K+ 候補 c / 全数値2回 / e:=a,c:=b∘a⁻¹ の零回参照式 / 最終累積 A–E 判定"
```

全体は引き続き `target-proof-checkpoint`。C10 の査読前 proposal を全体完了としない。

### C10 非中心 API finding の直接対応

固定 head `92602915ed8efc2ec683e68b28a31064608be181` の正式四本査読では、
数学 A が `No major findings`、数学 B・Lean A/B が `Minor issues`。
中心 finding はなく、三レーンの同じ no-unfold API 指摘を一件へ統合した。
[初回監査](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5227#issuecomment-5973153286)
に claim / premise / 反証試行 / coverage を記録した。

名指しされた `parameters_u/h/z/v` と `collapse_zero/one/two/three` の八公開補題を追加し、
`restore_factors/restore_values` の proof 内部を成分 API に置き換えた。
既存 theorem/def の signature、def/instance 本体、import、台帳 status は変更していない。
変更した三 source の exact prefix だけを再検証し、全153公開宣言の個別公理記録を更新した。
追加八補題と変更箇所は exit 0、warning なし、標準公理のみ。残る九 source/raw は同一 bytes。
直接対応の資格・finding 解消と新 head の CI は PR 監査に固定し、今回の差分だけで全体完了としない。

## C11 selection：同じ F2 四辺 K+ の数値補正と零回参照式

```yaml
ledger_type: target_cycle_result
goal: G-131-aat-repair-observation-duality
cycle: 11
goal_blob_sha: 054fea81b916c4d4a470b74af3e13c6cc5dde01c
base_oid: 8241bddce433837dbea9d76003aff851600dd616
tracking_issue: 5133
report_path: research/reports/G-131-aat-repair-observation-duality.md
selection:
  proof_state_ref: "C10受理 PR #5227 / Issue #5133 comment5973223904"
  proof_dag_predecessors: ["C1–C10", "G-130 NativeAffine全操作/全核/微分/独立実修復対応"]
  milestone: "G-131 E 最後の四辺 K+ 指定要求を同じ原始入力から放電"
  proof_obligations: ["二頂点・四辺 e/a/b/c・二面 e=aとce=b・固定a/b・候補cの構成", "全F2二値の物理実現とa(0)/b(0)の全実評価", "同じnative微分/負defectからu=b1,u+z=b2と全補正/独立実修復の往復", "候補c許可時の全数値出力の2回adaptive最適値と有限達成/元実復元", "値取得なしに参照/逆/合成ASTを生成してe:=a,c:=b∘a⁻¹を零回出力", "両言語が同じ元二面の実等号を満たす"]
  exit_criteria: ["元四辺と型付き面/固定/candidate/全核を保持", "全実入力・全パラメータの実現と原始評価", "同じ実方程式/全数値補正とG130による元native実修復", "数値2回の下限・停止正答達成・全値復元", "同じ実操作の参照式生成と零回/両面の実等号", "非空虚性/正負述語・全宣言個別公理と共通scan"]
  selection_reason: "Eの残る出力言語差を同じ実修復とC/Dへ接続し、A–E最終累積判定の候補へ進める"
  expected_result_type: proof-obligation-discharged
  lean_targets: ["RepairObservationDuality/KPlusInput.lean", "KPlus full actual/native coordinates and numerical/reference queries"]
  risks: ["三辺W5の候補なし分類を四辺K+へ直接適用しない", "参照式を具体数値値へ混入しない", "四辺の全実操作/二面を保持", "原始問い合わせ以外から未知値をcontrollerへ渡さない"]
  unchecked: ["K+構成・検証・独立PR査読", "別の最終A–E累積四本照合"]
```

C11 の終了条件を実装前に固定した。W5 の候補なし `global_iff` は使用せず、
n1017 §5.3 と再利用表 §4 の同じ四辺表示を構成する。
C10 までの証拠は受理済みで、今回の選定は E の残義務全体を扱う。

## C11 result proposal：四辺 K+ の全数値2回と同じ両面の参照式0回

n1017 §5.3 の二頂点 s/t、四辺 e/a/b:s→t と c:t→t、二面 e=a と ce=b を
`KPlusInput.geometry` に保持した。固定部分は全頂点と a/b、候補は元の c のみ。
常時辺 e と候補 c を許した場合を扱う。三辺 W5 の `global_iff` は使用していない。
全物理入力は a/b の全 native affine projection kernel の対であり、値は実操作の零点評価。
`values_realize` と `realize_values` により全 F2² の実現と全物理入力の両方向を証明した。

`KPlusActualRepairs.RealRepairs` は既存の独立な native affine repair 型をそのまま用いる。
元四操作・元線形成分・元二面・固定 a/b によって定義した後、修復の e/c 零点から u/z を読む。
`coordinates_operations` は元四操作の全一致、`actualCoordinatesEquiv` は全数値解との両方向、
`nativeCoordinatesEquiv` は G-130 の同じ元 categorical repair への両方向を与える。

`KPlusNativeEquation` は元二頂点の**全核**を全 F2 に線形同定し、完全な基底を構成した。
固定補正を課す前の native d1 は e−a と e+c−b。固定 a/b を零にした全 cochain を u/z で構成し、
逆に任意の全 native cochain がこの構成に戻ることを証明した。
同じ元実経路の負 defect は (b₁,b₂) であり、生成する D は (u,u+z)、b0=0、B=I。
二行の行列はこの同じ全微分から値取得前に生成する。
`restore_native_real` と `restore_native_correction` は元実操作と全四辺補正の一致を保持する。

`KPlusNumericalQueries` は一般 C の replay 下限と C9 の有限生成を適用する。
全方向から選ぶ finite argmin の最小集合は二原始 index、全停止正答 adaptive controller の最適値も二回。
controller に渡すのは既知の構造と履歴だけで、有限 visible reader と G-130 の generated section が
全 u/z の値を返す。`answer_exists` は全物理入力で実際に some h が得られることを証明する。
その h は同じ元実修復へ戻り、`restoreAnswer_values` が全数値値の保存を確認する。

`KPlusReferencePrograms` の出力は原始 a/b の `ref`、`inverse`、`compose` だけを含む有限 AST。
数値定数・後続原始問い合わせ・未知値の thunk を補正値に混ぜていない。
入力値によらず `e:=a,c:=b∘a⁻¹` の AST を構成し、同じ物理 a/b を解釈に用いる。
独立な `ValidProgram` は元二面の全操作等号そのもので、`program_valid` は全物理入力で両面を証明する。
`restore` は同じ元四操作・元線形部・固定 a/b の actual repair を返す。
`correct/run/worst_zero/optimum_zero` は全 physical controller に対する停止・正答・空 trace・最適零回を証明する。
数値と参照の fiber は同じ全入力 (`physical_fiber`) で、`same_faces` と `optimum_difference` によって
同じ二面の実等号と出力言語別の二回／零回を対応させた。

### C11 material premise と proof-use

| premise | role / provenance / proof-use |
| --- | --- |
| 同じ二頂点・四原始辺・二面・固定 a/b・元候補 c | discharge-required、`geometry/fixedRegion/candidates/edge_partition/candidate_not_fixed` で構成。実経路、全 native d1、復元、両出力へ使用 |
| 全原始物理入力、全値の実現、全実評価 | discharge-required、`Inputs/values/realize/values_realize/realize_values/original_evaluation`。一般 optimum の全入力・識別不能下限、全 actual Correct/Run へ使用 |
| 全核・核輸送・基底・元線形成分・二面の projected 一致 | discharge-required、G-130 の native whole kernel と `reference_linear/linear_faces/kernelCoordinate/bases/basis_value`。同じ native equation と全復元に使用 |
| 原始 word から全微分、負 defect、B=I、全数値解との両方向 | discharge-required、`native_first/native_second/signed_defect/full_cochain/original_differential/equation_iff/actualCoordinatesEquiv/nativeCoordinatesEquiv`。有限行列、replay 最適値、同じ実修復へ使用 |
| 全数値 output・有限最小 plan・visible 取得・生成 section・停止正答 | discharge-required、`sufficient/minimum_two/plan_points/points_card/correct/run/answer_exists/optimal/restoreAnswer_values`。未知の物理値を next に渡さない |
| 参照 AST・逆と合成・同じ元実面・停止と最適零回 | discharge-required、`Expression/Program/program/interpret/valid_iff/program_valid/restore/correct/run/optimum_zero/same_faces`。値取得なしの syntax 生成から解釈と元操作の両面へ使用 |
| 正しい数値 h / 正しい参照 p を復元 API に渡す条件 | direction-hypothesis。一般復元 API の入力であり、全入力 controller の正答は上の構成から別に放電 |
| G-130 native 操作・核・修復同値、一般 C と C9 の有限構成 | 受理済み依存の同じ signature・引数・現在 source を読む。全候補 secondQuotient や W5 の入力を四辺へ読み替えない |
| 新規独立数値／参照述語の非空虚性 | `equations_examples` と `program_examples`。それぞれ同じ物理 input に正例と負例を与え、構文が許されただけで ValidProgram を通さない |

### C11 検証証拠

5 source の非aggregate focused checks と exact source-prefix の全個別 `#print axioms` が exit 0、warning なし。
明示公開宣言160件と AST の生成公開宣言65件、計225件すべてで、依存公理は標準三公理以内。
各 source の末尾 `#assert_standard_axioms_only` も全現在 module の公開宣言を検査する。
Research 全体 build、全 file elaboration loop、ローカル Formal フル build は実行していない。
公理 audit の各 command は `cd research/lean && lake env lean .tmp/G131Cycle11/<Stem>Audit.lean`、
同名 source の全内容を prefix とし、その現在 module の全個別公理出力を raw 記録へ保持する。
次表は source と stdout+stderr の SHA256。AST の全生成宣言も個別出力に含めた。

| source | 個別公理件数 | source SHA256 | raw SHA256 |
| --- | --- | --- | --- |
| `KPlusInput.lean` | 47 | `2c51fb3a4a3f44dc038a51da023a9c632a6795d1d31d65a1429c37e40805445d` | `a7f13a7754db9707849ff4dd80c4f655d6704f06395b2395aa244279c516409b` |
| `KPlusActualRepairs.lean` | 32 | `10bead39d757b4a2add273894fe025b494cc5f4460e1c6e9fce994b49b1ebc93` | `c70f91f7ad696ca97c8df870674f6059bc32d12af1432eb1d31d523fa85adfb6` |
| `KPlusNativeEquation.lean` | 28 | `40e2b2300a1b4487df53bb1a7016c9289b67dcd7b2a5953eda88a067895d792c` | `4455de0a204fc5336d3559cbd668935d6467e7a2db0402a0cc8fcc14ecbda035` |
| `KPlusNumericalQueries.lean` | 22 | `f1bd16b82be289274d8968c6a2cfd2a8f2f70237263f1dc613ab5255a817c3d1` | `5c51ce15beab029c1ba5ab016b4f3d3c90760f6f82f19164d441c1feed816ff1` |
| `KPlusReferencePrograms.lean` | 96 | `e6e3cd0394214aa591f2137be17dac759de92ac34b38df91e06c1d30a77a687d` | `87f27097397f1e2cb93c8da5417656a3cb058687f43dae660dd47aef6f1d5181` |

共通 scan は `git diff --check`、変更七 artifact の hidden/bidi、placeholder、privacy/local path、
Formal→Research import 方向を確認する。標準独立 PR 査読・root acceptance・必要 CI と
その後の**別の**全 A–E 累積四本査読は PR 上の固定 head 記録で確定する。

```yaml
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "Eの同じF2四辺K+を構成し、全数値2回の下限/有限達成/全実復元と、原始参照/逆/合成ASTの零回/同じ両実面へ接続"
  exit_criteria_status: ["同じ原始四辺/二面/固定/candidate", "全物理入力・全F2二値実現・実評価", "全native核/基底と元全d1/負defect/全数値往復", "全adaptive数値2回と有限停止正答達成/全値・実復元", "値に依存しないAST生成/零回最適/元両面", "正負述語と全225個別公理clean"]
  split_reason: none
  completion_candidate: yes
  lean_artifacts: [KPlusInput.lean, KPlusActualRepairs.lean, KPlusNativeEquation.lean, KPlusNumericalQueries.lean, KPlusReferencePrograms.lean]
  evidence: [values_realize, realize_values, original_evaluation, coordinates_operations, actualCoordinatesEquiv, nativeCoordinatesEquiv, full_cochain, native_first, native_second, signed_defect, original_differential, equation_iff, restore_native_correction, numerical_cost, physical_cost, plan_points, points_card, correct, run, answer_exists, optimal, restoreAnswer_values, program_valid, program_examples, optimum_zero, same_faces, optimum_difference]
  claim_mapping:
    source_labels: ["G-131 E最後のF2 K+", "n1017 §5.3", "再利用map §4"]
    conjuncts: ["同じ原始操作/全実現/評価", "候補c許可と全補正", "同じ元native方程式/全値/実復元", "数値2回の全適応下限と有限達成", "零回参照ASTと全元両面等号"]
    undischarged_assumptions: []
    acceptance_point: "指定Eの最後の構成義務を同じ元実修復と一般C/Dへ適用する到達点。最終累積判定は別gate"
    port_status: unported
  remaining_proof_obligations: ["標準PR review/root acceptance/CI", "同じfixed GOALへの別の全A–E最終四本判定"]
audits:
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  blocking_findings: []
  next_obligation: "標準PR gateの後、固定headで最終packetと別の累積四本査読を実行"
```

現在の全体判定は `target-proof-checkpoint`。completion candidate は査読前の提案であり、
四本すべてと統合判定が `No major findings`、全共通 gate が pass になるまで全体完了にしない。

## 最終 A–E 累積照合の対応（C11 completion candidate）

固定 target は active commit `dbed043cb514e8c964589d2e12e982750c87ae83` の GOAL blob
`054fea81b916c4d4a470b74af3e13c6cc5dde01c`。現在カード blob
`61ba46c3af2266cbaafcc2a1f00137b9b08299c9` の変更は設計リンクだけで、target A–E は同じ。
同じ fixed commit の target theorem loop / acceptance / completion ledger / math-lean-review / 共有契約を
読み、現行適用版が同内容であることを照合する。n1017 の SHA256 は
`5eb80b86b932abc5ca923166f879e29473dcbe38c172b57e55326a134841b996`。

| target / 完了条件 | 累積実体の接続（各詳細・前提・方向・使用先は上の cycle 節） |
| --- | --- |
| A：同じ原始入力族・全S・負defect・D_S・q_S・元実修復 | C3 `SelectedCokernel/NativeCorrectionEquation` の任意S商・同じ面代表元・元独立修復。C4–5 `RelativeAffineDefect/PrimitiveAffineDefect/ActualAffineFamily/CoefficientTransport/PrimitiveAffineTower` で全元族から実合成、同じnative微分/defect、全realization/actual predicateへ。全候補商で任意Sを代用しない |
| A：全核の基底座標・禁止候補・実復元・局所記号的関係 | C6 `EquationCoordinates/FullCorrectionCoordinates/ActualFamilyCoordinates/ActualFamilyInterfaces`、C9 `FiniteFullCoordinates/ActualFinitePlanning`。全元terminal核・全always/selected値・元名・禁止値零・同じ元実修復を保持。global↔generated local relationの両方向 |
| B：観測fiber/核/annihilator/quotient dualと像 | C1 `FiberSufficiency`、C7 `LinearObservationDuality/ActualObservationPredicate`。同じq_SBと元実修復の平行移動から、factorization↔kernel inclusion↔span、full quotient dualとq_SBの像へ接続 |
| B：G-128作用・点・原始評価・回数・全適応最適値 | C7 `AdditiveObservationAction/PrimitiveReplyTranslation/PointQuerySimulation/ActualObservationPredicate`。全点(j,a)の既知平行移動と原始点(j,0)、stabilizer、元repair predicate、同じ繰返しを含むtrace/cost、有限minimum/∞/全不能0を対応 |
| C：一般非空情報fiber・判定と全数値出力十分性 | C1 `FiberSufficiency` の二つの同観測入力/独立Solvable/ValidOutput、C2 `PrimitiveQueries/QueryOptimum` の同じ全RHS。一つのhが異なるRHSを同時に解かないことをreplayに使用 |
| C：線形既知L/s・全停止正答adaptive・minimum/∞/全不能0・達成 | C2 `QueryOptimum` と C6 `PrimitiveInputQueries/ActualFamilyCoordinates`。direction witnessを全実現へ戻し、同じprimitive評価/元fullcoords、決定と数値の全procedure optimum、再問い合わせも1回を保持 |
| D：同じ元O/R_S不能評価・元候補支持・観測からの取得 | C8 `ResidualDualWitness/ActualDualWitness/DualValueAcquisition`、C9 `FiniteDualAcquisition`。同じ面代表元・元column名・非零障害・pullback ell q_S(b0+Bv) のknown contribution、restricted spanと取得の両方向 |
| D：値取得前の有限symbolic生成・最小計画・visible取得・全求解・元実復元 | C9 `FiniteMinimumPlan/FinitePrimitiveProcedure/FiniteObservedValues/FiniteMatrixSolver/FiniteRepairPlanning/FiniteCoordinatePlanning/ActualFinitePlanning`。全有限入力/field/index/basisを列挙してargmin/sectionを生成、全出力・停止・正答・費用・元修復を接続 |
| D：十分集合なし・識別不能実入力・更新後の追加観測 | C9 `FinitePlanningFailures/FinitePlanningBranches/ActualFinitePlanning/UpdatedPlanning`、C8 `KnownValueUpdates`。成功基準点と同観測失敗実入力、全不能0、保持/通知L/sを生成し同じsymbolic dataを再利用 |
| E：同じF3 W1全入力・原始評価・元全(u,h,z,v)・全表・受領関係 | C10 `W1PhysicalInputs/W1NumericalEquation/W1ObservationCosts/W1GeneratedNumericalPlan/W1GeneratedDecisionPlan/W1ReceivedRelations`。全四S、全x/y、全known regime、全adaptive下限と有限達成、actual全復元。hを捨てない |
| E：W1更新1/0・全split値・同じrx/ry回数・不能rx-only pair | C10 `W1UpdatedQueries/W1SubdivisionQueries/W1SubdivisionValues/W1RestrictedQueries/W1DualQueries`。任意既知rの全(u,z,v,alpha,beta)、元/分割の任意独立実修復・全値往復、両方向trace/cost、同じ(0,0)/(0,1)のactual不能 |
| E：同じF2四辺K+数値2・原始参照AST0・同じ実両面 | C11上記5source。全物理入力/実現/評価、全native補正/元式/全値復元、C/D数値最適2、値非依存有限syntax生成/全physical参照最適0、same_faces |
| 完了条件1–4 | 上の同じ族/式/primitive/actual predicate全接続、E全ケースの一般A–Dへの適用、十分集合なし/全不能、Research sourceとreport前提/proof-use/有限停止対応。最後に固定headの標準PR gateと別の累積四本gateで判定し、PR/Issueへ同期 |

C1–C10 の受理結果は実装者の全体完了申告として採用しない。
最終査読は固定 GOAL と**現在の累積 source / declaration / 各 raw 公理記録**を直接読む。
現在55 source の746明示公開宣言すべてに個別公理出力を対応させた。
C11 AST の65生成公開宣言も追加で全個別出力を保持する。
初期 C3 の raw が local scratch に残っていなかった二 source と、後で API が追加された
`FiberSufficiency/PrimitiveQueries/QueryOptimum` の三 source は、全 current exact-prefix 個別 audit で
不足を補った。他は受理記録の exact current source-prefix/raw bytes を照合した。
これは五つの必要な単一 file checks であり、Research全体または全55fileのelaboration loopではない。
全 module の path/source hash・全明示宣言名・個別raw/output hash・対応source-prefixを最終packetに対応させ、
欠落・中心未確認・head/hash不一致があれば completion不可とする。

Research上の目標証明と本体への蒸留は区別する。今回の固定GOALが指定する成果先はResearchであり、
`Formal/`への移植は実行していない。G-130とG-131の本体移植状態は引き続き `unported`。
``/goal``用の専用実行機構はこの環境に公開されていないため、同じskillの実装・査読・完了・停止規則を
直接実行している。この制限を未実行の専用機構として記録し、GOALの数学targetは変更しない。
