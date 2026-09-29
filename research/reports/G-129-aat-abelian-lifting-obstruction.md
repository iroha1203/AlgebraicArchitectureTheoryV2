# G-129：可換核と持ち上げ障害の証拠対応

一次仕様は [固定GOAL](../goals/G-129-aat-abelian-lifting-obstruction.md)、
実行・査読・mergeの記録は [tracking Issue #5082](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5082) を参照する。

## 第9Cycleの選定と証拠対応

```yaml
ledger_type: target_cycle_result
goal: G-129-aat-abelian-lifting-obstruction
cycle: 9
goal_blob_sha: 9f93a9a1c2ebd9ccd53362e878363144a934b4b8
base_oid: 2593e53e8ada79fd9c182165ba49db0cf6bcc363
tracking_issue: 5082
report_path: research/reports/G-129-aat-abelian-lifting-obstruction.md
selection:
  proof_state_ref: "Issue #5082 第8Cycle merge 後のproof state"
  proof_dag_predecessors:
    - OriginalTowerPresentation.solutionAddTorsor
    - OriginalTowerPresentation.solutionDifference
    - OriginalTowerPresentation.vertexGauge
    - d0ToZ1
    - H1
  milestone: "実際の解を頂点再同定で割った同値類を作り、同じH1のtorsorとして分類する"
  proof_obligations:
    - "C0の実際の頂点作用の軌道関係と解の商を構成する"
    - "二つの商類の差を同じZ1の差のH1類としてwell-definedに降ろす"
    - "H1の作用と差を商に降ろし、非空なとき自由・推移的なtorsorを作る"
    - "基準解の商類からH1との全単射を構成する"
  exit_criteria:
    - "商の関係がC1の元の辺の頂点作用そのものである"
    - "H1が別の係数や抽象補正集合ではなく同じ実解の商へ作用する"
    - "作用・差の消去則と基準商類との全単射をLeanで証明する"
    - "focused check・公理監査・共通scan・独立PRレビュー合格"
  selection_reason: "Cの商分類を閉じ、基準持ち上げ変更とDの解対応の受け皿を作る"
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - ResearchLean/AG/AbelianLiftingObstruction/H1Classification.lean
  risks:
    - "H1を定義するだけで実際の解の軌道との関係を示さない"
    - "商への作用の代表独立性を暗黙にしない"
  unchecked:
    - "独立PRレビュー前"
```

`SolutionOrbit` は元の `Solution` に対する `C⁰` 頂点作用の
`AddAction.orbitRel` による商である。`solutionOrbit_mk_eq_iff` は商類の等号を
実際の頂点再同定に戻す。`solutionOrbit_mk_eq_iff_difference_zero` はその等号と
同じ局所係数の `H¹` における実解の差の零性を同一視する。

任意の基準実解に対する `solutionOrbitEquivH1` は、実解の差から座標を取り、
`H¹` 類の代表コサイクルで元の実解へ作用する相互逆写像である。
`solutionOrbitAddTorsor` の作用と差は `solutionOrbit_vadd_mk` と
`solutionOrbit_vsub_mk` により、各代表上で元の `Solution` の作用・差と一致する。
`solutionOrbit_action_well_defined` と `solutionOrbit_difference_well_defined` は
コサイクル代表と実解代表の変更に対する独立性を明示する。

| 固定target | Lean宣言 | 放電の内容 |
| --- | --- | --- |
| 頂点作用の軌道 | `vertexAddAction`, `SolutionOrbit`, `solutionOrbit_mk_eq_iff` | C1の実際の頂点作用で元の解集合を割る |
| H¹との一致 | `solutionOrbit_mk_eq_iff_difference_zero`, `solutionOrbitEquivH1` | 差の零性と基準解からの全単射 |
| H¹ torsor | `solutionOrbitAddTorsor`, `solutionOrbit_vadd_mk`, `solutionOrbit_vsub_mk` | 同じ実解の商への自由・推移的作用と差 |
| 代表独立性 | `solutionOrbit_action_well_defined`, `solutionOrbit_difference_well_defined` | コサイクルと実解の両代表を変更しても値が一致 |

## 第8Cycleの選定（進行中）

```yaml
ledger_type: target_cycle_result
goal: G-129-aat-abelian-lifting-obstruction
cycle: 8
goal_blob_sha: 9f93a9a1c2ebd9ccd53362e878363144a934b4b8
base_oid: cfc4a3c233f17208ac7e08293d77c27dbe52c738
tracking_issue: 5082
report_path: research/reports/G-129-aat-abelian-lifting-obstruction.md
selection:
  proof_state_ref: "Issue #5082 第7Cycle merge 後のproof state"
  proof_dag_predecessors:
    - OriginalTowerPresentation.solutionAction_edge
    - OriginalTowerPresentation.solutionAddTorsor
    - d0ToZ1
    - kernelTransportHom_fac
  milestone: "頂点での再同定の実際の辺の射の式と、同じcore・比較を保つd0b作用を証明する"
  proof_obligations:
    - "任意のb:C0から実際のSolution上の頂点作用を構成する"
    - "各元の辺の射について指定C1式、すなわち終点左乗と始点右逆乗を証明する"
    - "同じcore・全指定比較の面等式を保ち、補正ではd0bの加算になることを示す"
    - "C0の零元・加法作用を証明する"
  exit_criteria:
    - "C1式が抽象cochainではなく元の辺の実際の射の等式で成立する"
    - "始点の核輸送は選ばれた実際の辺の強い性質から導出される"
    - "core・全face指定比較を同じSolutionで保持する"
    - "focused check・公理監査・共通scan・独立PRレビュー合格"
  selection_reason: "頂点再同定を実際の射の作用として固定し、次のH1商の関係を構成できるようにする"
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - ResearchLean/AG/AbelianLiftingObstruction/VertexGauge.lean
  risks:
    - "d0bを単に定義として作用させるだけでC1式を示さない"
    - "元の比較を選び直した比較に替えない"
  unchecked:
    - "独立PRレビュー前"
```

### 第8Cycleの証拠対応

`vertexGauge` は任意の頂点cochain `b` を同じ局所係数の `d0ToZ1` で
`Z¹` に送り、第7Cycleの実際の `Solution` 作用を実行する。
`vertexGauge_correction` は同じ `C¹` の補正が `d⁰b` だけ加算されることを示す。
`selectedEdge_kernel_fac` は同じcoreへの任意の実際の解の元の辺について、
先行する強い持ち上げから実際の核輸送を導き、基準持ち上げと輸送が等しいことを使う。
`vertexGauge_edge_arrow` はGOAL (C1)の始点・終点の射の式をこの元の辺で示す。
作用の値域は `Solution` であり、固定coreと元の指定比較に対する全ての面の等式を
保つ。`vertexGauge_zero` と `vertexGauge_add` は `C⁰` の群法則に対応する。

| 固定target | Lean宣言 | 放電の内容 |
| --- | --- | --- |
| 頂点作用と補正 | `vertexGauge`, `vertexGauge_correction` | 任意の頂点cochainによる実解の再同定と `d⁰b` の加算 |
| 元の辺のC1式 | `selectedEdge_kernel_fac`, `vertexGauge_edge_arrow` | 実際の辺の強い性質から核輸送を使い、両端の核自己同型による射の等式 |
| 頂点作用の群法則 | `vertexGauge_zero`, `vertexGauge_add` | 零元・加法と同じ固定core・比較の解集合への作用 |

focused check は成功し、`#assert_standard_axioms_only` はこのnamespace内の
6宣言で標準公理のみと報告した。

## 第7Cycleの選定（進行中）

```yaml
ledger_type: target_cycle_result
goal: G-129-aat-abelian-lifting-obstruction
cycle: 7
goal_blob_sha: 9f93a9a1c2ebd9ccd53362e878363144a934b4b8
base_oid: b986920dd2d0eef6e85f49d6ab59cbafa3831cf7
tracking_issue: 5082
report_path: research/reports/G-129-aat-abelian-lifting-obstruction.md
selection:
  proof_state_ref: "Issue #5082 第6Cycle merge 後のproof state"
  proof_dag_predecessors:
    - OriginalTowerPresentation.solutionOfCorrection
    - OriginalTowerPresentation.solutionCorrection
    - OriginalTowerPresentation.solutionCorrection_solutionOfCorrection
    - OriginalTowerPresentation.solutionOfCorrection_solutionCorrection
    - Z1
  milestone: "実際のSol(a)へのZ1自由推移作用と、任意の二解の一意な差を構成する"
  proof_obligations:
    - "同じ元の辺の核補正からZ1の各元の実際の解への作用を作る"
    - "作用の零元・加法法則、自由性、推移性を証明する"
    - "任意の二つの実際の解の差を一意なZ1の元として抽出し、基準解からの全単射を構成する"
  exit_criteria:
    - "作用は抽象cochain解だけでなく元の辺の実際のSolutionに作用する"
    - "差の抽出が同じ元の辺の核に由来し、自由・推移・一意である"
    - "非空なときのZ1 torsorと基準解との全単射をLeanで証明する"
    - "focused check・公理監査・共通scan・独立PRレビュー合格"
  selection_reason: "Cの第一段階を実際の解で閉じ、頂点再同定とH1商の入力を作る"
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - ResearchLean/AG/AbelianLiftingObstruction/SolutionTorsor.lean
  risks:
    - "補正方程式の解だけのtorsorをSol(a)のtorsorと呼ばない"
    - "基準解なしに非空性を仮定せずtorsorを構成しない"
  unchecked:
    - "独立PRレビュー前"
```

### 第7Cycleの証拠対応

`solutionAction` は実際の `Solution` の元の辺持ち上げから核補正を取り出し、
`Z1` の元を足して実際の `Solution` へ戻す。`solutionAction_correction` は
この操作が同じ `C¹` で加算になっていることを示す。`solutionAction_edge` は
各元の辺の持ち上げが核の包含値の左乗で変わることを直接示す。`solutionDifference` は任意の
二解の実際の核補正の差から `Z1` を構成し、`solutionDifference_action` と
`solutionDifference_solutionAction` が自由性・推移性・差の一意性を証明する。
`solutionAddTorsor` は実際の `Solution` 上の `AddTorsor` instance であり、
非空性のみを条件として持つ。`solutionEquivZ1` は基準解を選んだときの全単射である。

| 固定target | Lean宣言 | 放電の内容 |
| --- | --- | --- |
| `Z¹` の実際の解への作用 | `solutionAction`, `solutionAction_correction`, `solutionAction_edge`, `solutionAction_zero`, `solutionAction_add` | 元の辺の核補正による作用と群法則 |
| 二解の一意な差 | `solutionDifference`, `solutionDifference_action`, `solutionDifference_solutionAction`, `solutionAction_existsUnique` | 同じ `Z¹` の元の抽出、自由性、推移性 |
| 非空な解の torsor | `solutionAddTorsor`, `solutionEquivZ1` | `Solution` 上の `AddTorsor` と基準解からの全単射 |

focused check と単一モジュール targeted build は成功し、
`#assert_standard_axioms_only` はこのnamespace内の12宣言で標準公理のみと報告した。

## 第6Cycleの選定

```yaml
ledger_type: target_cycle_result
goal: G-129-aat-abelian-lifting-obstruction
cycle: 6
goal_blob_sha: 9f93a9a1c2ebd9ccd53362e878363144a934b4b8
base_oid: d185e3db4451f27a5549c76a5ec35b2c9b252a97
tracking_issue: 5082
report_path: research/reports/G-129-aat-abelian-lifting-obstruction.md
selection:
  proof_state_ref: "Issue #5082 第5Cycle merge 後のproof state"
  proof_dag_predecessors:
    - OriginalTowerPresentation.alternativeCorrection
    - OriginalTowerPresentation.alternativeDefect_eq_raw
    - TowerPresentation.correctedDefect_eq
    - TowerPresentation.obstructionClass
    - h2_eq_zero_iff
  milestone: "元の辺持ち上げからSol(a)を独立に定義し、同じH2障害零性と非空性の双方向を証明する"
  proof_obligations:
    - "元の各辺のc_e、固定coreへの射影、指定比較の元の面の射の等式でSol(a)を定義する"
    - "任意のSol(a)とd1h=-δの解を相互に構成し、元の辺の射を保持する"
    - "同じH2の障害類が零であることとSol(a)非空を両向きで証明する"
  exit_criteria:
    - "Sol(a)の定義にdefect方程式を条件として埋め込まない"
    - "実際の辺・面の等式と同じ補正方程式の双方向対応がある"
    - "同じH2でo(a)=0 iff Sol(a)非空"
    - "focused check・公理監査・共通scan・独立PRレビュー合格"
  selection_reason: "B3を完結し、次のCの実際の解集合への作用を可能にする"
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - ResearchLean/AG/AbelianLiftingObstruction/Solutions.lean
  risks:
    - "CoherentAt等の抽象的な再選択をSol(a)と取り違えない"
    - "片方向だけやdefect消滅を入力条件とする解を作らない"
  unchecked:
    - "独立PRレビュー前"
```

### 第6Cycleの証拠対応

`Solution` は元の辺ごとの fiber 自己同型、固定 core への射影、および元の道の
指定比較に関する面の射の等式で定義する。障害類や補正方程式はこの定義のフィールドに
含めない。`correctionChoice_edge` と `correctionChoice_path` は、任意の核補正から
作った元の辺・道の射が、既存の実際の補正済み辺・道と等しいことを示す。
`solutionCorrection_zero` は逆に任意の整合する元の持ち上げの raw defect を同じ核で
零とし、`solution_nonempty_iff_correction` は両方向の構成を与える。
`solutionCorrection_solutionOfCorrection` は補正側での合成が恒等であることを、
`solutionOfCorrection_solutionCorrection` は解側の構造全体で合成が恒等であることを示す。
後者は `correctionChoice_solutionCorrection` による各元の辺の復元から従う。
`obstructionClass_eq_zero_iff_solution` は同じ `H2` の商群の零判定をこの実際の
解集合の非空性へ結ぶ。条件4は `obstructionCocycle` の引数として保持される。

| 固定target | Lean宣言 | 放電の内容 |
| --- | --- | --- |
| 独立した `Sol(a)` | `Solution` | 元の辺持ち上げ、固定core、全ての指定面の射の等式 |
| 補正解との対応 | `solutionCorrection_d1`, `solutionOfCorrection`, `solution_nonempty_iff_correction`, `solutionCorrection_solutionOfCorrection`, `solutionOfCorrection_solutionCorrection` | 同じ辺・道の射を通じた両方向の構成と合成の恒等性 |
| B3 | `obstructionClass_eq_zero_iff_correction`, `obstructionClass_eq_zero_iff_solution` | 同じ実際の核、`C¹`、`C²`、`H²` による零性と非空性の同値 |

focused check と単一モジュール targeted build は成功し、
`#assert_standard_axioms_only` はこのnamespace内の33宣言で標準公理のみと報告した。

## 第5Cycleの選定（進行中）

```yaml
ledger_type: target_cycle_result
goal: G-129-aat-abelian-lifting-obstruction
cycle: 5
goal_blob_sha: 9f93a9a1c2ebd9ccd53362e878363144a934b4b8
base_oid: 623864ed33bfd045177d3c15fafae9d878d3d8cd
tracking_issue: 5082
report_path: research/reports/G-129-aat-abelian-lifting-obstruction.md
selection:
  proof_state_ref: "Issue #5082 第4Cycle merge 後のproof state"
  proof_dag_predecessors:
    - OriginalTowerPresentation.toTower
    - liftDifference
    - TowerPresentation.correctedDefect_eq
    - TowerPresentation.authoredSyzygy_correction_invariant
    - h2_eq_zero_iff
  milestone: "同じ固定coreの任意の別基準持ち上げを実際の核補正へ戻し、H2障害類の基準独立性を証明する"
  proof_obligations:
    - "任意の別持ち上げotherの元の辺と、基準持ち上げへの核補正後の元の辺が同じであることを証明する"
    - "otherから再構成したdefectとCycle4のcorrectedDefectが一致することを証明する"
    - "同じ核・係数・3-cell条件でのH2類を定義し、全otherについて不変であることを証明する"
  exit_criteria:
    - "全otherの元の辺の値と実際の核差の対応がある"
    - "otherの元のdefectとcorrectedDefectの値が一致する"
    - "全otherについて同じH2の障害類が等しい"
    - "focused check・公理監査・共通scan・独立PRレビュー合格"
  selection_reason: "Bの選択によらない障害を、後続B3で実際の解と比較できる形にする"
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - ResearchLean/AG/AbelianLiftingObstruction/ObstructionClass.lean
  risks:
    - "別の選択をC1の方程式だけで置き換えず、元のLとliftから得る辺を保持する"
    - "H2類を異なる係数や仮定付き証明に移さない"
  unchecked:
    - "実装と独立PRレビュー前"
```

### 第5Cycleの証拠対応

`alternativeCorrection` は同じ固定coreに射影する任意の別持ち上げ `other` と
基準持ち上げの差を、実際の射影の核 `liftDifference` から各辺で取り出す。
`alternativeEdge_eq` と `alternativePath_eq` は、元の `L` と `other` から得る
実際の辺・道が、この核補正を基準持ち上げへ実行して得る射と同じであることを示す。
`alternativeTransportData` は `other` の元の辺と元の指定比較を保持する。
`alternativeRawDefect_eq` と `alternativeDefect_eq_raw` は、この別選択で再構成した
raw defect と同じ実際の核の `C²` の値が一致することを示す。

| 固定target | Lean宣言 | 放電の内容 |
| --- | --- | --- |
| 同じcoreの任意の別持ち上げ | `alternativeCorrection`, `alternativeEdge_eq`, `alternativePath_eq` | 全 `other` の元の辺・道を実際の核補正と同定 |
| 別選択のdefect | `alternativeTransportData`, `alternativeCanonical_eq`, `alternativeRawDefect_eq`, `alternativeDefect_eq_raw` | 元の比較と別選択の元の道から生じるraw defectを同じC²の核値へ接続 |
| 条件4・係数 | `alternativeAuthoredSyzygy`, `localCoefficients_path_independent_lift` | 元の指定比較の3-cell条件と、同じ固定coreの道輸送が別選択でも成立 |
| H²障害類 | `obstructionCocycle`, `obstructionClass`, `correctedObstructionClass_eq`, `alternativeObstructionClass_eq` | 同じ有限表示と同じC²・d¹・d²のH²類が全 `other` で等しい |

```yaml
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta:
    - "全otherの元の辺・道を実際の核補正と値で同定"
    - "別選択の元のraw defectを、同じ実際の核にあるcorrectedDefectと同一視"
    - "同じC2,d1,d2,H2の障害類が全otherで不変"
  exit_criteria_status:
    - "全otherの元の辺と核差: alternativeEdge_eq、alternativePath_eq"
    - "別選択の元のdefectとcorrectedDefect: alternativeRawDefect_eq、alternativeDefect_eq_raw"
    - "同じH2の類: alternativeObstructionClass_eq"
    - "focused check・公理guard・共通scan・独立PRレビューは最終headで確認"
  completion_candidate: no
  lean_artifacts:
    - AbelianLiftingObstruction/ObstructionClass.lean
  claim_mapping:
    theorem_names: [alternativeEdge_eq, alternativePath_eq, alternativeDefect_eq_raw, alternativeObstructionClass_eq]
    source_labels: ["Bの基準持ち上げ独立性"]
    undischarged_assumptions: ["A条件1–3は一般定理の明示仮定", "条件4は元の比較のsyzygyとして明示仮定", "otherの固定coreへの射影等式"]
    acceptance_point: "同じcoreの任意の元の別持ち上げから計算した障害類が等しい"
    port_status: unported
audits:
  premise_delta:
    discharged: ["元の別持ち上げの核差", "元の別選択のraw defect一致", "同じH2類の全選択独立"]
    remaining: ["実際のSol(a)と障害零性の双方向対応", "CとD", "指定三例の条件1–4"]
  certificate_provenance:
    discharged: ["fiberPushforwardのkerからのliftDifference", "元のL・other辺射との同一性", "実際のraw defectの核包含", "B2とd2d1からの同じH2類"]
    unresolved: []
  proof_use:
    used: ["全otherの射影等式で核差を生成", "B2をH2の同値へ適用", "元の条件4を別選択のtyped pastingへ移す"]
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  blocking_findings: []
  next_obligation: "元の辺の全持ち上げからSol(a)を独立に定義し、障害零性との双方向を証明する"
```

## 第4Cycleの選定（進行中）

```yaml
ledger_type: target_cycle_result
goal: G-129-aat-abelian-lifting-obstruction
cycle: 4
goal_blob_sha: 9f93a9a1c2ebd9ccd53362e878363144a934b4b8
base_oid: a4c4269d0a961d9b654d43a6efc2e88b0fcfee7e
tracking_issue: 5082
report_path: research/reports/G-129-aat-abelian-lifting-obstruction.md
selection:
  proof_state_ref: "Issue #5082 第3Cycle merge 後のproof state"
  proof_dag_predecessors:
    - TowerPresentation.defect
    - pathReselectionTransition_fac
    - rawFaceDefect_transition
    - pathCorrection
    - d1
  milestone: "任意の実際の核補正で元の辺を再選択し、そのdefectが同じd1だけ変わることを証明する"
  proof_obligations:
    - "核補正の辺再選択を元の辺の射として構成し、道のendpoint transitionがT_w(h)の核包含に等しいと証明する"
    - "再選択した元の指定比較と標準比較のraw defectを実際の核へ制限する"
    - "条件3と実際の核の可換性を用い、全hについてδ^h=δ+d1hを同じC2で証明する"
    - "再選択後も同じ係数輸送と元の3-cell syzygy条件を使えることを証明する"
  exit_criteria:
    - "元の辺への全核補正の実行とendpoint transitionの値が一致"
    - "元のraw defectと再構成した核defectが一致"
    - "同じd1で全補正の変換則を証明"
    - "係数・3-cell条件の再選択独立、focused check・公理監査・共通scan・独立PRレビュー合格"
  selection_reason: "B2と障害類の基準選択独立を先に確立し、実際の解の同値へ接続する"
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - ResearchLean/AG/AbelianLiftingObstruction/Correction.lean
  risks:
    - "抽象的な補正方程式だけに置き換えず、元の辺と元の比較の再選択を保持する"
    - "結論を仮定へ移さず、任意の核補正を量化する"
  unchecked:
    - "実装と独立PRレビュー前"
```

### 第4Cycleの証拠対応

`correctionReselection` は任意の同じ `C¹` の値を実際の核から元の選択済み辺へ掛ける。
`correctedPath_fac` と `pathTransition_eq_correction` は、この辺の実行から作った
endpoint transition が各辺の出現を数える `T_w(h)` の核包含に等しいことを示す。
`correctedFaceDefect` は再選択後の二つの元の道と指定比較からA2を使って実際の核へ
制限した元であり、`correctedFaceDefect_eq_raw` が既存raw defectとの値の一致を固定する。

| 固定target | Lean宣言 | 放電の内容 |
| --- | --- | --- |
| 全核補正の実行 | `correctionReselection`, `correctedEdge_eq`, `correctedPath_fac`, `pathTransition_eq_correction` | 元の選択済み辺への任意の補正と、道全体の総補正を同じ値で結ぶ |
| 再構成したdefect | `correctedCoreAlignment`, `correctedFaceDefect`, `correctedFaceDefect_eq_raw`, `correctedDefect` | 再選択した道の元の指定比較から実際の核defectを作り直し、同じC²に置く |
| B2変換則 | `correctedFaceDefect_eq`, `correctedDefect_eq` | 既存の非可換raw遷移則を条件3で簡約し、可換核の演算で全hについてδ^h=δ+d¹hを証明 |
| 係数・条件4 | `correctedPathKernelTransport_eq`, `correctedPath_localCoefficients`, `authoredSyzygy_correction_invariant` | 同じ道輸送と元の指定比較の3-cell条件を補正後も保持 |

```yaml
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta:
    - "任意の実際の核補正を元の選択済み辺に実行し、道の遷移をT_w(h)と同一視"
    - "再選択した元の比較からdefectを再構成し、既存raw defectとの値の一致を証明"
    - "同じC2とd1でδ^h=δ+d1hを証明し、道の核輸送と条件4の基準独立性を確認"
  exit_criteria_status:
    - "全核補正とendpoint transition: correctedEdge_eq、pathTransition_eq_correction"
    - "実際の再構成defect: correctedFaceDefect_eq_raw"
    - "全hの同じd1変換則: correctedDefect_eq"
    - "係数・3-cell・focused check・公理guard・共通scan・独立PRレビューは最終headで確認"
  completion_candidate: no
  lean_artifacts:
    - AbelianLiftingObstruction/Correction.lean
  claim_mapping:
    theorem_names: [pathTransition_eq_correction, correctedFaceDefect_eq_raw, correctedDefect_eq, correctedPathKernelTransport_eq, authoredSyzygy_correction_invariant]
    source_labels: [B2, "A条件2–4"]
    undischarged_assumptions: ["A条件1–3はTowerPresentationの一般定理の明示仮定", "条件4は元の比較のsyzygyとして明示仮定"]
    acceptance_point: "任意の元の辺の核補正に対する実際のdefect変換則と係数・syzygy独立性"
    port_status: unported
audits:
  premise_delta:
    discharged: ["全核補正の実行", "元のraw defectとの再選択値一致", "B2変換則", "係数と元の3-cell条件の不変性"]
    remaining: ["同じcoreの任意の基準持ち上げ差とH2障害類", "実際の解との双方向対応", "CとD", "指定三例の条件1–4"]
  certificate_provenance:
    discharged: ["元の辺の射からのT_w(h)", "強い持ち上げの一意性でのendpoint transition", "A2から再構成した核defect"]
    unresolved: []
  proof_use:
    used: ["条件1で道の核補正の積順を交換", "条件2で指定比較のwhisker後の全核中心化", "条件3でraw遷移の共役を消去し、指定比較の貼り合わせを保持"]
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  blocking_findings: []
  next_obligation: "同じcoreの基準持ち上げの全差を核補正として表し、H2障害類と実際のSol(a)との同値を構成する"
```

## 第3Cycleの選定（進行中）

```yaml
ledger_type: target_cycle_result
goal: G-129-aat-abelian-lifting-obstruction
cycle: 3
goal_blob_sha: 9f93a9a1c2ebd9ccd53362e878363144a934b4b8
base_oid: d77a15490774f949013a28014b8125a0050e4d2d
tracking_issue: 5082
report_path: research/reports/G-129-aat-abelian-lifting-obstruction.md
selection:
  proof_state_ref: "Issue #5082 第2Cycle merge 後のproof state"
  proof_dag_predecessors:
    - TowerPresentation.localCoefficients
    - faceKernelDefect
    - rawDefect_cocycle_of_authoredSyzygy
    - d2Hom
  milestone: "元の指定比較と標準比較の実際の核差を同じC2へ置き、条件4からd2δ=0を証明する"
  proof_obligations:
    - "A2から元のu*m^-1を実際の核へ制限し、既存raw defectと同一視する"
    - "核の道輸送をwhiskerと一致させ、向きと後続道を保ってpastingRawDefectと加法的評価を接続する"
    - "指定比較の3-cell syzygy条件から同じd2でδがcocycleとなることを証明する"
  exit_criteria:
    - "defectがAと同じ実際の核のC2であり、元のu*m^-1を包含で復元する"
    - "各向き・各貼り合わせでraw defectの値と加法的総和の一致を証明する"
    - "A条件4を使用してd2δ=0を証明する"
    - "focused check・公理監査・共通scan・独立PRレビューが合格する"
  selection_reason: "Bの補正・障害類・実際の解同値が使うdefect cocycleを固定する"
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - ResearchLean/AG/AbelianLiftingObstruction/Defect.lean
  risks:
    - "既存のraw defectと別の補正方程式を定義しない"
    - "条件4をd2d1=0へ混入しない"
    - "3-cellの二つの型付き貼り合わせを同じ始終道で評価する"
  unchecked:
    - "実装と独立PRレビュー前"
```

### 第3Cycleの証拠対応

`TowerPresentation.toTransportData` は第2Cycleで構成した選択済みの元の辺・底の面一致・
指定比較を既存の任意関手上のデータへ移す。`faceDefect` はA2から作った実際の核の元であり、
`faceDefect_eq_raw` は既存の `rawFaceDefect` と包含後の値が同一であることを示す。
その加法化 `defect` は第2Cycleの `localCoefficients` と同じ `C2` に属する。

| 固定target | Lean宣言 | 放電の内容 |
| --- | --- | --- |
| B1の元のdefect | `faceDefect`, `faceDefect_inclusion`, `faceDefect_eq_raw`, `defect` | 元の `u*m⁻¹` を実際の核へ制限し、同じC²へ置く |
| 道・向き付き面 | `whisker_kernel`, `whisker_centralizes`, `reverseFaceDefect`, `orientedFaceDefect_inclusion` | 既存whiskerとAの核輸送の値を一致させ、逆向きを符号反転として評価 |
| 型付き貼り合わせ | `pastingAuthored_centralizes`, `pastingRawDefect_inclusion` | 後続比較による非可換な共役を条件3と道輸送全射性から消し、元のraw defectを同じ符号付き総和へ移す |
| 条件4の使用 | `defect_cocycle` | 指定された二つの3-cell貼り合わせの元の比較等式から、同じ複体の `d²δ=0` を証明 |

条件1の核可換性はAの輸送一致と選択独立性を通じて使用し、条件2の全単射性は
`whisker_centralizes` で終点の核全体への移行に使用する。条件3は指定比較とその
向き付き・全貼り合わせが核を中心化する証明に使用する。条件4は
`AuthoredSyzygy T.toTransportData 1` として、既存の元の比較の貼り合わせ等式を
そのまま保持し、`rawDefect_cocycle_of_authoredSyzygy` を経由して使用する。
複体恒等式 `d²d¹=0` への条件4の混入はない。

```yaml
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta:
    - "元の指定比較と標準比較の核差を、同じC2のdefectとして構成"
    - "向き・後続道・貼り合わせを保持してraw defectと加法的評価を一致"
    - "元の3-cell syzygyから同じd2でdefectのコサイクル性を証明"
  exit_criteria_status:
    - "B1の包含・raw値一致: faceDefect_inclusion、faceDefect_eq_raw"
    - "向き付き面・全貼り合わせ: orientedFaceDefect_inclusion、pastingRawDefect_inclusion"
    - "条件4からd2δ=0: defect_cocycle"
    - "個別focused check・公理guard・共通scan・独立PRレビューは最終headで確認"
  completion_candidate: no
  lean_artifacts:
    - AbelianLiftingObstruction/Defect.lean
  claim_mapping:
    theorem_names: [faceDefect_eq_raw, pastingRawDefect_inclusion, defect_cocycle]
    source_labels: [B1, "A条件4", "Bのcocycle"]
    undischarged_assumptions: ["A条件1–3は一般定理の明示仮定", "A条件4は元の比較のsyzygyとして明示仮定"]
    acceptance_point: "同じ実際の核とC2にある元のdefectが、条件4の下でcocycle"
    port_status: unported
audits:
  premise_delta:
    discharged: ["B1の実際の核所属", "raw defectと加法的貼り合わせの同値", "条件4からコサイクル"]
    remaining: ["任意の辺補正での元のdefectの変換則", "障害類の基準選択独立性", "実際の解との双方向対応", "指定三例の条件1–4"]
  certificate_provenance:
    discharged: ["A2による実際の核所属", "既存raw defectの値の保持", "型付き貼り合わせでの条件4"]
    unresolved: []
  proof_use:
    used: ["条件2の全射性で終点核の中心化", "条件3で各指定比較の共役を消去", "条件4で元のraw defectの二経路を一致"]
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  blocking_findings: []
  next_obligation: "任意の核補正の元の再選択からδ^h=δ+d1hを証明し、障害零性と実際の解の同値へ進む"
```

## 第2Cycleの選定

```yaml
ledger_type: target_cycle_result
goal: G-129-aat-abelian-lifting-obstruction
cycle: 2
goal_blob_sha: 9f93a9a1c2ebd9ccd53362e878363144a934b4b8
base_oid: 158e2024fe1e85c11aa8680542e29269d3488ba5
tracking_issue: 5082
report_path: research/reports/G-129-aat-abelian-lifting-obstruction.md
selection:
  proof_state_ref: "Issue #5082 第1Cycle merge 後のproof state"
  proof_dag_predecessors:
    - kernelTransportHom
    - kernelTransportAddEquiv
    - centralizes_iff_kernelTransport_eq
    - FiniteTransportPresentation
  milestone: "Aの同じ有限表示における局所係数、道・面・3-cellの複体とH1/H2を実際の核輸送から構成する"
  proof_obligations:
    - "元の辺の核輸送を道に合成し、同じcoreの持ち上げから独立にする"
    - "A2と面比較の中心化から道の関係への降下を証明する"
    - "全出現を数える道の総補正、d0・d1・d2と二つの複体等式を証明する"
    - "同じ複体のZ1・H1・H2とnative homologyへの対応を構成する"
  exit_criteria:
    - "実際の塔の原始辺から各係数群・辺輸送を生成し、面関係を放電する"
    - "空道・繰返し・向き・接頭辞・接尾辞を含む式からd1d0=0とd2d1=0を証明する"
    - "H1/H2が上の微分の核と像の商であり、同じnative複体へ対応する"
    - "focused check・全追加宣言の公理監査・共通scan・独立PRレビューが合格する"
  selection_reason: "第1Cycleの実際の核輸送を、BのdefectとCの解分類が共用する同じ複体へつなぐ"
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - ResearchLean/AG/AbelianLiftingObstruction/LocalCoefficients.lean
    - ResearchLean/AG/AbelianLiftingObstruction/Cochains.lean
    - ResearchLean/AG/AbelianLiftingObstruction/Cohomology.lean
  risks:
    - "face_transportを構造体fieldのまま未放電で受理しない"
    - "係数群の有限性を追加しない"
    - "3-cell条件をd2d1=0の仮定へ紛れ込ませない"
    - "元の核・辺・面と同じ対象を保つ"
  unchecked:
    - "固定headの独立PRレビューはPR作成後に実行"
```

### 第2Cycleの証拠対応

`OriginalTowerPresentation` は元の辺 `L`、core の `a`、その lift `ã` と
射影等式を保持する。`selectedUpper` と `selectedLowerStrong` は選択済みの辺と二つの
強い性質を元の入力から構成する。`pathTransport_independent_lift` は同じ core の
任意の二つの lift に対して全道の核輸送を一致させ、
`localCoefficients_path_independent_lift` は降下した局所係数の道輸送へ接続する。

`TowerPresentation` は第1Cycleの実際の `p ⋙ q` 上で選択済みの辺を保持し、同じ辺の
`p.map` が `q` について強いこと、底の道の一致、元の指定比較と(A2)を入力にする。
可換性・核輸送の全単射性・指定比較の中心化は固定target Aの条件1–3であり、
`pathLowerStrong`、`pathKernelTransportBijective`、`edgeCoefficients_face` で
道・面に沿う帰結を証明する。`localCoefficients` はその証明から構成した同じ実際の核である。
`LocalCoefficients.asFunctor` は同じ辺と面の生成関係で割った道の圏から
可換群の圏への関手であり、`descendedTransport_mk` は元の道輸送を返す。

| 固定target | このCycleの主なLean宣言 | 放電の内容 |
| --- | --- | --- |
| Aの原始辺と道 | `kernelTransportHom_comp`, `TowerPresentation.pathLowerStrong`, `pathKernelTransportBijective`, `edgeCoefficients_pathTransport` | 元の射の合成に沿う核輸送、空道、辺ごとの全単射性から全道の全単射性 |
| 元の辺・core・liftとの接続 | `OriginalTowerPresentation.toTower`, `edgeTransport_independent_lift`, `pathTransport_independent_lift`, `localCoefficients_path_independent_lift` | 元の `L/a/ã` から選択済み辺の強い性質と局所係数を構成し、同じcoreの別liftに対する全道の輸送一致を証明 |
| Aの面と局所係数 | `TowerPresentation.edgeCoefficients_face`, `localCoefficients`, `LocalCoefficients.asFunctor` | (A2)・核可換性・指定比較の中心化・道の全射性から面輸送を一致させ、生成関係へ降下 |
| A3の微分 | `pathCorrection`, `d0Hom`, `d1Hom`, `d2Hom`, `pathCorrection_d0`, `faceCorrection_d1`, `pastingCorrection_d1` | 終点の核へ各出現を輸送し、向きと接尾辞を保存して評価 |
| A3の複体 | `d1_d0`, `d2_d1`, `cochainComplex` | 同じ有限表示で二つの合成を零と証明。3-cellの貼り合わせは型付きであり、指定比較のsyzygyを仮定しない |
| A3のコホモロジー | `Z1`, `Z2`, `H1`, `H2`, `h1_eq_zero_iff`, `h2_eq_zero_iff`, `firstCochainHomologyIso`, `secondCochainHomologyIso` | 同じ微分の核・像による商と四項native複体の次数1・2のhomologyへの一致。係数群の有限性は不要 |
| 完了条件2–4の共通表示 | `squarePresentation`, `square_d0`, `square_d1`, `square_d2` | 一頂点・一ループ・面 `e²⇒∅`・先頭/末尾消去の3-cellから `1−ρ`,`1+ρ`,`ρ−1` を計算 |

前提の出所と使用は次の通り。`upper.edgeStrong` と `lowerStrong` はAの
原始辺条件で、道の強さ、射影に沿う輸送、比較の一意性に使用する。
`faceBase` と `coreAlignment` は底の道の一致と(A2)で、元の指定比較と
標準比較の射影一致に使用する。`kernelComm`、`edgeBijective`、
`comparatorCentralizes` はA条件1–3をそのまま保持し、選択独立性・道の
同型性・面輸送の一致に使用する。条件4はBのdefectのコサイクル性で
初めて必要となり、このCycleの `d²d¹=0` の仮定には入れていない。

```yaml
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta:
    - "元のL/a/ãから選択済み辺とその強い性質を構成し、同じcoreの全道輸送独立性を証明"
    - "元の辺の核輸送から全道の同型と合成則を証明"
    - "A2と指定比較の中心化から面関係を放電し、同じ生成関係への関手を構成"
    - "C0からC3、三つの微分、二つの複体等式、H1とH2を構成"
    - "指定の3-cell表示から三つの微分の符号を評価"
  exit_criteria_status:
    - "元のL/a/ãから選択済み辺を構成し、同じcoreの全道輸送独立性を証明: OriginalTowerPresentation"
    - "選択済み辺の実際の塔から面関係を放電: TowerPresentation.edgeCoefficients_face"
    - "d1d0とd2d1: Cochains.lean の直接証明"
    - "H1/H2と同じ四項native複体: firstCochainHomologyIso、secondCochainHomologyIso"
    - "個別focused check・axiom監査を最終差分で実施。独立PRレビューは最終headで再実施"
  completion_candidate: no
  lean_artifacts:
    - AbelianLiftingObstruction/LocalCoefficients.lean
    - AbelianLiftingObstruction/Cochains.lean
    - AbelianLiftingObstruction/Cohomology.lean
    - AbelianLiftingObstruction/PathKernelTransport.lean
    - AbelianLiftingObstruction/TowerPresentation.lean
    - AbelianLiftingObstruction/OriginalTowerPresentation.lean
    - AbelianLiftingObstruction/SquarePresentation.lean
  evidence:
    - "同じ有限表示の実際の核輸送・道の商・微分・コホモロジーのLean宣言"
    - "七つの非aggregate fileの個別focused check、各file末尾のstandard axiom guard"
    - "主要26宣言の #print axioms: propext, Classical.choice, Quot.sound のみ"
  claim_mapping:
    theorem_names: ["OriginalTowerPresentation.localCoefficients_path_independent_lift", "TowerPresentation.localCoefficients", "LocalCoefficients.asFunctor", d1_d0, d2_d1, cochainComplex, firstCochainHomologyIso, secondCochainHomologyIso, square_d0, square_d1, square_d2]
    source_labels: ["Aの局所係数", A3, "完了条件2–4の共通有限表示"]
    conjuncts: ["上の固定target対応表に記載"]
    undischarged_assumptions: ["A条件1–3は一般定理の明示仮定。具体例では後続Cycleで放電"]
    acceptance_point: "元のL/a/ãから同じ実際の核の係数複体を構成し、同じcoreの別liftに対する全道の係数輸送一致を証明。全G-129のcompletion candidateではない"
    port_status: unported
audits:
  premise_delta:
    discharged: ["道の強さ", "道の核輸送の全単射性", "面関係", "二つの複体等式"]
    remaining: ["A条件4を用いる実際のdefectコサイクル", "指定三例のA条件1–4の個別放電"]
  certificate_provenance:
    discharged: ["強い原始辺の合成", "生成された核輸送", "元の指定比較からの面関係", "型付き3-cellの二つの貼り合わせ"]
    unresolved: []
  proof_use:
    used: ["核可換性で面比較", "道の全射性で中心化同値の逆方向", "面輸送一致でd1d0", "型付き貼り合わせでd2d1"]
    unused: ["A条件4はこのCycleのclaimに含めない"]
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: ["七つのfocused check", "全追加宣言のstandard axiom guard", "Research full/aggregate/all-file buildなし"]
  blocking_findings: []
  next_obligation: "元の標準比較と指定比較の差を同じC2へ移し、A条件4からコサイクルを証明する"
```

## 固定参照と第1Cycleの選定

GOALと共通受入基準の適用版は `ed8f19fc6095b61fe0a40d5984af62c5acabd1ba`。
人間が指定した序盤の一括実装を第1Cycleとし、Cycleの粒度と終了条件の記録には
作業開始版 `0ff52f382c5f71c5016d0755f88ec7db34fed14f` のcycle ledgerを用いる。
GOALの数学的要求と受入基準は変更しない。

```yaml
ledger_type: target_cycle_result
goal: G-129-aat-abelian-lifting-obstruction
cycle: 1
goal_blob_sha: 9f93a9a1c2ebd9ccd53362e878363144a934b4b8
base_oid: 0ff52f382c5f71c5016d0755f88ec7db34fed14f
tracking_issue: 5082
report_path: research/reports/G-129-aat-abelian-lifting-obstruction.md
selection:
  proof_state_ref: "Issue #5082 初期proof state"
  proof_dag_predecessors:
    - TransportCoherence.Arbitrary.FiberAut
    - TransportCoherence.Arbitrary.whiskerFiberAutHom
    - CrossStageCoherence.compositeFiberPushforward
    - CrossStageCoherence.InnerFiberAut
    - CrossStageCoherence.FiniteCrossStageWitness
  milestone: "A・Dの実際の核と核輸送を構成し、完了条件4に使う幾何核の可換性と非自明性を証明する"
  proof_obligations:
    - "有限Atom carrier・非空site・実際の被覆・非零raw関係式を持つ幾何入力の核全体の可換性と非自明性"
    - "任意の圏の塔の実際の射影、核、核への包含と核所属の特徴づけ"
    - "強いopcartesian輸送と射影の可換式、核への制限、準同型性、全単射性からの同型"
    - "核の可換性の下で同じcoreの持ち上げに対する輸送の独立性と面の共役・中心化条件"
    - "一般側の核・包含・輸送と第4章の実際の核・射の対応"
  exit_criteria:
    - "採用幾何入力の全計算成分を含む核の可換性・非自明性が追加仮定なしでLeanに受理される"
    - "一般の核輸送が原始射から構成され、射影可換性・核所属・特徴づけ・独立性・面条件が証明される"
    - "第4章との同型が元の自己同型と射影を保ち、同じ輸送を回復する"
    - "対象宣言のfocused check・axiom監査・共通scanと独立PRレビューが合格する"
  selection_reason: "具体的な核の成立と一般側への接続を先に確定し、後続の複体・障害・分類に安定した入力とAPIを渡す"
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - ResearchLean/AG/AbelianLiftingObstruction/GeometryKernel.lean
    - ResearchLean/AG/AbelianLiftingObstruction/Tower.lean
    - ResearchLean/AG/AbelianLiftingObstruction/KernelTransport.lean
    - ResearchLean/AG/AbelianLiftingObstruction/CrossStageKernel.lean
  risks:
    - "係数写像だけで全幾何自己同型を同一視しない"
    - "選択された文脈射と任意のrestriction witnessを同一視しない"
    - "核上の全単射性は一般定理の仮定であり、準同型の構成は放電義務"
    - "射影・自己同型・輸送の対応を元の射で示す"
  unchecked:
    - "選定した証明義務は実装・検証前"
```

## 第1Cycleの構成と証拠

このCycleはAの核・輸送、Bのdefectの核所属、Dの核と輸送の対応を扱う。
A–D全体や完了条件4全体の完了判定ではない。成果は `unported (Research-proved)` とする。

### 具体的な幾何入力

`GeometryInput.package` は既存の有限Atom carrierと `FiniteModel.coreReadingFor` を使う。
文脈の対象とrestrictionの存在関係は既存構成と同じであり、
`PointedContexts.contextPreorder_le_iff` が関係の一致を証明する。
その関係の証人として選ぶrestrictionの各成分は、support・axis・observableの点を
`ArchitectureContext.Extension` に記録したprobe上で指定した値を返す。
これにより、全ての文脈間の自然性を満たす自己写像の各成分が恒等であることを証明する。
`GeomReadHom` の射の型や自然性条件は変更しない。

既存の `FiniteCrossStageWitness.package` が選ぶrestriction witnessと任意の指定した射は、
その存在だけでは同一視できない。このため、既存候補の核が非可換であるという主張はせず、
完了条件4が許す具体入力の選択として上のpackageを構成する。
係数環と非零raw関係式には既存候補の `Int × Int` と対角係数の `X²-X` を再利用する。
siteの非空性、実際の被覆、係数の非自明性、raw関係式の非零性を別々に証明する。

`GeometryKernel.inner_ext` は係数写像の一致から元の全幾何自己同型の一致を導く。
`PairCoefficients.comp_comm` と合わせて、選んだ部分群ではなく実際の
`InnerFiberAut GeometryInput.package` 全体の可換性を証明する。
係数交換 `innerSwap` は元の全幾何射として構成され、非恒等である。
同じ元が核全体と可換であり、どの核元の平方でもないことも証明する。

### 固定targetとの対応

以下のpathは `research/lean/ResearchLean/AG/AbelianLiftingObstruction/` からの相対、
一般宣言のnamespaceは `AAT.AG.AbelianLiftingObstruction` である。

| 条項・選定義務 | 宣言・構成 | 保持する対象と結論 |
| --- | --- | --- |
| A1の実際の射影と核 | `Tower.lean`: `fiberPushforward`, `Kernel`, `kernelInclusion`, `fiberPushforward_eq_one_iff`, `kernelEquivFiberAut` | 任意の圏の塔で、関手の元の自己同型への作用とそのkernelを使用。核所属は実際の `p.map` が恒等であることと同値 |
| A条件2の輸送写像の生成 | `StrongTransport.lean`: `fiberTransportHom`, `fiberTransportHom_fac`, `fiberTransport_unique` | 強いopcartesian射から生成し、因子分解の一意性と準同型性を証明 |
| 射影と輸送の整合、核所属 | `KernelTransport.lean`: `fiberPushforward_transport`, `kernelTransportHom`, `kernelTransportHom_fac`, `kernelTransportHom_unique` | 上下の強いopcartesian性から射影可換性を導き、生成済み輸送を実際の核へ制限 |
| A条件2の同型・加法化 | `kernelTransportEquiv`, `KernelTransportLaws.lean`: `KernelCoefficient`, `kernelTransportAddEquiv` | 同じ生成済み写像の全単射性をGOALの仮定として保持。`Additive` 型タグは核元と包含を保つ |
| 同じcoreを持ち上げる選択からの独立性 | `KernelTransportLaws.lean`: `kernelTransport_independent_lift` | 同じ元の辺への二つの補正の射影が等しいとき、差は核に属し、核の可換性で輸送が一致 |
| A2とB1の核所属 | `KernelComparison.lean`: `canonical_comparison_pushforward`, `faceKernelDefect`, `faceKernelDefect_inclusion` | 同じ元の射のcore整列から `p(m)=p(u)` を導き、消滅を仮定せず `u*m⁻¹` を実際の核へ戻す |
| Aの面の共役式と条件3の同値 | `kernelTransport_face_conjugacy`, `centralizes_iff_kernelTransport_eq` | 元の指定比較による共役式。逆方向には生成済み核輸送の全射性を使用 |
| Dの元の核・包含・射影 | `CrossStageKernel.lean`: `compositeFiberEquiv`, `compositeFiberEquiv_pushforward`, `innerKernelEquiv`, `innerKernelEquiv_hom`, `innerKernelEquiv_inv` | 既存の全自己同型とその逆射をそのまま保持し、`compositeFiberPushforward` と `InnerFiberAut` を回復 |
| Dの元の道の輸送 | `innerKernelEquiv_transport` | 任意の `TwoLayerLiftData`、辺の再選択、道について、同じ原始射の因子分解から既存の `upperWhiskerCompositeFiberAut` と一致 |
| 完了条件4のpackageと核 | `PointedContexts.lean`, `GeometryInput.lean`, `PairCoefficients.lean`, `GeometryKernel.lean` | 有限Atom carrier、非空site、被覆、非零raw関係式と、核全体の可換性・非自明性 |
| 同じ具体入力での条件1–3 | `GeometryKernelTransport.lean`: `actualKernelCommGroup`, `authoredKernelElement_ne_one`, `identityTransport_bijective`, `authored_centralizes` | `innerKernelEquiv` で一般側の実際の核へ渡す。恒等辺の強いopcartesian性、同じ一般写像の全単射性、非恒等比較と核全体の可換性を証明 |

### 前提の出所と使用

| 前提・証拠 | 分類・生成元 | 実際の使用先 |
| --- | --- | --- |
| 任意の圏・関手と上段・下段の強いopcartesian性 | Aの原始入力 | comparatorの構成と一意性、輸送準同型、射影可換性 |
| 同じcoreの二つの持ち上げ、A2の射影整列 | Aの原始入力・方向仮定 | `liftDifference` の核所属、`canonical_comparison_pushforward`、`faceKernelDefect` |
| 核全体の可換性 | 一般側ではA条件1、具体側では `GeometryKernel.inner_mul_comm` から放電 | `kernelTransport_eq_of_kernel_comparison` とauthored intertwiningの核元の交換 |
| 生成済み核輸送の全単射性 | 一般側ではA条件2、具体側では `kernelTransport_identity` から放電 | `kernelTransportEquiv` の逆写像、中心化同値の逆方向では全射性 |
| 面比較と核全体の可換性 | A条件3との同値を証明、具体側では核元の包含と可換性から放電 | 面の二つの輸送の一致 |
| 文脈restrictionの証人 | 元のrestriction関係から生成。probeでは明示構成 | 自然性からsupport・axis・observable成分が恒等になる証明 |
| 幾何射のraw関係保存・可換square | `GeometryInput` の対角係数と係数交換から構成 | 全幾何同型 `innerSwap` の実在と非自明性 |
| 3-cellのsyzygy | 後続Cycleの原始入力・具体例の証明義務 | 今回は複体・コサイクルを主張しないため未使用 |

既存依存として、G-109の第4章構成(受理PR #4029)、F18の任意関手上の輸送
(受理PR #4901)、既存の幾何packageと有限Atom構成を使う。
このCycleでは依存APIの型と呼出箇所を確認し、元の射を保つ接続を新たに証明する。
既存の受理済み定理そのものを再包装して新しい中心成果とはしない。

## 第1Cycleの結果と監査提案

正式な受理判定は固定headに対するPR監査コメントに置く。

```yaml
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta:
    - "具体packageの全幾何核の可換性と非自明性を構成から証明"
    - "任意の塔の実際の射影・核・包含・核所属同値を構成"
    - "強いopcartesian射から準同型を生成し、射影可換性と核所属を証明"
    - "同じcoreの持ち上げによる輸送の独立性、面共役式、中心化との両方向を証明"
    - "第4章の元の全自己同型、射影、包含、任意の道の輸送への対応を証明"
  exit_criteria_status:
    - "全幾何核: GeometryKernel.inner_mul_comm と GeometryInput.innerSwap_ne_one"
    - "一般の核輸送: KernelTransport・KernelComparison・KernelTransportLaws"
    - "第4章の射の保存: CrossStageKernelのhom/inv・pushforward・transport定理"
    - "機械検証は下記。独立PRレビューによる最終判定は固定headの監査コメント"
  split_reason: none
  completion_candidate: no
  lean_artifacts:
    - AbelianLiftingObstruction/Tower.lean
    - AbelianLiftingObstruction/PointedContexts.lean
    - AbelianLiftingObstruction/GeometryInput.lean
    - AbelianLiftingObstruction/PairCoefficients.lean
    - AbelianLiftingObstruction/GeometryKernel.lean
    - AbelianLiftingObstruction/StrongTransport.lean
    - AbelianLiftingObstruction/KernelTransport.lean
    - AbelianLiftingObstruction/KernelComparison.lean
    - AbelianLiftingObstruction/CrossStageKernel.lean
    - AbelianLiftingObstruction/KernelTransportLaws.lean
    - AbelianLiftingObstruction/GeometryKernelTransport.lean
  evidence:
    - "上の固定target対応表と各Lean証明本体"
    - "各file末尾のstandard axiom guardと全136宣言のprint axioms"
  claim_mapping:
    theorem_names:
      - GeometryKernel.inner_mul_comm
      - GeometryInput.innerSwap_ne_one
      - fiberPushforward_transport
      - kernelTransport_independent_lift
      - centralizes_iff_kernelTransport_eq
      - innerKernelEquiv_transport
    source_labels: [A1, A2, "A条件1–3", B1, "Dの核・輸送", "完了条件4の入力と核"]
    conjuncts: ["上の固定target対応表に記載"]
    undischarged_assumptions: ["このCycleの選定義務にはなし。一般定理が保持するAの明示仮定は前提表を参照"]
    acceptance_point: "選定した5義務を同じ実際の核・射で接続した。正式受理は独立PR監査"
    port_status: unported

audits:
  premise_delta:
    discharged: ["核輸送の生成・準同型・核所属", "具体幾何核全体の可換性と非自明性", "具体恒等辺の強いopcartesian性と核輸送の全単射性", "具体非恒等比較と核全体の可換性"]
    remaining: ["一般側のA条件1–4は固定targetの仮定として保持", "3-cell付き具体有限表示への統合とsyzygyの評価は後続義務"]
  certificate_provenance:
    discharged: ["canonicalFiberComparatorの生成と一意性", "元の射影のkernel", "probe restrictionの明示構成", "係数交換の全幾何同型", "Arrow-preserving innerKernelEquiv"]
    unresolved: []
  proof_use:
    used: ["上下の強いopcartesian性で輸送と射影の一意性", "core整列でdefectの核所属", "核可換性で基準独立性と面共役", "輸送全射性で中心化同値の逆方向", "全幾何成分の自然性で核の可換性", "元のpathの因子分解で第4章輸送との一致"]
    unused: ["3-cell syzygyはこのCycleのclaimの前提にしていない"]
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "11個の非aggregate fileの個別Lean check"
    - "追加136宣言すべてのprint axioms: 標準公理のみ"
    - "Research import方向・package方向、placeholder、hidden/bidi、privacy、diff check"
  blocking_findings: []
  next_obligation: "同じ核輸送から道の関係への降下・A3の複体を構成し、B–CとDのdefect/解への対応、指定された3例を証明"
```

### 再現可能な検証

対象を一つずつ指定する。Research全体、aggregate、全file loopのbuildは行わない。

```sh
research/lean/check_research_modules.sh --focused ResearchLean/AG/AbelianLiftingObstruction/GeometryKernelTransport.lean
.github/lean_quality/check_research_import_direction.sh
.github/lean_quality/check_research_package_direction.sh
git diff --check
```

他の10fileも実装時に個別指定で検証する。依存のcompiled cacheはtoolchain・manifest・
ソースの一致を確認したものを用い、不足した二つの依存fileだけを個別に検証する。
各fileの `#assert_standard_axioms_only` に加え、全136宣言の `#print axioms` を
単一のscratchから確認する。実行結果とログのhashはPRの検証記録に置く。

## 後続の証明義務

Aの道の関係への降下、同じ有限表示の `C⁰`–`C³` と微分、二つの複体の等式は未実装。
Bのdefect変換則・コサイクル条件・障害類・実際の解との両方向、Cの二つのtorsorと
頂点での再同定、Dの既存defect・解・G-127群拡大への全対応も後続義務である。
完了条件2・3の指定例、および完了条件4の3-cell付き表示・core整列・syzygy・障害評価は、
今回の幾何入力と核のAPIを用いて証明する。G-129全体の状態はactiveのままとする。
