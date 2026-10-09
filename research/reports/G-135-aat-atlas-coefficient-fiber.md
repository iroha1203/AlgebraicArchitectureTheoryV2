# G-135：固定targetの証拠対応

固定入力はtracking Issue [#5290](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5290)で指定した版を読む。
GOALは `dc6a46a993561233a824848c75ba547b23ddf863` の
`research/goals/G-135-aat-atlas-coefficient-fiber.md`、設計・共通基準は
`05d1c6c5cbdbb299d8d7120376135917b44f6fa1`、既存宣言は
`53b6a674a29807605a943b6f6304e7b17c2da0d6`。

## 現proof state（Cycle 25）

Cycle 1の有限incidence・一般極限・carrier対象/端点APIはPR #5292で受理済み。
Cycle 2の実M→carrier→右Kan→有限次元P→ηはPR #5293で受理済み。
Cycle 3の同じPからのcounit評価εと実u因子化、局所Φ・Γ・Λの構成・成分同定はPR #5294で受理済み。
ε のcochain条件と実u全三次数因子化、原始Φのchain/cochainと包含、Γの関係列、Φ・Γ・Λの実comma成分式は対象fileのLean検証を通過した。
chart→edge・edge→faceの係数自然性と原始端点・辺位置への同定も通過した。
mixed関係・三角形二経路の公開自然性APIとε次数別単射性も対象fileのLean検証を通過した。
Cycle 4の原始L・実ε像の両包含・実商双対同型・標準短完全列・H₀L/H⁰Q零性はPR #5295で受理済み。独立4査読の非中心API指摘に対応して正式再監査し、宣言一覧漏れはreport限定補正と新規直接確認で解消した。
Cycle 5の原始block分解からκ・実H₁L・R・標準H¹Qの同定とforest特殊化はPR #5296で受理済み。
Cycle 6の実τ・五項列・全R補正代表・原始消滅同値・pure消滅・W3の非零τはPR #5297で受理済み。
Cycle 7の原carrier filtration・実graded/SES/native spectral δ・exact couple・E₁/E₂と独立d₂＝同じτはPR #5298で受理済み。
Cycle 8の実核・余核SES、旧診断加法式、保存必要十分とG133相殺零はPR #5299で受理済み。
Cycle 9の局所十分条件・pure保存両方向/全A C3′・同じG107新旧条件はPR #5300で受理済み。
Cycle 10の原三錐・原Qへの擬同型・全次数と符号の対応はPR #5301で受理済み。
Cycle 11の実Law接続・原κ/R/τ/三錐・旧商/寄与和はPR #5302で受理済み。
Cycle 12の全A包含の原P・二射・κ/R/τ・三錐自然性はPR #5303で受理済み。正式再実行1の非中心指摘は有資格な新規単一確認で解消し、mergeとIssue同期を完了した。
Cycle 13の原Law全ラベルと任意部分台の同じ全射・κ/R/τ・三錐図式はPR #5304で受理・merge済み。中心0、非中心F1は有資格新規単一確認で解消した。
Cycle 14のG134原始正操作と部分セル有限合成はPR #5305で受理・merge済み。同じ原a同型・τ核零を接続し、非中心の出所誤記は独立直接確認で解消した。
Cycle 15の面複製はPR #5306で受理・merge済み。原P/η/ε・全A/任意LawのH¹保存と選択面の非零H²余核を同時に接続し、非中心LA-1は有資格新規限定確認で解消した。
Cycle 16の原τ消滅・全A/発生label有限検査はPR #5307で受理・merge済み。正式再査読の中心0、非中心F3は一文限定修正と新規直接確認四資格全PASSで解消した。
Cycle 17の有理表からの商座標と両逆はPR #5309で受理・merge済み。Cycle18の原P/Q全三次数座標・微分・二射はPR #5310、Cycle19の原a/T/R/τ/J全元表示はPR #5312、Cycle20の原κ・成分手順・全A/label保存判定はPR #5313で受理・merge済み。Cycle21のW1a・W1b全指定評価はPR #5314で受理・merge済み。Cycle22のW2全指定評価はPR #5315で受理・merge済み。Cycle23のW3面ありとmだけ除くpairedの全指定評価はPR #5316で受理・merge済み。Cycle24の同G134原表W4全指定評価はPR #5317で受理・merge済み。新規正式再査読数学2/Lean2とrootは全No major findings、reruns1/2。Cycle25の固定W5全数学要求は下記のLean実装・全215個別公理に対応したcompletion candidate。標準PRゲート・実CIと別全目標最終四査読は未実施。全目標はtarget-proof-checkpoint、Formalは未移植。

以下の各selection/result proposalは当時の履歴であり、受理状態は後続受理節へ対応させる。現在のdelta・未放電行は末尾のCycle25台帳で追跡する。

## Cycle 1 selection

```yaml
ledger_type: target_cycle_result
goal: G-135-aat-atlas-coefficient-fiber
cycle: 1
goal_blob_sha: cd5f3e684b7f390558796797874a1f16b52a6b18
base_oid: 76462410a8b325596abb99b4eb77001c011872d2
tracking_issue: 5290
report_path: research/reports/G-135-aat-atlas-coefficient-fiber.md
selection:
  proof_state_ref: Issue5290の固定入力・cycle数0
  proof_dag_predecessors: [G-134のSubsetComparisonとIncidenceSupportedComparison]
  milestone: GOAL A・設計§1–3の原始incidenceからの順像係数と実比較の因子化
  proof_obligations: [有限incidence圏, carrier関手, セル逆像と関係グラフ, 右Kan拡張と成分式, Pと二射, 全三次数の因子化]
  exit_criteria: [重複出現を保持した圏とcarrierの構成, 右Kan拡張の普遍性と成分式の同定, 二射のcochain性と既存uとの全次数等号]
  selection_reason: 全B–Eが依存する独立生成の順像と同じ射を先に構成する
  expected_result_type: proof-obligation-discharged
  lean_targets: [ResearchLean/AG/AtlasCoefficientFiber/Incidence.lean]
  risks: [重複incidence, 混在退化のcarrier, comma圏の成分同定, 未放電条件のfieldへの移動]
  unchecked: [carrierと普遍性と二射は未実装]
```

## Cycle 1 宣言と固定要求の対応

namespaceは `AAT.AG.AtlasCoefficientFiber`。以下はこのcycleの宣言リストであり、
G-135全体の受理済み証拠ではない。

| ファイル | 宣言 | 固定条項への対応 |
| --- | --- | --- |
| `Incidence.lean` | `Inc`, `IncHom`, `incComp`, `incCategory`, `incFinite`, `incHomFinite` | A・設計§2の有限incidence圏。対象は既存の支持subsetセル。chart→edge、edge→face、chart→faceの出現を区別 |
| 同上 | `edgeEndpoint`, `faceEdge`, `faceVertex`, `endpointPosition`, `edgeEndpoint_faceEdge`, `incComp_assoc` | 原始三角形の二経路の正規化と圏の結合律 |
| 同上 | `incCode`, `incCode_injective`, `incHomCode`, `incHomCode_injective` | 有限セルと有限出現位置から対象・射の有限性を導く |
| 同上 | `face_vertex_zero_relation`, `face_vertex_one_relation`, `face_vertex_two_relation`, `chartEdge_left_ne_right`, `edgeFace_ne_of_position_ne` | 三つの二経路の関係と、loopの左右・重複辺位置を保持する証拠 |
| 同上 | `IncidenceFunctorData`, `IncidenceFunctorData.vertexHom`, `endpoint_edge`, `obj`, `map`, `functor` | 生成射と三角形関係から関手を作る一般API。Mから三関係を放電するproducerは未実装 |
| `ConstantLimit.lean` | `RationalObject`, `constantRational`, `invariant_of_zigzag`, `constantRationalCone`, `cone_value_invariant` | 同じ有理係数の定数diagramと連結成分上の関数cone |
| 同上 | `constantRationalConeLift`, `constantRationalConeLift_apply`, `constantRationalConeIsLimit`, `constantRationalLimitIso`, `constantRationalLimitIso_eval` | 任意のconeから線形liftを構成し、極限の普遍性・標準射影への評価式を証明 |
| 同上 | `coefficientPushforward`, `coefficientCounit`, `coefficientIsRightKanExtension`, `coefficientCellIso`, `coefficientCellIso_eval`, `coefficientPushforward_map_eval` | 指定された任意の関手のcomma極限から右Kan拡張を生成し、comma成分式・射の前合成式へ接続する一般API。実Mのcarrierへの適用は未接続 |
| `Carrier.lean` | `degenerate_face_cases` | A・設計§1のFv／Fmの三原始パターンをG-134の符号付き零和から導く |
| 同上 | `Carrier.chart`, `edge`, `face`, `obj`, `edge_of_some`, `edge_of_none`, `face_of_some`, `face_of_vertical`, `face_of_mixed_left`, `face_of_mixed_right`, `chart_val`, `endpointHom` | 同じ原始Mと台輸送からcarrier対象値と左右端点射を構成。面への射と関手性は未実装 |

`IncidenceFunctorData`は生成射の関手APIであり、三関係を入力に保持する。
このAPIへ渡すM由来のdataとその関係の生成が完成するまで、Aのcarrier構成の完了とは扱わない。
`coefficientPushforward`も一般の関手に沿う構成であり、任意の中間複体を
固定targetのPへ読み替える証拠には用いない。実carrierの構成、comma成分から
Φ・Γ・Λへの全単射、係数射の自然性、P・η・εと既存uの同定が必要である。

### 前提の出所と使用

| 前提 | 役割 | 出所・使用先 | 状況 |
| --- | --- | --- | --- |
| 有限な両側のN、K1台、原始端点と三角形の等号 | ambient-boundary | 固定T0、既存`TargetSupportedNerve`。`Inc`の支持セル・有限性と`edgeEndpoint_faceEdge`に使用 | 一般入力として保持 |
| readingの順序、Mのセル写像と支持輸送 | ambient-boundary | 固定T0、G-134の`IncidenceSupportedComparison`とsubset輸送。`Carrier`の計算対象を生成 | 一般入力として保持 |
| 退化面の符号付き零和 | ambient-boundary | Mの原始field。`degenerate_face_cases`で使用し、三パターンを出力する | 派生分類を導出 |
| 任意Ac、Afとhs | direction-hypothesis | `Carrier`の汎用支持輸送。T0のAf=π⁻¹Acならhsは`fun _ ht => ht` | 実P構成への適用は未実装 |
| 一般の圏J、K、関手φ | direction-hypothesis | `ConstantLimit`の一般極限API。標準comma極限・射影・自然性を使用 | Aの実carrier関手への適用は未接続 |
| 生成射の値と三関係 | direction-hypothesis、実Mへの適用ではdischarge-required | `IncidenceFunctorData`の入力。`endpoint_edge`と関手の`map_comp`に使用 | 実Mからのproducerが未実装 |
| Φ・Γ・Λへのcomma成分同定 | discharge-required | A・設計§2 | 未実装 |
| P・η・ε、全次数因子化、L・商双対同定 | discharge-required | A・設計§3–4 | 未実装 |
| κ、R、短完全列、τ、filtration・保存条件・Law・有限判定・W1–W5 | discharge-required | B–E・W | 未実装 |

新規の結論を保持するcertificateは構成していない。完全性、同型、期待rankを
targetの入力に追加していない。原始入力のwitnessはWで構成する義務が残る。

### 依存DAG

- `Incidence` → G-134 `SubsetComparison` → 既存subsetの三角形・支持セル有限性。
- `Carrier` → `Incidence` ＋ G-134 `optionCell_incidence_iff`、同じsubset支持輸送と端点輸送。
- `ConstantLimit` → 固定mathlibの`ConnectedComponents`、`ModuleCat`極限、pointwise右Kan拡張。
- この三ファイルからP・実u・B–E・Wへのproof DAGは未接続。

既存subset輸送と原始Option分類はG-134 Cycle 1の
[PR #5274](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5274)、
[標準査読とacceptance](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5274#issuecomment-6020448130)
で受理されている。使用sourceは指定commitと今回baseでbyte一致することを確認した。
今回の証明では現在のstatementと適用引数を読み、端点等号・台輸送・原始Option分類へ適用した。
mathlibは固定`8f9d9cff6bd728b17a24e163c9402775d9e6a365`、Leanは`v4.28.0`。

## Cycle 1 result proposal

```yaml
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta:
    - 支持セルから有限incidence圏と三角形関係、出現の区別を構成した
    - 一般の定数有理係数diagramの極限とcomma成分式、標準右Kan拡張への接続を構成した
    - 原始退化面の分類、carrier対象値と端点射を構成した
  exit_criteria_status:
    - incidence圏と重複出現の保持はfocused checkと公理監査を確認
    - carrierの面射と三角形関係、実carrier関手は未実装
    - 実comma成分とΦ・Γ・Λの同定、P・二射・因子化は未実装
  split_reason: 有限incidence圏と定数diagramの普遍性は独立に再利用できる一般APIとして完成した。実carrierと成分の対応を追加する前に、この定義・普遍性・支持輸送を独立に監査する。元の終了条件は保持し、未達部分を次cycleへ引き継ぐ。
  completion_candidate: no
  lean_artifacts: [Incidence.lean, ConstantLimit.lean, Carrier.lean]
  evidence: [本reportの宣言対応表]
  claim_mapping:
    theorem_names: [本reportの宣言リスト]
    source_labels: [GOAL A, 設計README§1–2]
    conjuncts: [有限incidence圏, 一般極限API, 原始carrier対象値と端点射]
    undischarged_assumptions: [実carrierの三角形関係と関手性, commaから局所fiberへの成分同定, 実Pと二射の生成]
    acceptance_point: 独立査読前のproof-checkpoint提案。Aの終了条件と全GOALは未達。
    port_status: unported

audits:
  premise_delta:
    discharged: [原始零和からの退化三分類, 支持セルからのincidence有限性, 任意coneからの極限lift]
    remaining: [実carrier関手, 局所fiber同定, Pと二射, Aの残りとB–E・W]
  certificate_provenance:
    discharged: [constantRationalConeIsLimitは任意coneからliftを構成]
    unresolved: [実MからのIncidenceFunctorData producer]
  proof_use:
    used: [原始三角形等号, 原始退化零和, K1支持輸送, coneの自然性, 標準Kan普遍性]
    unused: []
  structure_field_escape: cannot-determine
  route_integrity: cannot-determine
  target_fitting: none-found
  vacuity: cannot-determine
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [対象3ファイルのfocused check, 全明示宣言print axioms, 各ファイル全宣言の標準公理検査]
  blocking_findings: [標準PR査読と必須Issue同期が未実施]
  next_obligation: 実carrierの面射と三角形関係、Φ・Γ・Λとのcomma成分同定
```

`structure_field_escape`等の未確認は実M→carrier→Pの受理経路についての状態であり、
一般APIの仮定をG-135の放電済み入力へ移すことは認めない。
GOAL・恒久設計を変更していない。Formalへの移植は未着手であり、
今回のResearch sourceを本体からimportしない。

## Cycle 1 検証記録

対象非aggregateの3ファイルだけをfocused checkした。各ファイルに全明示宣言の
`#print axioms`と末尾の`#assert_standard_axioms_only`を置いた。

| 対象 | コマンド | 結果・出力SHA-256 |
| --- | --- | --- |
| `Incidence.lean` | `research/lean/check_research_modules.sh --focused ResearchLean/AG/AtlasCoefficientFiber/Incidence.lean` | exit 0、error/warning 0、print 27宣言、axiom audit: 105 declarations under AAT.AG.AtlasCoefficientFiber, standard axioms only、`9f518c2dbb155aaf4af55d52b841e0b7ba99b1f779e5ae7a888dd8fb73e71a72` |
| `ConstantLimit.lean` | `research/lean/check_research_modules.sh --focused ResearchLean/AG/AtlasCoefficientFiber/ConstantLimit.lean` | exit 0、error/warning 0、print 16宣言、axiom audit: 16 declarations under AAT.AG.AtlasCoefficientFiber, standard axioms only、`ec12bae48be6f2eb019906149150b3ae69fb66ca0e7c49a0f22d94d2d9b15871` |
| `Carrier.lean` | `research/lean/check_research_modules.sh --focused ResearchLean/AG/AtlasCoefficientFiber/Carrier.lean` | exit 0、error/warning 0、print 13宣言、axiom audit: 14 declarations under AAT.AG.AtlasCoefficientFiber, standard axioms only、`de109e9074d902cf60f592a35cd236d85dd3cdfb37341f3d7ffebc1078a39c4b` |

全print出力は`propext`、`Classical.choice`、`Quot.sound`の部分集合だった。
placeholder・hidden/BiDi・privacy・追加語彙・import方向と`git diff --check`を確認した。
Research全体build、aggregate rootのelaboration、Formalフルbuild、CI、独立査読、
B–E・Wの検証は未実施。G-135全目標の完了候補ではない。

## Cycle 1 受理記録

PR #5292の固定head `7edbf4b1815c8b29648bc9d43f8811deb935c750` を、
標準4 lane査読・非中心findingの有資格な直接対応・root acceptance・全8 CI checksの後に
merge `010e321a4472d2fa6cc376b339575e73898e25c6` で受理した。
[標準監査](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5292#issuecomment-6041154269)、
[最終確認・acceptance](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5292#issuecomment-6041179525)、
[Issue同期](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5290#issuecomment-6041218043)。
受理はproof-checkpointであり、A・全GOALの終了条件達成ではない。Formal実Build/Kernel/Premise
stepはskip、本体full buildの証拠にしない。上の検証記録は最初の提案時点の履歴である。

## Cycle 2 selection

```yaml
ledger_type: target_cycle_result
goal: G-135-aat-atlas-coefficient-fiber
cycle: 2
goal_blob_sha: cd5f3e684b7f390558796797874a1f16b52a6b18
base_oid: 010e321a4472d2fa6cc376b339575e73898e25c6
tracking_issue: 5290
report_path: research/reports/G-135-aat-atlas-coefficient-fiber.md
selection:
  proof_state_ref: Cycle 1受理記録とIssue同期
  proof_dag_predecessors: [PR5292 Incidence, PR5292 Carrier, PR5292 ConstantLimit, G-134 SubsetComparison]
  milestone: GOAL A・設計README§1–3の原始Mから順像係数と実比較の因子化
  proof_obligations: [実carrierの面射と三関係の放電, 局所fiberと関係グラフの生成, comma成分の全単射と自然性, 実Pと二射, 全三次数の実u因子化]
  exit_criteria: [MだけからInc関手を生成, Φ・Γ・Λへの対応を全射・単射・incidence自然性まで証明, Pの微分とd1d0を構成, η・εをcochain Homとして構成, εηと既存uの全三次数等号]
  selection_reason: 未放電の実M producerを先に閉じ、受理済みの一般Kan APIを固定入力へ接続する
  expected_result_type: proof-obligation-discharged
  lean_targets: [CarrierFunctor.lean, LocalFiber.lean, PushforwardComplex.lean]
  risks: [退化の全パターンと出現の保持, 関係fieldへ結論を移さない, 一般Kanを実Pの代替にしない]
  unchecked: [実carrier以降の全構成, A残部のL, B–EとW]
```

## Cycle 2 宣言・前提・proof DAG

受理spineは `Carrier.incidenceData` → `Carrier.functor` → `Carrier.preimageFunctor` →
`pushforwardCoefficients` / `pushforwardIsRightKanExtension` → `pushforwardComplex` → `unitHom`。
以下の計算・有限性・普遍性のbridgeはこの生成経路の根拠である。固定Aの残義務は消さない。

| module | 宣言・bridge | 固定要求への対応 |
| --- | --- | --- |
| `CarrierFunctor` | `incidencePositionComp`, `incHomCode_comp`, `incHomCode_eqToHom`, `incHomCode_eqToHom_comp` | 出現コードで全合成を計算。合成不可能なコード対の値は実incidence合成の証拠に使わない |
| 同上・Carrier namespace | `endpointHom_of_some`, `endpointHom_of_none`, `endpointHom_code_some`, `endpointHom_code_none` | 既存端点射の公開計算式。Carrier.endpointHomの実装を明示した等号輸送の合成へ整理した |
| 同上 | `edge_of_face_some`, `mappedFaceEdgeHom`, `mappedFaceEdgeHom_code`, `endpoint_face_some_code` | mapped面の三つの辺出現を保持した面射 |
| 同上 | `face_none_edge0_some`, `face_none_edge0_none`, `vertical_edge_eq_face`, `verticalFaceEdgeHom`, `mixedLeftFaceEdgeHom`, `mixedRightFaceEdgeHom`, 各`*_code` | 原始退化三分類から面射を計算。二つのmixed型を端点/恒等射へ送る |
| 同上 | `edgeHom`, `faceVertexHomPosition`, `endpoint_edgeHom_code`, `incidenceData` | 全六経路の位置が同じ原始頂点に依存することから、三関係を生成して放電 |
| 同上 | `functor`, `functor_obj_chart`, `functor_obj_edge`, `functor_obj_face`, `functor_map_chartEdge`, `functor_map_edgeFace`, `preimageFunctor` | 全射のmap_compを持つ実carrier。T0のAf=π⁻¹Aではhsを追加入力にしない |
| `PushforwardCoefficient` | `structuredArrowFinite`, `commaConnectedComponentsFinite`, `coefficientPushforwardFiniteDimensional` | fine対象とcoarse各Homの有限性→実comma/成分の有限性→極限同型の単射から有限次元性 |
| 同上 | `pushforwardCoefficients`, `pushforwardCounit`, `pushforwardIsRightKanExtension`, `pushforwardCoefficientFiniteDimensional` | 実carrierのpointwise右Kanと標準普遍性、実各セル係数の有限次元性 |
| `PushforwardComplex` | `CoefficientC0/1/2`, `coefficientD0`, `coefficientD1`, `coefficient_chart_transport`, `endpoint_edge_normal`, `coefficient_endpoint_edge_eval`, `coefficient_d1_comp_d0` | 粗セル上の係数直積と端点差/三辺和。原始三角形とfunctor則からd1d0=0 |
| 同上 | `coefficientComplex`, `coefficientComplex_d0`, `coefficientComplex_d1`, `coefficientComplex_d0_apply`, `coefficientComplex_d1_apply`, `pushforwardComplex`, `pushforwardComplex_d0_apply`, `pushforwardComplex_d1_apply` | 一般係数APIを実右Kanへ適用してPを独立生成。Lや商dualを定義入力にしない |
| `PushforwardUnit` | `coefficientConstant`, `coefficientConstant_eval`, `coefficientConstant_naturality` | comma全成分上の定数関数を極限同型の逆で作り、前合成評価から自然性を証明 |
| 同上 | `unit0/1/2`, `unit0_apply`, `unit1_apply`, `unit2_apply`, `unit_comm0`, `unit_comm1`, `unitHom` | ηの全三次数を生成し両微分との可換性を証明。実uから逆算していない |

| material premise | 分類・provenance / proof-use | Cycle 2の状態 |
| --- | --- | --- |
| 元のN・M・支持/端点/原始三角形/退化零和 | ambient-boundary、固定T0/G-134。退化分類→面射、端点輸送→生成射、三角形→位置の合成関係に使用 | 同じ原始入力を保持 |
| Ac/Af/hs | 一般carrier APIのdirection-hypothesis | preimageFunctorの実適用でhsはmembershipから生成 |
| 三関係を持つIncidenceFunctorData | 一般APIのdirection-hypothesis、実Mではdischarge-required | incidenceDataが3fieldを原始Mから生成、functor.map_compに使用 |
| J/K/φと対象/各Hom有限性 | 一般有限Kan APIのdirection-hypothesis | 実φ=preimageFunctor、J=Inc(Nf)、Hom有限性はPR5292のincFinite/incHomFiniteから供給 |
| 一般係数Gと各G(σ)の有限次元性 | 一般coefficientComplex APIのdirection-hypothesis | 実G=pushforwardCoefficientsに固定。有限次元性はcomma極限同型から生成し複体fieldへ供給 |
| Pのd1d0とηの微分適合 | discharge-required | functorのmap_compと原始頂点関係、定数係数の前合成自然性から構成 |
| Φ・Γ・Λとの成分の全射/単射/incidence自然性 | discharge-required | 未実装 |
| ε・実u等号・L/商dual/短完全列 | discharge-required | 未実装 |
| κ・R・τ・低次数filtration、保存、Law/台制限、有限判定、W | discharge-required | 未実装 |

依存: PR5292の有限Inc/一般Kan/Carrier対象 → 今回の面射と三関係 → 実φ →
pointwise右Kan → 有限係数 → Pのセル微分 → η。極限はPR5292の任意coneからの生成、
carrier certificateは今回の`incidenceData`から生成する。H¹単射、exactness、rank、
κ/τの消滅を新規入力fieldへ移していない。PR5292は上記の受理refと現sourceのstatement/適用引数から再利用する。

## Cycle 2 result proposal

```yaml
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta:
    - 原始Mから全四パターンの面射と三関係を生成し、実carrierの前提を放電
    - 実carrierの右Kanと有限次元性を生成し、同じ係数射のセル微分でPを構成
    - comma成分上の定数写像からηを構成し、両微分との適合を証明
  exit_criteria_status:
    - Mだけからの実Inc関手、Pの微分とd1d0、η cochain Homは構成済み
    - Φ・Γ・Λの全単射とincidence自然性は未実装
    - ε cochain Homと実uとの全三次数等号は未実装
  split_reason: 原始Mから実carrier・標準右Kan・P・ηまでの生成経路が独立に再利用できる一般構成として閉じた。局所fiber同定と評価写像を追加する前に、この実M producerと係数/微分の生成を一体として監査する。元のA終了条件を保持し、残部を次cycleへ引き継ぐ。
  completion_candidate: no
  lean_artifacts: [Carrier.lean, CarrierFunctor.lean, PushforwardCoefficient.lean, PushforwardComplex.lean, PushforwardUnit.lean]
  evidence: [Cycle 2宣言対応表と対象focused check]
  claim_mapping:
    theorem_names: [Cycle 2受理spineと全bridge]
    source_labels: [GOAL A, 設計README§1–3]
    conjuncts: [実carrierと三関係, 実右Kanの普遍性と有限次元性, 独立したPと微分, 独立したηとcochain性]
    undischarged_assumptions: [Φ・Γ・Λ成分同定, εと実u, A残部とB–E/W]
    acceptance_point: 独立査読前のproof-checkpoint提案。全GOALの完了ではない。
    port_status: unported

audits:
  premise_delta:
    discharged: [実carrierの三関係, 実Kanへの適用, 実係数の有限次元性, Pのd1d0, ηの両微分適合]
    remaining: [Φ・Γ・Λ, εと実u, LとB–E/W]
  certificate_provenance:
    discharged: [incidenceDataはMの原始三分類と位置計算から生成, Kanはpointwise標準構成, Pはセル微分から生成, ηはcomma定数関数から生成]
    unresolved: [局所fiberから実評価と短完全列へ至る経路]
  proof_use:
    used: [原始端点と三角形, 退化零和, 支持輸送, 有限IncとHom, 標準Kan/極限, functor map_comp, 前合成による係数自然性]
    unused: []
  structure_field_escape: none-found
  route_integrity: cannot-determine
  target_fitting: none-found
  vacuity: cannot-determine
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [対象5fileのfocused checkと全宣言公理監査]
  blocking_findings: [独立査読前]
  next_obligation: Φ・Γ・Λとのcomma成分同定と自然性、同じ実Pからεと実uの全三次数等号
```

`route_integrity`/`vacuity`の未確認はA全体の実fiber/評価/商dual/witnessまでの経路に対するもの。
今回の実M→P/ηの生成を残部の代替にせず、全GOALの完了候補とはしない。
GOAL・恒久設計は不変、Formal移植は未着手、Research→Formalの参照方向を保持する。

## Cycle 2 検証記録

対象5fileの `check_research_modules.sh --focused` はすべてexit 0、error/warning 0。
変更対象81明示宣言と85全module宣言の依存は標準3公理の部分集合。

| file | focused target | print / 全宣言監査 | stdout+stderr SHA-256 |
| --- | --- | --- | --- |
| `Carrier.lean` | `ResearchLean/AG/AtlasCoefficientFiber/Carrier.lean` | 13 / 14 standard axioms only | `de109e9074d902cf60f592a35cd236d85dd3cdfb37341f3d7ffebc1078a39c4b` |
| `CarrierFunctor.lean` | `ResearchLean/AG/AtlasCoefficientFiber/CarrierFunctor.lean` | 32 / 35 standard axioms only | `67652a757e2538ecf968b211d40504fc0c326eb849bc8ce00560ce7709a8dd68` |
| `PushforwardCoefficient.lean` | `ResearchLean/AG/AtlasCoefficientFiber/PushforwardCoefficient.lean` | 7 / 7 standard axioms only | `bd1d0856f250f6c9662f3c3644615090008f3b7ab43f8a7537f0bb37762e719c` |
| `PushforwardComplex.lean` | `ResearchLean/AG/AtlasCoefficientFiber/PushforwardComplex.lean` | 17 / 17 standard axioms only | `a6cc72b1fa05ba149f85b0932f2e8ee0b2925f14970b4a3a9ca1da221faae440` |
| `PushforwardUnit.lean` | `ResearchLean/AG/AtlasCoefficientFiber/PushforwardUnit.lean` | 12 / 12 standard axioms only | `5de166de31d26c3f6489c3cc85d6adc7f21da7c7966091f2e78d1dd82d09d000` |

必要なimport cacheを作る単一targetの `lake env lean -o ... <file>` も専用worktreeで実行した。
sourceには68新規明示宣言それぞれのprintと各file末尾の全宣言監査を置いた。
placeholder、hidden/BiDi、privacy、4新規moduleの登録と全print対応、Formal→Research import方向、
`git diff --check`を確認した。GOAL/設計を変更せず、元mainの作業ツリーはcleanのまま。
Research full/aggregate/全file loop、Formal full build/移植、独立査読、CIはこの提案時点では未実施。

非中心の微分評価API指摘への対応として、定義所有者に一般/実Pの4評価補題を追加し、
unit_comm0/1のproof内部を既存unit*_applyと評価APIによる証明へ変更した。
上表のP/ηの検証件数とhashは、この対応後の対象2file再検証を反映する。

## Cycle 2 受理記録

PR #5293の固定head `f9dc1ceaf5d9ddfc3cc3f7d4be43c3617797284a` を、
初回独立4 lane・非中心API指摘の有資格な直接対応・root acceptance・全8 CI後に
merge `fa6f518d794bd8c1f7b0a09e84bb75aae9774225` で受理した。
[初回監査](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5293#issuecomment-6042523123)、
[直接対応・acceptance](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5293#issuecomment-6042646654)、
[全CI・merge記録](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5293#issuecomment-6042743719)、
[Issue同期](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5290#issuecomment-6042755786)。
受理はproof-checkpoint。元の終了条件は未達のまま保持。Formal実build/kernel/premiseはskip。
Cycle 2のproposal/検証記録は提案時点の履歴であり、受理状態はこの節に対応する。

## Cycle 3 selection

```yaml
ledger_type: target_cycle_result
goal: G-135-aat-atlas-coefficient-fiber
cycle: 3
goal_blob_sha: cd5f3e684b7f390558796797874a1f16b52a6b18
base_oid: fa6f518d794bd8c1f7b0a09e84bb75aae9774225
tracking_issue: 5290
report_path: research/reports/G-135-aat-atlas-coefficient-fiber.md
selection:
  proof_state_ref: Cycle 2受理記録とIssue同期
  proof_dag_predecessors: [PR5292 Incidence/ConstantLimit/Carrier, PR5293 実carrier/右Kan/P/η, G-134 SubsetComparison/SupportedChain]
  milestone: GOAL A・設計README§1–3の原始Mから順像係数と実比較の因子化
  proof_obligations: [局所fiberと関係グラフの生成, comma成分の全単射とincidence自然性, counitから実εを生成, 退化辺/面での零性とcochain条件, 全三次数の実u因子化]
  exit_criteria: [MだけからInc関手を生成, Φ・Γ・Λへの対応を全射・単射・incidence自然性まで証明, Pの微分とd1d0を構成, η・εをcochain Homとして構成, εηと既存uの全三次数等号]
  selection_reason: 受理済みの実Pから評価射を生成し、固定比較の因子化と局所セル成分へ直接接続する
  expected_result_type: proof-obligation-discharged
  lean_targets: [CoefficientEvaluation.lean, PushforwardEvaluation.lean, LocalFiber.lean]
  risks: [評価をuから逆算しない, mixed面の二mapped辺の適合をfieldへ移さない, ΦとLaw値fiberを混同しない, comma全単射とincidence自然性を省略しない]
  unchecked: [局所fiberと実評価, A残部のL/商dual, B–E/W]
```


## Cycle 3 固定条項と証拠対応

Cycle 3 selectionは実装前の記録である。下記は査読へ渡す実装の対応であり、
独立査読前のproposalとして扱う。GOAL Aの設計§4、B–E・Wは次の義務に残る。

| 固定条項 | 同じ入力・対象・写像へのLean接続 |
| --- | --- |
| A・README§1のΦ | `PhiChart/Edge/Face`は原始Option条件で選択。`phiBoundary1/2`、`phiComplex`、`phiEmbed0/1/2`、`phiEmbed_comm1/2`、包含単射により原支持chainの部分chainへ接続 |
| A・README§1のΓ | `GammaVertex/Edge`、`gammaSource/Target`、`GammaGraph`とQuiver、有限Hom、`gammaGraphArrow`は元のmapped辺・mixed面名を保持。`gammaBoundary_single`は同じ二端点の符号列 |
| A・README§1–2のΛ | `LambdaFace`、`lambdaCommaEquiv`、`faceComma_obj_eq_of_hom`、`lambdaComponentsEquiv`が原始面持ち上げと面commaの対象・成分を同定 |
| A・README§2のΦ成分式 | `phiComma_reachable`と`phiComma_common_target`を原始三退化パターンから生成し、`phiComponentsEquiv`と`phiCoefficientEquiv`へ接続 |
| A・README§2のΓ成分式 | `gammaComma_reachable`と`gammaComma_common_target`を同じ原始Mから生成し、`gammaComponentsEquiv`と`gammaCoefficientEquiv`へ接続 |
| A・README§2のincidence | `endpointComponents_vertex`、`faceEdgeComponents_lift`が原始細端点・面辺出現を返す。`coefficient_endpoint_naturality`、`coefficient_faceEdge_naturality`が同じ標準Kan写像を関数制限へ同定。`gamma_endpoint_relation`と`endpoint_faceEdge_components`がmixed関係と三角形の二経路を保持 |
| A・README§3のε | `coefficientEvaluationAt`は同じKan counitから生成。`evaluation_comm0/1`はmapped・垂直・mixed全パターンを放電し、`evaluationHom`へ接続 |
| A・README§3のη・ε・実u | `evaluation_unitHom`と`aSubnerveComparisonHom_factorization`は全三次数の同じcochain Homの等号。`unit0_phi`、`unit1_gamma`、`unit2_lambda`は局所成分上の定数式 |
| A・README§3の評価式と単射 | `evaluation0_phi`、`evaluation1_gamma`、`evaluation2_lambda`は同じ原始成分での評価。全Φ・Γ成分のchart/mapped辺代表元とΛ全持ち上げから`evaluation0/1/2_injective`を導く |

### Material premise・provenance・proof-use

| 行 | 分類 | 出所・実際の使用・放電 |
| --- | --- | --- |
| reading順序、有限N、K1、台輸送、原始M | ambient-boundary | T0の既存型。局所セル選択、全射分類、端点・面輸送、各有限性へ使用。全構成は任意A、細選択はπ⁻¹A |
| raw Option退化零和 | ambient-boundary | `degenerate_face_cases`の三分類を通じ、Φ・Γ carrier、Φ到達・common target、ε退化面零性へ使用 |
| 一般constant carrier包含の所属等号 | direction-hypothesis、実適用ではdischarge-required | `phiCellObj_carrier`、`gammaCellObj_carrier`、`lambdaFace_carrier`が原始所属から生成 |
| 一般component同値の到達・共通原像zigzag | direction-hypothesis、実適用ではdischarge-required | `ConnectedFiber`は一般API。実Φ・Γではそれぞれの`*_reachable`と`*_common_target`が任意comma対象・任意共通原像を尽くす |
| counit自然性に渡すfull carrier射等号 | direction-hypothesis、実適用ではdischarge-required | `CarrierFunctor`のmapped端点・mapped面・mixed左右面producerを`evaluation_comm0/1`で使用。対象写像だけの等号に置き換えない |
| 成分代表元の存在 | discharge-required | `phiComponent_chart_representative`と`gammaComponent_vertex_representative`は原始頂点incidenceから生成。ε単射性で使用 |
| 原始Φ・Γ・Λとcommaの同型・自然性 | discharge-required | 上の全単射・評価・incidence定理が出力として証明。入力fieldやexpected rank certificateへ移していない |
| L/商双対、κ/R/τ、標準完全列・filtration、C–Eと全W | discharge-required | 次の義務として未達。今回の二射・局所成分式から接続する |

同値の逆向きに使うchoiceは、原始Mから証明した到達全称命題の証人を選ぶ。
Pは既存の独立生成済み右Kanであり、εη=uという結論から選んでいない。
Φはセル逆像、Law値fiberはAの選択添字として区別し、mapped粗loopはΦ辺へ入れない。
Γのloop・平行面・二mapped辺の重複出現を保持する。

### 依存DAGと受理spine宣言リスト

- PR5292のIncidence/ConstantLimitとPR5293の実carrier/右Kan/P/η → counit評価 → 実ε → 実u全三次数因子化。
- 原始M → Φ部分chain・Γ多重グラフ・Λ → 原始包含 → 到達/common target → 実comma成分全単射 → 同じKanのstalk式。
- stalk式と原始incidence射 → endpoint/faceEdge成分写像 → Kan自然性、mixed関係・三角形関係 → η/ε局所評価 → ε次数別単射。
- G-134の`SubsetComparison`・`SupportedChain`の支持輸送と原始chainを再利用し、G-133の`GeneratedComposition`のcochain合成・extensionalityへ同じ二射を接続。

旧6ファイルで追加した定義所有者APIと新9ファイルの明示宣言を以下に固定する。
以下259宣言を今回の受理spine・その支持APIとする。名前空間は
`AAT.AG.AtlasCoefficientFiber`（CarrierのAPIは同名内部namespace）。
cycle scaffoldは成果sourceに含めず、未使用の試作とdiagnostic scratchは検証用作業領域だけに置いた。

| ファイル | 今回追加した明示宣言 |
| --- | --- |
| `Carrier.lean` | `Carrier.edge_eq_edge_iff`, `Carrier.face_eq_face_iff` |
| `CarrierFunctor.lean` | `Carrier.preimageFunctor_obj_chart`, `Carrier.preimageFunctor_obj_edge`, `Carrier.preimageFunctor_obj_face`, `Carrier.preimageFunctor_map_chartEdge`, `Carrier.preimageFunctor_map_edgeFace`, `Carrier.preimageFunctor_obj_edge_of_some`, `Carrier.preimageFunctor_obj_edge_of_none`, `Carrier.preimageFunctor_obj_face_of_some`, `Carrier.preimageFunctor_endpoint_of_some`, `Carrier.preimageFunctor_endpoint_of_none`, `Carrier.preimageFunctor_face_edgeMap_of_some`, `Carrier.preimageFunctor_face_edge_of_some`, `Carrier.preimageFunctor_face_edgeHom_of_some`, `Carrier.edgeHom_code_of_mixed_left`, `Carrier.edgeHom_code_of_mixed_right`, `Carrier.preimageFunctor_face_edgeHom_of_mixed_left`, `Carrier.preimageFunctor_face_edgeHom_of_mixed_right`, `incHomCode_comp_eqToHom`, `Carrier.preimageFunctor_map_edgeFace_code_of_some`, `Carrier.preimageFunctor_map_chartFace`, `Carrier.preimageFunctor_map_chartFace_code`, `Carrier.preimageFunctor_map_chartFace_code_of_some`, `Carrier.preimageFunctor_face_vertex_of_some`, `Carrier.preimageFunctor_face_vertexHom_of_some`, `Carrier.preimageFunctor_edge_endpoint_of_some`, `Carrier.preimageFunctor_map_chartEdge_code_of_some`, `Carrier.preimageFunctor_map_edgeFace_code_of_mixed_left`, `Carrier.preimageFunctor_map_edgeFace_code_of_mixed_right`, `Carrier.preimageFunctor_map_chartFace_code_of_mixed_left`, `Carrier.preimageFunctor_map_chartFace_code_of_mixed_right` |
| `ConstantLimit.lean` | `constantRational_map`, `coefficientCounit_eval`, `coefficientPushforward_map_component_eval` |
| `Incidence.lean` | `inc_endomorphism_eq_id`, `incHom_target_of_face`, `incHom_from_face_eq`, `incHom_edge_edge_target`, `IncidenceFunctorData.vertexHom_zero`, `IncidenceFunctorData.vertexHom_one`, `IncidenceFunctorData.vertexHom_two`, `incHom_chartFace_source_of_code`, `incHom_chartEdge_source_of_code`, `incHom_chart_chart_target`, `chartEdge_edgeFace_comp` |
| `PushforwardComplex.lean` | `coefficient_endpoint_chart_eval`, `coefficient_edge_transport` |
| `PushforwardUnit.lean` | `unitHom_f0`, `unitHom_f1`, `unitHom_f2` |
| `CoefficientEvaluation.lean` | `coefficientEvaluation`, `coefficientEvaluation_apply`, `coefficientEvaluation_naturality`, `coefficientEvaluation_constant`, `coefficientEvaluationAt`, `coefficientEvaluationAt_naturality`, `coefficientEvaluationAt_constant`, `coefficientEvaluationAt_cellIso` |
| `ConnectedFiber.lean` | `componentEquivOfCommonTargets`, `componentEquivOfCommonTargets_apply`, `componentEquivOfCommonTargets_symm_mk` |
| `FiberComma.lean` | `constantCarrier_transport`, `constantCarrierCommaFunctor`, `phiCommaFunctor`, `gammaCommaFunctor`, `lambdaCommaObj`, `lambdaCommaObj_injective`, `lambdaCommaObj_surjective`, `lambdaCommaEquiv`, `faceComma_obj_eq_of_hom`, `lambdaComponentToFace`, `lambdaComponentsEquiv`, `lambdaCoefficientEquiv`, `lambdaCoefficientEquiv_apply`, `constantCarrierCommaFullyFaithful`, `gammaCommaFunctor_obj_right`, `gammaCommaFunctor_obj_hom`, `gammaCommaFullyFaithful`, `constantCarrierCommaBackwardArrow`, `constantCarrierCommaBackwardArrow_right`, `constantCarrierComma_common_target`, `phiCommaFullyFaithful`, `phiCommaFunctor_obj_right`, `phiCommaFunctor_obj_hom`, `lambdaCommaObj_right`, `lambdaCommaObj_hom`, `lambdaComponentsEquiv_symm_apply` |
| `GammaComma.lean` | `gammaCellObj_surjective_of_carrier`, `gammaComma_arrow_of_same_cell`, `gammaComma_reachable_of_strict`, `gammaComma_reachable_of_mapped_face`, `gammaComma_reachable_of_edge_carrier`, `gammaComma_reachable`, `mapConnectedComponents_surjective_of_reachable`, `gammaComma_components_surjective`, `gammaComma_common_target_of_strict`, `gammaComma_source_of_mapped_face`, `gammaComma_common_target_of_mapped_face`, `gammaComma_common_target_of_edge_carrier`, `gammaComma_common_target`, `gammaComponentsEquiv`, `gammaCoefficientEquiv`, `gammaCoefficientEquiv_apply`, `gammaComponentsEquiv_apply` |
| `LocalEvaluation.lean` | `evaluation0_phi`, `evaluation1_gamma`, `evaluation2_lambda`, `unit0_phi`, `unit1_gamma`, `unit2_lambda`, `evaluation0_injective`, `evaluation1_injective`, `evaluation2_injective` |
| `LocalFiber.lean` | `PhiChart`, `PhiEdge`, `PhiFace`, `GammaVertex`, `GammaEdge`, `LambdaFace`, `phiEndpoint`, `phiEndpoint_val`, `phiFace_edge_chart`, `phiFace_edge_none`, `phiFaceEdge`, `phiFaceEdge_val`, `gammaSource`, `gammaTarget`, `gammaBoundary`, `gammaBoundary_single`, `phiD0`, `phiD1`, `phiD0_apply`, `phiD1_apply`, `phiD1_comp_phiD0`, `phiComplex`, `phiCellObj`, `PhiInc`, `phiCellObj_carrier`, `gammaCellObj`, `GammaInc`, `gammaCellObj_carrier`, `lambdaFace_carrier`, `phiBoundary1`, `phiBoundary2`, `phiBoundary1_single`, `phiBoundary2_single`, `phiBoundary1_dual`, `phiBoundary2_dual`, `phiBoundary1_comp_phiBoundary2`, `phiEmbed0`, `phiEmbed1`, `phiEmbed2`, `phiEmbed_comm1`, `phiEmbed_comm2`, `phiEmbed0_injective`, `phiEmbed1_injective`, `phiEmbed2_injective`, `gammaCellObj_inl`, `gammaCellObj_inr`, `gammaCellObj_injective`, `phiCellObj_chart`, `phiCellObj_edge`, `phiCellObj_face`, `phiCellObj_injective`, `phiIncFinite`, `gammaIncFinite`, `lambdaFaceFinite`, `gammaSource_val`, `gammaTarget_val_of_left`, `gammaTarget_val_of_right`, `GammaGraph`, `gammaGraphQuiver`, `gammaGraphFinite`, `gammaGraphHomFinite`, `gammaGraphArrow`, `gammaGraphArrow_val` |
| `LocalNaturality.lean` | `endpointComponents`, `faceEdgeComponents`, `coefficient_endpoint_naturality`, `coefficient_faceEdge_naturality`, `gammaEndpointChart`, `gammaEndpointChart_val`, `gammaEndpointCommaArrow`, `endpointComponents_vertex`, `lambdaEdgeVertex`, `lambdaEdgeVertex_val`, `lambdaEdgeCommaArrow`, `faceEdgeComponents_lift`, `gammaSourceIncidence`, `gammaTargetIncidence`, `gamma_relation_component`, `gammaComponent_vertex_representative`, `gamma_endpoint_relation`, `endpointComponentsAt`, `faceVertexComponents`, `endpoint_faceEdge_components`, `phiEndpointIncidence`, `phiFaceChart`, `phiFaceChartIncidence`, `phiComponent_chart_representative` |
| `PhiComma.lean` | `phiCellObj_surjective_of_carrier`, `phiMappedEndpoint`, `phiMappedEndpoint_val`, `phiMappedVertex`, `phiMappedVertex_val`, `phiMixedLeftCollapsed`, `phiMixedRightCollapsed`, `phiComma_common_target_of_strict`, `phiMixedLeftCollapsed_val`, `phiMixedRightCollapsed_val`, `phiComma_reachable_of_mapped_edge`, `phiComma_reachable_of_mapped_face`, `phiComma_arrow_of_same_cell`, `phiComma_reachable_of_strict`, `phiComma_reachable_of_mixed_left`, `phiComma_reachable_of_mixed_right`, `phiComma_reachable_of_chart_carrier`, `phiComma_reachable`, `phiComma_source_of_mapped_edge`, `phiComma_source_of_mapped_face`, `phiComma_common_target_of_mapped_edge`, `phiComma_common_target_of_mapped_face`, `phiMixedLeftAnchor`, `phiComma_arrow_to_mixed_left_anchor`, `phiMixedRightAnchor`, `phiComma_arrow_to_mixed_right_anchor`, `phiComma_common_target_of_mixed_left`, `phiComma_common_target_of_mixed_right`, `phiComma_common_target_of_chart_carrier`, `phiComma_common_target`, `phiComponentsEquiv`, `phiComponentsEquiv_apply`, `phiCoefficientEquiv`, `phiCoefficientEquiv_apply` |
| `PushforwardEvaluation.lean` | `evaluation0`, `evaluation1`, `evaluation2`, `evaluation0_apply`, `evaluation1_of_none`, `evaluation1_of_some`, `evaluation2_of_none`, `evaluation2_of_some`, `evaluation0_unit`, `evaluation1_unit`, `evaluation2_unit`, `evaluation_endpoint_of_some`, `evaluation_endpoint_of_none`, `evaluation_comm0`, `evaluation_face_edge_of_some`, `evaluation_face_edge_of_mixed_left`, `evaluation_face_edge_of_mixed_right`, `evaluation_comm1`, `evaluationHom`, `evaluationHom_f0`, `evaluationHom_f1`, `evaluationHom_f2`, `evaluation_unitHom`, `aSubnerveComparisonHom_factorization` |

## Cycle 3 result proposal

```yaml
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta:
    - 実Kan counitからεを生成し、退化全パターンでcochain条件を放電した
    - 既存uとεηを全三次数・同じcochain Homとして同定した
    - 原始Φ部分chain、Γ有限有向多重グラフ、Λを構成し実comma成分全単射へ接続した
    - 実Kan incidenceを指定細端点・辺成分での制限へ同定しmixedと三角形の関係を保持した
    - 全成分の原始代表元からεの次数別単射性を証明した
  exit_criteria_status:
    - MからのInc関手、Pの微分とd1d0、ηはPR5293の同じ宣言を再利用
    - ΦΓΛの実comma成分全単射と全incidence自然性は本cycleのproducer・同値・自然性定理へ対応
    - ηεは同じcochain Hom、εη=uはaSubnerveComparisonHom_factorizationへ対応
  split_reason: none
  completion_candidate: no
  lean_artifacts: [本reportの15ファイル・259追加宣言]
  evidence: [固定条項表、spine宣言表、対象fileの検証記録]
  claim_mapping:
    theorem_names: [本reportのspine宣言表]
    source_labels: [GOAL A, 設計README§1–3]
    conjuncts: [原始局所fiber, 実comma成分式, incidence自然性, 実εと同じ二射・u因子化]
    undischarged_assumptions: [A設計§4のLと商双対, B–E, 全W]
    acceptance_point: 選定到達点の全終了条件をLean構成へ対応した独立査読前のproposal
    port_status: unported

audits:
  premise_delta:
    discharged: [原始局所fiber所属, 原始comma到達と共通原像連結性, 成分全単射とincidence自然性, 実εとu等号, 次数別評価単射]
    remaining: [Lと商双対, κRτと標準完全列・filtration, 保存条件・錐, Law台制限・G134, 有限判定・全W]
  certificate_provenance:
    discharged: [Kan counit由来のε, 原始M由来のΦΓΛ, 原始全称producer由来のcomponent同値]
    unresolved: []
  proof_use:
    used: [原始Mと台輸送, Option退化零和, 原始端点・面出現, 標準Kan極限とcounit, G133 cochain合成, G134 chainと三角形]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [下記focused checkと全宣言公理監査・機械scan]
  blocking_findings: [標準PR独立査読とroot acceptanceとCIが未実施]
  next_obligation: 原始退化セルL、実Pとの商双対同型と標準短完全列
```

全体は`target-proof-checkpoint`。A設計§4、B–E、Wと最終4 lane完了監査が残る。
今回の到達点の受理後も、同じ固定targetへのループを続ける。
GOAL・恒久設計・Formalは変更していない。Researchの形式化であり、Formal移植は未実施。

## Cycle 3 検証記録

変更した非aggregateの15ファイルについて、それぞれ
`bash research/lean/check_research_modules.sh --focused ResearchLean/AG/AtlasCoefficientFiber/<file>`
を実行した。全件exit 0、error/warning 0。376明示宣言の`#print axioms`と、
各current module合計459宣言の標準公理監査を確認した。全依存は
`propext`、`Classical.choice`、`Quot.sound`の部分集合である。

| ファイル | 明示print / module監査 | 出力SHA-256 | source SHA-256 |
| --- | --- | --- | --- |
| `Carrier.lean` | 15 / 16 | `fd215c4cf298c6c78b4ab98c49f31e81f04f93db65ac15f9b5da0d8cad0e1d1c` | `d4bec60fcf7376f75ed7f63566ff4c01c3dad0ae2ef72e34d810c4804b2ae481` |
| `CarrierFunctor.lean` | 62 / 65 | `ba012131180c9d5f5dc809381af7ec8fc669330d0f85ca912c75973163f75df7` | `63cdb0ad4d179b63b7d76a9106fed478b20f719b64632fc58324ea787b0c376b` |
| `ConstantLimit.lean` | 19 / 19 | `4359f830e8bb207e2ac5ce02f1602c2404c7494a87458e8f9c0dbade405914c1` | `06fe20ab5798c210b8d7f2a7d0c359618aa1cdaec99ca6b167078fb686cb087e` |
| `Incidence.lean` | 38 / 116 | `234b89ccd13f66e56e6ffd9485254785669b9cc57b0932814723ded31199a28d` | `53ff46f6f4c4c5a9ad41d9ca49b0a8fc490f0ff99b5566cea6e477344b8fd6e5` |
| `PushforwardComplex.lean` | 19 / 19 | `669087bddd6656a5179162de2ec35a84936ecd2d0411a9f223fd4201d557d668` | `dba4006e68c979c9f65c04dadda104609d1e0004f4527c5d069639ec6ebbbc3d` |
| `PushforwardUnit.lean` | 15 / 15 | `e66d354433da41deb6822610c59b086d8204e379fb0820c72052d76a7fc8ba49` | `0a22341ed23f620e81fd05c517f6176d4910bb7e64a379cabd87f7694c12c53d` |
| `CoefficientEvaluation.lean` | 8 / 8 | `00e4c37ed8cb94a73825bdf2502bd0cc9b7c39e8cb4ef6d23b10dc24db5da9fb` | `3579e2791e008c13092ff21610e8f9bf323067d2714615d297278535a0bb25d9` |
| `ConnectedFiber.lean` | 3 / 3 | `7ae96ef9e041de5a9685c1f846766ca2d4306ffffe9d36d2bcd60dfc21c5166b` | `2fa188dd2b01bc10c04b054f8efbe57d518ef973e6eb60239943f5fc1e201d20` |
| `FiberComma.lean` | 26 / 26 | `54b2664ea36d80e8efc5289200b2641e25fd8d9e2faa989a3be59b5d89227a35` | `1c9fc78ae72becc29e68194651d4ab79d7a3935ca7b8b5b45688a18a3b5b9c28` |
| `GammaComma.lean` | 17 / 17 | `2a1a690e7060927a77c38b0ed5ff4df5fa7ed2ad58fd83d6fbff98940ba78e8c` | `e10ca3baaf4768f6fbdf042321459b6fb4d9fa24e3d9e25afc61032004ca8a13` |
| `LocalEvaluation.lean` | 9 / 9 | `c314007e7bffa2cc33a282ca93f622c34018d67e6aac01b7da98bdb942a007ca` | `26899aceb3add4f510a70bfd60031ab6df2f7920e3fe76e71b7bfeb6a7b470c7` |
| `LocalFiber.lean` | 63 / 63 | `e22ccd1c01e73f68df16017f9b364313c8d8e435142f4ffb081c8b023282ff45` | `8e1e6a00eb6a37ab0466e1a74b170e00a218e49c6eec32acea8128359fbaac21` |
| `LocalNaturality.lean` | 24 / 24 | `fe13ec9e5aed62ba708633a21c3100664ff27c3e731afe8971ed19783f0ff82b` | `1015b5e418fd49a243ef430b1ec87ec114a9e01df209e43befe1fc46f2dfd6b2` |
| `PhiComma.lean` | 34 / 34 | `6fd5825d9b044ce362d44ba9e62388d4bf41158cc944f173a086432693ebf8a4` | `22b3c53a81297a69a1c542d150ec82a911dff011a9e66151827a881c46208b6a` |
| `PushforwardEvaluation.lean` | 24 / 25 | `7b1d97c87be6a67a3d4410a2a930c6bf32552dcb3da6340d76449e646b3526f8` | `4089439605bc1dc43f121a8e1a6bc920dadc97679cf47e27b59faa08106e8ed6` |

必要なローカルimport cacheだけを同じ単一fileの`lake env lean -o <cache> <file>`で作成した。
Research full build、aggregate root、全Research file loopは実行していない。
Formal本体buildはローカル未実施であり、今回のPRではFormalに差分がない。
PRのCI実施範囲は完走後に監査コメント・Issue同期へ記録する。

placeholder、新規公理、hidden/BiDi、privacy/local-path scanは対象変更fileで検出ゼロ。
本体からResearchへのimport方向scanは検出ゼロ。
GOAL・設計・Formalのdiffは空であり、元のmain作業ツリーもcleanであることを確認した。
語彙scanで変更文の禁止語は検出ゼロ。`git diff --check`を最終文書へ実行した。
全W・L以降の検証と最終completion監査は、対応する実装後の義務に残る。

## Cycle 3 受理記録

PR [#5294](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5294)、
final head `dace21ebc3c8a845e0f66ac459103dd91b4e83b7`、
merge `18c21239e8b757cbe7205eb44945a68611a4645f`、2026-10-07T20:19:59Z。
[初回4 lane・数学全文](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5294#issuecomment-6045999657)、
[Lean全文](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5294#issuecomment-6046002686)、
[直接対応・root acceptance](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5294#issuecomment-6046087706)、
[merge記録](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5294#issuecomment-6046113302)、
[Issue同期](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5290#issuecomment-6046110673)。
全4 laneに中心findingなし、同じ非中心report現況ずれだけ。report2行の修正は
新規単一reviewerが全解消・直接対応有資格と確認した。全8CI後にmerge。
Formal実build/kernel/premiseはskip、Research full/aggregateは未実施。
Cycle resultはproof-obligation-discharged、元のA・設計README§1–3の終了条件はすべて放電。
全GOALはtarget-proof-checkpoint。Cycle 3 proposal・検証記録は提案時点の履歴として保持する。

## Cycle 4 selection

```yaml
ledger_type: target_cycle_result
goal: G-135-aat-atlas-coefficient-fiber
cycle: 4
goal_blob_sha: cd5f3e684b7f390558796797874a1f16b52a6b18
base_oid: 18c21239e8b757cbe7205eb44945a68611a4645f
tracking_issue: 5290
report_path: research/reports/G-135-aat-atlas-coefficient-fiber.md
selection:
  proof_state_ref: Cycle 3受理とIssue5290同期6046110673
  proof_dag_predecessors: [PR5294 実P/η/εと原始ΦΓΛ成分式, G-134 支持自由chainと双対, G-133 zeroExtension/端homology]
  milestone: GOAL A・設計README§4の原始退化部分複体と商双対・同じ標準短完全列
  proof_obligations: [Ev/Fv/FmからL生成, 原支持chainの部分複体と比較での零像, 実ε像とLのannihilator同定, 商chain双対と独立Pの同型, Q=L双対と標準短完全列, H0LとH0Q零性]
  exit_criteria: [指定L0/L1/L2と原支持chain包含・微分可換・Mによる零像, 全三次数で実ε像が指定Lをannihilateする全cochainに一致, 独立Pと商chain双対の同じ評価写像による複体同型, 全整数次数の標準短完全列が同じεと制限射で成立, 原始d1L1=L0からH0L=0と標準H0Q=0]
  selection_reason: κ/Rとτの一般混在完全列が依存する実Lと標準短完全列を先に生成し、次数別ε単射をH1へ接続できる経路を固定する
  expected_result_type: proof-obligation-discharged
  lean_targets: [DegenerateCells.lean, DegenerateSubcomplex.lean, EvaluationAnnihilator.lean, DualShortExact.lean]
  risks: [LをΦ直和へ置換しない, Pを商dualから定義し直さない, annihilator逆方向と全整数次数を省略しない, exactnessやH0零性を入力fieldへ移さない]
  unchecked: [L/商dual/標準短完全列/H0零性は未実装, κRτ以降と全W]
```

Cycle 4 selectionは実装前の記録である。固定GOAL・設計・共通基準を変更せず、
同じ任意M・任意Aと細選択π⁻¹Aで全終了条件の放電を進める。

## Cycle 4 implementation result（正式査読前）

元の終了条件をすべて維持し、任意の原始Mと任意Aについて次の証拠を構成した。

| 終了条件 | Lean証拠 |
| --- | --- |
| 指定Lと原支持chainの部分複体、Mの零像 | `degenerateL0/1/2`、`degenerateBoundary1/2`、`degenerateChainInclusion`、`degenerateChainInclusion_mono`、`degenerateChainInclusion_comparison_zero` |
| 実ε像が指定Lのannihilator全体 | `restriction0/1/2_zero_iff`、`evaluation0/1/2_preimage_of_restriction_zero`、`evaluation0/1/2_range_eq_ker` |
| 独立Pと同じ原支持chain商双対の複体同型 | `quotientChainProjection`、`quotientChain_d10/d21`、`evaluationQuotientDual0/1/2_mk`、`evaluationQuotientDualStandardIso` |
| 全ℤ次数の同じεと制限による標準短完全列 | `evaluationRestriction_degreewise_shortExact`、`evaluationRestriction_shortExact` |
| 原始境界の全射性から標準H₀L/H⁰Q零性 | `degenerateBoundary1_surjective`、`degenerateChain_H0_isZero`、`restrictionComplex_d0_injective`、`restrictionComplex_H0_isZero` |

L₁は垂直辺だけでなく混在面の全境界を含む。次数1の逆像は原始L₁閉条件から
Γの二端点一致を導き、その全incidenceで値を降ろし、既存の実Kan係数同型へ戻す。
次数0では垂直辺閉条件から全Φ incidenceへ下降し、次数2ではΛの全持ち上げ値を使う。
商双対同型の各次数は全chain代表元で同じεを評価し、二微分の可換式から
標準複体同型を構成する。商射の包含零性と原MによるLの零像も標準chain射として成立する。

```yaml
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: 原始Ev/Fv/Fmから指定L、原K′への標準包含とMによる零像、実ε像の両包含、同じK′/Lと独立Pの標準双対同型、Q=L双対と全ℤ次数の標準短完全列、標準H0L/H0Q零性を構成
  exit_criteria_status: [五条件すべて入力生成Lean証拠あり・正式PR監査待ち]
  split_reason: none
  completion_candidate: no
  lean_artifacts: [DegenerateCells.lean, DegenerateSubcomplex.lean, PrimitiveDescent.lean, DualRestriction.lean, EvaluationAnnihilator.lean, DegenerateChain.lean, DualShortExact.lean, QuotientDual.lean, QuotientChain.lean]
  claim_mapping:
    source_labels: [GOAL A, 設計README§4]
    conjuncts: [上の終了条件対応表]
    undischarged_assumptions: []
    acceptance_point: 指定Lと独立Pを任意M・任意Aで同じ実評価と標準短完全列へ接続する五条件の放電
    port_status: unported
  target_state: target-proof-checkpoint
audits:
  premise_delta:
    discharged: [原始退化分類からL生成と境界安定性, ΦΓの全incidence下降から実ε像の逆包含, 同じεのcochain条件から商双対同型, 体上のdualRestrict全射性, 原始L境界全射性から標準端homology零性]
    remaining: [κとH1Lのcokernel同定, R=ker κ双対, τの代表元生成と標準連結射, B–Eと全W, 最終完了監査]
  certificate_provenance:
    discharged: [任意Mの原始Option像と既存支持chain微分だけから生成, generic quotientDualEquivOfRestrictionのhi/hz/hsは実ε単射・制限零性・入力生成逆像で各三次数放電, generic moduleShortExact補助の完全性と単射・全射性を実二射から各次数放電]
    unresolved: []
  proof_use:
    used: [原始退化分類, 原支持chainのsquare-zero, 実counit評価と全三次数cochain条件, 原始ΦΓΛから実comma成分への同型, 原始境界全射性, mathlib dualRestrictとdualQuotEquivDualAnnihilator, G-133 zeroExtensionとoldH0Iso]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  blocking_findings: []
  next_obligation: 原始block分解からκ、H1L=cok κ、R、τを生成して一般混在完全列へ接続する
```

### Material premiseと受理spine

- 本文由来: Source、qc/qf、h、Nc/Nf、原始 `IncidenceSupportedComparison M`、任意の台A。
- 放電済み: Lの微分安定性・square-zero・Mの零像は原支持chainから生成。
  実ε像の逆包含はΦ/Γ/Λ下降の上記三producer。商双対同型、短完全列とH₀/H⁰零性は上記終了条件表の宣言を使う。
- generic補助の追加premiseは適用する実三次数ごとに放電した補助APIであり、固定目標の入力へ追加していない。
- 受理spine候補は下の全175明示宣言。すべてResearch側であり、Formalへの移植は未実施。
  GOAL全体の完了候補ではなく、正式PR査読でこの到達点の受理を判定する。

- `DegenerateCells.lean`: `VerticalEdge`, `VerticalFace`, `MixedFace`, `DegenerateFace`, `degenerateFace_vertical`, `mixedFace_patterns`, `degenerateFaceEquiv`, `degenerateFaceEquiv_symm_val`, `verticalFace_edge_none`, `verticalFaceEdge`, `verticalFaceEdge_val`, `cellInclusion`, `cellInclusion_single`, `cellInclusion_injective`, `freeRange_le_iff`, `cellInclusion_range_mono`, `annihilates_freeRange_iff`, `verticalEdgeInclusion`, `verticalFaceInclusion`, `mixedFaceInclusion`, `degenerateFaceInclusion`, `verticalEdgeInclusion_single`, `verticalFaceInclusion_single`, `mixedFaceInclusion_single`, `degenerateFaceInclusion_single`, `verticalBoundary`, `verticalBoundary_single`, `verticalBoundary_inclusion`, `verticalEdgeInclusion_injective`, `verticalFaceInclusion_injective`, `mixedFaceInclusion_injective`, `degenerateFaceInclusion_injective`, `verticalFaceInclusion_range_le_degenerate`, `mixedFaceInclusion_range_le_degenerate`, `degenerateFaceInclusion_range_eq`
- `DegenerateSubcomplex.lean`: `degenerateL0`, `degenerateL1`, `degenerateL2`, `mem_degenerateL0`, `mem_degenerateL1`, `mem_degenerateL2`, `degenerateL2_vertical_mixed`, `verticalEdge_range_le_L1`, `mixedBoundary_range_le_L1`, `degenerateL2_boundary_le`, `degenerateL1_boundary_eq`, `degenerateBoundary1`, `degenerateBoundary2`, `degenerateBoundary1_val`, `degenerateBoundary2_val`, `degenerateBoundary_square`, `degenerateBoundary1_surjective`, `verticalEdgeInclusion_map_zero`, `degenerateFaceInclusion_map_zero`, `degenerateL2_le_ker`, `degenerateL0_le_ker`, `degenerateL1_le_ker`
- `PrimitiveDescent.lean`: `componentFunction`, `componentFunction_mk`, `phiEdgeVertical`, `phiEdgeVertical_val`, `phiFaceVertical`, `phiFaceVertical_val`, `verticalFace_vertex_values`, `phiCellValue`, `phiCellValue_chart`, `phiCellValue_edge`, `phiCellValue_face`, `phiCellValue_invariant`, `phiDescendedValues`, `phiDescendedValues_chart`, `gammaFace_edge_value`, `gammaCellValue`, `gammaCellValue_vertex`, `gammaCellValue_invariant`, `gammaDescendedValues`, `gammaDescendedValues_vertex`
- `DualRestriction.lean`: `restrictionDifferential_square`, `restrictionComplex`, `restrictionComplex_d0_apply`, `restrictionComplex_d1_apply`, `restriction0`, `restriction1`, `restriction2`, `restriction0_apply`, `restriction1_apply`, `restriction2_apply`, `restriction0_surjective`, `restriction1_surjective`, `restriction2_surjective`, `restriction_comm0`, `restriction_comm1`, `restrictionHom`, `restrictionHom_f0`, `restrictionHom_f1`, `restrictionHom_f2`, `restrictionComplex_d0_injective`, `restrictionComplex_d0_ker`, `restrictionComplex_H0_isZero`
- `EvaluationAnnihilator.lean`: `dualRestriction_eq_zero_iff`, `restriction0_zero_iff`, `restriction1_zero_iff`, `restriction2_zero_iff`, `restriction0_evaluation0`, `restriction1_evaluation1`, `restriction2_evaluation2`, `evaluation0_preimage_of_restriction_zero`, `gamma_closed_of_restriction_zero`, `evaluation1_preimage_of_restriction_zero`, `evaluation2_preimage_of_restriction_zero`, `evaluation0_range_eq_ker`, `evaluation1_range_eq_ker`, `evaluation2_range_eq_ker`
- `DegenerateChain.lean`: `chainDegreeDifferential_out`, `degenerateDegreeObject`, `degenerateDegreeObject_out`, `degenerateDegreeDifferential`, `degenerateDegreeDifferential_square`, `degenerateChain`, `degenerateDegreeInclusion`, `degenerateDegreeInclusion_out`, `degenerateDegreeInclusion_comm`, `degenerateChainInclusion`, `degenerateChainInclusion_f`, `degenerateChainInclusion_comparison_zero`, `degenerateChainInclusion_mono`, `degenerateZeroShort`, `degenerateZeroScIso`, `degenerateZeroShort_exact`, `degenerateChain_H0_isZero`
- `DualShortExact.lean`: `degreeMap_out`, `evaluation_restriction_standard_zero`, `evaluationRestrictionShortComplex`, `evaluationRestrictionShortComplex_f`, `evaluationRestrictionShortComplex_g`, `moduleShortExact_of_range_eq_ker`, `evaluationRestriction_degreewise_shortExact`, `evaluationRestriction_shortExact`
- `QuotientDual.lean`: `quotientBoundary1`, `quotientBoundary2`, `quotientBoundary1_mk`, `quotientBoundary2_mk`, `quotientBoundary_square`, `quotientDualDifferential_square`, `quotientDualComplex`, `quotientDualComplex_d0_apply`, `quotientDualComplex_d1_apply`, `quotientDualEquivOfRestriction`, `quotientDualEquivOfRestriction_mk`, `evaluationQuotientDual0`, `evaluationQuotientDual1`, `evaluationQuotientDual2`, `evaluationQuotientDual0_mk`, `evaluationQuotientDual1_mk`, `evaluationQuotientDual2_mk`, `evaluationQuotientDual_comm0`, `evaluationQuotientDual_comm1`, `evaluationQuotientDualHom`, `evaluationQuotientDualHom_f0`, `evaluationQuotientDualHom_f1`, `evaluationQuotientDualHom_f2`, `evaluationQuotientDualHom_standard_isIso`, `evaluationQuotientDualStandardIso`, `evaluationQuotientDualStandardIso_hom`
- `QuotientChain.lean`: `quotientDegreeObject`, `quotientDegreeDifferential`, `quotientDegreeDifferential_square`, `quotientChain`, `quotientChain_d10`, `quotientChain_d21`, `quotientDegreeProjection`, `quotientDegreeProjection_comm`, `quotientChainProjection`, `quotientChainProjection_f`, `degenerateChainInclusion_quotient_zero`

### Cycle 4 validation

各対象fileを個別に `bash research/lean/check_research_modules.sh --focused ResearchLean/AG/AtlasCoefficientFiber/<file>.lean` で確認した。
9対象すべてerror/warning 0、全175明示宣言の `#print axioms` と各moduleのnamespace監査は標準三公理
`propext` / `Classical.choice` / `Quot.sound` のみ。必要なimport cacheは対象単一fileの `lake env lean -o` で生成した。
Research全体・aggregate root・全file loopのelaboration、`lake build`、Formal buildは未実施。

| File | 明示axiom監査 | source SHA-256 | focused log SHA-256 |
| --- | ---: | --- | --- |
| `DegenerateCells.lean` | 35 | `c9cad1af21d5101deed727cc0f2d18184ae665cb10046e4cfd8af679c375c7f3` | `8e3082ad8b81b317e964e27a8d3766393283ad3c8ebf8ca7af9bdc45444daa10` |
| `DegenerateSubcomplex.lean` | 22 | `273dd21044e3c5592cf3899110e304417da73dff65dc62409ac8fce5d3a7d77a` | `1f54cff87f9249cec8e1df08170c6c5de5f32edda0dd37f75e8f6540be5381a1` |
| `PrimitiveDescent.lean` | 20 | `f21bf9484ab106ebfe726f9ca53d8e1073980d5b50de91f9ad57cc5ee2dfa831` | `e67b7a0820cdb9da6539b18ee802a7a7ac21f72d7a51ae4ebafe8c6c214654f3` |
| `DualRestriction.lean` | 22 | `a8ff804a06a4eed304e9a5af50c04934ad7aefe815a9aa8a86b150b9efbd2b12` | `a7cfacee4e1b953ce20b878fe90717804696c776e24e8b6d7b9db47ccf57ded5` |
| `EvaluationAnnihilator.lean` | 14 | `e240cdad380f4a7ecfd3c422183eab5b6197ad7443faf85ad7fec7cc1fea061b` | `f2a0690f6e56d68f45b4b00d9bd90b695bd13c6c80e681ec3dbb69ff82d91e28` |
| `DegenerateChain.lean` | 17 | `72474e1b58b6db1aa8433c3eb6e762d64b64d0a210d55000dd00df6711b298c2` | `98f69b114dbd2c8fe05bb844fecfffce46719712b264e00811389b379f9b661c` |
| `DualShortExact.lean` | 8 | `3df1d54b5218a2badc42bfca66050be08ed024b0b0d23c06997e61166caca64a` | `bb966c79f676b4155a2604b6344b9031eaa81c3a2b8477f369de903bd02fe14f` |
| `QuotientDual.lean` | 26 | `cb16627ac7e803309250b0019d3f164af1b0a4520eb1168a87369643f0d1d7c9` | `9b61ca596fcc4ceb881377ec425cba845e0a17d44fff6238a852e3db3472969e` |
| `QuotientChain.lean` | 11 | `6456d7ff9763088510514718cf7a63ad188aa1a21359aef84230de6e2728153d` | `677500ca4b32744c6e90e953f6e38aa6c595ecb1c4d7441c85fe1e42da5505ce` |

### 実行継続時の差分保護

元の専用worktreeの7未コミットfileは削除・reset・stashせず保護した。
対象と一致する稼働プロセス、キュー、スレッド記録から別writerの所有者は特定できず、別実行の存在も確定しなかった。
ユーザーの「このG-135証明スレッドのみ」という確認を受け、書込み先を新しい専用worktreeへ分離した。
7fileはコピー前後のSHA-256一致を確認して引き継ぎ、以後の実装は新しいworktreeだけで行った。
元のworktreeや稼働プロセスには変更・停止操作を行っていない。実行時の所有記録とコピーSHAはtask-local evidenceに残した。

### 初回独立4査読とF1修正

初回固定head `05d5b96150abfbca8594bafc432c025b1d98ccb7` への標準review-prから
math-lean-reviewの新規数学A/B・Lean A/Bへ委譲した。
[初回監査・4全文](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5295#issuecomment-6047386432)
は数学2本No major findings、Lean2本Minor issues。中心finding 0、非中心F1は
外部定義を直接展開する次数外ケースのAPI不足で、初回headはmergeしない。

F1の6箇所を、基本計算API `chainDegreeDifferential_out`、`degreeMap_out`、
`degenerateDegreeInclusion_out` と既存 `degreeObject_isZero` の使用へ置換した。
追加3宣言も対象fileの明示公理監査へ収録した。旧172宣言のstatement、生成defの値、
GOAL・設計・import方向を維持している。standard IsIsoとmono instanceの証明本体にも
触れるため、直接対応の資格を推定せず、新規4laneの正式再監査（再実行1回目）で判定する。
台帳status・全GOALのtarget-proof-checkpoint・completion_candidate:noは維持する。


## Cycle 4受理とmain同期

最終head `927f6be84e525e853df340d1ad7c45f5c9f47358`、
[最終監査・全4全文・新規直接確認](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5295#issuecomment-6047664301)。
全4再監査は中心0・非中心の45宣言一覧漏れのみで、report8行だけを補正し、
直接対応資格4条件と全解消を独立確認した。最終内容Mergeable、元の五条件を
`proof-obligation-discharged`として受理した。宣言は175件、全source/print/log/spine一覧は一致する。
[PR5295](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5295)は
`e4918e2da20f6492cc5486fd645e04118864cf68` で2026-10-07T22:04:25Zにiroha1203がmerge。
[Issue同期](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5290#issuecomment-6047777814)へ
証拠・未完義務・次cycleを記録した。最終head CI全8SUCCESS
([Lean](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/actions/runs/37693053932)、
[Tool](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/actions/runs/37693053929))。
Research integrity各gate実施success、Formal setup/cache/build/kernel/premiseはskipped。
Research full/aggregate/全file loop/lake build、Formal移植・実buildは未実施。
元のCycle4 selection/resultの記述は各提案時の履歴として保持する。

## Cycle 5 selection

```yaml
ledger_type: target_cycle_result
goal: G-135-aat-atlas-coefficient-fiber
cycle: 5
goal_blob_sha: cd5f3e684b7f390558796797874a1f16b52a6b18
base_oid: e4918e2da20f6492cc5486fd645e04118864cf68
tracking_issue: 5290
report_path: research/reports/G-135-aat-atlas-coefficient-fiber.md
selection:
  proof_state_ref: Cycle4受理とIssue5290同期6047777814
  proof_dag_predecessors: [PR5295指定Lと標準短完全列/H0零性, PR5294原始ΦΓΛと実局所同定, G134同じ支持chain, G133標準homology]
  milestone: GOAL B・完全列設計§1の原始fiber適合κと実H1L/R/標準H1Q同定およびforest特殊化
  proof_obligations: [原支持chainのEv/EhとFv/Fm/Fh block分解, Bの同じ原始Γ有向incidenceへの同定, aV/aD+bB/bH零式, 垂直homologyと全Φの有限直和同定, κ:y↦Dy類の構成, 原始垂直包含によるH1Lの商とcokκ同定, 有限双対/標準homologyによるH1Qとkerκ双対同定, 原始multigraph forestからkerB零とR全fiber直和同定]
  exit_criteria: [同じ元Kの全blockとΓ/Phi微分が原始基底上で同定され三零式を導出, 全垂直fiber homologyの両方向同型と同じDyからκを生成, 元の指定Lの標準H1がker a/(imV+DkerB)とcokκへ同じ垂直包含で両方向同定, R=kerκ双対を全ΦH1直和の部分空間として生成し標準H1Qへ両方向同定, loop/平行辺を保持した原始forest条件からkerB=0とRの全fiberH1同型を導出]
  selection_reason: 一般混在五項列とτが要求するfiber始域を指定Lから生成して固定し、全fiberを無条件に使う誤経路を閉じる
  expected_result_type: proof-obligation-discharged
  lean_targets: [RawBlocks.lean, FiberChains.lean, FiberHomology.lean, ChainHomologyDual.lean, Kappa.lean, DegenerateHomology.lean, RestrictionHomology.lean, GammaForest.lean]
  risks: [任意中間複体で実Lを置換しない, 垂直だけのL1へ弱めない, Rを期待次元/供給fieldから作らない, 双対同定と標準H1を独立に接続する, Γのloop/平行辺をforest判定で消さない, pure/forestを一般Mの追加仮定にしない]
  unchecked: [全選定obligationは実装前, τと完全列/filtration以降, C–Eと全W, 最終完了監査]
```

このselectionを実装前に固定する。五終了条件に必要な構成・両方向・接続を同じcycleで進め、
fileや補題一つの完成だけでcycleを閉じない。固定GOAL/設計/共通基準は変更しない。

## Cycle 5 spineと固定要求の対応

namespaceは `AAT.AG.AtlasCoefficientFiber`。新規11module・198宣言をこのcycleのspine候補として固定する。足場宣言は残していない。全宣言名を次に列挙し、source末尾の明示 `#print axioms` と一対一で対応させる。

| file | 全宣言 |
| --- | --- |
| `RawBlocks.lean` | `cellProjection`, `cellProjection_apply`, `cellInclusion_apply`, `cellInclusion_apply_notmem`, `cellProjection_cellInclusion`, `cellProjection_complementInclusion`, `cell_recombination`, `cellRecombination`, `cellDecomposition`, `cellDecomposition_fst`, `cellDecomposition_snd`, `HorizontalEdge`, `HorizontalFace`, `edgeBlockEquiv`, `verticalEdgeProjection`, `horizontalEdgeProjection`, `horizontalEdgeInclusion`, `horizontalFaceInclusion`, `verticalEdgeBoundary`, `verticalEdgeBoundary_apply`, `verticalEdgeBoundary_single`, `horizontalEdgeBoundary`, `mixedVerticalBoundary`, `mixedHorizontalBoundary`, `mixedHorizontalBoundary_apply`, `horizontalFaceBoundary`, `verticalEdgeProjection_inclusion`, `verticalEdgeProjection_horizontal`, `horizontalEdgeProjection_inclusion`, `horizontalEdgeProjection_vertical`, `edgeBlock_recombination`, `mixedBoundary_recombination`, `verticalEdgeBoundary_comp_verticalBoundary`, `mixedBoundary_square`, `horizontalFace_edge_mapped`, `horizontalFace_vertical_zero`, `horizontalFaceBoundary_inclusion`, `horizontalEdgeBoundary_comp_horizontalFaceBoundary`, `horizontalEdgeProjection_single`, `horizontalEdgeProjection_vertical_single`, `degenerateFaceSplitEquiv`, `faceBlockEquiv`, `faceBlockEquiv_vertical`, `faceBlockEquiv_mixed`, `faceBlockEquiv_horizontal` |
| `FiberChains.lean` | `phiChartPartition`, `phiEdgePartition`, `phiFacePartition`, `phiChartPartition_symm_val`, `phiEdgePartition_symm_val`, `phiFacePartition_symm_val`, `phiEdgePartition_symm_apply`, `phiFacePartition_symm_apply`, `phiChainEquiv0`, `phiChainEquiv1`, `phiChainEquiv2`, `phiChainEquiv0_apply`, `phiChainEquiv1_apply`, `phiChainEquiv2_apply`, `phiChainEquiv0_single`, `phiChainEquiv1_single`, `phiChainEquiv2_single`, `phiChainEquiv0_single_other`, `phiChainEquiv1_single_other`, `phiChainEquiv2_single_other`, `phiChainEquiv0_single_same`, `phiChainEquiv1_single_same`, `phiChainEquiv2_single_same`, `phiChainEquiv_comm1`, `phiChainEquiv_comm2` |
| `FiberHomology.lean` | `phiCycles`, `phiBoundaryToCycles`, `PhiHomology`, `phiVerticalCyclesEquiv`, `phiVerticalCyclesEquiv_val`, `phiVerticalCyclesEquiv_range`, `verticalHomologyPhiEquiv`, `verticalHomologyPhiEquiv_mk`, `kappa`, `kappa_apply`, `kappa_apply_component`, `kappa_range`, `allPhiHomologyAddCommGroup`, `allPhiHomologyModule`, `KappaCokernel`, `kappaCokernelCoordinateEquiv`, `kappaCokernelCoordinateEquiv_mk`, `kappaCokernelHomologyEquiv`, `kappaCokernelStandardEquiv` |
| `ChainHomologyDual.lean` | `chainBoundaryToCycles`, `ChainFirstHomology`, `chainDualComplex`, `cocycleHomologyEvaluation`, `cocycleHomologyEvaluation_mk`, `cocycleHomologyEvaluation_surjective`, `cocycleHomologyEvaluation_ker`, `chainHomologyDualEquiv`, `chainHomologyDualEquiv_mk` |
| `Kappa.lean` | `verticalCycles`, `verticalBoundaryToCycles`, `verticalBoundaryToCycles_val`, `VerticalHomology`, `mixedCycles`, `mixedCycle_vertical_closed`, `mixedCycleToVertical`, `mixedCycleToVertical_val`, `rawKappa`, `rawKappa_apply`, `rawKappa_eq_zero_iff`, `verticalRelations`, `mem_verticalRelations`, `rawKappa_range`, `rawKappaCokernelEquiv`, `rawKappaCokernelEquiv_mk` |
| `DegenerateHomology.lean` | `degenerateCycles`, `degenerateBoundaryToCycles`, `degenerateBoundaryToCycles_val`, `DegenerateHomology`, `verticalCycleInclusion`, `verticalCycleInclusion_val`, `verticalCycleHomologyMap`, `verticalCycleHomologyMap_apply`, `degenerateCycle_vertical_representative`, `verticalCycleHomologyMap_surjective`, `verticalCycleHomologyMap_ker`, `verticalRelationsHomologyEquiv`, `verticalRelationsHomologyEquiv_mk`, `rawKappaCokernelHomologyEquiv`, `degenerateOneShort`, `degenerateOneScIso`, `degenerateHomologyStandardEquiv`, `rawKappaCokernelStandardEquiv` |
| `FiberCohomology.lean` | `phiDualCochainEquiv`, `phiHomologyDualEquiv`, `allPhiHomologyDualEquiv`, `phiCohomologyVerticalDualEquiv`, `kappaStar`, `kappaStar_apply`, `kappaStar_raw`, `R`, `fiberR_eq_ker`, `kernelEquivOfEquiv`, `fiberRRawEquiv`, `fiberRRawEquiv_val` |
| `RestrictionHomology.lean` | `RawR`, `rawKappaAnnihilatorEquiv`, `rawKappaCokernelDualEquiv`, `rawKappaCokernelDualEquiv_apply`, `restrictionHomologyDualEquiv`, `restrictionStandardHomologyRawREquiv`, `restrictionStandardHomologyREquiv` |
| `GammaChains.lean` | `horizontalEdge_has_image`, `horizontalCarrier`, `horizontalCarrier_map`, `horizontalCarrier_eq`, `gammaVertexPartition`, `mixedNegativeEdge`, `mixedCarrier`, `mixedCarrier_patterns`, `gammaEdgePartition`, `gammaVertexPartition_symm_val`, `gammaEdgePartition_symm_val`, `gammaHorizontalVertex`, `gammaHorizontalVertex_val`, `mixedGraphSource`, `mixedGraphTarget`, `mixedGraphSource_val`, `mixedGraphTarget_val_left`, `mixedGraphTarget_val_right`, `mixedHorizontalBoundary_single`, `mixedHorizontalBoundary_eq_incidence`, `gammaVertexPartition_symm_apply`, `gammaVertexPartition_mixed_source`, `gammaVertexPartition_mixed_target` |
| `NamedForest.lean` | `namedUndirectedGraph`, `namedUndirectedGraph_inc`, `NamedForest`, `namedForest_graph_iff`, `namedIncidence`, `namedIncidence_single`, `namedIncidence_leaf_value`, `namedIncidence_eq_zero_iff`, `namedIncidence_injective`, `namedForest_no_loop`, `namedForest_no_parallel`, `namedForest_of_isEmpty`, `namedForest_of_subsingleton` |
| `GammaForest.lean` | `gammaUndirectedGraph`, `GammaForest`, `mixedHorizontalBoundary_ker_eq_bot`, `mixedCycle_eq_zero`, `rawKappa_eq_zero_of_forest`, `kappa_eq_zero_of_forest`, `kappaStar_eq_zero_of_forest`, `fiberR_eq_top_of_forest`, `forestFiberREquiv`, `forestFiberREquiv_apply`, `forestRestrictionHomologyEquiv` |


| 元の終了条件・固定条項 | 同じ入力からの証拠・方向 |
| --- | --- |
| 1 / B・完全列設計§1の全原block・三零式 | `cellDecomposition`・`edgeBlockEquiv`・`faceBlockEquiv` は元基底をEv/EhおよびFv/Fm/Fhへ両方向分類。各射影の同じ原係数式、`mixedBoundary_recombination` と `horizontalFaceBoundary_inclusion` から原∂₂の全blockを読む。`verticalEdgeBoundary_comp_verticalBoundary`・`mixedBoundary_square`・`horizontalEdgeBoundary_comp_horizontalFaceBoundary` は元∂²=0からaV=0、aD+bB=0、bH=0を導く |
| 1 / 同じ原Γ incidence B | `gammaVertexPartition`・`gammaEdgePartition` は元Eh/Fmと全Γ頂点/辺の非交和との両方向分類。`gammaVertexPartition_mixed_source/target` は同じ原Γ両端点へ可換、`mixedHorizontalBoundary_single/eq_incidence` は同じ原混在面の二パターンからB=target−sourceを示す。元面名・同じ辺の重複出現・loop・平行辺を保持 |
| 2 / 全垂直homology・κ | `phiChainEquiv0/1/2` は全原Φ基底への両方向同型、`phiChainEquiv_comm1/comm2` は元a/Vへ可換。`phiVerticalCyclesEquiv_range` は実V像の両包含、`verticalHomologyPhiEquiv` は全Φ H₁有限直和への両方向商同型。`mixedCycle_vertical_closed` は原aD+bB=0からDy閉路性を導出、`rawKappa`・`kappa` と代表APIは同じDyの類 |
| 3 / 指定Lの標準H₁と二商 | `verticalCycleHomologyMap` は指定Lへの元垂直包含。`degenerateCycle_vertical_representative`・`verticalCycleHomologyMap_surjective/ker` が全閉路代表と両方向核計算を与える。`verticalRelationsHomologyEquiv`・`rawKappaCokernelHomologyEquiv/StandardEquiv` はker a/(im V+D ker B)と原κ余核を実Lへ両方向同定。`kappa_range`・`kappaCokernelCoordinateEquiv`・`kappaCokernelHomologyEquiv/StandardEquiv` は同じ全Φ表示のκ余核へ両方向接続 |
| 4 / R=ker κ*、標準H¹Q≅R | `chainHomologyDualEquiv` は実微分のhomology双対を閉代表評価から生成。`phiHomologyDualEquiv`・`allPhiHomologyDualEquiv` は既存の各Φ cochain H¹との実双対同型。`kappaStar`・`R` は同じ全Φ H¹内の部分空間で、`kappaStar_raw`・`fiberRRawEquiv` により原垂直表示へ両方向接続。`restrictionStandardHomologyREquiv` は指定Qの標準H¹を同じRへ両方向移す |
| 5 / 原Γの無向多重forest特殊化 | `namedUndirectedGraph` は元辺名を保つmathlib Graph。`NamedForest` は全非空有限辺部分集合のleaf特徴付け、`namedForest_graph_iff` は同じnative Incへ接続。`namedIncidence_leaf_value/eq_zero_iff` からker B=0、κ=κ*=0、R=⊤を導く。`forestFiberREquiv`・`forestRestrictionHomologyEquiv` は同じR/標準H¹Qを全Φ H¹有限直和へ両方向同定。空辺・一非loop辺で条件が成立し、loop・異名平行辺で不成立となることも原端点から導く |

有限直和は有限な `Nc.ChartInTargetSubset A` を添字とするPiで表示する。
有限性は元nerveの有限chartと支持部分型から得る。`sigmaFinsuppLEquivPiFinsupp`、
`Submodule.quotientPi`、`LinearMap.lsum` の同じ有限添字の同型を使い、
全fiberを保持した両方向の写像と代表式を示す。

### Cycle 5前提・生成・proof-use

| 前提 | 分類・出所 | 使用・放電 |
| --- | --- | --- |
| ℚ、任意の両側nerve・reading順序・任意M/A、Af=π⁻¹A | 本文由来 / ambient-boundary / 固定T0 | 元のchainD1/D2・Ev/Fv/Fmと実支持輸送へ使用。全A・空Aを保持し、一般構成へforest/pureを追加しない |
| 符号付き原∂²=0とM退化面パターン | 放電済み / discharge-required | G134の `chainD1_comp_chainD2` と受理済み `degenerate_face_cases` から三零式・混在二パターン・mapped面零垂直成分を導く |
| Generic chain dualityの二微分と平方零、有限次元性 | 一般APIの direction-hypothesis、実適用で放電済み | 実a/V、各原Φの二微分、指定Lの二微分と各producerを渡す。有限名前付き自由module、その部分空間・商、双対から有限次元instanceを得る。全Φのnative Pi加法群/moduleを二つの局所instanceで先に解決し、余核の型推論へ渡す。追加仮定はない。cochain評価の核・全射性を証明して同型を出力 |
| κのDy閉路性、関係商と実Lの同型、κ*核同型、標準H¹Q同型 | 放電済み / discharge-required | 原aD+bB=0、元L₂のFv/Fm分解と水平射影、quotient/double dual APIから構成。結論field・同型引数・供給rankは使用しない |
| 無向多重forest | 本文由来 / direction-hypothesis / B forest特殊化のみ | 原端点に対する全部分有限辺集合のleaf条件を実非零chainのsupportへ適用し、係数零性を導く。κ零性を入力にしない。W3等での具体forest生成は後続W義務 |
| Generic annihilator / kernel transportの可逆座標 | 放電済み / discharge-required | `verticalHomologyPhiEquiv`・`phiHomologyDualEquiv`・同じcokerκの標準quotient同型がproducer。全fieldは原係数値、線形性、両逆と原微分可換性を証明から生成 |

新たな同型・exactness・rankの入力slotはない。一般forest定理の方向仮定は
指定例Wの放電を代替せず、W3・W5を未完として保持する。

### Cycle 5依存DAGと追跡

- `RawBlocks` → PR5295の元 `DegenerateCells/Subcomplex` と元G134支持chain。原None/Someセルの全基底分解へ使用。
- `Kappa` → `RawBlocks` → 原Dy閉路・垂直商・第二同型定理。
- `ChainHomologyDual` → PR5295 `DualRestriction` / std3と固定mathlibの `Subspace.dualRestrict_surjective`、`range_dualMap_eq_dualAnnihilator_ker`、quotient。
- `DegenerateHomology` → `Kappa` ＋ PR5295元 `DegenerateChain` ＋ `ChainHomologyDual` → 同じ実L閉路・Fv/Fm・標準H₁。
- `FiberChains` → `RawBlocks` ＋ PR5294元 `LocalFiber.lean` のPhiChart/PhiEdge/PhiFace・phiBoundary1/2 → 全Φ基底・原a/V。
- `FiberHomology` → `FiberChains/Kappa/ChainHomologyDual/DegenerateHomology` → 全Φ一次homologyと同じκおよびcokerκ標準同定。
- `FiberCohomology` → `FiberHomology` ＋ 既存 `CochainEquiv.h1Equiv` → 実Φ cochain H¹・同じκ*・R。
- `RestrictionHomology` → `DegenerateHomology/ChainHomologyDual/FiberCohomology` → 同じ実標準H¹Q≅R。
- `GammaChains` → `RawBlocks` ＋ PR5294元 `LocalFiber.lean` のGammaVertex/GammaEdge・gammaSource/Target → 同じ原Γ分類・両端点・B。
- `NamedForest/GammaForest` → 原名付き多重Graph/leaf証明 ＋ `GammaChains/RestrictionHomology` → forest特殊化。

受理predecessorの版・review資格はCycle3/4の上記監査URLに固定され、今回使用箇所に
関係する定義・statement・適用引数を現sourceで読む。内部査読履歴全体の再認定をしない。
G133/G134の版は冒頭の固定参照を維持し、使用する元支持chain、標準zeroExtension、
oldH1Equiv、moduleCatHomologyIsoと各公開producer/APIを現在のstatementで適用する。
mathlib/Leanの固定版はCycle1の記録を維持する。Graphは使用版にBasicのみがあり、
native forest述語APIがないため有限部分グラフのleaf特徴付けを採用し、そのIncへ同定する。

## Cycle 5 result・audit提案

```yaml
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: 原基底blockと全Φ/Γ分類から三零式・実κを生成し、指定Lの標準H1と関係商/cokerκ、指定Q標準H1と実全Φ上Rを両方向同定。原ΓforestからkerB零とR全Φ特殊化を導出
  exit_criteria_status: [1全原blockと同じΓ/Phi微分および三零式あり, 2全垂直homology両方向と同じDyのκあり, 3同じ垂直包含による指定L標準H1と両商同定あり, 4全ΦcochainH1内R生成と指定Q標準H1両方向同定あり, 5原名付きforestからkerB零と全ΦR同型あり]
  split_reason: none
  completion_candidate: no
  lean_artifacts: [RawBlocks.lean, FiberChains.lean, FiberHomology.lean, ChainHomologyDual.lean, Kappa.lean, DegenerateHomology.lean, FiberCohomology.lean, RestrictionHomology.lean, GammaChains.lean, NamedForest.lean, GammaForest.lean]
  evidence: 上記全198宣言・五条件対応・単一file検証・公理監査
  claim_mapping:
    theorem_names: 上記全198宣言spine
    source_labels: [GOAL B, exact-sequence §1, T0]
    conjuncts: 上記五終了条件対応表
    undischarged_assumptions: []
    acceptance_point: 元の五終了条件を構成・両方向・標準APIへ接続した候補。固定headの独立査読とroot再統合により受理を判断
    port_status: unported
audits:
  premise_delta:
    discharged: [原Ev/Eh/Fv/Fm/Fh分類と平方零三式, 原B=全Γincidence, 実Dy閉路とκ, 全Φchain/cochain双対, 指定L標準H1=cokerκ, 指定Q標準H1=R, forest原incidence単射]
    remaining: [Bのτと五項列/filtration/消滅同値/pure, C–E, W1–W5, 最終独立完了査読]
  certificate_provenance:
    discharged: [全分類の両逆と原係数式, 実垂直包含のsurj/ker, quotient/dualの元評価, 同じ原Γ leaf support証明]
    unresolved: []
  proof_use:
    used: [元支持微分と実L, 退化三パターン, 全fiber分類, 原Γの全辺/面名と両端点, 標準homology/quotient/dual, forest方向仮定]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: 次の単一file検証表と機械scan
  blocking_findings: []
  next_obligation: Bの同じ標準短完全列連結射τと五項列の全写像/隣接完全性、代表βB=-zDとτ=βH、carrier filtrationとd2への実接続
```

元selectionの八targetに、必要な全Φ cochain接続の `FiberCohomology`、同じ原Γの
`GammaChains`、汎用多重forest証明 `NamedForest` を加えた。数学的到達点・元五終了条件は維持する。
τ・filtration・保存条件・Law自然性・有限行列判定と全固定例は完了根拠へ数えず、
全GOALの独立4本完了監査はこれらの放電後に別途実施する。Issue5290はopenを維持する。

### Cycle 5単一file検証と公理監査

各コマンドはリポジトリrootで `bash research/lean/check_research_modules.sh --focused ResearchLean/AG/AtlasCoefficientFiber/<file>.lean` として単独実行した。現sourceの11 focused checkはすべてexit 0、error/warning 0。各moduleの明示 `#print axioms` と `#assert_standard_axioms_only` は全198宣言を監査し、依存は `propext` / `Classical.choice` / `Quot.sound` の部分集合のみ。

| file / 件数 | source SHA-256 | focused stdout+stderr SHA-256 |
| --- | --- | --- |
| `RawBlocks.lean` / 45 | `99e4f1cea07b288a6713c7e5757cb373ed27d52666184c47bb0e325861e536db` | `391fff62fbef07925930d224a27bf2c061017fa69ea16670b4a21b07f106e84a` |
| `FiberChains.lean` / 25 | `04b412ea259af7c33f406a3ac2803e5b822633407ef60144e4faf8a37ef03774` | `9fc63cba818fc15fb4a12f07624a36cb9036f8587c82fba6d59d5c32ae83c0f0` |
| `FiberHomology.lean` / 19 | `7002890ed28d4ad6996c7cd2851e8399f901cb5ff0ebe692a7e7cbbe0f355aed` | `0ff2f76f6914255b7c5364b18b33382a8e09ff7fd7c4fe15eb5664ad1fb4679b` |
| `ChainHomologyDual.lean` / 9 | `d1eadbbb132bd199cff5b8b92aaadc719971a39f7ae8679187c8b38c8d7997d2` | `7b9de290ed87a7d12a235c192d796ba39681e47a56c0484933d0e0d18325da63` |
| `Kappa.lean` / 16 | `d82d43acacfb6bb5f30298e71603464adae075119fb311ac762ae85279a4193b` | `f838e43b47f4eeed00aa1f4c2e744434462a7de7709a2e153f155c5ddbcfea43` |
| `DegenerateHomology.lean` / 18 | `168c24bd3178e41860364a158453b8996331e9077624ed10f013da9a3624a7fb` | `7575017ede35ab01587f38c8ffb42b7bee7e84e461b413bf4cc29616dff3011f` |
| `FiberCohomology.lean` / 12 | `cf85c289ff0cb0ead245ccd2fd8e9860fec4a489f17e75b85a9da885ace99c67` | `e103ae0f0e32db35781f428d459976c5b645d1b2066e1ff26f2647496269efa9` |
| `RestrictionHomology.lean` / 7 | `edde3fdc56eec794ebf36f976622a315f4926a2627f2a930170f29cf39690fe8` | `68935ab0c4261167d0286adfa15c3fce60f0601c90f45678fc7ac5b37651db80` |
| `GammaChains.lean` / 23 | `5943afba7cddb60d1614f29413ba5bcf9b9dcba7d6381f4d2d4e0e0fcab3719f` | `593f26fe23686a13399a33e0c71f544c15c3b7c092f04c987623a0ff561afa71` |
| `NamedForest.lean` / 13 | `2116f69b5a631b72e637e143c5e60543747cb384638208513a640b781b17688e` | `6a840d61566d38c4325e4b9eb60a7c1938f8b16464784afef95a755db94eec44` |
| `GammaForest.lean` / 11 | `c783cd60bb052d487adaee010650109b8df5d89d31fb1c0b81458316d8f09948` | `8d369064a0e3b28c5f25c2a64b175fc921407fc128a785f929022a145c8fea83` |

検証metadataは `.tmp/g135/cycle5-validation.json`（SHA-256 `546cd269c1921cc6ed0fdfc41abb7405a449f8893ec8ba6dbdf64606e4008574`）。上記全宣言のsource/print/log/report一覧を一致させた。必要な単一import cacheも同じfileの `lake env lean -o <cache> <file>` で生成した。Research full/aggregate/全file loopのelaborationとlake buildは未実施。Formalへの移植・実buildは未実施で、成果はunported (Research-proved)。最終全GOAL完了査読は未実施。

共通scanは `.tmp/g135/cycle5-scans.json`（SHA-256 `1ba881cc99290b9e9d31c64e27002514adb608fc74ec8c8c05a02e9bf020a892`）へ固定した。変更14fileを列挙し、placeholder/new axiom、hidden/BiDi、privacy/local-path、追加語彙、`git diff --check`、Formal逆importを確認してclean。全198名のreport一覧もsource/print/logと一致。GOAL・設計・Formal・保護数学本文は変更していない。

## Cycle 5受理とmain同期

最終head `61659d7586accb379f03883d3722c5d6a622fad2`、
[最終監査・初回4本全文・新規直接確認](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5296#issuecomment-6049620284)。
初回4本は中心0・非中心の公開API/定理名/依存参照の指摘だけで、全指摘限定修正と
新規直接確認が解消・資格を独立確認した。最終内容Mergeable、元五条件を
`proof-obligation-discharged`として受理。全198名のsource/print/log/spineと順序が一致する。
[PR5296](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5296)は
`482d0ad4282224abb1de1f43921c2568b952df8b` で2026-10-08T00:40:07Zにmerge。
[Issue同期](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5290#issuecomment-6049762466)へ
放電・未完・次cycleを記録した。最終head CI全8SUCCESS
([Lean](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/actions/runs/37708310496)、
[Tool](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/actions/runs/37708310329))。
Research各実gate成功、Formal setup/cache/build/kernel/premiseはskipped。
Research full/aggregate/全file loop/lake build、Formal実build/移植は未実施。
元selection/resultは提案時の履歴として保持する。

## Cycle 6 selection

```yaml
ledger_type: target_cycle_result
goal: G-135-aat-atlas-coefficient-fiber
cycle: 6
goal_blob_sha: cd5f3e684b7f390558796797874a1f16b52a6b18
base_oid: 482d0ad4282224abb1de1f43921c2568b952df8b
tracking_issue: 5290
report_path: research/reports/G-135-aat-atlas-coefficient-fiber.md
selection:
  proof_state_ref: Cycle5受理とIssue5290同期6049762466
  proof_dag_predecessors: [PR5295の同じ標準短完全列とH0Q零性, PR5296の原block/κ/実H1Q=R, G133の標準homologyと端商同型, 固定mathlibのShortExactδ評価と全隣接完全性]
  milestone: GOAL B・完全列設計§2–3の実短完全列連結射と五項列を原block代表/chain連結射/原始消滅条件へ両方向接続
  proof_obligations: [同じε/制限から標準δとR上のτを構成, H0Q零性からH1ε単射と五項列の全写像/全隣接完全性, 原閉zとR条件からβB=-zDのβを生成, 原持ち上げの微分がmapped面でβHとなり標準δ評価と一致, β選択/zのcoboundary/可逆基底変更の独立性, 同じK/LのH2とkerHbarおよびBy=Hxからchain連結射[-Dy]の構成とτ双対同定, τ零と全By=Hxに対するDy関係像包含の同値および全A版, 旧hereditary入力からmixed空性を導きκとτ零性]
  exit_criteria: [任意M/Aの指定R上τが同じ標準短完全列δの輸送で構成される, 五項列の各指定射と全隣接三項完全性/H1ε単射が実生成定理, Rの全代表からβの存在を導出しτのβH式が標準δの評価式へ同定, β選択/z変更/基底変更で同じhomology類を返す, 原商H2と同じBy=Hxのchain連結射を両方向接続しτ双対から原始像包含との必要十分条件と全A版を得る, pure旧hereditaryの実入力からmixed零性とκ/τ零を導く]
  selection_reason: 全体診断に必要な一般混在τとその消滅を同じ原始行列から計算する再利用可能な数学的到達点。実carrier filtration/E1/E2/d2はこの標準δと代表式を利用する次の構成群であり未完のまま保持
  expected_result_type: proof-obligation-discharged
  lean_targets: [FiveTermSequence.lean, CochainRepresentatives.lean, HomologyRepresentatives.lean, TransgressionRepresentatives.lean, ConnectingEvaluation.lean, QuotientHorizontalHomology.lean, QuotientHomologyDual.lean, ChainConnecting.lean, TauDuality.lean, TransgressionVanishing.lean, PureComparison.lean]
  risks: [任意の中間複体や期待rankで代替しない, βの存在/完全性/同型を供給premiseへ移さない, L1のmixed全微分を維持, chain連結射の負符号と標準δの正符号を実評価で一致, forestだけからτ零を推論しない, filtration/d2未接続をtransgression全要求完了と数えない, 有限線形代数algorithmと全Wは後続義務]
  unchecked: [全選定obligationは実装前, 実carrier filtration/E1/E2/d2, C–Eと全W, 最終新規独立4本完了監査]
```

実装前にこの到達点と六終了条件を固定する。全終了条件に必要な構成・逆方向・
原始入力・標準写像の接続を同じcycleで進める。固定GOAL/設計/共通基準は維持する。


## Cycle 6 到達点と受理候補

同じ原始Mと任意の支持Aに対し、実ε・実L双対制限の標準短完全列から
`connectingTau` と五項列を構成した。Rの全類から原V閉代表zとβB=-zDを生成し、
原補正微分のP₂原像を標準δの `δ_eq` へ照合した。
商の二次閉路は同じliteral K′₂/L₂と原微分の核から水平ker Hbarへ両方向同定する。
原By=Hxの持ち上げをK′で微分して-I_vDyとなる式と、そのH₁L類を構成した。
同じ実H²Pの双対評価を通してτと鎖連結写像を同定し、τ零性を原始D像包含の
必要十分条件、および全A版に戻した。旧hereditary条件からmixed空性とκ/τ零を導く。

これは六つのCycle6終了条件についての受理候補である。初回独立PR査読は下記の指摘を返し、修正後の正式再査読を待つ。
固定GOAL全体は `target-proof-checkpoint`、`completion_candidate: no` のままである。
carrier filtration/E₁/E₂/d₂、Cの保存条件と錐、Dの自然性・G134操作、Eの生成有限計算、
全Wの同じ原始表による評価、最終新規4本完了監査は未完である。

| 六終了条件 | 入力からの構成と検証宣言 |
| --- | --- |
| 1 実R上の標準δ | `connectingTau`、`connectingTau_restrictionStandardHomologyREquiv`。PR5295の実短完全列とPR5296のR同型を同じM/Aで適用 |
| 2 全五項射・全隣接完全性・H¹ε単射 | `evaluationH1_injective`、`fiveTerm_exact_at_fineH1`、`fiveTerm_exact_at_fiber`、`fiveTerm_exact_at_pushforwardH2`。元H⁰Q零性と固定mathlibの標準homology sequenceを輸送 |
| 3 全Rの原補正生成・標準δ公式 | `fiberClass_has_correction`、`horizontalCorrection_exists`、`correctedEdgeCochain_d1_degenerate`、`evaluationRestriction_connecting_representative`、`connectingTau_correctedFiberClass`、`connectingTau_horizontal_evaluation`。Pは独立生成済みの実Kan順像で、ε原像全射性から代表を生成 |
| 4 代表・基底への独立性 | `correctedPushforwardCochain_independent_correction`、`correctedPushforwardCochain_coboundary`、`connectingTau_basis_independent`。任意有限基底の行列評価を同じ標準homologyへ戻す |
| 5 原商二次閉路・実鎖連結・双対・両方向消滅 | `quotientSecondCyclesEquiv`、`quotientStandardH2HorizontalEquiv`、`supportedBoundary_horizontalLift`、`quotient_horizontalLift`、`quotientChainConnecting_apply`、`pushforwardStandardH2HorizontalDualEquiv`、`connectingTau_chain_duality`、`connectingTau_zero_iff_primitive`、`connectingTau_allA_zero_iff_primitive` |
| 6 旧hereditaryからpure | `hereditary_mixedFace_isEmpty`、`hereditary_kappa_zero`、`hereditary_connectingTau_zero`。原Hのface_none_edge1と同じMixedFaceの負辺some条件から空性を生成 |

### Cycle 6 proof DAG と material premise

受理済みPR5295の実ε/Q短完全列・H⁰Q零性 → PR5296の原a,V,B,D,H/κと標準H¹Q≃R
→ FiveTermSequence。原V閉代表のhomology評価とdualMap像定理 → CochainRepresentatives。
G133の元三項homology同型と固定mathlibのcycle射公開API → HomologyRepresentatives。
同じ原L₂のannihilationとε原像全射性 → TransgressionRepresentativesのP₂代表と標準δ公式。
元K′/Lの係数射影核 → QuotientHorizontalHomologyの二次閉路同型・標準商H₂同型。
原By=Hx → ChainConnectingの実K′持ち上げ微分とH₁L類。
同じ実ε双対 → QuotientHomologyDualのH²P評価同型。
原R関係商双対と両代表の評価 → TauDuality → TransgressionVanishing → PureComparison。
DegenerateHomologyとRestrictionHomologyへの三つの追加公開補題は、この同じ代表の評価を保存する。
既存定義・statement・instanceの値を変更しない。

| material premise | 分類と使用・放電 |
| --- | --- |
| 原M、Nc/Nf、reading比較、任意A、指定有限ℚ支持cell | 本文由来のambient-boundary。PR5289設計のまま全構成へ渡す |
| 原V閉z、βB=-zD | 代表補題のdirection-hypothesis。全Rへの適用では `fiberClass_has_correction` が原dual像から放電し、補正微分とδ代表で実使用 |
| By=Hx | 鎖代表と像包含のdirection-hypothesis。全水平商閉路では `mem_horizontalFaceCycles_iff` が存在を生成。差のker B所属とL内代表に実使用 |
| exactness、H⁰Q零性、H¹ε単射、R同定 | discharge-required。受理済み実構成と標準homology APIから放電。新しい入力fieldに移動しない |
| τ消滅 | `connectingTau_zero_iff_primitive` の結論。原始像包含と両方向同値として証明し、pure適用ではmixed空性から放電 |
| 旧hereditary H | pure方向の本文由来入力。H.face_none_edge1を実使用して同じ原mixed空性を生成 |
| 任意有限基底 | 座標独立性のdirection-hypothesis。基底によるτ行列の評価を標準類に復元する式。有限algorithmの生成義務はEに保持 |

対象はResearch側の証拠であり、Formal移植は `unported (Research-proved)`。
固定GOAL・design・保護数学本文・Formalを編集していない。

### Cycle 6 宣言spine・focused証拠

以下の対象source全宣言と生成補助を順序付きで固定する。新規source205宣言とLean生成補助 `horizontalLiftCycle.congr_simp` 1宣言を含む。
原blockと既存ownerの全宣言も検証するので、監査対象は合計317宣言（source316と生成補助1）である。
全19fileの対象単一focused check、各全宣言の明示printとmodule公理監査を照合する。
Research full/aggregate/全file loop/lake build、Formal実build/移植は未実施。

### Cycle 6 ledger（PR前の固定候補）

```yaml
ledger_type: target_cycle_result
goal: G-135-aat-atlas-coefficient-fiber
cycle: 6
base_oid: 482d0ad4282224abb1de1f43921c2568b952df8b
tracking_issue: 5290
completion_candidate: no
root_candidate_result: proof-obligation-discharged
whole_goal_status: target-proof-checkpoint
formal_status: unported (Research-proved)
proof_delta: [実短完全列δと五項列の全写像・隣接完全性, 全Rから原zとβの生成, 同じε原像による標準δ代表式, 原商H2と水平閉路の双方向同型, 原鎖持ち上げ微分とH1L連結類, τの同じ鎖連結写像との双対同定, 原始像包含との必要十分条件と全A版, 旧hereditaryからpure κとτ零]
representative_independence: [水平補正の選択, 原垂直coboundary変更, 任意有限基底による行列表示からの復元]
validation: 19対象fileの単一focused check成功、317明示print/公理監査、標準3公理のみ、共通scan clean
review_gate: 初回standard review-pr -> math-lean-reviewはMajor revisions、全指摘修正後のfresh4正式再実行1待ち
unchecked_cycle_center: []
uncompleted: [実carrier filtrationとE1/E2/d2, Cの核余核と次元と保存と三錐, Dの全Lawと自然性とG134適用, Eの原始生成有限有理線形代数algorithm, 全Wの固定表評価, final fresh4全目標完了監査]
next_milestone: 実carrier filtrationと低次数exact couple/E1/E2/d2=τの構成
```

六終了条件のroot照合を受理候補として固定した。独立内容査読・acceptance再統合・
CI・merge同期は後続ゲートとして追跡する。source版と受理済みPR5295/5296の
宣言statement・適用M/A、固定G133とmathlibの使用APIを確認した。
対象groupの追加11file登録・aggregate配線は静的登録のみで、aggregate elaborationは行わない。

### Cycle 6 初回PR査読と修正

PR5297の初回固定head `79f1d0ac713b4c875028bc390c879c8aaccf144c` に対し、
standard review-prからmath-lean-reviewへ委譲し、新規数学A/B・LeanA/Bの4本を実行した。
数学A/B・LeanAはMinor issues、LeanBはMajor revisions。
統合はMajor revisionsであり、このheadをmergeしない。
初回監査: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5297#issuecomment-6050704746
原始消滅述語の否定例不足をLeanBが中心findingと分類したため、親の裁量で非中心へ変更しない。
正式再実行は初回後の1回目で、直接対応による合格を作らない。

| finding | 修正証拠と現在の位置づけ |
| --- | --- |
| F1 新規Propの否定instance不足（LeanB:中心、他3本:非中心） | 指定W3のSource/reading/非定数Law/全台/原セル像とmだけを除くpaired表を生成。`primitiveTransgressionVanishing_false` が同じ原B・D・Hから否定を証明し、`primitiveTransgressionVanishing_paired_true` が指定paired全支持で肯定する。原式 `B_m_eq_H_difference`、`D_m`、`B_kernel_zero` と垂直面空性を実使用。実標準τの非零性は `WitnessThree.connectingTau_ne_zero` へ接続。W3の全診断評価は未完 |
| F2 非自明defのImplementation notes不足 | HomologyRepresentatives、TransgressionRepresentatives、ConnectingEvaluation、ChainConnecting、QuotientHomologyDual、TauDualityに採用した定義形と退けた代替案の理由を記載 |
| F3 別owner同型の定義展開 | 元G133 ownerに `oldH1Iso_hom_comp` と `oldH2Iso_hom_comp` を追加し、HomologyRepresentativesの既存statementを維持したまま公開API経由へ変更。元ownerを単一focused登録・明示print監査。RawBlocksにも原B/D/Hの具体基底評価に必要な6公開APIを追加 |

固定GOAL、設計と共通基準の変更はない。新規Propの値、既存def/instanceの値、
既存theoremのstatementは維持する。W3の否定例を他の弱いセル表で代替していない。
初回固定headのCIは全8checks SUCCESS。Formal build/kernelの実stepsはSKIPPED、
Research integrityの実stepsはSUCCESS。修正後headのCIと新規4本査読は別途確認する。


<!-- cycle6-generated-evidence -->

| file | 全宣言（source/生成補助/print/logの同順序） |
| --- | --- |
| `FiveTermSequence.lean` | `evaluationH1`, `fiberRestrictionH1`, `connectingTau`, `evaluationH2`, `connectingTau_apply`, `fiberRestrictionH1_apply`, `evaluationH1_apply`, `evaluationH2_apply`, `connectingTau_restrictionStandardHomologyREquiv`, `evaluationH1_injective`, `fiveTerm_exact_at_fineH1`, `fiveTerm_exact_at_fiber`, `fiveTerm_exact_at_pushforwardH2`, `fiberRestrictionH1_evaluationH1`, `connectingTau_fiberRestrictionH1`, `evaluationH2_connectingTau` |
| `CochainRepresentatives.lean` | `VerticalCocycles`, `verticalCocycleClass`, `verticalCocycleClass_mk`, `verticalCocycleClass_kappa`, `verticalCocycleClass_rawR_iff`, `horizontalCorrection_exists`, `verticalCocycleClass_rawR_of_correction`, `correctedFiberClass`, `correctedFiberClass_raw`, `verticalCocycleClass_surjective`, `fiberClass_has_correction`, `correctedEdgeFunctional`, `correctedEdgeFunctional_apply`, `correctedEdgeFunctional_vertical`, `correctedEdgeFunctional_horizontal`, `correctedEdgeCochain`, `correctedEdgeCochain_dual`, `correctedEdgeCochain_d1_eval`, `correctedEdgeCochain_d1_vertical`, `correctedEdgeCochain_d1_mixed`, `correctedEdgeCochain_d1_horizontal`, `correctedEdgeCochain_d1_degenerate` |
| `HomologyRepresentatives.lean` | `shortComplex_liftCycles_class`, `zeroExtension_liftCycles_H1`, `zeroExtension_liftCycles_H2`, `elementArrow`, `elementArrow_one`, `elementArrow_comp`, `elementArrow_zero`, `zeroExtension_liftCycles_H1_apply`, `zeroExtension_liftCycles_H2_apply` |
| `TransgressionRepresentatives.lean` | `correctedEdgeCochain_d1_restriction_zero`, `correctedRestrictionCycle`, `correctedRestrictionCycle_val`, `correctedPushforwardCochain_exists`, `correctedPushforwardCochain`, `correctedPushforwardCochain_spec`, `evaluationRestriction_connecting_representative`, `correctedRestrictionCycle_fiberClass`, `connectingTau_correctedFiberClass`, `correctedFiberClass_independent_correction`, `correctedPushforwardCochain_independent_correction`, `verticalCocycleClass_coboundary`, `correctedFiberClass_coboundary`, `correctedPushforwardCochain_coboundary`, `connectingTau_basis_independent` |
| `ConnectingEvaluation.lean` | `correctedCocycle_annihilates_relations`, `correctedRelationsFunctional`, `correctedRelationsFunctional_mk`, `correctedRelationsFunctional_horizontalLiftClass`, `correctedRelationsFunctional_horizontalChainConnecting` |
| `QuotientHorizontalHomology.lean` | `horizontalFaceProjection`, `horizontalFaceProjection_apply`, `horizontalFaceProjection_inclusion`, `horizontalFaceProjection_degenerate`, `face_recombination`, `horizontalFaceProjection_surjective`, `horizontalFaceProjection_ker`, `quotientFaceEquiv`, `quotientFaceEquiv_mk`, `quotientFaceEquiv_symm_apply`, `HorizontalEdgeQuotient`, `horizontalQuotientBoundary`, `horizontalQuotientBoundary_apply`, `HorizontalFaceCycles`, `mem_horizontalFaceCycles_iff`, `horizontalEdgeQuotientProjection`, `horizontalEdgeQuotientProjection_apply`, `horizontalEdgeQuotientProjection_surjective`, `horizontalEdgeQuotientProjection_ker`, `quotientEdgeEquiv`, `quotientEdgeEquiv_mk`, `horizontalEdgeQuotientProjection_degenerate`, `horizontalEdgeQuotientProjection_boundary_degenerate`, `horizontalEdgeQuotientProjection_boundary_horizontal`, `quotientBoundary2_horizontal`, `QuotientSecondCycles`, `quotientSecondCyclesEquiv`, `quotientSecondCyclesEquiv_val`, `quotientSecondCyclesEquiv_symm_val`, `quotientSecondShort`, `quotientSecondScIso`, `quotientSecondStandardEquiv`, `quotientStandardH2HorizontalEquiv` |
| `QuotientHomologyDual.lean` | `pushforwardSecondCycleEvaluation`, `pushforwardSecondCycleEvaluation_apply`, `pushforwardSecondCycleEvaluation_surjective`, `pushforwardSecondCycleEvaluation_ker`, `pushforwardSecondHomologyDualEquiv`, `pushforwardSecondHomologyDualEquiv_mk`, `pushforwardStandardH2HorizontalDualEquiv`, `pushforwardStandardH2HorizontalDualEquiv_mk` |
| `ChainConnecting.lean` | `horizontalLift_vertical_closed`, `horizontalLiftCycle`, `horizontalLiftCycle_val`, `horizontalLiftClass`, `horizontalLiftClass_mk`, `horizontalLiftClass_independent`, `horizontalLiftClass_eq_zero_iff`, `horizontalCycleLift`, `horizontalCycleLift_spec`, `horizontalChainConnecting`, `horizontalChainConnecting_apply`, `horizontalChainConnecting_eq_zero_iff`, `supportedBoundary_horizontalLift`, `quotient_horizontalLift`, `quotientChainConnecting`, `quotientChainConnecting_apply`, `horizontalLiftCycle.congr_simp` |
| `TauDuality.lean` | `fiberRelationsDualEquiv`, `fiberRelationsDualEquiv_mk`, `fiberRelationsDualEquiv_corrected`, `connectingTau_horizontal_evaluation`, `connectingTau_chain_duality` |
| `TransgressionVanishing.lean` | `PrimitiveTransgressionVanishing`, `horizontalChainConnecting_zero_iff_primitive`, `connectingTau_zero_iff_chain`, `connectingTau_zero_iff_primitive`, `connectingTau_allA_zero_iff_primitive` |
| `PureComparison.lean` | `hereditary_mixedFace_isEmpty`, `kappa_zero_of_mixed_isEmpty`, `primitiveVanishing_of_mixed_isEmpty`, `connectingTau_zero_of_mixed_isEmpty`, `hereditary_kappa_zero`, `hereditary_connectingTau_zero` |
| `DegenerateHomology.lean` | `degenerateCycles`, `degenerateBoundaryToCycles`, `degenerateBoundaryToCycles_val`, `DegenerateHomology`, `verticalCycleInclusion`, `verticalCycleInclusion_val`, `verticalCycleHomologyMap`, `verticalCycleHomologyMap_apply`, `degenerateCycle_vertical_representative`, `verticalCycleHomologyMap_surjective`, `verticalCycleHomologyMap_ker`, `verticalRelationsHomologyEquiv`, `verticalRelationsHomologyEquiv_mk`, `rawKappaCokernelHomologyEquiv`, `rawKappaCokernelHomologyEquiv_mk`, `degenerateOneShort`, `degenerateOneScIso`, `degenerateHomologyStandardEquiv`, `rawKappaCokernelStandardEquiv` |
| `RestrictionHomology.lean` | `RawR`, `rawKappaAnnihilatorEquiv`, `rawKappaCokernelDualEquiv`, `rawKappaCokernelDualEquiv_apply`, `restrictionHomologyDualEquiv`, `restrictionStandardHomologyRawREquiv`, `restrictionStandardHomologyREquiv`, `restrictionStandardHomologyRawREquiv_mk`, `restrictionStandardHomologyREquiv_raw` |
| `RawBlocks.lean` | `cellProjection`, `cellProjection_apply`, `cellInclusion_apply`, `cellInclusion_apply_notmem`, `cellProjection_cellInclusion`, `cellProjection_complementInclusion`, `cell_recombination`, `cellRecombination`, `cellDecomposition`, `cellDecomposition_fst`, `cellDecomposition_snd`, `HorizontalEdge`, `HorizontalFace`, `edgeBlockEquiv`, `verticalEdgeProjection`, `horizontalEdgeProjection`, `horizontalEdgeInclusion`, `horizontalEdgeInclusion_single`, `horizontalFaceInclusion`, `verticalEdgeBoundary`, `verticalEdgeBoundary_apply`, `verticalEdgeBoundary_single`, `horizontalEdgeBoundary`, `mixedVerticalBoundary`, `mixedHorizontalBoundary`, `mixedHorizontalBoundary_apply`, `horizontalFaceBoundary`, `mixedVerticalBoundary_apply`, `horizontalFaceBoundary_apply`, `horizontalFaceInclusion_single`, `verticalEdgeProjection_inclusion`, `verticalEdgeProjection_horizontal`, `horizontalEdgeProjection_inclusion`, `horizontalEdgeProjection_vertical`, `verticalEdgeProjection_single`, `verticalEdgeProjection_horizontal_single`, `edgeBlock_recombination`, `mixedBoundary_recombination`, `verticalEdgeBoundary_comp_verticalBoundary`, `mixedBoundary_square`, `horizontalFace_edge_mapped`, `horizontalFace_vertical_zero`, `horizontalFaceBoundary_inclusion`, `horizontalEdgeBoundary_comp_horizontalFaceBoundary`, `horizontalEdgeProjection_single`, `horizontalEdgeProjection_vertical_single`, `degenerateFaceSplitEquiv`, `faceBlockEquiv`, `faceBlockEquiv_vertical`, `faceBlockEquiv_mixed`, `faceBlockEquiv_horizontal` |
| `ZeroExtension.lean` | `degreeObject`, `degreeDifferential`, `degreeDifferential_square`, `zeroExtension`, `degreeMap`, `degreeMap_comm`, `zeroExtensionMap`, `zeroExtensionMap_comp`, `oldShort`, `zeroExtensionScIso`, `oldH1Iso`, `oldH1Iso_hom_comp`, `oldShortMap`, `oldShortMapData`, `oldShortMap_homology`, `zeroExtensionScIso_natural`, `oldH1Iso_natural`, `degreeObjectFiniteDimensional`, `zeroExtension_X`, `degreeObject_isZero`, `zeroExtension_d`, `zeroExtensionMap_f`, `zeroExtensionMap_id`, `oldH1Equiv`, `oldH1Equiv_natural`, `zeroExtensionDegreeFiniteDimensional`, `zeroExtension_homology_isZero`, `homologyTransport_natural`, `zeroExtension_d0_apply`, `zeroExtension_d1_apply`, `zeroExtension_d_zero`, `zeroExtensionMap_f0_apply`, `zeroExtensionMap_f1_apply`, `zeroExtensionMap_f2_apply` |
| `EndpointHomology.lean` | `oldZeroShort`, `oldTwoShort`, `zeroExtensionZeroScIso`, `zeroExtensionTwoScIso`, `oldH0Iso`, `oldH2Iso`, `oldH2Iso_hom_comp`, `oldH0Equiv`, `oldH2Equiv` |
| `WitnessCommon.lean` | `Source`, `qc`, `qf`, `coarser`, `not_coarser`, `factor`, `laws`, `adequate_coarse`, `adequate_fine`, `law_nonconstant`, `label`, `labels_ne` |
| `WitnessThreeInput.lean` | `coarseNerve`, `fineNerve`, `Nc`, `Nf`, `M`, `pairedNerve`, `pairedNf`, `pairedM` |
| `WitnessThreeNonzero.lean` | `selectedEdge`, `selectedFace`, `k`, `a0`, `a1`, `b`, `c`, `f0`, `f1`, `m`, `a0_ne_a1`, `mixedFace_eq_m`, `verticalFaceIsEmpty`, `m_edge0`, `m_edge1`, `m_edge2`, `f0_edge0`, `f0_edge1`, `f0_edge2`, `f1_edge0`, `f1_edge1`, `f1_edge2`, `B_m`, `D_m`, `H_f0`, `H_f1`, `B_m_eq_H_difference`, `mixedChain_single`, `B_kernel_zero`, `pairedMixedIsEmpty`, `primitiveTransgressionVanishing_paired_true`, `primitiveTransgressionVanishing_empty_true`, `primitiveTransgressionVanishing_false`, `connectingTau_ne_zero` |

| file / declarations | source SHA-256 | focused output SHA-256 |
| --- | --- | --- |
| `FiveTermSequence.lean` / 16 | `c9fb934891dfd966ac23711e566cda115987220862e904c63cc5f9ed002687e3` | `e760ecfbdeadee97f842fa7ecd30c86c6eaa3144dfa49cdea5d989adadc9505c` |
| `CochainRepresentatives.lean` / 22 | `95807117bdb00bfc921f677118a6770a6abd0c38831f1b11ff934d46c4885025` | `446b6d4f660001f331bb8696710fa439cfc04de5718ea3c173d8d4f121d7b6bc` |
| `HomologyRepresentatives.lean` / 9 | `39921558a14922e4a8780463780fd05cf4c7c05cd23b8c52b783e3175e50dfd0` | `9f4679736dc328632f559ac35cde32e2c63b1a109fd85ab07e509cc86f01c95e` |
| `TransgressionRepresentatives.lean` / 15 | `264aa0a0632fe0a27991b1e9c6483670b29c1782e684e925428def8383c9d139` | `1ea5b24f2199e731082ab92fcb7823616eb89f536c067519b08954bae5d3e579` |
| `ConnectingEvaluation.lean` / 5 | `77614b92a1a032da401f04b2a0171c3548f2171fe896f226baefb0bff1d02e4d` | `6e43550df0550ffdf0fa1e09a7690cadb6b96d6f6071b4231a8e43d6c3a2e3e7` |
| `QuotientHorizontalHomology.lean` / 33 | `76cbf24ec3af1a7254b495228133ea3cb7ec42168cbd1e4cae12f0d05cb76ab3` | `de196a0fb09d878b457b8e3803462134507898c892cf891e37ba9879405e45e8` |
| `QuotientHomologyDual.lean` / 8 | `672f9c0149a5b34425b2fcbc803266cc984830e2b343840a91074d0ed3768ab2` | `95ed445aedf859af512ee495e61bb6bdcb2aeb0485ae2d46919c276a40512f9b` |
| `ChainConnecting.lean` / 17 | `565a5f23fad6c762af8cf912c62e132b9c76afede11bc1dd479c5a4aab8fe9dc` | `06b8e070ec0fd7a1ee6370d44c868b1ed74727011c88680e17e6e6ba1fcb7c65` |
| `TauDuality.lean` / 5 | `2dc630fc5d2af9bdd7f94f940d3e3c4ccf87f5147aa611711e36e26c7a93468a` | `2248e13f9319d063aabfbc43bc98482188414b77ff6cc37ac18a2647cd0a8030` |
| `TransgressionVanishing.lean` / 5 | `8247eb4a43cd04daa088bf10efd09e6fc5e54870db8496f550f4c56d48f2e82e` | `04e92ce8390e6aef090e3ada17da818deeec64dfa2ba993156c6906e231749d7` |
| `PureComparison.lean` / 6 | `ed95e9286b51c7ce15fb05e0fe19f83ac574e321ee1a01ec4216c951fc767d01` | `9f5a432519268f9b1e4495e6616e7f3e734322e3a3d2b7be98ec1e4e08934dd0` |
| `DegenerateHomology.lean` / 19 | `ee27d7247068a6e80c3c46401b7f964d87ccdcf2a4be092b7c26c5308c9e2ee8` | `f495dbef516debbd346ede151f4b889ff335c7363679c0b11fad8ede6e7e0065` |
| `RestrictionHomology.lean` / 9 | `44317eec491e425838829730a8c8c1474b8f855c8a97f58f82d8d0ac3ed1f5d0` | `766ace1b65d703f27bd676e99755294e97a44a6a57685dbd3026690e26e9b3c5` |
| `RawBlocks.lean` / 51 | `51204e6ae76527a20e03709955b9fb19d01dc0bd51b373c6f85ef1b3729142ef` | `d5ec83c6d5b3cf16278dcac086596ae1ed341fa19ec1a6bc4c71ec6fb4995796` |
| `ZeroExtension.lean` / 34 | `1c69bab689742a84e991b30c52aa43719481db15d9ffeeac206ee9a2980b4605` | `c10fe1d4b86109cd1106cb112708261ce4373cf6f5e36535cbfd61cb87978ee6` |
| `EndpointHomology.lean` / 9 | `6a1306afe9fb0bfcb0d8b7e93669c3d2300eeaea5450481923466631a90fcdcb` | `e0a68d4b02d8bc76e84f362912a8c5d0c76ef230c7c2390e891c540d0e88211b` |
| `WitnessCommon.lean` / 12 | `f4f46b1ae32e0462e6ed1785f88df7a31ad6ed18607169c6738b3c652bfdd56b` | `94bbfc88964cc5d4bf9e32e6593b6da91f65bc6cffaf6d6c474089d317e1a902` |
| `WitnessThreeInput.lean` / 8 | `93fb9be39be291d20af30aeabcbe090f46534d5913677a01286cf29841aebd0e` | `fc12b93d966d83959fd66264db95a6fa75d9f28687d445d2b759ec645a7969bc` |
| `WitnessThreeNonzero.lean` / 34 | `c3ae12fc3ce2076c1af064c11248f11babae23698021ee21109aeafaa838bc17` | `61fdf23fcef7bd6f511756e1ccd8343d05db922426d14ec27468ede738e92f27` |

再現metadata `.tmp/g135/cycle6-validation.json`（SHA-256 `4ca4946b6efc7db2812563e4589a57ded68f96d4113d24476f75ece8cfa9ce18`）。
共通scan metadata `.tmp/g135/cycle6-scans.json`（SHA-256 `b29fe6f4fa87bb76edbe0a3bf328d87340dedc1f407d9d81234e73402206304e`）。


## Cycle 6 受理・merge同期

正式再実行1の新規独立数学A/B・LeanA/Bは全4本 `No major findings`、
中心/非中心0。rootが固定head `160a3087d20d2e9cf22de758359acb5df7ec2ecd` の
実体へacceptance-contractと全regression scenarioを再統合し、
六終了条件を `proof-obligation-discharged` と受理した。
初回Major revisionsの3findingは同じ原始W3正負表・owner公開API・説明で解消。
正式再実行1/2、直接対応確認ではない。

最終監査: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5297#issuecomment-6050868943
PR5297 merge commit `19b1d5a1d6d725fb2b11495e1f095dfc7f502e62`、2026-10-08T02:23:08Z。
Issue同期: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5290#issuecomment-6050883644
固定headのCI全8 SUCCESS（Lean37716401113、Tool37716401125）。
Research integrity実steps SUCCESS、Formal setup/build/kernel/premise実steps SKIPPED。
19対象focused・317宣言監査は前節のhash固定証拠と4本の独立照合で一致。
Research full/aggregate/全file loop/lake build、Formal実build/移植は未実施。
全GOALは `target-proof-checkpoint / completion_candidate:no`、Issue OPEN、
Formalは `unported (Research-proved)`。六条件の受理を全目標完了にしない。

## Cycle 7 selection（実装前固定）

```yaml
ledger_type: target_cycle_result
goal: G-135-aat-atlas-coefficient-fiber
cycle: 7
goal_blob_sha: cd5f3e684b7f390558796797874a1f16b52a6b18
base_oid: 19b1d5a1d6d725fb2b11495e1f095dfc7f502e62
tracking_issue: 5290
report_path: research/reports/G-135-aat-atlas-coefficient-fiber.md
selection:
  proof_state_ref: PR5297最終監査・Issue6050883644・report Cycle6受理
  proof_dag_predecessors: [C6実短完全列δと原補正代表, C5原a/V/B/D/HとΦ/Γ同型, C4原商双対/ε短完全列, 固定mathlib spectralObjectMappingCone/precomp/descShortComplex]
  milestone: GOAL B・exact-sequence§2の実carrier filtrationから低次数exact coupleと指定E1/E2およびd2=同じτ
  proof_obligations: [原carrier次元部分複体と双対filtration, 各graded原商と標準短完全列, native spectral objectとδの対応, exact couple全射と完全性, E1のP行とκstar, derived E2と独立d2, 同じτへの符号込み同定]
  exit_criteria:
    - 原carrier次元≤0/1/2の鎖部分複体を原carrier関手の次元と一致させ、双対減少F0/F1/F2/F3を構成
    - 各隣接filtrationの原商graded複体と次数別短完全列、同じ原微分を同定
    - filtration包含を標準CochainComplexへの関手としnative spectralObjectMappingConeへprecomp、商への実擬同型とδを同定
    - 実graded標準homology/ShortExactδから低次数exact coupleの全射とexactnessを構成
    - E1 q=0行と各d1を実Kan Pの全三次数/微分へ同定
    - E1(0,1)=全ΦH1、E1(1,1)=cok Bstar=dual ker B、同じd1=κstarを原代表と標準δで証明
    - derived coupleからE2(0,1)=R・E2(2,0)=H2Pとd2を独立生成し、同じτへ全代表・符号込み同定
  selection_reason: 標準連結射を原carrier filtrationのtransgressionへ接続し、Bの未接続構成義務を直接閉じる
  expected_result_type: proof-obligation-discharged
  lean_targets: [CarrierFiltration.lean, FilteredComplexes.lean, GradedShortExact.lean, FilteredSpectralObject.lean, LowExactCouple.lean, FirstPage.lean, DerivedTransgression.lean]
  risks: [carrier≤0のK0をL0へ置換しない, 任意suppliedfiltrationで原始構成を代替しない, native objectの存在だけでd1/d2接続を完了にしない, R/τをE2/d2として定義して構成義務を消さない, 符号と全代表を追う]
  unchecked: [全選定obligation実装前, C–Eと全W, final fresh4全目標監査]
```

carrier≤0の0次は元K′₀全体、1次は垂直辺像、2次は垂直面像である。
carrier≤1は元K′₀/元K′₁/全none面像、carrier≤2は元K′である。
L₀=垂直辺微分像は別対象として維持する。d₂はnative δとexactnessからの
持ち上げ商類として独立生成し、原補正代表で既存τへ同定する。
全終了条件が満たされるまで同じcycle内で実装と対象focused検証を反復する。

## Cycle 7 result proposal：原carrier filtrationのtransgression

原carrier関手の対象次元から生成した鎖部分複体とその双対減少filtrationを使う。
隣接商はすべて実包含の標準cokernelと同型であり、実短完全列から標準homologyの
exact coupleを作る。E₂とd₂はR・τから独立に構成し、原補正代表で同じτへ移す。

| 固定終了条件 | Lean証拠と原入力からの放電 | 状態 |
| --- | --- | --- |
| 1 原carrier次元と鎖部分複体／双対F⁰–F³ | `carrierDimension`、全辺・面の次元分類、`carrierChain1/2_*_eq_span`、`carrierChainInclusion`、`carrierBoundary_square`。`verticalRestriction1/2_kernel_iff`、`secondFiltration_kernel_iff`、`carrierChart/Edge/Face_*annihilator_iff`で非零・零次数の実annihilatorを照合 | 入力生成Lean証拠あり |
| 2 全隣接gradedと原微分／短完全列 | `first/second/thirdGraded_degreewise_shortExact`、`first/second/thirdGraded_shortExact`、各`GradedCokernelIso`。微分は原a/V、B双対、原F²への同じ制限 | 入力生成Lean証拠あり |
| 3 native spectral object・実商擬同型・δ | `filteredCarrierFunctor`と全三包含API、`carrierSpectralObject`、全triangle distinguished、各`GradedConeDesc_quasiIso`。`carrierSpectralObject_delta`、`*_delta_inr`、`first/secondNativeConnecting_shortExact`でnative δと同じSES δを全次数で接続。零始点inrのhomology同型は`zeroFiltration_inr_quasiIso`と`carrierSpectralObject_inr_homology_isIso` | 入力生成Lean証拠あり |
| 4 実exact couple全射と完全性 | `first/secondCoupleI/J/K`は同じ包含・射影の標準homology射と実SES δ。`first/secondCouple_exact_ij/jk/ki`で全隣接完全性。`firstPageDifferential_square`は実j/k完全性から生成 | 入力生成Lean証拠あり |
| 5 E₁ q=0行の実Kan P | `firstRowCoordinates0/1/2`の両方向同型、`firstRow_firstDifferential`と`firstRow_secondDifferential`。各逆像は原εの像＝annihilatorから生成し、δは標準`δ_eq`で計算 | 入力生成Lean証拠あり |
| 6 全Φ H¹／cok B*／κ* | `firstGradedHomologyFiberEquiv`、`secondGradedHomologyDualEquiv`、両代表API、`firstPageDifferential_kappaStar`。κ*をd₁の定義に使わず、原zDを標準δと実jで読む | 入力生成Lean証拠あり |
| 7 独立E₂／d₂とτ | `DerivedFiberPage`、`DerivedHorizontalPage`、`derivedLift_exists`、`derivedClass_eq_of_lift`、`derivedSecondDifferential`。`derivedFiberREquiv`、`derivedHorizontalH2Equiv`で指定R/H²Pへ移し、`derivedSecondDifferential_tau`が全R・全Aで正符号の同じ商類を返す | 入力生成Lean証拠あり |

受理を求めるspineは、上表の構成、標準cokernel／擬同型、全隣接完全性、E₁/E₂座標、
`firstPageDifferential_kappaStar`、`derivedSecondDifferential_tau`である。
carrierの基底span照合、owner公開API、零延長代表射、各`_apply/_val`はその依存APIであり、
それ自体を別のtarget達成として数えない。

```yaml
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: 原carrier filtrationから実graded/SES/native spectral δ/exact coupleを生成し、全E1行座標と実d1、独立E2/d2=τを同じ原入力・全Aで接続
  exit_criteria_status: [1原carrier鎖と全双対次数あり, 2全三隣接商と次数別SESあり, 3native objectと実商擬同型およびδ対応あり, 4全i/j/kと隣接完全性あり, 5全P行と二微分あり, 6全fiber座標とκstar微分あり, 7独立E2/d2と全代表のτ同定あり]
  split_reason: none
  completion_candidate: no
  lean_artifacts: [CarrierFiltration, CarrierChain, FilteredComplexes, FiltrationAnnihilators, GradedShortExact, SecondGradedComplex, ThirdGradedComplex, FilteredSpectralObject, ZeroFiltrationCone, NativeSpectralConnecting, LowExactCouple, ThreeShortExactConnecting, FirstPageFiber, FirstPageRow, FirstPageVanishing, DerivedPageCoordinates]
  evidence: [上表と全宣言一覧・focused出力hash]
  claim_mapping:
    theorem_names: [firstPageDifferential_kappaStar, firstRow_firstDifferential, firstRow_secondDifferential, derivedSecondDifferential_tau]
    source_labels: [GOAL B, exact-sequence§2]
    conjuncts: [原carrier filtration, 全graded/SES, native δ接続, 指定E1/E2とd1/d2]
    undischarged_assumptions: []
    acceptance_point: 七終了条件の入力生成証拠を同じcycleで全て固定し正式PR監査へ渡す
    port_status: unported
  whole_goal_status: target-proof-checkpoint
  remaining_goal: [C診断保存と同じ三錐, D全Law/台自然性とG134保存接続, E原始有理行列の有限判定, W全指定表・診断・比較・二label/空台, final fresh4全GOAL監査]
audits:
  premise_delta:
    discharged: [carrier部分複体と原微分square, 原annihilator全次数, 各graded全射/核/商, 全SES完全性とnative δ対応, 全P/fiber座標逆像, d1とκstar一致, derived lift存在と曖昧さのk像, d2全代表とτ一致]
    remaining: [選定cycleにはなし・全GOALのC/D/E/Wは上記remaining_goal]
  certificate_provenance:
    discharged: [原carrier関手と原a/V/B/D/H, 実εの像producer, 元filtration包含, mathlib標準SES/δ/cone]
    unresolved: []
  proof_use:
    used: [原incidenceとcarrier分類, 原微分制限, 既受理ε像/κ/τ代表API, native短完全性・δ_eq・quasiIso]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  blocking_findings: [正式PR独立査読は未実施]
  next_obligation: Cの実H1η/ε/Tと核・余核短完全列、診断加法式・保存条件
```

material premiseの本文由来はT0の有限支持原始比較Mと任意A、ℚ係数である。
filtration、graded、完全性、P/fiber座標、E₂、d₂は入力fieldに移さず生成する。
汎用`threeShortExact_connecting_representative*`の短完全性・lift等式は方向仮定であり、
全適用箇所で同じ原filtrationとcounitから生成した証拠を渡す。
`derivedSecondDifferential`の持ち上げ選択は存在producerと同じk像による商独立性を伴う。
全体の有限計算アルゴリズムはEの未完obligationとして残し、この選択構成を代替にしない。
新しいProp述語・certificate構造の導入はなく、Mono/QuasiIso/IsIsoは既存述語の生成instanceである。

19対象fileのfocused checkは警告・エラーなし、全319 source宣言のprint/auditは標準公理のみ。
新規宣言は250、既存69も同じfileで再監査した。各fileのsource順と#print・log・下記一覧を照合する。
Research aggregateはimport登録の静的確認だけでelaborateしていない。
本体`lake build`、Research全体build、Formal移植、final fresh4全GOAL監査は未実施。

<!-- cycle7-generated-evidence -->

| file | 全宣言（source/print/logの同順序） |
| --- | --- |
| `RawBlocks.lean` | `cellProjection`, `cellProjection_apply`, `cellInclusion_apply`, `cellInclusion_apply_notmem`, `cellProjection_cellInclusion`, `cellProjection_complementInclusion`, `cell_recombination`, `cellRecombination`, `cellDecomposition`, `cellDecomposition_fst`, `cellDecomposition_snd`, `HorizontalEdge`, `HorizontalFace`, `edgeBlockEquiv`, `verticalEdgeProjection`, `horizontalEdgeProjection`, `horizontalEdgeInclusion`, `horizontalEdgeInclusion_single`, `horizontalFaceInclusion`, `verticalEdgeBoundary`, `verticalEdgeBoundary_apply`, `verticalEdgeBoundary_single`, `horizontalEdgeBoundary`, `mixedVerticalBoundary`, `mixedHorizontalBoundary`, `mixedHorizontalBoundary_apply`, `horizontalFaceBoundary`, `mixedVerticalBoundary_apply`, `horizontalFaceBoundary_apply`, `horizontalFaceInclusion_single`, `verticalEdgeProjection_inclusion`, `verticalEdgeProjection_horizontal`, `horizontalEdgeProjection_inclusion`, `horizontalEdgeProjection_vertical`, `verticalEdgeProjection_single`, `verticalEdgeProjection_horizontal_single`, `edgeBlock_recombination`, `mixedBoundary_recombination`, `verticalEdgeBoundary_comp_verticalBoundary`, `mixedBoundary_square`, `horizontalFace_edge_mapped`, `horizontalFace_vertical_zero`, `horizontalFaceBoundary_inclusion`, `horizontalEdgeBoundary_comp_horizontalFaceBoundary`, `horizontalEdgeProjection_single`, `horizontalEdgeProjection_vertical_single`, `degenerateFaceSplitEquiv`, `faceBlockEquiv`, `faceBlockEquiv_vertical`, `faceBlockEquiv_mixed`, `faceBlockEquiv_horizontal`, `mixedFaceProjection`, `mixedFaceProjection_apply`, `mixedFaceProjection_inclusion`, `mixedFaceProjection_vertical`, `verticalFaceProjection`, `verticalFaceProjection_apply`, `verticalFaceProjection_inclusion`, `verticalFaceProjection_mixed`, `degenerateFace_recombination` |
| `CarrierFiltration.lean` | `incDimension`, `carrierDimension`, `carrierDimension_chart`, `carrierDimension_edge_zero_iff`, `carrierDimension_edge_le_one`, `carrierDimension_face_zero_iff`, `carrierDimension_face_le_one_iff`, `carrierDimension_le_two`, `carrierChain0`, `carrierChain1`, `carrierChain2`, `carrierChain2_boundary_le`, `carrierChain1_boundary_le`, `carrierChain1_mono`, `carrierChain2_mono`, `freeRange_eq_span`, `carrierEdgeBasis`, `carrierFaceBasis`, `carrierChain1_zero_eq_span`, `carrierChain2_zero_eq_span`, `carrierChain2_one_eq_span`, `freeChain_eq_span`, `carrierChain1_one_eq_span`, `carrierChain2_two_eq_span` |
| `CarrierChain.lean` | `carrierBoundary1`, `carrierBoundary2`, `carrierBoundary1_apply`, `carrierBoundary2_val`, `carrierBoundary_square`, `carrierDegreeObject`, `carrierDegreeObject_out`, `carrierDegreeDifferential`, `carrierDegreeDifferential_square`, `carrierChain`, `carrierDegreeInclusion`, `carrierDegreeInclusion_out`, `carrierDegreeInclusion_comm`, `carrierChainInclusion`, `carrierChainInclusion_f`, `carrierChainInclusion_mono` |
| `FilteredComplexes.lean` | `verticalRestriction1`, `verticalRestriction2`, `verticalRestriction1_apply`, `verticalRestriction2_apply`, `verticalRestriction1_kernel_iff`, `verticalRestriction2_kernel_iff`, `secondFiltration_kernel_iff`, `verticalRestriction_comm1`, `firstFiltrationDifferential`, `firstFiltrationDifferential_val`, `firstFiltrationComplex`, `secondFiltrationComplex`, `zeroFiltrationComplex`, `firstFiltrationInclusion`, `secondFiltration_le_first`, `secondFiltrationInclusion`, `secondFiltrationInclusion_f0`, `secondFiltrationInclusion_f1`, `zeroFiltrationInclusion`, `firstFiltrationInclusion_f0`, `firstFiltrationInclusion_f1`, `firstFiltrationInclusion_f2`, `secondFiltrationInclusion_f2_val` |
| `GradedShortExact.lean` | `firstGradedComplex`, `verticalRestriction_comm0`, `firstGradedProjection`, `firstGradedProjection_f0`, `firstGradedProjection_f1`, `firstGradedProjection_f2`, `verticalRestriction1_surjective`, `verticalRestriction2_surjective`, `firstGraded_standard_zero`, `firstGradedShortComplex`, `firstGraded_degreewise_shortExact`, `firstGraded_shortExact`, `firstGradedCokernelIso` |
| `SecondGradedComplex.lean` | `horizontalRestriction1`, `mixedRestriction2`, `horizontalRestriction1_apply`, `mixedRestriction2_apply`, `mixedRestriction_comm1`, `secondGradedComplex`, `secondGradedProjection`, `horizontalCochainLift`, `horizontalCochainLift_dual`, `horizontalCochainLift_spec`, `horizontalRestriction1_surjective`, `horizontalRestriction1_injective`, `mixedCochainLift`, `mixedCochainLift_spec`, `mixedRestriction2_surjective`, `mixedRestriction2_second`, `mixedRestriction2_kernel`, `secondFiltrationInclusion_f2_injective`, `secondGradedProjection_f0`, `secondGradedProjection_f1`, `secondGradedProjection_f2`, `secondGraded_standard_zero`, `secondGradedShortComplex`, `secondGraded_degreewise_shortExact`, `secondGraded_shortExact`, `secondGradedCokernelIso` |
| `ThreeShortExactConnecting.lean` | `threeShortExact_connecting_representative`, `threeShortExact_connecting_representative_zero` |
| `FilteredSpectralObject.lean` | `zeroExtensionMap_mono_of_injective`, `firstFiltrationInclusion_standard_mono`, `secondFiltrationInclusion_standard_mono`, `zeroFiltrationInclusion_standard_mono`, `filteredCarrierFunctor`, `filteredCarrierFunctor_obj_zero`, `filteredCarrierFunctor_obj_one`, `filteredCarrierFunctor_obj_two`, `filteredCarrierFunctor_obj_three`, `filteredCarrierFunctor_map01`, `filteredCarrierFunctor_map12`, `filteredCarrierFunctor_map23`, `carrierSpectralObject`, `carrierSpectralObject_triangle_distinguished`, `firstGradedConeDesc`, `firstGradedConeDesc_quasiIso`, `secondGradedConeDesc`, `secondGradedConeDesc_quasiIso`, `firstGradedCone_connecting`, `secondGradedCone_connecting` |
| `LowExactCouple.lean` | `firstCoupleI`, `firstCoupleJ`, `firstCoupleK`, `secondCoupleI`, `secondCoupleJ`, `secondCoupleK`, `firstCouple_exact_ij`, `firstCouple_exact_jk`, `firstCouple_exact_ki`, `secondCouple_exact_ij`, `secondCouple_exact_jk`, `secondCouple_exact_ki`, `firstPageDifferential`, `secondPageRowDifferential`, `firstPageDifferential_square`, `firstCoupleK_apply`, `secondCoupleJ_apply`, `secondCoupleI_apply`, `secondCoupleK_apply`, `firstPageDifferential_apply`, `DerivedFiberPage`, `DerivedHorizontalPage`, `derivedLift_exists`, `derivedLift`, `derivedLift_spec`, `derivedClass`, `derivedClass_eq_of_lift`, `derivedSecondDifferential`, `derivedSecondDifferential_apply` |
| `FirstPageFiber.lean` | `firstGradedHomologyFiberEquiv`, `firstGradedHomologyFiberEquiv_mk`, `secondGradedHomologyDualEquiv`, `secondGradedHomologyDualEquiv_mk`, `verticalRestriction1_corrected`, `firstFiberLiftDifferential`, `firstFiberLiftDifferential_val`, `firstCoupleK_representative`, `mixedRestriction2_firstFiberLift`, `firstPageDifferential_representative`, `firstPageDifferential_kappaStar`, `derivedFiberREquiv`, `derivedFiberREquiv_val` |
| `FirstPageRow.lean` | `firstRowZeroMap`, `firstRowZeroMap_val`, `firstRowZeroMap_injective`, `firstRowZeroMap_surjective`, `firstRowZeroEquiv`, `firstFiltrationEvaluation1`, `firstFiltrationEvaluation1_val`, `secondFiltrationEvaluation2`, `secondFiltrationEvaluation2_val`, `firstFiltrationEvaluation1_d1`, `firstRowOneMap`, `firstRowOneMap_val`, `firstRowOneMap_injective`, `firstRowOneMap_surjective`, `firstRowOneEquiv`, `secondFiltrationEvaluation2_injective`, `secondFiltrationEvaluation2_surjective`, `secondFiltrationEvaluation2Equiv`, `secondGraded_boundaryToCycles_range_zero`, `firstRowCoordinates0`, `firstRowCoordinates1`, `firstRowCoordinates2`, `firstRowCoordinates0_apply`, `firstRowZeroLiftDifferential`, `firstRowZeroLift_spec`, `firstRowZero_connecting`, `firstRowCoordinates1_apply`, `firstRowCoordinates2_apply`, `firstRow_secondDifferential`, `firstRow_firstDifferential` |
| `DerivedPageCoordinates.lean` | `derivedHorizontal_range_coordinates`, `derivedHorizontalH2Equiv`, `derivedHorizontalH2Equiv_mk`, `correctedEdgeCochain_sub`, `correctedDerivedLift`, `derivedFiberREquiv_corrected`, `derivedSecondDifferential_tau` |
| `ThirdGradedComplex.lean` | `thirdGradedComplex`, `thirdGradedProjection`, `thirdGraded_standard_zero`, `thirdGradedShortComplex`, `thirdGraded_degreewise_shortExact`, `thirdGraded_shortExact`, `thirdGradedCokernelIso`, `thirdGradedConeDesc`, `thirdGradedConeDesc_quasiIso` |
| `ZeroFiltrationCone.lean` | `zeroFiltrationDegree_isZero`, `zeroFiltration_isZero`, `zeroFiltrationMap_eq_zero`, `zeroFiltrationConeShortComplex`, `zeroFiltrationConeShortExact`, `zeroFiltrationConeDesc`, `zeroFiltrationConeDesc_quasiIso`, `zeroFiltration_inr_desc`, `zeroFiltration_inr_quasiIso` |
| `NativeSpectralConnecting.lean` | `carrierSpectralObject_delta`, `carrierSpectralObject_delta_inr`, `carrierSpectralObject_homology_connecting`, `carrierSpectralObject_omega`, `carrierSpectralObject_inr_homology_isIso`, `firstNativeConnecting_shortExact`, `secondNativeConnecting_shortExact` |
| `FirstPageVanishing.lean` | `homology_isZero_of_degree`, `zeroExtension_homology_isZero_out`, `secondGraded_homology_zero_isZero`, `thirdGraded_homology_isZero`, `graded_homology_isZero_negative` |
| `FiltrationAnnihilators.lean` | `cochain_zero_iff_annihilate_all`, `carrierChart_annihilator_iff`, `carrierEdge_one_annihilator_iff`, `carrierEdge_two_annihilator_iff`, `carrierFace_two_annihilator_iff` |
| `HomologyRepresentatives.lean` | `shortComplex_liftCycles_class`, `zeroExtension_liftCycles_H1`, `zeroExtension_liftCycles_H2`, `zeroExtension_liftCycles_H0`, `elementArrow`, `elementArrow_one`, `elementArrow_comp`, `elementArrow_zero`, `zeroExtension_liftCycles_H1_apply`, `zeroExtension_liftCycles_H2_apply`, `zeroExtension_liftCycles_H0_apply` |
| `EndpointHomology.lean` | `oldZeroShort`, `oldTwoShort`, `zeroExtensionZeroScIso`, `zeroExtensionTwoScIso`, `oldH0Iso`, `oldH0Iso_hom_comp`, `oldH2Iso`, `oldH2Iso_hom_comp`, `oldH0Equiv`, `oldH2Equiv` |

| file / declarations | source SHA-256 | focused output SHA-256 |
| --- | --- | --- |
| `RawBlocks.lean` / 60 | `c87584a49ddd341aa965b4f16d53ca8499487e2f4023f18ef4484c6218e73b07` | `2a9d9d1ce5605b678a2ad021ccfd159e72ef0148b17d240261a7e7f9bd8b53ea` |
| `CarrierFiltration.lean` / 24 | `a33d48fa4a0330baeb1f5b8f8c3f88e6cd6feccc487a3283c949789f85d7475f` | `a2555b006a0d1aa378c8fcdfe4ec7cbdaf7cce00f333d86a18356e089838b4e5` |
| `CarrierChain.lean` / 16 | `63a081a33a2bfe2dfe07f6d9e0e9d76d8d782e4625316a20b668580d16afa18b` | `5c511de25f6fe7b4cf5fd40edc5606e5428b92fcd27d74a4c8bcec1341ad6f95` |
| `FilteredComplexes.lean` / 23 | `a652af61635e72fdc07477e8c503d4ab68860bfa29f7159c40fa33562e098ab1` | `7c0fd3ca6ae6d2f927cbe7ad5f09e6ffb0c829c8a91f9073385b0a8b7a0d66be` |
| `GradedShortExact.lean` / 13 | `885a46faabae0846ea5b98ff5339436d062e66b146fbd31e083955cfb73bc57f` | `1e4b9bd385276b2a2dc7c25518a0a0102830a67d54435d95093da806e23b8c9b` |
| `SecondGradedComplex.lean` / 26 | `59aea37b2ff35539c81df801a52ed37d3ad8afe4e6c1616453c89b0b2cb022eb` | `4161df0595de566d7db01c4b355fb3b8896b463359dd36e2bc3c8d481a0ce206` |
| `ThreeShortExactConnecting.lean` / 2 | `8a0038a83ebaa05ccde96361d64ccf1fc824b9b9acf322e0e1f666fa0197ecbe` | `d9dbcc5016dcaea4ae1f1c7e27d7387222ffadbade4de3ebf79be40e76187d9f` |
| `FilteredSpectralObject.lean` / 20 | `ac1df59d824d9807b0dc565529d1d4c8032388c8dd5f2076e2095d4ea5b2feba` | `1d511bf589198d38d27926fab71e9b89d999636b56f7d727a80950812538bf83` |
| `LowExactCouple.lean` / 29 | `cc63b4ddd98b9eff268daed9eb4c8e5c4c5ef1d7657904705d14e8d9c9c29292` | `bc3a9d7ecab6a0a9840ecccb6bf3cf2d82823241055cb018cec2cc74c6e24bb1` |
| `FirstPageFiber.lean` / 13 | `e27b4400ed2350013214164cce305190a01a9d1e45c517a6b4a191c7ca1bfc72` | `6524193bfc0c2a8e4c807cfebee9fe1a5add30ee588d13b9cd613875156f1b07` |
| `FirstPageRow.lean` / 30 | `d0b0e5ff3d462deb70e094d3c6ec9fb872646ad1f06cc3d88e04da4b069dfce8` | `a4571daacbb266762a647df2671827dc1b4cd0790c83ffd355d6041fbdef6ece` |
| `DerivedPageCoordinates.lean` / 7 | `eea1afc5b0d96c1190494524834a9aa92418916d8b4a41256e353c66b69122ed` | `0194d80aaec99b13762442fb52924b0d96d79ab776c850bdedf317e8cce69ae4` |
| `ThirdGradedComplex.lean` / 9 | `8ac84f61eef8e7508771c6190c63abcf3038bf7757a3a9bf8264c42f475ad863` | `57561b0714f5d677f2e7b32f67b54a9337409e09d478b15a888b146d6cc23c44` |
| `ZeroFiltrationCone.lean` / 9 | `361a1e1ce64ab54b9c16574ce31670e46dfe0d31cd21684e37798e480383a2a2` | `c3a4ba0723bf07d52a6e049a32498f4096871b6a9690a4f3949ab2fdb0b5f08d` |
| `NativeSpectralConnecting.lean` / 7 | `ff328793d7c421f554b9f59522fa5f943b648ec770a106ee19b9c16dee764003` | `ba15858e6d29fd91a23faf5506225c4a6e57b466a3833ae47fc0d4a0a2e86ae1` |
| `FirstPageVanishing.lean` / 5 | `8adc6a52edc0f0556708a7f5c5835571243fa36fc5c3bc9ec9d216c183359f5a` | `69fc9758e3ed442883bc406bebe745e7fc96055a9b1e969692effafb19ba18f5` |
| `FiltrationAnnihilators.lean` / 5 | `3abf7f5d3d0da9281da84bb5e41daec7fb1bf54de9f5163df44b011f6137e727` | `5d895a6f4e6e8c8fd04df78766647fafa6e428baffa3e0bce92e043b8e0d58b3` |
| `HomologyRepresentatives.lean` / 11 | `cee43137f7be42212ff7a02f9f0ff48a0541d5ea0a3f5ebb2c9a306dcae5c614` | `175aa9e4212147a2674886a7d10268ba52d65b29b3a22a094b38ff21bac6cd88` |
| `EndpointHomology.lean` / 10 | `1deb845209adcd269ea6e2a0113af970a747b20af890a6f1107eb2eb5e916e4b` | `386b43aeeb78b2a855af9fccfba2f538023c3a6bb547ebd6889ac0afbedbb9ef` |

再現metadata `.tmp/g135/cycle7-validation.json`（SHA-256 `a033386e36fdf71d9ef91a0be914cbf6d6baa22641eb66239a472e0706c01c36`）。

### Cycle 7 初回査読とF1対応

初回固定head `93498c53f43e697d227ef0a92211eaaed04b62b7`、標準review-prの
math-lean-review新規四本は数学A/BがNo major findings、LeanA/BがMinor issues。
中心findingは0、二票の非中心指摘は同じF1として統合した。
初回統合監査はPR5298のissuecomment-6051692210。

F1はcorrectedEdgeCochain_subが別ownerの二定義をchangeで展開する品質問題。
名指しされたhorizontalCochainLift_dualをSecondGradedComplexへ追加し明示printへ登録、
下流はこれと既存correctedEdgeFunctional_applyおよびLinearMap.extを用いる。
既存statement、def/instanceの値、import方向、台帳statusは変更していない。
変更二fileのfocusedを再実行し、全319宣言（新250）とsource/print/log順を更新した。
追加補題を含む公理監査は標準公理のみ。単一独立直接対応の資格・解消確認へ渡す。
formal_rerunsは0、内容の受理判定は修正後の監査コメントで行う。
全GOALは引き続きcompletion_candidate:no、C–E/Wと別final fresh4が残る。
共通scan metadata `.tmp/g135/cycle7-scans.json`（SHA-256 `46fee9a224c38f933162785156440cb6031c70dce0b700fdbeb5b6212d3465e9`）。

## Cycle 7受理・main同期

PR #5298の受理headは`30286d188076c362855ae8fb24953931b47e957b`、
mergeは`95b8bdd65d9192044d386f2068aecba09d7f7c65`（2026-10-08T03:50:32Z）。
初回監査issuecomment-6051692210、最終内容監査とroot acceptanceはissuecomment-6051786877。
新規四本の中心finding0、同一非中心F1は名指しowner APIとproof修正を新規単一直接対応で解消、
資格あり・新findingなし。正式rerunsは0。七終了条件をproof-obligation-dischargedとして受理した。

受理head CI全8件成功、Lean run37724096592・Tool run37724096561。
Research integrity必要実steps成功、Formal setup/cache/build/kernel/premise実stepsはSKIPPED。
19対象単一focused、319宣言（新250）source/print/log/report順一致・標準公理のみ。
Issue #5290同期はissuecomment-6051800185、OPENのまま。
専用worktreeのみorigin/mainの実mergeから次branchへ進めた。保護した別worktreeを変更していない。
GOAL/design/Formalは不変。全GOALはtarget-proof-checkpoint / completion_candidate:no。

## Cycle 8 selection（実装前固定）

```yaml
ledger_type: target_cycle_result
goal: G-135-aat-atlas-coefficient-fiber
cycle: 8
goal_blob_sha: cd5f3e684b7f390558796797874a1f16b52a6b18
base_oid: 95b8bdd65d9192044d386f2068aecba09d7f7c65
tracking_issue: 5290
report_path: research/reports/G-135-aat-atlas-coefficient-fiber.md
selection:
  proof_state_ref: Cycle7受理・Issue5290 issuecomment-6051800185・原五項列
  proof_dag_predecessors: [C3実η/ε/u因子化, C5原κ/R, C6実五項列とτ, C7原filtration同定, G133六項列/旧標準H1同型/欠損API]
  milestone: Cの同じ実比較の核・余核短完全列から旧blockDefectの加法式と保存条件を得て、G133相殺零を同じ二射へ特殊化する
  proof_obligations: [原標準H1η/Tと同じεによる因子化, kerTとkeraの元保存同型, cokεとkerτの原制限による同型, 旧G133第四/第五射を実cokTへ輸送するSES, 旧診断二成分とτ/κstarの加法式, 同じ実比較の保存必要十分とχ零]
  exit_criteria:
    - 1原η/独立uからa/Tを生成し標準H1の射等式T=H1εcompaと旧H1比較の可換式を証明
    - 2同じ原coarseH1の元を保つ両方向kerT≃keraと公開評価式を構成
    - 3cokH1ε≃kerτを同じfiberRestrictionH1の核像完全性から生成し全商代表の値を証明
    - 4coka→cokT→kerτの全実写像と両代表式・単射/完全性/全射を構成しG133第四/第五射に接続
    - 5同じ既存aSubnerveComparisonHom.h1MapのblockDefect第一成分と設計§4の二自然数加法式を証明し全PhiH1有限和に戻す
    - 6同じ旧診断J=0 iff aBijective and τInjectiveを両方向で証明し同じG133χの始域零/写像零と六項加法式特殊化を示す
  selection_reason: Bの入力生成五項列を固定Cの実診断へ直接接続し、後続局所条件・G134保存・W診断の共通producerを作る
  expected_result_type: proof-obligation-discharged
  lean_targets: [DefectMaps, DefectShortExact, DefectDiagnostics]
  risks: [標準H1と旧商の同じ射, cokTへの等号輸送と全代表, τとχの異なる始域, 全Aと全混在M, 未計算rankをEアルゴリズムと混同しない]
  unchecked: [上記六条件の構成/検証/正式独立PR監査, 全GOALの局所条件/pureC3prime/G107/三錐/D/E/W/別finalfresh4]
```

局所係数・pure C3′とG107同例、三錐は別の依存群として後続に保持する。
今回の到達点をC全体または全G-135の完了とは扱わない。終了条件を満たすまで同cycleで実装・検証を反復する。

## Cycle 8 result proposal：同じ実診断の係数・fiber分解

原ηと独立uの標準H¹からa/Tを生成し、実εのH¹単射性と原五項列を接続した。
G-133の同じ二射の第四・第五射を因子化等号で独立Tの余核へ移し、
原fiber制限によるcokH¹ε≃kerτを合成する。χの始域はkerH¹εであり、Rとは異なる。

| 固定終了条件 | 実Lean証拠・同じ射と前提放電 | 状態 |
| --- | --- | --- |
| 1 実a/Tと全H¹因子化・旧商接続 | `unitH1`、独立`directH1`、所有評価/標準等式、`directH1_factor`。原u全Hom因子化とzeroExtensionMap_comp/homologyMap_compを使用。`directH1_old`は同じ旧H¹商の自然性 | 入力生成証拠あり・修正後正式監査待ち |
| 2 元保存kerT≃kera | `directH1_kernel`は実ε単射性による同じcoarseH¹内の部分空間等号。`directKernelUnitEquiv`とvalは同じ元を両方向で保つ | 入力生成証拠あり・修正後正式監査待ち |
| 3 実cokε≃kerτ | `fiberRestriction_kernel/range`は原五項列の全隣接完全性。`evaluationCokernelTauKernelEquiv`はquotKerEquivRangeと核像等号輸送。全mk_valは同じ原制限 | 入力生成証拠あり・修正後正式監査待ち |
| 4 実余核SESの全写像 | `compositeDirectCokernelEquiv`は独立T因子化の等号、同じ代表の順逆mk。`coefficientCokernelInclusion`/`totalCokernelFiberProjection`は同じG133第四/第五射と原制限同型。全代表、単射/完全性/全射を`coefficientCokernel_shortExact`へ集約 | 入力生成証拠あり・修正後正式監査待ち |
| 5 旧診断二成分と自然数二加法式 | `directH1_defect`は標準H¹と既存商の同じblockDefect。`coefficient_kernel_dimension`、`coefficient_cokernel_dimension`、`coefficient_cokernel_kappa_dimension`は同じ核/商同型、G133次元式とτ/κ*のrank-nullity、全Φ有限Pi和から得る。整数表示も同じ第一加法式から導出 | 入力生成証拠あり・修正後正式監査待ち |
| 6 保存必要十分と同じG133特殊化 | `evaluationH1_surjective_iff`は実五項完全性の両方向。`directH1_bijective_iff`と`coefficient_zeroDefect_iff`は同じ独立T/J。零Jから原aの線形同型とkerτ零を生成。`evaluationH1_kernel`、`coefficientCancellation_zero`、二`coefficientSixTerm_*_dimension`が同じ二射の始域零と六項式特殊化。`witnessThree_cancellation_zero_and_tau_ne_zero`は同じ原W3でχ零/τ非零を併記 | 入力生成証拠あり・修正後正式監査待ち |

受理spineは実a/T、核同型、後段余核同型、実余核SES、旧診断加法式、保存必要十分、
原零診断からa同型/kerτ零を生成するproducer、同じ二射の相殺零とW3非零τとの区別である。
所有計算APIと部分空間等号輸送はその依存APIであり、別targetとして数えない。

### Cycle 8前提・provenance・proof-useと依存

- 本文由来の入力は任意原T0のM・任意A・ℚ。原支持nerveの有限fieldから三項・標準homology・部分空間/商・全Φの有限次元性を得る。新しい連結性/forest/pure/単射/全射/τ消滅仮定を一般入力へ追加しない。
- 実η/ε/u因子化は受理済C3の`aSubnerveComparisonHom_factorization`を同じM/Aへ適用。標準H¹を定義するとき独立uを使い、結論T因子化からTを定義しない。
- εの単射と二つの核像完全性は受理済C6の実SES・五項列から生成されたproducer。核等号、cokε≃kerτ、保存両方向へ実使用し、結論をcertificate fieldへ保持しない。
- G133六項列・第四/第五射・次元式は任意二線形射の一般定理。今回の適用では同じ原a/H¹ε、原ε単射性から生成したχ零、実T因子化等号を渡す。χの始域零も入力ではなく出力である。
- `sameSubmoduleEquiv`の等号は一般APIでは方向前提、具体適用では原五項完全性または原ε単射性で放電する。標準商と同じ元の輸送を両方向で保つ。
- 零Jを仮定する`unitH1EquivOfZeroDefect`と`tauKernel_eq_bot_of_zeroDefect`は保存定理の方向特殊化。一般必要十分式ではJ/τ/aの条件を隠れた入力として受け取らない。
- W3の既受理同じ入力`WitnessThree.M`と`connectingTau_ne_zero`を使用し、新しいMや供給τ非零に置換しない。全W3診断・Law・錐をこの一条項で完了表示しない。

依存DAGは原M/A → 受理済P/η/ε/u/原五項列 → 実a/g/Tと核像 → 原商同型/第四第五射 →
余核SES → 同じ旧blockDefectと保存必要十分。τとκ*のrankは同じ原定義に対するrank-nullity。
Eの入力生成有理行列アルゴリズムは未完義務として保持し、この次元式を代替にしない。

G133再利用の受理refはPR5269固定head`74cb93564070661509ac0c2f842596e63d0957fa`の
標準監査issuecomment-6007458427・全GOAL認定issuecomment-6007700344、merge`2e0f452c97af56ea4fe2db1f9ca134630d872c58`。
`DefectSequence`、`ComparisonHomology`、`ConeExactSequence`は設計参照版からbyte変更なし。
`ZeroExtension`は受理済C6の所有公開API/明示print追加があるが、今回使用する原zeroExtensionMap_comp、
oldH1Equiv/naturality、有限性producerのstatementとbodyは不変。追加箇所も現sourceで確認し、C6監査6050868943へ対応させる。
C3実因子化はPR5294監査6046087706、C5原κ/RはPR5296監査6049620284、
C6実五項列とW3はPR5297監査6050868943の現使用版を同じM/Aで追う。
固定mathlib8f9d9cff6bd728b17a24e163c9402775d9e6a365/Lean4.28.0の
quotKerEquivRange・quotEquivOfEq・homologyMap_comp・finrankとFinitePiの適用条件を照合する。

```yaml
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: 同じ原η/ε/独立uの標準H1と旧商を接続し、実核/余核SES・診断加法式・保存必要十分・G133χ零を全M/Aで生成
  exit_criteria_status: [1実a/T因子化と旧商可換あり, 2元保存核同型あり, 3原制限cokε同型あり, 4全実余核SESあり, 5同じ旧Jの二加法式あり, 6両方向保存条件と同じ六項特殊化あり]
  split_reason: none
  completion_candidate: no
  lean_artifacts: [DefectMaps, DefectShortExact, DefectDiagnostics]
  evidence: [上表・全宣言一覧・source/focused出力hash]
  claim_mapping:
    theorem_names: [coefficientCokernel_shortExact, coefficient_kernel_dimension, coefficient_cokernel_dimension, coefficient_cokernel_kappa_dimension, coefficient_zeroDefect_iff, witnessThree_cancellation_zero_and_tau_ne_zero]
    source_labels: [GOAL C, exact-sequence§4の診断一般式, exact-sequence§5のG133相殺零]
    conjuncts: [同じ実核/余核, 全原制限とG133第四/第五射, 旧blockDefect, 全保存方向, 同じχとτの区別]
    undischarged_assumptions: []
    acceptance_point: 六固定終了条件の証拠を同cycleで固定し標準PR独立監査へ渡す
    port_status: unported
  whole_goal_status: target-proof-checkpoint
  remaining_goal: [C局所係数/pureC3prime/G107同例と三錐, B/E全Aの有限消滅判定, D全Law/台自然性/G134接続, E原始有理行列計算法, W全指定例の全評価と二label/空台, 別finalfresh4]
audits:
  premise_delta:
    discharged: [実H1因子化, 原核同型/商同型, 実余核SES完全性と両端, 同じ旧J, 全Phi有限和, 保存両方向, 原相殺零]
    remaining: [選定cycleにはなし・全GOALのremaining_goal]
  certificate_provenance:
    discharged: [原P/η/ε/独立u, 原五項列, G133同じ二射の六項列, 原W3の非零τ]
    unresolved: []
  proof_use:
    used: [原因子化, 実ε単射/五項完全性, 旧H1自然性/欠損, 同じ商と全代表, 実rank-nullity]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  blocking_findings: [初回非中心F1/F2修正後の新規四本正式再査読は未実施]
  next_obligation: C局所係数からη同型/診断保存・pureC3prime全Aと同じG107旧C3非必要性例
```

### Cycle 8初回独立査読・全finding修正

PR #5299初回固定headは`0b7f329b0bedeb4a9eb6a0c712e378ea7f88d86f`、
標準review-prから新規数学2本・Lean2本へ委譲し、監査はissuecomment-6052163572へ固定した。
数学AはNo major findings、数学BはMinor issues非中心1、LeanA/BはMinor issues非中心各2、中心findingは四票とも0。
重複を除く全findingはF1/F2の二件で、実装フェーズへまとめて戻した。
F1の`sameSubmoduleEquiv`は公開signatureと原始元の順逆保存を維持し、固定mathlibの
`LinearEquiv.ofEq`と`coe_ofEq_apply`を構成/計算へ直接使用する。同じcompiler生成congr_simpも監査する。
F2の主`coefficientCokernel_exact`は二つの既存所有apply APIを使う証明へ改め、定義の本体展開を除いた。
F1はdef本体変更を含むため、共有review-protocolに従い直接対応資格なしと判定した。
数学statement/量化/一次仕様の変更はないが、修正後headで新規四本の正式再実行1を行う。
全六終了条件の内容合格とroot acceptanceはその再査読後に判定し、初回Needs changesから合格を合成しない。
初回同headのCI8件成功、Lean run37726365506/Tool run37726365443。
Formal setup/cache/build/kernel/premise実stepsはSKIPPED。修正後CIは別に確認する。

### Cycle 8単一file検証・全宣言spine

3対象非aggregate fileのfocusedは警告・エラーなし、48 source宣言と自動生成1件（計49）の
明示print/log順とmodule監査を照合した。DefectMapsのsameSubmoduleEquiv.congr_simpは
compiler生成宣言として明示printへ加え、source手書き宣言と分ける。すべて標準公理のみ。
必要依存WitnessThreeNonzeroの単一target cacheで34既受理宣言の標準公理監査も成功。
DefectMaps→DefectShortExactのcache完成後に依存側を検証した。
Research全体/aggregate/全file loop、local lake build、Formal移植、別finalfresh4は未実施。

<!-- cycle8-generated-evidence -->

| file | source宣言（source/print/log同順序）と生成宣言 |
| --- | --- |
| `DefectMaps.lean` | `unitH1`, `directH1`, `unitH1_apply`, `directH1_apply`, `unitH1_eq_standard`, `directH1_eq_standard`, `directH1_factor`, `directH1_old`, `directH1_kernel`, `sameSubmoduleEquiv`, `sameSubmoduleEquiv_val`, `directKernelUnitEquiv`, `directKernelUnitEquiv_val`, `fiberRestriction_kernel`, `fiberRestriction_range`, `evaluationCokernelTauKernelEquiv`, `evaluationCokernelTauKernelEquiv_mk_val`; 生成：`sameSubmoduleEquiv.congr_simp` |
| `DefectShortExact.lean` | `evaluationH1_kernel`, `coefficientCancellation_zero`, `compositeDirectCokernelEquiv`, `compositeDirectCokernelEquiv_mk`, `compositeDirectCokernelEquiv_symm_mk`, `coefficientCokernelInclusion`, `coefficientCokernelInclusion_apply`, `coefficientCokernelInclusion_mk`, `totalCokernelFiberProjection`, `totalCokernelFiberProjection_apply`, `totalCokernelFiberProjection_mk_val`, `coefficientFourth_injective`, `coefficientCokernelInclusion_injective`, `totalCokernelFiberProjection_surjective`, `coefficientCokernel_exact`, `coefficientCokernel_shortExact` |
| `DefectDiagnostics.lean` | `directH1_defect`, `coefficient_kernel_dimension`, `coefficientSixTerm_kernel_dimension`, `coefficientSixTerm_cokernel_dimension`, `coefficient_cokernel_dimension`, `allPhiH1_finrank_sum`, `coefficient_cokernel_kappa_dimension`, `coefficient_cokernel_dimension_int`, `evaluationH1_surjective_iff`, `directH1_bijective_iff`, `coefficient_zeroDefect_iff`, `unitH1EquivOfZeroDefect`, `unitH1EquivOfZeroDefect_apply`, `tauKernel_eq_bot_of_zeroDefect`, `witnessThree_cancellation_zero_and_tau_ne_zero` |

| file / source+generated | source SHA-256 | focused output SHA-256 |
| --- | --- | --- |
| `DefectMaps.lean` / 17+1 | `0d45260ccf0bc021c223c1a5c8b5fa09288bfd728684fab5af13513b3d3d4449` | `e23f084fcf822117a034eb8e9e8863e86785e7bb1db48f90fac5ab104cc58e63` |
| `DefectShortExact.lean` / 16+0 | `91d48bcd53b9979e35f93f5bee351d0ac48ac6c6432bbf8e435ac770e987d4c8` | `9055dd06c0de7bf0f4953325560d2350d7016a72606fdd662df92a319125c02c` |
| `DefectDiagnostics.lean` / 15+0 | `bd3d93c50341909af0ad968c8dec37ae7a591bfeaf1500e9a2a583ac67977504` | `badc829969856728f8e34d12e18c02765211ee79249d6bb05d0d5c4297516caa` |

再現metadata `.tmp/g135/cycle8-validation.json`（SHA-256 `bb77b9b50b15d64d17ece946f88f501030fc58279efe55b8ab5744b024e797f5`）。
共通scan metadata `.tmp/g135/cycle8-scans.json`（SHA-256 `4f8eeb0d05566ccc61f36dd8bad40298fda52a981ab52d5c8e561cb5ec6f2143`）。

## Cycle 8受理とマージ

PR [#5299](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5299)の
修正後固定head `4bdc59ea609b94fd087acad580666223c073a502`で、正式rerun1の新規数学2本・Lean2本が
すべてNo major findings、中心/非中心finding 0となった。F1/F2の全解消をsourceから確認した。
[最終標準監査・root acceptance](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5299#issuecomment-6052624414)は
六選定終了条件をapprove / proof-obligation-dischargedと判定した。
merge `290bb573ddef08da2c77fdf10cd9532bfe3a70f8`、2026-10-08T04:59:03Z、
[Issue同期](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5290#issuecomment-6052643608)。
同head CI8件SUCCESS、Lean run37727496373 / Tool run37727496432。
Formal setup/cache/build/kernel/premise実stepsはSKIPPED。全49宣言は標準公理のみ。
上記Cycle 8 proposalの「修正後正式監査待ち」は当時の履歴であり、本受理節で全六条件を放電済みへ進める。
全GOALのremaining_goalと別final fresh4は未完、Formalはunported。

## Cycle 9 selection

```yaml
ledger_type: target_cycle_result
goal: G-135-aat-atlas-coefficient-fiber
cycle: 9
goal_blob_sha: cd5f3e684b7f390558796797874a1f16b52a6b18
base_oid: 290bb573ddef08da2c77fdf10cd9532bfe3a70f8
tracking_issue: 5290
report_path: research/reports/G-135-aat-atlas-coefficient-fiber.md
selection:
  proof_state_ref: PR5299最終監査6052624414・Issue同期6052643608・現source
  proof_dag_predecessors: [C3実Phi/Gamma/Lambdaと原η, C6pure κ/τ零, C8保存必要十分, G107同じC3非必要性表と旧比較保存]
  milestone: GOAL C・exact-sequence§4の局所十分条件とpure全A C3primeを同じG107反例へ接続
  proof_obligations: [局所単一成分から実係数定数写像の同型生成, 原η次数別同型と実a同型, 全Phi H1零から局所零診断, pure Rの全Phi同定と保存両方向, 全A C3prime, 同じG107原始表の新旧条件の同時計算]
  exit_criteria:
    - 各選択粗chartの実Phi連結成分・粗辺の実Gamma連結成分・粗面の実Lambda持ち上げが各一つなら、原ηの全三次数線形同型を入力から生成し元保存と実unitHomを同定する
    - 同じ局所条件から原標準H1ηのbijectiveを導き、任意M/Aの実射aへ接続する
    - 同じ局所条件と全実Phi H1零から原blockDefect零を導く。高次fiber零性を仮定しない
    - pure原入力からκstar/τ零と元保存R≃全Phi H1積を生成し、τ単射と全Phi H1零を必要十分にする
    - pure J零 iff a bijectiveかつ全Phi H1零を両方向で証明し、全Aへ量化したC3primeと非空Aへの必要性を明記する
    - 同じG107 presentation/toGeometryの全Aで実Phi H1零・原比較保存・新C3primeを生成し、既存旧C3失敗と同じ非零H1証拠を同時に示す
  selection_reason: C8の保存一般式から入力幾何による十分条件とpure必要十分の未接続部分を閉じる
  expected_result_type: proof-obligation-discharged
  lean_targets: [AtlasCoefficientFiber/LocalCoefficientSingle.lean, AtlasCoefficientFiber/LocalPreservation.lean, AtlasCoefficientFiber/PurePreservation.lean, AtlasCoefficientFiber/G107FiberComparison.lean]
  risks: [連結とH1零の混同, 空選択/空coarsechart域, mappedloopを宣言上の垂直辺へ入れる誤り, 供給η同型, 異なるG107入力への置換, 高次fiber零仮定の追加]
  unchecked: [六終了条件は実装前・未確認]
```

Cycle 9の六条件を実装前に固定した。局所条件は一般十分条件の方向仮定であり、
G107適用では同じ原始表から生成する。G107受理refはPR3994固定head
`84050e9592635418198a41cbc23f2051f023b861`、最終標準四本・全GOAL監査issuecomment-5279154319、
merge `4c80532dded00ab2b5b0a7e066b7bd355ac1ede6`。
現在のConditionC3NonnecessityWitness.leanはそのheadからbyte変更なし。
既存全A旧比較保存と旧C3失敗のstatement/入力を実読して再利用し、内部の全受理履歴は再認定しない。
局所/pure結果は三錐・D/E/W全評価の代替にしない。全GOALはtarget-proof-checkpoint、Formalはunported。

### Cycle 9固定要求と実宣言の対応

| 終了条件 | 同じ入力からの構成・射 | 検証状況 |
| --- | --- | --- |
| 1 実ηの三次数同型 | LocalCoefficientSingleの原Phi/Gamma/Lambda定数評価、constantCoefficient_bijectiveの標準piUnique同定、localUnitEquivの原unit0/1/2と全Hom等号 | 入力生成証拠あり・正式監査待ち |
| 2 原標準H1η同型 | unitH1_bijective_of_local。生成cochain同型の実旧H1とoldH1Equiv_naturalの標準射をLinearConjugation.bijective_iffで接続 | 対象focused成功 |
| 3 局所零診断 | connectingTau_injective_of_phiH1_zeroとlocal_zeroDefect。実κstar核の部分空間・各Phi H1零からτ単射を導く | 対象focused成功 |
| 4 pure R・τ必要十分 | pure_kappaStar_zero、pure_fiberR_eq_top、標準ofTopによるpureFiberREquivと順逆元保存、pure_connectingTau_injective_iff | 入力生成証拠あり・正式監査待ち |
| 5 pure全A保存とC3prime | pure_zeroDefect_iff/finrank_iff、pure_allA_zeroDefect_iff、pure_C3prime_of_allA_zeroDefect。空Aを含む全A同値と非空A必要性を分ける | 入力生成証拠あり・正式監査待ち |
| 6 同じG107新旧条件 | G107DeclaredFiber.Mは既存presentation.toGeometryそのもの。edgeMap_someから全PhiEdge空、全Phi H1零。既受理実比較全単射を任意Setへ輸送して旧J零/原a同型/C3primeを生成し、同じ旧C3失敗と両側非零H1へ接続 | 入力生成証拠あり・正式監査待ち |

局所十分条件の連結成分一つとH1零は別々の方向仮定であり、局所連結性からH1消滅を推論しない。
全次数同型の構成は実右Kan成分式を使用し、係数同型やexactnessを供給recordへ移さない。
高次Phi H2零は仮定しない。pure原条件は同じMixedFaceの空性であり、κ・τ零は
PureComparisonの原始微分producerから得る。hereditary適用では原face_none_edgeから空性を生成する。
全Phi積零の逆方向は標準surjective_eval、R同型はofTop、局所H1は標準同型自然性へ接続する。
新しい保存/消滅Propや結論certificateを入力へ導入しない。

G107で再利用する現statementはaSubnerveComparisonHom_h1Map_bijective、
not_conditionC3AtTargetSubset、targetZero_both_h1_pos。前者のFinset量化を
有限Fin2上の任意Setへcoe_toFinsetで輸送し、同じ原射をHereditarySpecializationへ接続する。
新退化辺空性は原edgeMap=someから計算し、mapped粗loopを旧CoordinateFiberEdgeと区別する。
非零実H1は同じtargetZeroの原period cocycleとその同じ比較像である。
新Phi H1零を元のfine/coarse H1零へ言い換えない。
LocalFiberの新所有API phiComplex_C1_subsingletonだけを追加し、原定義・全既存宣言は保持する。

依存DAG: 原M/A → 受理済右Kan成分/定数係数 → 局所ηの三次数同型 → 原標準a同型 →
C8保存必要十分。別枝は原mixed面空 → κ/τ零 → R全Phi同型 → pure iff/C3prime。
G107原表 → same hereditary M / edgeMap some → 原PhiEdge空 / Phi H1零、
同じ既受理全A比較 → 原J零 → a同型 → pure全A同値 → 新旧条件と非零H1の同時成立。
G133 LinearConjugation/oldH1自然性はPR5269受理版、C3右KanはPR5294、
C6pure producerはPR5297、C8保存はPR5299、G134 hereditary所有APIはPR5274以後の受理現版を使用する。
全て使用するstatement・現在の定義・適用引数を確認する。

```yaml
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: 原局所成分からη全次数同型と保存を生成し、pure R同定/保存両方向/全A C3primeと同じG107原表の新旧条件を接続
  exit_criteria_status: [1原η三次数同型あり, 2原標準a同型あり, 3高次零仮定なしの局所零診断あり, 4pure R順逆元保存とτ単射iffあり, 5pure保存両方向と全A/非空A C3primeあり, 6同じG107全A実Phi零/比較保存/新条件と旧失敗/非零H1あり]
  split_reason: none
  completion_candidate: no
  lean_artifacts: [LocalCoefficientSingle, LocalPreservation, PurePreservation, G107FiberComparison, LocalFiberの所有API追加]
  evidence: [上表・全宣言spine・5対象focusedと標準公理監査]
  claim_mapping:
    theorem_names: [localUnitEquiv, unitH1_bijective_of_local, local_zeroDefect, pureFiberREquiv, pure_zeroDefect_iff, pure_allA_zeroDefect_iff, pure_C3prime_of_allA_zeroDefect, G107DeclaredFiber.newC3prime_and_oldC3_failure]
    source_labels: [GOAL C, exact-sequence§4局所十分条件, pure C3prime, G107同じ例]
    conjuncts: [実η三次数同型と元保存, 同じ原a/旧J, pure実κstar核とτ, 全A両方向, 同じG107入力と旧C3失敗]
    undischarged_assumptions: []
    acceptance_point: 六固定終了条件を同cycleで閉じ、固定headの標準PR独立監査へ渡す
    port_status: unported
  whole_goal_status: target-proof-checkpoint
  remaining_goal: [C三錐/標準composition triangle/全整数次数と符号/順像粗係数特殊化, B/E全A有限τ消滅判定, D全Law/台自然性/G134接続, E原始有理行列計算法, W全指定例全評価/全A/二label/空台, 別finalfresh4]
audits:
  premise_delta:
    discharged: [実係数定数写像のpiUnique同定, η次数別両逆と実H1, pure R/τ同定と保存両方向, G107同じ原表のPhi零と旧比較保存]
    remaining: [選定にはなし・全GOALのremaining_goal]
  certificate_provenance:
    discharged: [原rightKan/stalk/η, 原mixed面空からκ/τ零, 同じG107presentationと既受理比較/非零H1]
    unresolved: []
  proof_use:
    used: [局所Phi/Gamma/Lambda条件, 原unit微分可換性, 全Phi H1零, 原pure κ/τ producer, 元保存ofTop, 既存G107全A実比較, 同じ旧C3failure]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [5単一focused成功, 全100明示print/source/log同順序, 共通scan clean, 静的import方向228modules成功]
  blocking_findings: [新規四本の標準PR独立査読は未実施]
  next_obligation: C三錐と実composition triangle・fiber錐から原Qへの擬同型・全整数次数/符号
```

### Cycle 9単一file検証・全宣言spine

5対象非aggregate fileはfocused成功、警告/エラー0、全100 source宣言の明示printと実logを照合した。
新規37宣言、既存63宣言、自動生成追加0。LocalFiberは所有API1件追加と全printのsource順整列だけで、
既存定義・statement・proofを変更しない。全宣言は標準三公理のみ。
G107既受理証拠の再利用に必要な8単一dependency cache（ConditionCAllA、ExecutableRationalRank、
FiniteComparisonPresentation、PresentationASubnerveDefect、ConditionCAllAChecker、ConditionCAllABridge、
UniformPresentationDecider、ConditionC3NonnecessityWitness）は個別に生成し、全namespace標準公理監査成功。
依存cache完成後に依存moduleを検証する。Research全体/aggregate/全file loop、local lake build、
Formal移植、別final fresh4は未実施。

<!-- cycle9-generated-evidence -->

| file | source宣言（source/print/log同順序） |
| --- | --- |
| `LocalFiber.lean` | `PhiChart`, `PhiEdge`, `PhiFace`, `GammaVertex`, `GammaEdge`, `LambdaFace`, `phiEndpoint`, `phiEndpoint_val`, `phiFace_edge_chart`, `phiFace_edge_none`, `phiFaceEdge`, `phiFaceEdge_val`, `gammaSource`, `gammaTarget`, `gammaBoundary`, `gammaBoundary_single`, `phiD0`, `phiD1`, `phiD0_apply`, `phiD1_apply`, `phiD1_comp_phiD0`, `phiComplex`, `phiComplex_C1_subsingleton`, `phiCellObj`, `phiCellObj_chart`, `phiCellObj_edge`, `phiCellObj_face`, `phiCellObj_injective`, `PhiInc`, `phiCellObj_carrier`, `gammaCellObj`, `gammaCellObj_inl`, `gammaCellObj_inr`, `gammaCellObj_injective`, `GammaInc`, `gammaCellObj_carrier`, `lambdaFace_carrier`, `phiBoundary1`, `phiBoundary2`, `phiBoundary1_single`, `phiBoundary2_single`, `phiBoundary1_dual`, `phiBoundary2_dual`, `phiBoundary1_comp_phiBoundary2`, `phiEmbed0`, `phiEmbed1`, `phiEmbed2`, `phiEmbed_comm1`, `phiEmbed_comm2`, `phiEmbed0_injective`, `phiEmbed1_injective`, `phiEmbed2_injective`, `phiIncFinite`, `gammaIncFinite`, `lambdaFaceFinite`, `gammaSource_val`, `gammaTarget_val_of_left`, `gammaTarget_val_of_right`, `GammaGraph`, `gammaGraphQuiver`, `gammaGraphFinite`, `gammaGraphHomFinite`, `gammaGraphArrow`, `gammaGraphArrow_val` |
| `LocalCoefficientSingle.lean` | `constantCoefficient_bijective`, `phiCoefficientConstant_apply`, `gammaCoefficientConstant_apply`, `lambdaCoefficientConstant_apply`, `chartCoefficientConstant_bijective`, `edgeCoefficientConstant_bijective`, `faceCoefficientConstant_bijective` |
| `LocalPreservation.lean` | `localUnitEquiv`, `localUnitEquiv_e0_apply`, `localUnitEquiv_e1_apply`, `localUnitEquiv_e2_apply`, `localUnitEquiv_toHom`, `unitH1_bijective_of_local`, `connectingTau_injective_of_phiH1_zero`, `local_zeroDefect` |
| `PurePreservation.lean` | `phiH1_subsingleton_of_edges_isEmpty`, `allPhiH1_subsingleton_iff`, `pure_kappaStar_zero`, `pure_fiberR_eq_top`, `pureFiberREquiv`, `pureFiberREquiv_apply`, `pureFiberREquiv_symm_val`, `pure_connectingTau_injective_iff`, `pure_zeroDefect_iff`, `pure_zeroDefect_finrank_iff`, `pure_allA_zeroDefect_iff`, `pure_C3prime_of_allA_zeroDefect` |
| `G107FiberComparison.lean` | `M`, `edgeMap_some`, `phiEdge_isEmpty`, `phiH1_zero`, `comparisonH1_bijective`, `zeroDefect`, `unitH1_bijective`, `C3prime_allA`, `newC3prime_and_oldC3_failure` |

G107FiberComparisonのnamespaceは`AAT.AG.AtlasCoefficientFiber.G107DeclaredFiber`、他は`AAT.AG.AtlasCoefficientFiber`。

| file / source数 | source SHA-256 | focused output SHA-256 |
| --- | --- | --- |
| `LocalFiber.lean` / 64 | `27e300655e253d0b95a87f3fd985008c89c36988b533bc23e7ded6116888c348` | `43173ed3b24422ff93b721c99f89da177d62d66f97543d879f338f24213ea1a8` |
| `LocalCoefficientSingle.lean` / 7 | `6520da925b2d8b2cf009869213b02c9fc780ec2557cd4573b62144f730e92505` | `f1dd13232f5a404bee0b13041c006d99c2575256f3927b35258842fd7aa8c165` |
| `LocalPreservation.lean` / 8 | `29c5ab27b2e133dd2d1415612a229c3505c685542726a98ec25c8adc399f1061` | `5eacbd8741313dbe870600753fb118a4d1d4f61e33deb649d2eb5bfb96d6d8eb` |
| `PurePreservation.lean` / 12 | `c40d5e80e53d9475487a7372dc53744002b4120b4a21415fd1590e98314e19f1` | `fdf80315b9074ff9220f8f2f7b1129a5b9eb744bdc57db90db24aa6f09bbe15b` |
| `G107FiberComparison.lean` / 9 | `eeeca027e945e309f791128f7d97e5562d030cbff355afb5e4eedb6282ae0d96` | `0030229ae4bd992c4974457f68eb48180f77a8a6f75731d9d15ec70350341f7f` |

validation `.tmp/g135/cycle9-validation.json` SHA-256 `ed2a3ea8162414c1cf7cf2235bde3a3f0631918332775653073f395a33ef751f`。
scan `.tmp/g135/cycle9-scans.json` SHA-256 `0bb6e1eb5203841259dc4176ee61b4db8851a9dd9b10f13f6edc65d549ebf0f1`。

## Cycle 9受理とマージ

PR [#5300](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5300)、固定head
`70909cc76c24e689fe03efe4340afc2bbf164969`で、新規数学2本・Lean2本は全てNo major findings、
中心/非中心finding 0。正式reruns0。
[標準監査・root acceptance](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5300#issuecomment-6053115567)は
全六条件をapprove / proof-obligation-dischargedと判定した。
[数学二票全文](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5300#issuecomment-6053099904)、
[Lean二票全文](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5300#issuecomment-6053101828)。
merge `2d9dc331d43b52cb36824836747dfeb89e2c9baa`、2026-10-08T05:36:12Z、
[Issue同期](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5290#issuecomment-6053130472)。
同head CI8 SUCCESS、Lean37731874793/Tool37731874797。Formal実build/kernel/premise stepsはSKIPPED。
全100宣言は標準三公理のみ。Cycle 9 proposalの監査待ち表示は当時の履歴であり、
本受理節で六条件を放電済みへ進める。全GOAL remainingと別finalは未完、Formalはunported。

## Cycle 10 selection

```yaml
ledger_type: target_cycle_result
goal: G-135-aat-atlas-coefficient-fiber
cycle: 10
goal_blob_sha: cd5f3e684b7f390558796797874a1f16b52a6b18
base_oid: 2d9dc331d43b52cb36824836747dfeb89e2c9baa
tracking_issue: 5290
report_path: research/reports/G-135-aat-atlas-coefficient-fiber.md
selection:
  proof_state_ref: PR5300最終監査6053115567・Issue同期6053130472・現source
  proof_dag_predecessors: [C3原η/ε/独立u全Hom因子化, C4原Qとε/制限SES, C6原標準δとτ, C8実診断/G133相殺零, G133標準錐/合成triangle/全次数SES]
  milestone: GOAL C・exact-sequence§4–5の原三錐から原Qと同じτへの全次数/符号対応
  proof_obligations: [同じ原η/ε/uの三標準錐, 独立uを中間に持つ実composition triangleと全三射, 原ε錐から原Qへの実制限擬同型, 全整数次数の錐完全列と原SESδ, 次数1で同じR/τと包含/射影を同定, 順像Pを粗係数に選ぶ恒等unit特殊化]
  exit_criteria:
    - 原η/原ε/独立uの三標準錐を生成し、原全Hom因子化から実composition triangleを構成して全三対象/三射・全次数の第一第二成分式・第三射のshift負号・標準homotopy圏のdistinguishedを示す
    - 同じ三錐の全整数次数で原微分のtarget/source成分と負符号、次数外零性と有限次元性を保持する
    - 同じ原ε錐から原QへdescShortComplexを原SESから生成し、全次数で実値(y,x)を原L制限yへ送ることと包含合成を示し、全次数擬同型と元保存homology両方向同型を導く
    - 同じ錐連結射を原SESδへ全整数次数で同定し、包含/制限可換と次数1の同じR/τ・核への射影を符号付きで接続する。原H0Q零性も同じ擬同型へ移す
    - 原三射の全整数次数でcone_short_exactの実包含/核射影/完全性/単射全射/次元加法式を接続し、H0余核/H1核/H2核などを零と仮定せず残す
    - 原Pを粗係数に選ぶ恒等unitと原εの全Hom因子化を示し、その同じH1比較の核零/余核kerτ同型と全商代表の原制限値を得る
  selection_reason: Cの残る標準錐接続を原Q/τまで閉じ、後続Dの全Law錐/SES図式が再利用できる全次数APIを固定する
  expected_result_type: proof-obligation-discharged
  lean_targets: [AtlasCoefficientFiber/CoefficientCones.lean, AtlasCoefficientFiber/FiberCone.lean, AtlasCoefficientFiber/ConeSequences.lean, AtlasCoefficientFiber/PushforwardCoarseSpecialization.lean, AtlasDefectComposition/ConeCoordinates.lean所有API, AtlasDefectComposition/ConeHomologySequence.lean所有API, AtlasDefectComposition/ConeCompositionTriangle.lean所有API]
  risks: [独立uを合成から再定義しない, 任意Qへの置換, 低次数だけへの縮小, shift/δ負号の混同, H1保存から全錐零を誤推論, 供給擬同型/有限性, P粗係数特殊化をT0原粗Cの読み替えにしない]
  unchecked: [六終了条件は実装前・未確認]
```

六条件を実装前に固定した。原三項複体はG133 zeroExtensionで移し、原Qは既存restrictionComplexを使う。
標準descShortComplexの擬同型性は原evaluationRestriction_shortExactから生成する。
一般の任意M/A/ℚと全整数次数を保持し、局所/pure/forest仮定を加えない。
Pを粗係数に選ぶ補助特殊化は元のT0 C_Aと別に記し、原ηを恒等へ変更しない。
G133のχ零と同じW3τ非零の対応はC8受理証拠を保持する。全D/E/W評価と別finalは未完。

## Cycle 10 result proposal

| 固定終了条件 | 同じ入力・射の実証拠 | 結果 |
| --- | --- | --- |
| 1 原三錐・実合成triangle・全三射とshift符号 | CoefficientConesの原η/ε/独立uとstandardComparison_factorization、coefficientCompositionTriangle、obj₁/₂/₃、distinguished、first/second/third。G133所有compositionTriangle_thirdは実shift次数同型で(-x,0)を計算 | 全構成あり・正式監査待ち |
| 2 全次数微分・次数外零・有限次元 | coefficientCone_d/fiberCone_d/totalCone_dは全ℤの(dy+fx,-dx)。各isZeroは-1/0/1/2以外だけ。各finiteDimensionalは原有限cellから生成 | 7対象focused成功 |
| 3 同じ原Qへの制限評価擬同型・全次数両方向同型 | fiberConeDescは原evaluationRestrictionShortComplexのdescShortComplex。inr/inl_apply、symm_apply/applyで(y,x)→原制限y、inr_desc。quasiIsoは原SES短完全性から、homology_isIso/Equivと順/逆評価は全ℤ | 全構成あり・正式監査待ち |
| 4 原SESδ/包含と原R/τ・射影・H⁰ | 所有coneConnecting_shortExactは標準homotopyδとSESδの同定を標準homologyへ移す。fiberCone_connecting全ℤ、HomologyEquiv_inr、H1REquiv/inr/tau、KernelProjection_tau、同じQ零性を移すfiberCone_H0_isZero | 全構成あり・正式監査待ち |
| 5 原三射の全次数実短完全列・寄与保持 | threeCones_shortExact、各CokernelInclusion_mk/KernelProjection_val/injective/surjective/function_exact、全ℤhomology_dimensionとH0/H1_dimension。実target包含・標準連結射の同じ値を保つ | 全構成あり・正式監査待ち |
| 6 補助P粗係数・恒等unitと同じε・核零/余核kerτ | pushforwardCoarseUnit/Comparisonと全Hom等号/factorization、全次数unit_standard、H1_kernel、CokernelEquiv/mk_val。元T0 C/ηを変更しない | 全構成あり・正式監査待ち |

量化は任意の原M/A、細選択π⁻¹A、ℚ、全整数次数。局所/pure/forest、H⁰余核零、
H²核零、比較の同型やQの供給、擬同型の追加仮定はない。三錐は原三射の標準零延長錐であり、
中間錐は独立uのもの。原QはrestrictionComplex、原τは既存標準SESδと原R座標の合成を保持する。
標準錐の微分と第三射には負号を含め、SESδ同定は同じmathlib符号のまま全次数で証明した。

全homology両方向同型は同じ実descの標準asIsoで生成し、QuasiIso/IsIsoを入力として受けない。
原H⁰Q零性だけはC4の入力生成証拠を使い、その同じQへ擬同型で戻してfiber錐H⁰零を得る。
他の錐の低次数寄与を消去せず、全次数のliteral kernel/quotientと実射を保持する。
補助P粗係数は原ηの変更ではなく、同じPの恒等unitを新しい始域に選んだ特殊化として記す。
その核零はC6の原εH¹単射、余核同型はC8の原制限から生成済みの同型を実使用する。

所有APIはG133 ConeCoordinatesのsymm_eq/inr/inl、ConeHomologySequenceのshortExact対応、
ConeCompositionTriangleのthirdを追加した。既存statement/def/proofは不変、明示printを全source順で追加。
元三錐に適用するG133 comparisonCone/coordinate/d/finite/degree-out、compositionTriangleの全三射、
coneShortComplex/cokernel/kernel/exact/dimensionの現statementと同じ引数を読む。
受理資格はG133 PR5269（standard6007458427/whole6007700344）、
原因子化C3 PR5294（6046087706）、原SES/Q零C4 PR5295（6047664301）、
原R/C6δ・εH¹単射PR5297（6050868943）、原余核kerτ C8 PR5299（6052624414）。
使用する固定版からの関係差分を確認し、今回の新所有APIは本cycleで監査する。
標準Lean4.28.0/mathlib8f9d9cff6bd728b17a24e163c9402775d9e6a365のdescShortComplex/QI/δ、
asIso/homologyMap/shiftの条件を原SESと有限cellから満たす。供給exactness/結果certificateなし。

依存DAG: 原M/A→原η/ε/u→全Hom因子化/zeroExtension→三実錐/合成triangle/全次数SES。
原L/原Q/ε/制限→原短完全列→標準desc→全次数QI/実homology同型→原Q H⁰零/原R→同じτ。
原P/恒等unit/原ε→補助全Hom因子化→原εH¹単射/原五項完全性→補助核零/余核kerτ。
χ零と同じW3τ非零はC8の受理済witnessThree_cancellation_zero_and_tau_ne_zeroを保持する。

```yaml
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: 原三錐の実composition triangle/全三射とshift負号、原Qへの同じ実評価QI/全homology両方向、全次数原δと原τ対応、三実錐SES/低次数寄与、P粗係数補助特殊化を接続
  exit_criteria_status: [1原三対象/全三射/符号/distinguishedあり, 2全ℤ微分/次数外零/有限性あり, 3原Qへの実評価/QI/両逆あり, 4全ℤδ/包含と原R/τ/射影/H0同定あり, 5全ℤ実SES/全元と低次数加法式あり, 6補助恒等unit/原ε/核零/商全代表kerτ同型あり]
  split_reason: none
  completion_candidate: no
  lean_artifacts: [CoefficientCones, FiberCone, ConeSequences, PushforwardCoarseSpecialization, G133三所有API追加]
  evidence: [上表・全宣言spine・7対象focusedと標準公理監査]
  claim_mapping:
    theorem_names: [coefficientCompositionTriangle_distinguished, coefficientCompositionTriangle_third, fiberConeDesc_quasiIso, fiberConeHomologyEquiv, fiberConeH1REquiv_tau, threeCones_shortExact, pushforwardCoarseCokernelEquiv]
    source_labels: [GOAL C三錐, exact-sequence§5全次数と符号, exact-sequence§4順像粗係数特殊化]
    conjuncts: [独立u中間錐と原二射, 全ℤの標準錐微分/三射, 原Q評価/原SESδ/原Rとτ, literal核商と元保存, 恒等unitの補助比較]
    undischarged_assumptions: []
    acceptance_point: 六固定終了条件を同cycleで閉じ、固定headの標準PR独立監査へ渡す
    port_status: unported
  whole_goal_status: target-proof-checkpoint
  remaining_goal: [B/E全A有限τ消滅判定, D全Law/台自然性/G134接続, E原始有理行列計算法, W全指定例全評価/全A/二label/空台, 別finalfresh4]
audits:
  premise_delta:
    discharged: [原全Hom因子化/三錐, 原SESから同じ実desc/QI/δ, 原有限cellから全次数有限性, 原εH1単射/制限から補助核商]
    remaining: [選定にはなし・全GOALのremaining_goal]
  certificate_provenance:
    discharged: [同じ原η/ε/独立u, 原restrictionComplex/evaluationRestrictionShortComplex, 標準mappingCone/desc/asIso, 同じ原R/τ]
    unresolved: []
  proof_use:
    used: [原三成分因子化, 元短完全列, 標準錐座標/shift負号, 原H0Q零性, 同じR座標/標準τ, 原εH1単射/五項列, 原P恒等unit]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [7単一focused成功, 全124明示print/source/log同順序, 共通scanと静的方向]
  blocking_findings: [新規四本の標準PR独立査読は未実施]
  next_obligation: Dの原全A制限自然性とLaw生成複体/全射への接続
```

### Cycle 10単一file検証・全宣言spine

7対象非aggregate fileはfocused成功、警告/エラー0。
全124 source/明示print/実log同順序、新規80/既存44/自動生成追加0、標準三公理のみ。
所有三fileは全既存declも明示#printで照会した。必要な単一cacheは完了を確認してから依存対象を検証。
Research全体/aggregate/全file loop、local lake build、Formal実build/移植、別finalfresh4は未実施。
7moduleはmanifestとAGの直接静的importに各1件登録し、aggregateはelaborateしない。

<!-- cycle10-generated-evidence -->

| file | source宣言（source/print/log同順序） |
| --- | --- |
| `ConeCoordinates.lean` | `coneCoordinateEquiv`, `coneCoordinateEquiv_symm_eq`, `coneCoordinateEquiv_inr`, `coneCoordinateEquiv_inl`, `coneCoordinateEquiv_snd`, `coneCoordinateEquiv_fst`, `coneCoordinateEquiv_symm_snd`, `coneCoordinateEquiv_symm_fst`, `coneCoordinateEquiv_d`, `coneCoordinateEquiv_d_apply`, `coneCoordinateEquiv_map`, `comparisonCone`, `comparisonCone_eq`, `coneDegreeFiniteDimensional`, `comparisonCone_isZero`, `comparisonConeMinusOneEquiv`, `comparisonConeZeroEquiv`, `comparisonConeOneEquiv`, `comparisonConeTwoEquiv` |
| `ConeHomologySequence.lean` | `transportShortComplex`, `transportShortComplexIso`, `transportShortComplex_exact`, `coneConnecting`, `coneConnecting_shortExact`, `coneTargetSequence`, `coneTargetSequence_f`, `coneTargetSequence_g`, `cone_target_exact`, `coneMiddleSequence`, `coneMiddleSequence_f`, `coneMiddleSequence_g`, `cone_middle_exact`, `coneSourceSequence`, `coneSourceSequence_f`, `coneSourceSequence_g`, `cone_source_exact`, `homologyFactors_inv_natural`, `homologyFactors_hom_natural`, `coneConnecting_natural` |
| `ConeCompositionTriangle.lean` | `compositionTriangle`, `compositionTriangle_mor₁`, `compositionTriangle_mor₂`, `compositionTriangle_mor₃`, `compositionTriangle_eq`, `compositionTriangle_distinguished`, `compositionTriangle_first`, `compositionTriangle_second`, `compositionTriangle_third`, `compositionTriangleConeEquiv` |
| `CoefficientCones.lean` | `coefficientCone`, `fiberCone`, `totalCone`, `standardComparison_factorization`, `coefficientCompositionTriangle`, `coefficientCompositionTriangle_obj₁`, `coefficientCompositionTriangle_obj₂`, `coefficientCompositionTriangle_obj₃`, `coefficientCompositionTriangle_distinguished`, `coefficientCompositionTriangle_first`, `coefficientCompositionTriangle_second`, `coefficientCompositionTriangle_third`, `coefficientCone_d`, `fiberCone_d`, `totalCone_d`, `coefficientCone_isZero`, `fiberCone_isZero`, `totalCone_isZero`, `coefficientCone_finiteDimensional`, `fiberCone_finiteDimensional`, `totalCone_finiteDimensional` |
| `FiberCone.lean` | `fiberConeDesc`, `fiberConeDesc_eq`, `fiberConeDesc_inr_apply`, `fiberConeDesc_inl_apply`, `fiberConeDesc_symm_apply`, `fiberConeDesc_apply`, `fiberCone_inr_desc`, `fiberConeDesc_quasiIso`, `fiberConeDesc_homology_isIso`, `fiberConeHomologyEquiv`, `fiberConeHomologyEquiv_apply`, `fiberConeHomologyEquiv_symm_evaluation`, `fiberConeHomologyEquiv_inr`, `fiberCone_connecting`, `fiberConeH1REquiv`, `fiberConeH1REquiv_apply`, `fiberConeH1REquiv_inr`, `fiberConeH1REquiv_tau`, `fiberConeKernelProjection_tau`, `fiberCone_H0_isZero` |
| `ConeSequences.lean` | `threeCones_shortExact`, `coefficientConeCokernelInclusion_mk`, `coefficientConeKernelProjection_val`, `coefficientConeCokernelInclusion_injective`, `coefficientConeKernelProjection_surjective`, `coefficientCone_function_exact`, `coefficientCone_homology_dimension`, `coefficientCone_H0_dimension`, `coefficientCone_H1_dimension`, `totalConeCokernelInclusion_mk`, `totalConeKernelProjection_val`, `totalConeCokernelInclusion_injective`, `totalConeKernelProjection_surjective`, `totalCone_function_exact`, `totalCone_homology_dimension`, `totalCone_H0_dimension`, `totalCone_H1_dimension`, `fiberConeCokernelInclusion_mk`, `fiberConeKernelProjection_val`, `fiberConeCokernelInclusion_injective`, `fiberConeKernelProjection_surjective`, `fiberCone_function_exact`, `fiberCone_homology_dimension`, `fiberCone_H0_dimension`, `fiberCone_H1_dimension` |
| `PushforwardCoarseSpecialization.lean` | `pushforwardCoarseUnit`, `pushforwardCoarseComparison`, `pushforwardCoarseUnit_eq`, `pushforwardCoarseComparison_eq`, `pushforwardCoarse_factorization`, `pushforwardCoarseUnit_standard`, `pushforwardCoarseH1_kernel`, `pushforwardCoarseCokernelEquiv`, `pushforwardCoarseCokernelEquiv_mk_val` |

所有3fileのnamespaceは`AAT.AG.AtlasDefectComposition`、新4fileは`AAT.AG.AtlasCoefficientFiber`。

| file / source数 | source SHA-256 | focused output SHA-256 |
| --- | --- | --- |
| `ConeCoordinates.lean` / 19 | `8368d89ad31f8a78702e796d2f6f85315667b426da2ad06402d0c1f49daf2719` | `ca6e113c33e14a4ef10a52b3a468ae5af8d9ada15d531c5606315e9d20b589a8` |
| `ConeHomologySequence.lean` / 20 | `d97e72261487e405b65b27cfad2696d20617a80f416517d6212d08a0b1ce9776` | `eaadde2e1da469200c0618a31c67ca13be3b83d9bbb145907e26ddbf77969cd1` |
| `ConeCompositionTriangle.lean` / 10 | `64d1356a43d165ced198f509d85f1dd11716110f5c2a5c51c42d49115c15e651` | `d447ab2bd29763b60402611ae7ffa622baadbab99223731346498c7a9222eb2a` |
| `CoefficientCones.lean` / 21 | `2d8688138a80832675a9ee71e4cd6e41d56d96331d19b407b7470e2eb35c5f05` | `4429860c14d2f23dd563d395c957f7eb8880dcd51b8c2b635aac6db836b4bbcf` |
| `FiberCone.lean` / 20 | `1fa0f559589085b427114887a431c1a285c7fc72ba0be19a2b0a15ff90e0eb82` | `71544c1420b215604a57e32c9de79c094d61043d8b5fff7cc1cac6f1bb9b5c01` |
| `ConeSequences.lean` / 25 | `28b6b74c831faca3f5be94d79fade13316513d2e833c1f9d41950921ac6da654` | `930015ba247cd63b369b805b442c7e96a612f1b02893163bad68d83907451d04` |
| `PushforwardCoarseSpecialization.lean` / 9 | `57d1cebf9e4b6eede3f734d89a73b8e6f2f1555632a312ce5bdbe8a6afc083a4` | `c8b845077175096cec17105fdc5a31ea671bdfdfff56a2aaeef658837a8417bd` |

validation `.tmp/g135/cycle10-validation.json` SHA-256 `ae6a0c2df873e9885e8cfbf54d7d6b346ec3ee16679b8638f3ec2affe45d3b69`。
scan `.tmp/g135/cycle10-scans.json` SHA-256 `ee96281a17c4aa2d2c7c7493fde047e84433ef9f6637bb49b1d221f5e304a370`。


## Cycle 10受理とマージ

PR [#5301](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5301)、固定head `cc62fac23e82e41728dd8188967c73bde36b1516`。
新規数学2本・Lean2本はすべてNo major findings、中心/非中心0、正式reruns0。
[標準監査/root acceptance](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5301#issuecomment-6053510508)、
[数学全文](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5301#issuecomment-6053491418)、
[Lean全文](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5301#issuecomment-6053494390)。
六選定終了条件はapprove / proof-obligation-discharged。原三射/独立uの実triangle、全ℤ三射/微分/符号/錐SES、
同じ原Qへの評価QI、原δ/R/τと原制限による元保存、補助P粗係数の原ε比較を閉じた。
merge `8443383e5f2c39ad76fc117ce147eaf055fb12f8`、2026-10-08T06:05:54Z。固定head全8CI SUCCESS、Lean37734604000/Tool37734604006。
Formal build/kernel/premise実stepsはSKIPPED。root7単一focused/独立4指定focused PASS、全124宣言（新80/旧44/生成0）標準三公理のみ、警告/エラー0。
前節のvalidation/scan hashと全順序をreview後再照合し一致。GOAL/design/Formal不変。
[Issue同期](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5290#issuecomment-6053529998)。
全GOALはtarget-proof-checkpoint、Formal未移植、全未完D/E/W/B-E全A有限判定と別finalを保持する。

## Cycle 11 selection（実装前固定）

```yaml
ledger_type: target_cycle_result
goal: G-135-aat-atlas-coefficient-fiber
cycle: 11
goal_blob_sha: cd5f3e684b7f390558796797874a1f16b52a6b18
base_oid: 8443383e5f2c39ad76fc117ce147eaf055fb12f8
tracking_issue: 5290
report_path: research/reports/G-135-aat-atlas-coefficient-fiber.md
selection:
  proof_state_ref: Issue5290 Cycle10受理・report原三錐と全次数対応
  proof_dag_predecessors: [原MからのP/η/ε/u, 原L/Q/κ/R/τ, 三錐と実完全列, G134混在Law分解, G133有限族標準数学]
  milestone: GOAL Dの全有限発生ラベルの原P・二射・Q/R/τ・三錐/完全列を同じ実Law比較へ接続
  proof_obligations: [細adequacy生成, Law値fiberとcanonical逆像の全三次数同定, 原P/二射の有限族, 実Law全Hom因子化, 同じQ/R/κ/τの族と実完全列, 三錐と全次数写像の直和自然性, 同じ旧H1とblockDefectの係数/fiber和]
  exit_criteria:
    - 粗adequacyだけから細adequacyを生成し、原Law全三成分を同じ発生ラベルの粗Aと細π逆像へ両方向同定。Law値型全体有限を要求せず空族も保持。
    - 各原Pの有限族としてLaw順像と原η/εを生成し、独立generatedComparisonHomを全三次数/全Homで因子化。全整数次数の同じ零延長射と元評価にも接続。
    - 原Qと原κ/Rを全発生ラベルで集め、同じ実ε/制限の全次数SESとδを成分ごとに同定。H0Q零、H1Qと同じR族、原τ、五項列の全隣接完全性を実Lawの同じhomologyへ移す。
    - Law原二射と独立直接射の実三錐を原ラベル三錐の有限直和へ元/符号/全次数同定し、実合成triangleの三射とQへの評価・δ・R/τを同じ成分写像へ接続。
    - 同じ旧Law H1比較の核/余核を原係数/kerτへ接続し、実包含/余核射/代表値と完全性を保つ。原blockDefectを同じ各原aとkerτの寄与和へ戻し、同じ台のラベル重複を圧縮しない。
    - 上記全構成・全方向の宣言/元評価/標準API/依存版と全公理ログを固定し、空ラベル・空台も排除しない。台包含自然性/G134/E/W全評価は後続固定義務として残す。
  selection_reason: 受理済み任意Aの分解を元の実Law対象と同じ写像へ戻し、DのLaw接続gapを閉じる。台包含とG134操作は別の自然性/保存群であり今回の終了条件へ混ぜない。
  expected_result_type: proof-obligation-discharged
  lean_targets: [AtlasCoefficientFiber/LawCoefficientInput.lean, AtlasCoefficientFiber/LawCoefficientComparison.lean, AtlasCoefficientFiber/LawFiberSequence.lean, AtlasCoefficientFiber/LawCoefficientCones.lean, AtlasCoefficientFiber/LawDefectDiagnostics.lean]
  risks: [ラベル重複圧縮, 粗adequacy以外を新仮定へ移動, 任意中間P, 元canonical逆像輸送欠落, 同次元同型だけ, δ/triangle符号, 元の旧H1商と標準homology混同, 既存hereditary Law版へM変換]
  unchecked: [実Law接続群は未実装。全GOAL残件と別finalは未完。]
```

## Cycle 11 result proposal

全発生ラベルλを同じLawValueLabelのまま保持し、粗Aλとcanonical逆像π⁻¹Aλを使う。
入力はT0の原M・二readingと有限Law族・粗adequacyだけであり、細adequacyは
lawFineAdequateで生成する。Law値型全体のFintype、台の非空性、Nonemptyラベル、
hereditary比較、原比較の同型、期待rank、供給SES/δ/QIは要求しない。

| 固定終了条件 | 同じ実入力・射への宣言対応 | 結果 |
| --- | --- | --- |
| 1 粗adequacyから細を生成、原Law三成分と粗台/細逆像の両方向同定 | LawCoefficientInputのlawFineAdequate、lawFineFiber_eq_preimage、lawCoarseCanonicalEquiv/lawFineCanonicalEquiv。実block同値→元台等号→三項同値を合成しtoHomの全体等号を保持 | 構成あり・正式監査待ち |
| 2 原P族と別生成η/ε、独立generatedComparisonHomの全Hom因子化 | lawPushforwardComplex、lawUnitHom/lawEvaluationHomとf0/f1/f2、lawGeneratedComparison_factorization。lawCoarse/Pushforward/FineStandardIsoと三Standard_squareで全ℤの同じ射へ移す | 構成あり・正式監査待ち |
| 3 同じLaw Q/κ/R/τと実SES・全次数δ・五項列 | lawRestrictionComplexは各原Q族、lawKappa/Starは各原κ/κ*、lawRはliteral核。lawEvaluationRestriction_shortExactは原ラベルSESから実Law射を保って生成。lawConnecting_delta_component全ℤ、Q-H1-R同型/順逆成分値、lawConnectingTau_component、H0零、Law五項列の三完全性とεH1単射 | 構成あり・正式監査待ち |
| 4 原Law三錐の有限直和・全三射/符号・Q評価/δ/Rτ | lawCoefficient/Fiber/TotalConeFamilyIsoと各component/DirectSumIsoは同じ実原三射から生成。lawCoefficientCompositionTriangleのdistinguished/first/second/thirdと各componentで全ℤの三原ラベル射へ接続。lawFiberConeDescの(y,x)制限y、原SESからQI、family_square/HomologyEquiv_family/H1REquiv_family、connecting_component、KernelProjection_tauとH0零 | 構成あり・正式監査待ち |
| 5 同じ旧Law H1比較の核/余核SES・全代表・同じblockDefect和 | lawDirectH1は独立generatedComparisonHomのH1、lawDirectH1_oldで同じ旧generatedComparisonH1Mapへ戻す。lawOldKernelUnitEquivと値、lawOldCokernelStandardEquivと全mk、同じ旧Law余核包含/fiber射の全代表値・単射・完全性・全射。lawCoefficientBlockDefect_sumは同じ原a核とa余核+kerτを全ラベルで加算 | 構成あり・正式監査待ち |
| 6 全方向・全spine・標準API/版・空族も保持 | 全source/print/logの順序を固定。全Label量化の同型・射は空族も定義され、同じ台の別labelも残る。台包含/G134/E/Wの全評価と別finalは後続義務 | 構成あり・正式監査待ち |

LawHomologyCoordinatesは上記群の共通接続fileとして追加した。到達点と六終了条件は
選定時から不変であり、数学的到達点の分割はない。LawCoefficientConesの実family複体同型は
全微分を保持するので、元の各錐の負号を含む微分を別のrecordへ置き換えていない。
同じtriangle第三射は実shiftFunctorObjXIsoを通して(-x,0)となり、原各ラベルの第三射と可換。
Q評価はmappingCone.descShortComplexそのもの。QuasiIsoと全homology両方向同型は
原Law SESから生成し、その同じ評価の全元・包含・逆元・原R/τを接続する。

旧Law H1余核列はG133の同じ第四/第五射を同じLaw a/εへ適用する。
Tの定義は独立生成uのhomology射のまま保ち、因子化定理の等号で商を移す。
後段余核は原L制限の核/像とquotKerEquivRangeでkerτへ同定し、次元だけの同型を選ばない。
旧H1への戻しはoldH1Equiv_naturalとLinearConjugationの核/実商同型を使う。
全代表式と原Law制限の値を保ち、原blockDefectの加法式は同じ混在Law ownerの
lawH1Defect_subset_sumと各原a/τの受理証拠を使用する。

### Cycle 11 material premise・provenance・proof-use

| material premise | 分類・原始provenanceと使用経路 | 状態 |
| --- | --- | --- |
| T0原M・reading因子・原台/端点/退化面・ℚ | ambient-boundary。各原P/Q/κ/R/τを同じM/Aλから生成し、元比較全三成分へ接続 | 同じ入力を保持 |
| 有限Law族と粗adequacy | ambient-boundary。発生ラベルと粗fiberを生成、reading因子から細adequacyと細fiber逆像等号を生成 | 細adequacyは放電済み |
| LawFamilyの三項同値と元混在block square | discharge-required。G134受理ownerから同じ原粗/細Law対象をラベル族へ移し、独立generatedComparisonHomを同じ原u族へ同定 | 元statement・引数・使用を確認 |
| 各原評価/制限SES・H0Q零性・原Q-R同型/τ | discharge-required。C4–6の同じ原M/Aλ証拠を使用。全ラベルSESの族から実Law SESを生成し、native δ自然性で同じ各原δへ戻す | Law側に新供給仮定なし |
| Law R/H1Q・τ | discharge-required。lawRは各原κ*族のliteral核、kernelEquivで同じ各原R族へ両方向移送。τは同じ実Law SESδを同じH1Q-R同型で読む | 全R元・全ラベル成分式あり |
| Law三錐/QI/triangle・各成分同型 | discharge-required。全体独立uと別生成η/εの全Hom因子化、実標準coneMapIso/FiniteConeFamily.iso/FiniteComplexFamily.directSumIso、同じ原SESのdescから生成 | 同じ全射・微分・符号を保持 |
| 核/余核・旧Law比較・blockDefect和 | discharge-required。原εH1単射/五項完全性→Law核/商→G133第四第五射→元旧H1商同型。原実ラベル欠損を原aとkerτに分解 | 同じ全代表・完全性とラベル重複を保持 |
| generic family/comm/ShortExactの引数 | direction-hypothesis。汎用補助でのみ保持し、Law適用では各原shortExact・元射正方形・粗/細座標の実同型をproducerから供給 | Law出力に未放電行なし |

依存DAG: 原M/粗adequacy→粗Aλ/細adequacy/π⁻¹Aλ→原P/Q/κ/R/τ族。
原Law block同値/原混在block比較square→実Law全三次数座標→別η/εと独立u全Hom因子化。
各原ε/制限SES→族SES→実Law SES→native δ自然性→同じ原Q/R/τ成分と五項列。
実全Hom正方形→三実Law錐の族/有限直和同型→triangle三射とshift負号→同じQ desc/QI/R/τ。
原εH1単射/完全性→Law実核商→同じG133第四第五射→旧Law実比較核/余核SESと全代表。
元混在Law欠損族→各同じ原a/kerτ→原blockDefect全label和。

G133の汎用有限族・線形同定・標準錐/合成triangleはPR5269
（standard6007458427/whole6007700344）受理版の現在statementと同じ引数を使う。
G134の混在Law分解/全Hom block squareはPR5282、head
`062134827d0b41b7bb5a73db97a17bddebbc2ef7`、merge
`7f169e370dfc0f28229bae2b81b69b7a4ab538ac`、
[標準受理](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5282#issuecomment-6026457541)。
その受理版以後の対象owner関係差分は未使用のLawFiberBridge公開補題追加だけであり、
使用するlawBlockFiber_comparison_square/lawFiberComparison_canonicalと
lawH1Defect_subset_sumのstatement/proofは不変。
原P/因子化C3 PR5294、原SES/Q零C4 PR5295、原R/δ/τC6 PR5297、
原核商/診断C8 PR5299、三錐とQ desc/δ対応C10 PR5301の受理refは各受理節を使う。
Lean4.28.0/mathlib8f9d9cff6bd728b17a24e163c9402775d9e6a365の
ShortComplex.isoMk/shortExact_iff_of_iso、native δ_naturality、mappingCone.descShortComplex/QI、
asIso/homologyMapIso、LinearEquiv/quotKerEquivRangeを適用条件とともに確認した。
全new定義にはraw入力→生成のproducerがあり、期待rankや準備済み結果certificateを受けない。

```yaml
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: 実Law三項から同じ原P/二射/Q/κ/R/τ/三錐/五項列を全発生ラベルと全ℤで接続し、同じ旧LawH1実核余核列と原blockDefect係数/fiber和を構成
  exit_criteria_status: [1粗adequacyから細生成/全三成分両方向, 2原P族/別ηε/独立u全Hom因子化/全ℤ, 3原QκR族/実SES/nativeδ成分/Rτ/全五項完全性, 4実三錐有限直和/全三射と符号/Qdesc/δRτ自然性, 5旧LawH1核余核SES/全代表/原aとkerτ寄与和, 6全spine/版/公理/空族も保持]
  split_reason: none
  completion_candidate: no
  lean_artifacts: [LawCoefficientInput, LawCoefficientComparison, LawFiberSequence, LawHomologyCoordinates, LawCoefficientCones, LawDefectDiagnostics]
  evidence: [六固定条件対応表, 全宣言spineと単一focusedログ, 静的方向と共通scan]
  claim_mapping:
    theorem_names: [lawFineAdequate, lawGeneratedComparison_factorization, lawEvaluationRestriction_shortExact, lawConnectingTau_component, lawFiveTerm_exact_at_fiber, lawCoefficientCompositionTriangle_third_component, lawFiberConeDesc_family_square, lawFiberConeH1REquiv_family, lawOldCoefficientCokernel_shortExact, lawCoefficientBlockDefect_sum]
    source_labels: [GOAL D有限Law, 設計exact-sequenceの同じLaw二射/全構成, reuse-mapの混在Law owner接続義務]
    conjuncts: [粗adequacy生成と元Law同定, 原Pと別生成二射/独立u, 原κliteralR/原Qδτ, 全ℤ原三錐と三射/符号, 旧実H1/代表/診断両成分, 重複ラベル保持と空族]
    undischarged_assumptions: []
    acceptance_point: 固定headの標準PR独立四本とroot acceptanceで六選定条件を判定
    port_status: unported
  whole_goal_status: target-proof-checkpoint
  remaining_goal: [B/E全A有限τ消滅判定, D全A包含自然性/G134操作保存接続, E原始有理行列計算法, W全指定例全評価/全A/二label/空台, 別finalfresh4]
audits:
  premise_delta:
    discharged: [細adequacy/元Law同定, 同じ原P二射/独立u因子化, 原QκliteralR/実LawSESδτ, 三錐/全三射/Qdesc, 旧H1核余核と元保存/全label寄与]
    remaining: [選定にはなし・全GOALのremaining_goal]
  certificate_provenance:
    discharged: [原M/AλPと原ηεu, 原各L/QκRτ, 実Law全三次数生成射, nativeLaw短完全列/δ, 実標準三錐/有限直和/Qdesc, 同じ旧LawH1実商]
    unresolved: []
  proof_use:
    used: [粗Lawadequacyとreading因子, 原混在block square/canonicalfiber等号, 原P/二射全Hom, 原各SES/QR/δ/τ, 同じLawδ自然性, 標準三錐/Qdesc/shift負号, 原五項列とG133第四第五射, 旧H1自然性/原blockDefect実分解]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [6単一file focusedと全source/print/logの順序, 公理監査, 共通scanと静的方向]
  blocking_findings: [新規四本の標準PR独立査読は未実施]
  next_obligation: Dの原全A包含自然性/PηεκRτとG134保存操作の同じ比較への接続
```

### Cycle 11単一file検証・全宣言spine

6対象非aggregate fileはfocused成功、警告/エラー0。
全192宣言はsource/明示print/実log同順序、新規192/既存0/自動生成追加0。
各module末尾の全namespace auditも同じ件数で標準三公理のみ。
必要な単一cacheは完了を確認してから依存対象を検証した。
Research全体/aggregate/全file loop、local lake build、Formal実build/移植、別finalfresh4は未実施。
6moduleはmanifestとAGの直接静的importに各1件登録し、aggregateはelaborateしない。
静的Research import directionは228modulesの走査で成功。GOAL/design/Formalは不変。

<!-- cycle11-generated-evidence -->

| file | source宣言（source/print/log同順序） |
| --- | --- |
| `LawCoefficientInput.lean` | `coefficientCochainEquivTrans`, `coefficientCochainEquivTrans_toHom`, `coefficientCochainEquivOfEq`, `coefficientCochainEquivOfEq_comp`, `coefficientFamilyCochainEquiv`, `coefficientFamilyCochainEquiv_toHom`, `lawSelectedCochainEquiv`, `lawFineAdequate`, `lawFineFiber_eq_preimage`, `lawFineBlockCanonicalEquiv`, `lawFineCanonicalEquiv`, `lawCoarseCanonicalEquiv`, `coefficientCochain_comp_assoc`, `coefficientFamily_map_comp`, `coefficientFamilyEquiv_natural`, `lawFineBlockCanonicalEquiv_toHom`, `lawCoarseCanonicalEquiv_toHom`, `lawFineCanonicalEquiv_toHom` |
| `LawCoefficientComparison.lean` | `lawBlockCanonical_square`, `lawGeneratedCanonical_square`, `lawPushforwardComplex`, `lawUnitHom`, `lawEvaluationHom`, `lawUnitHom_f0`, `lawUnitHom_f1`, `lawUnitHom_f2`, `lawEvaluationCanonical_square`, `lawGeneratedComparison_factorization`, `lawStandardComparison_factorization`, `lawUnitHom_eq`, `lawEvaluationHom_eq`, `lawEvaluationHom_f0`, `lawEvaluationHom_f1`, `lawEvaluationHom_f2`, `lawPushforwardStandardIso`, `lawCoarseStandardIso`, `lawFineStandardIso`, `lawFineStandardIso_hom`, `lawUnitStandard_square`, `lawEvaluationStandard_square`, `lawGeneratedStandard_square` |
| `LawFiberSequence.lean` | `coefficientShortComplexFamily`, `coefficientShortComplexFamily_shortExact`, `lawRestrictionComplex`, `lawRestrictionHom`, `lawRestrictionHom_eq`, `lawEvaluation_restriction_zero0`, `lawEvaluation_restriction_zero1`, `lawEvaluation_restriction_zero2`, `lawEvaluation_restriction_standard_zero`, `lawEvaluationRestrictionShortComplex`, `lawRestrictionStandardIso`, `lawRestrictionStandard_square`, `lawEvaluationRestrictionFamilyIso`, `lawEvaluationRestriction_shortExact`, `coefficientShortComplexFamily_projection`, `lawEvaluationRestrictionProjection`, `lawEvaluationRestrictionProjection_τ1`, `lawEvaluationRestrictionProjection_τ3`, `lawPushforwardHomologyEquiv`, `lawRestrictionHomologyEquiv`, `lawPushforwardHomologyEquiv_component`, `lawRestrictionHomologyEquiv_component`, `lawConnecting_delta_component`, `lawKappa`, `lawKappaStar`, `lawR`, `lawRFamilyEquiv`, `lawRFamilyEquiv_val`, `lawRestrictionHomologyREquiv`, `lawRestrictionHomologyREquiv_component`, `lawConnectingTau`, `lawConnectingTau_apply`, `lawConnectingTau_component`, `lawRestriction_H0_isZero`, `lawEvaluationH1`, `lawFiberRestrictionH1`, `lawEvaluationH2`, `lawEvaluationH1_injective`, `lawFiveTerm_exact_at_fineH1`, `lawFiveTerm_exact_at_fiber`, `lawFiveTerm_exact_at_pushforwardH2`, `lawKappa_apply`, `lawKappaStar_apply`, `lawRFamilyEquiv_symm_val`, `lawEvaluationH1_eq_standard`, `lawEvaluationH1_apply`, `lawFiberRestrictionH1_apply`, `lawEvaluationH2_eq_standard` |
| `LawHomologyCoordinates.lean` | `coefficientFamilyHomologyEquiv`, `coefficientFamilyHomologyEquiv_component`, `coefficientFamilyHomologyEquiv_natural`, `lawCoarseHomologyEquiv`, `lawFineHomologyEquiv`, `lawPushforwardHomologyEquiv_eq`, `lawRestrictionHomologyEquiv_eq`, `lawUnit_homology_component`, `lawEvaluation_homology_component`, `lawGenerated_homology_component`, `lawRestriction_homology_component`, `lawOldCoarseH1Equiv`, `lawOldFineH1Equiv`, `lawUnitH1`, `lawDirectH1`, `lawDirectH1_factor`, `lawDirectH1_old`, `lawFiberRestrictionH1_component` |
| `LawCoefficientCones.lean` | `lawCoefficientFiniteBiproducts`, `coefficientFamilyConeIso`, `coefficientFamilyConeIso_component`, `lawCoefficientCone`, `lawFiberCone`, `lawTotalCone`, `lawCoefficientConeFamilyIso`, `lawFiberConeFamilyIso`, `lawTotalConeFamilyIso`, `lawCoefficientCompositionTriangle`, `lawCoefficientCompositionTriangle_distinguished`, `lawCoefficientCompositionTriangle_first`, `lawCoefficientCompositionTriangle_second`, `lawCoefficientCompositionTriangle_third`, `lawFiberConeDesc`, `lawFiberConeDesc_eq`, `lawFiberConeDesc_inr_apply`, `lawFiberConeDesc_inl_apply`, `lawFiberConeDesc_symm_apply`, `lawFiberConeDesc_apply`, `lawFiberCone_inr_desc`, `lawFiberConeDesc_quasiIso`, `lawFiberConeDesc_homology_isIso`, `lawFiberConeHomologyEquiv`, `lawFiberConeHomologyEquiv_apply`, `lawFiberCone_connecting`, `lawFiberConeH1REquiv`, `lawFiberConeH1REquiv_apply`, `lawFiberConeH1REquiv_tau`, `lawCoefficientConeFamilyIso_component`, `lawFiberConeFamilyIso_component`, `lawTotalConeFamilyIso_component`, `lawCoefficientConeDirectSumIso`, `lawFiberConeDirectSumIso`, `lawTotalConeDirectSumIso`, `lawCoefficientCompositionTriangle_first_component`, `lawCoefficientCompositionTriangle_second_component`, `lawCoefficientCompositionTriangle_third_component`, `lawFiberConeDesc_family_square`, `lawFiberConeFamilyHomologyEquiv`, `lawFiberConeHomologyEquiv_family`, `lawFiberConeH1REquiv_family`, `lawFiberCone_connecting_component`, `lawFiberConeKernelProjection_tau`, `lawFiberCone_H0_isZero`, `lawFiberConeHomologyEquiv_symm_evaluation`, `lawFiberConeHomologyEquiv_inr`, `lawFiberConeH1REquiv_inr` |
| `LawDefectDiagnostics.lean` | `lawDirectH1_kernel`, `lawDirectKernelUnitEquiv`, `lawDirectKernelUnitEquiv_val`, `lawFiberRestriction_kernel`, `lawFiberRestriction_range`, `lawEvaluationCokernelTauKernelEquiv`, `lawEvaluationCokernelTauKernelEquiv_mk_val`, `lawEvaluationH1_kernel`, `lawCoefficientCancellation_zero`, `lawCompositeDirectCokernelEquiv`, `lawCompositeDirectCokernelEquiv_mk`, `lawCompositeDirectCokernelEquiv_symm_mk`, `lawCoefficientCokernelInclusion`, `lawCoefficientCokernelInclusion_apply`, `lawCoefficientCokernelInclusion_mk`, `lawTotalCokernelFiberProjection`, `lawTotalCokernelFiberProjection_apply`, `lawTotalCokernelFiberProjection_mk_val`, `lawCoefficientFourth_injective`, `lawCoefficientCokernelInclusion_injective`, `lawTotalCokernelFiberProjection_surjective`, `lawCoefficientCokernel_exact`, `lawCoefficientCokernel_shortExact`, `lawOldKernelUnitEquiv`, `lawOldKernelUnitEquiv_val`, `lawOldCokernelStandardEquiv`, `lawOldCokernelStandardEquiv_mk`, `lawOldCoefficientCokernelInclusion`, `lawOldTotalCokernelFiberProjection`, `lawOldCoefficientCokernelInclusion_mk`, `lawOldTotalCokernelFiberProjection_mk_val`, `lawOldCoefficientCokernelInclusion_injective`, `lawOldTotalCokernelFiberProjection_surjective`, `lawOldCoefficientCokernel_exact`, `lawOldCoefficientCokernel_shortExact`, `coefficient_cokernel_sum`, `lawCoefficientBlockDefect_sum` |

全namespaceは`AAT.AG.AtlasCoefficientFiber`。

| file / source数 | source SHA-256 | focused output SHA-256 |
| --- | --- | --- |
| `LawCoefficientInput.lean` / 18 | `399b4b7f9f64559d039fb432a0ec1a10e309c7e8f14396c6c677b0cd62314752` | `734c9e12082ed3c4bfe4adcb025245bfbc746782dfb524cf1b06a20dfb5bb51a` |
| `LawCoefficientComparison.lean` / 23 | `d922dd7259c753d0c84b8eab8007fc75089b857fa73bc32b97d0a042bd131b99` | `ba733fb722b7f060f1734b269f2e8bffec71c110664ef29cecb041a682d7d2f2` |
| `LawFiberSequence.lean` / 48 | `44c10c81684293c46fc03f51e67020b974dcbc78d7925c77122ec206c16716bf` | `72ad54ac082be9f99ddfb3f1b21432d670a8715f8116977dab9540f0ba7b2188` |
| `LawHomologyCoordinates.lean` / 18 | `6052b12559e0f2fe036036ff60349e451e9fbb948da10582236aee718e3ae68c` | `7c170786ef69a2d4d62d381e7e80845974dbab112a8d9befee19da3a841c69c1` |
| `LawCoefficientCones.lean` / 48 | `6d1fe486a122491a23964b1229b9828c93bb0919076edd653942870b7638ccf4` | `01be77bca106150c28f22d4b7b3c6868fc444a60f9f204c2be57b1f69ef43014` |
| `LawDefectDiagnostics.lean` / 37 | `2269b369f00de215a3208021c05df0c77a476225e8fd6233e331759ae946e8d0` | `e9a415ff4117a5b7b6a6161f50d72d727612c6a740f3095530b0587830891db6` |

validation `.tmp/g135/cycle11-validation.json` SHA-256 `ab84685aef105ae507e7a2608d04e04b32f8dc7a76d751db4e7b048ce3685838`。
scan `.tmp/g135/cycle11-scans.json` SHA-256 `0e87f70bc69cdb8ec23c9f412825f19fd735431e57bf62109f085904fc2a7268`。


## Cycle 11受理・merge同期

PR [#5302](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5302)、head
`7f20e6aaaae8c51298b32d955ca16a6b0076b84a`、merge
`a993ccd6791f64cbbb8bdd6c4c6b591c3ea11dad`、2026-10-08T07:16:38Z。
[標準監査/root acceptance](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5302#issuecomment-6054697310)、
[数学二票全文](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5302#issuecomment-6054486053)、
[Lean二票全文](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5302#issuecomment-6054489763)、
[独立直接確認](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5302#issuecomment-6054674802)、
[Issue同期](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5290#issuecomment-6054722709)。
六固定終了条件はapprove / proof-obligation-discharged。初回新規数学2・Lean2は中心0、
非中心F1一件。名指しlawFineStandardIso_hom追加と下流proof内部・証拠文言の変更を、
新規独立単一確認が資格内/実体解消と確認し、新findingなし。正式reruns0。
全192source/print/log/report同順、生成追加0、標準三公理のみ、warning/error0。
root6単一focused/F1後2変更file/独立4指定focused/direct指定Fiberfocused成功。
validation SHA `ab84685aef105ae507e7a2608d04e04b32f8dc7a76d751db4e7b048ce3685838`、
scan SHA `0e87f70bc69cdb8ec23c9f412825f19fd735431e57bf62109f085904fc2a7268`。
6登録と共通scan/静的方向228modulePASS、GOAL/design/Formal不変。
修正head全8checkSUCCESS、Lean37741728268/Tool37741728254実run成功。
Formal setup/cache/build/kernel/premise実stepsSKIPPED、Research全体/aggregate/fullfileloopは未実施。
全GOALはcheckpoint、Formal unported、D全A自然性/G134・B/E有限判定・E原始算法・W・別finalは未完。

## Cycle 12 selection

```yaml
ledger_type: target_cycle_result
goal: G-135-aat-atlas-coefficient-fiber
cycle: 12
goal_blob_sha: cd5f3e684b7f390558796797874a1f16b52a6b18
base_oid: a993ccd6791f64cbbb8bdd6c4c6b591c3ea11dad
tracking_issue: 5290
report_path: research/reports/G-135-aat-atlas-coefficient-fiber.md
selection:
  proof_state_ref: Cycle11受理/Issue6054722709とDの全A制限未完行
  proof_dag_predecessors: [原incidence/carrier/右Kan C1–3, 原L商双対/SES C4, 原κQR C5, 原nativeδτ C6, 原三錐 C10, 実Law全射接続 C11, G134同じ支持包含と実u制限]
  milestone: GOAL Dの全A包含に対する原順像・二射・fiber適合・原連結射を同じprimitive support生成から自然にする
  proof_obligations: [出現を保つincidence包含とcarrier全正方形, 実comma包含/成分前合成の順像制限, 原nativechain/退化L包含と原商双対比較, 同じPの全三次数制限とηε/u正方形, 原Φ/混在閉路の包含とκ/κstar/literalR制限, 原Q-RとnativeSESδ/τ自然性, 同じ三錐/triangle制限と全次数/代表式]
  exit_criteria:
    - 全A包含Bの三次数セル包含・全incidence出現・carrier全射正方形から実comma関手と係数制限を生成し、全成分前合成値・係数incidence自然性を証明する
    - 元のnative細chain包含は原L各次数を保存し原商双対を含め同じP制限に接続する。原P全三微分/ηε/独立uの全Hom正方形を証明し、空Aと包含恒等/合成を保持する
    - 原Φ chainと原mixedCycles包含はB/D/Vを保存し、同じκの全代表で可換。双対κstarとliteralRの原fiber制限を構成し、原Q-H1-R同型がこの同じ制限と可換である
    - 同じQの三次数制限と原ε/制限SES射から全ℤnativeδ自然性を導き、次数1の同じ原τと五項列各実射を同じR制限で可換にする
    - 同じ原ηεuの三標準錐の制限を原正方形から生成し、全ℤの二座標/三triangle射/shift負号/Qdescと連結射の対応を保持する
    - 新しい供給自然性や同型仮定を入力へ移さず、全構成の元値/恒等/合成/両方向・標準API・全宣言/公理/依存を同じ原始Mと任意A包含で監査する
  selection_reason: Law各ラベルへの接続後に残る全台の同じ新対象/新写像の自然性を閉じ、G134保存操作と全A有限判定へ実射を渡す
  expected_result_type: proof-obligation-discharged
  lean_targets: [SupportCells, SupportCarrier, SupportCoefficients, SupportDegenerate, SupportPushforward, SupportFiber, SupportConnecting, SupportCones]
  risks: [全出現と対象輸送欠落, 係数stalk制限を根拠なく同型と扱うこと, 商から新Pを再定義, literalRを自由な座標制限へ交換, τを任意輸送で定義, 恒等/合成や全整数次数の片方向化]
  unchecked: [六終了条件の構成とfocused検証は未実装, 正式PR四本は到達点実装後, 全GOAL別final未実施]
```

## Cycle 12 result proposal

六固定終了条件を次の同じ原始入力経路で閉じた。全GOALの完了候補ではない。

```yaml
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: 同じMと任意A包含Bから原incidence/comma/右Kan P制限を生成し、原L/商双対・原Phi/混在閉路・実kappa/literalR・原SES/nativeδτ・三錐/triangleを同じ全代表で自然にした
  exit_criteria_status:
    - 条件1/closed：supportIncFunctorの全出現・supportCarrierIsoの全Inc射からStructuredArrow.map₂を生成し、supportCoefficientRestrict_component/eval/naturalが実CC前合成を証明
    - 条件2/closed：supportL0/1/2IncludeとsupportDegenerateChainIncludeは同じnative細chain包含。supportQuotient0/1/2と両微分・supportEvaluationQuotientDual0/1/2で原P双対を照合。supportPushforwardHomとηε/独立u正方形・恒等/合成・supportEmptyが全Aを保持
    - 条件3/closed：supportPhiChain_boundary1/2とsupportMixedVertical/HorizontalBoundary・supportVerticalBoundaryでB/D/Vの代表を包含。supportRawKappa/supportKappa・supportKappaStarからsupportFiberRをliteral核内に生成。supportQRawRとsupportFiberR_eq_supportRRestrictionが原Q-H1-R座標に接続
    - 条件4/closed：supportEvaluationRestrictionMorphismとsupportConnecting_deltaは全整数次数の同じnativeSES。supportFiberR_tau・supportEvaluationH1/H2・supportFiberR_fiveTermが原五項列の全実射を保持
    - 条件5/closed：supportCoefficient/Fiber/TotalConeは原三正方形のmappingCone.map。全次数の二座標・supportConeTriangle全三射・shift負号・supportFiberConeDesc/Q同型/Connectingを保持
    - 条件6/closed：供給自然性・選択済み同型を新入力とせず、原M/任意支持包含から全値・主制限の恒等/合成・元可逆座標・全宣言と標準APIを照合。全GOALの後続構成は別未完行に保持
  split_reason: none
  completion_candidate: no
  lean_artifacts: [SupportCells/Carrier/Coefficients, SupportDegenerate/StandardChains/Quotient, SupportPushforward/QRestriction/Connecting, SupportPhiCells/Restriction/Homology/Embedding, SupportFiberChains/VerticalHomology/Fiber, SupportCones/Empty]
  evidence: [下記source/print/log/report同順序spineと各単一file focused、公理監査]
  claim_mapping:
    theorem_names: [supportCoefficientRestrict_natural, supportEvaluationQuotientDual1, supportKappa, supportKappaStar, supportFiberR_eq_supportRRestriction, supportConnecting_delta, supportFiberR_tau, supportConeTriangle, supportFiberConeConnecting]
    source_labels: [GOAL D全台の原対象/実射自然性、A/B/C同じ原始構成への接続]
    conjuncts: [六終了条件と上記対応。Law全発生ラベルの台射とG134保存操作・有限合成は後続義務]
    undischarged_assumptions: []
    acceptance_point: 原始Mと支持包含から同じ新対象と写像を構成し、全代表と原標準連結射に接続した到達点。正式PR監査の受理前proposal
    port_status: unported
audits:
  premise_delta:
    discharged: [台incidenceとcarrier全射正方形、実comma係数前合成、Lと実商微分の保存、原Phi閉路/実V像の保存、kappaとその双対の可換性、literalR閉性、実Q-R座標の自然性、原標準SESδ/τ自然性、原三錐全射自然性]
    remaining: [D Law全発生ラベル台射・G134指定操作/reading pullback/部分セル比較有限合成・面複製、B/E全A有限τ判定、E原始有理行列生成と既存blockDefect一致、W全指定表と同時評価、全GOAL別finalfresh4]
  certificate_provenance:
    discharged: [StructuredArrow.map₂入力は原carrier等号から、coefficient制限は元Kan/CC同型と前合成から、L包含は原細自由chainから、原商はliteral Kprime/L、Phi閉路商は原両微分から、Rは実kappaStar核、SESは元ε/原L制限、錐射は同じ原二射と独立u正方形から]
    unresolved: []
  proof_use:
    used: [Mのrawセル像/none分類/出現位置と支持証拠、支持包含hab、元Phiの両微分、原B/D/Vとそのsquare-zero、既存ε次数単射・実H1商・元SES短完全性・原Q/R両方向同定、G133の同じ錐二座標と標準δ自然性]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [下記24単一file focused/全明示print/標準公理、共通scanと静的方向228module]
  blocking_findings: [初回四本の非中心F1は名指しAPIとproofで対応済み。指摘対象外report変更により直接対応資格喪失。D1を復元し新規正式四本再実行1/2とroot acceptanceは後続]
  next_obligation: Dの同じLaw全発生ラベル台射とG134保存操作/有限合成を原P/fiber/τへ接続し、B/E有限判定とW全指定例へ進む
```

## Cycle 12の生成・使用経路

`supportCellInclude`は元の選択セル名と支持証拠を保持する。左右端点、三辺、三頂点、
`IncHom`の全出現を保持し、原carrierの等号から実`StructuredArrow.map₂`を作る。
係数制限は元の右Kan/極限/CC値の両方向同型を使う前合成であり、追加セルにより
成分が合流する場合も同型とは仮定しない。原P・η・εの定義と独立uを交換しない。

原細chain包含はL₀の垂直端点像、L₁の垂直辺と混在面全微分、L₂の全退化面を保つ。
全整数次数の原L→元細chainの包含図式と、literal K′/Lの両微分・同じP双対を照合した。
Φの元細セル包含は原none条件と粗chart像を保つ。B/D/Vを全基底で保存し、
原混在閉路Dyと原V像の同じ商からraw κと全Φ κの可換性を証明した。
全Φ dualの自然性は原単一fiber類への実評価と同じ閉chain/cochain代表で照合する。
これにより直接Φ H¹制限がliteral κ*核Rを保ち、原Q-H¹-R座標制限と一致する。

原SESの射からmathlibのnative δ自然性を全ℤ・全元で導き、次数1を同じR座標のτへ戻す。
三錐は元η・ε・独立uの正方形から生成した実mappingCone.mapである。
全二座標、原triangle三射、第三射の標準shift負号、原fiber錐→Q評価と全連結射を保持する。
主制限の恒等・合成則は元cochain Homと同じ商・mappingConeの関手性で確認した。
空Aの三次数P制限とliteral Rを元選択支持証拠から明示検証した。

`M`の原始incidence/支持整合、有限な元nerve、`hab : A ⊆ B`は許された入力。
新たなexactness、natural transformation、H¹同型、期待rank、有限Sourceの仮定は受け取らない。
閉路・実微分像・quotient membershipの証拠は同じ原写像の可換式で生成して使用した。
C1–11の主定義・既存theorem signatureを変更せず、所有fileへ公開計算APIを追加した。
既存Carrierの3生成補助宣言も明示printへ追加し、既存ownerのprint順をsource順へ揃えた。
既存受理spineは各当時のcommitを読む。現在のowner再検証spineは下表へ固定する。

## Cycle 12検証と未実施項目

24対象を実装段階ごとに単一非aggregate fileのfocused checkで検証し、全てwarning/error0。
全495source宣言と18生成宣言（合計513）の明示#print、実出力、各module auditが一致する。
source宣言の相対順はprint/logの相対順と一致し、生成宣言の位置も下記spineに固定する。
新source314、新生成15、既存ownerの生成3を含む。全宣言は標準三公理
`propext`・`Classical.choice`・`Quot.sound`の部分集合のみ。空選択セルの矛盾は公理依存なし。
18新moduleはmanifestとAG直接静的importに各1件登録し、aggregateをelaborateしない。
静的Research import directionは228modulesで成功。必要な単一cacheのみを生成し、全体buildはしない。
共通diff/hidden・BiDi/placeholder/privacy/語彙/逆import scanと登録照合は下記記録へ固定する。
GOAL/design/Formalは不変。Research full/aggregate/全file loop、local lake build、
Formal実build/移植、別最終完了4査読は未実施。全GOALはtarget-proof-checkpoint。

## Cycle 12 初回PR査読とF1対応

初回固定head `2809851c60ccf638be6da28c6d0615b349726888` のPR5303を
standard review-prからmath-lean-reviewへ委譲し、新規独立4本を一括実行した。
数学A・LeanAはNo major findings、数学B・LeanBはMinor issues。中心finding0、
両Bの非中心重複指摘をF1として統合した。初回headは未解消のためmergeしない。
[数学2票全文](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5303#issuecomment-6056559053)、
[Lean2票全文](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5303#issuecomment-6056562971)、
[初回標準・root監査](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5303#issuecomment-6056566420)。

F1は別ownerの`supportAllPhiHomology`一般値を下流で展開する点と、既存
`cyclesMap_apply`・`supportPhiHom_f1`・`supportQHom_f1`を未使用の点である。
名指しの公開API `supportAllPhiHomology_apply` を所有fileに追加し、
SupportPhiEmbedding・SupportFiberの下流proofをそのAPI経由へ変更した。
SupportPhiHomology・SupportFiberの閉cochain代表は既存cyclesMap/f1 APIを使用する。
既存statement、def/instanceの値、import、宣言、GOAL/designと台帳statusは維持する。
追加APIと変更三fileを単一focusedで再確認し、下記spineへ同順序で同期した。
新規単一subagentは修正head `8668453458ec68afe97e218efe0f6fd452e06320` のF1全箇所解消を確認した。
reportの指摘対象外namespace説明削除・表header変更D1（非中心）が直接対応の範囲条件を満たさず、
このheadの直接対応資格は喪失した。D1二箇所を初回値へ戻し、固定修正headへ新規4本の
正式再実行1/2を行う。中心findingは出ていないが、単一確認を承認としない。
[直接対応確認全文](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5303#issuecomment-6056798254)。

初回headの24focused/512printは当該監査コメントのhashで固定し、以下は修正後の
24focused/513printへ更新する。変更三file以外のsourceとlogは同一であり、全file loopは行わない。
初回CIは全8SUCCESS（Lean37752939388/Tool37752939737）。Research実steps成功、
Formal setup/cache/build/kernel/premise実steps SKIPPED。修正headのCIは別途確認する。
全GOALはtarget-proof-checkpoint、completion_candidate:no、Formalはunported。

## Cycle 12 正式再実行1とF2・F3対応

固定head `362401c8efc7539a4e87c6c4a7eb19c242440f12` の新規独立数学2・Lean2を
一括取得した。数学AはMinor issues（中心0・非中心2）、数学B・LeanBは
Minor issues（各0・1）、LeanAはNo major findings（0・0）。正式再実行は1/2。
[数学二票全文](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5303#issuecomment-6057047692)、
[Lean二票全文](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5303#issuecomment-6057061818)、
[標準/root監査](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5303#issuecomment-6057062271)。

重複を統合した非中心F2は、冒頭の現在状態が初回正式査読を未実施とする点である。
初回・再実行1の実施と指摘対応確認待ちを区別する文言へ同期した。
非中心F3はSupportPhiEmbeddingのsupportPhiVerticalCycles_val proofで、
別ownerのphiVerticalCyclesEquiv値をchangeで読む点である。
既存公開phiVerticalCyclesEquiv_valを明示rwしてから同fileの局所表示を合わせた。
修正は一つの既存proof内部と指摘された現況・その証拠記録だけであり、
宣言追加・削除、既存statement、def/instance値、import、台帳statusの変更はない。
変更一fileのfocusedはwarning/error0・全9宣言標準公理のみ。
他23sourceと実logは同一、513件spineと対応を維持する。
新規単一subagentの直接対応確認を受け、資格と全指摘解消を別途判定する。
全GOALはtarget-proof-checkpoint、completion_candidate:no、Formalはunportedを維持する。

<!-- cycle12-generated-evidence -->

| file | 宣言（source/print/log/report相対順、生成宣言を含む） |
| --- | --- |
| `CarrierFunctor.lean` | `incidencePositionComp`, `incHomCode_comp`, `incHomCode_eqToHom`, `incHomCode_eqToHom_comp`, `incHomCode_comp_eqToHom`, `Carrier.endpointHom_of_some`, `Carrier.endpointHom_of_none`, `Carrier.edge_of_face_some`, `Carrier.mappedFaceEdgeHom`, `Carrier.endpointHom_code_some`, `Carrier.endpointHom_code_none`, `Carrier.mappedFaceEdgeHom_code`, `Carrier.endpoint_face_some_code`, `Carrier.face_none_edge0_some`, `Carrier.face_none_edge0_none`, `Carrier.vertical_edge_eq_face`, `Carrier.verticalFaceEdgeHom`, `Carrier.mixedLeftFaceEdgeHom`, `Carrier.mixedRightFaceEdgeHom`, `Carrier.verticalFaceEdgeHom_code`, `Carrier.mixedLeftFaceEdgeHom_code`, `Carrier.mixedRightFaceEdgeHom_code`, `Carrier.edgeHom`, `Carrier.faceVertexHomPosition`, `Carrier.endpoint_edgeHom_code`, `Carrier.incidenceData`, `Carrier.functor`, `Carrier.functor_obj_chart`, `Carrier.functor_obj_edge`, `Carrier.functor_obj_face`, `Carrier.functor_map_chartEdge`, `Carrier.functor_map_edgeFace`, `Carrier.preimageFunctor`, `Carrier.preimageFunctor_obj_chart`, `Carrier.preimageFunctor_obj_edge`, `Carrier.preimageFunctor_obj_face`, `Carrier.preimageFunctor_map_chartEdge`, `Carrier.preimageFunctor_map_edgeFace`, `Carrier.preimageFunctor_obj_edge_of_some`, `Carrier.preimageFunctor_obj_edge_of_none`, `Carrier.preimageFunctor_obj_face_of_some`, `Carrier.preimageFunctor_endpoint_of_some`, `Carrier.preimageFunctor_endpoint_of_none`, `Carrier.preimageFunctor_face_edgeMap_of_some`, `Carrier.preimageFunctor_face_edge_of_some`, `Carrier.preimageFunctor_face_edgeHom_of_some`, `Carrier.edgeHom_code_of_mixed_left`, `Carrier.edgeHom_code_of_mixed_right`, `Carrier.preimageFunctor_face_edgeHom_of_mixed_left`, `Carrier.preimageFunctor_face_edgeHom_of_mixed_right`, `Carrier.preimageFunctor_map_edgeFace_code_of_some`, `Carrier.preimageFunctor_map_chartFace`, `Carrier.preimageFunctor_map_chartFace_code`, `Carrier.preimageFunctor_map_chartFace_code_of_some`, `Carrier.preimageFunctor_face_vertex_of_some`, `Carrier.preimageFunctor_face_vertexHom_of_some`, `Carrier.preimageFunctor_edge_endpoint_of_some`, `Carrier.preimageFunctor_map_chartEdge_code_of_some`, `Carrier.preimageFunctor_map_edgeFace_code_of_mixed_left`, `Carrier.preimageFunctor_map_edgeFace_code_of_mixed_right`, `Carrier.preimageFunctor_map_chartFace_code_of_mixed_left`, `Carrier.preimageFunctor_map_chartFace_code_of_mixed_right`, `Carrier.preimageFunctor_map_chartEdge_code_of_none`, `Carrier.preimageFunctor_map_edgeFace_code_of_vertical`, `Carrier.preimageFunctor_map_chartFace_code_of_vertical`, `Carrier.edge.congr_simp`, `Carrier.mixedLeftFaceEdgeHom.congr_simp`, `Carrier.mixedRightFaceEdgeHom.congr_simp` |
| `PushforwardCoefficient.lean` | `structuredArrowFinite`, `commaConnectedComponentsFinite`, `coefficientPushforwardFiniteDimensional`, `pushforwardCoefficients`, `pushforwardCoefficients_map_component_eval`, `pushforwardCounit`, `pushforwardIsRightKanExtension`, `pushforwardCoefficientFiniteDimensional` |
| `PushforwardComplex.lean` | `CoefficientC0`, `CoefficientC1`, `CoefficientC2`, `coefficientD0`, `coefficientD1`, `coefficient_chart_transport`, `coefficient_edge_transport`, `coefficient_endpoint_chart_eval`, `coefficient_face_edge_eval`, `endpoint_edge_normal`, `coefficient_endpoint_edge_eval`, `coefficient_d1_comp_d0`, `coefficientComplex`, `coefficientComplex_d0`, `coefficientComplex_d1`, `coefficientComplex_d0_apply`, `coefficientComplex_d1_apply`, `pushforwardComplex`, `pushforwardComplex_d0_apply`, `pushforwardComplex_d1_apply` |
| `LocalFiber.lean` | `PhiChart`, `PhiEdge`, `PhiFace`, `GammaVertex`, `GammaEdge`, `LambdaFace`, `phiEndpoint`, `phiEndpoint_val`, `phiFace_edge_chart`, `phiFace_edge_none`, `phiFaceEdge`, `phiFaceEdge_val`, `gammaSource`, `gammaTarget`, `gammaBoundary`, `gammaBoundary_single`, `phiD0`, `phiD1`, `phiD0_apply`, `phiD1_apply`, `phiD1_comp_phiD0`, `phiComplex`, `phiComplex_d0`, `phiComplex_d1`, `phiComplex_C1_subsingleton`, `phiCellObj`, `phiCellObj_chart`, `phiCellObj_edge`, `phiCellObj_face`, `phiCellObj_injective`, `PhiInc`, `phiCellObj_carrier`, `gammaCellObj`, `gammaCellObj_inl`, `gammaCellObj_inr`, `gammaCellObj_injective`, `GammaInc`, `gammaCellObj_carrier`, `lambdaFace_carrier`, `phiBoundary1`, `phiBoundary2`, `phiBoundary1_single`, `phiBoundary2_single`, `phiBoundary1_dual`, `phiBoundary2_dual`, `phiBoundary1_comp_phiBoundary2`, `phiEmbed0`, `phiEmbed1`, `phiEmbed2`, `phiEmbed_comm1`, `phiEmbed_comm2`, `phiEmbed0_injective`, `phiEmbed1_injective`, `phiEmbed2_injective`, `phiIncFinite`, `gammaIncFinite`, `lambdaFaceFinite`, `gammaSource_val`, `gammaTarget_val_of_left`, `gammaTarget_val_of_right`, `GammaGraph`, `gammaGraphQuiver`, `gammaGraphFinite`, `gammaGraphHomFinite`, `gammaGraphArrow`, `gammaGraphArrow_val` |
| `DegenerateChain.lean` | `chainDegreeDifferential_out`, `degenerateDegreeObject`, `degenerateDegreeObject_out`, `degenerateDegreeDifferential`, `degenerateDegreeDifferential_out`, `degenerateDegreeDifferential_square`, `degenerateChain`, `degenerateDegreeInclusion`, `degenerateDegreeInclusion_out`, `degenerateDegreeInclusion_comm`, `degenerateChainInclusion`, `degenerateChainInclusion_f`, `degenerateChainInclusion_comparison_zero`, `degenerateChainInclusion_mono`, `degenerateZeroShort`, `degenerateZeroScIso`, `degenerateZeroShort_exact`, `degenerateChain_H0_isZero` |
| `FiberCohomology.lean` | `phiDualCochainEquiv`, `phiHomologyDualEquiv`, `phiHomologyDualEquiv_mk`, `allPhiHomologyDualEquiv`, `allPhiHomologyDualEquiv_apply`, `allPhiHomologyDualEquiv_single`, `phiCohomologyVerticalDualEquiv`, `phiCohomologyVerticalDualEquiv_apply`, `kappaStar`, `kappaStar_apply`, `kappaStar_raw`, `R`, `fiberR_eq_ker`, `kernelEquivOfEquiv`, `fiberRRawEquiv`, `fiberRRawEquiv_val` |
| `SupportCells.lean` | `supportCellInclude`, `supportCellInclude_val`, `supportCellInclude_refl`, `supportCellInclude_comp`, `supportSelectedRestrict_apply`, `supportCellInclude_endpoint`, `supportCellInclude_faceEdge`, `supportCellInclude_faceVertex`, `supportIncObj`, `supportIncMap`, `supportIncMap_code`, `supportIncFunctor`, `supportIncFunctor_obj`, `supportIncFunctor_obj_chart`, `supportIncFunctor_obj_edge`, `supportIncFunctor_obj_face`, `supportIncFunctor_map_chartEdge`, `supportIncFunctor_map_edgeFace`, `supportIncFunctor_map_chartFace`, `supportIncFunctor_map_code`, `supportIncFunctor_refl`, `supportIncFunctor_comp`, `supportChainInclude_single`, `supportChainInclude_boundary1`, `supportChainInclude_boundary2` |
| `SupportCarrier.lean` | `supportPreimageInclude`, `supportPreimageInclude_apply`, `supportCarrier_chart`, `supportCarrier_edge`, `supportCarrier_face`, `supportCarrier_obj`, `supportCarrierEndpointPosition`, `supportCarrierFaceEdgePosition`, `supportCarrierFaceVertexPosition`, `supportCarrierEndpointPosition_eq`, `supportCarrierFaceEdgePosition_eq`, `supportCarrierFaceVertexPosition_eq`, `supportCarrier_map_code`, `supportCarrierIso`, `supportCarrierIso_hom_app`, `supportCommaFunctor`, `supportCommaFunctor_obj_right`, `supportCommaFunctor_obj_hom` |
| `SupportCoefficients.lean` | `componentFunctionRestrict`, `componentFunctionRestrict_apply`, `componentFunctionRestrict_refl`, `componentFunctionRestrict_comp`, `supportCoefficientRestrict`, `supportCoefficientRestrict_component`, `supportCoefficientRestrict_eval`, `supportCommaFunctor_precomp`, `supportCoefficientRestrict_natural`, `supportCoefficientsRestriction`, `supportCoefficientsRestriction_app` |
| `SupportDegenerate.lean` | `supportVerticalEdgeInclude`, `supportVerticalFaceInclude`, `supportMixedFaceInclude`, `supportDegenerateFaceInclude`, `supportVerticalEdgeInclude_val`, `supportVerticalFaceInclude_val`, `supportMixedFaceInclude_val`, `supportDegenerateFaceInclude_val`, `supportVerticalEdgeChainInclude`, `supportVerticalEdgeChainInclude_single`, `supportVerticalEdgeChainInclude_inclusion`, `supportVerticalFaceChainInclude`, `supportVerticalFaceChainInclude_single`, `supportVerticalFaceChainInclude_inclusion`, `supportMixedFaceChainInclude`, `supportMixedFaceChainInclude_single`, `supportMixedFaceChainInclude_inclusion`, `supportDegenerateFaceChainInclude`, `supportDegenerateFaceChainInclude_single`, `supportDegenerateFaceChainInclude_inclusion`, `supportDegenerateL0_mem`, `supportDegenerateL1_mem`, `supportDegenerateL2_mem`, `supportL0Include`, `supportL1Include`, `supportL2Include`, `supportL0Include.congr_simp`, `supportL0Include_val`, `supportL1Include.congr_simp`, `supportL1Include_val`, `supportL2Include.congr_simp`, `supportL2Include_val`, `supportLInclude_boundary1`, `supportLInclude_boundary2`, `supportL0Include_refl`, `supportL0Include_comp`, `supportL1Include_refl`, `supportL1Include_comp`, `supportL2Include_refl`, `supportL2Include_comp` |
| `SupportPushforward.lean` | `supportPushforward0`, `supportPushforward1`, `supportPushforward2`, `supportPushforward0_apply`, `supportPushforward1_apply`, `supportPushforward2_apply`, `supportCoefficientRestrict_endpoint`, `supportCoefficientRestrict_faceEdge`, `supportPushforward_comm0`, `supportPushforward_comm1`, `supportPushforwardHom`, `supportPushforwardHom_f0`, `supportPushforwardHom_f1`, `supportPushforwardHom_f2`, `supportCoefficientRestrict_constant`, `supportUnit0`, `supportUnit1`, `supportUnit2`, `supportUnitHom`, `supportCommaFunctor_transport`, `supportCoefficientEvaluationAt`, `supportEvaluation0`, `supportEvaluation1`, `supportEvaluation2`, `supportEvaluationHom`, `supportPushforward0_refl`, `supportPushforward0_comp`, `supportPushforward1_refl`, `supportPushforward1_comp`, `supportPushforward2_refl`, `supportPushforward2_comp`, `supportPushforwardHom_refl`, `supportPushforwardHom_comp`, `supportDirectHom`, `supportPushforward2.congr_simp`, `supportIncFunctor.congr_simp`, `supportPushforward1.congr_simp`, `supportCellInclude.congr_simp`, `supportPushforward0.congr_simp`, `supportPushforwardHom.congr_simp` |
| `SupportQRestriction.lean` | `supportQ0`, `supportQ0_apply`, `supportQ1`, `supportQ1_apply`, `supportQ2`, `supportQ2_apply`, `supportQ_comm0`, `supportQ_comm1`, `supportQHom`, `supportQHom_f0`, `supportRestriction0`, `supportQ0_refl`, `supportQ0_comp`, `supportQHom_f1`, `supportRestriction1`, `supportQ1_refl`, `supportQ1_comp`, `supportQHom_f2`, `supportRestriction2`, `supportQ2_refl`, `supportQ2_comp`, `supportRestrictionHom`, `supportQHom_refl`, `supportQHom_comp`, `supportQ0.congr_simp`, `supportQ1.congr_simp`, `supportQ2.congr_simp`, `supportQHom.congr_simp` |
| `SupportConnecting.lean` | `supportEvaluationRestrictionMorphism`, `supportEvaluationRestrictionMorphism_τ1`, `supportEvaluationRestrictionMorphism_τ2`, `supportEvaluationRestrictionMorphism_τ3`, `supportConnecting_delta`, `supportRRestriction`, `supportRRestriction_apply`, `supportRRestriction_viaQ`, `supportRRestriction_refl`, `supportRRestriction_comp`, `supportConnecting_tau`, `supportEvaluationH1`, `supportFiberRestrictionH1`, `supportEvaluationH2` |
| `SupportPhiCells.lean` | `supportPhiChartInclude`, `supportPhiEdgeInclude`, `supportPhiFaceInclude`, `supportPhiChartInclude_val`, `supportPhiEdgeInclude_val`, `supportPhiFaceInclude_val`, `supportPhiChartInclude_endpoint`, `supportPhiEdgeInclude_faceEdge`, `supportPhiChain0`, `supportPhiChain0_single`, `supportPhiChain1`, `supportPhiChain1_single`, `supportPhiChain2`, `supportPhiChain2_single`, `supportPhiChain_boundary1`, `supportPhiChain_boundary2` |
| `SupportPhiRestriction.lean` | `supportPhi0`, `supportPhi0_apply`, `supportPhi0_dual`, `supportPhi1`, `supportPhi1_apply`, `supportPhi1_dual`, `supportPhi2`, `supportPhi2_apply`, `supportPhi2_dual`, `supportPhi_comm0`, `supportPhi_comm1`, `supportPhiHom`, `supportPhiHom_f0`, `supportPhiHom_f1`, `supportPhiHom_f2`, `supportAllPhiH1`, `supportAllPhiH1_apply`, `supportPhiH1_mk`, `supportPhiHom_refl`, `supportPhiHom_comp`, `supportAllPhiH1_refl`, `supportAllPhiH1_comp` |
| `SupportFiberChains.lean` | `supportHorizontalEdgeInclude`, `supportHorizontalEdgeInclude_val`, `supportHorizontalEdgeChainInclude`, `supportHorizontalEdgeChainInclude_single`, `supportVerticalEdgeProjection`, `supportHorizontalEdgeProjection`, `supportVerticalEdgeBoundary`, `supportMixedVerticalBoundary`, `supportMixedHorizontalBoundary`, `supportMixedCyclesInclude`, `supportMixedCyclesInclude_val`, `supportVerticalCyclesInclude`, `supportVerticalCyclesInclude_val`, `supportMixedCycleToVertical` |
| `SupportVerticalHomology.lean` | `supportVerticalBoundary`, `supportVerticalBoundaryToCycles`, `supportVerticalHomology`, `supportVerticalHomology_mk`, `supportRawKappa` |
| `SupportPhiHomology.lean` | `supportPhiCycles`, `supportPhiCycles_val`, `supportPhiBoundaryToCycles`, `supportPhiHomology`, `supportPhiHomology_mk`, `supportPhiHomologyDual`, `supportAllPhiHomology`, `supportAllPhiHomology_apply`, `supportAllPhiHomology_mk`, `supportKappa` |
| `SupportPhiEmbedding.lean` | `supportPhiVerticalEmbed`, `supportPhiVerticalEmbed_single`, `supportPhiVerticalEmbed_coordinates`, `supportPhiVerticalCycles`, `supportPhiVerticalCycles_val`, `supportPhiVerticalHomology_mk`, `supportPhiVerticalEmbed_include`, `supportPhiVerticalCycles_include`, `supportAllPhiHomology_single` |
| `SupportFiber.lean` | `supportAllPhiHomologyDual`, `supportKappaStar`, `supportFiberR`, `supportFiberR_val`, `supportPhiVerticalDual`, `supportVerticalCycleInclusion`, `supportQRawR`, `supportFiberR_eq_supportRRestriction`, `supportFiberR_tau`, `supportFiberR_refl`, `supportFiberR_comp`, `supportFiberR_fiveTerm` |
| `SupportQuotient.lean` | `supportQuotient0`, `supportQuotient0_mk`, `supportQuotient1`, `supportQuotient1_mk`, `supportQuotient2`, `supportQuotient2_mk`, `supportQuotient_boundary1`, `supportQuotient_boundary2`, `supportEvaluationQuotientDual0`, `supportEvaluationQuotientDual1`, `supportEvaluationQuotientDual2` |
| `SupportCones.lean` | `supportStandardUnit`, `supportStandardEvaluation`, `supportStandardDirect`, `supportCoefficientCone`, `supportCoefficientCone_apply`, `supportFiberCone`, `supportFiberCone_apply`, `supportTotalCone`, `supportTotalCone_apply`, `supportConeTriangle_first`, `supportConeTriangle_second`, `supportConeShift_apply`, `supportConeTriangle_third`, `supportConeTriangle`, `supportFiberConeDesc`, `supportFiberConeHomologyEquiv`, `supportFiberConeConnecting`, `supportCoefficientCone_refl`, `supportCoefficientCone_comp`, `supportFiberCone_refl`, `supportFiberCone_comp`, `supportTotalCone_refl`, `supportTotalCone_comp` |
| `SupportStandardChains.lean` | `supportFineDegreeInclude`, `supportFineDegreeInclude_comm`, `supportFineChainInclude`, `supportFineChainInclude_f`, `supportDegenerateDegreeInclude`, `supportDegenerateDegreeInclude_comm`, `supportDegenerateChainInclude`, `supportDegenerateChainInclude_f`, `supportDegenerateChainInclusion`, `supportDegenerateChainInclude_refl`, `supportDegenerateChainInclude_comp`, `supportFineDegreeInclude.congr_simp`, `supportDegenerateDegreeInclude.congr_simp` |
| `SupportEmpty.lean` | `supportSelected_empty`, `supportPushforward0_empty`, `supportPushforward1_empty`, `supportPushforward2_empty`, `supportFiberR_empty_subsingleton`, `supportFiberR_empty` |

全namespaceは`AAT.AG.AtlasCoefficientFiber`（`CarrierFunctor`の局所名は`Carrier`を含む）。

| file / source+生成数 | source SHA-256 | focused output SHA-256 |
| --- | --- | --- |
| `CarrierFunctor.lean` / 65+3 | `8d95fcf2401342e053c937479b6d6501eafc78223f141e8ceb6d0475a8156ff4` | `49c6e34af5c63a95f75846a7d41af370b4738ce552f65e89e586d493d23dea69` |
| `PushforwardCoefficient.lean` / 8+0 | `5b5eef702a4ee569a9fbc4d59f7e1720987aa19b72bb0a0f013473c1387053a9` | `3d36788e7009d4843a428b9d7ce9cee585636e363fbd56f07fae622e72468da8` |
| `PushforwardComplex.lean` / 20+0 | `d9a640dec22caae23efc7518a600e587fa0b643523376ea63848f40648865332` | `c8407ab60f606c777c9407eac7fc9d1ba5e2d8f9f36d38e903ff8b3815a6a110` |
| `LocalFiber.lean` / 66+0 | `cfc7d3a3d44a78879840daae8cf5a846510813156598c1006e9686c1b68013a4` | `67b85bf4638f505fcab9f73bd1c3fcf8aa8ff7a3edce81e754e45c2cda8828a4` |
| `DegenerateChain.lean` / 18+0 | `e0c0ff0004e9203f8dbb434cff0f2e762482acff99d190241d2349e8d63245f9` | `89b06cbbb9ff8b838b3121beca0709cb8fccf49ee62d9027c1638c33ecd25320` |
| `FiberCohomology.lean` / 16+0 | `74aa1f4930cbd01151d5c1792d76c43324208de1c0a795924312885b97fb6951` | `080cb930d8e705f1c6263ff4614329c15c4673313a2f13190a2fb2c572df3405` |
| `SupportCells.lean` / 25+0 | `14184eda8128449cf883983404a727db95069286e71cfe530f2023ff6fac8ae0` | `186e43b78fbd899653a55901b1a1cede78c9cc26d8ca5131a1d59d1ba1f2c298` |
| `SupportCarrier.lean` / 18+0 | `144d9928d05eecb0d518fac91d9d7066aaf0f0ff90b0371e67534a0767e85aff` | `44e998ea42ef19cad95598695e0adc7f2fd0b7ca7229f26df0ccf4dba85b92a4` |
| `SupportCoefficients.lean` / 11+0 | `6378cd9e90347b20759660d53a37f3ee48083d17838870393a87348f05de25eb` | `a302cc2916ddacabab0dc0f6bcd065fff80dbc2d232b0404f1b2beba79204dc3` |
| `SupportDegenerate.lean` / 37+3 | `69757c0b2ab7bad9f0bb95b8b85bbab25cf7fdb947973f76e28a8c3afbe447da` | `001cc0b7b381e36bed31a019231c8cd14d6d90a7a324e05bb1323a76a33d5704` |
| `SupportPushforward.lean` / 34+6 | `3be355a7717ac230fff849b5fbec0601bf8d795b45c7dba91f25bfb1e9c36169` | `273d9d752e94b5eebc891a872cf8f623a3d206d33febbcc874ee4a43fd56880f` |
| `SupportQRestriction.lean` / 24+4 | `d41fb4b8c49689ecfef03dc2b07843d9b15b5d1186134fe9581febaedeba0e0c` | `4f860f2f44c7deef872e018a137d5c8df1ab7b76b5a47fc96e8117235d1da53c` |
| `SupportConnecting.lean` / 14+0 | `19acec6ac58e312956881f59e32cf9713b7ed7f01a2440ea2835ed24f09264ee` | `c67d5874614af3ec82cb469876d884076a211fb725d7de937e3735f7b4565baf` |
| `SupportPhiCells.lean` / 16+0 | `68d02c534ea9b189a2f3be6a58ac8afab22bb23496f47ce48aabbfe18a99846a` | `7b0b3d06974859fbd0b3d4fe5a255cac923f8af9d4ee2e43455d8f45e6fba977` |
| `SupportPhiRestriction.lean` / 22+0 | `cde020ba4b6d14845b757e5edeeb5877c5ac936a83ef0205cc5f054a3da3f819` | `22d62540c96f795614668e59c442d503728f10721ffff391eae436c412b1e0f9` |
| `SupportFiberChains.lean` / 14+0 | `7f874a115e2ac29a505b6b85c3b354bb2dac9fe3e5875f04d4eaf7bfc469bd3e` | `c2532a34df73d70e2dc72c9ffa3ed8bcd10d70b41d034b0612c56dec2c028a52` |
| `SupportVerticalHomology.lean` / 5+0 | `dba8c7ebad20d478a1c72e487dfee3696c1a3dc152a12dc92c12e0061f9250d6` | `1f9d99671d8614e4b8a19c719edf692b6ddcc8168826176c0adb055536262db3` |
| `SupportPhiHomology.lean` / 10+0 | `925c9d40532ab85cdf06392cd35a32d0cb4ccd21910504da2d8390f7a8402e57` | `40da1902df25eabbee8e3eb753c46321852818d9d6810c069069f3a2dc9c47a0` |
| `SupportPhiEmbedding.lean` / 9+0 | `70a36346b1c558a1e37ce0232d666886ef84fb56f387a9c98a024490019a1148` | `f6baf2fb5047578dabd1a77c3f1fb3a1f37fe91322ff8b9bbfee4a3c36ff32f8` |
| `SupportFiber.lean` / 12+0 | `a78d9a4757bbbee0d934325a4f50e11029ac17b51b90e83aa8c27c412e0ffa8f` | `bca0099ab692f47b53e86e136185ad8e9ee65ab0fced176cd18de3c44ab66305` |
| `SupportQuotient.lean` / 11+0 | `4d4a3c64b0ef61df2475243d9fa36c666599ed9f6f0323e1d73acfd8558133de` | `f72724dd55001ffae9587b15b5e6937eb8f6afcc3d73173fc409987b146db512` |
| `SupportCones.lean` / 23+0 | `3f68f121e86eb3148542a81835c77787abb0c22dad022509e59642ee5be79a33` | `3817ad1bce7c83755535f76ed9b68f58255e88f5cf637532dd89532c97192d5b` |
| `SupportStandardChains.lean` / 11+2 | `814be9ce33abbf089d13fcd70db338c41adb04a5f6590358a0d107b44f1155ca` | `ed7fae64a3c9ff2ab670787b1c02d6cb108c4705dfbde3a2550cec391ae33f9b` |
| `SupportEmpty.lean` / 6+0 | `4c36a926bde0c7bb45685a36b5a8eaba203808bd45946d030bab5224f0889ef3` | `de0cb5a3b80ad0661b9379b8fc8820ae1d575a6759545db440e779bf655ef563` |

validation `.tmp/g135/cycle12-validation.json` SHA-256 `a817f1b53076d8695678e598a53595ac733402361cf75def2a23e36f7578234e`。
scan `.tmp/g135/cycle12-scans.json` SHA-256 `0bc92f804a44a42de4361da2a63c7a7ea8bd754c37dbb540537d198ba11b00f6`。


## Cycle 12受理・merge同期

PR [#5303](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5303)、最終head
`70633bfc653fe823fbdbbbcec8b1d6fc12a5bb5b`、merge
`9abbeb4ad0578e7aca653a11353707c268db2179`、2026-10-08T09:50:58Z。
[最終標準/root受理](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5303#issuecomment-6057242603)、
[正式再実行1数学](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5303#issuecomment-6057047692)、
[同Lean](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5303#issuecomment-6057061818)、
[有資格単一確認](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5303#issuecomment-6057242158)、
[Issue同期](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5290#issuecomment-6057258648)。
六固定終了条件はapprove / proof-obligation-discharged。初回F1対応後のreport対象外D1は
資格喪失・復元・正式再実行1/2を経た。再実行全四票の中心0、非中心F2/F3を
新規単一確認が資格内/実体解消と確認、新finding0。513件（495source+18生成）の
実#print/log/module audit/report順・hash一致、標準三公理のみ、warning/error0。
最終validation SHAa817f1b53076d8695678e598a53595ac733402361cf75def2a23e36f7578234e、
scan SHA0bc92f804a44a42de4361da2a63c7a7ea8bd754c37dbb540537d198ba11b00f6。
最終head8checksSUCCESS、Lean37758421348/Tool37758421096 exacthead一致。
Research実steps成功、Formal実build/kernel/premiseはSKIPPED。
全GOALはcheckpoint、Formal unported。全体/aggregate/全fileloop/local lake buildと別final未実施。

## Cycle 13 selection

```yaml
ledger_type: target_cycle_result
goal: G-135-aat-atlas-coefficient-fiber
cycle: 13
goal_blob_sha: cd5f3e684b7f390558796797874a1f16b52a6b18
base_oid: 9abbeb4ad0578e7aca653a11353707c268db2179
tracking_issue: 5290
report_path: research/reports/G-135-aat-atlas-coefficient-fiber.md
selection:
  proof_state_ref: Cycle12受理/Issue6057258648とDのLaw全ラベル台図式未完行
  proof_dag_predecessors: [原Law全射/原κRτ/標準三錐 C11, 原primitive支持自然性 C12, G133有限複体族と元錐座標, G134同じ実Law生成比較]
  milestone: GOAL D・designREADME§5のLaw分解と全台制限を同じ原Law全射へ接続する
  proof_obligations: [原Law各発生ラベルから任意A部分台への実projection, 原Lawκ/κstarと直接Phi台制限, literalLawRから同じR_Aへの全値とQ座標一致, 原LawSESδ/τ/五項全射とη独立u正方形, 元三Law錐/合成triangleから同じ原A錐への全次数射, 全ラベル族の図式と恒等合成/重複/空Law保存]
  exit_criteria:
    - 任意M/粗adequate Law/全発生ラベルl/任意A包含A_lについて原Lawから同じ原P_A/細cochain/Q_Aと粗cochainへの射を生成し、元canonical projectionと支持制限の全Hom/全三次数値を証明する
    - 原Lawκ/κstarの同じ混在閉路/原Phi値は台包含と可換であり、literalLawRの直接Phi制限から同じR_Aへ生成した射が原Q-H1-R制限と全元で一致する
    - 元Law短完全列から同じ原A短完全列への実射でnativeδ全ℤ/同じτを自然にし、η/ε/独立generatedComparisonHomと五項列の全実射を保持する
    - 元三Law標準錐から同じ原三A錐へのmappingCone射を生成し、全ℤ二座標/三triangle射/shift負号/元Qdescと標準連結射の対応を証明する
    - 任意のラベル別部分台族と包含に上の全図式を集め、原Law分解と同じ全族制限を可換にする。A_lそのものではC11原同型へ戻り、支持包含の合成・空支持・空Law・同じ台のラベル重複を保持する
    - 供給自然性/同型/期待rankを受けず、原Law値型有限性を課さず、同じ原始Mから全構成・値・両方向座標・標準API/全宣言公理/依存を監査する
  selection_reason: 受理した原Law分解とprimitive全台自然性を同じ全射で接続し、全発生ラベルでの保存操作/有限判定に渡す
  expected_result_type: proof-obligation-discharged
  lean_targets: [LawSupportProjection, LawSupportFiber, LawSupportConnecting, LawSupportCones, LawSupportFamilies]
  risks: [Law値型全体の有限性追加, ラベルを同じ台で同一視, arbitrary中間Pへ置換, 全HomをH1のみへ縮小, literalR直接値をQ由来定義だけで代替, shift負号/恒等合成欠落]
  unchecked: [六終了条件の実装/検証/正式PR受理は未完, G134/B-E/W/全GOAL別finalは後続]
```

## Cycle 13 証拠の構成経路

原Lawの `lawEvaluationRestrictionFamilyIso` と同じ各ラベルの
`supportEvaluationRestrictionMorphism` から実SES射を合成する。
左・中・右成分は原Law P・細cochain・Qから同じ原Aの三対象へ向かう全次数Homである。
粗側も元canonical族射影と `subsetRestrictHom` から作る。
`lawSupportUnit`・`lawSupportEvaluation`・`lawSupportDirect` は元η・εと
独立 `generatedComparisonHom` の全Hom正方形であり、H¹だけの置換をしていない。
`lawSupportP/Fine/Q/Coarse_component_apply` は全整数次数の原ラベル値とprimitive制限を読む。

κは同じ混在閉路を元ラベルへ含める射と原Φ H₁包含で照合する。
κ*は原Φ cochain H¹の直接制限と混在閉路包含の双対で照合する。
literal `lawR` から `R M A` への `lawSupportR` は `supportFiberR` による直接Φ制限であり、
`lawSupportR_val` がそのΦ値、`lawSupportR_viaQ` が既存Q-H¹-R両方向座標との一致を与える。
RをQ由来の新しい型へ置き換えず、元のκ*の核を保持している。

実SES射へmathlibの `HomologicalComplex.HomologySequence.δ_naturality` を適用し、
`lawSupport_delta` を全整数次数で得る。同じ原Q-R可逆座標で `lawSupport_tau` へ戻す。
五項列のH¹P→細H¹、細H¹→literal R、R→H²P、H²P→細H²の全射を保持する。
元Lawの短完全性と元Aの短完全性はC11/C4の同じ入力生成定理を使い、
追加の完全性・同型・自然性・期待rankを仮定にしない。

同じη・ε・独立u正方形から `mappingCone.map` を作り、
`lawSupportCoefficientCone/FiberCone/TotalCone_apply` が全整数次数の二座標を照合する。
`lawSupportConeTriangle_first/second/third` は三射を全Homで保ち、第三射では元shift負号まで使う。
原 `lawFiberConeDesc` と同じ `fiberConeDesc` の全Hom正方形、標準homology両方向同型と
全次数 `coneConnecting` を同じnative δへ接続する。

任意のラベル別部分台族 `A l ⊆ labelValueFiber laws qc ha l` を保持し、
`coefficientShortComplexFamily_map` により元Law SESから同じ原P/細cochain/Q族への全射を生成する。
`lawSupportFamilyUnit/Evaluation/Restriction/Direct` と `lawSupportFamily_delta` は全族のnative図式である。
`lawSupportFamilyKappa`・`lawSupportFamilyKappaStar` は実線形写像全体の等号、
`lawSupportFamilyR_val` はliteral R族の直接Φ値である。
原部分台Q族のH¹からR族への `supportFamilyQREquiv` を生成し、同じ実族SESのδで
`supportFamilyTau` を作る。元Law τの全族native可換式と全ラベル値を照合する。
全族の三錐射は元Law錐族同型とprimitive支持錐射から作り、各射影が同じnative Law錐射になることを
全次数の二座標で証明する。全三triangle射、Q評価、literal R、標準連結射を全族で保つ。

入れ子台の合成は元SES・P・細cochain・Q・粗cochain・literal R・三錐の同じ実制限を使う。
元ラベル台そのものではC11のcanonical族同型へ戻る。
`lawSupportP_single/other` と `lawSupportR_single/other` は元canonical逆射の単一成分を評価し、
同ラベルで元を回復し異ラベルで零を返す。台の一致による重複ラベルの同一視をしていない。
空台では元P射とliteral R射が零、空Lawでは元全複体・三錐の全整数次数が零になる。
これらの特殊化を一般構成の非空性仮定として入れていない。

### 使用した前提と受理済み依存

| 前提・依存 | 役割と生成・使用経路 | 状況 |
| --- | --- | --- |
| T0のM/reading/K1/有限Source/元nerve/ℚ | ambient-boundary。原primitive台制限・原Law分解・native複体/κの同じ引数に使用 | 固定入力 |
| 粗adequate Law | ambient-boundary。C11の `lawFineAdequate` と元canonical族座標を生成 | 細adequacyは同じreading因子から導出 |
| ラベル別支持包含・入れ子包含 | direction-hypothesis。全primitive制限・混在閉路包含・Φ制限・合成を生成 | 全包含で量化、非空性やfiber条件なし |
| 元Law P/細/Q族同型、実SES、κ/R/τ/三錐 | C11 PR5302 head7f20e6aaaae8c51298b32d955ca16a6b0076b84a、受理6054697310、mergea993ccd6791f64cbbb8bdd6c4c6b591c3ea11dad。現statement・M/l/台引数を照合 | 本cycleのowner追加は基本射影APIのみ |
| primitive全台P/二射/κ/直接R/δ/錐・合成 | C12 PR5303 head70633bfc653fe823fbdbbbcec8b1d6fc12a5bb5b、受理6057242603、merge9abbeb4ad0578e7aca653a11353707c268db2179。現statement・元台包含引数を照合 | 受理版から今回の使用箇所は不変 |
| 元有限複体族・実射影・元錐二座標 | G133 PR5269 head74cb93564070661509ac0c2f842596e63d0957fa、標準受理6007458427・全体6007700344。現API・型/universeを照合 | 同族射影の値APIだけをownerへ追加 |
| 新SES/全族図式/κκstar/R一致/native δ/τ/錐対応 | discharge-required。上記同じ入力とpredecessorから本cycleで構成する | 初回四票中心0、非中心F1の単一確認待ち |
| 全族canonical逆座標・単一成分 | 線形同型の両逆と原Pi.singleの値を使う | 供給certificateや期待rankなし |
| mathlib4.28.0/8f9d9cff6bd728b17a24e163c9402775d9e6a365 | 全Hom・ShortComplex・native δ・mappingCone・shift・homology・Piの標準API/適用型 | 版と使用条件を確認、library全体の再認定は対象外 |

全GOALの後続義務はDのG134指定基本変形と部分セル有限合成・面複製、
B/Eの全A有限τ判定、Eの原始有理行列から同じa/R/τ/J/blockDefectの計算、
W全表の同時評価、別final fresh4監査である。C13を全体完了へ読み替えない。


## Cycle 13 result proposal

```yaml
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: 原Law全射と任意ラベル別部分台のprimitive制限を実SES/κ/直接R/nativeδ/τ/五項列/原三錐で接続した
  exit_criteria_status:
    - 全M/l/A包含でlawSupportMorphismと原P/Fine/Q/Coarse canonical_eq・component_applyが全Homと全ℤ値を一致させる
    - lawSupportKappa/KappaStar/R_val/R_viaQと族版が元混在閉路/Φ/κstar核/Q可逆座標の全値を一致させる
    - lawSupport_deltaと族delta_componentが原nativeδを全ℤで保ち、元τ/五項列/ηε独立u全射が可換
    - 原三Law mappingConeと実支持射が全ℤ二座標/三triangle/shift負号/Qdesc/標準connectingで可換
    - 全族射・refl/comp・空台/空Law・Pi.single同ラベル回復/異ラベル零が同じ原生成対象と重複ラベルを保つ
    - 原始入力からの構成と公開API使用を照合し、14focused/283全宣言#print/std audit・依存版/使用経路を記録した。初回四票中心0、非中心F1の単一確認は未受理
  split_reason: none
  completion_candidate: no
  lean_artifacts: [LawSupportProjection, LawSupportFiber, LawSupportConnecting, LawSupportCones, LawSupportFamilies, LawSupportComposition, LawSupportFamilyHomology, LawSupportFamilyKappa, LawSupportEmpty, LawSupportLabels, LawSupportConeFamilies, LawSupportConeFamilyHomology]
  evidence: [上記同じ原Mの生成経路と下記283宣言spine・focused実log]
  claim_mapping:
    theorem_names: [lawSupportDirect, lawSupportR_viaQ, lawSupport_tau, lawSupportConeTriangle, lawSupportFamily_tau_native, supportFamilyTau_component, lawSupportFamilyKappaStar, lawSupportFamilyMorphism_comp, lawSupportConeFamilyTriangle_third, lawSupportFiberConeFamilyConnecting]
    source_labels: [GOAL D, designREADME§5, T0全量化]
    conjuncts: [原Lawから任意部分台全射, κ/κstar/literalR全値, 原SES/τ/五項列全射, 原三錐/triangle/shift/Q評価/connecting, 全族/恒等合成/空入力/重複保存]
    undischarged_assumptions: []
    acceptance_point: 初回独立数学2/Lean2の中心0、非中心F1対応を有資格単一確認へ渡すproposal
    port_status: unported
audits:
  premise_delta:
    discharged: [同じ原始MからのLaw支持SES/全族射/κR/δτ/錐自然性, 同じ逆座標の単一成分/空Law全次数]
    remaining: [DのG134指定操作/部分セル有限合成/面複製, B-E全A有限τ検査, E同じ原始有理行列/aRτJ/blockDefect, W全表の同時評価, 別finalfresh4]
  certificate_provenance:
    discharged: [C11元Law族可逆座標とC12primitive支持射から合成, nativeShortExactとdeltaとmappingConeは同じ元入力生成]
    unresolved: []
  proof_use:
    used: [原T0のM/reading/nerve/ℚ/有限Source, 粗Lawadequacyから細adequacyと元ラベル座標, 全支持包含から元制限/Φ混在閉路包含/合成]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [14focused warning/error0, 全283明示print/module audit/log標準公理のみ, 下記実source/log hash対応]
  blocking_findings: [初回四票の非中心F1は実装修正済み、独立単一確認未受理]
  next_obligation: C13標準PRgate後にDのG134指定操作と有限合成/面複製を選定する
```

上記は実装rootのproposalであり、独立reviewの代替ではない。
現GOAL全体はtarget-proof-checkpoint、Formalはunported。

## Cycle 13 初回四票とF1直接対応

PR [#5304](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5304)、初回head
`2a2847f3d499727e9ebf966c1f03fe277bdb2109`。
[数学A](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5304#issuecomment-6058595180)は
Minor issues、[数学B](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5304#issuecomment-6058597663)・
[LeanA](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5304#issuecomment-6058600719)・
[LeanB](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5304#issuecomment-6058603350)はNo major findings。
[初回標準監査](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5304#issuecomment-6058617394)で
中心0、統合非中心F1一件を固定した。正式再実行は0/2。
初回実282件（258source+24生成）のvalidation SHAは
`dc43e7aa696b38432e7a5defbbc340a276ae0ae883dbf92fda1ce3a768d08014`、
scan SHAは`c534a8d1b925d115f320ded750f9df88aa5f61cb5152da860f47d10c73b33c30`。
初回exactheadの8checksはSUCCESS、Lean37766622423/Tool37766622403。
Research実stepsは成功、Formal実build/kernel/premiseはSKIPPED。

F1はLawSupportCompositionの合成・恒等proofにあるowner定義の直接展開。
名指しされた `lawSupportFamilyMorphism_eq` をownerへ追加し、二つのproofを公開等号APIで書き換えた。
既存statement・def/instance本体値・宣言・import方向・台帳statusは変更していない。
追加補題を明示#printと下記spineへ収載し、変更二fileのfocusedがwarning/error0で通過した。
初回全findingへの対応と変更範囲・資格は新規単一確認へ渡す。未確認を受理へ読み替えない。

<!-- cycle13-generated-evidence -->

全259source宣言と24生成宣言の合計283件を同順序で明示#print・実log・module auditへ照合した。
新source186件（12新file180件と既存owner公開API6件）と新生成24件で210件のdelta。
生成congr_simpには本moduleで生成された既存import関数の名前も含み、所属moduleと実出力を確認した。
spine外のcycle scaffold宣言はない。

| file | 宣言（source/print/log/report相対順、生成宣言を含む） |
| --- | --- |
| `FiniteComplexFamily.lean` | `FiniteComplexFamily.complex`, `FiniteComplexFamily.degreeSubsingleton`, `FiniteComplexFamily.d_apply`, `FiniteComplexFamily.projection`, `FiniteComplexFamily.projection_apply`, `FiniteComplexFamily.map`, `FiniteComplexFamily.map_apply`, `FiniteComplexFamily.map_projection`, `FiniteComplexFamily.map_id`, `FiniteComplexFamily.map_comp`, `FiniteComplexFamily.iso`, `FiniteComplexFamily.iso_hom`, `FiniteComplexFamily.iso_natural`, `FiniteComplexFamily.fan`, `FiniteComplexFamily.fanIsLimit`, `FiniteComplexFamily.productIso`, `FiniteComplexFamily.degreeFiniteDimensional`, `FiniteComplexFamily.directSumIso`, `FiniteComplexFamily.directSumIso_projection`, `FiniteComplexFamily.directSumIso_natural`, `FiniteComplexFamily.additivePreservesFamily`, `FiniteComplexFamily.homologyIso`, `FiniteComplexFamily.homologyIso_projection`, `FiniteComplexFamily.homologyEquiv`, `FiniteComplexFamily.homologyEquiv_component`, `FiniteComplexFamily.homologyEquiv_natural` |
| `LawFiberSequence.lean` | `coefficientShortComplexFamily`, `coefficientShortComplexFamily_shortExact`, `lawRestrictionComplex`, `lawRestrictionHom`, `lawRestrictionHom_eq`, `lawEvaluation_restriction_zero0`, `lawEvaluation_restriction_zero1`, `lawEvaluation_restriction_zero2`, `lawEvaluation_restriction_standard_zero`, `lawEvaluationRestrictionShortComplex`, `lawRestrictionStandardIso`, `lawRestrictionStandard_square`, `lawEvaluationRestrictionFamilyIso`, `lawEvaluationRestriction_shortExact`, `coefficientShortComplexFamily_projection`, `coefficientShortComplexFamily_projection_τ1`, `coefficientShortComplexFamily_projection_τ2`, `coefficientShortComplexFamily_projection_τ3`, `lawEvaluationRestrictionProjection`, `lawEvaluationRestrictionProjection_eq`, `lawEvaluationRestrictionProjection_τ1`, `lawEvaluationRestrictionProjection_τ2`, `lawEvaluationRestrictionProjection_τ3`, `lawPushforwardHomologyEquiv`, `lawRestrictionHomologyEquiv`, `lawPushforwardHomologyEquiv_component`, `lawRestrictionHomologyEquiv_component`, `lawConnecting_delta_component`, `lawKappa`, `lawKappaStar`, `lawR`, `lawRFamilyEquiv`, `lawRFamilyEquiv_val`, `lawRestrictionHomologyREquiv`, `lawRestrictionHomologyREquiv_component`, `lawConnectingTau`, `lawConnectingTau_apply`, `lawConnectingTau_component`, `lawRestriction_H0_isZero`, `lawEvaluationH1`, `lawFiberRestrictionH1`, `lawEvaluationH2`, `lawEvaluationH1_injective`, `lawFiveTerm_exact_at_fineH1`, `lawFiveTerm_exact_at_fiber`, `lawFiveTerm_exact_at_pushforwardH2`, `lawKappa_apply`, `lawKappaStar_apply`, `lawRFamilyEquiv_symm_val`, `lawEvaluationH1_eq_standard`, `lawEvaluationH1_apply`, `lawFiberRestrictionH1_apply`, `lawEvaluationH2_eq_standard` |
| `LawSupportProjection.lean` | `lawSupportMorphism`, `lawSupportMorphism_eq`, `lawSupportP`, `lawSupportFine`, `lawSupportQ`, `lawSupportCoarse`, `lawSupportP_projection`, `lawSupportFine_projection`, `lawSupportQ_projection`, `lawSupportP_eq`, `lawSupportFine_eq`, `lawSupportQ_eq`, `lawSupportCoarse_eq`, `lawSupportP_apply`, `lawSupportFine_apply`, `lawSupportQ_apply`, `lawSupportCoarse_apply`, `lawSupportP_component_apply`, `lawSupportFine_component_apply`, `lawSupportQ_component_apply`, `lawSupportCoarse_component_apply`, `lawSupportUnit`, `lawSupportEvaluation`, `lawSupportRestriction`, `lawSupportDirect`, `lawSupportCoarse.congr_simp`, `lawSupportFine.congr_simp`, `lawSupportP.congr_simp`, `lawSupportQ.congr_simp` |
| `LawSupportFiber.lean` | `lawSupportMixedInsert`, `lawSupportMixedInsert_apply`, `lawSupportPhiHomologyInsert`, `lawSupportPhiHomologyInsert_apply`, `lawSupportKappa`, `lawSupportPhiH1`, `lawSupportPhiH1_apply`, `lawSupportKappaStar`, `lawSupportR`, `lawSupportR_apply`, `lawSupportR_val`, `lawSupportR_viaQ` |
| `LawSupportConnecting.lean` | `lawSupport_delta`, `lawSupport_tau`, `lawSupportEvaluationH1`, `lawSupportFiberRestrictionH1`, `lawSupportEvaluationH2` |
| `LawSupportCones.lean` | `lawSupportCoefficientCone`, `lawSupportCoefficientCone_apply`, `lawSupportFiberCone`, `lawSupportFiberCone_apply`, `lawSupportTotalCone`, `lawSupportTotalCone_apply`, `lawSupportConeTriangle_first`, `lawSupportConeTriangle_second`, `lawSupportConeShift_apply`, `lawSupportConeTriangle_third`, `lawSupportConeTriangle`, `lawSupportFiberConeDesc`, `lawSupportFiberConeHomologyEquiv`, `lawSupportFiberConeHomologyEquiv_symm`, `lawSupportFiberConeConnecting` |
| `LawSupportFamilies.lean` | `coefficientShortComplexFamily_map`, `coefficientShortComplexFamily_map_projection`, `lawSupportFamilyMorphism`, `lawSupportFamilyMorphism_eq`, `lawSupportFamilyP`, `lawSupportFamilyFine`, `lawSupportFamilyQ`, `lawSupportFamilyCoarse`, `lawSupportFamilyMorphism_projection`, `lawSupportFamilyP_eq`, `lawSupportFamilyFine_eq`, `lawSupportFamilyQ_eq`, `lawSupportFamilyCoarse_eq`, `lawSupportFamilyP_projection`, `lawSupportFamilyFine_projection`, `lawSupportFamilyQ_projection`, `lawSupportFamilyCoarse_projection`, `lawSupportFamilyP_apply`, `lawSupportFamilyFine_apply`, `lawSupportFamilyQ_apply`, `lawSupportFamilyCoarse_apply`, `lawSupportFamilyUnit`, `lawSupportFamilyEvaluation`, `lawSupportFamilyRestriction`, `lawSupportFamilyDirect`, `lawSupportFamily_shortExact`, `lawSupportFamily_delta`, `lawSupportFamilyR`, `lawSupportFamilyR_apply`, `lawSupportFamilyCoarse.congr_simp`, `lawSupportFamilyFine.congr_simp`, `lawSupportFamilyP.congr_simp`, `lawSupportFamilyQ.congr_simp` |
| `LawSupportComposition.lean` | `coefficientShortComplexFamily_map_id`, `coefficientShortComplexFamily_map_comp`, `supportEvaluationRestrictionMorphism_refl`, `supportEvaluationRestrictionMorphism_comp`, `lawSupportFamilyMorphism_comp`, `lawSupportFamilyP_comp`, `lawSupportFamilyFine_comp`, `lawSupportFamilyQ_comp`, `lawSupportFamilyCoarse_comp`, `lawSupportFamilyR_comp`, `lawSupportFamilyMorphism_refl`, `lawSupportFamilyP_refl`, `lawSupportFamilyFine_refl`, `lawSupportFamilyQ_refl`, `lawSupportFamilyCoarse_refl`, `lawSupportFamilyR_refl`, `supportEvaluationRestrictionMorphism.congr_simp` |
| `LawSupportFamilyHomology.lean` | `coefficientShortComplexFamily_delta_component`, `lawSupportFamilyPHomology`, `lawSupportFamilyPHomology_apply`, `lawSupportFamilyFineHomology`, `lawSupportFamilyFineHomology_apply`, `lawSupportFamilyQHomology`, `lawSupportFamilyQHomology_apply`, `lawSupportFamilyCoarseHomology`, `lawSupportFamilyCoarseHomology_apply`, `supportFamilyQREquiv`, `supportFamilyQREquiv_apply`, `supportFamilyQREquiv_symm_component`, `lawSupportFamilyR_viaQ`, `supportFamilyTau`, `supportFamilyTau_apply`, `supportFamilyTau_component`, `lawSupportFamily_tau_native`, `lawSupportFamily_tau`, `lawSupportFamilyEvaluationH1`, `lawSupportFamilyFiberRestrictionH1`, `lawSupportFamilyEvaluationH2` |
| `LawSupportFamilyKappa.lean` | `lawSupportFamilyMixed`, `lawSupportFamilyMixed_apply`, `lawSupportFamilyPhiHomology`, `lawSupportFamilyPhiHomology_apply`, `supportFamilyKappa`, `supportFamilyKappa_apply`, `lawSupportFamilyKappa`, `lawSupportFamilyPhiH1`, `lawSupportFamilyPhiH1_apply`, `lawSupportFamilyKappaStar`, `lawSupportFamilyR_val`, `lawSupportFamilyMixed.congr_simp`, `lawSupportFamilyPhiH1.congr_simp`, `lawSupportFamilyPhiHomology.congr_simp`, `supportAllPhiH1.congr_simp`, `supportAllPhiHomology.congr_simp`, `supportMixedCyclesInclude.congr_simp` |
| `LawSupportEmpty.lean` | `lawSupportLabels_empty`, `coefficientFamily_emptyDegree`, `lawSupportP_empty`, `lawSupportR_empty`, `lawSupportEmptyP`, `lawSupportEmptyFine`, `lawSupportEmptyQ`, `lawSupportEmptyCoarse`, `lawSupportEmptyR` |
| `LawSupportLabels.lean` | `lawSupportFamilyP_inverse`, `lawSupportP_single`, `lawSupportP_single_other`, `lawSupportFamilyR_inverse`, `lawSupportR_single`, `lawSupportR_single_other` |
| `LawSupportConeFamilies.lean` | `lawSupportCoefficientConeFamily`, `lawSupportCoefficientConeFamily_apply`, `lawSupportCoefficientConeFamily_projection`, `lawSupportFiberConeFamily`, `lawSupportFiberConeFamily_apply`, `lawSupportFiberConeFamily_projection`, `lawSupportTotalConeFamily`, `lawSupportTotalConeFamily_apply`, `lawSupportTotalConeFamily_projection`, `lawSupportCoefficientConeFamily_value`, `lawSupportFiberConeFamily_value`, `lawSupportTotalConeFamily_value`, `lawSupportConeFamilyTriangle_first`, `lawSupportConeFamilyTriangle_second`, `lawSupportFiberConeFamilyDesc`, `lawSupportCoefficientConeFamily_refl`, `lawSupportCoefficientConeFamily_comp`, `lawSupportFiberConeFamily_refl`, `lawSupportFiberConeFamily_comp`, `lawSupportTotalConeFamily_refl`, `lawSupportTotalConeFamily_comp`, `lawSupportCoefficientCone.congr_simp`, `lawSupportCoefficientConeFamily.congr_simp`, `lawSupportFiberCone.congr_simp`, `lawSupportFiberConeFamily.congr_simp`, `lawSupportTotalCone.congr_simp`, `lawSupportTotalConeFamily.congr_simp`, `supportCoefficientCone.congr_simp`, `supportFiberCone.congr_simp`, `supportTotalCone.congr_simp` |
| `LawSupportConeFamilyHomology.lean` | `lawSupportConeFamilyTriangle_third`, `lawSupportFiberConeFamilyHomology`, `lawSupportFiberConeFamilyHomology_apply`, `lawSupportFiberConeFamilyDesc_homology`, `lawSupportFiberConeFamilyQ`, `lawSupportFiberConeFamilyR`, `lawSupportFiberConeFamilyConnecting`, `lawSupportEmptyCoefficientCone`, `lawSupportEmptyFiberCone`, `lawSupportEmptyTotalCone` |

14単一focusedはwarning/error0。公理依存はpropext/Classical.choice/Quot.soundの部分集合だけ。
validation SHA `0da19bebeddfc91868fe516b9dbf9feab3846f8f6aaf35664f5f8baec25105bc`。

| file / source+生成件数 | source SHA256 | 実focused log SHA256 |
| --- | --- | --- |
| `FiniteComplexFamily.lean` / 26+0 | `72b6a3182448384493ac8ca43d9ff759a7fb77028e2ecc36ce2532d4e876edd7` | `9e8c7e087e15ac4958498e982a0262c48e04fa026095028db3463b6f4a38769d` |
| `LawFiberSequence.lean` / 53+0 | `2a838970a53412557e5ca9bc90e9296fd5547297076392a2bcd2bd37b5b6ec55` | `55577883509fde71446efd1c677810bda62b12639532d199eda3a8a3b4bf80a3` |
| `LawSupportProjection.lean` / 25+4 | `fdd1de12ed8f6bef2c22a64085bfd528c83aac64d614731a616e368c3cdf0710` | `89483dcff94d302add944f945c1ae51fe54744b1f58bb4dbb087a62ff5c30271` |
| `LawSupportFiber.lean` / 12+0 | `fb0236d7a06c213972fbd74051d95fbb128ac59dc5387e2d6869d99f16128e94` | `49c5722ffdbf416d30146c14bf741c22d3b3c900cc42790c7886e345fba55a94` |
| `LawSupportConnecting.lean` / 5+0 | `6c8e120bf4ee25669370b5b9206baadaa897cf51d592a7595719f2d17006d57b` | `c51be5d689f09e1b74cd20903247aef8dc121de1a938ec51d474623f3a8479dd` |
| `LawSupportCones.lean` / 15+0 | `3fa7d2c23a5bf8693b94cb2efa62ae85ff43a3327970ebf7f60bc06e2474fb81` | `c451df661da3f779e8a8d5c4ffe7ca7df70290000bcf249abb89192b4a49f0a8` |
| `LawSupportFamilies.lean` / 29+4 | `a1136265bf0516bfb25187b04978450d7acc32658791b19c5cc09db3dd6a8ce1` | `5be78f02f77079a1137aee224ccfefb33fa741c3dcbc3f531105c96b1a733ad1` |
| `LawSupportComposition.lean` / 16+1 | `7b37ee967962ee401ffc267d499cd751226aa622b9b0080b0b5f1ea84fd30285` | `b72b2a571f3f6611d63a2cb2ed5092a593b9a82eab7dd25a2656731f760e3901` |
| `LawSupportFamilyHomology.lean` / 21+0 | `9d3fcced03b0453365ceb917cfa35779cbda98e69327758d6081253cef86621d` | `d64e6d342b27a50de5167704d79ee1267f59c6ebf644ac5b2d50fbcf5b171808` |
| `LawSupportFamilyKappa.lean` / 11+6 | `4b2a68ef8948d1d9f712fb4851c6530b965496b1adf3bf9bf034473e1d3c79f5` | `56e583e7d71188d387b45da856a56a50678e7bc78f8f8b37b7a716b8dd7b48cb` |
| `LawSupportEmpty.lean` / 9+0 | `49fd353870f46280065e282c99acfc25759c5432d2284cda175581616c63a5c7` | `1c106d3118fd0346e1513b0c1d3ee89d98469203c7d019705d7c4f3fb42bbeb0` |
| `LawSupportLabels.lean` / 6+0 | `42785cc4c92eb7688135cd9c9f9b88d89e1a1493bd974e7fcbdba4e81f50a77a` | `f918e798017ac71b9f49738fd9c79b6f3bb8134f90a710eb9c7cbdcedee581ee` |
| `LawSupportConeFamilies.lean` / 21+9 | `eda7162de6b14ab3222b1c1a739e8ed0501c98b42b10a9079bf4ed700902e4c9` | `f212bde84fa0190e1f37513ef20d736613eb255376a0effd9c480e756f75a5ca` |
| `LawSupportConeFamilyHomology.lean` / 10+0 | `8b943a4d5df22d5e2983ccf165e2b392aabea46356ef92733e60274d834c9692` | `e1717afa5f6ee4086410fddcc3e94ef21bacf0bb3fcd4f7481297b0d9dfa33be` |

Research full/aggregate/全fileloop/local lake build、Formal実build/移植、全GOAL別finalは未実施。

共通scan SHA `0481836fbf74bdf05c94fc20d3fb396e6454ebbf4aed40e1e96a3a7e7058e5d3`。
新Unicode/placeholder/privacy/語彙/逆import0、diff check成功、GOAL/design/Formal不変、
13新直接登録（既存G133 ownerを含む）・14対象のmanifest/AG登録各1、静的方向228modulePASS。


## Cycle 13受理・merge同期

PR [#5304](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5304)、最終head
`657e562eaa154e94155681e07d3c218e6998375b`、merge
`231c985d6bad1fc80f90c3ef0cbd1d036c19840a`、2026-10-08T11:28:51Z。
[最終標準/root受理](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5304#issuecomment-6058853944)、
[有資格新規単一確認](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5304#issuecomment-6058851678)、
[Issue同期](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5290#issuecomment-6058877001)。
六固定終了条件はapprove / proof-obligation-discharged。初回四票中心0、非中心F1一件。
名指し公開補題と二proof内部だけの直接対応を新規単一確認が資格内/実体解消と判定、新finding0。
正式再実行0/2。283件（259source+24生成）全print/log/module audit/report順/hash一致、標準三公理のみ。
validation SHA0da19bebeddfc91868fe516b9dbf9feab3846f8f6aaf35664f5f8baec25105bc、
scan SHA0481836fbf74bdf05c94fc20d3fb396e6454ebbf4aed40e1e96a3a7e7058e5d3。
直接確認原記録SHAa3e21b257cffa3b072213fab39918d37ca64815cd002073e9fb53c59a795e85e、
機械記録SHA70da589b21360c752138649bfd517211de8b11a7bea872e1705a03f9eaa468fc。
最終samehead8checksSUCCESS、Lean37769465507/Tool37769465474。
Research実stepsSUCCESS、Formal実build/kernel/premiseSKIPPED。全GOAL checkpoint、Formal unported。

## Cycle 14 selection

```yaml
ledger_type: target_cycle_result
goal: G-135-aat-atlas-coefficient-fiber
cycle: 14
goal_blob_sha: cd5f3e684b7f390558796797874a1f16b52a6b18
base_oid: 231c985d6bad1fc80f90c3ef0cbd1d036c19840a
tracking_issue: 5290
report_path: research/reports/G-135-aat-atlas-coefficient-fiber.md
selection:
  proof_state_ref: Cycle13受理/Issue6058877001・GOAL DのG134保存操作未完行
  proof_dag_predecessors: [G134原始正操作r/s/h/k生成と有限列同値 PR5283, G134独立部分セル比較/全台生成, C8原a同型とτ単射の保存必要十分, C11-13実Law/全ラベル台族/三錐]
  milestone: G134三角形追加/面付き辺分割/reading pullbackの部分セル有限合成を同じ原比較に接続し原a同型とτ核零を導く
  proof_obligations: [原始部分セル表のSource支持有限和表示, 許容正操作列から実Option比較の生成, 既存r全三次数と独立subset/Law生成Homの一致, 同じG134逆有限和/二補正から原比較の全次数同型と錐零, 同じ旧J零から原a可逆座標と実τ核零, 全A/任意粗adequate Law/発生labelの量化と恒等合成/空台の保持]
  exit_criteria:
    - 任意reading/原MのSource支持基底を原chart/Option辺面から生成し恒等・部分合成・同じ実subset/Law全三成分と一致させる
    - 三角形追加/面付き辺分割/表示同型と指定reading pullbackの原始正操作有限列からMを生成する。結論同型やraw同値を操作入力にせずG134同じ原始列へ接続する
    - 全Aで同じ独立aSubnerveComparisonHomと元r実subset Homを全三次数/全値で同定し、同じ原逆有限和と二補正を標準HomotopyEquivの順逆に保持する
    - 全Aの旧H1商同型・全整数次数homology同型・原totalCone全次数零を同じG134定理から導き、同じaの順写像を持つ両方向線形同型と実τ核零を導く
    - 任意粗adequate Lawと全発生labelで同じgeneratedComparisonHom/原Law標準錐/旧blockDefectへ接続し、原Law a可逆性/τ核零と全台部分族の値を保持する
    - T0入力/粗adequacy/原始セル表以外の同型/vanish/rank入力を追加せず、空A/空Law/重複incidenceとlabelを保持し全宣言公理/placeholder/Unicode/privacy/import方向と証拠対応を監査する
  selection_reason: 未放電Dの保存適用を同じ原P/η/ε/κRτへ戻し、任意有限正操作列の入力生成を閉じる
  expected_result_type: proof-obligation-discharged
  lean_targets: [PrimitiveSourceBasis, PrimitiveSourceComparison, PositiveOperation, PositiveOperationPath, PositivePreservation, PositiveCoefficientPreservation]
  risks: [逆有限和をP入力へ混入, supplied preservation certificate, 読み変更を同じreadingだけへ縮小, 全射一致をH1だけへ縮小, inverse/補正の出所欠落, J零からτ零またはface複製全錐零と誤推論]
  unchecked: [上記六終了条件の実装/検証/正式PR受理は未完, D面複製・B/E/W・別finalは後続]
```


## Cycle 14 result proposal

```yaml
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: 原始正操作有限列から生成した同じ部分比較の順HomをG134原rと全三成分で同定し、全A/任意Lawの両逆と全錐零を導き、同じ原aの両逆とliteral R上のτ単射へ接続
  exit_criteria_status:
    - 原Source支持基底をchart/Option辺面から構成し、恒等列と任意部分合成、独立subset/Law全三成分へ接続
    - triangle/subdivision/presentationと指定reading pullbackのpositive nil/snoc列が元Option比較を生成。同じG134列のr表との一致を有限帰納で導出
    - subsetR_eq_generatedで独立原aSubnerve全Homと一致。元r/sと二補正から同じ標準HomotopyEquivの順逆を保持
    - subset旧H1同型/全整数次数homology同型/totalCone零。unitEquivの実原a順写像と両逆、τ単射/核零
    - lawR_eq_generatedで同じ独立generatedComparisonHom。全Law旧H1/全次数/錐零/旧J零、原Law a両逆とτ核零。任意ラベル台族で元a/τ全値と同じnative族SESτの可逆座標を保持
    - 6 focused warning/error0。90source+44生成134件を同順序print/log/module audit/reportへ照合、標準三公理のみ。空列/空台/空Law/重複incidenceとlabelを保持
  split_reason: none
  completion_candidate: no
  lean_artifacts: [PrimitiveSourceBasis, PrimitiveSourceComparison, PositiveOperation, PositiveOperationPath, PositivePreservation, PositiveCoefficientPreservation]
  evidence: [元セル表からのSupportedBasisMap, 原始positive nil/snoc, 元G134 r/s/h/k, 同じ独立subset/Law全Hom, 元C8保存必要十分, 元C13族SESτ成分]
  claim_mapping:
    theorem_names: [PositiveOperationPath.subsetR_eq_generated, PositiveOperationPath.lawR_eq_generated, PositiveOperationPath.subsetHomotopyEquiv_hom, PositiveOperationPath.subsetHomotopyEquiv_inv, PositiveOperationPath.lawHomotopyEquiv_hom, PositiveOperationPath.lawHomotopyEquiv_inv, PositiveOperationPath.unitEquiv_apply, PositiveOperationPath.lawUnitEquiv_apply, PositiveOperationPath.tauKernel_eq_bot, PositiveOperationPath.lawTauKernel_eq_bot, PositiveOperationPath.supportTau_native]
    source_labels: [GOAL DのG134正保存操作/部分有限合成, GOAL Cの同じa同型とτ核零への適用]
    conjuncts: [全三次数原比較一致, 全A/任意粗adequate Law/全発生label, 旧H1両逆/全整数次数同型と標準錐零, 元a両逆とliteral Rのτ核零, 任意ラベル部分台族のnative SESτ接続]
    undischarged_assumptions: [D面複製・B/E入力生成有限判定・W全同経路評価・別最終四票は後続]
    acceptance_point: 六固定終了条件の同じ対象/射/逆/全方向がroot検証済み。受理は固定headの標準四票とroot監査へ渡す
    port_status: unported
  audits:
    premise_delta:
      discharged: [原始positive入力から同じG134 raw r/s/h/k生成, r表と独立Option比較全Homの一致, 原比較H1全単射/全錐零, 元a可逆/τ単射]
      remaining: [D面複製・B/E有限producer・W全経路評価・別final]
    certificate_provenance:
      discharged: [Source基底は元Mセル表, positive comparisonは元identity/comp, 原G134生成raw同値はPR5283受理版producer, 原a同型はC8元J零導出, 任意台族τはC13同じ原SES]
      unresolved: [正式PR査読は未実施]
    proof_use:
      used: [各原始セル表のSource支持/Optionbind, 原G134 r表とsnoc合成, 元r/sと両補正, coarse Law adequacyによる元細adequacy, 全label元a値/原SESτ成分]
      unused: []
    structure_field_escape: none-found
    route_integrity: pass
    target_fitting: none-found
    vacuity: none-found
    one_way_as_equivalence: none-found
    goal_or_report_reinterpretation: none-found
    validation_refs: [6単一focused/134明示print/log/module audit, 共通scanと固定入力照合は下記]
    blocking_findings: [正式PR四票/root受理/CIは未実施]
    next_obligation: D面複製の同じP/ε/ηとH1保存/非零H2余核の接続
```

## Cycle 14固定要求・前提と同じ写像の対応

| 固定要求 | 同じ対象・射と構成経路 |
| --- | --- |
| D正保存操作のT0部分セル入力 | `PositiveOperation.triangle/subdivision/presentation` は元セル名・端点・面・台だけを取る。`reading` は元指定readingPresentation、`reading_toPrimitive`で同じG134 reading操作に一致。`PositiveOperationPath.comparison`は元恒等・Option部分合成から生成 |
| 任意reading/全Aの順比較 | `PrimitiveSource.basis0/1/2`は原Mのchart/Option表とSource台から直接生成。`_image/_self/_comp`と各`primitive_r0/1/2`で元G134列のr表を証明。`subsetR_eq_generated`は全ThreeCochainHomの三成分を同定 |
| 任意Lawの順比較 | `basis0/1/2_law`は同じ元混在Law pullbackと全座標で一致。`lawR_eq_generated`が元独立generatedComparisonHomに戻す。label値型の有限性を加えず、元発生label生成を用いる |
| 元G134両逆・全次数保存 | `subset/lawHomotopyEquiv`は同じ生成raw r/s/h/kを保持。`_hom/_inv`は原独立比較と元有限和逆射。`subset/lawHomologyIso_hom/_inv`は全整数次数、`subset/lawOldH1Iso_hom/_inv`は元旧商、`subset/lawCone_isZero`は同じ原標準錐 |
| 同じ原aの可逆性 | `unitEquiv`はC8の実旧J零から原η H1へ導出、`_apply`と二逆式は同じ原aの全値。`lawUnitEquiv`は元粗Law/原P可逆族座標、`_apply`は元lawUnitH1、二逆式は同じ元粗Lawと原Law P |
| literal Rと原τ | `tau_injective/tauKernel_eq_bot`はC8原J零の同値のτ側。`lawTau_injective`は元lawRFamilyEquivと原lawConnectingTau_componentの全値で導出。核零は同じliteral R/原lawR内 |
| 任意部分台族 | `supportUnitEquiv`は同じ元aの全ラベル値の両方向座標。`supportTau`は同じ原τのPi射。`supportTau_native`でC13元SES族nativeτの可逆homology座標と全値一致、`supportFamilyTau_injective`で同じnativeτの単射を得る |

| material premise | 分類 | 出所と実使用・放電 |
| --- | --- | --- |
| 任意reading/元M/原始セル・台とℚ | ambient-boundary | 元chart/OptionとcomparisonFactor_commutesをSource支持基底・三成分接続に使用 |
| positive triangle/subdivision/presentation | direction-hypothesis | D指定適用入力。presentationは名前/incidence/支持の同型表で、homologyや保存情報をfieldへ渡さない。元読みpullbackは既存readingPresentationで生成 |
| 任意Source有限性・粗Law adequacy | ambient-boundary | 元有限発生labelとLaw可逆座標。細adequacyは元adequate_of_coarserから導出 |
| 内部一般接続のraw r0/r1/r2等号 | direction-hypothesis → discharge-required | `rawR_eq_generated/rawLawR_eq_generated`の一般補題だけで保持。最終positive path適用では三つのprimitive_rを原始セルと有限帰納から生成し全放電 |
| raw同値・s/h/k・保存証拠 | discharge-required | `toPrimitive`が元PR5283 producerを同じ各段へ適用。final操作入力に証拠を受け取らず、元有限和逆射・二補正をそのまま使用 |
| 同じ旧J零/元a可逆/τ単射 | discharge-required | raw同値から元独立比較H1全単射→旧J零→C8原a両逆/τ単射。Lawは同じラベル原a値とliteral R値で接続 |
| 結論相当のsupplied iso/vanish/rank | conclusion-equivalent-risk | 新入力fieldなし。P/ε/ηは受理済み元M生成系、全a/R/τを同じ値へ接続 |

依存はG134 PR5283 final head `85516e645faa507dfc97c0dd607e209da7071c22`、merge
`196125e049ba96b908bd01ca1352d8579666ab7a`。初回標準監査6027498363は修正要求、
その非中心全finding解消と資格内の単一確認は6027595301。両記録を合わせて受理資格を追跡した。
C8 PR5299 head `4bdc59ea609b94fd087acad580666223c073a502`、merge
`290bb573ddef08da2c77fdf10cd9532bfe3a70f8`、最終受理6052624414。
C11-13の受理・sameheadは各上記受理節へ対応する。
現sourceの生成引数・対象・全Hom・両補正・C8元J0同値・C13元SESτ成分を確認した。
追跡完了predecessor内部全履歴の再認定は行わない。

<!-- cycle14-generated-evidence -->

全90source宣言と44生成宣言の合計134件が新delta。source相対順・全print/log/module auditを一致させた。spine外のscaffold宣言はない。

| file | 宣言（source/print/log/report相対順、生成宣言を含む） |
| --- | --- |
| `PrimitiveSourceBasis.lean` | `PrimitiveSource.basis0`, `PrimitiveSource.basis1`, `PrimitiveSource.basis2`, `PrimitiveSource.basis0_image`, `PrimitiveSource.basis1_image`, `PrimitiveSource.basis2_image`, `PrimitiveSource.basis0_self`, `PrimitiveSource.basis1_self`, `PrimitiveSource.basis2_self`, `PrimitiveSource.basis0_comp`, `PrimitiveSource.basis1_comp`, `PrimitiveSource.basis2_comp` |
| `PrimitiveSourceComparison.lean` | `PrimitiveSource.sourceSubset_eq`, `PrimitiveSource.basis0_selected`, `PrimitiveSource.basis1_selected`, `PrimitiveSource.basis2_selected`, `PrimitiveSource.rawR_eq_generated`, `PrimitiveSource.basis0_law`, `PrimitiveSource.basis1_law`, `PrimitiveSource.basis2_law`, `PrimitiveSource.rawLawR_eq_generated` |
| `PositiveOperation.lean` | `PositiveOperation`, `PositiveOperation.toPrimitive`, `PositiveOperation.coarser`, `PositiveOperation.comparison`, `PositiveOperation.reading`, `PositiveOperation.reading_toPrimitive`, `PositiveOperation.primitive_r0`, `PositiveOperation.primitive_r1`, `PositiveOperation.primitive_r2`, `PositiveOperation.casesOn`, `PositiveOperation.ctorElim`, `PositiveOperation.ctorElimType`, `PositiveOperation.ctorIdx`, `PositiveOperation.noConfusion`, `PositiveOperation.noConfusionType`, `PositiveOperation.presentation`, `PositiveOperation.presentation.elim`, `PositiveOperation.presentation.inj`, `PositiveOperation.presentation.injEq`, `PositiveOperation.presentation.noConfusion`, `PositiveOperation.presentation.sizeOf_spec`, `PositiveOperation.rec`, `PositiveOperation.recOn`, `PositiveOperation.subdivision`, `PositiveOperation.subdivision.elim`, `PositiveOperation.subdivision.noConfusion`, `PositiveOperation.subdivision.sizeOf_spec`, `PositiveOperation.triangle`, `PositiveOperation.triangle.elim`, `PositiveOperation.triangle.noConfusion`, `PositiveOperation.triangle.sizeOf_spec` |
| `PositiveOperationPath.lean` | `PositiveOperationPath`, `PositiveOperationPath.toPrimitive`, `PositiveOperationPath.toPrimitive_nil`, `PositiveOperationPath.toPrimitive_snoc`, `PositiveOperationPath.coarser`, `PositiveOperationPath.comparison`, `PositiveOperationPath.comparison_nil`, `PositiveOperationPath.comparison_snoc`, `PositiveOperationPath.single`, `PositiveOperationPath.single_comparison`, `PositiveOperationPath.primitive_r0`, `PositiveOperationPath.primitive_r1`, `PositiveOperationPath.primitive_r2`, `PositiveOperationPath.subsetR_eq_generated`, `PositiveOperationPath.lawR_eq_generated`, `PositiveOperationPath.below`, `PositiveOperationPath.brecOn`, `PositiveOperationPath.brecOn.eq`, `PositiveOperationPath.brecOn.go`, `PositiveOperationPath.casesOn`, `PositiveOperationPath.ctorElim`, `PositiveOperationPath.ctorElimType`, `PositiveOperationPath.ctorIdx`, `PositiveOperationPath.nil`, `PositiveOperationPath.nil.elim`, `PositiveOperationPath.nil.noConfusion`, `PositiveOperationPath.nil.sizeOf_spec`, `PositiveOperationPath.noConfusion`, `PositiveOperationPath.noConfusionType`, `PositiveOperationPath.rec`, `PositiveOperationPath.recOn`, `PositiveOperationPath.snoc`, `PositiveOperationPath.snoc.elim`, `PositiveOperationPath.snoc.inj`, `PositiveOperationPath.snoc.injEq`, `PositiveOperationPath.snoc.noConfusion`, `PositiveOperationPath.snoc.sizeOf_spec` |
| `PositivePreservation.lean` | `PositiveOperationPath.subsetHomotopyEquiv`, `PositiveOperationPath.subsetHomotopyEquiv_hom`, `PositiveOperationPath.subsetHomotopyEquiv_inv`, `PositiveOperationPath.subsetHomologyIso`, `PositiveOperationPath.subsetHomologyIso_hom`, `PositiveOperationPath.subsetHomologyIso_inv`, `PositiveOperationPath.subsetOldH1Iso`, `PositiveOperationPath.subsetOldH1Iso_hom`, `PositiveOperationPath.subsetOldH1Iso_inv`, `PositiveOperationPath.subsetH1_bijective`, `PositiveOperationPath.subsetDefect_zero`, `PositiveOperationPath.subsetCone_isZero`, `PositiveOperationPath.lawHomotopyEquiv`, `PositiveOperationPath.lawHomotopyEquiv_hom`, `PositiveOperationPath.lawHomotopyEquiv_inv`, `PositiveOperationPath.lawHomologyIso`, `PositiveOperationPath.lawHomologyIso_hom`, `PositiveOperationPath.lawHomologyIso_inv`, `PositiveOperationPath.lawOldH1Iso`, `PositiveOperationPath.lawOldH1Iso_hom`, `PositiveOperationPath.lawOldH1Iso_inv`, `PositiveOperationPath.lawH1_bijective`, `PositiveOperationPath.lawDefect_zero`, `PositiveOperationPath.lawCone_isZero` |
| `PositiveCoefficientPreservation.lean` | `PositiveOperationPath.unitEquiv`, `PositiveOperationPath.unitEquiv_apply`, `PositiveOperationPath.unitEquiv_symm_apply`, `PositiveOperationPath.unitEquiv_apply_symm`, `PositiveOperationPath.tau_injective`, `PositiveOperationPath.tauKernel_eq_bot`, `PositiveOperationPath.totalCone_isZero`, `PositiveOperationPath.lawUnitEquiv`, `PositiveOperationPath.lawUnitEquiv_apply`, `PositiveOperationPath.lawUnitEquiv_symm_apply`, `PositiveOperationPath.lawUnitEquiv_apply_symm`, `PositiveOperationPath.lawTau_injective`, `PositiveOperationPath.lawTauKernel_eq_bot`, `PositiveOperationPath.lawTotalCone_isZero`, `PositiveOperationPath.supportUnitEquiv`, `PositiveOperationPath.supportUnitEquiv_apply`, `PositiveOperationPath.supportTau`, `PositiveOperationPath.supportTau_apply`, `PositiveOperationPath.supportTau_injective`, `PositiveOperationPath.supportTau_native`, `PositiveOperationPath.supportFamilyTau_injective` |

6単一focusedはwarning/error0、全公理集合はpropext/Classical.choice/Quot.soundの部分集合。
validation SHA `d45ff87772c8e8a66cca8a3d1d9e793ced7d0a385f78efaad3d6e773b50776a1`。

| file / source+生成件数 | source SHA256 | 実focused log SHA256 |
| --- | --- | --- |
| `PrimitiveSourceBasis.lean` / 12+0 | `83b3ac55fc42de40f27ad69549037d71e046ef2431a1a2ca9d16339102e67d68` | `af936684759a1c3f508ea15510ffbb52ec8b33ba06f7548d7abacc14da4e936e` |
| `PrimitiveSourceComparison.lean` / 9+0 | `cef0311fa25fe9fc5c796abdb7ad8c858b303ce862705582459f418621140ba2` | `606c93b5c96403cb8a21dd8e819a5f4d9381f6d2df0c93df1dbed435332d04a6` |
| `PositiveOperation.lean` / 9+22 | `4b484f43de0565ea875247d096546e40c818e49cb57d23272d1be029cf5562ab` | `fa5f74df546468835354ff051b47cfd6eb67853ccbc28f8496d599a609063bb5` |
| `PositiveOperationPath.lean` / 15+22 | `13329fb68579ed44d017926065565b7c7f2323be6bb951835da2b102ba275f6e` | `21d98317f639c43fc0acc6f3b588aad32b963cd10f4979679149f22e717866a4` |
| `PositivePreservation.lean` / 24+0 | `02c8c0a3cdb3378c26aea8cfa8157d08d09012275e2c81ddcaf19d20ce4eb5ab` | `6b5c59c7dea72ecacc9149b97e2f49097d9afe41f0f1b1a3bd5d45bc29b0bd31` |
| `PositiveCoefficientPreservation.lean` / 21+0 | `1dbeb937bfdba21d227381a0c8a7e94a6aa4379720f62e53a49f25eff795a3eb` | `97c81c0422737cea6358f6593618a0a88002fad129a773b9ca0fdb43120fbdc3` |

Research full/aggregate/全fileloop/local lake build、Formal実build/移植、全GOAL別finalは未実施。

共通scan SHA `cfd7b203ef8b911e8bf92cb13edb27b5ef81ef072941c6446ebdd29886867d15`。
新Unicode/placeholder/privacy/語彙/逆import0、diff check成功、GOAL/design/Formal不変、
6新直接登録・6対象のmanifest/AG登録各1、静的Research依存方向PASS。

## Cycle 14 初回査読F1への直接対応

[初回標準/root監査](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5305#issuecomment-6059740260)の
数学A/BはNo major findings、LeanA/Bは同じ非中心F1（原始有限列producerのPR誤記）、中心finding0。
F1が名指ししたCycle14の受理元だけをPR5283へ訂正した。以前の混在Law分解のPR5282参照は保持する。
現在使用する原始producer9sourceはfinal head85516e64からbyte不変。
受理メタ記録SHA128e38fda852590523c2c18c369390f910476b08e70fa2c5c0d01e157d73c4ef、
source照合記録SHA6438bec42df9fabc8e77c7e073f7b6b3b73b5843e2b72adaaf254faedc43550e。
Lean全source・全宣言・公理・検証log・台帳statusは初回headのまま。単一新規独立確認と最終受理は未実施。

## Cycle 14最終受理と同期

PR [#5305](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5305)、最終head
`9cdf674adb720d23ade0f8e914426df8b7e2ca48`、merge
`4c605bf104854305d2279e211036f585e0b6e5d2`、2026-10-08T12:30:33Z。
[最終標準/root受理](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5305#issuecomment-6059890330)、
[独立直接確認](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5305#issuecomment-6059873540)、
[Issue同期](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5290#issuecomment-6059919762)。
六終了条件はapprove / proof-obligation-discharged。初回中心0、非中心F1はreport限定修正で解消、
直接確認は資格内・実体解消・新finding0、正式再実行0/2。134宣言全print/実log/module/report/hash一致、標準三公理のみ。
validation SHAd45ff87772c8e8a66cca8a3d1d9e793ced7d0a385f78efaad3d6e773b50776a1、
修正scan SHA7f8741a1eae08a9f6e3a90c3f03710d8926f7df64cae45f15733646b470c9fb1。
直接確認原記録SHA26b81716c1199cd0992c1e11e92a8c70dabae44343d6e8da7e50764e36fba136、
機械記録SHA4c48e624105ef44b085a36cecd9286f8761f70f1fac7f547b7f11d0a7644635d。
最終samehead8checksSUCCESS、Lean37776407058/Tool37776407043。Research実stepsSUCCESS、
Formal実setup/build/kernel/premiseSKIPPED。全GOAL checkpoint、Formal unported。

## Cycle 15 selection

```yaml
ledger_type: target_cycle_result
goal: G-135-aat-atlas-coefficient-fiber
cycle: 15
goal_blob_sha: cd5f3e684b7f390558796797874a1f16b52a6b18
base_oid: 4c605bf104854305d2279e211036f585e0b6e5d2
tracking_issue: 5290
report_path: research/reports/G-135-aat-atlas-coefficient-fiber.md
selection:
  proof_state_ref: Cycle14受理/Issue6059919762・固定D面複製未完
  proof_dag_predecessors: [G134原始FaceDuplication comparison/subsetHom/H1逆/H2差/標準錐とLaw, C4原L/ε像と独立P, C8原a保存必要十分, C10同じ三錐, C11-13原Law/全ラベル台族]
  milestone: 原面複製を同じP/η/εへ接続し、全Aと任意LawでH1保存・原a同型/τ零と選択面非零H2余核/総錐H2を同時に示す
  proof_obligations: [原Option表からL零と実ε三同型生成, canonical逆像とG134全三Homのtransport, 同じ旧H1両逆と元J零/原a同型, literalR零/原τ零, 選択面の実標準H2余核と原coefficient/total錐H2, 任意粗adequate Law/全ラベル/空入力と重複の保持]
  exit_criteria:
    - 全mapped原始辺面表からL三次数零と元ε三線形同型/全標準複体同型を生成する。Pを細複体から再定義しない
    - 面複製のcanonical逆像を元自己reading等号で輸送し、独立aSubnerve比較と元subsetHomを全三成分で一致させ、同じηεを原fold/対角面写像へ戻す
    - 全Aで同じ旧H1比較の順写像と逆・J零を示し、同じ原aの順写像と両逆、literalR零と原τ零を原始表から導く
    - 選択面Fに対して同じcanonical原H2比較の余核をℚへ両方向同定し、同じ原totalConeおよびcoefficientCone H2をℚへ接続する。元fresh面代表の非零性も保持する
    - 任意粗adequate Law/全発生labelへ元生成Homと全三次数座標を接続し、原Law a両逆/R零/τ零と選択labelH2余核/三錐を元ラベル族で保持する
    - 原始セル/支持/粗adequacy/面選択以外の保存/期待rank/vanishを入力にせず、空A/空Law/非選択面と重複incidence・labelを保持し全宣言公理/共通scan/証拠対応を検査する
  selection_reason: D最後のG134接続を原P/ε/η・実診断まで閉じ、H1保存とH2非保存を同じ入力で分離してE/Wへ進む
  expected_result_type: proof-obligation-discharged
  lean_targets: [MappedEvaluation, FaceCloneComparison, FaceCloneCoefficient, FaceCloneHomology, FaceCloneLaw]
  risks: [PをCfineへ再定義, canonical輸送をH1だけで代替, 旧H1同型から全錐零を推論, 全ラベル選択を一般Lawへ暗黙追加, H2余核の向き/原差代表欠落, 原射を同型共役で選び直す]
  unchecked: [六終了条件の実装/検証/正式受理, B/E入力生成有限判定とW全評価と別finalは後続]
```

## Cycle 15 result proposal

```yaml
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: 原面複製の全mapped表から元L零/ε同型を生成し、同じ独立u全Hom/元η対角へ接続。全A/任意Lawで旧H1と原a両逆/R零/τ零、選択面の同じ非零H2余核と原三錐を同時に保持
  exit_criteria_status:
    - 全mapped辺面から原L0/L1/L2零・元ε各次数線形同型と標準複体同型。同じKan生成Pを使用
    - canonical逆像の元自己reading等号と原u全ThreeCochainHomのtransport一致、原ηε/foldとold/fresh面対角を全元で同定
    - 全Aの原旧H1順逆/J零、原a順逆、原literalR零/τ零を元セル表から導出
    - 選択Fで同じcanonical原H2余核とηH2余核/原totalCone H2/原coefficientCone H2をℚへ両方向同定。原fresh-only代表の値1と非零性
    - 任意粗adequate Lawの同じ原全三次数ε・a順逆/J零/R零/τ零・ε錐零。原label族と非選択零性から選択labelH2余核と原η/u錐H2を生成
    - 5単一focused warning/error0、109全宣言source/print/log/module audit/report順一致、標準三公理のみ。原始表/支持/粗adequacy/面選択から生成、空台/空Law/非選択/重複を保持
  split_reason: none
  completion_candidate: no
  lean_artifacts: [MappedEvaluation, FaceCloneComparison, FaceCloneCoefficient, FaceCloneHomology, FaceCloneLaw]
  evidence: [原Option mapped表, 同じKan P, self_preimage全複体輸送, 原G134 subsetHom/section/H2差, 原ηεu因子化, 原Lawラベル族/三錐triangle]
  claim_mapping:
    theorem_names: [MappedCells.evaluationStandardIso_hom, FaceClone.comparison_transport, FaceClone.comparison_standard_square, FaceClone.oldH1Equiv_apply, FaceClone.unit_standard_square, FaceClone.unit2_old, FaceClone.unit2_fresh, FaceClone.unitEquiv_apply, FaceClone.R_zero, FaceClone.tau_zero, FaceClone.nativeFreshCokernelClass_nonzero, FaceClone.nativeH2CokernelEquiv, FaceClone.coefficientConeIso_first, FaceClone.lawEvaluationIso_hom, FaceClone.lawUnitEquiv_apply, FaceClone.lawTotalH2Equiv, FaceClone.lawH2CokernelEquiv]
    source_labels: [GOAL D面複製の同じH1保存/非零H2余核と原三錐, GOAL A/C原P/ηεu/保存へのD適用]
    conjuncts: [全A/全三Hom, 同じ旧/nativeH1両逆/J零/原a両逆, literalR零/原τ零, 選択面非零原余核/錐H2, 任意Law/全発生label/非選択零/原三錐]
    undischarged_assumptions: [B/E全A有限判定・E原始行列producer・W全同経路評価・全GOAL別finalは後続]
    acceptance_point: 六固定終了条件はroot実装検証済み。固定head標準四票とroot受理は未実施
    port_status: unported
  audits:
    premise_delta:
      discharged: [mapped表からL零とε同型, canonical全Homと元G134比較一致, 原H1可逆/J零/原a可逆, literalR零/原τ零, 原fresh非零H2余核と原錐同型, 非選択零から任意Law選択label族]
      remaining: [B/E有限producerとW全評価と別final]
    certificate_provenance:
      discharged: [Pは元Mから右Kan生成, ε同型は原L像/単射から生成, uは独立元生成Hom, H1逆は原G134 section, H2座標は元fresh差/実商, Law三錐と有限族はC11原射]
      unresolved: [正式PR受理は未実施]
    proof_use:
      used: [元edgeMap/faceMap全mapped表, 自己reading逆像, 原G134旧section/面差, 原ηεu全Hom, 原R定義, 元Law粗adequacy/全label台族, 原非選択面全次数保存]
      unused: []
    structure_field_escape: none-found
    route_integrity: pass
    target_fitting: none-found
    vacuity: none-found
    one_way_as_equivalence: none-found
    goal_or_report_reinterpretation: none-found
    validation_refs: [5単一focused/109全print/log/module audit, 下記source/log SHAと共通scan]
    blocking_findings: [正式PR四票/root受理/CIは未実施]
    next_obligation: B/E全A有限消滅判定と原始有理行列から同じa/R/τ/Jを表示し、W全表を同経路で評価する
```

## Cycle 15固定要求・前提と同じ写像の対応

| 固定要求 | 同じ対象・射と構成経路 |
| --- | --- |
| 原Pと三ε | `MappedCells.L0_eq_bot/L1_eq_bot/L2_eq_bot`は原none辺/面がないことから原始生成元を零化する。`evaluation0/1/2Equiv`は同じ独立εの単射と原restriction零から全射を生成、`evaluationStandardIso_hom`は全標準ε射。PはC2受理のcarrier/right Kan生成のまま |
| 原canonical uと元G134全三比較 | `fineStandardIso`は元`self_preimage`の細複体全体輸送。`comparison_transport/comparison_standard_square`で元独立`aSubnerveComparisonHom`を原`FaceDuplication.subsetHom`へ同定。H1だけの比較ではなく全ThreeCochainHom |
| 同じηのfold/面対角 | `unit_standard_square`は原εと全細輸送を原ηへ合成。`unit0_same/unit1_same/unit2_fold/unit2_old/unit2_fresh`は原foldとold/fresh面への同じ全元値。originalPとηを選び直さない |
| H1保存と原a | `nativeH1Equiv/oldH1Equiv`は元G134 section逆を可逆座標で接続。順射は同じ独立u、二逆式で同じ粗/細元を回復。旧J零からC8`unitH1EquivOfZeroDefect`を生成し`unitEquiv_apply`と二逆式で元aを保持 |
| literal Rとτ | `phiH1_zero`はnone辺不在から原ΦH1を零化。`R_zero`は同じliteral kerκstar内、`tau_zero`は同じ原τ。`fiberCone_zero`は原ε同型から全整数次数で導出 |
| 非零H2余核/原三錐 | `nativeH2CokernelOldEquiv`は元標準H2射と旧H2商の全正方形。`nativeFreshCokernelClass`は元fresh-only面1の実商類の逆輸送、`_value/_nonzero`で同じ値1/非零。`totalConeIso/coefficientConeIso`は同じ原u/η錐全体とG134元錐を可逆同定し、全二座標/原triangle第一射一致、各H2をℚへ同定。原ε錐は全次数零 |
| 任意Lawと空/非選択label | `lawEvaluationIso_hom`は原Law ε全複体射。原label値fiberから同じ原a両逆/J零/R零/τ零と原ε錐零。`lawTotalFamilyHomologyEquiv`はC11の原u錐族、`SelectedLabel`は原面支持を選ぶ発生labelのsubtype。非選択成分は原始非選択から全次数零、`lawTotalH2Equiv`は選択labelだけのℚ族。同じ原Lawu/ηのH2余核・錐H2と原triangle第一射を保持 |

| material premise | 分類 | 出所と実使用・放電 |
| --- | --- | --- |
| T0セル・reading・支持・ℚ | ambient-boundary | 元セル名・incidence・台を保持したG134 FaceDuplication原producer。一般全mapped補題はT0 Mから原L/ε/Φを使用 |
| 全mapped he/hf | direction-hypothesis → discharge-required | 一般`MappedCells`で各needed次数へ使用。最終面複製は`edge_mapped/face_mapped`の元some表から放電 |
| 原粗面Fと任意A | direction-hypothesis | D指定面複製入力、支持自己reading逆像を保持。選択hFは非零H2結論だけへ使用、H1/R/τ保存へ要求しない |
| 選択/非選択面hF | direction-hypothesis | 原F台とAの交差有無。非選択を`absent_homology_bijective/absent_totalCone_zero`へ使い、任意Lawへ全ラベル選択を加えない |
| 任意Law・粗adequacy・Source有限 | ambient-boundary | T0。細adequacyは元coarserから生成。Value型有限性なし、元有限発生labelを保持 |
| generic selectedFamilyEquivのe/hz | direction-hypothesis → discharge-required | 一般全族補題のみ。最終Law適用は原選択面錐H2座標と原非選択全次数零から各成分を生成 |
| 全ε同型、H1逆、H2商座標、錐同型 | discharge-required | 原L零/独立ε、原G134受理section/H2差/錐と全標準正方形、C8同じJ零から生成 |
| 保存/vanish/期待rankのsupplied入力 | conclusion-equivalent-risk | 最終面複製入力に追加fieldなし。固定原始F/台と元粗Law adequacyから出力する |

原FaceDuplication producer/旧H1逆/H2差/LawはG134
[PR5284](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5284) final head
`c6138111c0cb60fe566cbdcda77a4702791422ae`、merge
`c36d19589ccc9a75cbfc03cf5af354e1989dd417`、標準受理6028150343。
非選択面・全錐/標準H2接続はG134
[PR5287](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5287) final head
`0134623422114ae39f989d591cb167c6176aae3e`、merge
`6a54e336131eaaea2c61ac20f7f1b5b4f502c96a`、標準受理6030043920、全G134別final受理6030258596。
現在直接使用する8source（FaceDuplication Geometry/Comparison/DegreeTwo/Homology/Law/Absent/Endpoints/ChainSplit）は
PR5287受理headと固定reuse版53b6a67からbyte不変。現適用の対象・原射・生成前提を実sourceと照合した。
受理メタSHA5284は92a8a27bdbe59224fdc0892d3b8e9add0018932011c30f44a33390ee27e62e72、
5287は2a29d34b22e2c0dd2558b1cb07b2ee3b91f3d6ca4566dc01ed28cb81b1f7f8c6、
8source照合SHA6bdea76f8238de3c93c23108f181c577c4ee2b0367c8d279f9eda408602cb615。
C4/C8/C10/C11-13受理は上記各受理節の固定headへ対応する。

<!-- cycle15-generated-evidence -->

全109source宣言、新delta109件、生成宣言0件。source相対順・全print/log/module auditを一致させた。spine外のscaffold宣言はない。

| file | 宣言（source/print/log/report相対順） |
| --- | --- |
| `MappedEvaluation.lean` | `MappedCells.verticalEdge_isEmpty`, `MappedCells.mixedFace_isEmpty`, `MappedCells.degenerateFace_isEmpty`, `MappedCells.L0_eq_bot`, `MappedCells.L1_eq_bot`, `MappedCells.L2_eq_bot`, `MappedCells.restriction0_zero`, `MappedCells.restriction1_zero`, `MappedCells.restriction2_zero`, `MappedCells.evaluation0Equiv`, `MappedCells.evaluation1Equiv`, `MappedCells.evaluation2Equiv`, `MappedCells.evaluation0Equiv_apply`, `MappedCells.evaluation1Equiv_apply`, `MappedCells.evaluation2Equiv_apply`, `MappedCells.evaluation_standard_isIso`, `MappedCells.evaluationStandardIso`, `MappedCells.evaluationStandardIso_hom`, `MappedCells.evaluationHomologyEquiv`, `MappedCells.evaluationHomologyEquiv_apply`, `MappedCells.fiberCone_isZero`, `MappedCells.phiH1_subsingleton`, `MappedCells.R_subsingleton`, `MappedCells.tau_zero` |
| `FaceCloneComparison.lean` | `subsetTransportStandard_square`, `FaceClone.fineStandardIso`, `FaceClone.comparison_transport`, `FaceClone.comparison_standard_square`, `FaceClone.fineH1Equiv`, `FaceClone.fineH1Equiv_apply`, `FaceClone.nativeH1Equiv`, `FaceClone.nativeH1Equiv_apply`, `FaceClone.oldH1Equiv`, `FaceClone.oldH1Equiv_apply`, `FaceClone.nativeH1Equiv_symm_apply`, `FaceClone.nativeH1Equiv_apply_symm`, `FaceClone.oldH1Equiv_symm_apply`, `FaceClone.oldH1Equiv_apply_symm`, `FaceClone.H1_bijective`, `FaceClone.defect_zero` |
| `FaceCloneCoefficient.lean` | `FaceClone.edge_mapped`, `FaceClone.face_mapped`, `FaceClone.L0_zero`, `FaceClone.L1_zero`, `FaceClone.L2_zero`, `FaceClone.evaluationIso`, `FaceClone.evaluationIso_hom`, `FaceClone.coefficientStandardIso`, `FaceClone.coefficientStandardIso_hom`, `FaceClone.unit_standard_square`, `FaceClone.unit0_same`, `FaceClone.unit1_same`, `FaceClone.unit2_fold`, `FaceClone.unit2_old`, `FaceClone.unit2_fresh`, `FaceClone.unitEquiv`, `FaceClone.unitEquiv_apply`, `FaceClone.unitEquiv_symm_apply`, `FaceClone.unitEquiv_apply_symm`, `FaceClone.phiH1_zero`, `FaceClone.R_zero`, `FaceClone.tau_zero`, `FaceClone.fiberCone_zero`, `FaceClone.coefficientConeIso`, `FaceClone.coefficientConeIso_hom` |
| `FaceCloneHomology.lean` | `FaceClone.nativeFineHomologyEquiv`, `FaceClone.nativeFineHomologyEquiv_apply`, `FaceClone.nativeHomology_square`, `FaceClone.nativeH2CokernelOldEquiv`, `FaceClone.nativeH2CokernelEquiv`, `FaceClone.nativeFreshCokernelClass`, `FaceClone.nativeFreshCokernelClass_value`, `FaceClone.nativeFreshCokernelClass_nonzero`, `FaceClone.totalConeIso`, `FaceClone.totalConeIso_hom`, `FaceClone.totalConeIso_apply`, `FaceClone.coefficientConeIso_apply`, `FaceClone.coefficientConeIso_first`, `FaceClone.totalConeH2Equiv`, `FaceClone.coefficientConeH2Equiv`, `FaceClone.unitH2_square`, `FaceClone.coefficientH2CokernelEquiv`, `FaceClone.absent_homology_bijective`, `FaceClone.absent_totalCone_zero`, `FaceClone.absent_coefficientCone_zero` |
| `FaceCloneLaw.lean` | `selectedFamilyEquiv`, `selectedFamilyEquiv_apply`, `FaceClone.lawEvaluationIso`, `FaceClone.lawEvaluationIso_hom`, `FaceClone.lawEvaluationIso_apply`, `FaceClone.lawUnitEquiv`, `FaceClone.lawUnitEquiv_apply`, `FaceClone.lawUnitEquiv_symm_apply`, `FaceClone.lawUnitEquiv_apply_symm`, `FaceClone.lawH1_bijective`, `FaceClone.lawDefect_zero`, `FaceClone.lawR_zero`, `FaceClone.lawTau_zero`, `FaceClone.lawFiberCone_zero`, `FaceClone.lawCoefficientConeIso`, `FaceClone.lawCoefficientConeIso_hom`, `FaceClone.lawCoefficientConeIso_first`, `FaceClone.lawTotalFamilyHomologyEquiv`, `FaceClone.SelectedLabel`, `FaceClone.lawTotalH2Equiv`, `FaceClone.lawTotalH2Equiv_apply`, `FaceClone.lawCoefficientH2Equiv`, `FaceClone.lawH2CokernelEquiv`, `FaceClone.lawCoefficientH2CokernelEquiv` |

5単一focused warning/error0、全公理集合はpropext/Classical.choice/Quot.soundの部分集合。
validation SHA `4a6fcbd3874ecd50ad75459f45d86368ce9a000dccc61d6fddd378bf59668929`。

| file / source+生成件数 | source SHA256 | 実focused log SHA256 |
| --- | --- | --- |
| `MappedEvaluation.lean` / 24+0 | `5cf4664d5b34544d033f85b8cc95ef675043de72717f7d524aed2b170f195e7b` | `cd049a8565e14071f327c2f8cf0ca294bb2c87954cc46132d08753d166000af0` |
| `FaceCloneComparison.lean` / 16+0 | `d5403b62bf9dda7cb6a70014f7d3a1b82b5e61920cbcf1a3059c98fc2e7aadde` | `1a0b3a32aa3cfc881cd320eefe67d1429215e52eaaf80f4e1b75e69a92fd7acc` |
| `FaceCloneCoefficient.lean` / 25+0 | `740c9f8b775c74a6231dbf72123b546566832c6a468be6c6dd6f2e9ba8095abe` | `a8dd36640311d0a77e48cada67c3e107d314ecfc84d40e0729509e18931d7e8c` |
| `FaceCloneHomology.lean` / 20+0 | `005a470d54a7565d189caefe286e9cd9105c309e883848fc5cf4773f57405df5` | `ab03a4819a3abc224b72ad8a5a9b4482c028bff2439084f40a6f1b682833882f` |
| `FaceCloneLaw.lean` / 24+0 | `6d1dfd8d0f8e6be7e5d788c2666a816792582f03d737f90e51e1b3300889bc10` | `6ce8d0ea54971bda48e3b196c145f18b0ea12467132526d073de34a5cfc2cbfc` |

Research full/aggregate/全fileloop/local lake build、Formal実build/移植、全GOAL別finalは未実施。

共通scan SHA `cc79392a0b85c2ede3380bf1d1113c02cd9de91dc2578765ca0455461084bef8`。
新Unicode/placeholder/privacy/語彙/逆import0、diff check成功、GOAL/design/Formal不変、
5新直接登録・対象manifest/AG登録各1、静的Research依存方向228modules PASS。

## Cycle 15初回査読LA-1への直接対応

[初回標準/root監査](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5306#issuecomment-6060895737)、
[数学二票全文](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5306#issuecomment-6060858637)、
[Lean二票全文](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5306#issuecomment-6060865590)。
数学A/B・LeanBはNo major findings、LeanAはMinor issues。中心0、非中心LA-1は
FaceCloneCoefficient:59の「全射正方形」を「全次数の可換正方形」へ訂正する要求。
名指しdocstringだけを修正し、同sourceのSHAと再検証証拠を同期した。
signature/def値/instance値/proof/宣言集合/import方向/台帳statusは初回headのまま、追加宣言0。
変更fileの25単一focusedはwarning/error0、全25公理出力/実logは初回とbyte同一。
他4source/実log不変、全109source/print/log/module/report相対順一致と標準三公理のみを再照合。
初回validation SHAd9427c8c17c99269e4a2ff28a4cd1afe71c8823b32bc4cb9c25e2eca3e0778f2は原票と共に不変保存。
新規単一独立確認と最終受理は未実施、正式再実行0/2。


## Cycle 15最終受理

[PR5306](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5306)、head
`180477fd314e416689beed56f3609edfc91403fd`、merge
`2d4fd059bf1995e6b6e52fcdb39393c612d3884f`、2026-10-08T13:41:06Z。
[標準/root最終受理](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5306#issuecomment-6060895737)、
[新規独立直接確認](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5306#issuecomment-6061145863)。
[Issue同期](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5290#issuecomment-6061191910)。
六終了条件approve / proof-obligation-discharged。初回中心0、非中心LA-1はdocstring限定修正で解消、
四資格PASS、新規finding0、正式reruns0/2。全109source/print/log/module/report順とhash一致、標準三公理のみ。
直接確認raw SHA97efc99539c9507b943066d88f9415859f764e72c428a3601860d062004d2cf6、
機械記録SHA2222c8d544441c6e9ed714478735b474363c766622aba66e411edbe4a1894c29。
最終samehead8checksSUCCESS、Lean37784776666/Tool37784776366実ResearchstepsSUCCESS、Formal実build/kernel/premiseSKIPPED。
全GOAL checkpoint、Formal unported。

## Cycle 16 selection

```yaml
ledger_type: target_cycle_result
goal: G-135-aat-atlas-coefficient-fiber
cycle: 16
goal_blob_sha: cd5f3e684b7f390558796797874a1f16b52a6b18
base_oid: 2d4fd059bf1995e6b6e52fcdb39393c612d3884f
tracking_issue: 5290
report_path: research/reports/G-135-aat-atlas-coefficient-fiber.md
selection:
  proof_state_ref: C15最終受理・B一般τ零原始条件はC6受理済み、有限判定が未完
  proof_dag_predecessors: [C5原B/D/VとmixedCycles, C6原τ零とBy=Hx像包含の両方向, C11原Lawτとlabel族, G107受理rationalMatrixRank]
  milestone: 一般混在の同じ原τ消滅を原始B/D/H/Vブロック行列の実行可能rank判定へ両方向接続し全A/発生labelの有限検査を生成する
  proof_obligations: [制約核の像のrank加法, 原verticalRelationsとBy=Hx像の包含, 原セル自由基底からのブロック行列, 有理Gram rank evaluatorとの一致, 全A有限性と全label判定, 空/loop/平行辺/重複面の保持]
  exit_criteria:
    - 一般有限線形写像の制約核像とブロックrangeのrank加法を証明し、supplied核基底や期待rankを使わない
    - 原B/D/H/VからF(y,x)=By-Hx、WB(v,t)=(Vv+Dt,Bt)、Giant(v,t,y,x)=(Vv+Dt+Dy,Bt,F(y,x))を生成し、元τ零iff rankGiant=rankWB+rankFを両方向証明する
    - 元の名前付き有限セル自由基底で原B/D/H/Vと各ブロック行列を表示し、同じ線形写像の全元表示とsemantic rank一致を証明する
    - 有理入力だけを読むrationalMatrixRankからBool判定を構成し、同じ元τ零/原像包含との必要十分を証明する
    - Source有限とreading全射から全Aの有限列挙を導き、全A消滅および元Law全発生label消滅の有限Bool検査と必要十分にする。Value型有限性は要求しない
    - 空A/空セル/空Lawとloop/平行辺/重複incidence/labelを保持し、対象全宣言のfocused/print/audit/共通scanと出所使用を検査する
  selection_reason: Bに残る一般混在の有限判定を実行可能原始rank経路へ閉じ、E全写像producerの有限線形代数に再利用する
  expected_result_type: proof-obligation-discharged
  lean_targets: [ConstrainedRank, PrimitiveRankCriterion, PrimitiveMatrices, FiniteTauDecision]
  risks: [kernel基底を入力に移す, Pを中間複体へ交換, 原τとrank条件の接続欠落, Classical決定だけで実行可能と表示, 全Aやlabel重複の省略]
  unchecked: [六終了条件実装/検証/正式受理, E原a/R/τ/J全行列表示とW全評価と別finalは後続]
```


## Cycle 16 result proposal

```yaml
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: 原B/D/H/Vの全セル列と制約核像を保つrank加法から同じ原τ零の有理Bool必要十分を構成。全Aおよび全発生label有限検査を元Lawτへ接続
  exit_criteria_status:
    - 制約核の元g像と積射rangeのrank加法、および二独立制約の和射の同じ像の和をrank-nullityから証明
    - 同じ原By-Hx、Vv+Dt/Bt、Giant二制約と原像包含を全代表で接続し、同じ原τ零iff rankGiant=rankWB+rankFを両方向証明
    - 原B/D/H/Vを同じ名前付きsingle基底で表示。三blockの全元表示と同じ元射range次元を証明。原P/η/ε/R/τを選び直さない
    - 純有理四表から各block行列を生成するconstructorとnative表示を全entryで同定。G107 Gram rankからのBoolは元τ零と原像包含の必要十分
    - Source有限とreading全射からtarget有限性、全Finsetと全Setの同値を生成。全A検査および元Law発生label検査を元Law SES τ零へ両方向接続
    - 五単一focused warning/error0、74全source/print/log/audit/report順・hash一致、標準三公理のみ。空入力のtrue・障害有理表のfalseをkernel実評価。空/loop/平行辺/重複面とlabelを一般経路で保持
  split_reason: none
  completion_candidate: no
  lean_artifacts: [TransgressionVanishing所有API, ConstrainedRank, PrimitiveRankCriterion, PrimitiveMatrices, FiniteTauDecision]
  evidence: [原B/D/H/V single列, 同じ元By=Hx像包含とτ双対, 原名付き積基底, G107有理Gram rank, 元Law label族/SES τ成分, 全target有限性]
  claim_mapping:
    theorem_names: [ConstrainedRank.range_prod_finrank, ConstrainedRank.constrainedCoprod_range, primitiveVanishing_iff_image_le, connectingTau_zero_iff_block_rank, primitiveConstraintMatrix_represents, primitiveBaseMatrix_represents, primitiveGiantMatrix_represents, rationalGiantMatrix_eq_primitive, primitiveTauZeroDecision_eq_true_iff, allATauZeroDecision_eq_true_iff, lawTauZeroDecision_eq_true_iff]
    source_labels: [GOAL B一般混在τ零の有限行列包含と全A有限検査, GOAL D同じ実Law τへの適用, GOAL E有限有理線形代数のτ消滅判定部分]
    conjuncts: [同じ原τと原始条件の両方向, 元B/D/H/Vと実block表示全元・全entry, 純有理判定kernel, 全A/全発生label有限検査, 元Lawτ全成分]
    undischarged_assumptions: [E同じa/R/τ/J全行列表示と全A/label保存判定、W全指定表同経路評価、全GOAL別finalは後続]
    acceptance_point: 六固定終了条件の構成とroot検証を完了。正式四票/root受理/CIは未実施
    port_status: unported
audits:
  premise_delta:
    discharged: [制約核像rank加法, 元原始包含とrank等式, 原セル基底と同じblock表示, 有理rankから元τ零判定, 全A有限化, 同じ実Lawτと全label判定]
    remaining: [E全写像表示/保存判定・W全評価・別final]
  certificate_provenance:
    discharged: [原自由セルsingle基底/元B/D/H/V列, 原C6τ零両方向, 有理表からblock生成, G107受理rank producer, Source→reading有限性, 元Law発生labelとτ座標]
    unresolved: [正式PR受理未実施]
  proof_use:
    used: [原B/D/H/VとBy=Hx, 元mixedCyclesとV/D実関係代表, 制約二座標とrank-nullity, 元セルsingle基底, 元Source有限/reading全射, Law原SES τ成分とliteralR族同値]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [五単一focused/74全print/log/audit, 下記source/log SHA・共通scan]
  blocking_findings: [正式四票/root受理/CIは未実施]
  next_obligation: Eの同じ原a/R/τ/Jの全有理行列表示と保存判定を構成し、W1–W5全原始表を同経路で評価する
```

## Cycle 16固定要求・同じ写像と前提

| 固定要求 | 実構成と同じ射の対応 |
| --- | --- |
| 一般制約核像rank | `restrictedKernelEquiv`は元g/f共通核とgのker f制限核の同じ元による両逆。`range_prod_finrank`は三rank-nullityと実核同型から導出。`constrainedCoprod_range`は元制約核の実代表と和の両包含 |
| 原τ零と原始rank | `primitiveConstraint/BaseOutput/BaseConstraint/LiftOutput`は元B/D/H/Vの実射合成・和。`mem_primitiveBaseImage`は同じ元mixedCycles kerBのVv+Dt。`primitiveVanishing_iff_image_le`は元By=Hx代表に両方向適用。`connectingTau_zero_iff_block_rank`はC6同じ元τ零同値と上記rank加法、部分空間包含・同次元等号を使用 |
| 原始セルから行列 | `primitiveB/D/H/VMatrix_entry`は同じ原セルsingle列。三blockの行列は原セル積基底だけを使用、`*_represents`で任意元の元射値、`*_rank`で実range次元。元P・Rは既存のままで、任意複体/自由なhomology基底を入力にしない |
| 四有理表と同じ表示 | `rationalConstraint/Base/GiantMatrix`は元B/D/H/V表の列/符号/零を保つpure constructor。`*_eq_primitive`は同じ原射の全entry一致。`rationalPrimitiveTauDecision`は原四有理表だけを読み、G107 Gram rank kernelを適用。native `primitiveTauZeroDecision`で表を元Mから生成 |
| 全A | `readingTarget_finite`はSource有限とq.surjectiveを実使用。全Finset検査と全Setの同値を元任意台の有限化から導出し、`allATauZeroDecision_eq_true_iff`へ接続。空Aを除かない |
| 全元Law | `lawTauZeroDecision`は既存LawValueLabel型をそのまま走査。`lawConnectingTau_zero_iff_labels`は元Law R族の両逆とsingle代表、元SES τ成分を実使用し、元Lawτ零と全原labelτ零を両方向同定。同じ台を持つ別Law labelを商にしない |

| material premise | 分類 | 出所・実使用と放電 |
| --- | --- | --- |
| T0 M・支持・セル有限・ℚ | ambient-boundary | 固定T0。元セルclassとB/D/H/Vから原始block・基底を生成。pure/forest/保存/期待rankは一般入力に要求しない |
| 一般補題の有限次元X/Z | direction-hypothesis → discharge-required | generic rank-nullityの必要条件。元有限セルfree chain/積から自動生成 |
| Fintype/DecidableEqのセルindex | discharge-required | T0の元有限セル部分型からofFinite。名前付きsingleと積基底以外のhomology/核基底を受け取らない |
| generic有理B/D/H/V表 | direction-hypothesis → discharge-required | 任意有限有理表kernelの入力。最終元M適用は同じ元primitiveMatrixから生成し、全entry/native射/rankへ証明で接続 |
| Source有限・reading全射 | ambient-boundary | T0。実target有限性と全A検査に使う。Value型全体の有限性なし |
| Law/粗adequacy/発生label | ambient-boundary | T0。原labelValueFiberと原SES/τ/R族を使用。既存発生label有限性を再利用、ラベルごとの消滅を新fieldへ移さない |
| 像包含/期待rank/τ零/certificate | conclusion-equivalent-risk | 最終入力fieldとして追加せず、原表・generic rank correctnessとC6同値から出力する |

任意Set/抽象セル型を含むnative入力の有限列挙・表示は非計算的。実行kernelは有限有理B/D/H/V表のみを読み、semantic rank/核/像/消滅のoracleを読まない。
その二つを全entry・全元・元τの必要十分で接続した。Eの全a/R/τ/J行列表示やWの同経路全評価をこのτ零判定だけで代替しない。
空有理表trueと障害有理表falseは`decide +kernel`で実評価し、非標準のnative計算公理を使用しない。これはkernel発火検査で、W1–W5の証拠は後続。

G107 `ExecutableRationalRank`は[PR3994全GOAL受理](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/3994#issuecomment-5279154319)、head84050e9592635418198a41cbc23f2051f023b861、merge4c80532dded00ab2b5b0a7e066b7bd355ac1ede6に対応。
現sourceはその受理headおよび固定reuse版53b6a67からbyte不変。実使用はrationalMatrixRankとrank/実range一致の公開API、現statement・適用条件を確認済み。
出所照合SHA788f47b44bda6c5d477d5c2006d415eb48a99fd9ac0177dd604c677769101352。C5/C6/C11受理は前述固定headへ対応する。

<!-- cycle16-generated-evidence -->

全74source宣言、新delta69件（既存TransgressionVanishingへの所有API1と新四module）、生成宣言0件。source/全print/log/module audit/reportの相対順を一致させ、spine外scaffoldはない。

| file | 宣言（source/print/log/report相対順） |
| --- | --- |
| `TransgressionVanishing.lean` | `PrimitiveTransgressionVanishing`, `primitiveTransgressionVanishing_iff`, `horizontalChainConnecting_zero_iff_primitive`, `connectingTau_zero_iff_chain`, `connectingTau_zero_iff_primitive`, `connectingTau_allA_zero_iff_primitive` |
| `ConstrainedRank.lean` | `ConstrainedRank.restrictedKernelEquiv`, `ConstrainedRank.range_prod_finrank`, `ConstrainedRank.constrainedCoprod_range`, `ConstrainedRank.range_prodMap_finrank` |
| `PrimitiveRankCriterion.lean` | `primitiveConstraint`, `primitiveConstraint_apply`, `primitiveBaseOutput`, `primitiveBaseOutput_apply`, `primitiveBaseConstraint`, `primitiveBaseConstraint_apply`, `primitiveLiftOutput`, `primitiveLiftOutput_apply`, `primitiveBaseBlock`, `primitiveBaseBlock_apply`, `primitiveGiantBlock`, `primitiveGiantBlock_apply`, `primitiveGiantBlock_apply_all`, `mem_primitiveBaseImage`, `primitiveVanishing_iff_image_le`, `connectingTau_zero_iff_block_rank` |
| `PrimitiveMatrices.lean` | `matrix_represents_map`, `matrix_rank_eq_range`, `primitiveBMatrix`, `primitiveBMatrix_entry`, `primitiveDMatrix`, `primitiveDMatrix_entry`, `primitiveHMatrix`, `primitiveHMatrix_entry`, `primitiveVMatrix`, `primitiveVMatrix_entry`, `primitiveConstraintMatrix`, `primitiveBaseMatrix`, `primitiveGiantMatrix`, `primitiveConstraintMatrix_entry`, `primitiveBaseMatrix_entry`, `primitiveGiantMatrix_entry`, `primitiveConstraintMatrix_represents`, `primitiveBaseMatrix_represents`, `primitiveGiantMatrix_represents`, `primitiveConstraintMatrix_rank`, `primitiveBaseMatrix_rank`, `primitiveGiantMatrix_rank` |
| `FiniteTauDecision.lean` | `rationalBlockTauDecision`, `rationalBlockTauDecision_eq_true_iff`, `rationalConstraintMatrix`, `rationalBaseMatrix`, `rationalGiantMatrix`, `rationalPrimitiveTauDecision`, `rationalPrimitiveTauDecision_eq_true_iff`, `finiteFamilyDecision`, `finiteFamilyDecision_eq_true_iff`, `rationalPrimitiveTauDecision_empty`, `rationalPrimitiveTauDecision_failure`, `finiteFamilyDecision_empty`, `rationalConstraintMatrix_eq_primitive`, `rationalBaseMatrix_eq_primitive`, `rationalGiantMatrix_eq_primitive`, `primitiveTauZeroDecision`, `primitiveTauZeroDecision_eq_true_iff`, `primitiveTauZeroDecision_eq_true_iff_primitive`, `readingTarget_finite`, `allFinsets_iff_allSets`, `allATauZeroDecision`, `allATauZeroDecision_eq_true_iff`, `lawTauZeroDecision`, `lawTauZeroDecision_eq_true_iff_labels`, `lawConnectingTau_zero_iff_labels`, `lawTauZeroDecision_eq_true_iff` |

五単一focusedはexit0/warning/error0、全公理はpropext/Classical.choice/Quot.soundの部分集合。validation SHA `28ebc888407605d200a22cc8782a5cd570b40265f6be6fffabf54fc3bdc65890`。

| file / source+生成件数 | source SHA256 | 実focused log SHA256 |
| --- | --- | --- |
| `TransgressionVanishing.lean` / 6+0 | `e0c1de1dcd6d1ff15aa0406d08ec90dc946a09becaa0629f9f2c95cc5d7d5515` | `b5db000d8233d708a7ee04e395a29fc0e4823fe12f5709751276768d5fb0905b` |
| `ConstrainedRank.lean` / 4+0 | `539ad5e865b01829b9b7022b175a01431a402024069385d06c94938555bc5a70` | `96f45ba4fbae114fafd2817cce0628c7a915a91ca3bb7ff0595ba1d4b7f8a86f` |
| `PrimitiveRankCriterion.lean` / 16+0 | `2cb607759e052980eb6d74d552d62384c91af959443d57a2cf9e70f3ba727b4a` | `19509cb4d08ea0351ccfc5914785c2cbce47e469d1ae7fa5e266bac73daccd7c` |
| `PrimitiveMatrices.lean` / 22+0 | `01b190db58b95cc3a10f7f05df6c759ac354ae94c4ff535b49679f02e4a9da15` | `50d34b8ac6c748b924fa908050d0e139243846d0e19f8875a2ec0b5d75e9c3da` |
| `FiniteTauDecision.lean` / 26+0 | `d2022189715eb87149c34b27860b5216544d10df8accef3452721cabcaee39da` | `470cf1c99129fdea42b6e1ffb3e007678fbab98b5f2a4af57b66521e5d8d911b` |

Research full/aggregate/全fileloop/local lake build、Formal実build/移植、全GOAL別finalは未実施。

共通scan SHA `34b2f2a123c135d006d115cdb0491a2a5e43badccaf1734626b802912a78e55a`。
新Unicode/placeholder/privacy/語彙/逆import0、diff check成功、GOAL/design/Formal不変。
四新module登録・直接AG import各1、既存TransgressionVanishing登録不変、静的Research依存方向228modules PASS。


## Cycle 16初回査読への文書修正

[初回標準/root監査](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5307#issuecomment-6062198222)、
[数学二票全文](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5307#issuecomment-6062158151)、
[Lean二票全文](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5307#issuecomment-6062159018)。
四票Minor issues、中心0。非中心F1は新規19theoremのdocstring欠落、F2は新四moduleの設計理由と代替案理由の記述不足。
名指し19docstringと四moduleのImplementation notesだけを追加。全74宣言・signature・proof・def/instance値・import・進捗statusは不変。
初回→修正の非comment token一致、四修正moduleの再focusedは全exit0/warning/error0、標準三公理のみ。
source/print/log/audit/report74件とhashを再照合し、初回原票/log/metadataは不変保存。
有資格な新規独立直接確認とsamehead CI/root最終受理は後続。正式reruns0/2、completion_candidate:no。


## Cycle 16直接確認後の説明補完

[限定直接確認](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5307#issuecomment-6062464922)は
F2解消、F1のDecision三docstringの内容不足を未解消とし、四資格1FAIL/2・3・4PASS。
共有review protocolに従い正式四票の再実行へ戻す。原票raw SHA91341f90c8e218a7f1978d8a6796c01cfc48258517eac2acb92b29cf6c99bfa4、
機械記録SHAfcc9c9b05ccee1c948833e7b5e82185c7e319bb121236bf9a918976c43b3cf8c。
名指し三docstringへ定義所有APIの役割・設計§3/GOAL B/D対応・generic有限添字と元セル/台族/label列挙の出所を記した。
追加観測D1はConstrainedRankの保存metadata namespaceの初回からの誤記で、実source/log/auditは正常。
今回metadataを実namespaceへ訂正し、74全宣言の実公理監査・順序・件数・source/log hashを再照合した。
数学statement/signature/proof/def/instance値/import/宣言集合/進捗statusは不変。
正式再実行1/2待ち、全GOAL checkpoint/未完E・W・別final、Formal unportedを保持する。

## Cycle 16最終受理と同期

PR [#5307](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5307)は最終head `89e656e7e4b537b0c287e43c1ae8b704aba190e2`、merge `f874b0315d721e2c18bf70a1463c7ca89bdad18a`。
[正式数学二票](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5307#issuecomment-6062882896)と[Lean二票](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5307#issuecomment-6062887049)の中心findingは0。
F3のreport現状態一文は[有資格独立直接確認](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5307#issuecomment-6063052523)で四資格全PASS、数学source/status不変で解消。
最初の直接確認は資格1FAILとなり、規則どおり正式再実行1を行った。[13項目root最終受理](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5307#issuecomment-6063082167)と[Issue同期](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5290#issuecomment-6063139939)へ対応する。
全74宣言・新69・生成0、標準三公理のみ。root五単一focusedと四票各指定単一focusedはexit0/warning/error0。validation SHA `28ebc888407605d200a22cc8782a5cd570b40265f6be6fffabf54fc3bdc65890`、scan SHA `34b2f2a123c135d006d115cdb0491a2a5e43badccaf1734626b802912a78e55a`。
最終head全8CI成功、Lean37798629764/Tool37798629838実head・実steps一致、Research整合性検査成功、Formal実build等SKIPPED。Researchfull/aggregate/全fileloop/build、Formal移植なし。
六終了条件はproof-obligation-discharged、全GOALはtarget-proof-checkpoint、Formal unported、Issue OPEN。E残部/W/別finalへ継続する。

## Cycle 17 selection

```yaml
ledger_type: target_cycle_result
goal: G-135-aat-atlas-coefficient-fiber
cycle: 17
goal_blob_sha: cd5f3e684b7f390558796797874a1f16b52a6b18
base_oid: f874b0315d721e2c18bf70a1463c7ca89bdad18a
tracking_issue: 5290
report_path: research/reports/G-135-aat-atlas-coefficient-fiber.md
selection:
  proof_state_ref: Cycle16受理/Issue6063139939・E同じa/R/τ/J全表示は未完
  proof_dag_predecessors: [G107有理Gram rankと両方向correctness, C16原セルsingle/積行列と原τ判定, C4原L/ε像と元商同定]
  milestone: Eの入力有理行列から実像・核・余核商の座標を生成し、両方向同定・代表元式・計算次元を証明する
  proof_obligations: [有理adjugate逆と原Gram選択API, 計算rankから最大独立列全族の生成, 平均Gram射影の実像/対称/冪等, 元核への補射影の両包含, 元余核商との両逆/代表元, 空/矩形/重複列での同計算経路]
  exit_criteria:
    - 有限ℚ表だけからadjugate逆と最大Gram-good全族を実行可能に構成し、原G107計算rankと元列選択の存在/同像を証明。owner API追加は既存値/statement不変
    - 平均Gram射影のrangeが元行列rangeに等しく、元像全元を固定し、対称/冪等/元transpose核とのkernel等号を証明
    - Iからtranspose像射影を引いた計算kernel射影が元kerの同じ全元を表し、両包含・固定元・冪等と次元を証明
    - 元行列rangeによる商を生成座標へ両方向線形同型にし、全元のquotient代表式・逆公式と計算rankによる余核次元を証明
    - 空行/列/零rankと矩形projection/inclusion/重複列を同producerで評価、全宣言focused/print/audit/scan/出所を固定
  selection_reason: 原P/Qやhomology基底を入力へ移さず同じa/R/τ/Jの有限表示へ進むための生成線形代数を一つの再利用可能な到達点として閉じる
  expected_result_type: proof-obligation-discharged
  lean_targets: [UniformInvariance/ExecutableRationalRank所有API, AtlasCoefficientFiber/RationalGramProjection, AtlasCoefficientFiber/RationalImageProjection, AtlasCoefficientFiber/RationalKernelCoordinates, AtlasCoefficientFiber/RationalQuotientCoordinates]
  risks: [非計算Matrix inverseをkernelに使う, 期待rank/基底の入力供給, 空rankの非空条件追加, 平均の分母零, 元商を自分の像商へ交換, foreign定義unfold, 原P/Qを一般中間複体へ交換]
  unchecked: [上記五終了条件は実装/検証/受理待ち, 原P/Q/H1座標と同じa/R/τ/J全表示/全A保存は後続, W全評価/別finalは後続]
```

このcycleの一般有限有理表は方向仮定であり、原M適用では各entryの原始生成と原P/Q/κ/R/τ・旧商への接続が別の放電義務として残る。一般射影だけで全E完了としない。元Pは独立右Kan構成を保ち、原ε・restrictionを通じて座標を同定する。恒久設計とGOALは変更しない。

## Cycle 17 result proposal

```yaml
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: 原有理表の計算rankから最大Gram全族を生成し、その平均が原像・transpose核を両方向に表す。補射影で原核を生成し、原range商の両逆と代表元式・計算rankの元blockDefect一致を接続
  exit_criteria_status:
    - adjugateInverseは実行可能有理式、標準Matrix逆と全入力で一致。maximalGramSelectionsは計算rankから非空を導き各族の原range等号を証明。既存G107値/statement/proofは不変
    - imageProjectionは原range全元を固定しrange等号/対称/冪等/原transpose核等号を証明
    - kernelProjectionは原Ax=0への全元作用/両包含/固定元/冪等/対称と原核次元への計算rankを証明
    - quotientCoordinateEquivは原matrix range商と生成像の両方向同型、元商全代表式/逆の元class/両逆/余核次元、generatedCoordinateRanks_eq_blockDefectを証明
    - 空行/列/両方・矩形projection/inclusion・重複列の同producer行列/診断対をdecide +kernelで評価。五単一targetの全source/生成/print/log/auditを固定
  split_reason: none
  completion_candidate: no
  lean_artifacts: [G107所有API四補題, RationalGramProjection, RationalImageProjection, RationalKernelCoordinates, RationalQuotientCoordinates]
  evidence: [元有理表, G107計算rankのsound/complete, 同じ元列span/range, 元transpose式, 標準quotKerEquivRange, 下記全91宣言と五単一実log]
  claim_mapping:
    theorem_names: [下記全宣言表]
    source_labels: [GOAL E, 設計README§6]
    conjuncts: [入力生成像/核/商座標, 両方向/代表元式, 計算rankと元defect, 空/矩形/重複の実評価]
    undischarged_assumptions: [原MからP/Q/homology座標生成と全同写像transport, 全a/R/τ/J表示/全A保存, W全経路/別final]
    acceptance_point: Cycle17五終了条件の実装・root検証proposal。正式PR四票/root受理/CIは後続
    port_status: unported

audits:
  premise_delta:
    discharged: [最大Gram族存在/原range等号/分母非零/像核商両逆は表から生成]
    remaining: [原M適用時の有限原始表と同じP/Q/H1/R/τ表示・全A/label保存/W/別final]
  certificate_provenance:
    discharged: [期待rankや基底なしの全有限Gram探索, 原rangeと原kerの同値, 原quotientの全代表]
    unresolved: [原P/Q/κ/R/τと旧homologyの全成分輸送は後続]
  proof_use:
    used: [原列選択, determinant逆, rank両方向, 同じ原range, 原transpose, 有限族card, 原quotKerEquivRange]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [下記source/log/validation SHA, 五単一focused/cache target, 全91print/audit, 共通scan]
  blocking_findings: [正式PR四票/root受理/CIは未実施]
  next_obligation: 原L・ε/restrictionと同じP/Qのdegree/homology座標、原a/R/τ/J全行列表示・全A/label保存、W全原始表同経路評価
```

## Cycle 17固定要求・前提と依存

一般入力は任意有限行/列を持つℚ行列だけで、有限性/列挙はE原有限表の方向仮定である。DecidableEqはidentity/determinantの有限添字にのみ用いる。原M適用時には原セル/原incidence/signからの生成が別途放電される。結論相当のrank/核基底/像包含/零性/射影lawをfieldやinstanceに供給しない。
`adjugateInverse`はdet⁻¹•adjugateを計算し、非計算的な標準Matrix inverseはcorrectness側だけで使う。`maximalGramSelections`は計算rankサイズの全族とBoolを読む。原rangeへの包含と証明済み同次元から各族が元像を張り、非空族の平均は元像を固定する。対称性と元PA=Aのtransposeから原transpose核へ両方向接続する。空rankの空族を排除しない。
`kernelProjection`の原方程式と原range商の同型は元全代表を量化し、inverseは元classを返す。quotient transportは標準非計算同型だが、代表式の計算matrixは実行可能である。`generatedCoordinateRanks_eq_blockDefect`は同じ原matrix mapのliteral核/余核の寸法対に一致する。
原Pを任意中間複体へ交換していない。P/Qのdegreeとhomology座標、元ε/restriction/η/u・原κ/R/τ・旧商の全成分一致と基底変更の自然な同型、全A/label保存判定、W全同経路評価は後続義務である。generic射影だけを全E達成と数えない。

G107の受理PR3994/ref5279154319/head `84050e9592635418198a41cbc23f2051f023b861`とCycle17 baseの原sourceはSHA `79835a78a693cfbb758708780e54704d27caae9f443d4a53a01d810490b87f09`。今回は選択列entry/Gram式/transpose評価/range包含の所有API四補題と全printだけを追加し、既存の値/statement/proof/importの全非コメントtokenは不変と検算した。下流はこれらの所有APIを使い、既存列選択の定義を展開しない。出所は `.tmp/g135/cycle17-owner-provenance.json` に固定する。
固定Lean4.28.0/mathlib8f9d9cffのMatrix nonsingular inverse/transpose/mulVec/range/quotKerEquivRange/finite dimensionを使用し、適用条件を実sourceで確認した。標準基盤の内部全履歴を再認定しない。

## Cycle 17宣言・公理・実log

<!-- cycle17-generated-evidence -->

sourceの全宣言順を各print/実log/報告へ対応させる。全91＝source89＋生成2、新64＝新source62＋新生成2。生成補助はGram moduleの`adjugateInverse.congr_simp`と、Quotient moduleの実評価で生成された`kernelProjection.congr_simp`であり、個別printとmoduleauditへ含める。全公理集合は標準propext/Classical.choice/Quot.soundの部分集合だけ。

| file | 全source/生成宣言（source順、生成は末尾） | source SHA256 | 実log SHA256 |
| --- | --- | --- | --- |
| `ExecutableRationalRank.lean` | `selectedColumns`, `columnGram`, `selectedColumns_apply`, `columnGram_eq_transpose_mul`, `selectedColumns_transpose_mulVec`, `selectedColumns_range_le`, `columnGram_det_ne_zero_iff`, `selectionIndependent`, `selectionIndependent_eq_true_iff`, `hasNonzeroGramMinor`, `hasNonzeroGramMinor_eq_true_iff_exists`, `selectedColumns_rank_le`, `selectedColumns_rank_eq`, `rank_eq_of_selectedColumns_basis`, `hasNonzeroGramMinor_eq_true_iff`, `rationalMatrixRank`, `rationalMatrixRank_eq_rank`, `rationalMatrixRank_eq_finrank_range`, `rationalMatrixDefect`, `rationalMatrixDefect_eq_blockDefect`, `rank_pos_of_entry_ne_zero`, `Examples.projectionMatrix`, `Examples.inclusionMatrix`, `Examples.duplicateColumnMatrix`, `Examples.projectionMatrix_rank`, `Examples.inclusionMatrix_rank`, `Examples.duplicateColumnMatrix_rank`, `Examples.identityMatrix_rank`, `Examples.zeroMatrix_rank`, `Examples.projectionMatrix_defect`, `Examples.inclusionMatrix_defect` | `63c45770d6b0a428213a5002ab7d01c6c6a67579344a5ff1d126ce195d26e8c7` | `892640157f3abc49bc93c885d2c2f7b61bce68507800afc7d0e29932c8b1aec3` |
| `RationalGramProjection.lean` | `adjugateInverse`, `adjugateInverse_eq_inverse`, `adjugateInverse_mul`, `mul_adjugateInverse`, `adjugateInverse_transpose`, `maximalGramSelections`, `mem_maximalGramSelections_iff`, `maximalGramSelections_nonempty`, `maximalGramSelections_range`, `gramProjection`, `gramProjection_mulVec`, `gramProjection_mul_selectedColumns`, `gramProjection_fixes_range`, `gramProjection_transpose`, `adjugateInverse.congr_simp` | `24f1fd38fdf5b48ed11eff88ea00a5786e357f460fa9780f034d4d44419c8533` | `a5c3d101277ec6f97b8427b918d85031e8263de2a2ed6d94012fb7753c460081` |
| `RationalImageProjection.lean` | `imageProjection`, `maximalGramSelections_card_ne_zero`, `imageProjection_mulVec`, `imageProjection_fixes_range`, `imageProjection_mulVec_mem_range`, `imageProjection_range`, `imageProjection_transpose`, `imageProjection_mul_self`, `imageProjection_mul`, `imageProjection_mulVec_eq_zero_iff`, `imageProjection_ker` | `11046b918cbe907493e98e2b461437c137a342ac9185ca0ef7fe7303248d2484` | `3dfd6fbab6a8736ccfb116bfb751d9546dd3dcbdbf784f917da7a08dedd0396c` |
| `RationalKernelCoordinates.lean` | `kernelProjection`, `kernelProjection_mulVec`, `mul_kernelProjection`, `kernelProjection_mulVec_mem_ker`, `kernelProjection_fixes_ker`, `kernelProjection_range`, `kernelProjection_mulVec_eq_zero_iff`, `kernelProjection_ker`, `kernelProjection_mul_self`, `kernelProjection_transpose`, `kernelProjection_rank` | `4f8e64eb70087ebb129b5b059b05a9265bfb2333fb62a16d010ca22421ab316e` | `a929aad43e778187768f0371dd45be55c2b570651cffbf2052e157ad0876e198` |
| `RationalQuotientCoordinates.lean` | `quotientCoordinateEquiv`, `quotientCoordinateEquiv_mk`, `quotientCoordinateEquiv_symm_apply`, `quotientCoordinateEquiv_left_inverse`, `quotientCoordinateEquiv_right_inverse`, `quotientCoordinateEquiv_rank`, `generatedCoordinateRanks_eq_blockDefect`, `Examples.projection`, `Examples.inclusion`, `Examples.repeatedColumns`, `Examples.projection_kernel`, `Examples.projection_quotient`, `Examples.inclusion_image`, `Examples.inclusion_quotient`, `Examples.repeatedColumns_image`, `Examples.repeatedColumns_kernel`, `Examples.emptyRows_kernel`, `Examples.emptyColumns_quotient`, `Examples.empty_image`, `Examples.projection_coordinate_ranks`, `Examples.inclusion_coordinate_ranks`, `Examples.repeatedColumns_coordinate_ranks`, `kernelProjection.congr_simp` | `2f9e9a8ffea765a5315e1064d9bc12ff87853ddd2cecaef77866716e6487f53b` | `83f57808c891bc8c463b3df3abe7382ad061a66aa242b8e6cace6bc8480965cf` |

validation `.tmp/g135/cycle17-validation.json` SHA `77aeff86cb1ba8e096ec025c3675db104e1828aa1d48d8b89bb6ba995716f70a`。全宣言の公理集合・source/print/log同順、各moduleaudit、source/log SHAを収録した。

| 単一対象 | 実行・結果 |
| --- | --- |
| `ExecutableRationalRank.lean` | `bash research/lean/check_research_modules.sh --focused ResearchLean/AG/UniformInvariance/ExecutableRationalRank.lean`、cwd `.`、exit0/warning/error0、print/moduleaudit 31 |
| `RationalGramProjection.lean` | `lake env lean -o .lake/build/lib/lean/ResearchLean/AG/AtlasCoefficientFiber/RationalGramProjection.olean ResearchLean/AG/AtlasCoefficientFiber/RationalGramProjection.lean`、cwd `research/lean`、exit0/warning/error0、print/moduleaudit 15 |
| `RationalImageProjection.lean` | `lake env lean -o .lake/build/lib/lean/ResearchLean/AG/AtlasCoefficientFiber/RationalImageProjection.olean ResearchLean/AG/AtlasCoefficientFiber/RationalImageProjection.lean`、cwd `research/lean`、exit0/warning/error0、print/moduleaudit 11 |
| `RationalKernelCoordinates.lean` | `lake env lean -o .lake/build/lib/lean/ResearchLean/AG/AtlasCoefficientFiber/RationalKernelCoordinates.olean ResearchLean/AG/AtlasCoefficientFiber/RationalKernelCoordinates.lean`、cwd `research/lean`、exit0/warning/error0、print/moduleaudit 11 |
| `RationalQuotientCoordinates.lean` | `bash research/lean/check_research_modules.sh --focused ResearchLean/AG/AtlasCoefficientFiber/RationalQuotientCoordinates.lean`、cwd `.`、exit0/warning/error0、print/moduleaudit 23 |

rootの三target cache出力は必要な依存file一つずつの`lake env lean -o`だけであり、build/aggregate/全fileloopではない。namespace実inventoryの単一非aggregate複写scaffoldはignored `.tmp` に置き、生成二宣言のcoverageにだけ使用した。恒久sourceには足場を残さない。Formal移植/実build、Researchfull/aggregate/全fileloop、E残部/W全評価/別finalは未実施。

共通scan `.tmp/g135/cycle17-scans.json` SHA `a3c72f886aa1b9ddc708e355ab7cb44615ab4f1b1471b15e49902531f63724ad`。変更八fileのhidden/BiDi、Lean placeholder、privacy/local path、追加語彙、逆importの新ヒット0。diffcheck成功、固定GOAL/design/Formal不変、manifest/直接AG import四新module各1。静的root import方向228modulesとpackage方向は成功。

## Cycle 17初回四票F1への直接対応

初回head `0aa0e80536c049d6f9fc9c96c77be778a11c1d95` の新規独立四票は数学A/BがNo major findings、LeanA/BがMinor issues。中心0、非中心F1二箇所を一括採用した。全文はPR5309の数学6063884651・Lean6063889026、root初回監査は[6063916705](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5309#issuecomment-6063916705)。各票はsource/全91宣言/実log/出所/同head CI実stepsを独立検算した。

F1（LA-1/LB-F1）: Gram membershipの既存selectionIndependent直接展開と、元blockDefectのrfl還元。修正は名指し二証明の内部に限る。Gramは既存selectionIndependent_eq_true_iffとcolumnGram_det_ne_zero_iff、dimension対は既存blockDefect_eq_finrank_sub_rangeと標準rank-nullity/quotient dimensionを使用する。全theorem signature・def/instanceの値・宣言集合・import・ledger statusは維持し、新宣言なし。実log/対応source SHAだけ更新する。

初回raw四票と五targetの旧validation/scan、変更二targetの旧実logはignored記録へ不変保存した。有資格性・実体解消は新規単一finding限定確認に委ね、一条件でも不成立/判定不能なら正式四票再実行へ戻す。現formal reruns0/2、修正の受理は未判定。全GOALはcheckpoint、E残部/W/別finalとFormal未移植を維持する。

## Cycle 17最終受理と同期

PR [#5309](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5309) はhead `76fe2000fb1815202d748d6599b6614aadf6a429`、実merge `767ec4d86ecea481a8e68b04a8af78fca5d96f9d`、時刻 `2026-10-08T16:14:33Z`でMERGEDを確認。[最終root受理](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5309#issuecomment-6064145730) はNo major findings（五終了条件）・proof-obligation-discharged。[新規F1限定確認](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5309#issuecomment-6064114234) は四資格全PASS、対象外新finding0。正式reruns0/2。[Issue同期](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5290#issuecomment-6064170174) を完了し、Issue5290 OPENを維持する。
全91のsource/生成/print/log/auditと標準公理は固定証拠へ一致。修正head全7CI SUCCESS、Lean37806006816/Tool37806006501の全stepを実読し、Research/Tool実検査成功、Formal実build/axiom/premise SKIPPEDを区別する。Researchfull/aggregate/全fileloop、Formal蒸留、全E/W/別final未実施。全GOALcheckpoint・停止条件なし。最新main `767ec4d86ecea481a8e68b04a8af78fca5d96f9d` の専用C18 branchへ進む。

## Cycle 18 selection

```yaml
ledger_type: target_cycle_result
goal: G-135-aat-atlas-coefficient-fiber
cycle: 18
goal_blob_sha: cd5f3e684b7f390558796797874a1f16b52a6b18
base_oid: 767ec4d86ecea481a8e68b04a8af78fca5d96f9d
tracking_issue: 5290
report_path: research/reports/G-135-aat-atlas-coefficient-fiber.md
selection:
  proof_state_ref: C17受理/Issue6064170174・原Mから同じP/Q座標の生成gap
  proof_dag_predecessors: [C4原Lと実ε像/原Q制限SES, C3原Pと全三次数u因子化, C16原セルsingle基底の行列表示API, C17有理像/核/商射影と両方向correctness]
  milestone: 原始L行列から同じ独立Pと実Qの全三次数座標を生成し、両逆・原微分・unit/評価/制限の全代表表示と計算dimensionを証明する（Eのnative degree接続）
  proof_obligations: [原L0/1/2列と同range, 原fine差分/符号行列, 像/transpose核射影と原restrictionのkernel同定, 実εによる原P全degree同型, 原restrictionによる原Q全degree同型, 二微分とη/ε/u/restriction全三次数の表示, 原degree次元と計算rank, W3degree2原列から同producerへの非零実接続]
  exit_criteria:
    - 原L0は垂直端点差、L1は垂直singleと混在全signed boundary、L2はnone face singleから生成。原列entryと全元表示、元Lとのrange等号を三次数とも証明
    - 同じ原行列のq=imageProjectionとp=kernelProjection(transpose)が原restriction kernel/実ε像を表し、原セル有限性から生成。期待rank/原P/Q certificateなし
    - 原P/Q全三次数から生成射影像へのLinearEquivと全元両逆・原代表式/逆式・計算rank次元を証明。原PはKan構成、原QはdualLのまま
    - 原fine differential entries/全元と同じp-next*dFine*pおよびq-next*dFine*qを原P/Q二微分へ同定。原η/ε/u/restrictionを全三次数で同じ表へ接続し、必要吸収/squarezeroは原構成から放電
    - 指定W3の原none face列と原degree2表示を同有理producerへ同定しkernelで実評価。empty/zero/repeated incidenceを一般構成から排除せず、全宣言focused/axiom/scan/出所を固定
  selection_reason: 一般有理表の条件を原M適用で放電し、任意中間P/供給homology基底へ逃がさずE同じa/R/τ/J表示への距離を直接縮める
  expected_result_type: proof-obligation-discharged
  lean_targets: [AtlasCoefficientFiber/PrimitiveDegreeMatrices, AtlasCoefficientFiber/ProjectionTransport, AtlasCoefficientFiber/NativeDegreeCoordinates, AtlasCoefficientFiber/NativeDegreeDifferentials, AtlasCoefficientFiber/DegreeCoordinateWitnesses]
  risks: [元Pの射影複体への再定義, 原Q自己像への縮小, ker/像/商の片方向包装, 原Set入力の非計算表示と表algorithmの混同, finite列挙へ期待basis/rankを混入, foreign定義直接unfold, unused ambientのH1次元への混入, G107pure presentationでmixed入力を交換]
  unchecked: [上記五終了条件は実装/受理待ち, 原homology座標と同じa/R/κ/τ/J全表示/基底変更自然同型/全A保存は後続, W全評価/別finalは後続]
```

C18で一般線形transportのsame-kernel/injective/surjective条件を方向仮定として扱う場合も、原M適用ではC4原始構成から放電しcaller fieldに残さない。セルの列挙/DecidableEqは原始有限表に相対的で、semantic homology基底/期待dimensionは入力にしない。任意Setのnative表示が非計算的なことと、有限有理表を読む計算producerを区別する。Wの実表は同じproducerを評価し、原M表示への一致を証明する。GOAL/恒久設計は変更しない。

## Cycle 18 result proposal

```yaml
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: 原Lの全列/全元/rangeから元restriction kernelを放電し、実Kan評価/dualL制限で全三次数P/Q同型と両逆/代表式/計算次元を構成。原fine微分表を同じ射影で輸送し、元P/Q微分・η/ε/u/制限全次数の表表示、吸収則/squarezeroを証明。指定W3none面から同producerをkernel評価し、元P2/Q2次元2/1を得た
  exit_criteria_status:
    - 1: primitiveL0Matrix_entry・primitiveL1Matrix_entry_inl/inr・primitiveL2Matrix_entry、三Matrix_mulVecと三Matrix_range
    - 2: 三restriction_eq_zero_iff_primitive/ker_eq_primitive、三evaluation_range_eq_primitive/三nativePProjection_range。原C4 injective/surjectiveも使用
    - 3: 六nativeP/QCoordinateEquiv、各apply/symm_apply/left_inverse/right_inverse、六Projection_rank
    - 4: primitiveD0/1Matrix_entry/mulVec、四nativeP/QDifferential_represents/all_representatives、P absorption二式とP/Q squarezero、三primitiveComparisonMatrix_transport/unit/mulVec、三nativeEvaluation/Restriction_represents
    - 5: W3faceMap_none_iffとselectedFace_valから原Finite列挙を生成、primitiveL2Matrix_eq_degreeL2Table、同producer image/annihilator/ranksをdecide+kernel、元nativeP/QProjection等号と元degree2 finrank2/1。七focused/全244公理監査・scan記録あり
  split_reason: none
  completion_candidate: no
  lean_artifacts: [ProjectionTransport, PrimitiveDegreeMatrices, NativeDegreeCoordinates, NativeDegreeDifferentials, DegreeCoordinateWitnesses, WitnessThreeInput所有API1件, WitnessThreeNonzero所有API1件]
  evidence: [原構成APIと下記全宣言spine・七focused公理出力・W3kernel producer評価]
  claim_mapping:
    theorem_names: [restriction0_ker_eq_primitive, restriction1_ker_eq_primitive, restriction2_ker_eq_primitive, nativeP0CoordinateEquiv, nativeP1CoordinateEquiv, nativeP2CoordinateEquiv, nativeQ0CoordinateEquiv, nativeQ1CoordinateEquiv, nativeQ2CoordinateEquiv, nativeP0Differential_represents, nativeP1Differential_represents, nativeQ0Differential_represents, nativeQ1Differential_represents, primitiveL2Matrix_eq_degreeL2Table, degreeL2Table_projection_ranks]
    source_labels: [G135 E元P/Q degree座標生成/原始差分/二射表示, W3原none面の同producer接続]
    conjuncts: [下記五条件の主証拠表と全宣言spine]
    undischarged_assumptions: [選択したC18五条件に未放電semantic premiseなし・正式独立PR監査待ち, E homology座標/同じa/R/kappa/tau/J全表示/基底変更/全A-label保存未完, W全評価/別最終監査未完]
    acceptance_point: 原始列から元native構成への全次数・両方向接続と全元可換式、W3同producer実評価を同じcycleで閉じたproposal。正式PR受理は別監査で判定する
    port_status: unported
audits:
  premise_delta:
    ambient-boundary: [原Source/readings/coarser/Nc/Nf/M/K1/Option分類/A、原有限セルの列挙と等号判定、係数Q]
    direction-hypothesis: [汎用embedding transportのinjective/same-image、restriction transportのsurjective/same-kernel、range_matrix_of_representsの全元表示。原M適用ではすべて下記生成定理で放電]
    discharged: [C3 evaluation0/1/2_injective、C4 evaluation0/1/2_range_eq_kerとrestriction0/1/2_surjective、原生成列rangeと三restriction_ker_eq_primitive、元evaluation/restriction_comm0/1、元C3 fullHom因子化と原P/Q square]
    remaining: [E/Wの後続固定目標だけ未完]
  certificate_provenance:
    discharged: [L0=chainD1(vertical single), L1=vertical+chainD2(all mixed), L2=all none inclusion、K(Ltranspose)/P(L)はC17 sameproducer、W3Finite列挙は元Option表の唯一none名から生成]
    unresolved: []
  proof_use:
    used: [元primitive range→元restriction核→C4評価像→六同型→両逆/次元、C3/C4 cochain式→四微分表/全代表/吸収/square、C3fullHom因子化→元u/eta同じ表、W3原列等号→同producer実行→元degree2 dimension]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [下記七focused/source/全244print/module audit/loghashとvalidation metadata, 共通scan新0・固定入力不変・静的登録/方向check・所有API出所照合]
  blocking_findings: [正式PR監査未実施]
  next_obligation: 同じ原P/Qと粗/細native homologyの計算座標を生成し、元a/R/kappa/tau/Jの全代表行列表示・basis変更・全A-label保存と全W実評価を閉じる
```

以上はrootの実装proposalで、独立受理ではない。GOAL全体は`target-proof-checkpoint`。
原Pは`pushforwardComplex`の独立Kan構成、Qは`restrictionComplex`の指定dualLのまま。
原homology・同じa/R/κ/τ/Jの全行列と全A/label保存・全W・別最終4本は後続であり、W3degree2計算だけでW全体の完了にしない。

| 固定終了条件 | 生成と全方向の主証拠 | 読み取り |
| --- | --- | --- |
| 1 原L全列/全元/同range | `primitiveL0/1/2Generator_range`、四entry・三mulVec・三range | L1はkerBへの制限を置かず、混在面の三つの符号付き辺出現を保持 |
| 2 原restriction核/実ε像 | `restriction0/1/2_ker_eq_primitive`、`evaluation0/1/2_range_eq_primitive`、`nativeP0/1/2Projection_range` | C4の逆像生成・全射性から同条件を放電。P/Qのbasis/rankを入力にしない |
| 3 元P/Q全degree両逆/代表/次元 | 六`nativeP/QCoordinateEquiv`とapply/symm_apply/left_inverse/right_inverse、六`Projection_rank` | 任意原元・全生成座標を同じε/制限で往復。finite/equalityは原セルだけ |
| 4 原微分/二射の全元表示 | `primitiveD0/1Matrix`、四`nativeP/QDifferential`、全代表・P absorption・P/Q square、三`primitiveComparisonMatrix_unit/mulVec/transport`、全evaluation/restriction | p-next*dFine*pとq-next*dFine*qを元P/Qへ輸送。ε表は同じセル座標の恒等、制限表は同じq。η/uは元Option表 |
| 5 W3同producer/公理検査 | `primitiveL2Matrix_eq_degreeL2Table`、image/annihilator/projection_ranks、nativeP/Q同producer等号、`pushforward_degree2_finrank`/`restriction_degree2_finrank` | 原Fin3のf0/f1/mと原none面一列を保持。kernelがrank2/1を算出し元P2/Q2へ接続 |

## Cycle 18 provenance と検証

C18固定baseはC17 merge `767ec4d86ecea481a8e68b04a8af78fca5d96f9d`。
GOAL blob `cd5f3e684b7f390558796797874a1f16b52a6b18` と適用基準commit `05d1c6c5cbdbb299d8d7120376135917b44f6fa1` は維持する。
C3 PR #5294 / C4 PR #5295 / C16 PR #5307 / C17 PR #5309の受理構成を利用し、元Mの値を変更しない。
W3入力側の差分は新規所有API `faceMap_none_iff` と `selectedFace_val`、各公理printだけ。
C6の指定表・nonzero/paired反証の既存値/statement/proofは不変。C17有理producer値も不変。

汎用transportの同像/同核/injective/surjectiveは方向仮定であり、それを保持するだけではG135の放電と呼ばない。
原適用は生成列のrangeとC3/C4を通して全条件を証明した。型のFinite/Fintype/DecidableEqは原始セル列挙から読み、原P/Q/homologyの期待basis/次元を含まない。
任意Setのnative座標同型は非計算的な標準線形輸送である。同じ原始表からの有理射影producerとW3列挙・表のkernel実行は別に記録する。
空/零列、loop、平行辺、重複incidence、全mixed/nonefaceを一般構成から除外していない。

七つのsingle-file focused checkを実行し、全244宣言（source239＋生成5）の明示公理printとmodule auditが一致した。
新規はsource197＋生成5＝202宣言、既存42宣言も二所有API変更の回帰として同時監査した。
全出力は`propext`/`Classical.choice`/`Quot.sound`だけで、warning零。生成五宣言は実environment inventoryから抽出した。
Research full/aggregate build・全file loop・Formal buildは未実施。依存の単一targetedキャッシュはQuotientCoordinates、ProjectionTransport、PrimitiveDegreeMatrices、NativeDegreeCoordinates、WitnessThreeInput、WitnessThreeNonzeroに限定した。
集約ファイルの変更は五直接importの静的登録だけで、elaborationはしていない。

<!-- cycle18-generated-evidence -->

| file | 明示公理printを実行した全宣言spine（file namespace相対名、生成を含む） |
| --- | --- |
| `ProjectionTransport.lean` | `embeddingCoordinateEquiv`, `embeddingCoordinateEquiv_apply`, `embeddingCoordinateEquiv_symm_apply`, `embeddingCoordinateEquiv_rank`, `restrictionCoordinateEquiv`, `restrictionCoordinateEquiv_apply`, `restrictionCoordinateEquiv_symm_apply`, `restriction_imageProjection`, `restrictionCoordinateEquiv_rank` |
| `PrimitiveDegreeMatrices.lean` | `chainCoordinates`, `chainCoordinates_apply`, `chainCoordinates_symm_apply`, `pairChainCoordinates`, `pairChainCoordinates_apply`, `range_matrix_of_represents`, `freeChainMatrix`, `freeChainMatrix_entry`, `freeChainMatrix_mulVec`, `freeChainMatrix_range`, `freePairChainMatrix`, `freePairChainMatrix_entry`, `freePairChainMatrix_mulVec`, `freePairChainMatrix_range`, `freeDualEquiv_finite_sum`, `freeChainMatrix_transpose_mulVec`, `freeChainMatrix_transpose_eq_zero_iff`, `freePairChainMatrix_transpose_mulVec`, `freePairChainMatrix_transpose_eq_zero_iff`, `primitiveL0Generator`, `primitiveL0Generator_apply`, `primitiveL0Generator_range`, `primitiveL1Generator`, `primitiveL1Generator_apply`, `primitiveL1Generator_range`, `primitiveL2Generator`, `primitiveL2Generator_apply`, `primitiveL2Generator_range`, `primitiveL0Matrix`, `primitiveL1Matrix`, `primitiveL2Matrix`, `primitiveL0Matrix_entry`, `primitiveL1Matrix_entry_inl`, `primitiveL1Matrix_entry_inr`, `primitiveL2Matrix_entry`, `primitiveL0Matrix_mulVec`, `primitiveL1Matrix_mulVec`, `primitiveL2Matrix_mulVec`, `primitiveL0Matrix_range`, `primitiveL1Matrix_range`, `primitiveL2Matrix_range`, `restriction0_eq_zero_iff_primitive`, `restriction0_ker_eq_primitive`, `restriction1_eq_zero_iff_primitive`, `restriction1_ker_eq_primitive`, `restriction2_eq_zero_iff_primitive`, `restriction2_ker_eq_primitive`, `freeChainMatrix.congr_simp`, `freePairChainMatrix.congr_simp`, `primitiveL0Matrix.congr_simp`, `primitiveL1Matrix.congr_simp`, `primitiveL2Matrix.congr_simp` |
| `NativeDegreeCoordinates.lean` | `nativeP0Projection`, `nativeP0Projection_eq`, `nativeQ0Projection`, `nativeQ0Projection_eq`, `evaluation0_range_eq_primitive`, `nativeP0Projection_range`, `nativeP0CoordinateEquiv`, `nativeP0CoordinateEquiv_apply`, `nativeP0CoordinateEquiv_symm_apply`, `nativeP0CoordinateEquiv_left_inverse`, `nativeP0CoordinateEquiv_right_inverse`, `nativeP0Projection_rank`, `nativeP0Projection_evaluation`, `nativeQ0CoordinateEquiv`, `nativeQ0CoordinateEquiv_apply`, `nativeQ0CoordinateEquiv_symm_apply`, `nativeQ0CoordinateEquiv_left_inverse`, `nativeQ0CoordinateEquiv_right_inverse`, `nativeQ0Projection_rank`, `restriction0_nativeQProjection`, `nativeP0Projection_preimage`, `nativeQ0Projection_coordinate`, `nativeP1Projection`, `nativeP1Projection_eq`, `nativeQ1Projection`, `nativeQ1Projection_eq`, `evaluation1_range_eq_primitive`, `nativeP1Projection_range`, `nativeP1CoordinateEquiv`, `nativeP1CoordinateEquiv_apply`, `nativeP1CoordinateEquiv_symm_apply`, `nativeP1CoordinateEquiv_left_inverse`, `nativeP1CoordinateEquiv_right_inverse`, `nativeP1Projection_rank`, `nativeP1Projection_evaluation`, `nativeQ1CoordinateEquiv`, `nativeQ1CoordinateEquiv_apply`, `nativeQ1CoordinateEquiv_symm_apply`, `nativeQ1CoordinateEquiv_left_inverse`, `nativeQ1CoordinateEquiv_right_inverse`, `nativeQ1Projection_rank`, `restriction1_nativeQProjection`, `nativeP1Projection_preimage`, `nativeQ1Projection_coordinate`, `nativeP2Projection`, `nativeP2Projection_eq`, `nativeQ2Projection`, `nativeQ2Projection_eq`, `evaluation2_range_eq_primitive`, `nativeP2Projection_range`, `nativeP2CoordinateEquiv`, `nativeP2CoordinateEquiv_apply`, `nativeP2CoordinateEquiv_symm_apply`, `nativeP2CoordinateEquiv_left_inverse`, `nativeP2CoordinateEquiv_right_inverse`, `nativeP2Projection_rank`, `nativeP2Projection_evaluation`, `nativeQ2CoordinateEquiv`, `nativeQ2CoordinateEquiv_apply`, `nativeQ2CoordinateEquiv_symm_apply`, `nativeQ2CoordinateEquiv_left_inverse`, `nativeQ2CoordinateEquiv_right_inverse`, `nativeQ2Projection_rank`, `restriction2_nativeQProjection`, `nativeP2Projection_preimage`, `nativeQ2Projection_coordinate` |
| `NativeDegreeDifferentials.lean` | `cochainMatrix`, `cochainMatrix_entry`, `cochainMatrix_mulVec`, `primitiveD0Matrix`, `primitiveD0Matrix_entry`, `primitiveD0Matrix_mulVec`, `primitiveD1Matrix`, `primitiveD1Matrix_entry`, `primitiveD1Matrix_mulVec`, `primitiveD1Matrix_mul_D0`, `nativeP0Differential`, `nativeP0Differential_mulVec`, `nativeP0Differential_represents`, `nativeP0Differential_all_representatives`, `nativeP0Differential_absorption`, `nativeQ0Differential`, `nativeQ0Differential_mulVec`, `nativeQ0Differential_represents`, `nativeQ0Differential_all_representatives`, `nativeP1Differential`, `nativeP1Differential_mulVec`, `nativeP1Differential_represents`, `nativeP1Differential_all_representatives`, `nativeP1Differential_absorption`, `nativeQ1Differential`, `nativeQ1Differential_mulVec`, `nativeQ1Differential_represents`, `nativeQ1Differential_all_representatives`, `nativeP1Differential_mul_P0`, `nativeQ1Differential_mul_Q0`, `originalComparison_f0`, `primitiveComparison0Matrix`, `primitiveComparison0Matrix_mulVec`, `primitiveComparison0Matrix_entry`, `primitiveComparison0Matrix_transport`, `primitiveComparison0Matrix_unit`, `nativeEvaluation0_represents`, `nativeRestriction0_represents`, `originalComparison_f1`, `primitiveComparison1Matrix`, `primitiveComparison1Matrix_mulVec`, `primitiveComparison1Matrix_entry`, `primitiveComparison1Matrix_transport`, `primitiveComparison1Matrix_unit`, `nativeEvaluation1_represents`, `nativeRestriction1_represents`, `originalComparison_f2`, `primitiveComparison2Matrix`, `primitiveComparison2Matrix_mulVec`, `primitiveComparison2Matrix_entry`, `primitiveComparison2Matrix_transport`, `primitiveComparison2Matrix_unit`, `nativeEvaluation2_represents`, `nativeRestriction2_represents` |
| `DegreeCoordinateWitnesses.lean` | `degreeFaceEquiv`, `degreeFaceEquiv_val`, `degreeNoneFace_name`, `degreeNoneFaceEquiv`, `degreeNoneFaceEquiv_val`, `degreeFaceFintype`, `degreeNoneFaceFintype`, `degreeFaceDecidableEq`, `degreeNoneFaceDecidableEq`, `degreeL2Table`, `degreeL2Table_entry`, `primitiveL2Matrix_eq_degreeL2Table`, `degreeL2Table_image`, `degreeL2Table_annihilator`, `degreeL2Table_projection_ranks`, `nativeP2Projection_eq_degreeProducer`, `nativeQ2Projection_eq_degreeProducer`, `pushforward_degree2_finrank`, `restriction_degree2_finrank` |
| `WitnessThreeInput.lean` | `coarseNerve`, `fineNerve`, `Nc`, `Nf`, `M`, `faceMap_none_iff`, `pairedNerve`, `pairedNf`, `pairedM` |
| `WitnessThreeNonzero.lean` | `selectedEdge`, `selectedFace`, `selectedFace_val`, `k`, `a0`, `a1`, `b`, `c`, `f0`, `f1`, `m`, `a0_ne_a1`, `mixedFace_eq_m`, `verticalFaceIsEmpty`, `m_edge0`, `m_edge1`, `m_edge2`, `f0_edge0`, `f0_edge1`, `f0_edge2`, `f1_edge0`, `f1_edge1`, `f1_edge2`, `B_m`, `D_m`, `H_f0`, `H_f1`, `B_m_eq_H_difference`, `mixedChain_single`, `B_kernel_zero`, `pairedMixedIsEmpty`, `primitiveTransgressionVanishing_paired_true`, `primitiveTransgressionVanishing_empty_true`, `primitiveTransgressionVanishing_false`, `connectingTau_ne_zero` |

| file / declarations | source SHA-256 | focused output SHA-256 |
| --- | --- | --- |
| `ProjectionTransport.lean` / 9 | `1f0635db1dac80413f70e3161f6153f6953cbf92df4497a0a7e9a2e8ea256806` | `f177b34e4d9dc2e9b7a6e3bfdb19f833c33d07deb1d77f28d767123d6ce7c454` |
| `PrimitiveDegreeMatrices.lean` / 52 | `9715101a77f58d1d01aab7f3e31b6b454c338046289b1529f28d62a0e065e1f6` | `6829fdd55f14d5af8e59da3c3fe0f2c1857669ab41dcbef8be86c490a57386da` |
| `NativeDegreeCoordinates.lean` / 66 | `965d7624f99a1d10ac078012a22ba8f543c147a2d162d7fe1850c02934155a20` | `7105a153c4b4fe3e221360937d10d7670cc4643a5956ae8a2afed8706a59a2e4` |
| `NativeDegreeDifferentials.lean` / 54 | `38bddba83f8c7da6c45c7f38bd97a234464fada87d6bcd45107bad74d036047b` | `009cf55a964bbbf9dc393245e387bdd4088c5c1fe8c42a86da1e7ec6050f6f8c` |
| `DegreeCoordinateWitnesses.lean` / 19 | `30917e6809d431060286a3ad763b4229a1b26d7708c6b96e200abecc3afe2420` | `7a485577afea208eede10e85e67addc19719666187076de4577e637623241455` |
| `WitnessThreeInput.lean` / 9 | `181bbbe7dd194e86dbced634842385e11041387dd5eb08d91832589396dafbd8` | `dd8ed0d985dec535c4dce65f89246063fe794d6b481a1869ac21ec2adb88f35d` |
| `WitnessThreeNonzero.lean` / 35 | `1c469a03faf21b7037b98bb902ea17ab1af6ec17a84bf8afb02409caf97a89af` | `df4299e40bc799c9d8e4082ffabb2bee379e2fe74f3296ce39fae2a117d4fac7` |

| cwd / command | 結果 |
| --- | --- |
| `research/lean` / `./check_research_modules.sh --focused ResearchLean/AG/AtlasCoefficientFiber/ProjectionTransport.lean` | exit0、warning0、全9明示print/module audit一致 |
| `research/lean` / `./check_research_modules.sh --focused ResearchLean/AG/AtlasCoefficientFiber/PrimitiveDegreeMatrices.lean` | exit0、warning0、全52明示print/module audit一致 |
| `research/lean` / `./check_research_modules.sh --focused ResearchLean/AG/AtlasCoefficientFiber/NativeDegreeCoordinates.lean` | exit0、warning0、全66明示print/module audit一致 |
| `research/lean` / `./check_research_modules.sh --focused ResearchLean/AG/AtlasCoefficientFiber/NativeDegreeDifferentials.lean` | exit0、warning0、全54明示print/module audit一致 |
| `research/lean` / `./check_research_modules.sh --focused ResearchLean/AG/AtlasCoefficientFiber/DegreeCoordinateWitnesses.lean` | exit0、warning0、全19明示print/module audit一致 |
| `research/lean` / `./check_research_modules.sh --focused ResearchLean/AG/AtlasCoefficientFiber/WitnessThreeInput.lean` | exit0、warning0、全9明示print/module audit一致 |
| `research/lean` / `./check_research_modules.sh --focused ResearchLean/AG/AtlasCoefficientFiber/WitnessThreeNonzero.lean` | exit0、warning0、全35明示print/module audit一致 |

C18 source/print/log/module-auditの全順序照合、個別公理出力とsource/log hash metadata SHA-256: `3c44451f28f3d2d8ebd498f1b7433620d4299e4daf9f976f453ffcf910c834f7`。

PR候補検証時の共通scan metadata SHA-256: `09fafc63c43eb197202f3b2acc02ff9ff52f70ecdd71a49aa3cde885d867e261`。
新規hidden/BiDi・placeholder・privacy・禁止語・逆import零、`git diff --check`成功。
privacy既存文言と公開repositoryリンクだけを行単位で除外し、新規local pathは零。
`check_research_package_direction.sh`静的check成功、`check_research_import_direction.sh`は本体228modules scan成功（Research集約elaborationではない）。
二つのW3所有API単位とprintを取り除くと、両ファイルは固定baseの全既存source bytesと一致する。出所照合metadata SHA-256: `00d9aafcd81ef775b4e11162710fb880b8a6f7e4fe698e0a249e6105a45f3fe7`。
同じGOAL/design、Formal、他worktreeの作業は変更していない。C18のCI/正式査読/merge/Issue結果は次の正式監査で記録する。

## Cycle 18 push拒否・承認待ち

実装コミットは `fdfe07b1ddc1d3606d0de97af516588fea203dea`、専用branchは `codex/5290-g135-cycle18`。
自動承認レビューが `git push -u origin codex/5290-g135-cycle18` を拒否した。
理由は未検証の外部originへpotentially private sourceを送る明示許可不足（sensitive egress）である。
originのhostとrepository pathを読取照合し、[送信先リポジトリ](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/)へ対応することを確認した。
拒否後のpush再試行・別送信経路でのsource送信は実行していない。

sourceと全244公理出力・五終了条件のroot検証はローカルに固定済み。
C18のremote branch push、PR作成、正式review-pr/math-lean-review新規四票、CI、mergeは未実施。
全GOALはtarget-proof-checkpoint、Formal unportedで、数学的な完了・反証・停滞は主張しない。
続行には上記GitHubリポジトリへの専用branch pushの明示承認が必要。
IssueはOPENを維持する。承認待ちにより先のPRゲートへ進めず、ループの未完E/W/別final義務を保持する。

承認待ち実行状態は[tracking Issueの同期コメント](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5290#issuecomment-6065112177)へ記録した。sourceコードは投稿していない。
承認待ち記録追加後の共通scan metadata SHA-256: `cdd1655a95140799f68df18e0db4eca44c715cc73cf004758060605b606be190`。

## Cycle 18 push承認・再開

上の承認待ちは履歴であり、ユーザーの明示指示「pushを許可する」で解消した。
同じ専用branchへの `git push -u origin codex/5290-g135-cycle18` はexit0で成功し、送信先は上記公開repositoryと一致した。
数学sourceと検証結果は変更していない。PRゲートの新規独立四査読から再開する。
Eのホモロジー座標・全診断写像、Wの全例接続、別の最終四査読は未完であり、全GOALはtarget-proof-checkpoint、Formal unportedのままである。

## Cycle 18 正式受理・同期

[PR5310](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5310) はhead `6c6ddd845b5834721c8ea6c79a78dde3fed6164d`、実merge `0a58ef47534acb3d02e2e5296bcf92b5e63154d5`、`2026-10-08T22:48:05Z` でMERGEDを確認した。
[標準PR root監査](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5310#issuecomment-6070579525) の判定はNo major findings、五終了条件をproof-obligation-dischargedとして受理。新規数学A/B・LeanA/BすべてNo major findings、中心0/非中心0、reruns0/2。[数学全文](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5310#issuecomment-6070563400)、[Lean全文](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5310#issuecomment-6070563833)、[Issue同期](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5290#issuecomment-6070590427)。全244標準公理・七rootfocused・四独立singlefocused・新規scan零は固定実証拠に一致。全7CI成功、Researchintegrity実steps成功、Formal実build/kernel/premise6skipを区別する。
全目標checkpoint・Formal unported、未完E/W/別finalを保持。停止条件なし。最新main `0a58ef47534acb3d02e2e5296bcf92b5e63154d5` の専用C19 branchへ進む。

## Cycle 19 selection

```yaml
ledger_type: target_cycle_result
goal: G-135-aat-atlas-coefficient-fiber
cycle: 19
goal_blob_sha: cd5f3e684b7f390558796797874a1f16b52a6b18
base_oid: 0a58ef47534acb3d02e2e5296bcf92b5e63154d5
tracking_issue: 5290
report_path: research/reports/G-135-aat-atlas-coefficient-fiber.md
selection:
  proof_state_ref: C18受理/Issue6070590427・元native homologyと同診断写像表示gap
  proof_dag_predecessors: [C18原P/Q全degree座標/原微分と二射全成分, C17同有理射影/商producer, C5元QH1とliteralR同型, C6元delta代表符号, C8元blockDefect診断]
  milestone: 原degree射影と原微分から原P/Qおよび粗細H1/H2の計算座標を生成し、同じa/T/R/tau/Jの全代表行列表示と計算dimension/defectを接続する（Eのnative homology接続）
  proof_obligations: [原degree射影像に限るharmonic射影, 元cycles/boundaries商との全同型, H1/H2全両逆と原代表/逆代表, 原unit/directH1全写像表示, 元literalRの計算座標, 原delta符号と全R上tau表示, 実blockDefectの計算rank公式, W3同producerの非零homology/tau接続]
  exit_criteria:
    - 原degree pと二微分からH1/H2射影をentriesだけで生成し、原cycles/boundariesの全商へ両方向に同定。unused ambient complementを除く
    - 元P/Qと粗細targetSubsetComplexのH1/H2座標・全元両逆・全原代表/逆式・計算rank次元。元P/Qを任意中間complexから再定義しない
    - 原unitと独立uの同じH1射a/Tを生成表へ全元で同定し、必要原compatible/projector条件を原構成から放電。基底/表示変更は原写像へ戻す同型として証明
    - 元QH1からC5literalRへの同型を使いR座標を生成し、同じ原fine微分と原delta代表式から全Rのtau行列/符号を同定。Rを全Phiへ交換しない
    - 原a/Tのkernel/cokernel診断をactual source/target projection rankとmap rankから計算し既存blockDefectへ同定、W3同producerに原homologyと非零tauを接続、全spine focused/axiom/scan/provenance固定
  selection_reason: 原P/Q degree接続を原商homologyと実診断へ進め、一般有理行列だけの条件包装をE完成に読み替えずproof distanceを縮める
  expected_result_type: proof-obligation-discharged
  lean_targets: [RationalHarmonicCoordinates, HomologyCoordinateTransport, NativeHomologyCoordinates, NativeDiagnosticMatrices, HomologyCoordinateWitnesses]
  risks: [ambient核をnativehomologyと誤る, 原商の自己像置換, suppliedsemanticbasis/rank, 条件をinstanceへ逃がす, tau符号逆, literalRをPhi全体に交換, foreign定義unfold, 非計算native同型とentriesproducerの混同]
  unchecked: [上記五終了条件は実装/受理待ち, kappa原始表示と全A/発生label保存有限判定は後続, W全要求/別finalは後続]
```

汎用projector条件・native座標条件は一般補題のdirection-hypothesisとして明示し、原M適用ではC18同じ生成表と原微分の証明から放電する。入力はrawセル列挙/原始有理表に限り、semantic homology基底・期待dimensionは渡さない。全A/labelと全Wの残義務は保持する。

## Cycle 19 result proposal

```yaml
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: 原degree射影と原微分からH1/H2計算射影を生成し、原cycles/boundaries商との両逆・原代表/逆代表・計算次元を構成。原Kan P/dualL Qと粗細targetSubsetComplexへ適用し、同じunitH1/directH1/literal R/connectingTauの全元行列式、rankと実blockDefectを接続。W3原表の同producerから原H2P次元1と非零tau行列を得た
  exit_criteria_status:
    - 1: harmonicProjection_closed/closed_eq_zero_iff/idempotent、cycleHarmonicMap_ker/range、homologyCoordinateEquivと両逆/inverse_cycle、secondHomologyProjectionと原商equiv/両逆/inverse_representative
    - 2: 原nativeP/QとcellularのH1/H2四種類のProjection/CoordinateEquiv、全mk/left_inverse/right_inverse/rank、原cyclesとH2元への全逆代表、standardHomology接続。六degree射影のsymmetric/idempotentと四原微分のabsorption/同range/squarezeroから原適用条件を放電
    - 3: nativeAMatrix_represents/unitH1、nativeTMatrix_represents/directH1は全原H1元を量化。nativeA/TMatrix_imageMap、homologyImageMap_changeとkernel/cokerEquivで同じ原射を基底表示変更へ輸送
    - 4: nativeRCoordinateEquivはC5 restrictionStandardHomologyREquivを介したliteral Rとの両逆。restriction1_nativeQ1Embedding、nativeTauMatrix_connectingTauは全R元を原Qcycleに戻し原fine微分とC6 actual delta符号から同じtauへ接続。nativeRProjection_rankとnativeTauMatrix_rankも同射
    - 5: nativeA/TMatrix_blockDefectはsource/target射影rankから実写像rankを引く対。W3primitiveL1Matrix/homologyL1Table、原P1微分と原P2 incoming rangeの全等号、同producer image/secondHomology射影のkernel評価からoriginalP2Homology_finrank/originalP2StandardHomology_finrankで次元1。originalTauMatrix_ne_zeroは同生成tau行列とC6原非零tauを接続。十focused/全301公理監査/scan
  split_reason: none
  completion_candidate: no
  lean_artifacts: [RationalHarmonicCoordinates, HomologyCoordinateTransport, SecondHomologyCoordinateTransport, NativeHomologyCoordinates, CellularHomologyCoordinates, HomologyCoordinateRank, NativeDiagnosticMatrices, HomologyCoordinateWitnesses, WitnessThreeInput所有API1件, WitnessThreeNonzero所有API1件]
  evidence: [原始射影/微分からの生成式, 下記全宣言spine, 十focused公理出力, W3同producer kernel評価]
  claim_mapping:
    theorem_names: [homologyCoordinateEquiv, secondHomologyCoordinateEquiv, nativeP1HomologyCoordinateEquiv, nativeQ1HomologyCoordinateEquiv, nativeP2HomologyCoordinateEquiv, nativeQ2HomologyCoordinateEquiv, cellularH1CoordinateEquiv, cellularH2CoordinateEquiv, nativeAMatrix_unitH1, nativeTMatrix_directH1, nativeTauMatrix_connectingTau, nativeA/TMatrix_blockDefect, nativeRProjection_rank, originalTauMatrix_ne_zero]
    source_labels: [G135 E原homology計算座標/同a-T-R-tau-J表示, W3同原producer H2Pとtau接続]
    conjuncts: [下記五終了条件対応表と全宣言spine]
    undischarged_assumptions: [今回選択五条件に未放電semantic premiseなし・正式PR独立監査待ち, E原kappa表示/全A-label有限保存と全Wおよび別whole finalは未完]
    acceptance_point: 元cycles/boundariesの商との全方向接続、原a/T/tau全元式と実blockDefect、選択W3同producer接続を同cycleで閉じたroot proposal。独立受理は別監査
    port_status: unported
audits:
  premise_delta:
    ambient-boundary: [原Source/readings/coarser/Nc/Nf/M/K1/Option分類/A, 原有限セル列挙/等号判定, 係数Q]
    direction-hypothesis: [汎用射影のsymmetric/idempotent/incoming吸収/outgoing吸収/squarezeroと原微分全元式/原degree像一致, 汎用rank輸送の全元表示/source射影吸収]
    discharged: [原C18全degree座標両逆と射影性/微分全元式/同range/squarezero, 原cellular微分全元式と原squarezero, 原cycle商の第一同型定理と原kernel/range等号, C5 literal R両逆, C4原P2逆像とC6delta代表符号, C8実blockDefect次元式]
    remaining: [後続E/W/whole finalの固定義務]
  certificate_provenance:
    discharged: [H1=p-image(d1 transpose)-image(d0), H2=p-image(d1), 原P/Qとcoarse/fine degree射影と原微分を使用, a=HP1*F1*HC1/T=HF1*F1*HC1/tau=HP2*dFine1*HQ1, W3原Option表からcell列挙とL1全mixed列/P2incomingを生成]
    unresolved: []
  proof_use:
    used: [原closed/boundaryfree→原商kernel/range→両逆と逆代表→原H1全元a/T式, 原Qcycle逆代表→原restrictionとfine微分→C4P2逆像→C6delta符号→全R tau式, 全元表示→rank輸送→原blockDefect, W3原列range等号→同image/secondHomology射影→kernel rank評価→原H2P dimension]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [下記十focused/source/log/fullprint/moduleauditとhash, 共通scan新0/固定入力不変/静的登録/所有API旧bytes照合]
  blocking_findings: [正式PR独立監査待ち]
  next_obligation: 原kappaとvertical fiber homologyの計算表示、全A/有限発生labelの保存Boolと実blockDefectの一致、W1-W5全指定要求の同A-E経路評価、別whole final fresh4
```

以上は実装proposalで、全GOALは`target-proof-checkpoint`。原Pは独立Kan構成、原Qは指定dualLのまま。原cycles・原boundariesのquotientを使い、補助ambient座標の未使用補空間をhomologyに含めない。
W3の今回の値は原H²Pの次元1と同じ生成τ行列の非零性である。τrank1/同型の数値評価、原Jの全値、全A/実Law/錐、paired版の全要求を今回の達成と呼ばない。E/W全体と別最終四票は後続義務のまま。

| 固定終了条件 | 原入力からの主証拠と全方向 | 照合点 |
| --- | --- | --- |
| 1 H1/H2計算射影と原商 | `harmonicProjection_closed_eq_zero_iff`、`cycleHarmonicMap_ker/range`、`homologyCoordinateEquiv`、`secondHomologyCoordinateEquiv`と全両逆/逆代表 | quotientは原cycles/range原d0および原C2/range原d1。方向仮定を具体的原適用に残さない |
| 2 元P/Q・粗細homology | native四H1/H2 CoordinateEquiv/standardEquiv、cellular二CoordinateEquiv/standardEquiv、全mk/両逆/逆代表/rank | 原Kan評価とQ制限から得たdegree表示を使用。期待homology基底・次元を入力にしない |
| 3 実a/Tと表示変更 | `nativeAMatrix_unitH1`、`nativeTMatrix_directH1`、三imageMap、`homologyImageMap_change`、kernel/cokerEquiv | 全原H1類に対する等式。同じ原射を別表示へ輸送し、異なる基底のmatrix entry一致を主張しない |
| 4 literal Rと全R tau | `nativeRCoordinateEquiv`、`nativeRProjection_rank`、`nativeTauMatrix_connectingTau`、`nativeTauMatrix_rank` | C5 QH1↔Rの両逆を保持。原Qcycle、原fine d1、原P2逆像とC6符号から全R元の式を証明 |
| 5 実defectとW3 | `nativeA/TMatrix_blockDefect`、原W3全列/全range等号、生成secondHomology射影rank1、原H2P finrank1、`originalTauMatrix_ne_zero` | rank(p/q)-rank(B)の対が実blockDefect。同producerのkernel評価と原非零τを使用。W3全要求は後続 |

## Cycle 19 provenance と検証

固定baseはC18 merge `0a58ef47534acb3d02e2e5296bcf92b5e63154d5`、GOAL blob `cd5f3e684b7f390558796797874a1f16b52a6b18`、適用基準commit `05d1c6c5cbdbb299d8d7120376135917b44f6fa1`。GOAL/恒久設計/Formalは不変。
C3 PR #5294、C4 #5295、C5 #5296、C6 #5297、C8 #5299、C17 #5309、C18 #5310の受理済み宣言を現source/適用引数まで確認して使用する。既存LinearConjugationと標準first-isomorphism/quotient APIも現statementを確認して輸送に使う。受理済み内部履歴の再帰再認定はしない。
W3owner差分は`edgeMap_none_iff`/`selectedEdge_val`と各printだけ。これらの追加を除去するとbaseの原入力/nonzero source bytesと一致する。C6実例値とstatementを変更しない。

汎用射影/輸送の方向仮定は原微分・原degree像・原squarezero・全元表示から放電する。一般補題の条件を保持するだけでは原G135達成としない。原finite/equality/列挙はsemantic homology基底や期待dimensionを含まない。任意Setへの非計算的原商同型と、有理原表からの計算射影producerを区別する。W3の列・射影・rankは後者の同producerをkernelで評価する。
空/零列、loop、平行辺、重複incidence、全mixed/nonefaceを一般構成から除外しない。Rを全Phiに置換せず、forest/pure/τ零を追加仮定にしない。

rootは十single-file focused checkを実行し、全301宣言（source288＋生成13）、新257（source244＋生成13）、旧44の明示公理出力をsource順/module auditと全件照合した。標準`propext`/`Classical.choice`/`Quot.sound`のみ、warning0。生成13宣言は実environment inventoryから固定した。各commandは下表のfileに対する`./check_research_modules.sh --focused ResearchLean/AG/AtlasCoefficientFiber/<file>`、cwdは`research/lean`、exit0。
必要な単一targeted依存キャッシュだけを作成し、Research full/aggregate/全file loopとFormal build/蒸留は未実施。八新moduleのmanifest/aggregate直接importは静的登録のみで、aggregateをelaborateしていない。

<!-- cycle19-generated-evidence -->

| file | 明示公理printを実行した全宣言spine（file namespace相対名、生成を含む） |
| --- | --- |
| `RationalHarmonicCoordinates.lean` | `mul_imageProjection_of_mul_eq`, `mul_imageProjection_of_mul_zero`, `harmonicProjection`, `harmonicProjection_mulVec`, `imageProjection_zero`, `harmonic_outgoing_absorption`, `harmonicProjection_degree`, `harmonic_corrections_mul_zero`, `harmonicProjection_cycle`, `harmonicProjection_boundary_free`, `harmonicProjection_closed`, `harmonicProjection_closed_eq_zero_iff`, `harmonicProjection_mul_self`, `harmonicProjection_transpose`, `imageProjection_eq_of_range_eq`, `kernelProjection_eq_complement` |
| `HomologyCoordinateTransport.lean` | `degreeProjection_fixes_range`, `cycleHarmonicMap`, `cycleHarmonicMap_apply`, `degreeEmbedding_fixed`, `cycleHarmonicMap_ker`, `cycleHarmonicMap_range`, `homologyCoordinateEquiv`, `homologyCoordinateEquiv_mk`, `homologyCoordinateEquiv_left_inverse`, `homologyCoordinateEquiv_right_inverse`, `homologyCoordinateEquiv_symm_representative`, `homologyCoordinateEquiv_rank`, `homologyCoordinateEquiv_inverse_cycle` |
| `SecondHomologyCoordinateTransport.lean` | `secondHomologyProjection`, `secondHomologyProjection_sub`, `secondHomologyProjection_eq`, `secondHomologyProjection_degree`, `secondHomologyProjection_mul_self`, `secondHomologyProjection_transpose`, `secondHarmonicMap`, `secondHarmonicMap_apply`, `secondHarmonicMap_ker`, `secondHarmonicMap_range`, `secondHomologyCoordinateEquiv`, `secondHomologyCoordinateEquiv_mk`, `secondHomologyCoordinateEquiv_left_inverse`, `secondHomologyCoordinateEquiv_right_inverse`, `secondHomologyCoordinateEquiv_symm_representative`, `secondHomologyCoordinateEquiv_rank`, `secondHomologyCoordinateEquiv_inverse_representative` |
| `NativeHomologyCoordinates.lean` | `range_subtype_coordinateEquiv`, `nativeP0Projection_symmetric`, `nativeP0Projection_idempotent`, `nativeQ0Projection_symmetric`, `nativeQ0Projection_idempotent`, `nativeP1Projection_symmetric`, `nativeP1Projection_idempotent`, `nativeQ1Projection_symmetric`, `nativeQ1Projection_idempotent`, `nativeQ1Embedding`, `nativeQ1Embedding_apply`, `nativeQ1Embedding_injective`, `nativeQ1Embedding_range`, `nativeP2Projection_symmetric`, `nativeP2Projection_idempotent`, `nativeQ2Projection_symmetric`, `nativeQ2Projection_idempotent`, `nativeQ2Embedding`, `nativeQ2Embedding_apply`, `nativeQ2Embedding_injective`, `nativeQ2Embedding_range`, `nativeP0Differential_left_projection`, `nativeP0Differential_right_projection`, `nativeQ0Differential_left_projection`, `nativeQ0Differential_right_projection`, `nativeP0Differential_range`, `nativeQ0Differential_range`, `nativeP1Differential_left_projection`, `nativeP1Differential_right_projection`, `nativeQ1Differential_left_projection`, `nativeQ1Differential_right_projection`, `nativeP1Differential_cycle_iff`, `nativeQ1Differential_cycle_iff`, `nativeP1Differential_range`, `nativeQ1Differential_range`, `nativeP1HomologyProjection`, `nativeP1HomologyProjection_eq`, `nativeP1HomologyCoordinateEquiv`, `nativeP1HomologyCoordinateEquiv_mk`, `nativeP1HomologyCoordinateEquiv_left_inverse`, `nativeP1HomologyCoordinateEquiv_right_inverse`, `nativeP1HomologyCoordinateEquiv_symm_representative`, `nativeP1HomologyProjection_rank`, `nativeP1HomologyProjection_mul_self`, `nativeP1HomologyCoordinateEquiv_inverse_cycle`, `nativeP1StandardHomologyCoordinateEquiv`, `nativeP1StandardHomologyCoordinateEquiv_apply`, `nativeP1StandardHomologyCoordinateEquiv_mk`, `nativeQ1HomologyProjection`, `nativeQ1HomologyProjection_eq`, `nativeQ1HomologyCoordinateEquiv`, `nativeQ1HomologyCoordinateEquiv_mk`, `nativeQ1HomologyCoordinateEquiv_left_inverse`, `nativeQ1HomologyCoordinateEquiv_right_inverse`, `nativeQ1HomologyCoordinateEquiv_symm_representative`, `nativeQ1HomologyProjection_rank`, `nativeQ1HomologyProjection_mul_self`, `nativeQ1HomologyCoordinateEquiv_inverse_cycle`, `nativeQ1StandardHomologyCoordinateEquiv`, `nativeQ1StandardHomologyCoordinateEquiv_apply`, `nativeQ1StandardHomologyCoordinateEquiv_mk`, `nativeP2HomologyProjection`, `nativeP2HomologyProjection_eq`, `nativeP2HomologyCoordinateEquiv`, `nativeP2HomologyCoordinateEquiv_mk`, `nativeP2HomologyCoordinateEquiv_left_inverse`, `nativeP2HomologyCoordinateEquiv_right_inverse`, `nativeP2HomologyCoordinateEquiv_symm_representative`, `nativeP2HomologyProjection_rank`, `nativeP2StandardHomologyCoordinateEquiv`, `nativeP2StandardHomologyCoordinateEquiv_mk`, `nativeP2HomologyProjection_mul_self`, `nativeP2StandardHomologyCoordinateEquiv_apply`, `nativeP2HomologyCoordinateEquiv_inverse_representative`, `nativeQ2HomologyProjection`, `nativeQ2HomologyProjection_eq`, `nativeQ2HomologyCoordinateEquiv`, `nativeQ2HomologyCoordinateEquiv_mk`, `nativeQ2HomologyCoordinateEquiv_left_inverse`, `nativeQ2HomologyCoordinateEquiv_right_inverse`, `nativeQ2HomologyCoordinateEquiv_symm_representative`, `nativeQ2HomologyProjection_rank`, `nativeQ2StandardHomologyCoordinateEquiv`, `nativeQ2StandardHomologyCoordinateEquiv_mk`, `nativeQ2HomologyProjection_mul_self`, `nativeQ2StandardHomologyCoordinateEquiv_apply`, `nativeQ2HomologyCoordinateEquiv_inverse_representative`, `nativeP0Differential.congr_simp`, `nativeP1Differential.congr_simp`, `nativeQ0Differential.congr_simp`, `nativeQ1Differential.congr_simp`, `nativeP0Projection.congr_simp`, `nativeP1Projection.congr_simp`, `nativeP2Projection.congr_simp`, `nativeQ2HomologyProjection.congr_simp`, `nativeP2HomologyProjection.congr_simp` |
| `CellularHomologyCoordinates.lean` | `primitiveD0Matrix_range`, `cellularH1Projection`, `cellularH1Projection_eq`, `cellularH1CoordinateEquiv`, `cellularH1CoordinateEquiv_mk`, `cellularH1CoordinateEquiv_left_inverse`, `cellularH1CoordinateEquiv_right_inverse`, `cellularH1Projection_rank`, `cellularH1StandardCoordinateEquiv`, `cellularH1StandardCoordinateEquiv_mk`, `cellularH1Projection_mul_self`, `cellularH1CoordinateEquiv_inverse_cycle`, `cellularH1StandardCoordinateEquiv_apply`, `primitiveD1Matrix_range`, `cellularH2Projection`, `cellularH2Projection_eq`, `cellularH2CoordinateEquiv`, `cellularH2CoordinateEquiv_mk`, `cellularH2CoordinateEquiv_left_inverse`, `cellularH2CoordinateEquiv_right_inverse`, `cellularH2Projection_rank`, `cellularH2StandardCoordinateEquiv`, `cellularH2StandardCoordinateEquiv_mk`, `cellularH2Projection_mul_self`, `cellularH2CoordinateEquiv_inverse_representative`, `cellularH2StandardCoordinateEquiv_apply`, `cellularH2Projection.congr_simp`, `primitiveD1Matrix.congr_simp`, `primitiveD0Matrix.congr_simp`, `cellularH1Projection.congr_simp` |
| `HomologyCoordinateRank.lean` | `coordinateMatrix_range`, `coordinateMatrix_rank`, `coordinateProjection_dimensions`, `coordinateMatrix_blockDefect`, `homologyImageMap`, `homologyImageMap_apply`, `homologyImageMap_matrix`, `homologyImageMap_natural`, `homologyImageMap_kernelEquiv`, `homologyImageMap_cokernelEquiv`, `homologyImageMap_change`, `rationalMatrixRank_transpose` |
| `NativeDiagnosticMatrices.lean` | `nativeAMatrix`, `nativeAMatrix_eq`, `nativeTMatrix`, `nativeTMatrix_eq`, `nativeRCoordinateEquiv`, `nativeRCoordinateEquiv_apply`, `nativeRCoordinateEquiv_restriction`, `nativeTauMatrix`, `nativeTauMatrix_eq`, `nativeAMatrix_right_projection`, `nativeAMatrix_left_projection`, `nativeTMatrix_right_projection`, `nativeTMatrix_left_projection`, `nativeTauMatrix_right_projection`, `nativeTauMatrix_left_projection`, `nativeAMatrix_represents`, `nativeTMatrix_represents`, `nativeAMatrix_unitH1`, `nativeTMatrix_directH1`, `restriction1_nativeQ1Embedding`, `nativeTauMatrix_connectingTau`, `nativeAMatrix_rank`, `nativeTMatrix_rank`, `nativeTauMatrix_rank`, `nativeAMatrix_blockDefect`, `nativeTMatrix_blockDefect`, `nativeAMatrix_imageMap`, `nativeTMatrix_imageMap`, `nativeTauMatrix_imageMap`, `nativeRProjection_rank` |
| `HomologyCoordinateWitnesses.lean` | `homologySelectedChart`, `homologySelectedChart_val`, `homologyChartEquiv`, `homologyEdgeEquiv`, `homologyVertical_name`, `homologyVerticalEquiv`, `homologyMixedEquiv`, `homologyChartFintype`, `homologyEdgeFintype`, `homologyFaceFintype`, `homologyVerticalFintype`, `homologyMixedFintype`, `homologyNoneFaceFintype`, `homologyChartDecidableEq`, `homologyEdgeDecidableEq`, `homologyFaceDecidableEq`, `originalR_coordinate_inverses`, `originalTauMatrix_ne_zero`, `homologyL1Table`, `homologyL1Table_inl`, `homologyL1Table_inr`, `primitiveL1Matrix_eq_homologyTable`, `homologyL1Table_image`, `homologyP1Projection`, `homologyQ1Projection`, `homologyD1Table`, `homologyD1Table_entry`, `primitiveD1Matrix_eq_homologyTable`, `homologyP2Projection`, `homologyQ2Projection`, `homologyP1DifferentialTable`, `homologyP1DifferentialTable_entry`, `nativeP1Differential_eq_homologyTable`, `homologyP2IncomingColumn`, `homologyP2IncomingColumn_entry`, `homologyP2IncomingColumn_range`, `homologyP2IncomingColumn_image`, `homologyP2HomologyProjection`, `homologyP2HomologyProjection_rank_one`, `originalP2Homology_finrank`, `originalP2StandardHomology_finrank` |
| `WitnessThreeInput.lean` | `coarseNerve`, `fineNerve`, `Nc`, `Nf`, `M`, `edgeMap_none_iff`, `faceMap_none_iff`, `pairedNerve`, `pairedNf`, `pairedM` |
| `WitnessThreeNonzero.lean` | `selectedEdge`, `selectedFace`, `selectedEdge_val`, `selectedFace_val`, `k`, `a0`, `a1`, `b`, `c`, `f0`, `f1`, `m`, `a0_ne_a1`, `mixedFace_eq_m`, `verticalFaceIsEmpty`, `m_edge0`, `m_edge1`, `m_edge2`, `f0_edge0`, `f0_edge1`, `f0_edge2`, `f1_edge0`, `f1_edge1`, `f1_edge2`, `B_m`, `D_m`, `H_f0`, `H_f1`, `B_m_eq_H_difference`, `mixedChain_single`, `B_kernel_zero`, `pairedMixedIsEmpty`, `primitiveTransgressionVanishing_paired_true`, `primitiveTransgressionVanishing_empty_true`, `primitiveTransgressionVanishing_false`, `connectingTau_ne_zero` |

| file | source SHA-256 | focused stdout SHA-256 | print/module audit |
| --- | --- | --- | --- |
| RationalHarmonicCoordinates.lean | `e6184794bcbc89b3a5c9726233e99ca735ac6a826ae71bdbb804f7033b1addcb` | `012fd2396a1f75f704f953555295bbfb2ae174d812b49e2ea7ddb78c6a60ec9b` | 16/16 |
| HomologyCoordinateTransport.lean | `f87b97c94694af53821971d4eb8f2b6920ff304f87cefc77b6b34a989fe1f57b` | `91745e43486944a41b525c3c1de0f2603ae0a529edcdd34be9e224fd9b699c20` | 13/13 |
| SecondHomologyCoordinateTransport.lean | `092afa58fafd6821f22c3f38f99ce1f818937db1f449515370b45ba01e672683` | `7a103b55db9202a5f795832606512a02a802d869623e5f13b90f010e1a8991af` | 17/17 |
| NativeHomologyCoordinates.lean | `c650ee0aec9f640f44620815ffca88be963043d3c7a5cc5cbfc1ceb312ba86d5` | `2e63bd2229f1bac93cde9cacb771f6de7b9da49144baac1e5faeab9592f8cd53` | 96/96 |
| CellularHomologyCoordinates.lean | `4e639d785e9fc77369dcca7b398e367256c75bbe6e073dc111c7f77b7053a6ed` | `9b8700ced8934c0fce750cef03b6972c23b1bd4d1d805ac3028289017b46489e` | 30/30 |
| HomologyCoordinateRank.lean | `fd3f40e8ff80f244852b78d15054bf9d37a52f79506a9fef898387dc09a0fcb6` | `f16428779ab9419eaa8e0f4dc868e8ec3ea0d53fb778dc6ba04261d9e7f21066` | 12/12 |
| NativeDiagnosticMatrices.lean | `bc8157bc5ffe2d35c339fe0ecc10e3a1126ccadd539257284783436c44f7b46a` | `cf1efec0c3b27002c45a28dbea333022db25398b661c3db8fe1da8b509904696` | 30/30 |
| HomologyCoordinateWitnesses.lean | `6d899f606c5aa6c6465913fe3a9a6352a0345fd2f61a76bb7390da1ed09b9824` | `ad099e62a85ae47f830f194a9c4897ea0c04d4c6e2e37570816d224cb0cfdf82` | 41/41 |
| WitnessThreeInput.lean | `68f89f83e088f3d4e2f55bb7e08fe6be339e8751ade0ffdc2d4f3147282b34c8` | `72946d5c12df272ab7f7ea0e71067e88f2c5ce6dd255c4d5bc0c9caad1f58b85` | 10/10 |
| WitnessThreeNonzero.lean | `23139f001353ef0512506cf97709d8829b4b8fc6b3733a6622bde5e8c72114fb` | `a66c4df23ab72ab36ed0f44c58013244616e30d870e15b5225e1a4f8960cc144` | 36/36 |

validation metadata SHA-256 `7ebe14e96e0bdd079ef052a7506bb6471e4ab1949e53476aa09000852e15470a`。所有API旧bytes保存証拠 SHA-256 `5b85a5e32f175a6f67719ffb38009929006d96388b7de37d3bfa8cb10d0f6e3a`。共通scan/source-log照合・静的登録・固定入力不変をPR前に最終確認する。独立PR査読/受理監査/CI/merge/Issue同期はこのproposalの後に行い、全GOAL完了へ読み替えない。


## Cycle19 accepted / 同期

[PR5312](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5312)はhead `a90fee53a0ee64caea90acb1073d43b776521cd3`、merge `8822a0d9bbc42ab91711c7e3839aa58be0239fa0`、`2026-10-09T00:08:53Z`で実MERGED。[13項目root受理](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5312#issuecomment-6071529511)はNo major findings / proof-obligation-discharged。[数学A](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5312#issuecomment-6071505138)、[数学B](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5312#issuecomment-6071507446)、[LeanA](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5312#issuecomment-6071509546)、[LeanB](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5312#issuecomment-6071511508)全て新規独立No major findings、中心0/非中心0、reruns0/2。[同一票scan資格追補](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5312#issuecomment-6071513555)も新finding0、元bytes不変・追加elaboration0。[Issue同期](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5290#issuecomment-6071546610)でOPEN保持。全301標準公理・十root/四独立single focused・scan/静的方向PASS、全7CI成功、Formal実検証六skipを区別。全GOALcheckpoint、停止条件なし。

## Cycle20 selection — 原fiber適合と全保存判定の有限計算

```yaml
ledger_type: target_cycle_result
goal: G-135-aat-atlas-coefficient-fiber
cycle: 20
goal_blob_sha: cd5f3e684b7f390558796797874a1f16b52a6b18
base_oid: 8822a0d9bbc42ab91711c7e3839aa58be0239fa0
tracking_issue: 5290
report_path: research/reports/G-135-aat-atlas-coefficient-fiber.md
selection:
  proof_state_ref: Cycle19 accepted / Issue6071546610 / 原native a-T-R-tau全元表示
  proof_dag_predecessors: [C1 incidence圏とcomma成分, C5原κ-Φ-R, C8実defect, C11原Law block和, C16有限全A-label検査, C17有理producer, C19原商座標と実診断]
  milestone: E 原fiber適合の表示・連結成分手順・全Aと発生label保存判定を同じ原A-D写像へ戻す
  proof_obligations:
    - 原a/B/D/V全元有理表示から原verticalCycles/VerticalHomology/mixedCyclesの全座標を構成
    - 原kerB上のDyから生成κ行列が同じrawκおよび全Φのκを全元で表示し原dimension/rankへ戻る
    - 有限incidence圏の実射存在からbounded到達判定を生成し原Zigzag/ConnectedComponentsへ両方向同定、元commaと順像係数成分へ適用
    - 原粗細d0/d1とF1からJと保存Boolを生成し同じ原blockDefect零と必要十分
    - 全Set A・全有限発生labelの保存Boolと実Law blockDefectを双方向接続、Value全体有限性・同台重複除去なし
  exit_criteria:
    - 原a/B/D/Vの全vector同定、原vertical/混在商座標の両逆と原κ全元表示・rank
    - 成分のbounded有限判定と元incidence/comma連結関係・成分への両方向同定
    - 同じprimitive粗細表によるJ/Boolが原直接比較blockDefectと一致、a同型かつtau単射条件へ接続
    - 全A有限走査と元全Set保存、全発生label走査と既存実Law欠損零が必要十分
    - 全追加spine focused、公理・scan・登録・proof-use/出所固定、空台/空Law/重複保持
  selection_reason: 残Eの原κと成分/全保存判定を閉じ、指定W全評価を同じ計算経路に置けるようにする
  expected_result_type: proof-obligation-discharged
  lean_targets: [PrimitiveMatrices所有API, FiberCompatibilityCoordinates, FiniteComponents, FinitePreservationDecision]
  risks: [原cycles商を補助複体へ交換しない, 原κの全Φ同値方向, computationと非計算的index表示の区別, incidence射の重複保持, semantic rank/保存仮定を入力しない]
  unchecked: []
```

実装前の選定。五終了条件が揃うまで同cycle内で実装・検証を反復する。W全体と別最終四査読は次義務でありcompletion_candidateはまだno。


## Cycle20 result proposal

```yaml
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: 原a/B/D/V全vector表示から元verticalCycles/VerticalHomology/mixedCyclesの同座標と両逆を構成し、実κ全元・全Phi・computed rankへ接続。原incidenceとcarrier commaの有限射存在からbounded path検査/成分数を生成し、元Zigzag/ConnectedComponents/同Kan係数とincidence作用へ同定。原粗細微分/F1からJを生成し、全A/有限発生label保存Boolを同じ旧blockDefectと実Lawへ双方向接続
  exit_criteria_status:
    - 1: primitiveB/D/VMatrix_mulVec、primitiveVerticalEdgeMatrix_entry/mulVec、chainKernelEmbedding_range/chainKernelCoordinateEquiv、verticalCycle/mixedCycleCoordinateEquiv、primitiveVMatrix_cycle_range/kernel_absorption、verticalHomologyCoordinateEquivと原mk/両逆/全逆代表、同Phi座標。nativeKappaMatrix_rawKappa/kappa/imageMapは全原mixedCycles/全生成座標、raw_rank/rankは実κ像の次元
    - 2: categoryComponentGraph_reachable_iffは元Zigzagと両方向、finiteZagDecidableは原有限Homのcardから生成。categoryComponentDecisionは長さcard未満の全finite walksを走査し元component等号と必要十分、成分同値/元代表/成分数。元incidence/commaの有限列挙・有限射・同Bool、同Kan cell座標/全incidence作用へ接続
    - 3: rationalProjectionDefect/rationalPreservationDecisionは実homology射影と実map rankのみを読む。primitiveDiagnostic_eq_blockDefectはC19原T全表示と同homology/rankへ接続。primitivePreservationDecisionの原欠損零同値と元a同型かつtau単射条件
    - 4: readingTarget_finite/allFinsets_iff_allSetsからallAPreservationDecisionの全原Set同値。lawPreservationDecisionは全原発生labelを走査、lawBlockDefect_zero_iff_labelsは同旧Law比較の非負block和の零性と全label零の双方向、primitiveLawDiagnosticは全対を同旧Law欠損へ同定
    - 5: 四single focused/全101宣言とgenerated congr_simp1件の個別公理/全登録/scan/元owner bytes保存/現predecessor適用を固定。empty kernel成功と実余核failureを同Boolでkernel評価、空Set/空Law/同台重複を一般式から除外しない
  split_reason: none
  completion_candidate: no
  lean_artifacts: [PrimitiveMatrices所有API3件, FiberCompatibilityCoordinates, FiniteComponents, FinitePreservationDecision]
  evidence: [下記五条件と全宣言spine, 四focused全公理出力, bounded path kernel, finite rational ranks/Bool]
  claim_mapping:
    theorem_names: [chainKernelEmbedding_range, verticalHomologyCoordinateEquiv, nativeKappaMatrix_kappa, nativeKappaMatrix_rank, categoryComponentDecision_eq_true_iff_components, coefficientComponentCoordinateEquiv_map, primitiveDiagnostic_eq_blockDefect, allAPreservationDecision_eq_true_iff, lawPreservationDecision_eq_true_iff, primitiveLawDiagnostic_eq_blockDefect]
    source_labels: [G135 E原fiber適合/成分有限計算/同J/全A-label保存判定, A原Kan係数表示, C原保存条件, D実Law比較]
    conjuncts: [下記全宣言spineと五条件表]
    undischarged_assumptions: [選択五条件のsemantic premiseなし・正式PR独立監査待ち, 全W1-W5の指定値/同Source-Law台/代表/錐対応と別whole-finalは未完]
    acceptance_point: 原有限入力だけから生成した表示と検査を同じ原商/実κ/原incidence成分/同a-T-tau-Law比較へ双方向で戻した提案
    port_status: unported
audits:
  premise_delta:
    discharged: [原a/B/D/V全vector, 元kernel/range/V原cycle像, 原vertical商全同値/両逆, rawκから同Phiκ表示, 原finiteHom→bounded component procedure, 同nativeT/J→旧defect, 全Set/全発生labelと元Law和]
    remaining: [正式PR監査, 全指定Wと別最終四査読]
  certificate_provenance:
    discharged: [原named cell single基底, 原ker a/ker Bと実V/D, C5原vertical-Phi同値, 原incidence/commaの有限射, C19原homology表示と実rank, C16全target/発生label有限列挙]
    unresolved: []
  proof_use:
    used: [全vector→原kernel/range, Vの実cycle閉性→原商座標, 元mixedCycle→Dy→原vertical類→全Phiκ, fullsource absorption→実κrank, actualZag→全boundedpath→原成分/同Kan, 原T全表示→実J, 非負発生block和→Law保存]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [下記四single focused/source-log hashes/101標準公理, scans/owner記録]
  blocking_findings: []
  next_obligation: W1-W5の全指定要求を原始Source/readings/実Law二発生labelから同A-E経路で評価、その後別whole-goal fresh4
```

上記 `audits` は同じcycleの提案であり、正式受理は固定headの標準PR監査に置く。GOAL全体はtarget-proof-checkpointを保持し、Eの残計算接続だけでW全体完了としない。

### 五終了条件の証拠対応と前提

| 条件 | 元入力・構成・実接続 |
| --- | --- |
| 1 原fiber適合 | 元verticalEdgeBoundary a、mixedHorizontalBoundary B、mixedVerticalBoundary D、verticalBoundary V。全named原セル係数→元ker a/ker B→ker a/im Vのliteral原商。C5元verticalHomologyPhiEquivを合成し全Phiのκに同じHΦ·D·K_Bを同定。両逆/全原逆代表/全原mixedCycle/全生成座標を保持。V閉性は原aV零のverticalBoundaryToCycles、Dy閉性は原aD+bB零のmixedCycleToVerticalから放電 |
| 2 原成分計算 | 原有限射のcard正性からZagをdecideし、長さcard J未満の全walkを列挙する。graphはπ0計算だけで、元圏やKan extensionをgraph/posetへ置換しない。元Zigzagの両方向・元ConnectedComponentsの両逆と代表・count、元carrier commaの全Hom/objects finiteを入力から生成。同Kan cellと全元incidence射作用はC3原component-value isoへ接続 |
| 3 同J/保存 | C19元粗細H1射影・独立direct Tの全元式/rank/source absorptionから生成二rank差を同じ旧M.aSubnerveComparisonHom.h1MapのblockDefectへ同定。BoolはこのNat対を読むだけで、保存/期待rankを入力しない。同BoolをC8元a同型∧実τ単射へ接続 |
| 4 全A/発生label | 有限Sourceと全射readingからtarget finite、全Finsetと全Setの同値。発生label finiteは元laws×Source経路でValue全体finiteなし。同台labelを商にせず各summandを保持。G-134受理原Law比較block和とNat非負和の零性から原全label保存と実Law保存を双方証明、対の計算値も一致 |
| 5 検証・出所 | 全新/既存owner宣言とgenerated宣言をsource/print/実stdout/moduleauditへ全照合。原empty/zero/loop/parallel/repeated incidenceの制約追加なし。有限kernelの空行列true/余核falseをkernel評価。全W指定値の代替例とはしない |

material premise分類：T0原Source/readings/coarser/Nc/Nf/M/K1/Option/incidence/任意A/ℚと有限namedセル列挙はambient input。一般 `chainKernelEmbedding_range/chainKernelCoordinateEquiv` の全vector matrix representationはdirection-hypothesisで、nativea/Bではprimitive全元所有APIにより放電。一般category kernelのfinite objects・等号・decidable actualZagは方向条件で、nativeでは原セル/射finiteと有限Hom-card判定から生成する。既存secondHomology条件は原a-kernel対称/冪等、原V-range、原Vのa閉性から全放電。原κ/R/tau/保存同型/期待次元を新引数・instance・structure fieldに保持しない。

計算の区別：rationalProjectionDefect/Bool、image/kernel/商射影、bounded finite-walk検査とfinite-family走査は有限表の計算。任意Setを含む元Mからのセル/射列挙と元商同値・逆代表は非計算的transport。nativeZagをClassical.emで検査する方式を採らず、明示 `finiteZagDecidable` を原finite Hom列挙から作る。期待homology基底・semantic rank・成分関係のoracleを入力にしない。

出所：C3 PR5294/受理6046087706の原Incidence finite、ConstantLimitのcoefficientCellIsoと原incidence作用表示、C12 PR5303/最終受理6057242603のPushforwardCoefficient現source（元有限comma/Kan係数はC3、pushforwardCoefficients_map_component_evalはC12追加）、C5 PR5296/受理6049620284のKappa/FiberHomology、C8 PR5299/受理6052624414のDefectMaps/DefectDiagnostics、C16 PR5307/受理6063082167のPrimitiveMatrices/FiniteTauDecision、C19 PR5312/受理6071529511の元商/全原a-T-R-tau-J表示を使用する。Lawの原block和はG-134 PR5287 head0134623422114ae39f989d591cb167c6176aae3e/全体受理6030258596のFaceRelationSubdivision.LawComparisonFiberDiagnostics `lawH1Defect_subset_sum` に同じ現M/laws/粗細adequacyを適用する（C11 PR5302でも同原和を接続済み）。現使用十sourceの受理head・受理PR/監査・宣言・source SHAを照合し、十source全体が各記載受理版とbytes一致する。出所照合記録SHA `b07723e8a5b53a2daa2db16f6a56f52a4687f111e6bb86a8a38998446e207070`。追跡完了predecessor内部全履歴を再認定しない。

原PrimitiveMatricesは三所有APIとprintだけを追加し、これらを除くとbase bytesに一致（owner保存SHA `b5f53ab47718e676107a397a13a006d8cd6ce20fb147c6971c73426fc9cdf0f9`）。Lean4.28.0 / mathlib8f9d9cffの元quotient・有限graph path・rank・Nat有限和APIの実適用条件を用いる。

<!-- cycle20-generated-evidence -->

### Cycle20 全宣言spineと実検証

source100＋生成1＝全101、新source78＋生成1＝新79、旧owner22。全公理はpropext/Classical.choice/Quot.soundの部分集合で、sorryAx/custom/ofReduceBoolなし。四single focusedはすべてexit0/warning0。sourceと明示printの順序・実stdout・moduleaudit・全個別公理集合を全件照合。

| file | 全宣言（全項を受理spine/既存owner保持の監査対象にする） | 実focused / count / source SHA / stdout SHA |
| --- | --- | --- |
| `PrimitiveMatrices.lean` | `matrix_represents_map`, `matrix_rank_eq_range`, `primitiveBMatrix`, `primitiveBMatrix_entry`, `primitiveDMatrix`, `primitiveDMatrix_entry`, `primitiveHMatrix`, `primitiveHMatrix_entry`, `primitiveVMatrix`, `primitiveVMatrix_entry`, `primitiveConstraintMatrix`, `primitiveBaseMatrix`, `primitiveGiantMatrix`, `primitiveConstraintMatrix_entry`, `primitiveBaseMatrix_entry`, `primitiveGiantMatrix_entry`, `primitiveConstraintMatrix_represents`, `primitiveBaseMatrix_represents`, `primitiveGiantMatrix_represents`, `primitiveConstraintMatrix_rank`, `primitiveBaseMatrix_rank`, `primitiveGiantMatrix_rank`, `primitiveBMatrix_mulVec`, `primitiveDMatrix_mulVec`, `primitiveVMatrix_mulVec` | `./check_research_modules.sh --focused ResearchLean/AG/AtlasCoefficientFiber/PrimitiveMatrices.lean`、exit0/warning0、25、source `e25acff4b48526c10109d291b3c93b9e8771f857e6a94222dda0ce064cb0442f`、stdout `0632635448f3cf5c381ee76801742bc58f80eb05230bfa38974cf9b91a7e6041` |
| `FiberCompatibilityCoordinates.lean` | `chainKernelEmbedding`, `chainKernelEmbedding_apply`, `chainKernelEmbedding_injective`, `chainKernelEmbedding_range`, `chainKernelCoordinateEquiv`, `chainKernelCoordinateEquiv_apply`, `primitiveVerticalEdgeMatrix`, `primitiveVerticalEdgeMatrix_entry`, `primitiveVerticalEdgeMatrix_mulVec`, `verticalCycleCoordinateEquiv`, `verticalCycleCoordinateEquiv_apply`, `mixedCycleCoordinateEquiv`, `mixedCycleCoordinateEquiv_apply`, `primitiveVMatrix_cycle_range`, `primitiveVMatrix_kernel_absorption`, `verticalHomologyProjection`, `verticalHomologyProjection_eq`, `verticalHomologyCoordinateEquiv`, `verticalHomologyCoordinateEquiv_mk`, `phiHomologyCoordinateEquiv`, `nativeKappaMatrix`, `nativeKappaMatrix_eq`, `nativeKappaMatrix_rawKappa`, `nativeKappaMatrix_kappa`, `nativeKappaMatrix_right_projection`, `nativeKappaMatrix_raw_rank`, `nativeKappaMatrix_rank`, `verticalHomologyCoordinateEquiv_left_inverse`, `verticalHomologyCoordinateEquiv_right_inverse`, `verticalHomologyCoordinateEquiv_inverse_representative`, `verticalHomologyProjection_mul_self`, `verticalHomologyProjection_rank`, `phiHomologyProjection_rank`, `nativeKappaMatrix_left_projection`, `nativeKappaMatrix_imageMap`, `chainKernelEmbedding.congr_simp` | `./check_research_modules.sh --focused ResearchLean/AG/AtlasCoefficientFiber/FiberCompatibilityCoordinates.lean`、exit0/warning0、36、source `ebdd08c9b3223e96f52b5b6a051d30f1b220b806cb2be65709b9c8f998dabe47`、stdout `eaab3f68c4cafc6bbaf06c7b9a954d46c62148c1656afb60a7f1b233776c2dce` |
| `FiniteComponents.lean` | `categoryComponentGraph`, `categoryComponentGraph_adj`, `categoryComponentGraph_reachable_iff`, `finiteZagDecidable`, `categoryComponentGraph_decidableAdj`, `categoryComponentDecision`, `categoryComponentDecision_eq_true_iff`, `categoryComponentDecision_eq_true_iff_components`, `categoryComponentEquiv`, `categoryComponentEquiv_mk`, `categoryComponentCount`, `categoryComponentCount_eq`, `incidenceComponentDecision`, `incidenceComponentDecision_eq_true_iff`, `originalCommaHomFinite`, `commaComponentDecision`, `commaComponentDecision_eq_true_iff`, `coefficientComponentCoordinateEquiv`, `coefficientComponentCoordinateEquiv_apply`, `coefficientComponentCoordinateEquiv_map`, `commaComponentCount`, `commaComponentCount_eq` | `./check_research_modules.sh --focused ResearchLean/AG/AtlasCoefficientFiber/FiniteComponents.lean`、exit0/warning0、22、source `9fb360ef24faa328bcd7e45447a5e73a732b5c9e7555a3166dbfb1ea49e410ce`、stdout `fc1abdf73b60f846c873f61c0e957e2741dd08d2292da77d0736473af3f6821e` |
| `FinitePreservationDecision.lean` | `rationalProjectionDefect`, `rationalPreservationDecision`, `rationalPreservationDecision_eq_true_iff`, `rationalPreservationDecision_empty`, `rationalPreservationDecision_failure`, `primitiveDiagnostic`, `primitiveDiagnostic_eq_blockDefect`, `primitivePreservationDecision`, `primitivePreservationDecision_eq_true_iff`, `primitivePreservationDecision_eq_true_iff_coefficient`, `allAPreservationDecision`, `allAPreservationDecision_eq_true_iff`, `lawPreservationDecision`, `lawPreservationDecision_eq_true_iff_labels`, `lawBlockDefect_zero_iff_labels`, `lawPreservationDecision_eq_true_iff`, `primitiveLawDiagnostic`, `primitiveLawDiagnostic_eq_blockDefect` | `./check_research_modules.sh --focused ResearchLean/AG/AtlasCoefficientFiber/FinitePreservationDecision.lean`、exit0/warning0、18、source `64815b21177bdef5df81a15df88a6aa783632667047e6ee7483b1b64d6e18ef8`、stdout `918a63e7085dfd4cf82b28da46e27b3338a27d937799daa48b76f1e8f88943ae` |

validation SHA `a875e816aec850f3675fafeee742cde7c1ccbf5903d45f0f3857a25319e5e2a5`。`chainKernelEmbedding.congr_simp` は同環境runtime inventoryから抽出し明示printを加えた生成宣言1件である。三新moduleのmanifest/aggregate直接登録を静的に各一回確認し、aggregateをelaborateしない。Researchfull/aggregate/全fileloop/local lakebuild、Formal移植/実build、全W/別whole-finalは未実施。固定GOAL/design/Formal/保護数学本文に変更なし。


## Cycle20 accepted / 同期

[PR5313](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5313)はhead `fc95be6c3a948aa993a0e6af15f6c44546ce90b3`、merge `056634e46f2696d6fc4ff2a7118e9be1df74df48`、`2026-10-09T01:02:27Z`で実MERGED。[root13項目/全13回帰受理](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5313#issuecomment-6072107116)はNo major findings / proof-obligation-discharged。新規数学2/Lean2の全文は同PRコメント6072078693/6072080696/6072082865/6072085029、全票No major findings・finding0・正式reruns0/2。数学B/LeanA同一初回票の資格追補は元bytes/判定/coverage不変、source変更・追加elaboration0。[Issue同期](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5290#issuecomment-6072125462)はOPENを実確認。全101標準公理・四root/四独立single focused・scan/静的方向PASS。全7CI実成功、Formal実検証六skipを区別。固定目標checkpoint、停止条件なし。

## Cycle21 selection — W1削除・重複の両例の全指定評価

```yaml
ledger_type: target_cycle_result
goal: G-135-aat-atlas-coefficient-fiber
cycle: 21
goal_blob_sha: cd5f3e684b7f390558796797874a1f16b52a6b18
base_oid: 056634e46f2696d6fc4ff2a7118e9be1df74df48
tracking_issue: 5290
report_path: research/reports/G-135-aat-atlas-coefficient-fiber.md
selection:
  proof_state_ref: Cycle20 accepted / Issue6072125462 / E原κと全保存判定接続
  proof_dag_predecessors: [C3原comma成分, C5原κ-R, C8欠損, C11同Law和, C15全mapped評価, C19原商表示と実nativeT, C20同Jと全Set-label]
  milestone: W1aとW1bの原始Source/readings/Law/全台から指定係数差と実比較・全J・代表保存を同時評価する
  proof_obligations:
    - Bool×Bool/fst/idと非定数Law、実二発生label、全chart台、K1、指定セルとOptionを保持し三次数の生成式/chain-mapを同じ原Mに接続
    - Φ点・退化なし・L/Q/R零・ε同型・κ/τ零を原fiber/商/錐と同じ原始表から証明
    - W1a eの元順像係数零とW1b eの元順像係数Q²、原η/ε/u全三次数表示
    - 非空A実比較(x,y)→y/(x,x,y)、原a/kernel/coker/fiber/κ/R/τ/rank/Jと空A零を同じproducerにより証明
    - e核/差余核とh非零保存代表、同実Law二label和による(2,0)/(0,2)を証明
  exit_criteria:
    - 指定二原始表と全Source/reading/Law/support/生成全次数/比較の対応を保持
    - 元P係数/η/εと元L-Q-R/κ-τ零を両入力で全A評価
    - 同実H1比較全元表示、全指定rank/Jと空Aの零性
    - 同実核/余核代表とh非零保存、実二Law summandと全Law欠損の指定値
    - 全spine focused/個別公理/scan/方向/出所/登録/reportを固定
  selection_reason: E接続済みの同producerを固定非保存二入力に適用し、未完W1の全指定要求を一到達点で閉じる
  expected_result_type: proof-obligation-discharged
  lean_targets: [WitnessOneInput, WitnessFullSupport, WitnessOneEvaluation, WitnessOneCoefficients, WitnessOneDiagnostics, WitnessOneLaw]
  risks: [原Kanを期待係数へ定義しない, 同実H1比較全元/商/代表, 非空Aとempty両方, 発生二labelを保持, 結論rank/保存を入力しない]
  unchecked: []
```

実装前の選定。W1の全終了条件まで同cycleで反復する。W2-W5と別全目標最終四査読は未完であり、completion_candidateはno。


## Cycle21 result proposal

```yaml
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: W1a/bの指定原始Source/readings/Law/全台と元Optionから、独立Kan Pの元e係数・η/ε/u全三次数・全A実H1比較・原J/rank・指定代表・実二Law summandの指定値を同時に評価
  exit_criteria_status:
    - 1: WitnessCommonの四点Source/fst/id/非定数Lawと二発生labelを保持。loopNerve/Nc/Na/Nb/Ma/Mbは指定名・端点・Option・面なし・K1全台を生成。元subset d0/d1およびprimitiveD0/D1全entry零、実比較全三成分squareとcomm0/comm1により同原chain-mapを確認
    - 2: 原Gamma全射/成分両逆からe Kan係数零/Q²と同unit対角。原Pの実ε三成分両逆を構成し原unit/独立uと三成分squareで一致。元Phi chart点・全mappedからL/Q/R零、κ/κ*/τ零、ε同型を全Aで証明
    - 3: 元H1全商の両逆座標で同実Tはy/(x,x,y)。元kernel/cokerと全代表をe値/二e差へ両逆同定、原aとTの指定kernel/coker次元、全Phi Betti和/κ*rank/R次元/τrank/Jを評価。空Aの実零欠損と同primitive Jを明示
    - 4: 元cochain e単独1の非零実核、e1単独1の非零実余核、元h単独1の両比較保存と粗細非零を証明。実全Law核/余核は元二labelのperiod族、同実全Law比較/欠損(2,0)/(0,2)/Rとτ零/両label h保存非零を証明
    - 5: 九single focusedと全167source/明示print/実stdout/moduleauditを全件照合、標準公理のみ。全登録/出所/scan/静的方向/固定入力保持を固定
  split_reason: none
  completion_candidate: no
  lean_artifacts: [WitnessOneInput, WitnessFullSupport, WitnessOneEvaluation, WitnessOneCoefficients, WitnessOneFiber, WitnessOneDiagnostics, WitnessOneLaw, WitnessOneRepresentatives, WitnessOneGeneration]
  evidence: [下記全167spineとsource/log hashes、同原始表→元右Kan→元η/ε/u→元商→同実J/Law比較]
  claim_mapping:
    theorem_names: [a_e_coefficient_zero, b_e_coefficient_equiv, b_e_unit_diagonal, a_eta_square, b_eta_square, a_subset_map, b_subset_map, a_allA_primitive_J, b_allA_primitive_J, a_e_kernel, b_extra_period, a_h_preserved, b_h_preserved, a_law_defect, b_law_defect, a_law_h_preserved, b_law_h_preserved]
    source_labels: [W共通Source/readings/Law/全台/全A/empty、W1a/b全指定値、有限計算表W1二行]
    conjuncts: [下記五条件対応、原a核/余核・Phi和・κ*rank・R・τrank・同J、指定代表と同全Law]
    undischarged_assumptions: [選択五条件のsemantic premiseなし・正式PR独立監査待ち、全W2-W5と別全目標最終四査読は未完]
    acceptance_point: 指定二例の全要求を同じ原始表から同じ実比較で証明した提案
    port_status: unported
audits:
  premise_delta:
    discharged: [Source/Law/真のreading細分、元全台/有限セル/Option、零微分、Gamma実成分、Phi点、全mapped、原全商同値と代表、同実J/全Law二summand]
    remaining: [正式PR独立監査、全W2-W5、別whole-goal final]
  certificate_provenance:
    discharged: [原始表/K1、原右Kan/comma成分、元ε両逆、元subsetとblock全次数同値、元商kernel/range、原二label実族]
    unresolved: []
  proof_use:
    used: [原Option/端点/面なし→原微分と成分、原ε→独立P全三次数、原実u因子化→同η square、原H1全元→実核/余核/J、全mapped→原L/Q/κ/R/τ、原label族→実Law和とh保存]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [下記九single focused/全167標準公理、scan/方向/登録、現predecessor SHA/適用]
  blocking_findings: []
  next_obligation: W2 pure fiber閉路の全指定要求、その後W3 paired/W4同G134/W5混在適合と別全目標最終四査読
```

五条件のroot提案であり、正式受理は固定headの標準PR監査へ置く。固定GOAL・四designに変更なし。W1を全目標の完了にしない。

### 原始表から同じ写像への対応

| 条件 | 入力・実写像・証明 |
| --- | --- |
| 1 全原始入力/chain | 共通WitnessCommonのqc/qf/coarser/not_coarser/laws/adequacy/nonconstant/labels_neを使用。粗Fin1 chart、e/hのFin2 loop、a細hのFin1、b細e0/e1/hのFin3、面Fin0。原targetSubsetComplexのd0/d1とprimitive行列は全entry零。r0は原chartMap、r1は原Optionでa=(0,1)、b=(e,e,h)、r2は面なしの零射。独立incidenceNamedHomのcommとsubset全三成分squareをη/ε squareへ戻し、微分二乗零とchain-mapをrankより前の原構成から保持 |
| 2 元P/η/ε/Φ | gamma_hom_eqは元GammaIncの全Homから各原辺名の保持を導き、元ConnectedComponents両逆→元right Kan coefficient。aのe liftなし→零、bのe lift二名→Q²で元ηの値が対角。a/b_P_named_equivは独立生成Pを実εの三両逆で同細原namedComplexへ移す。Pを細複体として定義し直さず、同η/ε/u全Hom等号を証明。a/b_phi_point、L/Q零、κ/κ*/τ零、ε整数次数isoは全A |
| 3 元商/全A/数値 | zeroDifferentialH1Equivは原cycles.valの核=原boundary rangeと全射を証明、全元商の両逆。subset全三次数squareから実T全元式。aKernelEquivとbCokernelEquivは同実Tの元kernel/quotientをe値/差periodへ両逆同定。空Aも同実零複体・primitiveJ零。unit欠損は同C8式と元R/τ零から実aへ戻す |
| 4 実代表/二Law | coarseCycle/aFineCycle/bFineCycleは元subset cochainで原セル値を明示、元cycles商の類。e/h/e1代表の値と非零性・同T像を証明。全LawはG134の実lawH1FamilyEquiv/全block square/元kernel-coker族を通じ二発生labelを保つ。coarseLawH/aLawH/bLawHは同元商全座標の逆で両labelの原h period1を実現し、実全Law Tの保存/非零を証明 |
| 5 出所/検証 | 下記全167source宣言と全個別標準公理、moduleaudit、現source/log SHAとreport全spineを照合。九moduleをmanifestとaggregateへ各一回登録し、aggregateをelaborateしない。固定GOAL/design/Formal/保護本文を保持 |

| W1（任意非空A/一実label） | dim ker a | dim coker a | Σ b1 Phi | rank κ* | dim R | rank τ | 同J | 全Law同J |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | --- | --- |
| a | 1 | 0 | 0 | 0 | 0 | 0 | (1,0) | (2,0) |
| b | 0 | 1 | 0 | 0 | 0 | 0 | (0,1) | (0,2) |

原入力/M/K1と任意A/ℚはambient。共通一般補題の零微分・全台・面なし・全Hom名前保存はdirection-hypothesis、指定両適用では原端点/Option/Fin0/全台から放電する。Nonempty Aは設計の非空行の方向条件、空A行は別に原実商から証明。zeroDifferentialH1Equivのh0はboundary rangeの零性、h1は全cochainのcycle化に使用。gamma_hom_eqの原射と面なしは元成分商の両逆に使用。全mappedは元εの各両逆、原L/Q/Φ/κ/R/τ零に使用。全台/同原三次数squareを元H1自然性へ、全元式/両逆を実kernel/cokerと代表へ使用。新semantic rank/同型/保存certificateなし。全Aのifは実非空/空の二証明の分類で、指定値は同実kernel/rangeから導出する。実商/成分の逆は非計算的transport、有限producerは元行列から生成した同Jである。

### 使用predecessorの現sourceと適用

各受理sourceのbytesと現使用宣言を照合し、必要な定義・実M/A/laws引数・proof-useを読む。追跡完了predecessorの内部全履歴を再認定しない。標準Lean4.28/mathlib8f9d9cffのquotient first iso、piCongrLeft/Right、finrank、元homology自然性APIの方向と条件を確認する。

| source | 現使用宣言 | 受理PR/監査・source版 | 現source SHA256 |
| --- | --- | --- | --- |
| `AtlasCoefficientFiber/WitnessCommon.lean` | `qc`, `qf`, `laws`, `adequate_coarse`, `adequate_fine`, `law_nonconstant`, `labels_ne` | [PR5297](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5297#issuecomment-6050868943) / `160a3087d20d2e9cf22de758359acb5df7ec2ecd`、現bytes一致 | `f4f46b1ae32e0462e6ed1785f88df7a31ad6ed18607169c6738b3c652bfdd56b` |
| `AtlasCoefficientFiber/GammaComma.lean` | `GammaInc`, `gammaCoefficientEquiv` | [PR5294](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5294#issuecomment-6046087706) / `dace21ebc3c8a845e0f66ac459103dd91b4e83b7`、現bytes一致 | `e10ca3baaf4768f6fbdf042321459b6fb4d9fa24e3d9e25afc61032004ca8a13` |
| `AtlasCoefficientFiber/MappedEvaluation.lean` | `evaluation0Equiv`, `evaluation1Equiv`, `evaluation2Equiv`, `evaluationStandardIso`, `phiH1_subsingleton`, `R_subsingleton`, `tau_zero` | [PR5306](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5306#issuecomment-6060895737) / `84de18ff5245f3716b5d30cb2f596446ddac39f0`、現bytes一致 | `5cf4664d5b34544d033f85b8cc95ef675043de72717f7d524aed2b170f195e7b` |
| `AtlasCoefficientFiber/LocalCoefficientSingle.lean` | `gammaCoefficientConstant_apply` | [PR5300](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5300#issuecomment-6053115567) / `70909cc76c24e689fe03efe4340afc2bbf164969`、現bytes一致 | `6520da925b2d8b2cf009869213b02c9fc780ec2557cd4573b62144f730e92505` |
| `AtlasCoefficientFiber/NativeDegreeDifferentials.lean` | `primitiveD0Matrix_entry`, `primitiveD1Matrix_entry` | [PR5310](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5310#issuecomment-6070579525) / `6c6ddd845b5834721c8ea6c79a78dde3fed6164d`、現bytes一致 | `38bddba83f8c7da6c45c7f38bd97a234464fada87d6bcd45107bad74d036047b` |
| `AtlasCoefficientFiber/DefectDiagnostics.lean` | `coefficient_kernel_dimension`, `coefficient_cokernel_dimension` | [PR5299](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5299#issuecomment-6052624414) / `4bdc59ea609b94fd087acad580666223c073a502`、現bytes一致 | `bd3d93c50341909af0ad968c8dec37ae7a591bfeaf1500e9a2a583ac67977504` |
| `AtlasCoefficientFiber/FinitePreservationDecision.lean` | `primitiveDiagnostic_eq_blockDefect`, `primitiveLawDiagnostic_eq_blockDefect` | [PR5313](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5313#issuecomment-6072107116) / `fc95be6c3a948aa993a0e6af15f6c44546ce90b3`、現bytes一致 | `64815b21177bdef5df81a15df88a6aa783632667047e6ee7483b1b64d6e18ef8` |
| `AtlasCoefficientFiber/LawFiberSequence.lean` | `lawRFamilyEquiv`, `lawR`, `lawConnectingTau` | [PR5304](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5304#issuecomment-6058853944) / `2a2847f3d499727e9ebf966c1f03fe277bdb2109`、現bytes一致 | `2a838970a53412557e5ca9bc90e9296fd5547297076392a2bcd2bd37b5b6ec55` |
| `FaceRelationSubdivision/FullSupportSubsetComparison.lean` | `fullSelected`, `fullSubsetNamedEquiv`, `fullSubsetNamed_square` | [PR5287](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5287#issuecomment-6030258596) / `0134623422114ae39f989d591cb167c6176aae3e`、現bytes一致 | `893423de007db0a677b7f933408bab4041ee9f45011f7042f1c79de8d98e15b0` |
| `FaceRelationSubdivision/LawComparisonFiberDiagnostics.lean` | `lawH1Defect_subset_sum` | [PR5287](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5287#issuecomment-6030258596) / `0134623422114ae39f989d591cb167c6176aae3e`、現bytes一致 | `99fbd72c77adf71ff6cec151ce0dda3c804f541459039c2280cdf41d86e25206` |
| `AtlasDefectComposition/FullSupportIncidence.lean` | `fullBlockNamedEquivalence`, `fullSupport_edge`, `fullSupport_face` | [PR5287](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5287#issuecomment-6030258596) / `0134623422114ae39f989d591cb167c6176aae3e`、現bytes一致 | `7707340dfe3a4bc13e9b7cd8dd8217bc332b163aab847f5f984404db298bd66c` |
| `FaceRelationSubdivision/IncidenceNamedComparison.lean` | `incidenceNamedHom_square` | [PR5287](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5287#issuecomment-6030258596) / `0134623422114ae39f989d591cb167c6176aae3e`、現bytes一致 | `56698b687013379306b13fb3bcf912d081a76ec3d4a6a71e1b644687e65f602a` |
| `FaceRelationSubdivision/LawComparisonDecomposition.lean` | `lawH1Family_natural` | [PR5287](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5287#issuecomment-6030258596) / `0134623422114ae39f989d591cb167c6176aae3e`、現bytes一致 | `496ba43e5989e9bb309860976a432ed31df91e9c6c286237a6b92b6172434f63` |
| `FaceRelationSubdivision/LawComparisonDefect.lean` | `lawH1KernelFamilyEquiv`, `lawH1CokernelFamilyEquiv` | [PR5287](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5287#issuecomment-6030258596) / `0134623422114ae39f989d591cb167c6176aae3e`、現bytes一致 | `ba062facc20c993767ee9ce423fbc0573ece5da57ee5c7c7993abc8e34cb8b72` |
| `AtlasDefectComposition/LinearConjugation.lean` | `kernelEquiv`, `cokernelEquiv` | [PR5287](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5287#issuecomment-6030258596) / `0134623422114ae39f989d591cb167c6176aae3e`、現bytes一致 | `2fb0f6f319a8dcdf8848f4dfd7672371a930b41aa96919888df2b4a273b40fbb` |

出所照合SHA `37d3594443779bda8371a97d65789002a4dc9a57c206ba102f02a1e30c854feb`。C11 LawFiberSequenceの現在版はC13追加所有APIを含む受理source、同lawR/lawRFamilyEquiv/lawConnectingTauのbodyはC11から不変。

<!-- cycle21-generated-evidence -->

### Cycle21 全宣言spineと実検証

全167=source167、generated0。九single focusedは全exit0/warning0。全source/明示print/実stdoutの順序と全個別公理集合、runtime moduleauditの全件数を照合。各公理はpropext/Classical.choice/Quot.soundの部分集合、sorryAx/custom/ofReduceBoolなし。

| file | 全受理候補spine（全項） | 実focused / count / source SHA / stdout SHA |
| --- | --- | --- |
| `WitnessOneInput.lean` | `loopNerve`, `Nc`, `Na`, `Nb`, `Ma`, `Mb`, `Ma_all_mapped`, `Mb_all_mapped`, `Ma_faces_mapped`, `Mb_faces_mapped` | `./check_research_modules.sh --focused ResearchLean/AG/AtlasCoefficientFiber/WitnessOneInput.lean`、exit0/warning0、10、source `1470764f7aba1a7571873ed9671d29736d9fa16ab9213de4e200d37d15490518`、stdout `6fc5336528292ccc3afe48b1e540c584d36e27c3731a1bd385242cb5187eff18` |
| `WitnessFullSupport.lean` | `zeroDifferentialH1Equiv`, `zeroDifferentialH1Equiv_mk`, `fine_nonempty`, `labelEquiv`, `labelEquiv_symm`, `labels_card` | `./check_research_modules.sh --focused ResearchLean/AG/AtlasCoefficientFiber/WitnessFullSupport.lean`、exit0/warning0、6、source `95b4dca558735ab40bc172f8ff648884296f3c7bcf086d4d44a1560bcb107b1d`、stdout `3fb912af4d01bc66060dd7dc309cc81f1b65d7b6b8aff6919db6490f81a4c633` |
| `WitnessOneEvaluation.lean` | `coarse_d0_zero`, `coarse_d1_zero`, `a_d0_zero`, `a_d1_zero`, `b_d0_zero`, `b_d1_zero`, `coarseNamedCoordinates`, `aNamedCoordinates`, `bNamedCoordinates`, `a_named_map`, `b_named_map`, `coarseCoordinates`, `aCoordinates`, `bCoordinates`, `a_subset_square`, `b_subset_square`, `a_subset_map`, `b_subset_map`, `coarse_subset_d0_zero`, `coarse_subset_d1_zero`, `coarse_primitive_D0_zero`, `coarse_primitive_D1_zero`, `a_subset_d0_zero`, `a_subset_d1_zero`, `a_primitive_D0_zero`, `a_primitive_D1_zero`, `b_subset_d0_zero`, `b_subset_d1_zero`, `b_primitive_D0_zero`, `b_primitive_D1_zero` | `./check_research_modules.sh --focused ResearchLean/AG/AtlasCoefficientFiber/WitnessOneEvaluation.lean`、exit0/warning0、30、source `5a888a070d71dd71b6dd5e5dc7230d9fad2876caf2afb101b06c5d455d8e1206`、stdout `3b4acda4ed74886b88b312ae9fe345bec0dbe5c13e99b2f10b1f31b72fbea030` |
| `WitnessOneCoefficients.lean` | `componentsEquivOfHomEq`, `gamma_hom_eq`, `gammaObjectEquiv`, `gammaNoFaceComponentsEquiv`, `gammaNoFaceCoefficientEquiv`, `coarseEdge`, `a_e_vertices_empty`, `a_e_coefficient_zero`, `b_e_vertices_equiv`, `b_e_coefficient_equiv`, `b_e_unit_diagonal` | `./check_research_modules.sh --focused ResearchLean/AG/AtlasCoefficientFiber/WitnessOneCoefficients.lean`、exit0/warning0、11、source `36d4e207e595c51c9a06c39ce9c73c14be80b7079bfdf995cc7a048306a6e4ea`、stdout `291c2b2b13d564a365919443d341e56e476efceec8b1af3c5a851bc31cfa6c76` |
| `WitnessOneFiber.lean` | `a_phi_point`, `a_L_zero`, `a_Q_zero`, `a_evaluation_iso`, `a_phi_H1_zero`, `a_kappa_zero`, `a_kappaStar_zero`, `a_R_dimension`, `a_tau_zero`, `a_kappaStar_rank`, `a_tau_rank`, `b_phi_point`, `b_L_zero`, `b_Q_zero`, `b_evaluation_iso`, `b_phi_H1_zero`, `b_kappa_zero`, `b_kappaStar_zero`, `b_R_dimension`, `b_tau_zero`, `b_kappaStar_rank`, `b_tau_rank`, `a_phi_H1_sum`, `b_phi_H1_sum` | `./check_research_modules.sh --focused ResearchLean/AG/AtlasCoefficientFiber/WitnessOneFiber.lean`、exit0/warning0、24、source `3a27e935048054133c2713d2240a08ce9fbcb1d67aefe89f1658aa56d22c9e4a`、stdout `9c29e5a5e2c1e66796522d22b9adf1677b8800d20d4dfb5c9a9f3e6e89ecee22` |
| `WitnessOneDiagnostics.lean` | `aMap`, `bMap`, `aMapKernelEquiv`, `aMap_surjective`, `bMap_injective`, `differencePeriod`, `differencePeriod_kernel`, `differencePeriod_surjective`, `bMapCokernelEquiv`, `bMapCokernelEquiv_mk`, `aKernelEquiv`, `bCokernelEquiv`, `bCokernelEquiv_mk`, `a_surjective`, `b_injective`, `a_defect`, `b_defect`, `a_primitive_J`, `empty_H1_subsingleton`, `a_unit_defect`, `a_empty_defect`, `a_empty_primitive_J`, `a_allA_primitive_J`, `b_primitive_J`, `b_unit_defect`, `b_empty_defect`, `b_empty_primitive_J`, `b_allA_primitive_J` | `./check_research_modules.sh --focused ResearchLean/AG/AtlasCoefficientFiber/WitnessOneDiagnostics.lean`、exit0/warning0、28、source `e6b420c45d48034cfc49cb7da90b6d7f61d7b8e4ea564838f3422153eb430a65`、stdout `bcc9e603e1dbebc0c2ae5deb395fb9c92f66f7b41be5b1a7bf2ffaef84e320f1` |
| `WitnessOneLaw.lean` | `coarseBlockCoordinates`, `aBlockCoordinates`, `bBlockCoordinates`, `a_block_map`, `b_block_map`, `aLawKernelEquiv`, `bLawCokernelEquiv`, `a_law_defect`, `b_law_defect`, `a_primitive_law_J`, `b_primitive_law_J`, `a_law_R_zero`, `a_law_tau_zero`, `a_law_R_tau_dimensions`, `b_law_R_zero`, `b_law_tau_zero`, `b_law_R_tau_dimensions`, `coarseLawCoordinates`, `aLawCoordinates`, `bLawCoordinates`, `a_law_map`, `b_law_map`, `coarseLawH`, `aLawH`, `bLawH`, `a_law_h_preserved`, `b_law_h_preserved`, `coarse_law_h_nonzero`, `a_law_h_nonzero`, `b_law_h_nonzero` | `./check_research_modules.sh --focused ResearchLean/AG/AtlasCoefficientFiber/WitnessOneLaw.lean`、exit0/warning0、30、source `de0f6a54e13784214208a2d0e38aaade13e43c85ab8e30903a5d66b78eda05a0`、stdout `1b631ba1cc12490158a01df311317016fdef8402f084e78e5419fd722f1171b1` |
| `WitnessOneRepresentatives.lean` | `coarseCycle`, `aFineCycle`, `bFineCycle`, `coarseClass`, `aFineClass`, `bFineClass`, `coarseClass_coordinates`, `aFineClass_coordinates`, `bFineClass_coordinates`, `a_e_kernel`, `coarse_e_nonzero`, `a_h_preserved`, `b_h_preserved`, `coarse_h_nonzero`, `a_h_nonzero`, `b_h_nonzero`, `b_extra_period`, `b_extra_cokernel_nonzero` | `./check_research_modules.sh --focused ResearchLean/AG/AtlasCoefficientFiber/WitnessOneRepresentatives.lean`、exit0/warning0、18、source `2bfe81917bed961dd3598d42ebaf678e7fb3d36dd250a2ec4e551e8fa7339a3d`、stdout `14fe9b4eee5b88f2d59e4f02759b40342a7f06bc09374284d25ca92ea327eafd` |
| `WitnessOneGeneration.lean` | `a_evaluation_equiv`, `a_evaluation_equiv_toHom`, `a_P_named_equiv`, `a_epsilon_square`, `a_eta_square`, `b_evaluation_equiv`, `b_evaluation_equiv_toHom`, `b_P_named_equiv`, `b_epsilon_square`, `b_eta_square` | `./check_research_modules.sh --focused ResearchLean/AG/AtlasCoefficientFiber/WitnessOneGeneration.lean`、exit0/warning0、10、source `f7732a3b36f0bce962240d7ad9f39f532f8d0eb005baf7a588abcc97a9947aaf`、stdout `4817f2cf96edf3373dea1c47ac28933bd7a1202c72b2558a78f94ea83813f7c5` |

validation SHA `3fdd0226267fcafc50f1151b86458ef59ae21fcd69e8f98db5992091c883ac37`。必要な単一dependency cacheはrootのみ生成し、追加前のdependencyを用いたcheckの使用APIは同source内の既存bodyが不変であることを確認。Research full/全module/aggregate/fileloop/lake full build、Formal build/移植、W2-W5の全指定評価、別全目標最終査読は未実施。

## Cycle21 受理後同期

固定head `fecb994402b579b6a0fe15190ef10b4752a7c44b`、[PR5314](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5314)、実merge `ff9f9c008ea3d942776e14503ac575098206395c`。五条件 `proof-obligation-discharged`、新規独立数学2/Lean2すべてNo major findings、中心0/非中心0、reruns0/2。[全13root受理](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5314#issuecomment-6072664284)、[Issue同期](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5290#issuecomment-6072677769)。全167source/generated0、九focused exit0/warning0/std3。七CI成功、Formal六step skipped。全GOALcheckpoint、W2–5/別wholefinal/Formal移植未完。

## Cycle22 selection（実装前固定）

```yaml
ledger_type: target_cycle_result
goal: G-135-aat-atlas-coefficient-fiber
cycle: 22
goal_blob_sha: cd5f3e684b7f390558796797874a1f16b52a6b18
base_oid: ff9f9c008ea3d942776e14503ac575098206395c
tracking_issue: 5290
report_path: research/reports/G-135-aat-atlas-coefficient-fiber.md
selection:
  proof_state_ref: Issue5290 Cycle21同期6072677769 / PR5314 root6072664284
  proof_dag_predecessors: [C3原Kan, C5原fiber, C8欠損式, C9局所η同型, C10pure条件, C13実Law, C20原producer, C21全台商座標]
  milestone: W2指定pure circleの全要求を同原始入力から同時に評価する
  proof_obligations:
    - 同Source/fst-id/非定数Law二発生label/全台K1、粗c-h/細c-h-k/face無し、h mapped/k noneの原入力と全三次数生成
    - 原Phiのk円・Gamma h一点、原Kanの全係数とη次数別同型、独立P/η/ε/u全三成分の対応
    - 原kappa/原tau零、literal R全商とQの両逆、Phi Betti和/κrank/Rdim/τrank、同ηH1欠損00と同u x→(x,0)/J01
    - 原k単独1のfiber類と同実余核類、h非零保存、pure C3prime違反、全A空Aおよび実二Lawの核余核/R/τの和
    - 全新spineのfocused/個別公理/source/log/report/受理dependency/登録/scan/方向、固定GOALとdesign保持
  exit_criteria:
    - 指定原始表と同reading/Law/全台の構成、原微分と全三次数比較squareが証明済み
    - 原Kan係数の局所単一成分条件から原ηの全次数両逆、独立Pと元ε/u/ηの対応が証明済み
    - 同原R/Q座標・κτ・全rank・η欠損・実T全元式・Jが入力から証明済み
    - 指定原代表/非零h/pure非保存/全A空A/全Law二成分の全要求が証明済み
    - 全宣言個別print/log/runtime/公理と検証・出所・登録・記録が一致
  selection_reason: 一般spineとW1は受理済み。pure classでη同型とfiber非保存を独立評価し全Wへの直接deltaを作る
  expected_result_type: proof-obligation-discharged
  lean_targets: [WitnessTwoInput, WitnessTwoComparison, WitnessTwoCoefficients, WitnessTwoFiber, WitnessTwoLaw]
  risks: [Pを粗複体から選ばない, 原Phi圏のloop端点二射を保持, Rを全Phiへ移すのは原mixed空証明の後のみ, 二Lawを台で商化しない, 空Aを全Aから除かない]
  unchecked: [W2の全選定条件は未実装、同cycle内で全放電する]
```

分割理由なし。補題一file完成のみではcycleを閉じない。W3–W5と別全目標最終四査読は引き続き未完。GOAL/design/Formalは変更しない。

## Cycle22 result proposal

```yaml
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: 指定W2の原始h/k Option表から原Kan η同型とpure R/k代表・同実T余核・全A/二Lawの全指定値を同時に接続
  exit_criteria_status:
    - 1: 同四点Source/fst-id/非定数fst Law/二発生labelを保持。Nc c-h/Nf c-h-k/Fin0 faces/全台K1/Mのh some・k none、元subsetとprimitive d0/d1零、独立u全三次数squareを原表から構成
    - 2: 元PhiIncのk両端点射を保つ全対象zigzag、元Gamma h一点と粗面なしから単一成分条件を生成。原Kan unitηの全三次数両逆、独立Pと粗namedのcochain同値・η/ε/u全Hom squareを証明
    - 3: 原mixed空からκ/κ*/標準τ零、literal kerκ*のR全両逆と元H¹Q両逆を構成。Phi Betti和1/κ*rank0/Rdim1/τrank0、元ηH¹欠損00、全元T x→(x,0)・実余核k period/J01を同原商で評価
    - 4: k単独1の同cochain→原Phi非零類と実余核非零類、実五項制限によるR類非零、原h類の保存と粗細非零、pure C3prime違反・非保存、空A/全A nativeJ/R/Phi和を証明。二発生Lawを保持した同実全Law T/余核/R/κ/τ/η/代表/和を評価
    - 5: 全新source/生成補助/print/実stdout/標準公理/runtime/reportを照合。必要root単一cache、直接登録、現受理source出所、全scan/方向/固定入力保持を確認
  split_reason: none
  completion_candidate: no
  lean_artifacts: [WitnessTwoInput, WitnessTwoComparison, WitnessTwoCoefficients, WitnessTwoFiber, WitnessTwoGeneration, WitnessTwoLaw]
  evidence: [下記全spineと同source/log hashes、元Kan成分→同η両逆→P全三次数→元商T/R/Q→同代表→同実Law/原producer]
  claim_mapping:
    theorem_names: [phi_zigzag, gamma_components, etaEquiv, eta_epsilon_square, pNamedEquiv, eta_square, epsilon_square, rCoordinates, qCoordinates, kappa_zero, tau_zero, subset_map, defect, allA_primitive_J, k_cochain_fiber, k_cokernel_nonzero, kFiberClass_nonzero, h_preserved, C3prime_failure, law_defect, law_R_dimension, law_unit_defect, lawK_cokernel_nonzero]
    source_labels: [W共通Source/readings/Law/全台/全A/空A、W2 pure fiber円、同原三次数と数値表、同実Law二成分の和]
    conjuncts: [上記五固定終了条件、原η欠損/Phi和/κ*rank/R/τrank/J/指定h-k代表と非零性/実全Law]
    undischarged_assumptions: [選択五条件のsemantic premiseなし・正式PR独立監査待ち、全W3 paired/W4同G134/W5と別全目標最終四査読は未完]
    acceptance_point: W2の全指定要求を原表から同じ原P/R/τ/u/Law比較で評価したroot提案
    port_status: unported
audits:
  premise_delta:
    discharged: [指定全台/有限セル/Option/端点、mixed空、元Phi-Gamma-Lambda単一成分、原η全次数両逆、元商全座標/原代表/同実欠損/二Law和]
    remaining: [正式PR独立監査、全W3–W5、別whole-goal final]
  certificate_provenance:
    discharged: [原始表/K1→原incidenceとright Kan、局所元商条件→η三両逆、原κ→literal R、標準SES→原τ/制限、原T商period→J、二発生label→実Law族]
    unresolved: []
  proof_use:
    used: [端点/Fin0→微分と成分、mapped/none→Gamma/Phiとκ/τ、原mixed空→R全Phi同定、原η逆と原u因子化→独立P全次数square、元H1両逆→実余核/指定非零k-h、原制限完全性とη可逆→同k実R非零、原label族→実Law二和]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [下記六single focused/全個別標準公理/source-log照合、直接登録/scan/方向と受理source現版]
  blocking_findings: []
  next_obligation: 指定W3面ありとmだけ除くpairedの全要求、その後W4同G134/W5混在適合と別全目標最終四査読
```

rootの五条件受理提案。全GOALはtarget-proof-checkpointであり、全目標の完了判定ではない。固定GOAL・四design・Formal・保護本文を変更しない。

### 原始入力から同じ写像への対応

| 固定条件 | 同じ入力・構成・実写像 |
| --- | --- |
| 1 原表/chain | WitnessCommonのqc/qf/coarser/非constant fst Law/adequacy/二発生labelを再利用。粗Fin1 chart/h loop、細Fin1 chart/h0-k1 loop、粗細faceFin0、h some0/k none。元d0は同端点差、d1は原面なし、primitiveD0/D1全entryも零。Mの原commと全三次数subset_squareから原r0/r1/r2へ接続 |
| 2 元係数/P/二射 | 原PhiIncのinduced incidence圏の全対象へ原chart-edge射のzigzagを生成。k loopのfalse/true二射を減らさない。元Gammaはh一本/faceなし、元Lambdaは粗faceなし。localUnitEquivを実条件に適用し原right Kan η全三次数両逆・微分可換を生成。Pを粗複体へ定義し直さず、η逆で全三次数pNamedEquivを構成し元η/ε/uのf0/f1/f2等号を証明 |
| 3 同原R/Q/T/τ | 原mixed空から原κ・κ*・標準SESのτ零。Rはliteral kerκ*のままpureFiberREquivで全Phi族へ、元Phi商からk値へ両逆。元H¹Qの同原R同型を合成してqCoordinates。元cycles/boundary商座標→全T x→(x,0)→同実range quotient k period両逆→J01。η欠損は独立元unitH1の両逆から00 |
| 4 同原代表/二Law | fineCycle ![0,1]は元k単独1 cocycle、同cochainの原Phi制限はphiKCycle。元Phi類/R類/実余核類のperiod1非零、さらに同細H¹を実五項制限射で送るkFiberClassがη可逆・元完全性・同実余核非零により非零。h単独1は原Tで保ち粗細とも非零。空Aの実H¹/R/Phi添字を零にし全A nativeJ分類を証明。実Lawは両発生labelを台で商化せず元block全三square/H¹自然性/kernel-coker族/R族/標準δ成分から同値と和を生成 |
| 5 検証/記録 | 六module各単一focused、全sourceと生成補助の個別print/標準公理/runtime/source-log/report照合、manifest/aggregate各一回直接登録、静的方向検査、保護入力差分0。必要単一dependencycacheはrootのみ生成。正式受理は固定headの独立PR監査に置く |

| W2任意非空A/一label | dim ker a | dim coker a | Σ b1 Phi | rank κ* | dim R | rank τ | 同J |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | --- |
| 指定pure円 | 0 | 0 | 1 | 0 | 1 | 0 | (0,1) |
| 空A | 0 | 0 | 0 | 0 | 0 | 0 | (0,0) |
| 同実全Law二発生成分の和 | 0 | 0 | 2 | 0 | 2 | 0 | (0,2) |

指定Source/readings/原Option/全台K1/ℚ/全Aはambient。一般zeroDifferentialやlocalUnitEquivの零微分・単一成分、pureFiberREquivのMixed空は方向仮定で、指定適用では端点/原射zigzag/Fin0/Optionから放電。Nonempty Aは設計数値表の方向条件、空Aを別証明して全Aを保持。P・η・ε・u・R・τ・実Law比較は元生成経路を再利用し、期待rank/保存情報をfieldへ渡さない。非計算的商transport/有限Pi/逆選択は証明済み元全射・両逆に限る。原Jの有限producerは元行列からの同じ実blockDefectを返す。

### 使用predecessorの現source版と適用

元型・必要定義・適用M/A/Law引数・proof-useを読み、受理版と現sourceのbytesを照合した。受理済み内部全履歴を再認定しない。

| source | 現使用API | 受理PR/監査・source版 | 現source SHA256 |
| --- | --- | --- | --- |
| `AtlasCoefficientFiber/WitnessCommon.lean` | `qc`, `qf`, `laws`, `adequate_coarse`, `adequate_fine`, `law_nonconstant`, `labels_ne` | [PR5297](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5297#issuecomment-6050868943) / `160a3087d20d2e9cf22de758359acb5df7ec2ecd`、現bytes一致 | `f4f46b1ae32e0462e6ed1785f88df7a31ad6ed18607169c6738b3c652bfdd56b` |
| `AtlasCoefficientFiber/NativeDegreeDifferentials.lean` | `primitiveD0Matrix_entry`, `primitiveD1Matrix_entry` | [PR5310](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5310#issuecomment-6070579525) / `6c6ddd845b5834721c8ea6c79a78dde3fed6164d`、現bytes一致 | `38bddba83f8c7da6c45c7f38bd97a234464fada87d6bcd45107bad74d036047b` |
| `AtlasCoefficientFiber/FinitePreservationDecision.lean` | `primitiveDiagnostic_eq_blockDefect`, `primitiveLawDiagnostic_eq_blockDefect` | [PR5313](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5313#issuecomment-6072107116) / `fc95be6c3a948aa993a0e6af15f6c44546ce90b3`、現bytes一致 | `64815b21177bdef5df81a15df88a6aa783632667047e6ee7483b1b64d6e18ef8` |
| `AtlasCoefficientFiber/LawFiberSequence.lean` | `lawRFamilyEquiv`, `lawR`, `lawConnectingTau` | [PR5304](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5304#issuecomment-6058853944) / `2a2847f3d499727e9ebf966c1f03fe277bdb2109`、現bytes一致 | `2a838970a53412557e5ca9bc90e9296fd5547297076392a2bcd2bd37b5b6ec55` |
| `FaceRelationSubdivision/FullSupportSubsetComparison.lean` | `fullSelected`, `fullSubsetNamedEquiv`, `fullSubsetNamed_square` | [PR5287](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5287#issuecomment-6030258596) / `0134623422114ae39f989d591cb167c6176aae3e`、現bytes一致 | `893423de007db0a677b7f933408bab4041ee9f45011f7042f1c79de8d98e15b0` |
| `FaceRelationSubdivision/LawComparisonFiberDiagnostics.lean` | `lawH1Defect_subset_sum` | [PR5287](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5287#issuecomment-6030258596) / `0134623422114ae39f989d591cb167c6176aae3e`、現bytes一致 | `99fbd72c77adf71ff6cec151ce0dda3c804f541459039c2280cdf41d86e25206` |
| `AtlasDefectComposition/FullSupportIncidence.lean` | `fullBlockNamedEquivalence`, `fullSupport_edge`, `fullSupport_face` | [PR5287](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5287#issuecomment-6030258596) / `0134623422114ae39f989d591cb167c6176aae3e`、現bytes一致 | `7707340dfe3a4bc13e9b7cd8dd8217bc332b163aab847f5f984404db298bd66c` |
| `FaceRelationSubdivision/IncidenceNamedComparison.lean` | `incidenceNamedHom_square` | [PR5287](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5287#issuecomment-6030258596) / `0134623422114ae39f989d591cb167c6176aae3e`、現bytes一致 | `56698b687013379306b13fb3bcf912d081a76ec3d4a6a71e1b644687e65f602a` |
| `FaceRelationSubdivision/LawComparisonDecomposition.lean` | `lawH1Family_natural` | [PR5287](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5287#issuecomment-6030258596) / `0134623422114ae39f989d591cb167c6176aae3e`、現bytes一致 | `496ba43e5989e9bb309860976a432ed31df91e9c6c286237a6b92b6172434f63` |
| `FaceRelationSubdivision/LawComparisonDefect.lean` | `lawH1KernelFamilyEquiv`, `lawH1CokernelFamilyEquiv` | [PR5287](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5287#issuecomment-6030258596) / `0134623422114ae39f989d591cb167c6176aae3e`、現bytes一致 | `ba062facc20c993767ee9ce423fbc0573ece5da57ee5c7c7993abc8e34cb8b72` |
| `AtlasDefectComposition/LinearConjugation.lean` | `kernelEquiv`, `cokernelEquiv` | [PR5287](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5287#issuecomment-6030258596) / `0134623422114ae39f989d591cb167c6176aae3e`、現bytes一致 | `2fb0f6f319a8dcdf8848f4dfd7672371a930b41aa96919888df2b4a273b40fbb` |
| `AtlasCoefficientFiber/LocalFiber.lean` | `PhiChart`, `PhiEdge`, `phiD0_apply`, `GammaVertex`, `GammaInc`, `LambdaFace` | [PR5303](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5303#issuecomment-6057242603) / `70633bfc653fe823fbdbbbcec8b1d6fc12a5bb5b`、現bytes一致 | `cfc7d3a3d44a78879840daae8cf5a846510813156598c1006e9686c1b68013a4` |
| `AtlasCoefficientFiber/LocalPreservation.lean` | `localUnitEquiv`, `unitH1_bijective_of_local` | [PR5300](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5300#issuecomment-6053115567) / `70909cc76c24e689fe03efe4340afc2bbf164969`、現bytes一致 | `29c5ab27b2e133dd2d1415612a229c3505c685542726a98ec25c8adc399f1061` |
| `AtlasCoefficientFiber/DefectMaps.lean` | `directH1_factor`, `directH1_old` | [PR5313](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5313#issuecomment-6072107116) / `fc95be6c3a948aa993a0e6af15f6c44546ce90b3`、現bytes一致 | `0d45260ccf0bc021c223c1a5c8b5fa09288bfd728684fab5af13513b3d3d4449` |
| `AtlasCoefficientFiber/FiveTermSequence.lean` | `fiberRestrictionH1`, `fiveTerm_exact_at_fineH1` | [PR5297](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5297#issuecomment-6050868943) / `160a3087d20d2e9cf22de758359acb5df7ec2ecd`、現bytes一致 | `c9fb934891dfd966ac23711e566cda115987220862e904c63cc5f9ed002687e3` |
| `AtlasCoefficientFiber/PurePreservation.lean` | `pureFiberREquiv`, `pure_kappaStar_zero` | [PR5300](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5300#issuecomment-6053115567) / `70909cc76c24e689fe03efe4340afc2bbf164969`、現bytes一致 | `c40d5e80e53d9475487a7372dc53744002b4120b4a21415fd1590e98314e19f1` |
| `AtlasCoefficientFiber/PureComparison.lean` | `kappa_zero_of_mixed_isEmpty`, `connectingTau_zero_of_mixed_isEmpty` | [PR5297](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5297#issuecomment-6050868943) / `160a3087d20d2e9cf22de758359acb5df7ec2ecd`、現bytes一致 | `ed95e9286b51c7ce15fb05e0fe19f83ac574e321ee1a01ec4216c951fc767d01` |
| `AtlasCoefficientFiber/RestrictionHomology.lean` | `restrictionStandardHomologyREquiv` | [PR5297](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5297#issuecomment-6050868943) / `160a3087d20d2e9cf22de758359acb5df7ec2ecd`、現bytes一致 | `44317eec491e425838829730a8c8c1474b8f855c8a97f58f82d8d0ac3ed1f5d0` |
| `AtlasCoefficientFiber/LawHomologyCoordinates.lean` | `lawCoarseHomologyEquiv`, `lawUnit_homology_component`, `lawUnitH1` | [PR5302](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5302#issuecomment-6054697310) / `7f20e6aaaae8c51298b32d955ca16a6b0076b84a`、現bytes一致 | `6052b12559e0f2fe036036ff60349e451e9fbb948da10582236aee718e3ae68c` |
| `AtlasCoefficientFiber/WitnessOneInput.lean` | `loopNerve` | [PR5314](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5314#issuecomment-6072664284) / `fecb994402b579b6a0fe15190ef10b4752a7c44b`、現bytes一致 | `1470764f7aba1a7571873ed9671d29736d9fa16ab9213de4e200d37d15490518` |
| `AtlasCoefficientFiber/WitnessFullSupport.lean` | `zeroDifferentialH1Equiv`, `fine_nonempty`, `labels_card` | [PR5314](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5314#issuecomment-6072664284) / `fecb994402b579b6a0fe15190ef10b4752a7c44b`、現bytes一致 | `95b4dca558735ab40bc172f8ff648884296f3c7bcf086d4d44a1560bcb107b1d` |
| `AtlasCoefficientFiber/WitnessOneEvaluation.lean` | `coarse_d0_zero` | [PR5314](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5314#issuecomment-6072664284) / `fecb994402b579b6a0fe15190ef10b4752a7c44b`、現bytes一致 | `5a888a070d71dd71b6dd5e5dc7230d9fad2876caf2afb101b06c5d455d8e1206` |
| `AtlasCoefficientFiber/WitnessOneDiagnostics.lean` | `empty_H1_subsingleton` | [PR5314](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5314#issuecomment-6072664284) / `fecb994402b579b6a0fe15190ef10b4752a7c44b`、現bytes一致 | `e6b420c45d48034cfc49cb7da90b6d7f61d7b8e4ea564838f3422153eb430a65` |
| `AtlasCoefficientFiber/WitnessOneCoefficients.lean` | `componentsEquivOfHomEq` | [PR5314](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5314#issuecomment-6072664284) / `fecb994402b579b6a0fe15190ef10b4752a7c44b`、現bytes一致 | `36d4e207e595c51c9a06c39ce9c73c14be80b7079bfdf995cc7a048306a6e4ea` |

出所照合SHA `337e2f787094b4af370b3e085a2acae03abfee38083b0109e09d851357105738`。C9 LocalFiberの今回使用APIは不変、C12追加を含む現在版をC12受理版で照合した。C6の同じ五項制限/標準τ/Q-R、C8の元directH1は現owner版で追う。標準Lean4.28/mathlib8f9d9cffの原商first iso、piCongr/関数Unique、旧/native H¹自然性、finrank/finite sumの方向とinstanceを確認。全期待数値は指定原始表の帰結である。

<!-- cycle22-generated-evidence -->

### Cycle22 全宣言spineと実検証

全131=source130、generated1。六single focused全exit0/warning0。全source/明示print/実stdout/moduleauditの件数と順序、全個別公理を照合。各集合はpropext/Classical.choice/Quot.soundの部分集合。

| file | 全受理候補spine（全項） | 実focused/count/source SHA/stdout SHA |
| --- | --- | --- |
| `WitnessTwoInput.lean` | `Nc`, `Nf`, `M`, `mixed_empty` | `./check_research_modules.sh --focused ResearchLean/AG/AtlasCoefficientFiber/WitnessTwoInput.lean`、exit0/warning0、4、source `ccb5ede9bc9bce722b6057b550d1e3de5bdb2fbd9ee867deb060445f6e41a76c`、stdout `8648bd462cd62d661bb13ebf7ba583d018a1a0633dbe6d18389aaaacdec161f9` |
| `WitnessTwoComparison.lean` | `coarse_d0_zero`, `coarse_d1_zero`, `fine_d0_zero`, `fine_d1_zero`, `coarseNamedCoordinates`, `fineNamedCoordinates`, `named_map`, `coarseCoordinates`, `fineCoordinates`, `subset_square`, `subset_map`, `coordinateMap`, `coordinateMap_injective`, `kPeriod`, `kPeriod_kernel`, `kPeriod_surjective`, `coordinateCokernelEquiv`, `coordinateCokernelEquiv_mk`, `cokernelEquiv`, `cokernelEquiv_mk`, `comparison_injective`, `defect`, `primitive_J`, `empty_defect`, `allA_primitive_J`, `coarse_subset_d0_zero`, `coarse_subset_d1_zero`, `coarse_primitive_D0_zero`, `coarse_primitive_D1_zero`, `fine_subset_d0_zero`, `fine_subset_d1_zero`, `fine_primitive_D0_zero`, `fine_primitive_D1_zero` | `./check_research_modules.sh --focused ResearchLean/AG/AtlasCoefficientFiber/WitnessTwoComparison.lean`、exit0/warning0、33、source `a35a7394b6e529070001a0850536bdea096e93d68f32f0e8adb5cf237f8a2988`、stdout `ff47616b3fd745c86dd459af2470e2eef50865daeef6e167c405a6968438bc6b` |
| `WitnessTwoCoefficients.lean` | `phiChartEquiv`, `phiChart_subsingleton`, `phi_zigzag`, `phi_components`, `gammaVertexEquiv`, `gammaObjectEquiv`, `gamma_components`, `lambda_components`, `etaEquiv`, `etaEquiv_toHom`, `unit_bijective`, `unit_defect`, `eta_epsilon_square` | `./check_research_modules.sh --focused ResearchLean/AG/AtlasCoefficientFiber/WitnessTwoCoefficients.lean`、exit0/warning0、13、source `3d87ab5f8e442265a5736ec2ecb85e8b8ec37d289bdb8c0eef09ef2413c4489c`、stdout `6b93f998298a0b42eda0beca5571286403ced508538bde64a2edc2db318c3dab` |
| `WitnessTwoFiber.lean` | `phiEdgeEquiv`, `phi_d0_zero`, `phi_d1_zero`, `phiCoordinates`, `phi_dimension`, `coarseChartEquiv`, `phi_dimension_sum`, `kappa_zero`, `kappaStar_zero`, `kappaStar_rank`, `rFamilyEquiv`, `rCoordinates`, `r_dimension`, `tau_zero`, `tau_rank`, `phiKCycle`, `phiKClass`, `phiK_period`, `phiK_nonzero`, `rK`, `rK_period`, `rK_nonzero`, `coarseCycle`, `fineCycle`, `coarseClass`, `fineClass`, `coarseClass_coordinates`, `fineClass_coordinates`, `h_preserved`, `coarse_h_nonzero`, `fine_h_nonzero`, `k_cokernel_period`, `k_cokernel_nonzero`, `C3prime_failure`, `nonpreservation`, `k_cochain_fiber`, `empty_R_subsingleton`, `empty_R_dimension`, `allA_R_dimension`, `qCoordinates`, `q_dimension`, `allA_phi_dimension_sum`, `kFiberClass`, `kFiberClass_nonzero` | `./check_research_modules.sh --focused ResearchLean/AG/AtlasCoefficientFiber/WitnessTwoFiber.lean`、exit0/warning0、44、source `24df232ed7d5cf39861d419797a9558165543e12b6d7f5e402ac6361e1360458`、stdout `3978675b5d32934a9735fd660ae2bfb7383a2af5a1fb127e4a45fbbefea2b530` |
| `WitnessTwoGeneration.lean` | `pNamedEquiv`, `eta_square`, `epsilon_square` | `./check_research_modules.sh --focused ResearchLean/AG/AtlasCoefficientFiber/WitnessTwoGeneration.lean`、exit0/warning0、3、source `2917a4b4ef8b7c508634fe22314e07c8899b526241d59ae82a8a1879de1ef934`、stdout `9a01567d4d28e3cda529f3edaf4260dd8ab24bac3bed807e6ea74844a0aac1b4` |
| `WitnessTwoLaw.lean` | `coarseBlockCoordinates`, `fineBlockCoordinates`, `block_map`, `lawCokernelEquiv`, `law_defect`, `primitive_law_J`, `law_kernel_dimension`, `law_cokernel_dimension`, `lawRCoordinates`, `law_R_dimension`, `law_kappaStar_zero`, `law_kappaStar_rank`, `law_tau_zero`, `law_tau_rank`, `coarseLawCoordinates`, `fineLawCoordinates`, `law_map`, `coarseLawH`, `fineLawH`, `fineLawK`, `law_h_preserved`, `coarse_law_h_nonzero`, `fine_law_h_nonzero`, `lawRK`, `lawRK_period`, `law_unit_bijective`, `law_unit_defect`, `lawCokernelEquiv_mk`, `lawK_cokernel_period`, `lawK_cokernel_nonzero`, `lawRK_nonzero`, `law_kappa_zero`, `law_phi_dimension_sum`, `rCoordinates.congr_simp` | `./check_research_modules.sh --focused ResearchLean/AG/AtlasCoefficientFiber/WitnessTwoLaw.lean`、exit0/warning0、34、source `1bf8a87e1305d75a6a18864a4acda3a52b3a60b25c67ed895f362094aa143a13`、stdout `fca136b597d5b343a65d5b3c96cbe014f606a9dfb68d6a10154ebda3067d88b3` |

生成補助`rCoordinates.congr_simp`はLaw moduleの実auditが捕捉する一宣言であり、個別printも追加して全件を保持した。validation SHA `0e4b9e1bc8e498a7d3d33b5d3e89487b6f3edcc28b4cfa72f3afc7a830ef4091`。必要root単一dependency cacheのみ生成し、同APIの後追加/コメント更新は既存使用body不変、最終六focusedは現source版を検証した。Research full/全module/aggregate/fileloop/lake full build、Formal build/移植、W3–W5全指定評価、別全目標最終四査読は未実施。

静的import方向228moduleとpackage方向はPASS。diff check、placeholder/hidden-BiDi/privacy/追加禁止語/逆importの新hit0、固定GOAL/design/Formal/保護領域の差分0、六manifest/aggregate各一回登録。scan SHA `62883e06ed27b4ba24392192671bdb98bfa8314471df08db76bc41116ae02b7b`。正式独立PR四査読・CI・受理・merge・Issue同期はこの提案の後に記録する。


## Cycle22 受理・実マージ同期

[PR #5315](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5315) の固定head `fc5051f31c46a22cd6074ae71de0fec52fe9ff1b` は新規独立数学2/Lean2の全No major findings、中心0/非中心0、reruns0/2で、W2固定五終了条件をproof-obligation-dischargedとして受理した。[root全13監査](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5315#issuecomment-6073341813)は四票全文/全131個別appendixと現source/log/実scan match/24受理現版を再統合した。実merge `2d8f4dfe1924a5f4c1e5bd245975443a813365b1`（2026-10-09T02:59:31Z）はGitHub MERGEDと取得origin/mainが一致。[Issue同期](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5290#issuecomment-6073361593)を実再取得して全文一致・OPENを確認した。

root六focusedと四独立指定single-focusedはexit0/warning0、全131公理はpropext/Classical.choice/Quot.soundのみ。固定head七CI SUCCESS、Research integrity実step成功、Formal六build/cache/audit stepはSKIPPED、新六focusedのCI実行なし。Research full/aggregate/fileloop/local lakebuild/Formalbuild/移植未実施。全目標はcheckpoint、W3–W5と別whole-finalは未完。停止条件なし。

## Cycle23 selection

実装前の選定。W3の面あり/mだけ除いたpaired全指定要求を一到達点とし、以下の終了条件まで同cycleで実装・検証を反復する。W4/W5と別全目標最終四査読は後続であり、completion_candidate:no。

```yaml
ledger_type: target_cycle_result
goal: G-135-aat-atlas-coefficient-fiber
cycle: 23
goal_blob_sha: cd5f3e684b7f390558796797874a1f16b52a6b18
base_oid: 2d8f4dfe1924a5f4c1e5bd245975443a813365b1
tracking_issue: 5290
report_path: research/reports/G-135-aat-atlas-coefficient-fiber.md
selection:
  proof_state_ref: Issue5290 Cycle22同期6073361593 / 同report Cycle22受理 / 原WitnessThreeInput・NonzeroとC19 native表示
  proof_dag_predecessors: [C3原局所fiber/Kan, C5κ/R/forest, C6原補正代表/五項τ, C8原診断/G133相殺, C10錐, C11/C13実Law族, C18-C20原座標表示, C21全台元商/API]
  milestone: GOAL W3の面ありとmだけ除くpairedをA-Eの同原生成経路で全同時評価する
  proof_obligations: [同指定セル/Option/全台とpaired差分, 全Phi/Gamma/Lambda成分と独立P/ηεu三次数, 原κ/R/H1Q/τとz/β符号, 原H1/H2商の全両逆と実T/J, 同h非零保存/G133相殺/総錐, 全A/空A/同二発生Lawの元各射とrank, 全新宣言監査/受理依存/記録]
  exit_criteria:
    - 原WitnessThree.MとpairedMのセル/像を保持しmだけを除去した差を全三次数原微分・比較へ接続する
    - 面ありGamma_aのforest/連結性とPhi_xの円・他Phi/Gammaの点/Lambda唯一を原圏から生成しPを粗表/η恒等へ三次数同定、pairedGamma_a二孤立成分/P各生成式/η対角とε/uを同原Kanから同定する
    - 面あり原B核零/κ零/R=Q[k]dual/H1Q両逆、標準τの指定k代表とbeta(a1)=1・f0f1=(0,1)の符号を証明しH2P=Q2/diag/τ同型/rank1、pairedR=Q/τ零/H2P零を同原射で証明する
    - 原coarse/fine/paired全H1商をh/h-k座標へ両逆同定し実T=id/(h,0)、実J00/01/同h非零保存、fineH2零/H2比較核Q/原totalConeH1Qと同G133相殺零、全A空Aおよび実二発生Lawの全要求・代表・rankを接続する
    - 全新sourceと実生成補助を個別print/axioms/focused/runtime/report/hashへ照合し全登録・受理現dependency・scan/import方向/固定入力保持と標準PR新規数学2Lean2/root全13回帰を通過する
  selection_reason: 未完W3を既受理非零τだけで代替せず、原順像の生成同定と全診断・paired・Law・錐までを閉じて固定W全体へのproof distanceを縮める
  expected_result_type: proof-obligation-discharged
  lean_targets: [WitnessThreeCoefficients, WitnessThreeComparison, WitnessThreeFiber, WitnessThreeGeneration, WitnessThreeTransgression, WitnessThreeDiagnostics, WitnessThreeLaw]
  risks: [full induced圏の重複射, 原H1の非零d0とboundary商, pairedη次数1非同型だがH1同型, z/beta/標準δ符号, mだけ除去の保持, G133相殺とτの区別, 全A/二label/原totalCone]
  unchecked: [W3全局所成分/P生成, 全H1H2同定/同τ代表, paired全評価, 全A/Law/原錐]
```

## Cycle23 result proposal：W3の同原面あり/なし全指定評価

元selectionの五終了条件と粒度を保持する。実装fileを11へ分けて局所成分、全商、生成三次数、代表、錐、Law、rankを接続した。一file完了によるcycle分割はしていない。正式PRゲート前のproposalであり、math/Lean四査読・root受理・CI・mergeは次の運用段階で確認する。W3の数学要求は以下の同原構成で満たす候補となった。W4/W5と別whole-goal最終四査読は未完、completion_candidate:no。

| 固定W3要求 | 同じ原対象・射への証拠 | 全方向と指定値 |
| --- | --- | --- |
| 元セル・Option・台・Law、mだけ除くpaired | C19受理WitnessThreeInputのNc/Nf/M/pairedNf/pairedM、C6受理WitnessCommon、今回subset_square/paired_subset_square | chartと六辺名は同じ、f0/f1の名と像を保持。面ありのみm=(k,a1,a0)、k/m像none、同名平行a0/a1を保持。全非空Aの全セル、空A零、元二発生labelを保持 |
| 原全Phi/Gamma/Lambda成分 | phiChartEquiv/phiFace_empty/phi_zigzag/phi_components、gammaM/gamma_vertex_zigzag/gamma_components、lambdaFaceEquiv/lambda_components | 全誘導incidence圏の元chartEdge/edgeFace射からzigzagを構成。Phiのk loopや二端incidenceを消さず一成分、Gamma_aはmで二liftを接続。mの異名両端を使うgamma_forest/B_kernel。原面liftは各一名 |
| mなし同成分・a係数差 | pairedPhiChartEquiv/paired_phi_components/pairedLambdaFaceEquiv、pairedGammaEdge_empty/paired_gamma_hom_eq/pairedGammaComponentsEquiv/pairedAVerticesEquiv/pairedACoefficientEquiv/paired_a_unit_diagonal | 全原Gamma成分は原lift名を保つ。aはa0/a1二成分・Q²、原unitは(q,q)。他の水平辺は各同名一lift、二原面はmapped。Phiは同原chart/k名と全空面型のpairedPhiEquiv |
| 独立Kan P・三次数η/ε/u | etaEquiv/etaEquiv_toHom、pNamedEquiv/eta_square/epsilon_square、pairedP0Equiv/pairedP1Equiv/pairedP2Equiv/pairedPNamedEquiv/paired_eta0_values/paired_eta1_values/paired_eta2_values | 面ありPを原粗三次数へ両逆同定しηは恒等。paired Pは原ε像の全射/単射から原水平五辺座標へ両逆同定、d0=(y-x,y-x,z-x,z-y,0)、d1=(a0-b+c,a1-b+c)。η1=(a,a,b,c,h)、εは原k値0、uは独立元比較。Pをこれら座標から再定義しない |
| 原H¹全商・T/J・同h | coarsePeriod_kernel/surjective/finePeriod_kernel/surjective/pairedPeriod_kernel/surjective、coarse/fine/pairedCoordinates、subset_map/paired_subset_map、primitive_J/paired_primitive_J、coarseHCycle/coarseHClass/coarse_h_nonzero/fine_h_nonzero/paired_h_nonzero | 全cycles periodの核を元d0像へ両包含で同定し、全有理periodを元cycleで実現して両逆。Tはid/(h,0)、J00/01。h元類が両方で同じ非零period1。実paired全余核はpairedCokernelEquiv/mkの元k period |
| 全原Phi H¹・κ・literal R・Q | phiEdgeXEquiv/phiEdge_other_empty/phi_d0_zero/phi_d1_zero/phiXCoordinates/phiFamilyPeriod_bijective、gamma_forest/B_kernel/kappa_zero/kappaStar_zero/rFamilyEquiv/rCoordinates/qCoordinates、pairedRFamilyEquiv/pairedPhiEquiv/pairedRCoordinates/pairedQCoordinates | xのk全商のみQ、他chartは零、sum b1=1。原forest leaf条件でB核零→κ/κ*零、元R=kerκ*から全Phiとの両逆を生成。元Q標準H¹も同literal R経由でQ。pairedも同kが1、τ零 |
| 元z/βとτ符号・全rank | verticalZ/horizontalBeta/verticalZ_single/horizontalBeta_single/horizontalBeta_corrects/correctedEdge_eq_W/correctedW_face_values、rK/tauPRepresentative/tau_rK/tau_rK_period、verticalKCycle/rawRPeriod/rawRPeriod_rK/rK_spans/tau_period/rawRCoordinates/tauEquiv/tau_rank | 原k値1、水平a1値1/他0、βB=-zD、元三面微分(0,1,0)。元標準δの代表式を使い元τ[k]は原二面商(0,1)、F1-F0=1。独立k閉路双対periodで全R/全τを同定して両逆・rank1、τ/rK非零。τからdomain座標を選ばない |
| 元H²/総錐/G133相殺 | secondPeriod_kernel/surjective/coarseNamedH2Coordinates/coarseH2Coordinates/pH2Coordinates、fine_d1_surjective/fineH2_subsingleton/paired_d1_surjective/pairedPH2_subsingleton、comparisonH2KernelCoordinates/totalConeH1Coordinates/totalConeH1_dimension/cancellation_zero/paired_cancellation_zero | 粗二面微分像は同対角値、元H²P=Q²/diag≃Q。細全三面の任意値を元d1で実現しH²fine零。元H²u核Q、元totalCone H¹は指定G133核射影経由Q。原η/εのG133相殺は全Aで零。paired P H²零/τ零 |
| 全Aと空A・同二実Law成分 | allA_primitive_J/allA_paired_primitive_J、unit_bijective/allA_paired_unit_bijective、allA_R_dimension/allA_paired_R_dimension、allA_phi_dimension_sum/allA_paired_phi_dimension_sum/empty_tau_zero/allA_tau_rank、Law module全族同定 | 非空A行は同原全セル、空Aの原商/元P H¹/R/τは零。原各labelは非空値逆像。law_mapは全label恒等、paired_law_mapは各(h,0)、元J00/02。原lawR/lawQ全商Q²、原lawκ/κ*零、原lawτ全元独立period恒等で同型/rank2、pairedτ零。全元Law a同型、同h非零保存/paired k実余核非零、元Law総錐H¹次元2/G133相殺零 |
| 全原rank表・E実producer | full_rank_table/paired_full_rank_table、law_full_rank_table/paired_law_full_rank_table、law_phi_dimension_sum/paired_law_phi_dimension_sum | 以下の原数値を同じunitH1/原全Phi/κ*/literalR/connectingTau/primitiveDiagnostic/primitiveLawDiagnosticから証明。期待rankの供給はない |

| 原入力 | dim ker a / dim coker a | sum b1 Phi | rank κ* | dim R | rank τ | 元J |
| --- | --- | --- | --- | --- | --- | --- |
| 面あり・各非空A | 0 / 0 | 1 | 0 | 1 | 1 | (0,0) |
| mなし・各非空A | 0 / 0 | 1 | 0 | 1 | 0 | (0,1) |
| 面あり・元二発生Law | 0 / 0 | 2 | 0 | 2 | 2 | (0,0) |
| mなし・元二発生Law | 0 / 0 | 2 | 0 | 2 | 0 | (0,2) |
| 空A・両方 | 0 / 0 | 0 | 0 | 0 | 0 | (0,0) |

mは既存x上のk閉路を使用し、両側chart型は同じFin3である。G134のfresh頂点/区間を増やす原操作との違いはこの原表、phiEdgeXEquiv/phiXCoordinates、tau_rK_periodで評価した。G134の区間の全評価はW4の次到達点として保持する。

### Material premiseとproof-use

| premise / 役割 | 出所・放電 | 使用先 |
| --- | --- | --- |
| 指定Source/readings/全射/coarser・非定数Law/粗細adequacy・二発生label、finite named K1/M/Option・全A / Wのdischarge-required | 受理C6 WitnessCommonと受理C19 WitnessThreeInputの全field、原m表、元fullSupport/全選択両逆。任意A.Nonemptyは指定の方向仮定、空Aは同原商から別に証明 | 元Kan/carrier/局所圏、全subset同型、同元lawGeneratedComplex/各label |
| 局所成分/forest/pure / 具体Wのdischarge-required | 元Φ全incidence zigzag、原m二incidenceによるΓ全接続、元Lambda唯一、mixed_subsingletonと異名端点、paired全some面によるmixed空 | 元localUnitEquiv、B核零/κ零、R全Φ、paired標準τ零。一般構成へ追加しない |
| period核＝元d0像・period全射 / 汎用direction-hypothesis、具体Wはdischarge-required | 粗/細/paired/P元全cycle方程式から元chart potentialを構成し両包含、h/k単独元cycleから全有理値を生成 | periodQuotientEquiv、元H¹全商両逆、同実比較と全余核、実a同型/J |
| P三次数両逆・微分可換・全ε像 / discharge-required | 面あり原η局所同型の逆、paired原ε単射とrestriction零cochainの原Kan lift、原ε微分可換と原因子化。CochainEquiv全fieldは同原射から構成 | 同η/ε/u三次数、paired P全d1像とH¹/H²、元standard同型/錐 |
| k cochain閉性・βB=-zD・元ε2原像・標準δ符号 / discharge-required | 原垂直面空、元correctedW再結合/原m微分零、原二面unitのε評価=(0,1,0)、受理標準δ代表公式 | 原rK、原τ代表と非零、原k閉路独立period、全R/全τ座標、全Law原τ |
| H²全像/商・τ単射全射・原totalCone条件 / discharge-required | 原coarse secondPeriod核/全射、fine/paired/P原d1全射、実際T全単射と元zeroDefect iff、元五項列exact、元標準H¹u全射 | τEquiv/rank、H²u核、G133指定coneKernelProjectionEquiv、lawTotalCone族 |
| lawUnit/LawR/τ/余核全族同型・各同名h/k / discharge-required | 受理C11/C13原族自然性和同じ旧H¹商、今回各label原単射/全射・原periodと標準τ成分公式。labelEquiv/labels_cardを保持 | 元全Law J/κ/R/Q/τ/rank、同非零h/k、G133相殺/元総錐 |

元同型・rank・期待τ・exactnessを新引数/結論fieldへ置いていない。periodQuotientEquivとstandardH2_subsingleton_of_surjectiveの一般条件は具体原微分から放電する。k独立periodは元垂直closed chainへの双対評価であり、τの値から定義しない。全原商/両逆を保つため、逆像への対象縮小・供給certificate・種類の交換・未使用material premiseは見いだしていない。

### Cycle23 result ledger

```yaml
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: 原W3全局所成分/Kan/全商/全ηεu/κRτ/指定代表/全A/空A/実二Law/錐/G133相殺/全rankを同時接続
  exit_criteria_status: [1同原セル表/像は保持, 2原全局所成分/P三次数両逆とηεuを構成, 3原κR/Q/標準τ代表符号と両側全H2を構成, 4全H1/実T/J/非零h/原総錐/G133/全A/Lawを構成, 5全275公理/十一focused/現依存/全登録を照合・正式PR四票/root全13回帰は次段階]
  split_reason: none
  completion_candidate: no
  lean_artifacts: [WitnessThreeComparison, WitnessThreeCoefficients, WitnessThreeGeneration, WitnessThreeFiber, WitnessThreeDiagnostics, WitnessThreePairedGeneration, WitnessThreePairedFiber, WitnessThreeTransgression, WitnessThreeCones, WitnessThreeRankTable, WitnessThreeLaw]
  evidence: [以下全275spineと検証]
  claim_mapping:
    theorem_names: [上の条項別mappingと以下全spine]
    source_labels: [固定GOAL W3/A-E, 固定witnesses W3と有限計算表]
    conjuncts: [同元A/二射/商/κRτ/全指定代表/原Law/錐への上の対応]
    undischarged_assumptions: []
    acceptance_point: 五選定終了条件を保持しW3全要求を同原Kanから評価、正式受理前proposal
    port_status: unported
  unchecked: [標準PR新規四票/root受理, actual CI/merge/Issue同期, 全GOAL W4/W5/別final]
audits:
  premise_delta:
    discharged: [上の具体原入力/全局所成分/商/二射/κRτ/全指定代表/全A/実二Law/原錐]
    remaining: [W4/W5/別whole-final]
  certificate_provenance:
    discharged: [原Option表/元incidence/Zigzag/元η逆/元ε像/原cycle/標準δ代表/原literalR/元Law族]
    unresolved: []
  proof_use:
    used: [上の役割別使用先]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [以下十一単一focused/275個別公理とstatic scan]
  blocking_findings: []
  next_obligation: 標準PRゲートの後、G134同原W4全比較を順像・fiber分解へ全指定評価する。W5/別全目標四査読も保持
```

### 受理済み現dependency

下の38sourceは記載受理版と現bytesが一致する。使用する現statement、必要な定義、適用引数と今回proof-useを確認し、受理内部全履歴の再認定はしない。C13源版は最終受理657e版でもbytes一致する。EndpointHomologyのG133後追加APIはC7/C10受理版、今回は同oldH2Equivを使用する。固定Lean4.28.0/mathlib8f9d9cffのquotKerEquivOfSurjective、piCongr、homologyMapIso、ofBijective、finite/rank APIの条件を保持する。

| source | 今回使用宣言 | 受理ref/源版 | source SHA-256 |
| --- | --- | --- | --- |
| `AtlasCoefficientFiber/WitnessCommon.lean` | `qc`, `qf`, `laws`, `adequate_coarse`, `adequate_fine` | [PR5297](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5297#issuecomment-6050868943) / `160a3087d20d2e9cf22de758359acb5df7ec2ecd` | `f4f46b1ae32e0462e6ed1785f88df7a31ad6ed18607169c6738b3c652bfdd56b` |
| `AtlasCoefficientFiber/FinitePreservationDecision.lean` | `primitiveDiagnostic_eq_blockDefect`, `primitiveLawDiagnostic_eq_blockDefect` | [PR5313](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5313#issuecomment-6072107116) / `fc95be6c3a948aa993a0e6af15f6c44546ce90b3` | `64815b21177bdef5df81a15df88a6aa783632667047e6ee7483b1b64d6e18ef8` |
| `AtlasCoefficientFiber/LawFiberSequence.lean` | `lawRFamilyEquiv`, `lawR`, `lawConnectingTau` | [PR5304](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5304#issuecomment-6058853944) / `2a2847f3d499727e9ebf966c1f03fe277bdb2109` | `2a838970a53412557e5ca9bc90e9296fd5547297076392a2bcd2bd37b5b6ec55` |
| `FaceRelationSubdivision/FullSupportSubsetComparison.lean` | `fullSelected`, `fullSubsetNamedEquiv`, `fullSubsetNamed_square` | [PR5287](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5287#issuecomment-6030258596) / `0134623422114ae39f989d591cb167c6176aae3e` | `893423de007db0a677b7f933408bab4041ee9f45011f7042f1c79de8d98e15b0` |
| `FaceRelationSubdivision/LawComparisonFiberDiagnostics.lean` | `lawH1Defect_subset_sum` | [PR5287](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5287#issuecomment-6030258596) / `0134623422114ae39f989d591cb167c6176aae3e` | `99fbd72c77adf71ff6cec151ce0dda3c804f541459039c2280cdf41d86e25206` |
| `AtlasDefectComposition/FullSupportIncidence.lean` | `fullBlockNamedEquivalence`, `fullSupport_edge`, `fullSupport_face` | [PR5287](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5287#issuecomment-6030258596) / `0134623422114ae39f989d591cb167c6176aae3e` | `7707340dfe3a4bc13e9b7cd8dd8217bc332b163aab847f5f984404db298bd66c` |
| `FaceRelationSubdivision/IncidenceNamedComparison.lean` | `incidenceNamedHom_square` | [PR5287](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5287#issuecomment-6030258596) / `0134623422114ae39f989d591cb167c6176aae3e` | `56698b687013379306b13fb3bcf912d081a76ec3d4a6a71e1b644687e65f602a` |
| `FaceRelationSubdivision/LawComparisonDecomposition.lean` | `lawH1Family_natural` | [PR5287](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5287#issuecomment-6030258596) / `0134623422114ae39f989d591cb167c6176aae3e` | `496ba43e5989e9bb309860976a432ed31df91e9c6c286237a6b92b6172434f63` |
| `FaceRelationSubdivision/LawComparisonDefect.lean` | `lawH1CokernelFamilyEquiv` | [PR5287](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5287#issuecomment-6030258596) / `0134623422114ae39f989d591cb167c6176aae3e` | `ba062facc20c993767ee9ce423fbc0573ece5da57ee5c7c7993abc8e34cb8b72` |
| `AtlasDefectComposition/LinearConjugation.lean` | `cokernelEquiv` | [PR5287](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5287#issuecomment-6030258596) / `0134623422114ae39f989d591cb167c6176aae3e` | `2fb0f6f319a8dcdf8848f4dfd7672371a930b41aa96919888df2b4a273b40fbb` |
| `AtlasCoefficientFiber/LocalFiber.lean` | `PhiChart`, `PhiEdge`, `phiD0_apply`, `GammaVertex`, `GammaInc`, `LambdaFace` | [PR5303](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5303#issuecomment-6057242603) / `70633bfc653fe823fbdbbbcec8b1d6fc12a5bb5b` | `cfc7d3a3d44a78879840daae8cf5a846510813156598c1006e9686c1b68013a4` |
| `AtlasCoefficientFiber/LocalPreservation.lean` | `localUnitEquiv`, `unitH1_bijective_of_local` | [PR5300](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5300#issuecomment-6053115567) / `70909cc76c24e689fe03efe4340afc2bbf164969` | `29c5ab27b2e133dd2d1415612a229c3505c685542726a98ec25c8adc399f1061` |
| `AtlasCoefficientFiber/PurePreservation.lean` | `pureFiberREquiv`, `pure_kappaStar_zero` | [PR5300](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5300#issuecomment-6053115567) / `70909cc76c24e689fe03efe4340afc2bbf164969` | `c40d5e80e53d9475487a7372dc53744002b4120b4a21415fd1590e98314e19f1` |
| `AtlasCoefficientFiber/PureComparison.lean` | `kappa_zero_of_mixed_isEmpty`, `connectingTau_zero_of_mixed_isEmpty` | [PR5297](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5297#issuecomment-6050868943) / `160a3087d20d2e9cf22de758359acb5df7ec2ecd` | `ed95e9286b51c7ce15fb05e0fe19f83ac574e321ee1a01ec4216c951fc767d01` |
| `AtlasCoefficientFiber/RestrictionHomology.lean` | `restrictionStandardHomologyREquiv` | [PR5297](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5297#issuecomment-6050868943) / `160a3087d20d2e9cf22de758359acb5df7ec2ecd` | `44317eec491e425838829730a8c8c1474b8f855c8a97f58f82d8d0ac3ed1f5d0` |
| `AtlasCoefficientFiber/LawHomologyCoordinates.lean` | `lawCoarseHomologyEquiv`, `lawUnit_homology_component`, `lawUnitH1` | [PR5302](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5302#issuecomment-6054697310) / `7f20e6aaaae8c51298b32d955ca16a6b0076b84a` | `6052b12559e0f2fe036036ff60349e451e9fbb948da10582236aee718e3ae68c` |
| `AtlasCoefficientFiber/WitnessFullSupport.lean` | `zeroDifferentialH1Equiv`, `fine_nonempty`, `labels_card` | [PR5314](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5314#issuecomment-6072664284) / `fecb994402b579b6a0fe15190ef10b4752a7c44b` | `95b4dca558735ab40bc172f8ff648884296f3c7bcf086d4d44a1560bcb107b1d` |
| `AtlasCoefficientFiber/WitnessOneDiagnostics.lean` | `empty_H1_subsingleton` | [PR5314](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5314#issuecomment-6072664284) / `fecb994402b579b6a0fe15190ef10b4752a7c44b` | `e6b420c45d48034cfc49cb7da90b6d7f61d7b8e4ea564838f3422153eb430a65` |
| `AtlasCoefficientFiber/WitnessOneCoefficients.lean` | `componentsEquivOfHomEq` | [PR5314](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5314#issuecomment-6072664284) / `fecb994402b579b6a0fe15190ef10b4752a7c44b` | `36d4e207e595c51c9a06c39ce9c73c14be80b7079bfdf995cc7a048306a6e4ea` |
| `AtlasCoefficientFiber/RawBlocks.lean` | `edgeBlock_recombination`, `verticalEdgeBoundary_single`, `verticalEdgeInclusion_single` | [PR5301](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5301#issuecomment-6053510508) / `cc62fac23e82e41728dd8188967c73bde36b1516` | `c87584a49ddd341aa965b4f16d53ca8499487e2f4023f18ef4484c6218e73b07` |
| `AtlasCoefficientFiber/GammaChains.lean` | `mixedGraphTarget_val_left` | [PR5296](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5296#issuecomment-6049620284) / `61659d7586accb379f03883d3722c5d6a622fad2` | `5943afba7cddb60d1614f29413ba5bcf9b9dcba7d6381f4d2d4e0e0fcab3719f` |
| `AtlasCoefficientFiber/CochainRepresentatives.lean` | `correctedFiberClass`, `correctedFiberClass_raw`, `correctedEdgeCochain`, `correctedEdgeCochain_dual`, `correctedEdgeCochain_d1_mixed`, `verticalCocycleClass_mk` | [PR5297](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5297#issuecomment-6050868943) / `160a3087d20d2e9cf22de758359acb5df7ec2ecd` | `95807117bdb00bfc921f677118a6770a6abd0c38831f1b11ff934d46c4885025` |
| `AtlasCoefficientFiber/FiberCohomology.lean` | `fiberRRawEquiv` | [PR5303](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5303#issuecomment-6057242603) / `70633bfc653fe823fbdbbbcec8b1d6fc12a5bb5b` | `74aa1f4930cbd01151d5c1792d76c43324208de1c0a795924312885b97fb6951` |
| `AtlasCoefficientFiber/NamedForest.lean` | `namedForest_of_subsingleton` | [PR5296](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5296#issuecomment-6049620284) / `61659d7586accb379f03883d3722c5d6a622fad2` | `2116f69b5a631b72e637e143c5e60543747cb384638208513a640b781b17688e` |
| `AtlasCoefficientFiber/WitnessThreeInput.lean` | `Nc`, `Nf`, `M`, `pairedNf`, `pairedM`, `fineNerve`, `edgeMap_none_iff` | [PR5312](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5312#issuecomment-6071529511) / `a90fee53a0ee64caea90acb1073d43b776521cd3` | `68f89f83e088f3d4e2f55bb7e08fe6be339e8751ade0ffdc2d4f3147282b34c8` |
| `AtlasCoefficientFiber/GammaForest.lean` | `GammaForest`, `mixedHorizontalBoundary_ker_eq_bot`, `kappa_eq_zero_of_forest`, `kappaStar_eq_zero_of_forest`, `forestFiberREquiv` | [PR5296](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5296#issuecomment-6049620284) / `61659d7586accb379f03883d3722c5d6a622fad2` | `c783cd60bb052d487adaee010650109b8df5d89d31fb1c0b81458316d8f09948` |
| `AtlasCoefficientFiber/EvaluationAnnihilator.lean` | `restriction0_zero_iff`, `restriction1_zero_iff`, `evaluation0_preimage_of_restriction_zero`, `evaluation1_preimage_of_restriction_zero` | [PR5295](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5295#issuecomment-6047664301) / `927f6be84e525e853df340d1ad7c45f5c9f47358` | `e240cdad380f4a7ecfd3c422183eab5b6197ad7443faf85ad7fec7cc1fea061b` |
| `AtlasCoefficientFiber/MappedEvaluation.lean` | `evaluation2Equiv` | [PR5306](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5306#issuecomment-6060895737) / `84de18ff5245f3716b5d30cb2f596446ddac39f0` | `5cf4664d5b34544d033f85b8cc95ef675043de72717f7d524aed2b170f195e7b` |
| `AtlasCoefficientFiber/TransgressionRepresentatives.lean` | `evaluationRestriction_connecting_representative`, `correctedRestrictionCycle_fiberClass` | [PR5297](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5297#issuecomment-6050868943) / `160a3087d20d2e9cf22de758359acb5df7ec2ecd` | `264aa0a0632fe0a27991b1e9c6483670b29c1782e684e925428def8383c9d139` |
| `AtlasCoefficientFiber/ConeSequences.lean` | `totalCone` | [PR5301](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5301#issuecomment-6053510508) / `cc62fac23e82e41728dd8188967c73bde36b1516` | `28b6b74c831faca3f5be94d79fade13316513d2e833c1f9d41950921ac6da654` |
| `AtlasCoefficientFiber/LawDefectDiagnostics.lean` | `lawCoefficientCancellation_zero` | [PR5304](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5304#issuecomment-6058853944) / `657e562eaa154e94155681e07d3c218e6998375b` | `2269b369f00de215a3208021c05df0c77a476225e8fd6233e331759ae946e8d0` |
| `AtlasCoefficientFiber/LawCoefficientCones.lean` | `lawTotalConeFamilyIso` | [PR5304](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5304#issuecomment-6058853944) / `657e562eaa154e94155681e07d3c218e6998375b` | `6d1fe486a122491a23964b1229b9828c93bb0919076edd653942870b7638ccf4` |
| `AtlasCoefficientFiber/DefectShortExact.lean` | `coefficientCancellation_zero` | [PR5299](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5299#issuecomment-6052624414) / `4bdc59ea609b94fd087acad580666223c073a502` | `91d48bcd53b9979e35f93f5bee351d0ac48ac6c6432bbf8e435ac770e987d4c8` |
| `AtlasCoefficientFiber/DefectDiagnostics.lean` | `coefficient_zeroDefect_iff` | [PR5299](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5299#issuecomment-6052624414) / `4bdc59ea609b94fd087acad580666223c073a502` | `bd3d93c50341909af0ad968c8dec37ae7a591bfeaf1500e9a2a583ac67977504` |
| `AtlasDefectComposition/EndpointNaturality.lean` | `oldH2Equiv_natural`, `oldH2Map_mk` | [PR5287](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5287#issuecomment-6030258596) / `0134623422114ae39f989d591cb167c6176aae3e` | `04e56cbecdd1fc4a7c0056533c58e590750e0eb81a2f0c6371cdebde8f446b80` |
| `AtlasDefectComposition/EndpointHomology.lean` | `oldH2Equiv` | [PR5301](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5301#issuecomment-6053510508) / `cc62fac23e82e41728dd8188967c73bde36b1516` | `1deb845209adcd269ea6e2a0113af970a747b20af890a6f1107eb2eb5e916e4b` |
| `AtlasDefectComposition/CochainEquivalence.lean` | `cochainEquivZeroExtensionIso` | [PR5269](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5269#issuecomment-6007700344) / `74cb93564070661509ac0c2f842596e63d0957fa` | `7c02968c79ec94b9a0f8349701cd965d4208d9ea7017b08507255272d4255d8a` |
| `AtlasDefectComposition/ConeConditional.lean` | `coneKernelProjectionEquiv` | [PR5269](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5269#issuecomment-6007700344) / `74cb93564070661509ac0c2f842596e63d0957fa` | `8ec1099b4465cda75163a788c1b79f1ed5e1fa04565db1eac74b28af9995c3c9` |

源照合SHA `9a620fb1aeee56cf93f470ad78d7513882e0d060a2f6fb37c67035603923ebf7`。受理コメント現取得の本文/file hashも公開受理refsへ対応させた。

<!-- cycle23-generated-evidence -->
### 全spine・個別公理・focused検証

namespaceは`AAT.AG.AtlasCoefficientFiber.WitnessThree`。全275（273source+2生成）を省略せず列挙する。全項が元入力からの構成/実同型/代表/全元射/診断とその支持APIで、今回新設spineである。各root単一file focusedはexit0/warning0、個別公理とmodule監査数が同じ。

| file | 全受理候補spine（全項） | 実focused/count/source SHA/stdout SHA |
| --- | --- | --- |
| `WitnessThreeComparison.lean` | `periodQuotientEquiv`, `periodQuotientEquiv_mk`, `coarsePeriod`, `coarsePeriod_kernel`, `coarsePeriod_surjective`, `coarseNamedCoordinates`, `finePeriod`, `finePeriod_kernel`, `finePeriod_surjective`, `fineNamedCoordinates`, `pairedPeriod`, `pairedPeriod_kernel`, `pairedPeriod_surjective`, `pairedNamedCoordinates`, `named_map`, `paired_named_map`, `coarseCoordinates`, `fineCoordinates`, `pairedCoordinates`, `subset_square`, `paired_subset_square`, `subset_map`, `paired_subset_map`, `comparison_bijective`, `defect`, `pairedCoordinateMap`, `pairedCoordinateMap_injective`, `kPeriod`, `kPeriod_kernel`, `kPeriod_surjective`, `coordinateCokernelEquiv`, `pairedCokernelEquiv`, `pairedCokernelEquiv_mk`, `paired_comparison_injective`, `paired_defect`, `primitive_J`, `paired_primitive_J`, `empty_defect`, `paired_empty_defect`, `allA_primitive_J`, `allA_paired_primitive_J` | `./check_research_modules.sh --focused ResearchLean/AG/AtlasCoefficientFiber/WitnessThreeComparison.lean`、exit0/warning0、41、source `3f8e454fda05f5114dd34bbe68238724b012704fe933de23e86299feb4fe0a7e`、stdout `88b25e3968a59054380efc965f1bf0c15d397ba8602d278aeb6826bb92e7b229` |
| `WitnessThreeCoefficients.lean` | `phiChartEquiv`, `phiChart_subsingleton`, `phiFace_empty`, `phi_zigzag`, `phi_components`, `pairedPhiChartEquiv`, `pairedPhiChart_subsingleton`, `pairedPhiFace_empty`, `paired_phi_zigzag`, `paired_phi_components`, `lambdaFaceEquiv`, `pairedLambdaFaceEquiv`, `gammaVertexChoice`, `gammaM`, `gamma_vertex_zigzag`, `gamma_zigzag`, `gamma_components`, `lambda_components`, `etaEquiv`, `etaEquiv_toHom`, `unit_bijective`, `unit_defect`, `pairedGammaEdge_empty`, `paired_gamma_hom_eq`, `pairedGammaObjectEquiv`, `pairedGammaComponentsEquiv`, `pairedGammaCoefficientEquiv`, `pairedAVerticesEquiv`, `pairedACoefficientEquiv`, `paired_a_unit_diagonal` | `./check_research_modules.sh --focused ResearchLean/AG/AtlasCoefficientFiber/WitnessThreeCoefficients.lean`、exit0/warning0、30、source `add79e0c1d0b8c3e7de3515177d289ac7545d64c002f65ab87a86ed91f89e8ff`、stdout `86006aaefd791991151fd784dc350945ab232d32a245c6ba9dfa330efe3f495b` |
| `WitnessThreeGeneration.lean` | `pNamedEquiv`, `eta_square`, `epsilon_square` | `./check_research_modules.sh --focused ResearchLean/AG/AtlasCoefficientFiber/WitnessThreeGeneration.lean`、exit0/warning0、3、source `0ce1387b307e46d2b999040a96a5d1eab9645eedd691c57c7ca30e7ec34e7b8e`、stdout `ca1fcb3342042e21a5ac40cfdaf7ffc9c3b2860f8c201a721e79d548c83037e8` |
| `WitnessThreeFiber.lean` | `mixed_name`, `mixed_subsingleton`, `mixed_endpoints_ne`, `gamma_forest`, `B_kernel`, `kappa_zero`, `kappaStar_zero`, `rFamilyEquiv`, `paired_mixed_empty`, `paired_kappa_zero`, `paired_kappaStar_zero`, `paired_tau_zero`, `pairedRFamilyEquiv`, `xChart`, `phiEdgeXEquiv`, `phiEdge_other_empty`, `phi_d0_zero`, `phi_d1_zero`, `phiXCoordinates`, `phi_other_subsingleton`, `phiFamilyPeriod`, `phiFamilyPeriod_bijective`, `rCoordinates`, `r_dimension`, `qCoordinates`, `xChart.congr_simp` | `./check_research_modules.sh --focused ResearchLean/AG/AtlasCoefficientFiber/WitnessThreeFiber.lean`、exit0/warning0、26、source `40141909c17c6773cc59df567dc9269786a7017b785f2ce66ed5cfe5cef4b192`、stdout `d307ef3f865ed786dd8b688daf40f16f94d0ea54bb585c7e4ef8de3fba32b000` |
| `WitnessThreeDiagnostics.lean` | `standardCoordinates`, `secondPeriod`, `secondPeriod_kernel`, `secondPeriod_surjective`, `coarseNamedH2Coordinates`, `coarseNamedH2Coordinates_mk`, `fine_d1_surjective`, `paired_d1_surjective`, `standardH2_subsingleton_of_surjective`, `coarseH2Coordinates`, `pH2Coordinates`, `pH2Coordinates_mk`, `fineH2_subsingleton`, `pairedFineH2_subsingleton`, `pH2_dimension`, `coarseHCycle`, `coarseHClass`, `coarse_h_period`, `coarse_h_nonzero`, `fineHClass`, `fine_h_period`, `fine_h_nonzero`, `paired_h_period`, `paired_h_nonzero` | `./check_research_modules.sh --focused ResearchLean/AG/AtlasCoefficientFiber/WitnessThreeDiagnostics.lean`、exit0/warning0、24、source `0ef8351e4da2841969e38d0617b739e729034bd65076e79693b4e902c01bb4f7`、stdout `2aec3d854002aa161e9d14397dddfda25c932cf7ce39b3818bd07fe3e4ddaaad` |
| `WitnessThreePairedGeneration.lean` | `pairedPNamedComplex`, `pairedFineEdge`, `pairedP1Period`, `paired_evaluation_k`, `pairedP1Period_injective`, `pairedP1Period_surjective`, `pairedP1Equiv`, `paired_evaluation0_surjective`, `pairedP0Equiv`, `pairedP2Equiv`, `pairedPNamedEquiv`, `paired_eta1_values`, `paired_eta0_values`, `paired_eta2_values`, `pairedP_d1_surjective`, `pairedPPeriod`, `pairedPPeriod_kernel`, `pairedPPeriod_surjective`, `pairedPNamedH1Coordinates`, `pairedPH1Coordinates`, `paired_unit_coordinates`, `paired_old_unit_bijective`, `paired_unit_bijective`, `paired_unit_defect` | `./check_research_modules.sh --focused ResearchLean/AG/AtlasCoefficientFiber/WitnessThreePairedGeneration.lean`、exit0/warning0、24、source `24882f263e6c6203bdc39c4cfaf44a4e3b3d50b097462eebce027445a4136fa8`、stdout `7b3dfc62c9b6be6e93870f4bf8f8ead5a0f39f5c49f969135937436096e1c748` |
| `WitnessThreePairedFiber.lean` | `pairedPhiEquiv`, `pairedRCoordinates`, `paired_R_dimension`, `pairedQCoordinates`, `pairedPH2_subsingleton`, `paired_evaluation_coordinates`, `emptyP_standardH1_subsingleton`, `allA_paired_unit_bijective`, `empty_R_subsingleton`, `paired_empty_R_subsingleton`, `allA_R_dimension`, `allA_paired_R_dimension` | `./check_research_modules.sh --focused ResearchLean/AG/AtlasCoefficientFiber/WitnessThreePairedFiber.lean`、exit0/warning0、12、source `12afda884e84ea00dbc523a0d0d2cf6b7fc594ff0a5a5b27d6ca449f1fa4758c`、stdout `d1cccebd4c8f9fef2ebb4cfaae7beb534e1d8e9935f05982129c4bc83f006f7b` |
| `WitnessThreeTransgression.lean` | `vertical_faces_empty`, `correctedW`, `verticalZ`, `horizontalBeta`, `correctedEdge_eq_W`, `correctedW_mixed_zero`, `horizontalBeta_corrects`, `rK`, `tauPRepresentative`, `tauPRepresentative_evaluation`, `tau_rK`, `tau_rK_period`, `tau_nonzero`, `rK_nonzero`, `tau_injective`, `tau_surjective`, `tauEquiv`, `tau_rank`, `verticalZ_single`, `horizontalBeta_single`, `correctedW_face_values`, `kAt`, `verticalKCycle`, `rawRPeriod`, `rawRPeriod_rK`, `rK_spans`, `tau_period`, `rawRCoordinates` | `./check_research_modules.sh --focused ResearchLean/AG/AtlasCoefficientFiber/WitnessThreeTransgression.lean`、exit0/warning0、28、source `bbc567bbdfd5bfa4549aee8abec5a042699c9fff8f84e6f77a11a599298efde9`、stdout `4fe06ac60507995d6f9ebc804173635a44d9b64d60d753c0e01fa862a95d0635` |
| `WitnessThreeCones.lean` | `standard_comparison_bijective`, `standard_comparison2_zero`, `comparisonH2KernelCoordinates`, `totalConeH1Coordinates`, `totalConeH1_dimension`, `cancellation_zero`, `paired_cancellation_zero` | `./check_research_modules.sh --focused ResearchLean/AG/AtlasCoefficientFiber/WitnessThreeCones.lean`、exit0/warning0、7、source `dcac2d4f196e6f5f1242af948935277c5083ecbe9c7db922fe4ec284ef720306`、stdout `5fcceb3098e6e2bfc0405a3cb7b9fa208487cf54f2594ade99a0b2d98b1cdfe9` |
| `WitnessThreeRankTable.lean` | `phi_dimension`, `phi_dimension_sum`, `paired_phi_dimension_sum`, `empty_phi_dimension_sum`, `kappaStar_rank`, `paired_kappaStar_rank`, `paired_tau_rank`, `full_rank_table`, `paired_full_rank_table`, `allA_phi_dimension_sum`, `allA_paired_phi_dimension_sum`, `empty_tau_zero`, `allA_tau_rank`, `allA_paired_unit_defect` | `./check_research_modules.sh --focused ResearchLean/AG/AtlasCoefficientFiber/WitnessThreeRankTable.lean`、exit0/warning0、14、source `2c26d8dde2360bdbf1103b4db086194b93dcf8456fd830d34103277f69641b61`、stdout `4cb650da89da7ca4a0385cb3b8a1a1693173295e2941c42b4fb16fc42bb870cc` |
| `WitnessThreeLaw.lean` | `coarseBlockCoordinates`, `fineBlockCoordinates`, `pairedBlockCoordinates`, `block_map`, `paired_block_map`, `coarseLawCoordinates`, `fineLawCoordinates`, `pairedLawCoordinates`, `law_map`, `paired_law_map`, `law_defect`, `paired_law_defect`, `primitive_law_J`, `paired_primitive_law_J`, `pairedLawCokernelCoordinates`, `lawRCoordinates`, `pairedLawRCoordinates`, `law_R_dimension`, `paired_law_R_dimension`, `lawPH2Coordinates`, `law_tau_coordinates`, `law_tau_bijective`, `law_tau_rank`, `law_kappa_zero`, `law_kappaStar_zero`, `paired_law_kappa_zero`, `paired_law_kappaStar_zero`, `paired_law_tau_zero`, `paired_law_tau_rank`, `lawRK`, `lawRK_period`, `law_tau_RK_period`, `lawRK_nonzero`, `coarseLawH`, `fineLawH`, `pairedLawH`, `pairedLawK`, `law_h_preserved`, `paired_law_h_preserved`, `coarse_law_h_nonzero`, `fine_law_h_nonzero`, `paired_law_h_nonzero`, `pairedLawCokernelCoordinates_mk`, `pairedLawK_period`, `pairedLawK_nonzero`, `law_cancellation_zero`, `paired_law_cancellation_zero`, `lawUnit_bijective_of_components`, `law_unit_bijective`, `paired_law_unit_bijective`, `law_unit_defect`, `paired_law_unit_defect`, `law_kappaStar_rank`, `paired_law_kappaStar_rank`, `lawQCoordinates`, `pairedLawQCoordinates`, `lawTotalConeH1Coordinates`, `law_totalConeH1_dimension`, `pairedLawPH2_subsingleton`, `law_phi_dimension_sum`, `paired_law_phi_dimension_sum`, `law_Q_dimension`, `paired_law_Q_dimension`, `law_full_rank_table`, `paired_law_full_rank_table`, `rawRCoordinates.congr_simp` | `./check_research_modules.sh --focused ResearchLean/AG/AtlasCoefficientFiber/WitnessThreeLaw.lean`、exit0/warning0、66、source `c429f9112a0d4296e047ebf9ff37270aa574d80a0f5c3555e4411c62bb45c372`、stdout `b5b54ff67c638328fb5d7fa67015e69dfa65203837a38cd766da9cc885114da5` |

全275公理はpropext/Classical.choice/Quot.soundのみ。実module inventoryが捕捉した生成`xChart.congr_simp`（Fiber）と`rawRCoordinates.congr_simp`（Law）も個別printへ含めた。validation SHA `9956fa555aa62465708e4c45ebec4652d498fea78f69d0328ecceb6c25749636`。必要root単一dependency cacheのみ生成し、同依存の数学body不変を保持した。十一sourceの最終focusedは現版を検証した。Research full/全module/aggregate/全fileloop/local lakebuild、Formal build/移植、W4/W5、別全目標最終四査読は未実施。標準PRゲート後の受理/CI/実merge/Issue同期は次の記録へ対応させる。

静的本体import方向は228moduleでPASS、Research package方向はPASS。diffcheck/hidden-BiDi/placeholder/privacy/新規禁止語/逆importの新hit0、固定GOAL/design/Formal/保護範囲変更0、十一manifest/aggregate各一回。scan SHA `3411440788a69dd21d8267cd6c880721d3ee931acd1d78c4857e8c6b583b6b8d`。aggregateはelaborateしていない。

## Cycle23 受理・実マージ同期

[PR #5316](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5316)の固定head `155478e8a595a8a396c28eacae0570f49237d6a6`は、初回新規独立数学2/Lean2（GPT6.1Sol High、履歴非継承）の全No major findings、中心0/非中心0、reruns0/2で、W3固定五終了条件をproof-obligation-dischargedとして受理した。[root全13監査](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5316#issuecomment-6074532951)で四票本文・全275個別record・現source/print/log/公理/hash、38現受理source/元owner/最終受理資格、実scan argvと全matchを再統合した。root資格検算SHA `f99abfc0cc5494ae84186f3431ab74bf70cfecb5b7db466c1b54fbde83457433`。全四原raw/evidenceは専用worktreeでbytes不変に保存し、全hashを公開監査に記録。大型全文artifact25件の公開は自動承認レビューに拒否され未実施、安全な代替のsource本文・内部ログを含まない必要受理要約/公開source refs/検証hashだけを投稿・実本文一致確認した。拒否対象を迂回していない。

実merge `38b190e208e9bde67e019a97d75d617c9ac8b8fe`（2026-10-09T04:55:06Z）はGitHub MERGEDと取得origin/mainが一致。[Issue同期](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5290#issuecomment-6074560435)は再取得全文一致、Issue OPENを維持。

root十一focusedと四指定独立single-focusedはexit0/warning0、全275公理はpropext/Classical.choice/Quot.soundのみ。固定head七CI SUCCESS、実Research/Tool step成功、Formal六build/cache/audit stepはSKIPPED。新十一focusedのCI実行、Research full/aggregate/全fileloop/local lakebuild/Formal build/移植は未実施。全GOALはcheckpoint、W4/W5と別whole-finalは未完。停止条件なし。

## Cycle24 selection

実装前の選定。固定W4の同G134原表・全比較・部分支持・全同時要求を一到達点とする。以下五終了条件まで同cycleで構成・補題・接続・検証を反復する。W5と別whole-goal最終四査読は後続であり、completion_candidate:no。

```yaml
ledger_type: target_cycle_result
goal: G-135-aat-atlas-coefficient-fiber
cycle: 24
goal_blob_sha: cd5f3e684b7f390558796797874a1f16b52a6b18
base_oid: 38b190e208e9bde67e019a97d75d617c9ac8b8fe
tracking_issue: 5290
report_path: research/reports/G-135-aat-atlas-coefficient-fiber.md
selection:
  proof_state_ref: Issue5290 Cycle23同期6074560435 / 同report Cycle23受理 / 固定G135 witnesses W4とG134 witnesses W1-W3
  proof_dag_predecessors: [G134同原始rPlus/rMinus/WitnessTwoA-B-C/WitnessThree, C3原局所fiber/Kan, C4原L/ε全像, C5κ/R, C8原診断, C10原錐, C11-C13実Law族, C14原正操作全合成と逆有限和, C15原面複製, C21-C23原全商/成分支持API]
  milestone: GOAL W4の全G134同原比較を原順像・fiber・実診断分解へ全指定評価する
  proof_obligations: [同G134原始表/比較/台/三重出現/Law保持, 三角形ありなしの原Phi区間/原Gamma成分/原Kan二射, 原kappa/R/tau零と係数差/実余核, W2a-c全選択成分と原収縮/二射/全錐保存, 原面複製P=L商/eta面対角/epsilon同型/非零H2差と錐, 全A/空A/二発生Law/同代表/全rank, 全宣言/受理依存/記録/独立PRgate]
  exit_criteria:
    - G134 rPlus/rMinusおよびW2a-b-cとW3面複製の同原chart/edge/face/Option/incidence/支持/Lawをそのまま用い、全三次数原P/eta/epsilon/独立uへ接続する
    - 三角形ありなしのPhi_vを原c区間/他Phi点としてH1零を証明し、Gamma_eは面あり連結/なし二成分と原Kan係数へ同定する。原kappa/literalR/標準tau零から係数欠損と同実T余核0/Q・実Law0/Q2を導き、同G134四diagnostic定理と一致させる
    - W2aのalpha全セル/beta片側c成分、W2bの三原出現と符号、W2c空辺台とcだけ選択を全A/空Aで保持。原Phi/Gamma/Lambda成分/P各生成式/eta-epsilonと同G134逆有限和・収縮を対応させ、実H1保存/a同型/ker tau零と同原総錐全次数零を証明する。P次数別同型を追加仮定しない
    - 同原G134 W3面複製のall-mapped表からL零/P=Cprime/epsilon恒等とLambda_F二lift/eta対角を同定し、同H1保存と元H2余核Q/総錐H2Q・差period非零/同非零h保存を同時接続する。全A/空A/同実二Law/原kappa-R-tau/全rankを評価しH1零欠損から錐全体零を推論しない
    - 全新source/生成補助を個別print/axioms/focused/runtime/report/hashへ照合し、全登録・受理現dependency・scan/import方向・固定入力保持と標準新規数学2Lean2/root全13回帰/CIを通過する
  selection_reason: 未完W4を汎用保存/面複製定理名だけで代替せず、同原台・incidenceからKan係数/fiber分解と実診断・代表・錐まで閉じて全W完了へproof distanceを縮める
  expected_result_type: proof-obligation-discharged
  lean_targets: [PhiInterval, WitnessFourTriangle, WitnessFourCoefficients, WitnessFourSubdivision, WitnessFourDuplication, WitnessFourLaw, WitnessFourDiagnostics]
  risks: [原full induced圏と平行lift, 原Phiの非零d0像, reading合成rPlus同定, c-only部分台, 三重面出現/別名diagonal, 面複製eta2非同型とH1保存, 全A/空A/二label, 標準総錐全次数]
  unchecked: [W4同原局所成分/原Kan全生成, 全指定区間/係数差/代表/診断, 全部分台分割と収縮接続, 同面複製Lambda/差period/錐, 全A/Law/全rank, 独立PRgate]
```

## Cycle24 実装結果・同じ入力の対応

五終了条件の数学的構成とローカル検証を次の同じ経路で閉じた。独立標準PR gateはこれから実行し、現時点のcycle resultはproof-checkpoint（review未完）、completion_candidate:no。GOAL全体はtarget-proof-checkpoint、未完はW4受理・W5・別whole-final。停止条件なし。

1. **同じ原始入力**。G134 `WitnessOne.rPlus/rMinus`、`WitnessTwo.Case/old/edge/fine/comparison`、`WitnessThree.N/fine/comparison`を直接適用する。新しい入力record・期待rank・P同型の入力fieldを加えていない。三角形は同じreading pullbackと新c/e₂/f、細分は原各Occurrence(F,i)の別diagonal/triangle、複製は同じ旧/freshFを保持する。
2. **原三角形のKan・二射・係数差**。`WitnessFourPhi`が全元Φchart/edge/faceとzigzagを生成し、cの異なる端点と唯一の辺から実d0全射→原H¹商零、他chartは点を証明する。面ありΓは同fの独立edgeFace位置1/2で二liftを結び、面なしΓは元categoryの全Homを読み、二つの元頂点へ成分両逆を与える。`WitnessFourCoefficients`の実rightKan座標は面なしe係数ℚ²/η対角、面ありは単一成分である。plusの原η全三次数同型は局所成分から生成し、同じεと独立uの全三成分式を示した。minus P0は元η0の両逆、P1は原εが読む旧e/旧k/fresh e₂全三座標を単射・全射の両方から構成、P2は空fine面の実評価から零。d0=(y−x,0,y−x)、η1=(e,k,e)を同じ原微分・因子化で証明した。
3. **原κ/R/τと実診断・代表**。上の原Φ H¹零から原双対・κ・κ*・literal R・標準τを零とし、実ε H¹の両逆を生成する。その座標で原aはminusのk↦(k,0)、実a余核ℚ、面ありa同型。C8の実核/余核完全列へ適用して同じ独立T欠損をplus(0,0)/minus非空(0,1)、空A(0,0)とした。G134の同e₂だけ1 cocycleを元ε逆で原Pへ移し、実a余核period1・非零、同じkだけ1を原aが保存して非零を証明した。G134の実block四診断のうちplus/minus二本と一致。`WitnessFourLaw`は同G134二Boolラベルを元component図式で実Lawへ集め、元a余核ℚ²、κ/R/τ零、実plusLaw(0,0)/minusLaw(0,2)を原係数寄与から得る。元G134 `plus_law_defect/minus_law_defect`と同じ射・値である。
4. **同じW2a–c・全支持**。`SubdivisionCoefficients`は任意N/e/Aの実Φ/Γ/Λを全元分類する。c台は旧左chart台、b/diagonal/triangleは原edge台なので、台でcだけ残る場合もgamma選択はretained liftへ、Φは実cの区間へ接続する。centerΛはFin1、各元Occurrenceのtriangleが同diagonalとbを結び、元成分からη全三次数の両逆を生成する。`WitnessFourSubdivision`は同G134三Caseへ適用し、原η/ε/独立u全三成分正方形、原a同型・τ核零・全A J零・同総錐全ℤ零・全Lawを得る。同G134 `rs_all/sr_h_all/subset_comparison`を同選択r/s/hに直接接続する。W2a alpha全セル/beta片側c、W2b三出現のs2中心+t0−t1+t2/h1diagonal=−triangle、W2c空edge台/alpha c対/beta旧wのみは元原始表とその同じ選択constructorで保持される。非零k代表・原rの送るfine保持k値は受理済みG134 `WitnessTwoALoop/BLoop`の同じlabel/raw cellであり、今回のactual比較は同`blockR_eq_generated`と`lawR_eq_generated`へ接続する。W2cは同入力の全H¹零。P次数別同型は入力せず、成分から出力する。
5. **同じ面複製・非零H²**。all-mapped原表からL0/1/2零、実P評価は同fine標準複体の全次数同型、その座標でε恒等、元ηと独立u可換。Λ_Fは旧/fresh二元、面係数ℚ²/η2対角。全A H¹ J零と原a両逆/R/κ/τ零の一方、非空Aの同じ原H²比較余核ℚ・総錐H²ℚ、元fresh差period1/nonzeroを接続する。原k cocycleの粗period1/nonzeroと同独立uによるfine非零を同時保持。空A総錐は全ℤ零、fiber錐は全A全ℤ零。全実二LawのH²余核・総錐は選択ラベルを元二Boolへ両逆で戻したℚ²で、重複度を保つ。

### 階数と有限producer

全行は同じ原Φ/κ*/literal R/標準τ/原a/独立T。原全AのΦ Betti和、κ*実像rank、R次元、τ実像rankはすべて0（全Lawもκ*/R/τは0）。表の原a/実Jは次の通り。

| 同原入力 | 非空Aのa欠損/実J | 空Aのa欠損/実J | 同原二Law a欠損/実J | 同原総錐 |
| --- | --- | --- | --- | --- |
| 三角形あり | (0,0)/(0,0) | (0,0)/(0,0) | (0,0)/(0,0) | 元G134正操作の全次数零 |
| 三角形なし | (0,1)/(0,1) | (0,0)/(0,0) | (0,2)/(0,2) | 追加実H¹余核を保持 |
| W2a/b/c辺細分 | 全Case (0,0)/(0,0) | 全Case (0,0)/(0,0) | 全Case (0,0)/(0,0) | 全A/元Law・全ℤ零 |
| W3面複製 | (0,0)/(0,0) | (0,0)/(0,0) | (0,0)/(0,0) | 非空A H²=ℚ、元Law H²=ℚ² |

`WitnessFourRankTable`は全A（minusは空台分岐を含む）と元Lawについて同`primitiveDiagnostic/primitiveLawDiagnostic`を実blockDefectへ接続する。producerは原d0/d1/独立uの有理核像射影とrankであり、期待表を返す別行列は作っていない。Set選択のtransportは非計算的、rank/Bool kernelは有限有理計算である。Set producer全体の`#eval`・外部数値測定を実行したとは主張しない。

### Material premise・proof-use・DAG

| premise/構成 | 分類・出所 | 同じ使用先 |
| --- | --- | --- |
| 原有限Source/readings/K1/Option/incidence/support/Law/adequacy | Wではdischarge-required。元G134入力constructor（同Case含む）を直接再利用、現受理sourceとのbytes同一性を照合 | 全Φ/Γ/Λ、原Kan、二射、実generated比較 |
| 区間唯一辺・異なる両端、点、連結成分、singleΛ | discharge-required。元raw cell分類、元chartEdge/edgeFace射・zigzag・実component quotientで構成 | 原η0/1/2両逆、原d0像、Φ H¹零 |
| d0全射/Φ H¹零/R零 | 一般helperではdirection-hypothesis、各W適用では上記原入力から放電 | actualκ*/R/τ、実ε H¹両逆、C8実欠損式 |
| 原η次数同型/実a同型/ε同型/期待rank | 入力ではなく出力。minus P1は実ε全像の両包含、細分ηは元成分、複製Pはall-mapped原L商 | 同u全三成分square、実商・診断・錐・primitive J |
| 非空A | 値1/非零を要求する方向だけの仮定。原全台セルから証人を生成、空Aを別証明し全Aへ戻す | 同e₂/k/fresh代表と実余核。空Aを捨てない |
| 原G134r/s/hおよび非零代表 | accepted predecessor、同原primitive constructor/選択出力。受理版・現版hashと元label図式を照合 | 同逆有限和収縮、同実u全ℤcone、同kの値 |
| 全二Law | 元`LawValueLabel`とcomponent図式、二Bool両逆・selectedLabel両逆 | 全原a/ε/κ/R/τ/実J/非零H²の元重複度 |

新spineは下表の全244宣言であり、cycle scaffoldは置かない。DAGは原G134入力→原Φ/Γ/Λ/既存右Kan→原η/ε・原u→実Φ商/κ/R/τ→原a・実商/診断/三錐→同全Law/有限producer。一般C1–C20、W1–W3の受理済み補助からの今回の使用は現sourceの実引数・型・proof bodyを読んで照合し、受理済みownerの内部履歴を再認定しない。

<!-- cycle24-generated-evidence -->
### 全spine・個別公理・focused検証

全241source+3生成=244。新十二moduleの239source+3生成に、元ownerの名指しされた二つの代表評価APIを含める。各sourceは最終single-file focused exit0/warning0。個別print・実log・module公理数は標準三公理のみ。owner WitnessOneSubsetのmodule監査26件のうち24件は既存受理宣言、今回spineは追加API二件だけであり、既存24件を今回の新規宣言数へ含めない。元owned runtime inventoryは新spine244と全単射一致する。

| file | namespaceと全spine（全項） | 実focused/count/source SHA/stdout SHA |
| --- | --- | --- |
| `PhiInterval.lean` | `AAT.AG.AtlasCoefficientFiber`: `h1_subsingleton_of_d0_surjective`, `phiD0_surjective_of_interval`, `phiH1_subsingleton_of_interval`, `phiHomology_subsingleton_of_h1_zero`, `kappa_zero_of_phiH1_zero` | `./check_research_modules.sh --focused ResearchLean/AG/AtlasCoefficientFiber/PhiInterval.lean`、exit0/warning0、spine 5 / module監査 5、source `420d40468363aef5ac74a560dd41593cfb1c8220a73c66132ae1147961627b7c`、stdout `6c0d0c925c554027dbee6221946931d19e738e2c3d79ca01787be72ef663bf03` |
| `WitnessFourTriangle.lean` | `AAT.AG.AtlasCoefficientFiber.WitnessFourTriangle`: `plus_vertical_name`, `minus_vertical_name`, `plus_edge_subsingleton`, `minus_edge_subsingleton`, `plus_endpoints_ne`, `minus_endpoints_ne`, `plus_phiH1_zero`, `minus_phiH1_zero`, `plus_kappaStar_zero`, `minus_kappaStar_zero`, `plus_R_zero`, `minus_R_zero`, `plus_tau_zero`, `minus_tau_zero`, `plus_kappa_zero`, `minus_kappa_zero` | `./check_research_modules.sh --focused ResearchLean/AG/AtlasCoefficientFiber/WitnessFourTriangle.lean`、exit0/warning0、spine 16 / module監査 16、source `d5d105cfc89d3f8fdf48d1baeea795ce88037111a1a2c0a4c8c5d3c92c930b96`、stdout `44108ce3a67bfbcbbc7f0c3ad0c6be4d12da9561eb139f111e17de0194e74791` |
| `WitnessFourCoefficients.lean` | `AAT.AG.AtlasCoefficientFiber.WitnessFourCoefficients`: `minus_gamma_hom_eq`, `minusGammaObjectEquiv`, `minusGammaComponentsEquiv`, `minusGammaCoefficientEquiv`, `coarseE`, `minusEVerticesEquiv`, `minusECoefficientEquiv`, `minus_e_unit_diagonal`, `plusGammaChoice`, `plusGammaF`, `plus_gamma_vertex_zigzag`, `plus_gamma_zigzag`, `plus_gamma_components`, `plusEdgeUnitEquiv` | `./check_research_modules.sh --focused ResearchLean/AG/AtlasCoefficientFiber/WitnessFourCoefficients.lean`、exit0/warning0、spine 14 / module監査 14、source `df92bf1c3a9d09360125aee6db491ce3ffdea0632c3826a9a61f8510f82c5ada`、stdout `42bb98bd925a9294afced2d2d92065fdd47d7010e8d743ab47ee00a68c64ba1c` |
| `WitnessFourPhi.lean` | `AAT.AG.AtlasCoefficientFiber.WitnessFourPhi`: `plusOldChart`, `plusC`, `plus_vertex_zigzag`, `plus_face_empty`, `plus_zigzag`, `plus_components`, `minusOldChart`, `minusC`, `minus_vertex_zigzag`, `minus_face_empty`, `minus_zigzag`, `minus_components`, `plus_other_chart_single`, `plus_other_edge_empty`, `minus_other_chart_single`, `minus_other_edge_empty` | `./check_research_modules.sh --focused ResearchLean/AG/AtlasCoefficientFiber/WitnessFourPhi.lean`、exit0/warning0、spine 16 / module監査 16、source `d47bfb94af5267d233ccf8ccee28bf9e6c96faef3226e9e7e5b317947ffa303e`、stdout `951d49f24f47e391fe4b466f7159ecf1759477ce7764480af10d718ae4bda368` |
| `WitnessFourTriangleGeneration.lean` | `AAT.AG.AtlasCoefficientFiber.WitnessFourTriangleGeneration`: `plusEtaEquiv`, `plusEtaEquiv_toHom`, `plusPCoarseEquiv`, `minusEta0Equiv`, `minusEta0Equiv_apply`, `minusFineEdge`, `horizontalName`, `minusP1Period`, `minus_evaluation_c`, `minusP1Period_injective`, `minusP1Period_surjective`, `minusP1Equiv`, `minusP2_zero`, `minus_eta1_values`, `minusP0Equiv`, `minus_d0_values`, `plus_epsilon_square`, `minusP0Equiv.congr_simp` | `./check_research_modules.sh --focused ResearchLean/AG/AtlasCoefficientFiber/WitnessFourTriangleGeneration.lean`、exit0/warning0、spine 18 / module監査 18、source `ee7757cadd55ef6ed3df943f8667f852d4ac1929f280eb5e0a38a310509cb249`、stdout `c440ab59f23e481ad4f56e48113b56c469786deca5cacf8059e18ec2d3917893` |
| `SubdivisionFiber.lean` | `AAT.AG.AtlasCoefficientFiber.SubdivisionFiber`: `vertical_name`, `edge_subsingleton`, `endpoints_ne`, `phiH1_zero`, `kappa_zero`, `kappaStar_zero`, `R_zero`, `tau_zero` | `./check_research_modules.sh --focused ResearchLean/AG/AtlasCoefficientFiber/SubdivisionFiber.lean`、exit0/warning0、spine 8 / module監査 8、source `2bf344e408c348565ebcb4a08ab6a33248239b8a59a3fa5905c3a277410a0cf6`、stdout `2caac72037eb7e973455760c0fbb5c4cad372128e32bb4c66d72570c89cd7b17` |
| `SubdivisionCoefficients.lean` | `AAT.AG.AtlasCoefficientFiber.SubdivisionCoefficients`: `oldChart`, `cEdge`, `vertex_zigzag`, `face_empty`, `zigzag`, `phi_components`, `lambdaEquiv`, `lambda_single`, `selectedEdge`, `gammaB`, `gammaRetained`, `gammaChoice`, `gammaDiagonal`, `gammaTriangle`, `gamma_vertex_zigzag`, `gamma_zigzag`, `gamma_components`, `etaEquiv`, `etaEquiv_toHom`, `gammaB.congr_simp`, `gammaRetained.congr_simp` | `./check_research_modules.sh --focused ResearchLean/AG/AtlasCoefficientFiber/SubdivisionCoefficients.lean`、exit0/warning0、spine 21 / module監査 21、source `72af7316e4604242766b4e7829b5379453932d570749f512be1bd335c6d6be08`、stdout `5e12123a52e0b82ee80051e3215a57481e7a97b44b4a9fecca7fbbf223308dd4` |
| `WitnessFourSubdivision.lean` | `AAT.AG.AtlasCoefficientFiber.WitnessFourSubdivision`: `path`, `path_comparison`, `etaEquiv`, `etaEquiv_toHom`, `pOriginalEquiv`, `eta_square`, `phiH1_zero`, `kappa_zero`, `kappaStar_zero`, `R_zero`, `tau_zero`, `unit_bijective`, `defect_zero`, `tauKernel_zero`, `totalCone_zero`, `contraction_factorization`, `contraction_rs`, `lawUnitEquiv`, `lawTotalCone_zero`, `epsilon_square`, `law_unit_bijective`, `law_unit_defect`, `law_R_zero`, `law_tau_zero`, `law_kappa_zero`, `law_kappaStar_zero`, `contraction_sr_h` | `./check_research_modules.sh --focused ResearchLean/AG/AtlasCoefficientFiber/WitnessFourSubdivision.lean`、exit0/warning0、spine 27 / module監査 27、source `da9ab107ff396b64e8fbdfc49fe30a1ab631ac7d05d7d583d176c45ab6fedd28`、stdout `22fc3cd2fa281a8f7877656dcfcd36ff79ea9b432167d0da9af3a5e7f547ab8d` |
| `WitnessFourDiagnostics.lean` | `AAT.AG.AtlasCoefficientFiber.WitnessFourDiagnostics`: `defect_eq_unit_of_R_zero`, `plus_unit_bijective`, `plus_unit_defect`, `plus_defect`, `minusEvaluationEquiv`, `minusEvaluationEquiv_apply`, `coarseCoordinates`, `minusFineCoordinates`, `minusPCoordinates`, `minus_direct_old`, `minus_unit_coordinates`, `minus_unit_injective`, `minusUnitCokernelEquiv`, `minus_unit_defect`, `minus_defect`, `plus_block_agrees`, `minus_block_agrees`, `minus_empty_defect`, `minus_empty_unit_defect`, `allA_minus_defect`, `minusUnitCokernelEquiv_mk`, `minusExtraClass`, `minus_extra_period`, `minusPExtraClass`, `minus_extra_cokernel_period`, `minus_extra_cokernel_nonzero`, `oldLoopClass`, `old_loop_period`, `minus_mapped_loop_nonzero` | `./check_research_modules.sh --focused ResearchLean/AG/AtlasCoefficientFiber/WitnessFourDiagnostics.lean`、exit0/warning0、spine 29 / module監査 29、source `74a7798c44a61657731cd2736124c9eef6a0306ae7712b0ca11be8ad7e05ca7f`、stdout `a1ba4b9e5f3a7096a485ff402e47836c88e3a3543eba8113b4d9d3838bd1da0d` |
| `WitnessFourDuplication.lean` | `AAT.AG.AtlasCoefficientFiber.WitnessFourDuplication`: `face_selected`, `lambdaEquiv`, `faceCoefficientEquiv`, `eta_face_diagonal`, `L0_zero`, `L1_zero`, `L2_zero`, `pFineIso`, `pFineIso_hom`, `unit_square`, `unitEquiv`, `unitEquiv_apply`, `defect_zero`, `phiH1_zero`, `kappa_zero`, `kappaStar_zero`, `R_zero`, `tau_zero`, `h2CokernelEquiv`, `totalConeH2Equiv`, `freshClass`, `fresh_period`, `fresh_nonzero`, `totalConeH2_dimension`, `empty_totalCone_zero`, `fiberCone_zero`, `lawUnitEquiv`, `law_defect_zero`, `law_R_zero`, `law_tau_zero`, `lawTotalH2Equiv`, `lawH2CokernelEquiv`, `selectedLabelEquiv`, `selectedCoefficientEquiv`, `lawTotalH2PairEquiv`, `lawH2CokernelPairEquiv`, `lawTotalH2_dimension`, `oldHPeriod`, `oldHClass`, `old_h_period`, `old_h_nonzero`, `fineHClass`, `fine_h_nonzero`, `eta2_values`, `epsilon_coordinates_identity`, `law_kappa_zero`, `law_kappaStar_zero` | `./check_research_modules.sh --focused ResearchLean/AG/AtlasCoefficientFiber/WitnessFourDuplication.lean`、exit0/warning0、spine 47 / module監査 47、source `be9f694ac8c6586bb25a3ae79b6d4c7302ef33fed4ac65318f6c7b40708e288b`、stdout `986538354b91cacc3fec3dcb3640eb0f9c5452a0ba7c423b0934bec785b19504` |
| `WitnessFourLaw.lean` | `AAT.AG.AtlasCoefficientFiber.WitnessFourLaw`: `labels_card`, `plus_R_zero`, `minus_R_zero`, `plus_tau_zero`, `minus_tau_zero`, `plusUnitEquiv`, `plusUnitEquiv_apply`, `plus_unit_defect`, `minusEvaluationEquiv`, `minusEvaluationEquiv_apply`, `minus_unit_injective`, `minusUnitCokernelStandardEquiv`, `minusUnitCokernelEquiv`, `minus_unit_defect`, `plus_defect`, `minus_defect`, `plus_kappa_zero`, `plus_kappaStar_zero`, `minus_kappa_zero`, `minus_kappaStar_zero` | `./check_research_modules.sh --focused ResearchLean/AG/AtlasCoefficientFiber/WitnessFourLaw.lean`、exit0/warning0、spine 20 / module監査 20、source `0c709af6f129b8b8f78078724e995a62f1805a6e5a74b1fd066a7854c451f358`、stdout `522f0f92cd72e469f03201bce15b3dc20f68ca9266383a83722d2715f5327b7f` |
| `WitnessFourRankTable.lean` | `AAT.AG.AtlasCoefficientFiber.WitnessFourRankTable`: `fiber_zero_ranks`, `law_zero_ranks`, `plus_fiber_ranks`, `minus_fiber_ranks`, `subdivision_fiber_ranks`, `duplication_fiber_ranks`, `plus_law_fiber_ranks`, `minus_law_fiber_ranks`, `subdivision_law_fiber_ranks`, `duplication_law_fiber_ranks`, `allA_minus_unit_defect`, `duplication_unit_defect`, `duplication_law_unit_defect`, `plus_primitive_J`, `minus_primitive_J`, `duplication_primitive_J`, `subdivision_primitive_J`, `plus_primitive_LawJ`, `minus_primitive_LawJ`, `duplication_primitive_LawJ`, `subdivision_primitive_LawJ` | `./check_research_modules.sh --focused ResearchLean/AG/AtlasCoefficientFiber/WitnessFourRankTable.lean`、exit0/warning0、spine 21 / module監査 21、source `16d67b79a8906ff98930948f505f6dea52b9cd4606e24e889718370cf0e4c8d6`、stdout `cce9fa36b89c0e3e313d1b2850741ce9ac12c2b45baa81259d8284e636028738` |
| `WitnessOneSubset.lean` | `AAT.AG.FaceRelationSubdivision.WitnessOne`: `oldSubsetPeriod_mk`, `minusSubsetPeriod_mk` | `./check_research_modules.sh --focused ResearchLean/AG/FaceRelationSubdivision/WitnessOneSubset.lean`、exit0/warning0、spine 2 / module監査 26、source `a9000928e721cb31e8abe8c5880877d501a8e1dd8b2ccd02811c418be826e2cd`、stdout `298a7256ac527b3ceb83bcd5b15993c8adead740217ea0b653bb2293cd95a6b3` |

validation SHA `7202158a69c8dc8955276cd7c91f2486b1c9aa2ed30ffbb2556ad1ee80c30efc`、runtime SHA `d2481fa3c27601847a45c7c6ed05b7532bf0557bc1a31d4f5871359fddac1cff`。生成3はminusP0Equiv.congr_simpとgammaB/gammaRetained.congr_simpを個別printへ含めた。修正四fileと元owner一fileを必要focusedで検証し、数学bodyを変えない他八fileは同source版の初回focusedログを再照合した。必要root単一dependency cacheと同target owned inventoryのみ実行し、Research full/全module/aggregate/全fileloop/local lakebuild/Formal build/移植は未実施。Research-proved候補、Formal unported。正式再実行/実CI/merge/Issue同期は後続gateで記録する。

### 現受理predecessorの版照合

以下42owner sourceは使用箇所・適用引数を確認した。41ownerは受理版と現bytesが同じ。WitnessOneSubsetには今回の二APIと個別printだけを追加し、既存定義・statement・proof bodyは受理版とbytes同一である。追加二APIは本PRの新spine・正式再査読対象として扱う。原W2a/b/c表はCase→old/edge/fine/comparison/同selected constructorを経て使用する。宣言欄がimport/入力定義のownerを示すものも、原表のprovenanceとして閉じる。DAG追跡の内部受理履歴再認定は行わない。

| 現owner | 使用宣言/API | 受理PR/review/head | 現/受理SHA（追加API ownerは区別） |
| --- | --- | --- | --- |
| `FaceRelationSubdivision/WitnessOneInput.lean` | `Source`, `qc`, `qf`, `laws`, `coarseAdequate`, `fineAdequate`, `coarser`, `labelEquiv`, `nerve`, `N`, `plus`, `minus`, `chart_full`, `plus_chart_full`, `minus_chart_full`, `edge_full`, `face_full`, `plus_edge_full`, `plus_face_full`, `minus_edge_full`, `d0_apply` | [PR5287](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5287#issuecomment-6030258596) / `0134623422114ae39f989d591cb167c6176aae3e` | `53452d383799618adfd17ebf948ac09634efd3d578fd9bcd824f835835a72ba1` |
| `FaceRelationSubdivision/WitnessOneComparison.lean` | `rPlus`, `rMinus`, `rPlus_edge_old`, `rPlus_edge_c`, `rPlus_edge_e2`, `rMinus_edge`, `plusBlockHom`, `minusBlockHom`, `plusLawHom`, `minusLawHom`, `minusNamedHom` | [PR5287](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5287#issuecomment-6030258596) / `0134623422114ae39f989d591cb167c6176aae3e` | `17458d7bc4805cfddad36c281a2112233eb173f030eef7d6e4e5f157122ff1fb` |
| `FaceRelationSubdivision/WitnessOneSubset.lean` | `fineSubset`, `minusSubsetHom`, `oldSubsetEquiv`, `minusSubsetEquiv`, `minus_subset_square`, `oldSubsetPeriod`, `minusSubsetPeriod`, `minus_subset_injection`, `emptySubsetEquiv`, `minus_empty_identity` | [PR5287](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5287#issuecomment-6030258596) / `0134623422114ae39f989d591cb167c6176aae3e` | 現 `a9000928e721cb31e8abe8c5880877d501a8e1dd8b2ccd02811c418be826e2cd` / 受理 `3685db6fe7a65bf0b583a127ff8416e347007cdb5c1ff5a411777f78d51b4c78`（既存24宣言不変、二API追加） |
| `FaceRelationSubdivision/WitnessOnePeriods.lean` | `oldLoopOnly`, `minusSection`, `oldPeriod_loop`, `minusPeriod_section`, `oldH1Period_mk`, `minusH1Period_mk` | [PR5287](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5287#issuecomment-6030258596) / `0134623422114ae39f989d591cb167c6176aae3e` | `e4323bc4049f566de85b7fd7e6ff2793dc25ca0c30f676c9190508f95ee7e687` |
| `FaceRelationSubdivision/WitnessOnePeriodMaps.lean` | 同原入力/dispatch/import owner | [PR5287](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5287#issuecomment-6030258596) / `0134623422114ae39f989d591cb167c6176aae3e` | `5ca30a309100032a885b5301ad7c16f5afbb34af8905845056f724d877d09b42` |
| `FaceRelationSubdivision/WitnessOneCokernel.lean` | `periodInjection`, `injectionCokernel`, `minus_extra_cokernel_nonzero` | [PR5287](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5287#issuecomment-6030258596) / `0134623422114ae39f989d591cb167c6176aae3e` | `cadd62936450ebc8aa182459de5d9ac19f588a6669dc8b87089ed7d43439d732` |
| `FaceRelationSubdivision/WitnessOneDiagnostics.lean` | `labelPairEquiv`, `minusLawCokernel`, `plus_block_defect`, `minus_block_defect` | [PR5287](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5287#issuecomment-6030258596) / `0134623422114ae39f989d591cb167c6176aae3e` | `fc3153e09a68e103c304aeda3a277eecc8bce26ffb3ea269d7179eaf23bb354f` |
| `FaceRelationSubdivision/WitnessTwoAInput.lean` | `N`, `fine`, `comparison` | [PR5287](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5287#issuecomment-6030258596) / `0134623422114ae39f989d591cb167c6176aae3e` | `8b1d425b755d3066d5514e923e607f78a208ea22455d6eae8ecf72d736246dcc` |
| `FaceRelationSubdivision/WitnessTwoALoop.lean` | `oldLoopClass` | [PR5287](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5287#issuecomment-6030258596) / `0134623422114ae39f989d591cb167c6176aae3e` | `28426027c31dd15049d5c884fa6508e5dbbd3014f6beb461d98ea129657378f3` |
| `FaceRelationSubdivision/WitnessTwoBInput.lean` | `nerve`, `N`, `fine`, `comparison`, `chart_full`, `d0_apply` | [PR5287](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5287#issuecomment-6030258596) / `0134623422114ae39f989d591cb167c6176aae3e` | `4b6bdc381508fafdd8e62c4b5fd8a508226685619b372c8a6630295a9464e1b7` |
| `FaceRelationSubdivision/WitnessTwoBLoop.lean` | `oldLoopClass` | [PR5287](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5287#issuecomment-6030258596) / `0134623422114ae39f989d591cb167c6176aae3e` | `ab177628c77402f63de842948f1222f2305e159a325e179cbff06d412502c504` |
| `FaceRelationSubdivision/WitnessTwoCInput.lean` | `nerve`, `N`, `fine`, `comparison`, `contraction`, `law_comparison` | [PR5287](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5287#issuecomment-6030258596) / `0134623422114ae39f989d591cb167c6176aae3e` | `0473a7fd7e3185df850f6575cc185bcb2038f62262a27248cee1cebb51976011` |
| `FaceRelationSubdivision/WitnessTwoDiagnostics.lean` | `old`, `edge`, `fine`, `comparison`, `contraction`, `rs_all`, `sr_h_all`, `subset_comparison`, `law_comparison`, `law_defect_zero` | [PR5287](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5287#issuecomment-6030258596) / `0134623422114ae39f989d591cb167c6176aae3e` | `2746a8b1dc394d13f3f4ac45f8eb3237edafb14e62a19a8369f4ab5c526982d0` |
| `FaceRelationSubdivision/WitnessThreeInput.lean` | `N`, `fine`, `comparison`, `chart_full`, `edge_full`, `face_full`, `fine_face_full`, `d0_apply` | [PR5287](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5287#issuecomment-6030258596) / `0134623422114ae39f989d591cb167c6176aae3e` | `9d3124d4e0afd5fc5cabf0a82fbac1078b5573453394860f48a1882c24e0af4d` |
| `FaceRelationSubdivision/WitnessThreePeriods.lean` | `loopOnly`, `namedH1Equiv`, `namedH1Equiv_mk` | [PR5287](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5287#issuecomment-6030258596) / `0134623422114ae39f989d591cb167c6176aae3e` | `72e8e663a519d590a469bdfc9b48e3e26cfa4689e0ec5f8bb0ffee34fcad1f9a` |
| `FaceRelationSubdivision/WitnessThreeDiagnostics.lean` | `face_selected`, `labelPairEquiv`, `lawH2CokernelPairEquiv` | [PR5287](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5287#issuecomment-6030258596) / `0134623422114ae39f989d591cb167c6176aae3e` | `7110da57ca54de0a526d5278f085bee34cd728d85d163174d219366871e399a0` |
| `AtlasCoefficientFiber/PositiveOperation.lean` | `coarser`, `comparison` | [PR5305](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5305#issuecomment-6059890330) / `9cdf674adb720d23ade0f8e914426df8b7e2ca48` | `4b484f43de0565ea875247d096546e40c818e49cb57d23272d1be029cf5562ab` |
| `AtlasCoefficientFiber/PositiveOperationPath.lean` | `coarser`, `comparison`, `single`, `single_comparison` | [PR5305](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5305#issuecomment-6059890330) / `9cdf674adb720d23ade0f8e914426df8b7e2ca48` | `13329fb68579ed44d017926065565b7c7f2323be6bb951835da2b102ba275f6e` |
| `AtlasCoefficientFiber/PositivePreservation.lean` | `lawDefect_zero` | [PR5305](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5305#issuecomment-6059890330) / `9cdf674adb720d23ade0f8e914426df8b7e2ca48` | `02c8c0a3cdb3378c26aea8cfa8157d08d09012275e2c81ddcaf19d20ce4eb5ab` |
| `AtlasCoefficientFiber/PositiveCoefficientPreservation.lean` | `unitEquiv`, `unitEquiv_apply`, `totalCone_isZero`, `lawUnitEquiv`, `lawUnitEquiv_apply`, `lawTotalCone_isZero` | [PR5305](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5305#issuecomment-6059890330) / `9cdf674adb720d23ade0f8e914426df8b7e2ca48` | `1dbeb937bfdba21d227381a0c8a7e94a6aa4379720f62e53a49f25eff795a3eb` |
| `AtlasCoefficientFiber/FaceCloneComparison.lean` | `fineStandardIso`, `oldH1Equiv`, `defect_zero` | [PR5306](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5306#issuecomment-6060895737) / `180477fd314e416689beed56f3609edfc91403fd` | `d5403b62bf9dda7cb6a70014f7d3a1b82b5e61920cbcf1a3059c98fc2e7aadde` |
| `AtlasCoefficientFiber/FaceCloneCoefficient.lean` | `L0_zero`, `L1_zero`, `L2_zero`, `coefficientStandardIso`, `coefficientStandardIso_hom`, `unit_standard_square`, `unitEquiv`, `unitEquiv_apply`, `phiH1_zero`, `R_zero`, `tau_zero`, `fiberCone_zero` | [PR5306](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5306#issuecomment-6060895737) / `180477fd314e416689beed56f3609edfc91403fd` | `740c9f8b775c74a6231dbf72123b546566832c6a468be6c6dd6f2e9ba8095abe` |
| `AtlasCoefficientFiber/FaceCloneHomology.lean` | `nativeH2CokernelEquiv`, `nativeFreshCokernelClass`, `nativeFreshCokernelClass_value`, `nativeFreshCokernelClass_nonzero`, `totalConeH2Equiv`, `absent_totalCone_zero` | [PR5306](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5306#issuecomment-6060895737) / `180477fd314e416689beed56f3609edfc91403fd` | `005a470d54a7565d189caefe286e9cd9105c309e883848fc5cf4773f57405df5` |
| `AtlasCoefficientFiber/FaceCloneLaw.lean` | `lawUnitEquiv`, `lawUnitEquiv_apply`, `lawDefect_zero`, `lawR_zero`, `lawTau_zero`, `SelectedLabel`, `lawTotalH2Equiv`, `lawH2CokernelEquiv` | [PR5306](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5306#issuecomment-6060895737) / `180477fd314e416689beed56f3609edfc91403fd` | `6d1dfd8d0f8e6be7e5d788c2666a816792582f03d737f90e51e1b3300889bc10` |
| `AtlasCoefficientFiber/WitnessOneCoefficients.lean` | `componentsEquivOfHomEq` | [PR5314](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5314#issuecomment-6072664284) / `fecb994402b579b6a0fe15190ef10b4752a7c44b` | `36d4e207e595c51c9a06c39ce9c73c14be80b7079bfdf995cc7a048306a6e4ea` |
| `AtlasCoefficientFiber/WitnessFullSupport.lean` | `fine_nonempty`, `labelEquiv`, `labels_card` | [PR5314](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5314#issuecomment-6072664284) / `fecb994402b579b6a0fe15190ef10b4752a7c44b` | `95b4dca558735ab40bc172f8ff648884296f3c7bcf086d4d44a1560bcb107b1d` |
| `AtlasCoefficientFiber/FinitePreservationDecision.lean` | `primitiveDiagnostic`, `primitiveDiagnostic_eq_blockDefect`, `primitiveLawDiagnostic`, `primitiveLawDiagnostic_eq_blockDefect` | [PR5313](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5313#issuecomment-6072107116) / `fc95be6c3a948aa993a0e6af15f6c44546ce90b3` | `64815b21177bdef5df81a15df88a6aa783632667047e6ee7483b1b64d6e18ef8` |
| `AtlasCoefficientFiber/LocalPreservation.lean` | `localUnitEquiv`, `unitH1_bijective_of_local`, `connectingTau_injective_of_phiH1_zero` | [PR5300](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5300#issuecomment-6053115567) / `70909cc76c24e689fe03efe4340afc2bbf164969` | `29c5ab27b2e133dd2d1415612a229c3505c685542726a98ec25c8adc399f1061` |
| `AtlasCoefficientFiber/LocalCoefficientSingle.lean` | `gammaCoefficientConstant_apply`, `lambdaCoefficientConstant_apply`, `chartCoefficientConstant_bijective`, `edgeCoefficientConstant_bijective` | [PR5300](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5300#issuecomment-6053115567) / `70909cc76c24e689fe03efe4340afc2bbf164969` | `6520da925b2d8b2cf009869213b02c9fc780ec2557cd4573b62144f730e92505` |
| `AtlasCoefficientFiber/GammaComma.lean` | `gammaCoefficientEquiv` | [PR5296](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5296#issuecomment-6049620284) / `61659d7586accb379f03883d3722c5d6a622fad2` | `e10ca3baaf4768f6fbdf042321459b6fb4d9fa24e3d9e25afc61032004ca8a13` |
| `AtlasCoefficientFiber/LawHomologyCoordinates.lean` | `lawCoarseHomologyEquiv`, `lawFineHomologyEquiv`, `lawUnit_homology_component`, `lawEvaluation_homology_component`, `lawUnitH1`, `lawDirectH1`, `lawDirectH1_factor` | [PR5302](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5302#issuecomment-6054697310) / `7f20e6aaaae8c51298b32d955ca16a6b0076b84a` | `6052b12559e0f2fe036036ff60349e451e9fbb948da10582236aee718e3ae68c` |
| `AtlasCoefficientFiber/LawFiberSequence.lean` | `lawPushforwardHomologyEquiv`, `lawKappa`, `lawKappaStar`, `lawR`, `lawRFamilyEquiv`, `lawConnectingTau`, `lawEvaluationH1`, `lawKappa_apply`, `lawKappaStar_apply` | [PR5304](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5304#issuecomment-6058853944) / `657e562eaa154e94155681e07d3c218e6998375b` | `2a838970a53412557e5ca9bc90e9296fd5547297076392a2bcd2bd37b5b6ec55` |
| `AtlasCoefficientFiber/LawDefectDiagnostics.lean` | `lawOldCokernelStandardEquiv`, `coefficient_cokernel_sum`, `lawCoefficientBlockDefect_sum` | [PR5304](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5304#issuecomment-6058853944) / `657e562eaa154e94155681e07d3c218e6998375b` | `2269b369f00de215a3208021c05df0c77a476225e8fd6233e331759ae946e8d0` |
| `AtlasCoefficientFiber/EvaluationAnnihilator.lean` | `restriction1_zero_iff`, `evaluation1_preimage_of_restriction_zero` | [PR5295](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5295#issuecomment-6047664301) / `927f6be84e525e853df340d1ad7c45f5c9f47358` | `e240cdad380f4a7ecfd3c422183eab5b6197ad7443faf85ad7fec7cc1fea061b` |
| `AtlasCoefficientFiber/WitnessCommon.lean` | `qc`, `qf`, `laws` | [PR5297](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5297#issuecomment-6050868943) / `160a3087d20d2e9cf22de758359acb5df7ec2ecd` | `f4f46b1ae32e0462e6ed1785f88df7a31ad6ed18607169c6738b3c652bfdd56b` |
| `FaceRelationSubdivision/FullSupportSubsetComparison.lean` | `fullSelected`, `fullSubsetNamedEquiv` | [PR5287](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5287#issuecomment-6030258596) / `0134623422114ae39f989d591cb167c6176aae3e` | `893423de007db0a677b7f933408bab4041ee9f45011f7042f1c79de8d98e15b0` |
| `AtlasDefectComposition/LinearConjugation.lean` | `cokernelEquiv` | [PR5287](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5287#issuecomment-6030258596) / `0134623422114ae39f989d591cb167c6176aae3e` | `2fb0f6f319a8dcdf8848f4dfd7672371a930b41aa96919888df2b4a273b40fbb` |
| `AtlasCoefficientFiber/LocalFiber.lean` | `PhiChart`, `PhiEdge`, `GammaVertex`, `GammaInc`, `LambdaFace` | [PR5303](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5303#issuecomment-6057242603) / `70633bfc653fe823fbdbbbcec8b1d6fc12a5bb5b` | `cfc7d3a3d44a78879840daae8cf5a846510813156598c1006e9686c1b68013a4` |
| `AtlasCoefficientFiber/WitnessThreeInput.lean` | `Nc`, `Nf`, `M` | [PR5312](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5312#issuecomment-6071529511) / `a90fee53a0ee64caea90acb1073d43b776521cd3` | `68f89f83e088f3d4e2f55bb7e08fe6be339e8751ade0ffdc2d4f3147282b34c8` |
| `AtlasCoefficientFiber/MappedEvaluation.lean` | `evaluation2Equiv` | [PR5306](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5306#issuecomment-6060895737) / `84de18ff5245f3716b5d30cb2f596446ddac39f0` | `5cf4664d5b34544d033f85b8cc95ef675043de72717f7d524aed2b170f195e7b` |
| `AtlasCoefficientFiber/ConeSequences.lean` | `totalCone` | [PR5301](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5301#issuecomment-6053510508) / `cc62fac23e82e41728dd8188967c73bde36b1516` | `28b6b74c831faca3f5be94d79fade13316513d2e833c1f9d41950921ac6da654` |
| `AtlasCoefficientFiber/DefectDiagnostics.lean` | `coefficient_zeroDefect_iff` | [PR5299](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5299#issuecomment-6052624414) / `4bdc59ea609b94fd087acad580666223c073a502` | `bd3d93c50341909af0ad968c8dec37ae7a591bfeaf1500e9a2a583ac67977504` |

predecessor資格metadata SHA `e88ba3908d8bb1aa2e59305ec3990fd43615be7b7d17e78d1a65fe96530f6959`。元ownerの追加二APIだけを除くsource bytes一致を機械照合した。正式再実行の新規四lane/root全13回帰と同head実CI・merge・Issue同期は未完であり、未実施を受理済みと表示しない。

共通scanは新hit0、固定GOAL/design/Formal変更0、十二新manifest/aggregate各一回。元ownerは既存登録をそのまま使用する。scan metadataは同最終source/report版で再生成し正式gateに固定する。aggregateはelaborateしていない。

### Cycle24 初回査読・公開API修正

PR5317初回固定head 15b9cab01d21e2652c8c9be9023a2a022ab27c34の標準ゲートは、[初回統合](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5317#issuecomment-6075573274)のNeeds changes。数学A/LeanAの非中心API指摘、数学B/LeanBのNo major findings、中心0/選定W4数学未確認0を記録した。全242初回個別宣言/42依存/全scanと四票のroot資格検算SHA e23dd67b3a92eeafab8ae5a986141570143bcce8b3e97a697a2feaf6715d1a40を保存した。

MA-N1/LA1は元EdgeSubdivision edgeImage/faceImage/faceEdge1の公開評価APIへ、MA-N2/LA1は元WitnessOneSubsetに名指しされたoldSubsetPeriod_mk/minusSubsetPeriod_mkを追加して原代表へ、LA1のcloneはfullSelected_valへ接続した。原G134入力・期待式・全statement・全選定五条件を変えていない。lambdaEquivのdef本体内の左右逆証明を修正したため直接対応資格外であり、修正最終headに対する履歴非継承の新規数学2/Lean2正式再実行1/2へ進む。root単独で解消判定・acceptance合格を生成しない。


## Cycle24 受理・merge同期

[PR #5317](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5317)固定head `364671473ba1ea5db53cf3d668c74cea42f0e6d1`を新規正式再実行数学2/Lean2（履歴非継承GPT6.1Sol High）の全No major findings、中心0/非中心0、reruns1/2で受理。[root全13監査](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5317#issuecomment-6076267444)は全244個別source/print/log/公理と42現受理source・各票190 API records・全scan出力を実再計算して五終了条件をproof-obligation-discharged / approveとした。root資格検算SHA `ef78639f5151aad0309ecea4a36dafd10a4fc569ebfd103bde2c98fac7759548`。生成3kernelbodyは未観測、owner/runtime/個別公理を区別した。全原票/hashを専用worktreeに保存。

実merge `addd0a4f647d2d2e6cb48e4f9c6ba152e7008ed1`（2026-10-09T07:14:06Z）はGitHub MERGEDと取得origin/mainが一致。[Issue同期](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5290#issuecomment-6076292033)を再取得して全文一致・OPENを確認。全244は標準公理のみ、root13/四指定focusedはexit0/warning0、七CI SUCCESS。Research integrity実step成功、Formal六build/cache/audit stepはSKIPPED。新13focusedのCI実行/Research full/aggregate/全fileloop/local lakebuild/Formal移植は未実施。全GOALはcheckpoint、W5/別whole-final未完、停止条件なし。

## Cycle25 selection

実装前に固定。到達点は固定W5全要求と全固定targetのcompletion候補対応。五終了条件が揃うまで同cycleで構成・補題・接続・検証を反復し、一file完成では分割しない。全数学義務が閉じた時点だけcompletion_candidate yesとし、標準PR gateの後に別新規whole-final四査読へ進む。

```yaml
ledger_type: target_cycle_result
goal: G-135-aat-atlas-coefficient-fiber
cycle: 25
goal_blob_sha: cd5f3e684b7f390558796797874a1f16b52a6b18
base_oid: addd0a4f647d2d2e6cb48e4f9c6ba152e7008ed1
tracking_issue: 5290
report_path: research/reports/G-135-aat-atlas-coefficient-fiber.md
selection:
  proof_state_ref: Issue5290 C24同期6076292033 / 同report C24受理 / 固定W5原始表
  proof_dag_predecessors: [C1-C20一般T0-A-E, C21-C24全W1-W4, WitnessCommon原Source-readings-Law, 原Kan二射, 原rawKappa-全Phi双対, 原Law族-全rank]
  milestone: 固定W5混在適合の全要求を原始表から閉じ全固定target完了候補へ接続する
  proof_obligations: [原W5表-支持-Option-独立比較, 全原Phi-Gamma-Lambda-Kan二射, 原D-B-κ同型とliteralR-τ, 全H1商-実比較-非零保存と誤列反証, 全A-空A-二Law-全rank-累積記録]
  exit_criteria:
    - 原Source Bool2・qc=fst/qf=id・真のreading細分と同非定数Law二発生labelを用い、粗一chartUnit二loopFin2面Empty、細同chart三loopFin3一faceUnit m=(k,e,e)の位置と符号を保持。e/hは同名・k/mはnone、全台から全Aと原三次数uを生成する
    - 同原Phi_cをchart+k circle・d0/d1零・実H1/chainH1商Q、Gamma_eを一頂点一loop m・二edgeFace位置別射・B0/kerBQ、Gamma_hを点、Lambdaを粗面なしとして同定する。全元comma成分から実rightKan Pとeta全三次数両逆を生成し、原P↔粗named complex・eta座標恒等・epsilonと独立uの全成分squareを示す
    - 同m閉路のDはk単独chain。全A actualrawκとκ/κ*の両逆、κ(m)=[k]と非零・literalR0/標準τ0を証明。非空Phi和1/κ*rank1・空A全0、同原二Law和2/κ*rank2/R0/τ0を評価しW3のκ0/τrank1と区別する
    - 同原粗細H1の全商をe/h Q2へ両逆、細d1z=z(k)とcycle iff k0、原T全元恒等・a同型/J00、e/h各actualclass period1/nonzero保存、actualP H2零を証明。任意g細H1→wholePhiと任意t wholePhi→actualP H2についてactualepsilon-gとg-tの両Exactは同時不能と同原非零Phi k類で証明する
    - 空Aも同原商で零、同原全Law各labelの全射/三次数/κ-τ/代表/重複度/producer/rankへ接続する。全新宣言-生成-owner-body-print-公理-focused-runtime-hash-登録-scan-現受理依存とreport全固定T0-A-E-W対応を同期し、標準新規四査読/root13/CI後同headfinalpacketと別新規whole-final四査読を行う
  selection_reason: 最後の固定W5を弱いforest/pure特殊値で代替せず同原混在閉路のκと全Phi誤列の具体反証を構成して全目標完了監査へ進む
  expected_result_type: proof-obligation-discharged
  lean_targets: [WitnessFiveInput, WitnessFiveComparison, WitnessFiveCoefficients, WitnessFiveGeneration, WitnessFiveFiber, WitnessFiveKappa, WitnessFiveDiagnostics, WitnessFiveLaw, WitnessFiveRankTable]
  risks: [同e二位置の射保持, actualrawDの全元両逆, 全A空A, 全Phi誤列と正しいRの区別, actualPと独立u, 同e-h非零代表, 原Law重複度, 全固定target累積coverage]
  unchecked: [上記全W5数学義務, 新宣言公理と検証, 全累積最新対応, 標準PRgate, 別whole-final]
```

## Cycle25 実装結果：同原W5の混在適合と誤列の具体反証

原入力は粗一chart/二loop e,h/面なし、細同chart/三loop e,h,k/原m=(k,e,e)。原Source/readings/LawはWitnessCommonのBool²/fst/id、非定数Lawと発生Bool二labelを用いる。e,hは同名、k,mはnone、全台を保持する。mの二つのe位置を同セルとして保ちながら別incidence射として証明する。Pは元carrierに沿う右Kanのままである。

| 五条件 | 同じ原始入力からの証拠と使用経路 |
| --- | --- |
| 1 原始表と実比較 | `WitnessFiveInput.Nc/Nf/M` は原支持・端点・三位置・符号付き零和を構成。`edgeMap_e/h/k`、`faceMap_apply`、`fine_faceEdge0/1/2` は独立Mの原データ。WitnessCommon `coarser/not_coarser/adequate_coarse/adequate_fine/law_nonconstant/labels_ne` とWitnessFullSupport `labelEquiv/labels_card/fine_nonempty` を同Sourceで使用 |
| 2 原Φ/Γ/Λと右Kan | `phiChartEquiv/phiEdgeEquiv/phiFace_empty` により同Φは原k circle。`phi_d0_zero/phi_d1_zero/phiH1Coordinates` と `phiHomologyCoordinates` は原cochain/chain全商のQ両逆。原Γは `gammaVertexEquiv`、`gammaEEdgeEquiv`、`gammaHEdge_empty`。同mの二位置は `gamma_parallel_incidence` で別射。`gammaBoundary_zero/gammaCycleCoordinates/gammaCycle_dimension` は実e上のΓ核Q。`phi_components/gamma_components/lambda_components` から原localUnitEquivへ接続し `etaEquiv` 全三次数両逆。`pNamedEquiv/eta_square/epsilon_square` は独立Pとη/ε/uを全三成分で同定。`named_u0/named_u1/named_u2` は元r0=id/r1=(e,h,0)/r2=0 |
| 3 原混在適合 | 同原m↔kを `mixedVerticalEquiv` で全A構成。原a/V/B零と `mixedVerticalBoundary_single/eq/bijective` から実Dの全両逆を生成。`rawKappaEquiv/kappaEquiv/kappaStarEquiv` は実κ/κ*そのもの。原セル値1から独立構成する `mCycle/kCycle/phiK/phiKDual` を `mCycle_vertical/kappa_m/phiK_pairing/phiK_period/kappaStar_m_period` で接続する。`mCycle_nonzero/phiK_nonzero/not_gammaForest` が非空混在発火を保証。literal `R_zero/R_dimension` と同標準 `tau_zero/tau_rank` は全Aで零 |
| 4 実H¹と誤列反証 | `fine_d1_apply/fine_cycle_iff/k_only_not_cycle` は原k cochainが閉でないことを示す。`coarseNamedCoordinates/fineNamedCoordinates` は全原商Q²の両逆、`subset_map/allA_comparison_bijective/defect` は実uの全e/h恒等とJ00。独立粗細単独1代表 `coarseLoop/fineLoop` は `loop_preserved/standard_loop_preserved`、全periodと各非零性へ接続。`pH2_subsingleton/pH2_dimension` は原P H²零。`wholePhi_sequence_not_exact` は任意g:元fine標準H¹→元全Φ H¹と任意t:同全Φ→元P H²に対し元ε-gとg-tの両Exactの同時成立を否定。ε全射・P H²零・同非零k dual類を実証明で使う |
| 5 全A・二Law・有限判定 | `allA_phi_dimension_sum/allA_kappaStar_rank/full_rank_table` は非空Φ和1/κ*rank1、空A全零を同選択規則で保持。原全Law族の `block_map/law_map/lawKappaEquiv/lawKappaStarEquiv/law_kappa_m/law_kappaStar_m_period` と `law_R_zero/law_tau_zero/law_full_rank_table` により同台二labelのΦ和2/κ*rank2/R0/τ0/J00を証明。両e/h原Law類の非零保存、原Law ε可逆/P H²零/全Φ誤列反証も接続。`primitive_J/primitive_law_J/primitive_preservation_true/allA_preservation_true/law_preservation_true` はEの独立原有限producerを同実診断と同じBoolへ戻す |

W3の原m=(k,a1,a0)ではΓaがforest・κ=0・非零τとなる。同じ一般κ/τ APIへの今回W5適用では原同eの符号相殺でB=0、D可逆、κ*可逆、R=0・τ=0となる。全Φ項をRへ読み替えたり、混在面を垂直面に交換したりしていない。

### Material premiseとproof-use

| material premise | 役割・状態 | 入力からの生成と使用先 |
| --- | --- | --- |
| Source/readings/有限namedセル/原支持/端点/Option/符号 | 一般T0のambient input、Wではdischarge-requiredを構成 | WitnessCommonとWitnessFiveInputが固定表からM全fieldを生成。K1台→同selected cells→同carrier/Φ/Γ/Λ/原Dと実u |
| Law/粗adequacy/細adequacy/発生label | 一般T0のambient input、Wでは放電済み | 元非定数Lawとadequacy、label≃Bool/card2、原Law族の同blockと全射自然性に使用。Value全体有限性を追加しない |
| 非空A、原eの名前0/1 | 非空指定成分だけの方向条件 | 非空性からfullSelectedで全セルを構成。空Aは元添字空・原商・同射で別に放電。全A結果の条件には残さない |
| Φ/Γ/Λの成分条件 | 一般localUnitEquivの方向条件、固定W5では放電済み | 同原Φchart/Γvertexの両逆と各zigzag、原face空から生成。原rightKan ηの両逆と原P全三次数同定に使用 |
| a/V/B零、D同型、κ/κ*同型 | discharge-required、放電済み | 原mの二e位置・k辺の射影・m↔k支持両逆から生成。原rawκ核/全射→κ・双対→literalR・元標準τ |
| H¹座標・P H²零・rankと非零代表 | discharge-required、放電済み | 原d0/d1核・像・商とe/h全period両逆、原ηのe2両逆。元非零k dualとε全射を任意二射の誤列反証で使用 |
| 全Law可逆性とrank2 | discharge-required、放電済み | 原label族の実自然性と各原κ*両逆。二labelを保持した全ΦQ²と実κ*range、原LawR/τ/ε/P H²/非零類 |
| 有限producerと保存Bool | discharge-required、放電済み | C20の原native表示→同旧blockDefectへ現Mを適用し00を生成。全Set/全label Boolへ双方向同値を適用 |

新しいconclusion-equivalent premise、結論certificate field、未使用material premiseは導入していない。両逆に渡すbijective・kernel/range等号は同原入力のLean証明から生成し、期待rankを受け取らない。原η・κ・τの構成と商の両方向を証明する有限witnessであり、下記の有理表のprecheckは補助観測として区別する。

### 全固定targetの累積対応（completion candidate）

次の対応はGOAL T0・A–E・Wと設計四文書の固定要求全体に対する現在のcandidateである。最終受理には同headの標準PRゲートと別新規数学2/Lean2によるwhole-goal完了監査を要する。過去cycleの自己申告やPRのマージだけを数学的証拠にはしない。

| 固定要求 | 累積Lean実体と同じ写像の接続 | 受理された構成段階 |
| --- | --- | --- |
| T0：全有限原入力・全A・任意Law・空/重複/loop/平行 | Incidenceの有限対象/射・distinct位置、CarrierのM由来全関手、SupportEmpty/LawSupportEmptyと原label生成。一般APIは任意M/A、finite Sourceからreading target/label有限性を導く。Wの指定表が非空発火を構成 | C1–3、C11–13、C16、C21–25 |
| A：incidence圏・carrier・右Kanの普遍性 | `IncidenceFunctorData.functor` に原Mの全三関係を放電して `Carrier.preimageFunctor` を生成。ConstantLimitの任意cone lift/uniqueness・`coefficientIsRightKanExtension` と実 `pushforwardIsRightKanExtension`。Φ/Γ/Λのcomma成分両逆と全原incidence射作用 | C1–3 |
| A：P・η・ε・独立u・原商双対 | `pushforwardComplex/unitHom/evaluationHom/aSubnerveComparisonHom_factorization` は全三次数。原degenerate chain Lの閉性、実ε像の両包含、`evaluationQuotientDualHom/evaluationQuotientDualStandardIso` の全両逆と代表評価 | C2–4 |
| B：原B/D/V/κ・literalR・H⁰Q/H¹Q・SES | RawBlocks/Kappaの原行列分解と実closed chain、`verticalHomologyPhiEquiv/kappa/kappaStar/fiberR_eq_ker`、原L/Qのzero degreeと `restrictionStandardHomologyREquiv`、`evaluationRestriction_shortExact` | C4–5 |
| B：全五項列・標準τ・代表と符号 | `evaluationH1/fiberRestrictionH1/connectingTau/evaluationH2` と各隣接三項のFunction.Exact。`connectingTau_correctedFiberClass` は原補正β・全代表・符号・補正/代表/基底の独立性を標準SESδへ同定 | C6 |
| B：filtration/E₂/d₂ | 原carrier filtration、graded全SES、native `carrierSpectralObject` と全三角δ、LowExactCoupleの二組全Exact・独立derivedLift/derivedSecondDifferential、同E₂のR/H²P両逆と元τ等号 | C7 |
| B：forest/pure/一般消滅必要十分/全A有限検査 | `forestFiberREquiv` は元Γforestの原B核零から導く。旧pureには原MixedFace空からκ/τ零を導出。`connectingTau_zero_iff_primitive` と原有限matrix包含Bool `primitiveTauZeroDecision/allATauZeroDecision` は両方向・全Setを保持 | C5–6、C9、C16 |
| C：kernel/cokernel SES・次元式・保存両方向 | `directH1_kernel/directH1_old`、`coefficientCokernelInclusion/totalCokernelFiberProjection/coefficientCokernel_shortExact`。`coefficient_cokernel_kappa_dimension/coefficient_zeroDefect_iff` は同旧Tと同a/R/τを使用 | C8 |
| C：局所十分条件/pure C3′/新旧C3 | `localUnitEquiv/local_zeroDefect/pure_allA_zeroDefect_iff/pure_C3prime_of_allA_zeroDefect`。G107FiberComparisonが既存C3非必要性の同入力に新pure/Φ条件を実適用 | C9 |
| C：三標準錐/triangle/Q擬同型/全整数次数/相殺 | `coefficientCompositionTriangle_distinguished` と三原Cone、`fiberConeDesc` の擬同型、全nのCone SES/Exact/代表/符号と `fiberCone_connecting/fiberConeH1REquiv_tau`。`coefficientCancellation_zero` はG133同相殺始域零を使用し、W3τ非零と区別 | C8、C10、C23 |
| D：同実Law比較・旧H¹・全三次数/全錐/SES/δ/重複 | LawCoefficientInput/LawCoefficientComparison/LawFiberSequence/LawHomologyCoordinates/LawCoefficientCones/LawDefectDiagnosticsで全元・全nの実族自然性。原発生label添字を保持し、G134 `lawH1Defect_subset_sum` で同旧block和へ戻す | C11、C13 |
| D：全A⊆A′自然性・任意label部分台 | SupportCarrier/Pushforward/Quotient/Fiber/Connecting/Conesの全原制限とrefl/comp。LawSupport族はlabel support data任意、κ/τ/全錐/全射図式へ接続 | C12–13 |
| D：G134正操作・reading pullback・有限合成/逆和写像/面複製 | PositiveOperationPath/PositivePreservation/PositiveCoefficientPreservationは同G134原生成比較と同ホモトピーの逆有限和からa同型・τ核零・全n錐零。FaceClone全構成は同mapped入力P=C′/ε恒等/η面対角を実H¹保存・非零H²余核・総錐H²へ接続 | C14–15、C24 |
| E：原有理matrix表示・核像商・同a/R/τ/J/成分・全A/label | PrimitiveMatrices/RationalQuotientCoordinates/NativeDegreeCoordinates/NativeDegreeDifferentials/NativeHomologyCoordinates/FiberCompatibilityCoordinatesは全vectorと全原商両逆。FiniteComponentsは有限Homの原Zagからbounded paths/同Kan成分へ両方向。FiniteTauDecision/FinitePreservationDecisionは原有限matrix・非負Law block和から同旧診断/全Set・全発生label Boolへ必要十分 | C16–20 |
| W1–W2：係数だけの二欠損とpure k | WitnessOneの両独立表、元a/Φ/R/τ/比較・非零h・全rank/Law欠損(2,0)/(0,2)。WitnessTwoの元k pure代表、余核/rank/R同Q、κ/τ0、保存hとC3′非保存、全Law(0,2) | C21–22 |
| W3：原full/paired・非零τ・H²/錐/G133 | WitnessThree全指定三角原表を保持。fullは原Γforest・κ0・R/H²P Q・原βからτ(0,1)非零/同型/J00、pairedはmだけ除去・原k余核/J01、原h双方保存。全Lawτrank2/pairedJ02、totalConeH¹QとG133相殺0 | C23 |
| W4：同G134全表・c-only/repeated/empty台・面複製 | WitnessFour全spineはG134同constructorから原Φ/Γ/Λ/η/εとPを生成、plus/minus原余核0/Q・全Law0/Q²、W2a–c同保持とP次数別同型を仮定せず、mapped clone H¹保存と非零H²余核/総錐H²Q・全LawQ²を同定 | C24 |
| W5：混在適合を除いた誤列 | 上記五条件。原D(m)=k/κ同型/R0/τ0/P=粗/e-h保存/J00、原全Φ非零と元P H²零に任意誤列完全性が両立不能。全A・空A・二Law・同有限producerを保持 | C25 |

全固定completion criteria 1はこの全T0/A–E/Wの構成・両方向・具体適用と接続へ、2は本report/ResearchLean全宣言spine/前提と出所へ、3は一般混在入力のκ/R/τとW3/W5の区別・指定版の独立最終監査へ対応する。数学上の未放電行は候補として空、正式標準PR監査・root acceptance・実CI・別whole-goal四査読・root最終再判定とIssue同期は実行待ちである。Formalは未移植（Research-proved候補）であり本体からResearchをimportしない。GOALと恒久設計は固定版を保つ。

### Cycle25 全spine・個別公理・focused検証

rootが各新fileを必要な単一focused targetとして検証した。以下が全213 source宣言と生成congr_simp 2件の全spineであり、本文の主要名だけを公理監査していない。生成2件は所有def/現runtime/個別print axiomsで同定し、sourceに文字通り存在するproof bodyとは区別する。

<!-- cycle25-generated-evidence -->

| file | namespace・全宣言spine（prefixを以下の各名へ付ける） | source SHA-256 | 個別公理出力SHA-256 |
| --- | --- | --- | --- |
| `WitnessFiveInput.lean` | `AAT.AG.AtlasCoefficientFiber.WitnessFive`：`coarseNerve`, `fineNerve`, `Nc`, `Nf`, `M`, `chartMap_apply`, `edgeMap_e`, `edgeMap_h`, `edgeMap_k`, `edgeMap_none_iff`, `edgeMap_some_iff`, `faceMap_apply`, `fine_edgeLeft`, `fine_edgeRight`, `fine_faceEdge0`, `fine_faceEdge1`, `fine_faceEdge2` | `8583cbedb495200fd9a25b2cbf3b56076a1743523cfbe4071091c93f5cefed95` | `480512c58a2465622d1e062fee08024b5ea1f8b0d13203d5596b334fbffb14f8` |
| `WitnessFiveCoefficients.lean` | `AAT.AG.AtlasCoefficientFiber.WitnessFive`：`phiChartEquiv`, `phiChart_subsingleton`, `phiFace_empty`, `phi_zigzag`, `phi_components`, `gammaVertexEquiv`, `gammaVertex_subsingleton`, `gamma_zigzag`, `gamma_components`, `lambda_components`, `etaEquiv`, `etaEquiv_toHom`, `unit_bijective`, `unit_defect`, `eta_epsilon_square` | `e8e6607324da920a39122ac18cdbca281d161caf6d3c7b3ca6294adeda3203f4` | `b6d07e2001ca3ce9f84840526d8c30287112961f195c74b2484d5ae64069ae8b` |
| `WitnessFiveComparison.lean` | `AAT.AG.AtlasCoefficientFiber.WitnessFive`：`coarse_d0_zero`, `coarse_d1_zero`, `fine_d0_zero`, `fine_d1_apply`, `fine_cycle_iff`, `k_only_not_cycle`, `coarseNamedCoordinates`, `finePeriod`, `finePeriod_kernel`, `finePeriod_surjective`, `fineNamedCoordinates`, `fineNamedCoordinates_mk`, `named_map`, `coarseCoordinates`, `fineCoordinates`, `subset_square`, `subset_map`, `comparison_bijective`, `empty_comparison_bijective`, `allA_comparison_bijective`, `defect`, `coarseCoordinates_apply`, `fineCoordinates_apply` | `3dba2abfe8337f9b036d34981e63aa3f6506c5dfcd42b665403499755f0193e7` | `23214f5b32b71dd019f20222a7dbf6d0d0070b0faee0aea0eda3f2234a4a19fe` |
| `WitnessFiveGeneration.lean` | `AAT.AG.AtlasCoefficientFiber.WitnessFive`：`pNamedEquiv`, `eta_square`, `epsilon_square`, `named_u0`, `named_u1`, `named_u2` | `98f14d66895d3a5fa2bd50c7c326d1043f1ef45c8560c580da279e8d470c062a` | `7f1c99264c9bb777cc1225180d59619155e43874d007666f5976951cb81e8b4a` |
| `WitnessFiveFiber.lean` | `AAT.AG.AtlasCoefficientFiber.WitnessFive`：`nonempty_of_vertical`, `mixedToVertical`, `verticalToMixed`, `mixedVerticalEquiv`, `mixedVerticalEquiv_apply`, `fineChart_subsingleton`, `verticalEdgeBoundary_zero`, `verticalFace_empty`, `verticalBoundary_zero`, `mixed_horizontal_endpoints`, `mixedVerticalBoundary_single`, `mixedVerticalBoundary_eq`, `mixedVerticalBoundary_bijective`, `mixedHorizontalBoundary_zero`, `phiEdgeEquiv`, `phi_d0_zero`, `phi_d1_zero`, `phiH1Coordinates`, `phiH1_dimension`, `gammaEdge_coarse_name`, `gammaEEdgeEquiv`, `gammaHEdge_empty`, `gammaBoundary_zero`, `gammaCycleCoordinates`, `gamma_parallel_incidence`, `phiH1Coordinates_mk` | `8ffb47a4378575defbf1db4174f21d000035020c114eb2e92b310102638f7a51` | `30bb4f9a125d5b7b80ee5b711bd61f90ba8db8dc3dc06684a8096705b5eb044e` |
| `WitnessFiveKappa.lean` | `AAT.AG.AtlasCoefficientFiber.WitnessFive`：`rawKappa_injective`, `rawKappa_surjective`, `rawKappaEquiv`, `rawKappaEquiv_toLinearMap`, `kappaEquiv`, `kappaEquiv_toLinearMap`, `kappaStarEquiv`, `kappaStarEquiv_toLinearMap`, `R_zero`, `R_subsingleton`, `tau_zero`, `evaluation_bijective` | `a150d313bba26121a68664d2697a2d4ac7510dab23579ab46d78b59888ba9539` | `02a7c4951ba394e5d45530a153b45173e9a1aa679dbeede928518c803afa6994` |
| `WitnessFiveRepresentatives.lean` | `AAT.AG.AtlasCoefficientFiber.WitnessFive`：`coarseChart`, `verticalK`, `mixedM`, `mixedM_vertical`, `mCycle`, `kCycle`, `mCycle_vertical`, `phiK`, `kappa_m`, `mCycle_nonzero`, `kappa_m_nonzero`, `phiKCocycle`, `phiKDual`, `phiKDual_period`, `phiKDual_nonzero`, `phiK_pairing`, `phiK_nonzero`, `wholePhiCoordinates`, `wholePhi_dimension`, `wholePhiK`, `wholePhiK_period`, `wholePhiK_nonzero`, `chart_card`, `phi_dimension_sum`, `kappaStar_m_period`, `mCycle.congr_simp`, `phiK.congr_simp`, `mCycle_val`, `kCycle_val`, `phiK_eq_mk` | `f92d009717019fd643bfacf63a2f41428ba97b78e9f63fd84ce85fdbb8b1b8be` | `92619e3d16cc1fca95077dc7d383a8d0c6169ae0234eaad6e833b4824ae68704` |
| `WitnessFiveChain.lean` | `AAT.AG.AtlasCoefficientFiber.WitnessFive`：`phiBoundary1_zero`, `phiBoundaryToCycles_zero`, `phiHomologyCoordinates`, `phiHomology_dimension`, `mixedFaceEquiv`, `mixedCycleCoordinates`, `mixedCycle_dimension`, `gammaCycle_dimension`, `phiHomologyCoordinates_mk`, `phiK_period`, `mixedCycleCoordinates_apply`, `mCycle_period`, `not_gammaForest` | `c868e3affb9605189f9fd9602867ff099a472473587267147c3e5c4f46136394` | `271a12eb2b65b35ef1623a1705ce187d1f14f25d117ef95541e753d126e6435c` |
| `WitnessFiveDiagnostics.lean` | `AAT.AG.AtlasCoefficientFiber.WitnessFive`：`pC2_subsingleton`, `pH2_subsingleton`, `wholePhi_sequence_not_exact`, `coarseLoopCycle`, `coarseNamedLoop`, `fineLoopCycle`, `fineNamedLoop`, `coarseNamedLoop_period`, `fineNamedLoop_period`, `coarseLoop`, `fineLoop`, `coarseLoop_period`, `fineLoop_period`, `loop_preserved`, `coarseLoop_nonzero`, `fineLoop_nonzero`, `standard_loop_preserved` | `495a93d9526e9f12647ee7213091c70aca510d677f3e521c7d22d2a9cfa3273d` | `5a65ec80d34b7f6a29dfd9aa6288eceeb968dc090fafc4dd5fe12350a5bb01b2` |
| `WitnessFiveLaw.lean` | `AAT.AG.AtlasCoefficientFiber.WitnessFive`：`coarseBlockCoordinates`, `fineBlockCoordinates`, `block_map`, `law_defect`, `primitive_law_J`, `coarseLawCoordinates`, `fineLawCoordinates`, `law_map`, `coarseLawLoop`, `fineLawLoop`, `law_loop_preserved`, `coarse_law_loop_nonzero`, `fine_law_loop_nonzero`, `law_unit_bijective`, `law_unit_defect`, `lawKappaEquiv`, `lawKappaEquiv_toLinearMap`, `lawKappaStarEquiv`, `lawKappaStarEquiv_toLinearMap`, `law_R_zero`, `law_R_subsingleton`, `law_R_dimension`, `law_tau_zero`, `law_tau_rank`, `lawWholePhiCoordinates`, `law_wholePhi_dimension`, `law_kappaStar_rank`, `lawMCycle`, `lawPhiK`, `law_kappa_m`, `law_phi_dimension_sum`, `law_evaluation_bijective`, `law_pH2_subsingleton`, `lawWholePhiK`, `lawWholePhiK_period`, `lawWholePhiK_nonzero`, `law_kappaStar_m_period`, `law_wholePhi_sequence_not_exact` | `3cce2427c88626826e5e6f4d690b7936bb071ebe6edf76cc38e05ac0208d3775` | `1a19e51185b6bfb8e88b5c3428ab14f46781a969a8a207314416d6d30e550e11` |
| `WitnessFiveRankTable.lean` | `AAT.AG.AtlasCoefficientFiber.WitnessFive`：`kappaStar_rank`, `empty_chart_isEmpty`, `empty_phi_dimension_sum`, `empty_kappaStar_zero`, `allA_kappaStar_rank`, `allA_phi_dimension_sum`, `R_dimension`, `tau_rank`, `primitive_J`, `full_rank_table`, `law_full_rank_table`, `coarse_H1_dimension`, `fine_H1_dimension`, `p_degrees_dimension`, `pH2_dimension`, `primitive_preservation_true`, `allA_preservation_true`, `law_preservation_true` | `c911f0e87909040be29f38e8378cbb544e64be592e2a4e3714ba461f0c1e8be3` | `2c240a61facaee67f5fa204cf2cca8545e3bb670d1f19658e34b5ed3b3c73d10` |

各fileのコマンドは cwd `research/lean` の `./check_research_modules.sh --focused ResearchLean/AG/AtlasCoefficientFiber/<file>`。全11対象でexit0/error0/warning0、全215個別出力とmodule auditは `propext` / `Classical.choice` / `Quot.sound` の部分集合。検証照合artifact SHA `df22979ea579529907d686e06ee0c7322955eb274f8a54b5ca29ffdafbd44fff`。必要な単一root cache生成をdependent importに用いた。Research full/aggregate/全fileloop、本体lake build、Formal移植は実行していない。

### 現受理predecessorと累積公理出力の版照合

以下はcurrent sourceとaccepted headのgit showをbyte比較した所有file群。APIのlexical候補リストを実使用そのものと混同せず、使用は上の構成・proof-useと現Lean bodyから追う。原rightKan・一般短完全列・商双対・標準homology・実族自然性の強度と同M/A/lawsへの適用条件を保持する。

| 現owner file | accepted head・PR・review ref | source SHA-256 |
| --- | --- | --- |
| `AtlasCoefficientFiber/WitnessCommon.lean` | `160a3087d20d2e9cf22de758359acb5df7ec2ecd` / [PR #5297](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5297) / [受理監査](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5297#issuecomment-6050868943) | `f4f46b1ae32e0462e6ed1785f88df7a31ad6ed18607169c6738b3c652bfdd56b` |
| `AtlasCoefficientFiber/FinitePreservationDecision.lean` | `fc95be6c3a948aa993a0e6af15f6c44546ce90b3` / [PR #5313](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5313) / [受理監査](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5313#issuecomment-6072107116) | `64815b21177bdef5df81a15df88a6aa783632667047e6ee7483b1b64d6e18ef8` |
| `AtlasCoefficientFiber/LawFiberSequence.lean` | `657e562eaa154e94155681e07d3c218e6998375b` / [PR #5304](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5304) / [受理監査](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5304#issuecomment-6058853944) | `2a838970a53412557e5ca9bc90e9296fd5547297076392a2bcd2bd37b5b6ec55` |
| `FaceRelationSubdivision/FullSupportSubsetComparison.lean` | `0134623422114ae39f989d591cb167c6176aae3e` / [PR #5287](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5287) / [受理監査](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5287#issuecomment-6030258596) | `893423de007db0a677b7f933408bab4041ee9f45011f7042f1c79de8d98e15b0` |
| `FaceRelationSubdivision/LawComparisonFiberDiagnostics.lean` | `0134623422114ae39f989d591cb167c6176aae3e` / [PR #5287](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5287) / [受理監査](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5287#issuecomment-6030258596) | `99fbd72c77adf71ff6cec151ce0dda3c804f541459039c2280cdf41d86e25206` |
| `AtlasDefectComposition/FullSupportIncidence.lean` | `0134623422114ae39f989d591cb167c6176aae3e` / [PR #5287](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5287) / [受理監査](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5287#issuecomment-6030258596) | `7707340dfe3a4bc13e9b7cd8dd8217bc332b163aab847f5f984404db298bd66c` |
| `FaceRelationSubdivision/IncidenceNamedComparison.lean` | `0134623422114ae39f989d591cb167c6176aae3e` / [PR #5287](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5287) / [受理監査](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5287#issuecomment-6030258596) | `56698b687013379306b13fb3bcf912d081a76ec3d4a6a71e1b644687e65f602a` |
| `FaceRelationSubdivision/LawComparisonDecomposition.lean` | `0134623422114ae39f989d591cb167c6176aae3e` / [PR #5287](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5287) / [受理監査](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5287#issuecomment-6030258596) | `496ba43e5989e9bb309860976a432ed31df91e9c6c286237a6b92b6172434f63` |
| `AtlasDefectComposition/LinearConjugation.lean` | `0134623422114ae39f989d591cb167c6176aae3e` / [PR #5287](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5287) / [受理監査](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5287#issuecomment-6030258596) | `2fb0f6f319a8dcdf8848f4dfd7672371a930b41aa96919888df2b4a273b40fbb` |
| `AtlasCoefficientFiber/LocalFiber.lean` | `70633bfc653fe823fbdbbbcec8b1d6fc12a5bb5b` / [PR #5303](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5303) / [受理監査](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5303#issuecomment-6057242603) | `cfc7d3a3d44a78879840daae8cf5a846510813156598c1006e9686c1b68013a4` |
| `AtlasCoefficientFiber/LocalPreservation.lean` | `70909cc76c24e689fe03efe4340afc2bbf164969` / [PR #5300](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5300) / [受理監査](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5300#issuecomment-6053115567) | `29c5ab27b2e133dd2d1415612a229c3505c685542726a98ec25c8adc399f1061` |
| `AtlasCoefficientFiber/LawHomologyCoordinates.lean` | `7f20e6aaaae8c51298b32d955ca16a6b0076b84a` / [PR #5302](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5302) / [受理監査](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5302#issuecomment-6054697310) | `6052b12559e0f2fe036036ff60349e451e9fbb948da10582236aee718e3ae68c` |
| `AtlasCoefficientFiber/WitnessFullSupport.lean` | `fecb994402b579b6a0fe15190ef10b4752a7c44b` / [PR #5314](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5314) / [受理監査](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5314#issuecomment-6072664284) | `95b4dca558735ab40bc172f8ff648884296f3c7bcf086d4d44a1560bcb107b1d` |
| `AtlasCoefficientFiber/WitnessOneDiagnostics.lean` | `fecb994402b579b6a0fe15190ef10b4752a7c44b` / [PR #5314](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5314) / [受理監査](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5314#issuecomment-6072664284) | `e6b420c45d48034cfc49cb7da90b6d7f61d7b8e4ea564838f3422153eb430a65` |
| `AtlasCoefficientFiber/WitnessThreeInput.lean` | `a90fee53a0ee64caea90acb1073d43b776521cd3` / [PR #5312](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5312) / [受理監査](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5312#issuecomment-6071529511) | `68f89f83e088f3d4e2f55bb7e08fe6be339e8751ade0ffdc2d4f3147282b34c8` |
| `AtlasCoefficientFiber/GammaForest.lean` | `61659d7586accb379f03883d3722c5d6a622fad2` / [PR #5296](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5296) / [受理監査](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5296#issuecomment-6049620284) | `c783cd60bb052d487adaee010650109b8df5d89d31fb1c0b81458316d8f09948` |
| `AtlasCoefficientFiber/MappedEvaluation.lean` | `180477fd314e416689beed56f3609edfc91403fd` / [PR #5306](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5306) / [受理監査](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5306#issuecomment-6060895737) | `5cf4664d5b34544d033f85b8cc95ef675043de72717f7d524aed2b170f195e7b` |
| `AtlasDefectComposition/EndpointHomology.lean` | `cc62fac23e82e41728dd8188967c73bde36b1516` / [PR #5301](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5301) / [受理監査](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5301#issuecomment-6053510508) | `1deb845209adcd269ea6e2a0113af970a747b20af890a6f1107eb2eb5e916e4b` |
| `FaceRelationSubdivision/WitnessOneInput.lean` | `0134623422114ae39f989d591cb167c6176aae3e` / [PR #5287](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5287) / [受理監査](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5287#issuecomment-6030258596) | `53452d383799618adfd17ebf948ac09634efd3d578fd9bcd824f835835a72ba1` |
| `FaceRelationSubdivision/WitnessOneComparison.lean` | `0134623422114ae39f989d591cb167c6176aae3e` / [PR #5287](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5287) / [受理監査](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5287#issuecomment-6030258596) | `17458d7bc4805cfddad36c281a2112233eb173f030eef7d6e4e5f157122ff1fb` |
| `FaceRelationSubdivision/WitnessTwoALoop.lean` | `0134623422114ae39f989d591cb167c6176aae3e` / [PR #5287](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5287) / [受理監査](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5287#issuecomment-6030258596) | `28426027c31dd15049d5c884fa6508e5dbbd3014f6beb461d98ea129657378f3` |
| `FaceRelationSubdivision/WitnessTwoBInput.lean` | `0134623422114ae39f989d591cb167c6176aae3e` / [PR #5287](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5287) / [受理監査](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5287#issuecomment-6030258596) | `4b6bdc381508fafdd8e62c4b5fd8a508226685619b372c8a6630295a9464e1b7` |
| `FaceRelationSubdivision/WitnessTwoBLoop.lean` | `0134623422114ae39f989d591cb167c6176aae3e` / [PR #5287](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5287) / [受理監査](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5287#issuecomment-6030258596) | `ab177628c77402f63de842948f1222f2305e159a325e179cbff06d412502c504` |
| `FaceRelationSubdivision/WitnessTwoCInput.lean` | `0134623422114ae39f989d591cb167c6176aae3e` / [PR #5287](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5287) / [受理監査](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5287#issuecomment-6030258596) | `0473a7fd7e3185df850f6575cc185bcb2038f62262a27248cee1cebb51976011` |
| `FaceRelationSubdivision/WitnessThreeInput.lean` | `0134623422114ae39f989d591cb167c6176aae3e` / [PR #5287](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5287) / [受理監査](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5287#issuecomment-6030258596) | `9d3124d4e0afd5fc5cabf0a82fbac1078b5573453394860f48a1882c24e0af4d` |
| `AtlasCoefficientFiber/PositiveOperation.lean` | `9cdf674adb720d23ade0f8e914426df8b7e2ca48` / [PR #5305](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5305) / [受理監査](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5305#issuecomment-6059890330) | `4b484f43de0565ea875247d096546e40c818e49cb57d23272d1be029cf5562ab` |
| `AtlasCoefficientFiber/PositiveOperationPath.lean` | `9cdf674adb720d23ade0f8e914426df8b7e2ca48` / [PR #5305](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5305) / [受理監査](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5305#issuecomment-6059890330) | `13329fb68579ed44d017926065565b7c7f2323be6bb951835da2b102ba275f6e` |
| `AtlasCoefficientFiber/FaceCloneComparison.lean` | `180477fd314e416689beed56f3609edfc91403fd` / [PR #5306](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5306) / [受理監査](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5306#issuecomment-6060895737) | `d5403b62bf9dda7cb6a70014f7d3a1b82b5e61920cbcf1a3059c98fc2e7aadde` |
| `AtlasCoefficientFiber/FaceCloneCoefficient.lean` | `180477fd314e416689beed56f3609edfc91403fd` / [PR #5306](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5306) / [受理監査](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5306#issuecomment-6060895737) | `740c9f8b775c74a6231dbf72123b546566832c6a468be6c6dd6f2e9ba8095abe` |
| `AtlasCoefficientFiber/WitnessThreeComparison.lean` | `155478e8a595a8a396c28eacae0570f49237d6a6` / [PR #5316](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5316) / [受理監査](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5316#issuecomment-6074532951) | `3f8e454fda05f5114dd34bbe68238724b012704fe933de23e86299feb4fe0a7e` |
| `AtlasCoefficientFiber/WitnessOneEvaluation.lean` | `fecb994402b579b6a0fe15190ef10b4752a7c44b` / [PR #5314](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5314) / [受理監査](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5314#issuecomment-6072664284) | `5a888a070d71dd71b6dd5e5dc7230d9fad2876caf2afb101b06c5d455d8e1206` |
| `FaceRelationSubdivision/SupportedChain.lean` | `0134623422114ae39f989d591cb167c6176aae3e` / [PR #5287](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5287) / [受理監査](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5287#issuecomment-6030258596) | `9b89c91f607903ce61243c2c1798e983e5fa9dd47c4b19b7f93894fb3147f721` |
| `AtlasCoefficientFiber/FiberHomology.lean` | `61659d7586accb379f03883d3722c5d6a622fad2` / [PR #5296](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5296) / [受理監査](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5296#issuecomment-6049620284) | `7002890ed28d4ad6996c7cd2851e8399f901cb5ff0ebe692a7e7cbbe0f355aed` |
| `AtlasCoefficientFiber/FiberChains.lean` | `61659d7586accb379f03883d3722c5d6a622fad2` / [PR #5296](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5296) / [受理監査](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5296#issuecomment-6049620284) | `04b412ea259af7c33f406a3ac2803e5b822633407ef60144e4faf8a37ef03774` |
| `AtlasCoefficientFiber/Kappa.lean` | `61659d7586accb379f03883d3722c5d6a622fad2` / [PR #5296](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5296) / [受理監査](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5296#issuecomment-6049620284) | `d82d43acacfb6bb5f30298e71603464adae075119fb311ac762ae85279a4193b` |
| `AtlasCoefficientFiber/FiveTermSequence.lean` | `160a3087d20d2e9cf22de758359acb5df7ec2ecd` / [PR #5297](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5297) / [受理監査](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5297#issuecomment-6050868943) | `c9fb934891dfd966ac23711e566cda115987220862e904c63cc5f9ed002687e3` |
| `AtlasCoefficientFiber/DegenerateCells.lean` | `927f6be84e525e853df340d1ad7c45f5c9f47358` / [PR #5295](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5295) / [受理監査](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5295#issuecomment-6047664301) | `c9cad1af21d5101deed727cc0f2d18184ae665cb10046e4cfd8af679c375c7f3` |
| `AtlasCoefficientFiber/RawBlocks.lean` | `cc62fac23e82e41728dd8188967c73bde36b1516` / [PR #5301](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5301) / [受理監査](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5301#issuecomment-6053510508) | `c87584a49ddd341aa965b4f16d53ca8499487e2f4023f18ef4484c6218e73b07` |
| `AtlasCoefficientFiber/FiberCohomology.lean` | `70633bfc653fe823fbdbbbcec8b1d6fc12a5bb5b` / [PR #5303](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5303) / [受理監査](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5303#issuecomment-6057242603) | `74aa1f4930cbd01151d5c1792d76c43324208de1c0a795924312885b97fb6951` |

全39ownerの現byte照合artifact SHA `536b5237103ee1e5af80f8640a189ac362433ced826ebc7029d03b379466a2b3`。RawBlocksはC10受理head、FiberCohomologyはC12受理headの現公開API版へ照合した。C5初版からの変更を無視せず、現statementと原Mへの使用を確認する。追跡完了したpredecessorの内部依存・全査読史を再認定しない。

C1–24の現186所有fileは、同source SHAを記録した実成功validationとlog SHAを照合した。全3828個別公理出力がその成功logに存在し、未対応0、標準三公理のみ。累積current-source qualification artifact SHA `3f6d4e5772602a5a2acd3c72ac9ea30d526ee2e442cf1750e910e2e35543f3da`。これは受理済み現版の検証証拠を再利用する静的照合であり、全file loopの再elaborationではない。

同原有理表の四A/二LawについてFractionによる補助precheckも行った。原d1/chain-map式、D=1/B=0、Pの三次数1/2/0、η恒等・ε=(e,h,0)、原H¹Q²、Φ1/κ*rank1/R0/τ0/J00を観測した。これはLeanの上記全核・像・商・代表・同実射の証明とは別の観測記録である。

### Cycle25 result proposal

```yaml
ledger_type: target_cycle_result
goal: G-135-aat-atlas-coefficient-fiber
cycle: 25
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: [原W5全表と同原Kan二射, 原Φcircle/Γone-loop/原B核Q, 原D全両逆とκ[m]=[k], literalR0/標準τ0, 原e/h全商Q2と非零保存, 元P H2零と全Φ任意誤列反証, 全A/空A/二Law全rankと同有限producer, 全固定T0-A-E-W累積対応]
  exit_criteria_status: [五数学条件は上の同入力Lean構成・全両方向・全代表・全個別公理で対応, 標準PR監査と別whole-final監査は未実施]
  split_reason: none
  completion_candidate: yes
  lean_artifacts: [WitnessFiveInput, WitnessFiveCoefficients, WitnessFiveComparison, WitnessFiveGeneration, WitnessFiveFiber, WitnessFiveKappa, WitnessFiveRepresentatives, WitnessFiveChain, WitnessFiveDiagnostics, WitnessFiveLaw, WitnessFiveRankTable]
  claim_mapping:
    theorem_names: [上の全215新spineと全固定target累積対応]
    source_labels: [固定GOAL T0-A-E-W, 固定設計W5と原有限計算表, 同全Aと原二発生Law label]
    conjuncts: [上の五条件と全T0-A-E-W対応]
    undischarged_assumptions: []
    acceptance_point: 全数学義務のLean実装candidate。正式PR/別全目標最終監査の合格と実CI前にtarget-theorem-provedを出さない
    port_status: unported
  unchecked: [標準新規数学2-Lean2, root acceptance全13, 実CI, 同head final packet, 別新規whole-goal数学2-Lean2, root完了再判定と実merge-Issue同期]
audits:
  premise_delta:
    discharged: [上のmaterial premise全構成行]
    remaining: []
  certificate_provenance:
    discharged: [原入力全field, 原component条件, 同D両逆, 原全商と非零代表, 同rawκ/κ/κ*/literalR, 原標準τ, 同Law族とproducer]
    unresolved: []
  proof_use:
    used: [原mの二e位置と符号→B0/Dk, 同m-k支持両逆→D可逆, 原κ定義→原m-k等号, 原Φ dual対合と全商→κ*rank, literal核→R/標準τ, 元ε全射/P H2零/非零Φ→誤列反証, 元r1/全H1商→同e-h保存/J, 原label重複→全Lawrank2, 同nativeBool→実欠損]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  blocking_findings: []
  next_obligation: 同固定headの標準PR/rootゲート・実CI後、別新規whole-goal最終四査読とroot全固定target完了監査
```

Cycle25の実runtime所有module・型/値constant依存は215件すべて個別print集合と一致し、213 source + 2 generatedを区別して照合した。累積旧3828宣言の現sourceは各受理済み個別成功logとbyte/hash一致し、新215件との総計4043件の個別公理出力は通常3公理以下である。最終共通scanは新規Unicode・placeholder・privacy・逆importが零、登録11件は一回ずつ、固定GOAL/design/Formalは不変である。

現全GOALは正式判定までtarget-proof-checkpointを保持する。固定targetの弱化・追加仮定・指定例の変更はなく、SKILLの停止条件はない。tracking Issueは人間の明示close指示を受けていないためOPENを保持する。
