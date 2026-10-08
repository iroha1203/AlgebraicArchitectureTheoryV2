# G-135：固定targetの証拠対応

固定入力はtracking Issue [#5290](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5290)で指定した版を読む。
GOALは `dc6a46a993561233a824848c75ba547b23ddf863` の
`research/goals/G-135-aat-atlas-coefficient-fiber.md`、設計・共通基準は
`05d1c6c5cbdbb299d8d7120376135917b44f6fa1`、既存宣言は
`53b6a674a29807605a943b6f6304e7b17c2da0d6`。

## 現proof state（Cycle 8）

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
現在はCの実核・余核と旧診断への接続をCycle 8に選定する。局所係数/pure C3′/G107同例、
三錐、D・E・全W評価と別最終完了監査は未完。全目標はtarget-proof-checkpoint、Formalは未移植。

以下の各selection/result proposalは当時の履歴であり、受理状態は後続受理節へ対応させる。
現在のdelta・未放電行は末尾のCycle 8台帳で追跡する。

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
| 1 実a/Tと全H¹因子化・旧商接続 | `unitH1`、独立`directH1`、所有評価/標準等式、`directH1_factor`。原u全Hom因子化とzeroExtensionMap_comp/homologyMap_compを使用。`directH1_old`は同じ旧H¹商の自然性 | 入力生成証拠あり・正式監査前 |
| 2 元保存kerT≃kera | `directH1_kernel`は実ε単射性による同じcoarseH¹内の部分空間等号。`directKernelUnitEquiv`とvalは同じ元を両方向で保つ | 入力生成証拠あり・正式監査前 |
| 3 実cokε≃kerτ | `fiberRestriction_kernel/range`は原五項列の全隣接完全性。`evaluationCokernelTauKernelEquiv`はquotKerEquivRangeと核像等号輸送。全mk_valは同じ原制限 | 入力生成証拠あり・正式監査前 |
| 4 実余核SESの全写像 | `compositeDirectCokernelEquiv`は独立T因子化の等号、同じ代表の順逆mk。`coefficientCokernelInclusion`/`totalCokernelFiberProjection`は同じG133第四/第五射と原制限同型。全代表、単射/完全性/全射を`coefficientCokernel_shortExact`へ集約 | 入力生成証拠あり・正式監査前 |
| 5 旧診断二成分と自然数二加法式 | `directH1_defect`は標準H¹と既存商の同じblockDefect。`coefficient_kernel_dimension`、`coefficient_cokernel_dimension`、`coefficient_cokernel_kappa_dimension`は同じ核/商同型、G133次元式とτ/κ*のrank-nullity、全Φ有限Pi和から得る。整数表示も同じ第一加法式から導出 | 入力生成証拠あり・正式監査前 |
| 6 保存必要十分と同じG133特殊化 | `evaluationH1_surjective_iff`は実五項完全性の両方向。`directH1_bijective_iff`と`coefficient_zeroDefect_iff`は同じ独立T/J。零Jから原aの線形同型とkerτ零を生成。`evaluationH1_kernel`、`coefficientCancellation_zero`、二`coefficientSixTerm_*_dimension`が同じ二射の始域零と六項式特殊化。`witnessThree_cancellation_zero_and_tau_ne_zero`は同じ原W3でχ零/τ非零を併記 | 入力生成証拠あり・正式監査前 |

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
  blocking_findings: [正式PR独立査読は未実施]
  next_obligation: C局所係数からη同型/診断保存・pureC3prime全Aと同じG107旧C3非必要性例
```

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
| `DefectMaps.lean` / 17+1 | `a00f3e643fa9296a4f488653cb835ba61f5788ed3179ee67f7f6358d2cec5cfb` | `e23f084fcf822117a034eb8e9e8863e86785e7bb1db48f90fac5ab104cc58e63` |
| `DefectShortExact.lean` / 16+0 | `14f3592a8851008fdb78c4d897cf6fb488cce4d5110345ddeaa86bb0bf1b7a63` | `9055dd06c0de7bf0f4953325560d2350d7016a72606fdd662df92a319125c02c` |
| `DefectDiagnostics.lean` / 15+0 | `bd3d93c50341909af0ad968c8dec37ae7a591bfeaf1500e9a2a583ac67977504` | `badc829969856728f8e34d12e18c02765211ee79249d6bb05d0d5c4297516caa` |

再現metadata `.tmp/g135/cycle8-validation.json`（SHA-256 `2b35dc34ba7ec447ad262f3472b9f41b09bddbd29049c2f97eecb00ad8c0801f`）。
共通scan metadata `.tmp/g135/cycle8-scans.json`（SHA-256 `4f8eeb0d05566ccc61f36dd8bad40298fda52a981ab52d5c8e561cb5ec6f2143`）。
