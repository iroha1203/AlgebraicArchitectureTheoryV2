# G-135：固定targetの証拠対応

固定入力はtracking Issue [#5290](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5290)で指定した版を読む。
GOALは `dc6a46a993561233a824848c75ba547b23ddf863` の
`research/goals/G-135-aat-atlas-coefficient-fiber.md`、設計・共通基準は
`05d1c6c5cbdbb299d8d7120376135917b44f6fa1`、既存宣言は
`53b6a674a29807605a943b6f6304e7b17c2da0d6`。

## 現proof state（Cycle 4）

Cycle 1の有限incidence・一般極限・carrier対象/端点APIはPR #5292で受理済み。
Cycle 2の実M→carrier→右Kan→有限次元P→ηはPR #5293でcheckpoint受理済み。
Cycle 3の同じPからのcounit評価εと実u因子化、局所Φ・Γ・Λの構成・成分同定はPR #5294で受理済み。
ε のcochain条件と実u全三次数因子化、原始Φのchain/cochainと包含、Γの関係列、Φ・Γ・Λの実comma成分式は対象fileのLean検証を通過した。
chart→edge・edge→faceの係数自然性と原始端点・辺位置への同定も通過した。
mixed関係・三角形二経路の公開自然性APIとε次数別単射性も対象fileのLean検証を通過した。
Cycle 4の原始L・実ε像の両包含・実商双対同型・標準短完全列・H₀L/H⁰Q零性は対象fileのLean検証を通過した。初回独立4査読は中心finding 0、非中心の次数外API不足を修正し、正式再監査待ち。κ/R/τ、設計§5以降と全Wは未達。
Cycle 4は原始退化セル生成L、同じ評価像と商双対、標準短完全列へ接続する。全目標はtarget-proof-checkpoint。

以下のCycle 1 selectionから検証記録までは、最初の提案時点の履歴である。
現在のdelta・未放電行は後続のCycle 4台帳へ対応させる。

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
