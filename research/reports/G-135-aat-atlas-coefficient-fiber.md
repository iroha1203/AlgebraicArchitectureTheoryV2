# G-135：固定targetの証拠対応

固定入力はtracking Issue [#5290](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5290)で指定した版を読む。
GOALは `dc6a46a993561233a824848c75ba547b23ddf863` の
`research/goals/G-135-aat-atlas-coefficient-fiber.md`、設計・共通基準は
`05d1c6c5cbdbb299d8d7120376135917b44f6fa1`、既存宣言は
`53b6a674a29807605a943b6f6304e7b17c2da0d6`。

## 現proof state（Cycle 2）

Cycle 1の有限incidence・一般極限・carrier対象/端点APIはPR #5292で受理済み。
Cycle 2では原始Mから面射と三関係を放電し、実carrierに沿う右Kan・有限次元係数・
セル微分によるP・成分上の定数写像ηを構成した。Cycle 2の独立査読は未実施である。
Φ・Γ・Λへの成分同定、εと実u、L以降と全Wは未達。全目標はtarget-proof-checkpoint。

以下のCycle 1 selectionから検証記録までは、最初の提案時点の履歴である。
現在のdelta・未放電行は後続のCycle 2台帳へ対応させる。

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
| 同上 | `coefficientComplex`, `coefficientComplex_d0`, `coefficientComplex_d1`, `pushforwardComplex` | 一般係数APIを実右Kanへ適用してPを独立生成。Lや商dualを定義入力にしない |
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
変更対象77明示宣言と81全module宣言の依存は標準3公理の部分集合。

| file | focused target | print / 全宣言監査 | stdout+stderr SHA-256 |
| --- | --- | --- | --- |
| `Carrier.lean` | `ResearchLean/AG/AtlasCoefficientFiber/Carrier.lean` | 13 / 14 standard axioms only | `de109e9074d902cf60f592a35cd236d85dd3cdfb37341f3d7ffebc1078a39c4b` |
| `CarrierFunctor.lean` | `ResearchLean/AG/AtlasCoefficientFiber/CarrierFunctor.lean` | 32 / 35 standard axioms only | `67652a757e2538ecf968b211d40504fc0c326eb849bc8ce00560ce7709a8dd68` |
| `PushforwardCoefficient.lean` | `ResearchLean/AG/AtlasCoefficientFiber/PushforwardCoefficient.lean` | 7 / 7 standard axioms only | `bd1d0856f250f6c9662f3c3644615090008f3b7ab43f8a7537f0bb37762e719c` |
| `PushforwardComplex.lean` | `ResearchLean/AG/AtlasCoefficientFiber/PushforwardComplex.lean` | 13 / 13 standard axioms only | `2cc3b49673b60b9ec3093eb59d2699caae10b3da39350bf8f99781d463758d04` |
| `PushforwardUnit.lean` | `ResearchLean/AG/AtlasCoefficientFiber/PushforwardUnit.lean` | 12 / 12 standard axioms only | `5de166de31d26c3f6489c3cc85d6adc7f21da7c7966091f2e78d1dd82d09d000` |

必要なimport cacheを作る単一targetの `lake env lean -o ... <file>` も専用worktreeで実行した。
sourceには64新規明示宣言それぞれのprintと各file末尾の全宣言監査を置いた。
placeholder、hidden/BiDi、privacy、4新規moduleの登録と全print対応、Formal→Research import方向、
`git diff --check`を確認した。GOAL/設計を変更せず、元mainの作業ツリーはcleanのまま。
Research full/aggregate/全file loop、Formal full build/移植、独立査読、CIはこの提案時点では未実施。
