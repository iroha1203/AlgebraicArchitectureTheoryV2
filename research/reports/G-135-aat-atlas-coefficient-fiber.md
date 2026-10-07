# G-135：固定targetの証拠対応

固定入力はtracking Issue [#5290](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5290)で指定した版を読む。
GOALは `dc6a46a993561233a824848c75ba547b23ddf863` の
`research/goals/G-135-aat-atlas-coefficient-fiber.md`、設計・共通基準は
`05d1c6c5cbdbb299d8d7120376135917b44f6fa1`、既存宣言は
`53b6a674a29807605a943b6f6304e7b17c2da0d6`。

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

## 宣言と固定要求の対応

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

## 検証記録

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
