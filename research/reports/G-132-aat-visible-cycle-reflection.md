# G-132：可視閉路による修復障害の零性反映

一次仕様は `dd4e86f56cc1b64db8dfaf7eb2b0ed8e8293198d` の
[固定GOAL](../goals/G-132-aat-visible-cycle-reflection.md) T0・A–C・W1–W3。
共通基準・設計は `75319c99f8732c1993142735460334dcaed2c170`、既存宣言は
`7547b0d1dc9d523e63c0e8596180dd61e6119529` を参照する。開始時main
`a6f239eea22be47f1adec5f7200b081ef8b23320` とcycle 3 base
`cdf08763d6f024287c82f1cea272ce1ce4a7af35` で参照対象のsource差分はない。

## Cycle 1 selection

```yaml
ledger_type: target_cycle_result
goal: G-132-aat-visible-cycle-reflection
cycle: 1
goal_blob_sha: 4fb28b116ddd9f9d98cc03834d03a0a68b1ba49d
base_oid: a6f239eea22be47f1adec5f7200b081ef8b23320
tracking_issue: 5250
report_path: research/reports/G-132-aat-visible-cycle-reflection.md
selection:
  proof_state_ref: 'Issue #5250: cycle 0, not-started'
  proof_dag_predecessors:
    - 'G-125 PR #4822 / #4825, reuse-map.md の型・適用条件'
  milestone: 'T0・A: 任意の原始入力と実被覆から continuous support と実Čech被覆を生成'
  proof_obligations:
    - point/generator Atom と原始関係の保持
    - interior support・product restriction・admissibility
    - generated topology に対する continuity
    - 全非空二重交差と完全な face index の空性
    - 既存 FaceEmptyAATCechCover への接続
  exit_criteria:
    - 任意のT0構造に対する生成構成をLeanで確認
    - 結論相当のcertificateを外部入力に追加しない
    - focused check・全宣言axiom・placeholder・Unicode・privacy・import scan
  selection_reason: Aの原始入力から既存比較へ至る最初の未接続部分を閉じる
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - ResearchLean/AG/VisibleCycleReflection/AtomInput.lean
    - ResearchLean/AG/VisibleCycleReflection/OpenSupport.lean
    - ResearchLean/AG/VisibleCycleReflection/OpenSupportContinuity.lean
    - ResearchLean/AG/VisibleCycleReflection/ActualCover.lean
  risks:
    - 特殊化された八点幾何を一般入力の証拠としない
    - face型の空性だけで幾何の完全性を代替しない
    - T_i と U_i を区別する
  unchecked:
    - 未実装のA座標同定・B・C・W1–W3
```

## Cycle 1 時点の全targetのproof obligation

Aの座標同定、既存比較の成分計算、B三条件の全方向、整数補正、状態層と貼り合わせ、
必要性の実入力、Cの停止探索と正確性、W1–W3は未証明。cycle 1 は全targetの完了判定ではない。
Formal への移植は未実施。Research 全体buildとローカル Formal 全体buildは実行しない。

## Cycle 1 の構成と宣言対応

受理対象の宣言一覧は次の57宣言である。自動生成されたfield・constructorも各module末尾の
`#assert_standard_axioms_only` の検査対象に入る。実装途中のcycle足場は残していない。

| ファイル | 固定targetへの対応 | 主要な構成・定理 |
| --- | --- | --- |
| `AtomInput.lean` | T0・Aのpoint/generator Atomと原始関係 | `atomCarrier`、`architectureObject`、`generator_relation_iff`、`generator_payload`、`point_not_related` |
| `OpenSupport.lean` | Aのopen context、restriction、product、被覆admissibility | `openContext`、`contextSupport_openContext`、`contextSupport_product`、`openContext_le`、`site`、`coverageFamily_admissible` |
| `OpenSupportContinuity.lean` | Aの生成topologyから導くcontinuity | `supportFunctor_preservesPullback`、`mapped_pullback_mem_open_topology`、`supportFunctor_isContinuous`、`contextOpenSupport` |
| `ActualCover.lean` | T0・Aの完全な実nerveと既存実Čech被覆 | `GeometricCover.Edge`、`Face`、`faceIsEmpty`、`edgeOfOverlap`、`edge_eq_of_endpoints`、`supportedNerve`、`coverage_admissible`、`actualCechCover` |

`OpenSupport`のsupportとcoverageはG-125の構成方法を任意入力へ一般化した新規構成である。
`ContextOpenSupport` と `FaceEmptyAATCechCover` は既存の型へ接続する。既存の八点空間・
固定presentation・共通代表条件の成立を一般入力へ持ち込んでいない。

### Material premise と使用先

| 入力／義務 | 分類 | 使用先と放電状況 |
| --- | --- | --- |
| 位相空間X、Source、Law、原始Rとラベル保存 | T0由来 | Atom carrierのLaw・値・R、contextの台、restrictionとsite。反映条件R_qは後段の係数同定で用いる |
| 開chart、非空有限ordered index、被覆 | T0由来 | `coverageFamily_admissible`のpoint coverageとgenerator patch選択に使用 |
| chart非空・連結、非空二重交差の連結 | T0由来 | `actualCechCover`の次数0・1のnonempty/preconnected instanceに使用。非空＋IsPreconnectedで連結を表示 |
| 相異なる三重交差の空性 | T0由来 | 完全な順序付きtriple indexの`faceIsEmpty`に使用 |
| T_iとその非空性 | T0由来 | `supportedNerve`の同じ幾何セルへ載せ、既存K1からT_i∩T_jを得る |
| supportの単調性、product保持、admissibility | 放電済み | 原始contextとinput coverから証明。continuityのpullback sieveに接続 |
| support continuity | 放電済み | `supportFunctor_isContinuous`から生成。外部certificateとして受け取らない |
| 実Čech被覆の全field | 放電済み | `actualCechCover`は実開集合とその包含から構成。全非空実交差の収載はEdgeの型、重複除去は`edge_eq_of_endpoints` |
| 実係数層と指定類、座標・商・既存比較の評価 | 未接続 | 既存型を適用する入口を構成した段階。Aの残義務として保持 |

依存経路は、T0原始入力 → Atom／architecture object → open context・actual restriction →
product-support／admissible cover → pullback sieve → continuous support →
完全実nerve → `FaceEmptyAATCechCover` である。
`GeometricCover`のfieldはT0の入力幾何だけであり、比較の単射性・potential・修復の存在を保持しない。

### Cycle 1 result（独立査読前のproposal）

```yaml
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: T0・Aのsite、continuous support、完全実nerve、actual Cech coverを任意入力から生成
  exit_criteria_status:
    - 構成と全fieldの生成をLeanで確認
    - focused elaborationと57宣言の公理監査を確認
    - GOAL・設計・共通基準は変更なし
  split_reason: none
  completion_candidate: no
  lean_artifacts: [AtomInput.lean, OpenSupport.lean, OpenSupportContinuity.lean, ActualCover.lean]
  evidence: [Spine declaration list, 各moduleの標準公理監査, 全57宣言のprint axioms]
  claim_mapping:
    theorem_names: [coverageFamily_admissible, supportFunctor_isContinuous, faceIsEmpty, actualCechCover]
    conjuncts:
      - point/generator Atom: architectureObjectとgenerator_relation_iff
      - 実台とcoverage: contextSupport_productとcoverageFamily_admissible
      - continuity: supportFunctor_isContinuous
      - 完全実nerveと既存被覆: EdgeとFaceとactualCechCover
    source_labels: [T0, Aの実被覆構成]
    undischarged_assumptions: []
    acceptance_point: 選定した実被覆構成の到達点。A全体・B・C・Wは未完
    port_status: unported
audits:
  premise_delta:
    discharged: [原始contextの台とproduct一致, coverageのadmissibility, 生成topologyのcontinuity, 完全face型の空性, actualCechCoverの全field]
    remaining: [Aの係数と座標と類の接続, B, C, W1–W3]
  certificate_provenance:
    discharged: [siteはpointとgeneratorのcoverageから生成, continuousはpullback sieveの開被覆像から証明, coverは入力の実開集合と包含から生成]
    unresolved: [選定範囲にはなし]
  proof_use:
    used: [原始RはAtomのrelation, chart被覆はcoverage, 非空性と連結性はcoverのinstance, tripleEmptyはfaceIsEmpty, target台はsupportedNerve]
    unused: [R_qとadequacyはA後段の係数比較に割り当て、cycle 1では使用しない]
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [4対象fileのfocused elaboration, 全57宣言のprint axioms, placeholderとUnicodeとprivacyとimport方向scan]
  blocking_findings: []
  next_obligation: Aの整数ラベル座標、可視block同定と既存比較の成分計算
```

検証環境はLean `v4.28.0`、mathlib `8f9d9cff6bd728b17a24e163c9402775d9e6a365`。
`GeneratorPresentation` と `FaceEmptyCechNormalization` の対象module buildは依存準備として成功。
対象4ファイルのfocused check、57宣言の`#print axioms`、各moduleの標準公理監査を実行した。
検出公理は`propext`、`Classical.choice`、`Quot.sound`のみ。
Research全体build、ローカルFormal全体build、Formalへの移植は実施していない。
PR査読とCIは別に確認し、結果をtracking Issueへ同期する。

### Spine declaration list

```text
AAT.AG.VisibleCycleReflection.AtomKind
AAT.AG.VisibleCycleReflection.atomCarrier
AAT.AG.VisibleCycleReflection.architectureObject
AAT.AG.VisibleCycleReflection.generator_relation_iff
AAT.AG.VisibleCycleReflection.generator_payload
AAT.AG.VisibleCycleReflection.point_not_related
AAT.AG.VisibleCycleReflection.OpenSupport.openContext
AAT.AG.VisibleCycleReflection.OpenSupport.openContext_reads_point
AAT.AG.VisibleCycleReflection.OpenSupport.openContext_reads_generator
AAT.AG.VisibleCycleReflection.OpenSupport.generatorSilentContext
AAT.AG.VisibleCycleReflection.OpenSupport.readablePointSet
AAT.AG.VisibleCycleReflection.OpenSupport.contextSupport
AAT.AG.VisibleCycleReflection.OpenSupport.readablePointSet_mono
AAT.AG.VisibleCycleReflection.OpenSupport.contextSupport_mono
AAT.AG.VisibleCycleReflection.OpenSupport.contextPreorder
AAT.AG.VisibleCycleReflection.OpenSupport.supportFunctor
AAT.AG.VisibleCycleReflection.OpenSupport.supportFunctor_obj
AAT.AG.VisibleCycleReflection.OpenSupport.contextSupport_openContext
AAT.AG.VisibleCycleReflection.OpenSupport.readablePointSet_product
AAT.AG.VisibleCycleReflection.OpenSupport.contextSupport_product
AAT.AG.VisibleCycleReflection.OpenSupport.supportFunctor_obj_product
AAT.AG.VisibleCycleReflection.OpenSupport.contextSupport_product_openContext
AAT.AG.VisibleCycleReflection.OpenSupport.openContextMorphism
AAT.AG.VisibleCycleReflection.OpenSupport.openContextMorphism_isRestriction
AAT.AG.VisibleCycleReflection.OpenSupport.openContext_le
AAT.AG.VisibleCycleReflection.OpenSupport.equationSystem
AAT.AG.VisibleCycleReflection.OpenSupport.signature
AAT.AG.VisibleCycleReflection.OpenSupport.coverageRequirements
AAT.AG.VisibleCycleReflection.OpenSupport.overlap
AAT.AG.VisibleCycleReflection.OpenSupport.site
AAT.AG.VisibleCycleReflection.OpenSupport.admissible_support_covers
AAT.AG.VisibleCycleReflection.OpenSupport.admissible_generator_reading
AAT.AG.VisibleCycleReflection.OpenSupport.generatorSilentContext_not_generator_visible
AAT.AG.VisibleCycleReflection.OpenSupport.coverageFamily
AAT.AG.VisibleCycleReflection.OpenSupport.coverageFamily_admissible
AAT.AG.VisibleCycleReflection.OpenSupport.contextPullbackCone
AAT.AG.VisibleCycleReflection.OpenSupport.contextPullbackConeIsLimit
AAT.AG.VisibleCycleReflection.OpenSupport.contextHasPullback
AAT.AG.VisibleCycleReflection.OpenSupport.supportMapPullbackConeIsLimit
AAT.AG.VisibleCycleReflection.OpenSupport.supportFunctor_preservesPullback
AAT.AG.VisibleCycleReflection.OpenSupport.mapped_pullback_mem_open_topology
AAT.AG.VisibleCycleReflection.OpenSupport.supportFunctor_isContinuous
AAT.AG.VisibleCycleReflection.OpenSupport.contextOpenSupport
AAT.AG.VisibleCycleReflection.OpenSupport.contextOpenSupport_obj_openContext
AAT.AG.VisibleCycleReflection.GeometricCover
AAT.AG.VisibleCycleReflection.GeometricCover.Edge
AAT.AG.VisibleCycleReflection.GeometricCover.Face
AAT.AG.VisibleCycleReflection.GeometricCover.faceIsEmpty
AAT.AG.VisibleCycleReflection.GeometricCover.nerve
AAT.AG.VisibleCycleReflection.GeometricCover.edgeOfOverlap
AAT.AG.VisibleCycleReflection.GeometricCover.edge_eq_of_endpoints
AAT.AG.VisibleCycleReflection.GeometricCover.overlap
AAT.AG.VisibleCycleReflection.GeometricCover.supportedNerve
AAT.AG.VisibleCycleReflection.GeometricCover.supportedNerveFaceIsEmpty
AAT.AG.VisibleCycleReflection.GeometricCover.supportedNerve_edgeSupport
AAT.AG.VisibleCycleReflection.GeometricCover.coverage_admissible
AAT.AG.VisibleCycleReflection.GeometricCover.actualCechCover
```

### Cycle 1 の査読対応

PR #5253 の初回固定head `0913eb1e9a91d9a10304cd29dadd4d457c81793b` を、
数学2本・Lean2本で独立査読した。数学Aの非中心F1は、supportのobject mapについて
公開正規化APIを使わず他moduleの定義をproof内で展開していた点である。
名指しされた `supportFunctor_obj`、`supportFunctor_obj_product`、
`contextOpenSupport_obj_openContext` を追加し、そのAPIを使用する証明へ切り替えた。
既存宣言の型と構成dataは維持する。rootの非中心F2はresult/監査schemaの記録不足であり、
上記のartifact・claim対応・auditsを追記した。proposalのstatusと選定範囲は変更しない。
修正後の直接対応確認と最終受理は固定headのPR監査コメントに記録する。

## Cycle 2 selection

```yaml
ledger_type: target_cycle_result
goal: G-132-aat-visible-cycle-reflection
cycle: 2
goal_blob_sha: 4fb28b116ddd9f9d98cc03834d03a0a68b1ba49d
base_oid: 14c8b9447ffa91773204a3a933d14e9542d6bab2
tracking_issue: 5250
report_path: research/reports/G-132-aat-visible-cycle-reflection.md
selection:
  proof_state_ref: 'cycle 1 accepted PR #5253 / Issue comment 5978402926'
  proof_dag_predecessors: [cycle 1の実被覆構成, G-125の係数商と実比較, G-104のlaw-value cochainとH1分解]
  milestone: 'A: 整数ラベル座標と可視グラフ複体を同定し、既存実比較の各成分を係数変更と制限へ接続'
  proof_obligations: [R_qから整数ラベル座標, 同じtargetの支持から可視cell生成, cochainと微分の同定, 商と代表元の同定, 既存指定類と独立診断の対応]
  exit_criteria: [全T0構造と全局所データへの既存実比較を同定, cochainだけでなくH1と指定代表を接続, focusedと全宣言公理と機械scan成功]
  selection_reason: 次のBの零性反映を実AAT入力へ接続する係数と比較の未接続部分を閉じる
  expected_result_type: proof-obligation-discharged
  lean_targets: [IntegralLabelCoordinates.lean, VisibleCoordinates.lean, CechGraphComparison.lean, GraphH1Comparison.lean]
  risks: [H1の単射性を係数単射から推論しない, 可視辺の同じtargetを保持, 診断を比較像として再定義しない, legacyとadditive H1を区別]
  unchecked: [実装中のAの全接続, 未選定BとCとW1–W3]
```

## Cycle 2 の構成と対応

R_qから原始presentationの関係blockをsource-generated labelへ同定し、自由アーベル群の
有限座標を合成した `integralLabelEquiv` が整数ラベル座標を与える。
`coefficientComparison_eq_cast` は既存係数比較の各値がこの整数座標の有理数埋め込みである
ことを示す。`labelBasis` は原始係数商への逆写像から作り、非零性を証明する。

`VisibleCell` は同じ台上のLaw値の発生を保持する。辺は既存K1のtarget交差台を使い、
端点で別のtargetが同ラベルを持つ条件へ置き換えない。既存blockのcell射影の単射性と発生
同値から `blockCellEquiv` を構成し、端点を保つこととcochainの微分対応を証明する。

| Aの条項 | 新しい接続と使用する既存API |
| --- | --- |
| M_R と整数ラベル座標 | `integralLabelEquiv`、`coefficientComparison_eq_cast`。G-125のpresentationGroupEquivBlocks、blockLabelEquiv、block係数評価を合成 |
| 可視頂点・同じtargetを要する可視辺 | `blockCellEquiv`、`visibleVertexEquiv`、`visibleEdgeEquiv`。G-104のblock_cell_injectiveとexists_block_coordinate_cell_iff |
| cochain・微分・空の次数2 | `actualIntegralCochain0/1/2Equiv`、`actualIntegral_d0/d1`、`visibleCochain0/1/2Equiv`、`visibleD0/D1_intertwining` |
| 整数障害の商と代表元 | `actualIntegral_range`、`actualIntegralH1Equiv_mk`、`existingDescent_graph_representative`、`actualMismatch_normalized` |
| 診断の商と各可視成分 | `visibleBlock_range`、`visibleBlockH1Equiv_mk`、`diagnosticVisibleH1Equiv_mk_component`。既存lawGeneratedH1BlockEquivを合成 |
| 既存比較の成分 | `actualCechDiagnosticH1Map_factorization` は全actual H1類の係数変更・制限の分解式 |
| 原始AAT入力・全局所データへの接続 | `GeometricCover.input_local_data_factorization` はcycle 1の実生成被覆で全ξ,pを量化し、既存descent類と独立診断へ上の分解を適用 |

既存診断の定義は変更していない。`existingDescent_comparison` は既存の独立した
transition評価＋状態の診断微分と、同じ原始入力のexisting descent類を接続する。
元の比較は加法準同型であり、有理線形同型やH1の単射性を主張しない。
有理potential、反映、閉路条件、整数補正、状態層、有限判定、指定例はcycle 2の結論に含めない。

### Material premise と proof-use

| premise | role | provenance と使用先 |
| --- | --- | --- |
| 有限Source・有限Law、adequate reading、ラベル保存RとR_q | ambient-boundary | T0。R_qはblockLabelEquivと整数係数回収、有限Sourceは全ラベルのfinite sumと有限自由座標、adequacyとsurj readingは発生ラベルと既存比較に使用 |
| 実被覆・非空連結chart/交差・三重交差空・非空target台 | ambient-boundary | cycle 1の生成構成を使用。実section正規化の条件は同じactual coverから得る。全face空性は次数2と全edge cochainのcocycle化へ使用 |
| 整数ラベル座標と基底 | discharge-required / discharged | 原始presentation→自由block→R_qのlabel同値→有限整数座標。基底はその逆写像で生成 |
| exact visible cell、端点、微分対応 | discharge-required / discharged | 台の発生とblockのcell射影。証人差は同一cell/labelの同値で消し、端点で同じtargetを保持 |
| 実cochain・商・比較同定 | discharge-required / discharged | 実section正規化→整数座標、d0対応→coboundary rangeの両方向等式→quotient同値→代表元計算 |
| 既存H1比較と独立診断の対応 | discharge-required / discharged | 既存actualCechDiagnosticH1Mapを代表元で追跡。整数castとvisible restrictionの独立な商写像を定義し等式を証明 |
| H1反映・全グラフpotential | discharge-required / remaining | Bの次義務。係数の単射性や今回のH1成分式から反映を推論していない |

再利用するG-104部分は同report cycle 11/14の `approve / proof-obligation-discharged` 記録と
PR #3943の受理記録へ接続する。G-104の後続の別claimの反証を、この二つのcoordinate/H1分解へ
取り違えない。参照版 `7547b0d1dc9d523e63c0e8596180dd61e6119529` のsource blobは
LawValueCoordinateSubnerve `16bd6ee8b9788fbad092c45222a56c7992a120f0`、
LawValueBlockCohomology `8dce9e67cc15ed46ebdbfa013306a1501596dd48`。
現sourceのstatement・必要条件・今回の適用を照合し、関連変更なしを確認する。

### Cycle 2 result（独立査読前のproposal）

```yaml
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: Aの整数ラベル座標、exact visible cell、cochainと微分、H1商と代表、既存実比較の係数変更と制限への分解を構成
  exit_criteria_status: [全T0構造の生成被覆と全局所データへ適用, 0–2 cochainと微分とH1商の同定, focusedと全82新宣言公理監査と機械scan]
  split_reason: none
  completion_candidate: no
  lean_artifacts: [IntegralLabelCoordinates.lean, VisibleCoordinates.lean, CechGraphComparison.lean, GraphH1Comparison.lean]
  evidence: [Cycle 2 spine declaration list, 実入力へのinput_local_data_factorization, 84宣言のprint axioms]
  claim_mapping:
    theorem_names: [integralLabelEquiv, blockCellEquiv, actualIntegral_d0, actualIntegralH1Equiv, visibleBlockH1Equiv, actualCechDiagnosticH1Map_factorization, GeometricCover.input_local_data_factorization]
    source_labels: [T0のラベルと可視部分, A]
    conjuncts: [係数同定と有理埋め込み, 全実cochainの正規化, 同じtargetの可視block, 微分と商の両方向対応, 全actualH1の比較成分式, 全ξとpの独立診断と既存descent類]
    undischarged_assumptions: []
    acceptance_point: 選定したAの比較同定。BとCとW1–W3は未完
    port_status: unported
audits:
  premise_delta:
    discharged: [原始関係から整数ラベル係数, 可視cellと端点, cochain微分, coboundary rangeの両方向対応, quotientとrepresentative, 既存比較の全類成分, 原始実入力への適用]
    remaining: [B全方向とpotentialと整数補正と状態層, C, W1–W3]
  certificate_provenance:
    discharged: [原始係数商とR_q, 既存K1台の発生, 同じ実coverとrestriction, 商写像のrange保存から生成]
    unresolved: [選定範囲にはなし]
  proof_use:
    used: [R_qのblock-label同値と係数回収, finiteSourceの座標とdirectsum, adequacyのLaw発生, 全face空性のcocycle化, 実d0正規化とvisible d0対応のrange等式, range等式のquotient同定, 元のactualCechDiagnosticH1Mapの代表元]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [対象4file focused elaboration, 全84宣言print axioms, 標準公理のみ, placeholderとUnicodeとprivacyとimport方向scan]
  blocking_findings: []
  next_obligation: Bの非橋辺とchain包含と零性反映の全方向、整数補正と状態層
```

全目標の現状態はAの構成・同定をcycle 2の受理proposalとして追加し、B・C・W1–W3を
未完として保持する。Formal移植はunported。Research全体build/aggregate elaborationと
ローカルFormal全体buildは実行しない。実入力適用定理は同じ構成への名前付き引数で接続し、標準の検証上限で確認する。

### Cycle 2 spine declaration list

```text
AAT.AG.VisibleCycleReflection.integralLabelEquiv
AAT.AG.VisibleCycleReflection.integralLabelEquiv_apply
AAT.AG.VisibleCycleReflection.coefficientComparison_eq_cast
AAT.AG.VisibleCycleReflection.labelBasis
AAT.AG.VisibleCycleReflection.integralLabelEquiv_labelBasis
AAT.AG.VisibleCycleReflection.labelBasis_ne_zero
AAT.AG.VisibleCycleReflection.coefficientComparison_labelBasis
AAT.AG.VisibleCycleReflection.VisibleCell
AAT.AG.VisibleCycleReflection.blockCellEquiv
AAT.AG.VisibleCycleReflection.blockCellEquiv_val
AAT.AG.VisibleCycleReflection.blockCellEquiv_symm_cell
AAT.AG.VisibleCycleReflection.VisibleVertex
AAT.AG.VisibleCycleReflection.VisibleEdge
AAT.AG.VisibleCycleReflection.visibleVertexEquiv
AAT.AG.VisibleCycleReflection.visibleEdgeEquiv
AAT.AG.VisibleCycleReflection.visibleVertexEquiv_symm_cell
AAT.AG.VisibleCycleReflection.visibleEdgeEquiv_symm_cell
AAT.AG.VisibleCycleReflection.visibleLeft
AAT.AG.VisibleCycleReflection.visibleRight
AAT.AG.VisibleCycleReflection.visibleLeft_val
AAT.AG.VisibleCycleReflection.visibleRight_val
AAT.AG.VisibleCycleReflection.visibleVertexEquiv_left
AAT.AG.VisibleCycleReflection.visibleVertexEquiv_right
AAT.AG.VisibleCycleReflection.visibleCochain0Equiv
AAT.AG.VisibleCycleReflection.visibleCochain1Equiv
AAT.AG.VisibleCycleReflection.visibleCochain0Equiv_apply
AAT.AG.VisibleCycleReflection.visibleCochain1Equiv_apply
AAT.AG.VisibleCycleReflection.visibleD0
AAT.AG.VisibleCycleReflection.visibleD0_apply
AAT.AG.VisibleCycleReflection.visibleD0_intertwining
AAT.AG.VisibleCycleReflection.integralGraphD0
AAT.AG.VisibleCycleReflection.integralGraphD0_apply
AAT.AG.VisibleCycleReflection.actualIntegralCochain0Equiv
AAT.AG.VisibleCycleReflection.actualIntegralCochain1Equiv
AAT.AG.VisibleCycleReflection.actualIntegralCochain2Equiv
AAT.AG.VisibleCycleReflection.actualIntegral_d1
AAT.AG.VisibleCycleReflection.actualCoefficient2_eq_zero
AAT.AG.VisibleCycleReflection.actualIntegralCochain0Equiv_apply
AAT.AG.VisibleCycleReflection.actualIntegralCochain1Equiv_apply
AAT.AG.VisibleCycleReflection.actualIntegral_d0
AAT.AG.VisibleCycleReflection.actualCoefficient0_apply
AAT.AG.VisibleCycleReflection.actualCoefficient1_apply
AAT.AG.VisibleCycleReflection.actualCoefficient0_visible
AAT.AG.VisibleCycleReflection.actualCoefficient1_visible
AAT.AG.VisibleCycleReflection.actualMismatch_normalized
AAT.AG.VisibleCycleReflection.existingDescent_comparison
AAT.AG.VisibleCycleReflection.IntegralGraphH1
AAT.AG.VisibleCycleReflection.actualIntegralCyclesEquiv
AAT.AG.VisibleCycleReflection.actualIntegralCyclesEquiv_apply
AAT.AG.VisibleCycleReflection.actualIntegral_range
AAT.AG.VisibleCycleReflection.actualIntegralH1Equiv
AAT.AG.VisibleCycleReflection.actualIntegralH1Equiv_mk
AAT.AG.VisibleCycleReflection.existingDescent_graph_representative
AAT.AG.VisibleCycleReflection.VisibleGraphH1
AAT.AG.VisibleCycleReflection.visibleBlockFaceIsEmpty
AAT.AG.VisibleCycleReflection.visibleBlockD1_eq_zero
AAT.AG.VisibleCycleReflection.visibleCochain2Equiv
AAT.AG.VisibleCycleReflection.visibleGraphComplex
AAT.AG.VisibleCycleReflection.visibleD1_intertwining
AAT.AG.VisibleCycleReflection.visibleBlockCyclesEquiv
AAT.AG.VisibleCycleReflection.visibleBlockCyclesEquiv_apply
AAT.AG.VisibleCycleReflection.visibleBlock_range
AAT.AG.VisibleCycleReflection.visibleBlockH1Equiv
AAT.AG.VisibleCycleReflection.visibleBlockH1Equiv_mk
AAT.AG.VisibleCycleReflection.rationalGraphD0
AAT.AG.VisibleCycleReflection.rationalGraphD0_apply
AAT.AG.VisibleCycleReflection.RationalGraphH1
AAT.AG.VisibleCycleReflection.graphCoefficientCast
AAT.AG.VisibleCycleReflection.graphCoefficientCast_apply
AAT.AG.VisibleCycleReflection.graphCoefficientCast_d0
AAT.AG.VisibleCycleReflection.integerToRationalH1
AAT.AG.VisibleCycleReflection.integerToRationalH1_mk
AAT.AG.VisibleCycleReflection.rationalRestriction1
AAT.AG.VisibleCycleReflection.rationalRestriction1_apply
AAT.AG.VisibleCycleReflection.rationalRestriction_d0
AAT.AG.VisibleCycleReflection.rationalRestrictionH1
AAT.AG.VisibleCycleReflection.rationalRestrictionH1_mk
AAT.AG.VisibleCycleReflection.diagnosticVisibleH1Equiv
AAT.AG.VisibleCycleReflection.diagnosticVisibleH1Equiv_component
AAT.AG.VisibleCycleReflection.diagnosticVisibleH1Equiv_mk_component
AAT.AG.VisibleCycleReflection.actualCechDiagnosticH1Map_factorization
AAT.AG.VisibleCycleReflection.GeometricCover.input_local_data_factorization
AAT.AG.ResolutionInvariance.TargetSupportedNerve.lawValueBlockD0_apply
AAT.AG.ObstructionDiagnosticBridge.GeneratorPresentation.ActualCechAffineLocalData.actualMismatch_eq
```

検証結果：対象4fileのfocused elaborationは成功（module標準公理監査は順に8・23・16・36宣言）。
全84明示宣言の `#print axioms` を実行し、source/report/list/outputの一致を確認した。
依存公理はpropext、Classical.choice、Quot.soundのみ。print出力SHA-256は
`e0d48691ed64bab0ae589d2b41ca4047f09a2a5061ef34200620347d1174622b`。
placeholder、hidden/BiDi、privacy、語彙、FormalからResearchへのimport方向、diff checkはclean。
固定GOAL・設計・共通基準・再利用sourceの関連差分なし。正式査読とCIはPRの固定headで確認する。

### Cycle 2 の非中心finding対応

初回4 laneの判定はMinor issues、中心findingなし。
[初回統合](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5254#issuecomment-5978705421)
のF1に対し、既存比較と整数H1同値の公開代表元APIを使用した。
既存block微分とaffine mismatchの公開評価／生成APIを2宣言補い、下流から使用する。
F2に対し、新4moduleのImplementation notesへ定義形の理由と代替案を記した。
査読済みsignature、def/instanceの値、import方向、ledger statusは変更していない。
全84宣言の公理監査は標準公理のみ。修正後の直接対応資格と解消を別途固定headで確認する。

## Cycle 3 selection

```yaml
ledger_type: target_cycle_result
goal: G-132-aat-visible-cycle-reflection
cycle: 3
goal_blob_sha: 4fb28b116ddd9f9d98cc03834d03a0a68b1ba49d
base_oid: cdf08763d6f024287c82f1cea272ce1ce4a7af35
tracking_issue: 5250
report_path: research/reports/G-132-aat-visible-cycle-reflection.md
selection:
  proof_state_ref: Issue cycle2受理 comment5978799427・PR5254最終監査comment5978791850
  proof_dag_predecessors: [cycle1の完全実nerveと生成被覆, cycle2の全実H1比較cast+res同定, G125整数floor補正]
  milestone: BのB1⇔B2⇔B3と同じ実入力の整数補正および任意不可視非橋辺の実失敗入力
  proof_obligations:
    - 完全な幾何nerveをMathlib SimpleGraphへ接続し順序付き辺を同定
    - 向き付きchain微分と可視部分のchain包含を構成
    - Mathlib IsBridgeと有限連結成分数増加による橋の一致
    - 橋における閉路chain係数零と非橋辺を一度通る閉路chain
    - H1 chain包含全射と全非橋辺可視の同値
    - 可視有理potentialから全グラフpotentialと整数補正を構成
    - 任意不可視非橋辺から零診断かつ非零既存障害の実切断データを構成
    - 全実ξ,pの零性反映とB2/B3の全方向およびp変更不変性
  exit_criteria:
    - B1/B2/B3を同じK/P/targetの任意T0実入力に適用した三条件同値
    - 仮定B2またはB3と診断零から実d0 n=ξ+d0 pを証明
    - 任意不可視非橋辺とラベルの単一辺基底実データ・閉路period非零・診断零
    - GOALの橋定義との一致と部分グラフchain写像を省かない
    - 全新宣言のfocused確認・公理監査・scanおよび独立査読
  selection_reason: Aの比較からBの全入力必要十分条件へ直接接続しpotentialを実整数補正へ戻す
  expected_result_type: proof-obligation-discharged
  lean_targets: [GraphChains.lean, GraphBridge.lean, VisibleCycleCriterion.lean, IntegralVisibleReflection.lean, ActualReflection.lean]
  risks: [橋と連結成分数の不一致, 同じtarget部分graph包含, 全実データ量化縮小, 有理potentialを全辺へ拡張せずfloor, 抽象graphだけで実入力省略]
  unchecked: [Bの未実装義務, 状態層は後続独立構成義務, C/W1–W3/最終completion未完]
```

状態層・局所自明化・大域貼り合わせは本cycleの同値・整数補正を使う後続の構成義務として保持する。
B全体やGOAL全体の完了は、この到達点だけでは認定しない。

## Cycle 3 の構成と対応

cycle 2は[最終監査](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5254#issuecomment-5978791850)
後に通常mergeされ、[Issue同期](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5250#issuecomment-5978799427)
で選定Aの受理を記録した。以下はcycle 3の新しい到達点である。

| GOALの条項 | 入力からの構成・証拠 | 宣言／使用先 |
| --- | --- | --- |
| 完全nerveから単純グラフ | 異なるchartの実交差を隣接とし全順序付き辺へ同定 | `GeometricCover.graph`, `graphEdgeEquiv` と両端点API |
| B2のchain写像 | 右端delta−左端deltaの有限線形incidence、部分集合のzero extension、次数0も可換 | `Graph.boundary`, `visibleBoundary_formula`, `boundary_zeroExtend_comm`, `h1Inclusion` |
| 橋の定義一致 | 削除→原graphの連結成分写像は全射、橋で非単射、非橋で単射 | `Graph.isBridge_iff_component_count` |
| B2⇔B3 | 橋cutのd0は単一辺delta、閉路係数は橋で零。非橋は削除後pathから一回閉路 | `cycle_bridge_coefficient`, `exists_once_cycle`, `h1Inclusion_surjective_iff_nonbridge_visible` |
| 可視potential→全辺potential | 零延長の残差は橋だけに支持され、有限cut和で補う | `Graph.d0_bridgePrimitive`, `exists_full_potential` |
| 整数補正 | 全辺差を証明してG125 floorを適用、整数座標と実切断同値の逆で戻す | `Graph.exists_integral_correction`, `GeometricCover.exists_actual_integral_correction` |
| B1の十分性・必要性 | 実生成coverの全ξ,p。零診断のpotentialと任意不可視非橋辺の実失敗入力 | `input_reflection_iff_nonbridge_visible`, `input_reflection_iff_homology_surjective` |
| 必要性の実入力 | 原始商基底を単一実辺の定数切断へ復元、p=0。独立診断cochain零・既存障害非零 | `singleEdgeData`, `singleEdgeData_transition_value`, `singleEdgeData_diagnostic_mismatch_zero`, `singleEdgeData_existing_nonzero` |
| 原始係数のperiod | 実transitionの評価を向きに従って加算、係数比較で標準chain pairingと一致 | `Graph.walkPeriod`, `map_walkPeriod`, `singleEdgeData_period`, `exists_actual_counterinput` |
| pのみの変更 | 任意二状態差を既存adjustLocalStateに戻し既存障害と独立診断の不変性 | `existingDescent_eq_of_transition_eq`, `diagnostic_eq_of_transition_eq` |

`GraphChains`・`GraphBridge`・`VisibleCycleCriterion`・`IntegralVisibleReflection`は
独立に再利用できる有限単純グラフの補題。`ActualReflection`と`ActualCounterinput`は
同じ原始P、K、targetから生成した実AAT入力への接続を担う。原始値のperiodを
有理観測だけで代替しないため、内部依存として`GraphPeriods`を追加した。
選定milestone・終了条件・量化は変更していない。

G125の`IntegralReflection.exists_integral_correction`は、指定predecessorからsource差分なし、
blob `c862d40514cc988a878db98f4189b1c64dca6dc0`。実際の前提は全辺で整数差に等しい
有理potentialであり、本cycleの全辺拡張の後で使用する。
共通代表条件を要するG125の反映定理は使用しない。

### Cycle 3 material premise と proof-use

| premise | 分類・出所 | 使用・放電 |
| --- | --- | --- |
| Source/Lawの有限性・adequate reading・原始R・Rq | ambient-boundary / T0 | cycle2整数座標と原始basis、独立Law診断、全実入力に適用 |
| I有限・順序と実被覆K、target台 | ambient-boundary / T0 | 全実隣接と向き・有限chain和・成分数比較。targetは先に固定 |
| generic部分集合の端点閉性 | direction-hypothesis / subgraph入力 | 実適用では`visibleEdge_left/right`が同じedgeSupportのtargetから放電 |
| B2/B3 | direction-hypothesis / GOAL B | 一般十分性だけで保持し、全実反映から任意単一辺反例でB3を導出 |
| 可視有理potential | discharge-required | 診断quotient零からrange証人、既存比較factorizationで生成 |
| 全有理potential・整数補正 | discharge-required | 橋のcut和→全辺式→既存floor→actual切断inverse |
| 原始係数period・実失敗入力 | discharge-required | basis・actual section inverse・mathlib deleted-edge path→simple cycle→period非零 |
| face空性・continuous support・実restriction | discharge-required / A | cycle1の同じ完全実coverから供給、cycle2の比較と正規化を使用 |

### Cycle 3 result（独立査読前のproposal）

```yaml
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: B2/B3の全方向と橋定義一致から同じ実入力のB1全量化・整数補正・任意単一辺失敗入力へ接続
  exit_criteria_status:
    - B1⇔B2⇔B3: input_reflection_iff_nonbridge_visible / input_reflection_iff_homology_surjective / input_homology_iff_nonbridge_visible
    - 実整数補正: exists_actual_integral_correction
    - 不可視非橋辺の実失敗入力と一回閉路period: exists_actual_counterinput
    - 橋定義とchain写像: isBridge_iff_component_count / boundary_zeroExtend_comm
    - 検証と査読: fixed headのfocused・全明示宣言print・scans、標準4laneはPR後
  split_reason: none
  completion_candidate: no
  lean_artifacts: [GraphChains.lean, GraphBridge.lean, VisibleCycleCriterion.lean, IntegralVisibleReflection.lean, GraphPeriods.lean, ActualReflection.lean, ActualCounterinput.lean]
  evidence: [以下のcycle3 spine declaration listと上表の条項接続]
  claim_mapping:
    theorem_names: [input_reflection_iff_nonbridge_visible, input_reflection_iff_homology_surjective, exists_actual_integral_correction, exists_actual_counterinput]
    source_labels: [T0, B1, B2, B3, B整数補正, B必要性実入力, B状態変更不変性]
    conjuncts: [全actual ξ/pでの反映, chain包含全射, 非橋辺可視, actual整数補正, 単一辺actual基底と一回閉路, 独立診断零と既存障害非零]
    undischarged_assumptions: []
    acceptance_point: 選定到達点を全方向と同じ実入力への接続まで証明したproposal
    port_status: unported
audits:
  premise_delta:
    discharged: [端点閉性, 橋と成分数定義の一致, 全有理potential, actual整数補正, 任意単一辺actual入力とperiod, B1からB3必要性]
    remaining: [B状態層と局所自明化・gluing, C有限表と探索, W1–W3]
  certificate_provenance:
    discharged: [Raw K/P/target→graph/visible subsets→chain inclusion, independent診断零→potential→floor→actual切断, basis→単一actual辺→deleted-edge path→period]
    unresolved: []
  proof_use:
    used: [Rqとbasis/整数座標, adequacyと同じtarget発生, 有限Iとchain和/成分数, B3と橋残差, 完全face空性と全transition, 既存比較とdescent対応]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [対象7fileのfocused, 全123明示新宣言のprint axioms, scans, PR固定headのCI]
  blocking_findings: []
  next_obligation: Bのアフィン状態層・局所自明化・actual gluing、続いてCとW1–W3
```

Bの状態層・局所自明化・自由かつ推移的な作用・大域状態の非空性との同値は
未完。C、W1–W3、Formal移植、独立全GOALcompletion判定も未完。
本cycleの成功だけで全目標を完了としない。

### Cycle 3 spine declaration list

```text
AAT.AG.VisibleCycleReflection.Graph.Edge
AAT.AG.VisibleCycleReflection.Graph.edgeFintype
AAT.AG.VisibleCycleReflection.Graph.left
AAT.AG.VisibleCycleReflection.Graph.right
AAT.AG.VisibleCycleReflection.Graph.unoriented
AAT.AG.VisibleCycleReflection.Graph.left_lt_right
AAT.AG.VisibleCycleReflection.Graph.adj
AAT.AG.VisibleCycleReflection.Graph.edge_ext
AAT.AG.VisibleCycleReflection.Graph.vertexUnit
AAT.AG.VisibleCycleReflection.Graph.edgeUnit
AAT.AG.VisibleCycleReflection.Graph.vertexUnit_apply
AAT.AG.VisibleCycleReflection.Graph.edgeUnit_apply
AAT.AG.VisibleCycleReflection.Graph.boundary
AAT.AG.VisibleCycleReflection.Graph.boundary_apply
AAT.AG.VisibleCycleReflection.Graph.boundary_edgeUnit
AAT.AG.VisibleCycleReflection.Graph.H1
AAT.AG.VisibleCycleReflection.Graph.d0
AAT.AG.VisibleCycleReflection.Graph.d0_apply
AAT.AG.VisibleCycleReflection.Graph.hopChain
AAT.AG.VisibleCycleReflection.Graph.hopChain_of_lt
AAT.AG.VisibleCycleReflection.Graph.hopChain_of_not_lt
AAT.AG.VisibleCycleReflection.Graph.boundary_hopChain
AAT.AG.VisibleCycleReflection.Graph.walkChain
AAT.AG.VisibleCycleReflection.Graph.walkChain_nil
AAT.AG.VisibleCycleReflection.Graph.walkChain_cons
AAT.AG.VisibleCycleReflection.Graph.boundary_walkChain
AAT.AG.VisibleCycleReflection.Graph.boundary_pairing
AAT.AG.VisibleCycleReflection.Graph.cycle_pairing_d0
AAT.AG.VisibleCycleReflection.Graph.hopChain_eq_zero
AAT.AG.VisibleCycleReflection.Graph.walkChain_eq_zero
AAT.AG.VisibleCycleReflection.Graph.closedWalkH1
AAT.AG.VisibleCycleReflection.GeometricCover.graph
AAT.AG.VisibleCycleReflection.GeometricCover.graph_adj
AAT.AG.VisibleCycleReflection.GeometricCover.graphEdgeEquiv
AAT.AG.VisibleCycleReflection.GeometricCover.graphEdgeEquiv_left
AAT.AG.VisibleCycleReflection.GeometricCover.graphEdgeEquiv_right
AAT.AG.VisibleCycleReflection.Graph.unoriented_injective
AAT.AG.VisibleCycleReflection.Graph.withoutEdge
AAT.AG.VisibleCycleReflection.Graph.withoutEdge_adj
AAT.AG.VisibleCycleReflection.Graph.withoutEdge_le
AAT.AG.VisibleCycleReflection.Graph.isBridge_iff_not_reachable
AAT.AG.VisibleCycleReflection.Graph.other_edge_reachable
AAT.AG.VisibleCycleReflection.Graph.cutPotential
AAT.AG.VisibleCycleReflection.Graph.cutPotential_apply
AAT.AG.VisibleCycleReflection.Graph.cutPotential_eq_of_reachable
AAT.AG.VisibleCycleReflection.Graph.d0_cutPotential
AAT.AG.VisibleCycleReflection.Graph.cycle_bridge_coefficient
AAT.AG.VisibleCycleReflection.Graph.exists_once_cycle
AAT.AG.VisibleCycleReflection.Graph.reachable_withoutEdge_of_endpoints
AAT.AG.VisibleCycleReflection.Graph.componentMap
AAT.AG.VisibleCycleReflection.Graph.componentMap_mk
AAT.AG.VisibleCycleReflection.Graph.componentMap_surjective
AAT.AG.VisibleCycleReflection.Graph.componentMap_injective_of_not_bridge
AAT.AG.VisibleCycleReflection.Graph.componentMap_not_injective_of_bridge
AAT.AG.VisibleCycleReflection.Graph.isBridge_iff_component_count
AAT.AG.VisibleCycleReflection.zeroExtend
AAT.AG.VisibleCycleReflection.zeroExtend_mem
AAT.AG.VisibleCycleReflection.zeroExtend_not_mem
AAT.AG.VisibleCycleReflection.sum_zeroExtend
AAT.AG.VisibleCycleReflection.Graph.visibleBoundary
AAT.AG.VisibleCycleReflection.Graph.visibleBoundary_apply
AAT.AG.VisibleCycleReflection.Graph.visibleBoundary_formula
AAT.AG.VisibleCycleReflection.Graph.boundary_zeroExtend_outside
AAT.AG.VisibleCycleReflection.Graph.boundary_zeroExtend_comm
AAT.AG.VisibleCycleReflection.Graph.VisibleH1
AAT.AG.VisibleCycleReflection.Graph.h1Inclusion
AAT.AG.VisibleCycleReflection.Graph.h1Inclusion_val
AAT.AG.VisibleCycleReflection.Graph.h1Inclusion_outside
AAT.AG.VisibleCycleReflection.Graph.h1Inclusion_surjective_iff
AAT.AG.VisibleCycleReflection.Graph.h1Inclusion_surjective_iff_nonbridge_visible
AAT.AG.VisibleCycleReflection.Graph.bridgePrimitive
AAT.AG.VisibleCycleReflection.Graph.bridgePrimitive_apply
AAT.AG.VisibleCycleReflection.Graph.d0_bridgePrimitive
AAT.AG.VisibleCycleReflection.Graph.visibleD0
AAT.AG.VisibleCycleReflection.Graph.visibleD0_apply
AAT.AG.VisibleCycleReflection.Graph.d0_zeroExtend_visible
AAT.AG.VisibleCycleReflection.Graph.exists_full_potential
AAT.AG.VisibleCycleReflection.Graph.exists_integral_correction
AAT.AG.VisibleCycleReflection.Graph.hopValue
AAT.AG.VisibleCycleReflection.Graph.walkPeriod
AAT.AG.VisibleCycleReflection.Graph.walkPeriod_nil
AAT.AG.VisibleCycleReflection.Graph.walkPeriod_cons
AAT.AG.VisibleCycleReflection.Graph.hopValue_vertex_difference
AAT.AG.VisibleCycleReflection.Graph.walkPeriod_vertex_difference
AAT.AG.VisibleCycleReflection.Graph.map_hopValue
AAT.AG.VisibleCycleReflection.Graph.map_walkPeriod
AAT.AG.ObstructionDiagnosticBridge.GeneratorPresentation.ActualCechAffineLocalData.actualClass_generation
AAT.AG.ObstructionDiagnosticBridge.GeneratorPresentation.ActualCechAffineLocalData.actualCocycle_value
AAT.AG.ObstructionDiagnosticBridge.GeneratorPresentation.ActualCechAffineLocalData.adjustLocalState_generation
AAT.AG.ObstructionDiagnosticBridge.GeneratorPresentation.ActualCechAffineLocalData.existingDescent_zero_iff_correction
AAT.AG.ObstructionDiagnosticBridge.GeneratorPresentation.ActualCechAffineLocalData.existingDescent_eq_of_transition_eq
AAT.AG.ObstructionDiagnosticBridge.GeneratorPresentation.ActualCechAffineLocalData.diagnostic_eq_of_transition_eq
AAT.AG.VisibleCycleReflection.GeometricCover.visibleVertexSet
AAT.AG.VisibleCycleReflection.GeometricCover.visibleEdgeSet
AAT.AG.VisibleCycleReflection.GeometricCover.visibleEdge_left
AAT.AG.VisibleCycleReflection.GeometricCover.visibleEdge_right
AAT.AG.VisibleCycleReflection.GeometricCover.actualVisibleEdgeEquiv
AAT.AG.VisibleCycleReflection.GeometricCover.actualVisibleEdgeEquiv_val
AAT.AG.VisibleCycleReflection.GeometricCover.visible_d0_actual
AAT.AG.VisibleCycleReflection.GeometricCover.graphMismatch
AAT.AG.VisibleCycleReflection.GeometricCover.graphMismatch_apply
AAT.AG.VisibleCycleReflection.GeometricCover.visible_potentials_of_diagnostic_zero
AAT.AG.VisibleCycleReflection.GeometricCover.exists_actual_integral_correction
AAT.AG.VisibleCycleReflection.GeometricCover.input_reflection_of_nonbridge_visible
AAT.AG.VisibleCycleReflection.GeometricCover.input_homology_iff_nonbridge_visible
AAT.AG.ObstructionDiagnosticBridge.GeneratorPresentation.ActualCechAffineLocalData.diagnosticClass_generation
AAT.AG.ObstructionDiagnosticBridge.GeneratorPresentation.ActualCechAffineLocalData.diagnosticCocycle_value
AAT.AG.ObstructionDiagnosticBridge.GeneratorPresentation.ActualCechAffineLocalData.diagnosticClass_zero_of_mismatch_zero
AAT.AG.VisibleCycleReflection.GeometricCover.singleEdgeData
AAT.AG.VisibleCycleReflection.GeometricCover.singleEdgeData_transition
AAT.AG.VisibleCycleReflection.GeometricCover.singleEdgeData_localState
AAT.AG.VisibleCycleReflection.GeometricCover.singleEdgeData_transition_value
AAT.AG.VisibleCycleReflection.GeometricCover.singleEdgeData_mismatch
AAT.AG.VisibleCycleReflection.GeometricCover.singleEdgeData_normalized
AAT.AG.VisibleCycleReflection.GeometricCover.singleEdgeData_diagnostic_mismatch_zero
AAT.AG.VisibleCycleReflection.GeometricCover.singleEdgeData_diagnostic_zero
AAT.AG.VisibleCycleReflection.GeometricCover.actualTransitionPeriod
AAT.AG.VisibleCycleReflection.GeometricCover.actualTransitionPeriod_apply
AAT.AG.VisibleCycleReflection.GeometricCover.singleEdgeData_period
AAT.AG.VisibleCycleReflection.GeometricCover.singleEdgeData_existing_nonzero
AAT.AG.VisibleCycleReflection.GeometricCover.exists_actual_counterinput
AAT.AG.VisibleCycleReflection.GeometricCover.input_reflection_iff_nonbridge_visible
AAT.AG.VisibleCycleReflection.GeometricCover.input_reflection_iff_homology_surjective
```

Cycle 3検証：7対象fileのfocused elaborationは成功。namespace標準公理監査は
GraphChains 36、GraphBridge 19、VisibleCycleCriterion 15、IntegralVisibleReflection 8、
GraphPeriods 9、ActualReflection 13、ActualCounterinput 18。生成内部宣言と別owner namespaceの
基本APIの扱いが異なるため、この件数は明示spine宣言の単純和ではない。
明示123新宣言（元namespaceの9基本APIを含む）のsource/report/list/実print出力は全件一致し、
標準3公理のみ。実print出力SHA256 `462689d218b6dda326675379479e067c948defd11cf2fb1b81d822d750e84750`。
全7新moduleをmanifestとAG importに登録し、aggregateはelaborateしない。
placeholder/hidden/BiDi/privacy/語彙/diff/import方向scanはclean。
Research import gateは228modulesを静的に走査して成功。
G125 IntegralReflectionのみのtargeted module check成功（3701jobs、全体buildではない）。
Research full/aggregateおよびローカルFormal full buildは不実行。
正式4laneとCIはPRの固定headで確認する。

### Cycle 3 初回査読と非中心API修正

[初回正式監査](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5255#issuecomment-5979282446)
はhead `ae3ceee1b1fd26487a758c4f59ec2d817a540954` を4laneで確認した。
数学BはNo major findings、数学A・LeanA/Bは同じ非中心F1のみでMinor issues。
中心claimのstatement強度・全入力・premise放電・実入力provenanceにfindingはない。
F1はGraphBridge/GraphPeriodsで他moduleの`hopChain`を展開するAPI欠落である。
名指しされた順序別公開API `hopChain_of_lt` / `hopChain_of_not_lt` だけをGraphChainsへ追加し、
指摘された2consumerを置換した。既存statementとdef/instance値・import・statusは維持する。
修正対象3fileと実入力topのfocused確認は成功し、全123明示宣言の公理監査は標準3公理のみ。
直接対応の資格・解消は新しい単一確認subagentが固定headで判定する。

## Cycle 4 selection

Cycle 3は[最終acceptance](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5255#issuecomment-5979341521)
を経て通常merge `12a84121c9489bfb467b769e586d567c7f08a136`、
[Issue同期](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5250#issuecomment-5979351345)
で選定B1/B2/B3・実整数補正・必要性を受理した。停止条件はない。

```yaml
ledger_type: target_cycle_result
goal: G-132-aat-visible-cycle-reflection
cycle: 4
goal_blob_sha: 4fb28b116ddd9f9d98cc03834d03a0a68b1ba49d
base_oid: 12a84121c9489bfb467b769e586d567c7f08a136
tracking_issue: 5250
report_path: research/reports/G-132-aat-visible-cycle-reflection.md
selection:
  proof_state_ref: Issue cycle3受理 comment5979351345・PR5255最終監査comment5979341521
  proof_dag_predecessors: [cycle1の生成siteとcontinuous support, cycle2の実切断正規化, cycle3のactual整数補正と既存障害零同値]
  milestone: Bの原始アフィン遷移から状態層・局所自明化・自由推移作用と実一意gluingを構成し零障害/実補正/大域状態を同値にする
  proof_obligations:
    - 任意実整数遷移から自己0・逆向き負・空交差0の遷移を生成しT0からpointwise cocycleを証明
    - 同じ原始PresentationGroupのアフィンfiberとrestriction付き状態presheafを構成
    - 係数の局所定数性からsheaf条件を証明し全chartで局所自明化と両逆を構成
    - 各chartの係数層作用が自由かつ推移的でrestrictionと可換することを証明
    - 同じproved continuous supportから状態層をAAT siteへ引き戻す
    - 実correction後のp-nが同じ遷移を通して一致し一意global stateへ貼り合うことを証明
    - global stateから実chart状態rとn=p-rを回収しd0n=ξ+d0pを証明
    - 既存障害零/actual correction存在/同じ状態層のglobal section非空の全方向を証明
  exit_criteria:
    - 状態層/sheaf条件/局所自明化/自由推移作用は原始ξとT0から生成し結論相当fieldを受け取らない
    - topologyとAAT siteの同じsupport/restrictionに実gluingを接続
    - 任意実ξ,pと各actual correctionのp-n localrepresentationを持つunique global state
    - zero obstruction/correction/global stateの同値とcycle3診断反映条件の適用
    - 全新宣言のfocused・print axioms・scans・独立PR査読
  selection_reason: cycle3の実整数補正から残るB状態層と実貼り合わせを放電してB全体を閉じる
  expected_result_type: proof-obligation-discharged
  lean_targets: [AffineTransition.lean, AffineFibers.lean, AffineStateSheaf.lean, ActualStateGluing.lean, AATStateSheaf.lean]
  risks: [global nonemptyのfield escape, 通常係数restrictionとaffine transitionの混同, 原始係数をラベル観測で代替, 実p-nとglobalstateの未接続, T0cocycleの供給化]
  unchecked: [B状態層の未実装義務, C有限表と探索, W1–W3, 全GOALcompletion]
```

固定GOAL・設計・共通基準を変更せず、CとW1–W3は本cycle後の義務として保持する。


### Cycle 4 implementation and premise correspondence

実際の任意整数遷移`ξ`から、幾何的交差が空なら零、自己は零、逆向きは負という
`transitionValue`を生成する。T0の三重交差空性から、各点で三chartの少なくとも二つが
一致することを証明し、pointwise cocycleを導く。一般`AffineAtlas`のcocycle fieldは
この構成で放電する。遷移は元の実辺切断の任意点での値と一致する。

各点のfiberは、その点を含む全chartの互換な原始`PresentationGroup`座標である。
任意の一chartの任意係数からfiberを生成し、座標同値の両逆を証明する。
各chartの局所定数座標というprelocal predicateをMathlibのsheafificationへ渡し、
`TopCat.subsheafToTypes`からrestrictionを持つ状態層を構成する。各chart内でその
sectionが局所定数係数に同値なことを証明し、係数の点ごとの加法作用が自由かつ
推移的でrestrictionと可換する。大域stateの存在をrecord fieldへ入れていない。

同じcycle 1のcontinuous supportで状態層を元のAAT siteへ引き戻す。
`aatLocalTrivialization`のtargetは既存の原始係数層であり、その作用・局所自明化は
元の係数restrictionおよび状態restrictionと可換する。実base/chartのsupport同値は
fiber値とrestrictionを保存する明示transportとして実装する。

任意の実補正`n`について`d0(p-n)=-ξ`を元のactual differentialから導き、各点で
元の実sectionと一致するchart表示をMathlibの状態層の一意gluingへ渡す。
`aat_corrected_gluing`は元のAAT chart inclusionを通る`p-n`表示を持つ大域切断の
存在と一意性を証明する。逆方向では、大域状態のchart座標をconnectednessで定数化し、
元の実cochain同値の逆から`r`を回収して`n=p-r`のactual mismatch式を証明する。
この両方向により既存障害零・実補正存在・同じAAT大域状態非空を同値にする。
cycle 3のB3からの整数補正を適用して、独立診断零から実補正と一意gluingを得る。

当初5fileの到達点を維持し、実cochainへの逆接続を内部依存`ActualStateRepair.lean`
へ分けた6fileとして実装した。終了条件の縮小・cycle途中分割は行っていない。

| material premise | 分類 | 生成・使用と証拠 |
| --- | --- | --- |
| 任意のP、K、独立target台と全ξ,p | ambient-boundary | 固定T0、actualAffineAtlasと全actual local dataへの定理 |
| 自己・逆向き・pointwise cocycle | discharge-required | transitionValue_self/reverse/cocycle、index_eq_of_mem_three、atlasFromCochain |
| fiber非空と全chart座標の互換性 | discharge-required | fiberFromCoordinate/fiberEquiv、T0 coverからfiber_nonempty |
| 状態sheaf条件と局所自明化の両逆 | discharge-required | statePrelocal/sheafify/subsheafToTypes、coordinates_locallyConstant、localTrivialization |
| 既存係数sheafの自由推移作用とrestriction | discharge-required | existsUnique_translateSection、existsUnique_aatTranslateSection、aatTranslateSection_restriction、aatLocalTrivialization_restriction |
| AAT状態sheaf条件 | discharge-required | 受理cycle 1のcontinuous supportへstateSheafを渡すaatStatePresheaf_isSheaf |
| 実補正後のcompatibilityと一意gluing | discharge-required | actual_corrected_d0/compatibility、existsUnique_gluing_chart_coordinates、aat_corrected_gluing |
| 大域状態からの実補正 | discharge-required | stateChartValue_eq/edge、actualStateFromGlobal_d0、actualCorrectionFromGlobal_d0 |
| 元の障害/補正/大域状態同値 | discharge-required | existingDescent_zero_iff_correction受理APIとcorrection_iff_aat_global_state、existingDescent_zero_iff_aat_global_state |
| B3と診断零 | direction-hypothesis | exists_actual_repair_and_aat_gluing、diagnostic_zero_iff_aat_global_stateがcycle 3のactual補正・反映を使用 |

構成上の依存は、受理cycle 1 PR5253・cycle 2 PR5254・cycle 3 PR5255のsourceと
受理refを上記cycle節で固定する。今回使用するstatementと入力は、原始係数、同じactual
cover/support、`existingDescent_zero_iff_correction`、`exists_actual_integral_correction`、
`input_reflection_of_nonbridge_visible`であり、全ξ,pへの型とproof-useを確認した。
標準基盤は固定mathlib `8f9d9cff6bd728b17a24e163c9402775d9e6a365`の
`TopCat.PrelocalPredicate.sheafify`、`TopCat.subsheafToTypes`、
`Sheaf.existsUnique_gluing'`、局所定数・開集合のcontinuous embeddingのAPIである。
それらの適用条件は本cycleのpredicate、patch covering、局所compatibilityから放電する。

### Cycle 4 result（独立査読前のproposal）

```yaml
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: Bの原始ξからの状態層/局所自明化/係数作用/実一意gluing/零障害と修復と大域状態の全同値を構成
  exit_criteria_status: [全ξからcocycleと状態sheaf生成, 原始係数の自由推移作用とrestriction, 同じAAT supportからstate sheafと元inclusionの実gluing, 各actual修復のp-nの一意globalstate, globalstateから実修復と全同値, cycle3診断反映から修復gluing, focusedと全114新宣言print公理と機械scan]
  split_reason: none
  completion_candidate: no
  lean_artifacts: [AffineTransition.lean, AffineFibers.lean, AffineStateSheaf.lean, ActualStateGluing.lean, ActualStateRepair.lean, AATStateSheaf.lean]
  evidence: [Cycle 4 spine declaration list, aat_corrected_gluing, existingDescent_zero_iff_aat_global_state, exists_actual_repair_and_aat_gluing, diagnostic_zero_iff_aat_global_state]
  claim_mapping:
    theorem_names: [actualAffineAtlas, stateSheaf, localTrivialization, existsUnique_translateSection, aatStateSheaf, aatLocalTrivialization, existsUnique_aatTranslateSection, aat_corrected_gluing, correction_iff_aat_global_state, existingDescent_zero_iff_aat_global_state, exists_actual_repair_and_aat_gluing]
    source_labels: [T0の全実局所データ, Bの状態層と実貼り合わせと存在同値]
    conjuncts: [原始遷移からsheafと全chart局所自明化, 原始係数作用の自由推移性, 元AAT supportとrestrictionへ接続, 全actual補正のp-n一意gluing, 全actual大域stateから元整数修復, 障害零と修復とglobal非空の同値, cycle3診断から修復とgluing]
    undischarged_assumptions: []
    acceptance_point: 選定B状態層と実gluing。CとW1–W3と全GOAL独立completionは未完
    port_status: unported
audits:
  premise_delta:
    discharged: [入力からaffine cocycle, fiber構成とchart同値, 局所定数state sheaf, 係数層自由推移作用, AAT連続supportの引き戻し, p-n互換性と元AAT inclusionの一意gluing, globalstateからactual修復, 零障害/修復/global非空の全方向]
    remaining: [C有限表と探索, W1–W3, 独立全GOALcompletion]
  certificate_provenance:
    discharged: [任意actualξとT0三重空性, 同じ原始PresentationGroup, locallyconstant predicate, 同じcycle1 actualsupport, 任意actual補正と元のd0, 任意globalstateとconnected chartから実cochain inverse]
    unresolved: [選定範囲にはなし]
  proof_use:
    used: [tripleEmptyのpointwise cocycle, chart coveringのfiber生成とsheaf gluing, locallyconstant/preconnectedによる両方向chart表示, support.continuousのAAT sheaf, actuald0とmismatchのp-n互換性, globalstate chart値の元actual inverse, cycle3整数補正と障害零同値]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [新6file focused成功, 全114明示宣言print公理は標準3公理のみ, placeholder/Unicode/privacy/語彙/diff/import方向scan]
  blocking_findings: []
  next_obligation: Cの有限表T0検証/復号/停止探索/成功同値/同表の実失敗証拠、W1–W3、独立全GOALcompletion
```

### Cycle 4 spine declaration list

```text
AAT.AG.VisibleCycleReflection.AffineAtlas
AAT.AG.VisibleCycleReflection.GeometricCover.transitionValue
AAT.AG.VisibleCycleReflection.GeometricCover.transitionValue_forward
AAT.AG.VisibleCycleReflection.GeometricCover.transitionValue_self
AAT.AG.VisibleCycleReflection.GeometricCover.transitionValue_reverse
AAT.AG.VisibleCycleReflection.GeometricCover.transitionValue_empty
AAT.AG.VisibleCycleReflection.GeometricCover.not_mem_three
AAT.AG.VisibleCycleReflection.GeometricCover.index_eq_of_mem_three
AAT.AG.VisibleCycleReflection.GeometricCover.transitionValue_cocycle
AAT.AG.VisibleCycleReflection.GeometricCover.atlasFromCochain
AAT.AG.VisibleCycleReflection.GeometricCover.actualAffineAtlas
AAT.AG.VisibleCycleReflection.GeometricCover.actualAffineAtlas_patch
AAT.AG.VisibleCycleReflection.GeometricCover.actualAffineAtlas_transition
AAT.AG.VisibleCycleReflection.AffineAtlas.Fiber
AAT.AG.VisibleCycleReflection.AffineAtlas.coordinate
AAT.AG.VisibleCycleReflection.AffineAtlas.coordinate_change
AAT.AG.VisibleCycleReflection.AffineAtlas.fiberFromCoordinate
AAT.AG.VisibleCycleReflection.AffineAtlas.coordinate_fiberFromCoordinate
AAT.AG.VisibleCycleReflection.AffineAtlas.fiberEquiv
AAT.AG.VisibleCycleReflection.AffineAtlas.fiberEquiv_apply
AAT.AG.VisibleCycleReflection.AffineAtlas.fiberEquiv_symm_apply
AAT.AG.VisibleCycleReflection.AffineAtlas.fiber_ext
AAT.AG.VisibleCycleReflection.AffineAtlas.fiber_nonempty
AAT.AG.VisibleCycleReflection.AffineAtlas.translateFiber
AAT.AG.VisibleCycleReflection.AffineAtlas.coordinate_translateFiber
AAT.AG.VisibleCycleReflection.AffineAtlas.translateFiber_zero
AAT.AG.VisibleCycleReflection.AffineAtlas.translateFiber_add
AAT.AG.VisibleCycleReflection.AffineAtlas.existsUnique_translateFiber
AAT.AG.VisibleCycleReflection.AffineAtlas.coordinates
AAT.AG.VisibleCycleReflection.AffineAtlas.coordinates_change
AAT.AG.VisibleCycleReflection.AffineAtlas.statePrelocal
AAT.AG.VisibleCycleReflection.AffineAtlas.stateLocal
AAT.AG.VisibleCycleReflection.AffineAtlas.stateLocal_pred
AAT.AG.VisibleCycleReflection.AffineAtlas.stateSheaf
AAT.AG.VisibleCycleReflection.AffineAtlas.StateSection
AAT.AG.VisibleCycleReflection.AffineAtlas.stateSheaf_obj
AAT.AG.VisibleCycleReflection.AffineAtlas.stateSheaf_isSheaf
AAT.AG.VisibleCycleReflection.AffineAtlas.restrict
AAT.AG.VisibleCycleReflection.AffineAtlas.restrict_value
AAT.AG.VisibleCycleReflection.AffineAtlas.stateSheaf_map
AAT.AG.VisibleCycleReflection.AffineAtlas.sectionEquivOfEq
AAT.AG.VisibleCycleReflection.AffineAtlas.sectionEquivOfEq_value
AAT.AG.VisibleCycleReflection.AffineAtlas.sectionEquivOfEq_restrict
AAT.AG.VisibleCycleReflection.AffineAtlas.coordinates_locallyConstant
AAT.AG.VisibleCycleReflection.AffineAtlas.sectionFromCoordinates
AAT.AG.VisibleCycleReflection.AffineAtlas.sectionFromCoordinates_value
AAT.AG.VisibleCycleReflection.AffineAtlas.localTrivialization
AAT.AG.VisibleCycleReflection.AffineAtlas.localTrivialization_apply
AAT.AG.VisibleCycleReflection.AffineAtlas.localTrivialization_symm
AAT.AG.VisibleCycleReflection.AffineAtlas.localTrivialization_change
AAT.AG.VisibleCycleReflection.AffineAtlas.localTrivialization_restrict
AAT.AG.VisibleCycleReflection.AffineAtlas.translateSection
AAT.AG.VisibleCycleReflection.AffineAtlas.translateSection_value
AAT.AG.VisibleCycleReflection.AffineAtlas.localTrivialization_translate
AAT.AG.VisibleCycleReflection.AffineAtlas.translateSection_zero
AAT.AG.VisibleCycleReflection.AffineAtlas.translateSection_add
AAT.AG.VisibleCycleReflection.AffineAtlas.sectionAddAction
AAT.AG.VisibleCycleReflection.AffineAtlas.section_vadd
AAT.AG.VisibleCycleReflection.AffineAtlas.existsUnique_translateSection
AAT.AG.VisibleCycleReflection.AffineAtlas.translateSection_restrict
AAT.AG.VisibleCycleReflection.AffineAtlas.existsUnique_gluing_coordinates
AAT.AG.VisibleCycleReflection.AffineAtlas.existsUnique_gluing_chart_coordinates
AAT.AG.ObstructionDiagnosticBridge.GeneratorPresentation.actualSectionEquiv
AAT.AG.ObstructionDiagnosticBridge.GeneratorPresentation.actualSectionEquiv_restriction
AAT.AG.ObstructionDiagnosticBridge.GeneratorPresentation.aatLocallyConstantObstructionSectionEquiv_value
AAT.AG.ObstructionDiagnosticBridge.GeneratorPresentation.presentationD0_apply
AAT.AG.ObstructionDiagnosticBridge.GeneratorPresentation.faceEmptyCechCochain0Equiv_value
AAT.AG.ObstructionDiagnosticBridge.GeneratorPresentation.faceEmptyCechCochain1Equiv_value
AAT.AG.VisibleCycleReflection.GeometricCover.actualChartSupport_eq
AAT.AG.VisibleCycleReflection.GeometricCover.actualOverlapSupport_eq
AAT.AG.VisibleCycleReflection.GeometricCover.actualChartPoint
AAT.AG.VisibleCycleReflection.GeometricCover.actualOverlapPoint
AAT.AG.VisibleCycleReflection.GeometricCover.actualChartCoordinates
AAT.AG.VisibleCycleReflection.GeometricCover.actualChartCoordinates_apply
AAT.AG.VisibleCycleReflection.GeometricCover.actualChartCoordinates_actual_value
AAT.AG.VisibleCycleReflection.GeometricCover.actualAffineAtlas_actual_transition_value
AAT.AG.VisibleCycleReflection.GeometricCover.actual_corrected_edge
AAT.AG.VisibleCycleReflection.GeometricCover.actual_corrected_compatibility
AAT.AG.VisibleCycleReflection.GeometricCover.stateChartCoordinates
AAT.AG.VisibleCycleReflection.GeometricCover.stateChartCoordinates_value
AAT.AG.VisibleCycleReflection.GeometricCover.stateChartValue
AAT.AG.VisibleCycleReflection.GeometricCover.stateChartValue_eq
AAT.AG.VisibleCycleReflection.GeometricCover.stateChartValue_edge
AAT.AG.VisibleCycleReflection.GeometricCover.actualStateFromGlobal
AAT.AG.VisibleCycleReflection.GeometricCover.actualStateFromGlobal_coordinates
AAT.AG.VisibleCycleReflection.GeometricCover.actualStateFromGlobal_d0
AAT.AG.VisibleCycleReflection.GeometricCover.actual_corrected_d0
AAT.AG.VisibleCycleReflection.GeometricCover.actual_corrected_gluing
AAT.AG.VisibleCycleReflection.GeometricCover.actualCorrectionFromGlobal
AAT.AG.VisibleCycleReflection.GeometricCover.actualCorrectionFromGlobal_d0
AAT.AG.VisibleCycleReflection.GeometricCover.correction_iff_global_state
AAT.AG.VisibleCycleReflection.GeometricCover.existingDescent_zero_iff_global_state
AAT.AG.VisibleCycleReflection.GeometricCover.aatStatePresheaf
AAT.AG.VisibleCycleReflection.GeometricCover.aatStatePresheaf_isSheaf
AAT.AG.VisibleCycleReflection.GeometricCover.aatStateSheaf
AAT.AG.VisibleCycleReflection.GeometricCover.aatStateSheaf_obj
AAT.AG.VisibleCycleReflection.GeometricCover.aatStateSheaf_map
AAT.AG.VisibleCycleReflection.GeometricCover.aatLocalTrivialization
AAT.AG.VisibleCycleReflection.GeometricCover.aatTranslateSection
AAT.AG.VisibleCycleReflection.GeometricCover.aatTranslateSection_zero
AAT.AG.VisibleCycleReflection.GeometricCover.aatTranslateSection_add
AAT.AG.VisibleCycleReflection.GeometricCover.aatLocalTrivialization_translate
AAT.AG.VisibleCycleReflection.GeometricCover.existsUnique_aatTranslateSection
AAT.AG.VisibleCycleReflection.GeometricCover.aatTranslateSection_restriction
AAT.AG.VisibleCycleReflection.GeometricCover.aatLocalTrivialization_restriction
AAT.AG.VisibleCycleReflection.GeometricCover.actualBaseSupport_eq
AAT.AG.VisibleCycleReflection.GeometricCover.aatGlobalStateEquiv
AAT.AG.VisibleCycleReflection.GeometricCover.aatChartStateEquiv
AAT.AG.VisibleCycleReflection.GeometricCover.aatGlobalStateEquiv_restriction
AAT.AG.VisibleCycleReflection.GeometricCover.aat_corrected_gluing
AAT.AG.VisibleCycleReflection.GeometricCover.existingDescent_zero_iff_aat_global_state
AAT.AG.VisibleCycleReflection.GeometricCover.correction_iff_aat_global_state
AAT.AG.VisibleCycleReflection.GeometricCover.exists_actual_repair_and_aat_gluing
AAT.AG.VisibleCycleReflection.GeometricCover.diagnostic_zero_iff_aat_global_state
```

Cycle 4の新6fileのfocused checkは成功。namespace監査はAffineTransition 30、
AffineFibers 15、AffineStateSheaf 34、ActualStateGluing 2と元係数ownerの6、
ActualStateRepair 24、AATStateSheaf 22。明示114宣言のsource/list/実print出力が全件一致し、
標準3公理のみ。実print出力SHA256 `192fac9c9f811e87c340c8d2b2ab487bb563f7c9cb475727fdccb2609efd4662`。
6moduleをmanifestとAG importへ登録し、Research aggregateをelaborateせず静的import gateを通す。
placeholder/hidden/BiDi/privacy/語彙/diff scanはclean。固定GOAL・設計・共通基準とFormalは不変。
Researchのfull/aggregate build、ローカルFormal full buildは不実行。
正式4laneとPR固定headのCIは続いて確認する。全GOALのcompletion candidateはnoである。


## Cycle 5 selection

Cycle 4は[最終内容・acceptance監査](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5256#issuecomment-5979789150)
で独立4本No major findings、CI8件SUCCESSを確認し、通常merge
`f3d990011711583decb2f36ade570551ab264fde`と
[Issue同期](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5250#issuecomment-5979801472)
でB状態層・実一意gluing・零障害/修復/global非空の全方向を受理した。停止条件はない。

```yaml
ledger_type: target_cycle_result
goal: G-132-aat-visible-cycle-reflection
cycle: 5
goal_blob_sha: 4fb28b116ddd9f9d98cc03834d03a0a68b1ba49d
base_oid: f3d990011711583decb2f36ade570551ab264fde
tracking_issue: 5250
report_path: research/reports/G-132-aat-visible-cycle-reflection.md
selection:
  proof_state_ref: cycle4受理監査comment5979789150/merge/Issuecomment5979801472
  proof_dag_predecessors: [cycle1の実Atom/site/coverage/support, cycle2の係数と診断比較, cycle3の全入力反映, cycle4の状態層と修復]
  milestone: Cの有限原始表のT0検証と同じ実入力への復号を計算手続きと正確性で閉じる
  proof_obligations:
    - finite Source/Law値/reading/原始R/target台とfinite幾何点/全開集合/実chartの表を実装
    - 表上の全射/adequacy/原始ラベル保存/Rqを有限生成関係探索から判定しdecoded原始構造へ証明
    - 有限開集合表のtopology法則とchartの開性/被覆/非空/二重連結/三重空を有限検査
    - 有限open separation検査を実IsPreconnectedへ全方向対応させる
    - 無効入力を区別し検査成功から全T0を持つ実P/q/K/target/Atom/site/実Cech coverを構成
    - 全chart対の非空実交差と同じtarget交差を表から生成し既存実nerve/可視性と一致
    - 任意実局所データのaccepted A/B/state APIsに同じdecoded入力を接続
  exit_criteria:
    - runtime validatorはfinite列挙/原始関係到達性の計算でありClassical.choiceやT0供給fieldに依存しない
    - validator成功の正確性と必要性、decoded inputの全T0条件、全実交差と同じtarget交差の一致
    - finite表から生成した同じ原始関係商/Atom/site/actualcoverと任意actual inputへのA/B適用
    - 対象focusedと全新宣言print/scansと独立PR監査
  selection_reason: Cの停止判定と失敗証拠が必要とするraw表からT0と実AAT入力への未接続を先に閉じる
  expected_result_type: proof-obligation-discharged
  lean_targets: [FiniteInputTable.lean, FiniteTopologyTable.lean, PrimitiveTableValidation.lean, ActualTableDecode.lean]
  risks: [入力妥当性fieldへの結論移動, noncomputable validation, 幾何台とtarget台の混同, 実連結性未接続, Rqをラベル同値relationで代替, 全非空交差の欠落, decoded入力のactual API未接続]
  unchecked: [有限表の未実装義務, Cのreflection判定とfailure探索/閉路/同表実反例, W1–W3, 全GOALcompletion]
```

設計README §5の一般被覆表の入口を用い、全開集合の有限表から実位相を生成する。
連結性は列挙した全開集合対に対するopen separation条件を実`IsPreconnected`へ
一致させて検証する。WのAlexandrov incidence例は、この有限位相表への具体入力として
後続で順序の上集合との一致も証明する。Cのreflection検索・失敗出力は、ここで構成した
同じT0入力を用いる次の到達点として保持し、全Cの完了表示はしない。


## Cycle 5 result proposal

終了条件に必要な有限判定の正例・拒否例を`FiniteValidationWitness.lean`へ追加した。
これは同じ到達点のnonvacuity/入力検査の証拠であり、元の終了条件を縮める途中分割ではない。

```yaml
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta:
    raw_table: finite Source/Law依存値/reading/Boolean原始R/独立targetとgeometryの実表
    primitive_validation: finite generated relation graphの計算到達性と元EqvGen/Rqの双方向一致
    geometry_validation: finite全open familyからactual topologyを生成しfinite separationとactual IsPreconnectedを双方向一致
    decoded_actual_input: validateから同じ原始P/q/actualTopology/K/target/Atom site/actual Cech入力を生成
    all_cells_and_visibility: rawGraph/全rawEdges/全generated labelsとactual graph/nerve/同一target可視性の一致
    accepted_aat_connection: 任意actual ξ,pのA比較factorization/B全入力反映/B3と整数修復/実AAT一意gluing
  exit_criteria_status:
    - finite validator/validatedはcomputableな有限列挙と原始関係到達性、raw fieldにcertificateなし
    - validate_true_iff/false_iff/validated_some_iff、topologyValid_iff_exists、geometryValid_iff_exists、adequate_iff/reflectionCondition_iff
    - actualReading/actualPresentation/actualGeometry/actualTarget、actual_coverage_admissible、actual_input_factorization
    - 全新5file focused/全163明示宣言print/scans成功、正式4laneとPR CIは次段階
  split_reason: none
  completion_candidate: no
  lean_artifacts: [FiniteInputTable.lean, FiniteTopologyTable.lean, PrimitiveTableValidation.lean, ActualTableDecode.lean, FiniteValidationWitness.lean]
  evidence: [validate_true_iff, topologyValid_iff_exists, preconnected_iff, geometryValid_iff_exists, relationGraph_reachable_iff, reflectionCondition_iff, actualRawEdgeEquiv, actualGraphRawEdgeEquiv, rawLabels_complete_actual, rawLabels_sound_actual, vertexVisible_iff_actual, edgeVisible_iff_actual, actual_coverage_admissible, actual_input_factorization, actual_reflection_iff_nonbridge_visible, actual_diagnostic_zero_iff_global_state, actual_repair_and_gluing, onePointTable_validates, onePoint_reflects]
  claim_mapping:
    theorem_names: [validate_true_iff, actual_input_factorization, actual_reflection_iff_nonbridge_visible, actual_repair_and_gluing]
    source_labels: [Cの有限表T0検査と実入力復号, T0, A, B]
    conjuncts:
      - 同じraw原始RをactualPresentationに保持しEqvGen到達性からRqを生成
      - raw全open familyがexact actualTopology、finite open separationがexact actual preconnectedness
      - 全actual交差セルとsource-generated labelのexact有限列挙、独立同一target台のexact可視性
      - 同じactualCechCoverと任意ξ,pにaccepted A/Bと元AAT state sheaf/gluingを適用
    undischarged_assumptions: []
    acceptance_point: C全体ではなく選定した有限T0検証/復号到達点のproposal
    port_status: unported

audits:
  premise_delta:
    discharged: [finite全射/adequacy/ラベル保存/Rq, actual topology, chart開性/被覆/非空/連結/二重連結/三重空, target非空, exact raw/actual cellとsame-target support, actual site admissibility, 同じactual入力へのA/B/state API適用]
    remaining: [Cのbridge/反映判定/有限探索/出力once-cycle/同表実反例, W1–W3, 全GOAL独立completion]
  certificate_provenance:
    discharged: [validatedのproofはraw有限decisionから生成, actualGeometry全fieldはrawfinite検査から生成, actual Rqは元Boolean relation graphのfinite reachabilityから生成]
    unresolved: []
  proof_use:
    used: [Boolean relationからactual primitive relation, finite open closureからactual topology, finite separationからactual connectedness, geometry/target別表からexact nerveとsupport, Rq/adequacyをsame actual比較/反映/整数修復に適用]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [5対象focused成功, 163source/list/print入力/実print出力一致, standard3axiomsのみ, runtime bool評価とkernel decide witnesses, diff/placeholder/Unicode/privacy/語彙/import/package方向scan]
  blocking_findings: []
  next_obligation: Cの有限bridge判定/反映成功同値と失敗時のラベル/辺/once-cycle/同表実ξ,pを探索から出力
```

### Cycle 5 claim/premise/dependency spine

rawのdataは有限index・Bool原始関係・全open family・chart点集合・独立target集合である。
`edgeOrder`は表示列順だけで、全chart対を後続列挙して欠落を許さず、実非空交差filterと
重複除去を適用する。Sourceで生成したラベルを列挙し、Lawタグと依存値の等号を保つ。

`Valid`はT0だけを検査し、B1/B3・零障害・integer potential・global stateを検査項目へ
混入しない。`validate`と`validated`は`noncomputable`ではなく、原始関係graphの到達性も
Mathlibの有限長walk列挙から計算する。`validated_retains_input`は成功後のtable変更を禁止する。
actualの意味復号に非計算的Mathlib構成を用いることと、runtime decisionの停止計算を区別する。

Material premiseのraw table data/finite codesはambient-boundary。`Valid`を引数に取る
actual APIはgeneric decoderだが、実入口`validated`はこのproofをfinite decisionから生成する。
T0の全射・adequacy・Rq・実被覆全field・非空targetはdischarge-requiredで、各finite checkの
双方向特徴づけとconstructorに対応する。B3/diagnostic零は方向の仮定であり、本cycleで
bridge/反映decisionを構成したとは主張しない。後続CがこのB3を計算から放電する。

原始Rは同ラベル等号relationへの置換をしない。`relationGraph_reachable_iff`がloopsを
reflexivity、逆向きをsymmetryとして元`Relation.EqvGen`へ対応させる。
`actualGeometry_graph`・`actualRawEdgeEquiv`・`actualGraphRawEdgeEquiv`は全実交差を保ち、
`edgeVisible_iff_actual`は同じtargetが二台の交差に属することを保持する。
実係数は元P.PresentationGroup、actualデータは元`ActualCechAffineLocalData`の全ξ,pである。

依存は受理cycle1の実Atom/site/連続support/coverage、cycle2のfull比較、cycle3の反映/反例、
cycle4の実状態層・修復をcurrent declaration/必要定義/同じ引数で使用する。
新owner API `GeometricCover.graphEdgeEquiv_symm_val`は元ordered pairの公開評価だけを追加する。
G-125/G-104の既受理経路・固定sourceとreview refはcycle2/3の依存記録から不変である。

非空正例`onePointTable`はT0検査とactual ξ=p=0の存在、全入力反映をkernel確認する。
open不足・空chart・空target・未全射reading・不十分adequacy・ラベル横断原始R・
同ラベル未到達・二点分離の否定例を実表で与える。各raw Propには正/負のinstanceがある。
`ActualReflects`/`ActualNonbridgeVisible`の負instanceは、有効な3chart/6pointの
`nonreflectingTriangle`上で不可視非橋辺を発火させた同表の両否定で閉じる。
初回監査の不足F1を修正した証拠であり、未完W2の指定評価は引き続き別義務である。
このone-chart正例はW1–W3を代替せず、Cの反映検索の成功/失敗とも区別する。

### Cycle 5 explicit declaration list

```text
AAT.AG.VisibleCycleReflection.FiniteInputTable
AAT.AG.VisibleCycleReflection.FiniteInputTable.Source
AAT.AG.VisibleCycleReflection.FiniteInputTable.Point
AAT.AG.VisibleCycleReflection.FiniteInputTable.Chart
AAT.AG.VisibleCycleReflection.FiniteInputTable.Generator
AAT.AG.VisibleCycleReflection.FiniteInputTable.RawLabel
AAT.AG.VisibleCycleReflection.FiniteInputTable.laws
AAT.AG.VisibleCycleReflection.FiniteInputTable.rawLabel
AAT.AG.VisibleCycleReflection.FiniteInputTable.rawLabel_apply
AAT.AG.VisibleCycleReflection.FiniteInputTable.relationGraph
AAT.AG.VisibleCycleReflection.FiniteInputTable.relationGraph_adj
AAT.AG.VisibleCycleReflection.FiniteInputTable.relationGraphDecidable
AAT.AG.VisibleCycleReflection.FiniteInputTable.rawGraph
AAT.AG.VisibleCycleReflection.FiniteInputTable.rawGraph_adj
AAT.AG.VisibleCycleReflection.FiniteInputTable.rawGraphDecidable
AAT.AG.VisibleCycleReflection.FiniteInputTable.RawEdge
AAT.AG.VisibleCycleReflection.FiniteInputTable.firstOccurrences
AAT.AG.VisibleCycleReflection.FiniteInputTable.mem_firstOccurrences
AAT.AG.VisibleCycleReflection.FiniteInputTable.firstOccurrences_nodup
AAT.AG.VisibleCycleReflection.FiniteInputTable.rawGenerators
AAT.AG.VisibleCycleReflection.FiniteInputTable.mem_rawGenerators
AAT.AG.VisibleCycleReflection.FiniteInputTable.rawLabels
AAT.AG.VisibleCycleReflection.FiniteInputTable.mem_rawLabels_iff
AAT.AG.VisibleCycleReflection.FiniteInputTable.rawEdgePairs
AAT.AG.VisibleCycleReflection.FiniteInputTable.mem_rawEdgePairs
AAT.AG.VisibleCycleReflection.FiniteInputTable.rawEdges
AAT.AG.VisibleCycleReflection.FiniteInputTable.mem_rawEdges
AAT.AG.VisibleCycleReflection.FiniteInputTable.rawEdges_nodup
AAT.AG.VisibleCycleReflection.FiniteInputTable.VertexVisible
AAT.AG.VisibleCycleReflection.FiniteInputTable.EdgeVisible
AAT.AG.VisibleCycleReflection.FiniteInputTable.decidableVertexVisible
AAT.AG.VisibleCycleReflection.FiniteInputTable.decidableEdgeVisible
AAT.AG.VisibleCycleReflection.FiniteInputTable.SurjectiveReading
AAT.AG.VisibleCycleReflection.FiniteInputTable.AdequateReading
AAT.AG.VisibleCycleReflection.FiniteInputTable.LabelPreserving
AAT.AG.VisibleCycleReflection.FiniteInputTable.RelationReflecting
AAT.AG.VisibleCycleReflection.FiniteInputTable.TopologyValid
AAT.AG.VisibleCycleReflection.FiniteInputTable.Preconnected
AAT.AG.VisibleCycleReflection.FiniteInputTable.GeometryValid
AAT.AG.VisibleCycleReflection.FiniteInputTable.TargetValid
AAT.AG.VisibleCycleReflection.FiniteInputTable.Valid
AAT.AG.VisibleCycleReflection.FiniteInputTable.decidableSurjectiveReading
AAT.AG.VisibleCycleReflection.FiniteInputTable.decidableAdequateReading
AAT.AG.VisibleCycleReflection.FiniteInputTable.decidableLabelPreserving
AAT.AG.VisibleCycleReflection.FiniteInputTable.decidableRelationReflecting
AAT.AG.VisibleCycleReflection.FiniteInputTable.decidableTopologyValid
AAT.AG.VisibleCycleReflection.FiniteInputTable.decidablePreconnected
AAT.AG.VisibleCycleReflection.FiniteInputTable.decidableGeometryValid
AAT.AG.VisibleCycleReflection.FiniteInputTable.decidableTargetValid
AAT.AG.VisibleCycleReflection.FiniteInputTable.decidableValid
AAT.AG.VisibleCycleReflection.FiniteInputTable.validate
AAT.AG.VisibleCycleReflection.FiniteInputTable.validate_true_iff
AAT.AG.VisibleCycleReflection.FiniteInputTable.validate_false_iff
AAT.AG.VisibleCycleReflection.FiniteInputTable.validated
AAT.AG.VisibleCycleReflection.FiniteInputTable.validated_none_iff
AAT.AG.VisibleCycleReflection.FiniteInputTable.validated_retains_input
AAT.AG.VisibleCycleReflection.FiniteInputTable.validated_some_iff
AAT.AG.VisibleCycleReflection.FiniteInputTable.opens_sUnion
AAT.AG.VisibleCycleReflection.FiniteInputTable.topology
AAT.AG.VisibleCycleReflection.FiniteInputTable.topology_isOpen_iff
AAT.AG.VisibleCycleReflection.FiniteInputTable.topology_finset_isOpen_iff
AAT.AG.VisibleCycleReflection.FiniteInputTable.topologyValid_iff_exists
AAT.AG.VisibleCycleReflection.FiniteInputTable.preconnected_iff
AAT.AG.VisibleCycleReflection.FiniteInputTable.patch
AAT.AG.VisibleCycleReflection.FiniteInputTable.mem_patch
AAT.AG.VisibleCycleReflection.FiniteInputTable.patch_coe
AAT.AG.VisibleCycleReflection.FiniteInputTable.geometricCover
AAT.AG.VisibleCycleReflection.FiniteInputTable.geometricCover_patch
AAT.AG.VisibleCycleReflection.FiniteInputTable.geometricCover_edge_iff
AAT.AG.VisibleCycleReflection.FiniteInputTable.geometryValid_iff_exists
AAT.AG.VisibleCycleReflection.FiniteInputTable.generatedLabelEquiv
AAT.AG.VisibleCycleReflection.FiniteInputTable.generatedLabelEquiv_apply
AAT.AG.VisibleCycleReflection.FiniteInputTable.generatedLabelEquiv_primitive
AAT.AG.VisibleCycleReflection.FiniteInputTable.primitive_label_eq_iff
AAT.AG.VisibleCycleReflection.FiniteInputTable.reading
AAT.AG.VisibleCycleReflection.FiniteInputTable.reading_read
AAT.AG.VisibleCycleReflection.FiniteInputTable.adequate_iff
AAT.AG.VisibleCycleReflection.FiniteInputTable.presentation
AAT.AG.VisibleCycleReflection.FiniteInputTable.presentation_relation
AAT.AG.VisibleCycleReflection.FiniteInputTable.relationGraph_reachable_iff
AAT.AG.VisibleCycleReflection.FiniteInputTable.presentation_related_iff
AAT.AG.VisibleCycleReflection.FiniteInputTable.reflectionCondition_iff
AAT.AG.VisibleCycleReflection.Graph.unoriented_val
AAT.AG.VisibleCycleReflection.GeometricCover.graphEdgeEquiv_symm_val
AAT.AG.VisibleCycleReflection.FiniteInputTable.validSurjective
AAT.AG.VisibleCycleReflection.FiniteInputTable.validAdequate
AAT.AG.VisibleCycleReflection.FiniteInputTable.validLabelPreserving
AAT.AG.VisibleCycleReflection.FiniteInputTable.validRelationReflecting
AAT.AG.VisibleCycleReflection.FiniteInputTable.validTopology
AAT.AG.VisibleCycleReflection.FiniteInputTable.validGeometry
AAT.AG.VisibleCycleReflection.FiniteInputTable.validTarget
AAT.AG.VisibleCycleReflection.FiniteInputTable.actualReading
AAT.AG.VisibleCycleReflection.FiniteInputTable.actualPresentation
AAT.AG.VisibleCycleReflection.FiniteInputTable.actualTopology
AAT.AG.VisibleCycleReflection.FiniteInputTable.actualGeometry
AAT.AG.VisibleCycleReflection.FiniteInputTable.actualTarget
AAT.AG.VisibleCycleReflection.FiniteInputTable.actualTarget_mem
AAT.AG.VisibleCycleReflection.FiniteInputTable.actualTarget_coe
AAT.AG.VisibleCycleReflection.FiniteInputTable.actualTarget_nonempty
AAT.AG.VisibleCycleReflection.FiniteInputTable.actualAdequate
AAT.AG.VisibleCycleReflection.FiniteInputTable.actualReflectionCondition
AAT.AG.VisibleCycleReflection.FiniteInputTable.actualPresentation_relation
AAT.AG.VisibleCycleReflection.FiniteInputTable.actualReading_read
AAT.AG.VisibleCycleReflection.FiniteInputTable.actualTopology_isOpen_iff
AAT.AG.VisibleCycleReflection.FiniteInputTable.actualGeometry_patch_coe
AAT.AG.VisibleCycleReflection.FiniteInputTable.actualGeometry_edge_iff
AAT.AG.VisibleCycleReflection.FiniteInputTable.actualGeometry_graph
AAT.AG.VisibleCycleReflection.FiniteInputTable.actualRawEdgeEquiv
AAT.AG.VisibleCycleReflection.FiniteInputTable.actualRawEdgeEquiv_val
AAT.AG.VisibleCycleReflection.FiniteInputTable.rawLabels_complete_actual
AAT.AG.VisibleCycleReflection.FiniteInputTable.rawLabels_sound_actual
AAT.AG.VisibleCycleReflection.FiniteInputTable.actualLawDescend_read
AAT.AG.VisibleCycleReflection.FiniteInputTable.rawSupport_iff_actual
AAT.AG.VisibleCycleReflection.FiniteInputTable.vertexVisible_iff_actual
AAT.AG.VisibleCycleReflection.FiniteInputTable.actualGraphRawEdgeEquiv
AAT.AG.VisibleCycleReflection.FiniteInputTable.actualGraphRawEdgeEquiv_val
AAT.AG.VisibleCycleReflection.FiniteInputTable.edgeVisible_iff_actual
AAT.AG.VisibleCycleReflection.FiniteInputTable.ActualLocalData
AAT.AG.VisibleCycleReflection.FiniteInputTable.actualNerve
AAT.AG.VisibleCycleReflection.FiniteInputTable.actual_input_factorization
AAT.AG.VisibleCycleReflection.FiniteInputTable.ActualReflects
AAT.AG.VisibleCycleReflection.FiniteInputTable.ActualNonbridgeVisible
AAT.AG.VisibleCycleReflection.FiniteInputTable.actual_reflection_iff_nonbridge_visible
AAT.AG.VisibleCycleReflection.FiniteInputTable.actual_coverage_admissible
AAT.AG.VisibleCycleReflection.FiniteInputTable.actual_diagnostic_zero_iff_global_state
AAT.AG.VisibleCycleReflection.FiniteInputTable.actual_repair_and_gluing
AAT.AG.VisibleCycleReflection.FiniteValidationWitness.onePointTable
AAT.AG.VisibleCycleReflection.FiniteValidationWitness.onePointTable_validates
AAT.AG.VisibleCycleReflection.FiniteValidationWitness.onePointTable_valid
AAT.AG.VisibleCycleReflection.FiniteValidationWitness.missingOpens
AAT.AG.VisibleCycleReflection.FiniteValidationWitness.missingOpens_rejected
AAT.AG.VisibleCycleReflection.FiniteValidationWitness.emptyChart
AAT.AG.VisibleCycleReflection.FiniteValidationWitness.emptyChart_rejected
AAT.AG.VisibleCycleReflection.FiniteValidationWitness.emptyTarget
AAT.AG.VisibleCycleReflection.FiniteValidationWitness.emptyTarget_rejected
AAT.AG.VisibleCycleReflection.FiniteValidationWitness.missingPrimitiveRelation
AAT.AG.VisibleCycleReflection.FiniteValidationWitness.missingPrimitiveRelation_rejected
AAT.AG.VisibleCycleReflection.FiniteValidationWitness.missingReading
AAT.AG.VisibleCycleReflection.FiniteValidationWitness.missingReading_not_surjective
AAT.AG.VisibleCycleReflection.FiniteValidationWitness.inadequateReading
AAT.AG.VisibleCycleReflection.FiniteValidationWitness.inadequateReading_not_adequate
AAT.AG.VisibleCycleReflection.FiniteValidationWitness.crossLabelRelation
AAT.AG.VisibleCycleReflection.FiniteValidationWitness.crossLabelRelation_not_preserving
AAT.AG.VisibleCycleReflection.FiniteValidationWitness.missingPrimitiveRelation_not_reflecting
AAT.AG.VisibleCycleReflection.FiniteValidationWitness.missingOpens_not_topology
AAT.AG.VisibleCycleReflection.FiniteValidationWitness.emptyChart_not_geometry
AAT.AG.VisibleCycleReflection.FiniteValidationWitness.emptyTarget_not_target
AAT.AG.VisibleCycleReflection.FiniteValidationWitness.separatedPoints
AAT.AG.VisibleCycleReflection.FiniteValidationWitness.separatedPoints_not_preconnected
AAT.AG.VisibleCycleReflection.FiniteValidationWitness.onePoint_preconnected
AAT.AG.VisibleCycleReflection.FiniteValidationWitness.vertex_support_pair
AAT.AG.VisibleCycleReflection.FiniteValidationWitness.edge_support_pair
AAT.AG.VisibleCycleReflection.FiniteValidationWitness.onePoint_nonbridge_visible
AAT.AG.VisibleCycleReflection.FiniteValidationWitness.onePoint_reflects
AAT.AG.VisibleCycleReflection.FiniteValidationWitness.ActualData
AAT.AG.VisibleCycleReflection.FiniteValidationWitness.actualData_nonempty
AAT.AG.VisibleCycleReflection.FiniteValidationWitness.nonreflectingTriangle
AAT.AG.VisibleCycleReflection.FiniteValidationWitness.nonreflectingTriangle_valid
AAT.AG.VisibleCycleReflection.FiniteValidationWitness.triangleLabel
AAT.AG.VisibleCycleReflection.FiniteValidationWitness.triangleRawEdge
AAT.AG.VisibleCycleReflection.FiniteValidationWitness.triangleRawEdge_not_bridge
AAT.AG.VisibleCycleReflection.FiniteValidationWitness.nonreflectingTriangle_not_nonbridge_visible
AAT.AG.VisibleCycleReflection.FiniteValidationWitness.nonreflectingTriangle_not_reflects
```

5新file focused成功。namespace auditはFiniteInputTable 81、FiniteTopologyTable 15、
PrimitiveTableValidation 12、ActualTableDecode 44、FiniteValidationWitness 37。
明示163宣言のsource/list/print入力/実出力は一致し、標準3公理のみ（公理不要な宣言も含む）。
実print SHA256 `fa50744e1034169cffa5f838e06d1a3b6f4e769173a2f429d86387debb71afb9`。
5moduleをmanifestとAG importへ登録する。root import方向gate（228module）とpackage方向、
新moduleのimport source解決・登録一対一を確認した。Researchだけをscan rootにした同gateは
依存Formal sourceをrootに含めないため未解決local importを報告し、この使用方法を合格根拠にはしない。
Research全体/aggregate buildとローカルFormal全体buildは不実行。固定GOAL/設計/共通基準と
Formalは不変、Formal移植はunported。独立PR監査と固定head CIはこれから確認する。

Runtime評価は `[true,false,false,false,false,false,false,false,false]`（正例1、不正表8）。
`validated.isSome`は正例true、Rq欠落表false。実generator/labelの有限列挙は各`[(0,0)]`、
実edge列挙は空。この観測に加えてkernel `by decide`とgeneric sound/complete theoremを証拠とする。


### Cycle 5 initial review and substantive repair

初回head `aa2b68dd80bdac00cfe0b0133d414035e957e464`の独立4lane結果と全findingsを
[初回監査](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5257#issuecomment-5980365570)
と[Issue](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5250#issuecomment-5980365755)へ記録した。
数学A/LeanA/LeanBはMinor issues、数学BはMajor revisions。全laneが新actual述語の
有効有限表上の負instance不足F1を挙げ、数学A/LeanAは12判定instanceのdocstring不足F2も挙げた。
F1の中心/非中心の分類は異なったが、rootは中心nonvacuity findingとして本筋修正と正式再実行を適用する。

F1修正は`nonreflectingTriangle`、そのfinite validatorによる`Valid`、生成label1、
実交差辺01の非橋性、同じactual入力の`¬ActualNonbridgeVisible`/`¬ActualReflects`である。
辺01を除いても0–2–1が残り、label1のtarget台は全chartで空なので不可視。
原始sourceは2、Lawは1、value0/1とreading恒等、Rは空（各同label生成子は一つ）。
幾何は三頂点と三辺点の全上集合の表で、任意ξ,pの実AAT入力を復号する。
LeanBの独立反証scratchもこの負instanceが構成可能であることを確認したが、
repositoryの提供義務はrootのsource収録とfocused/kernel証拠で修正する。
補助公開API`Graph.unoriented_val`を追加し、既存graph定義を下流で展開せず端点pairを評価する。
F2の12instanceにはfinite検査上の役割をdocstringで記した。査読済み定理のsignature/既存def値は変更しない。

中心findingへの本筋修正なので直接対応は使わず、同cycle内で新fixed headへfresh独立4laneを
正式再実行する。正式レビューは初回と本筋修正後の2回まで。中心findingが再実行後に残るか
新たに出れば当該headをmergeせず、規定のrejected/次選定へ進む。停止条件は現時点では成立しない。

修正後の163明示宣言source/list/実print一致、標準公理のみ、SHA256 `fa50744e1034169cffa5f838e06d1a3b6f4e769173a2f429d86387debb71afb9`。

### Cycle 5 acceptance sync

最終head `85a99e2c5b76a9391967e87dda94b4ef5a17c30a`、merge `c3782b22f19868e43fd5aec8e7c3761eb3c60df0`。
[最終内容・acceptance](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5257#issuecomment-5980642448)は正式再監査4laneと有資格単一直接確認を統合し、選定到達点を `proof-obligation-discharged` と受理した。
最終CI8件SUCCESS、Formal/integrity37206494003・tools37206494018。Research focusedと全163公理print、Formal移植unported。C全体は未完、stop condition:none。

## Cycle 6 selection — Cの有限反映探索と同表の実失敗出力

```yaml
ledger_type: target_cycle_result
goal: G-132-aat-visible-cycle-reflection
cycle: 6
goal_blob_sha: 4fb28b116ddd9f9d98cc03834d03a0a68b1ba49d
base_oid: c3782b22f19868e43fd5aec8e7c3761eb3c60df0
tracking_issue: 5250
report_path: research/reports/G-132-aat-visible-cycle-reflection.md
selection:
  proof_state_ref: cycle5 accepted PR5257 and Issue5250
  proof_dag_predecessors: [cycles1–5, ActualTableDecode, GraphBridge, ActualCounterinput]
  milestone: Cの計算探索がB1–B3と同値で失敗時に同じ実入力の証拠を返す
  proof_obligations: [有限道列挙と探索の停止・soundness/completeness, 削除道からonce-cycle構成, generated labelと全raw edge列の失敗探索, 成功とactual B1–B3の同値, serialized single-edge遷移と同表actual ξ・pの解釈, 零診断・非零原始period・既存障害, 有効正負表runtime]
  exit_criteria: [選択公理でdataを選ばない有限探索, 成功iff B1/B2/B3, failure λ/e/γ/xが列挙から出力され同表actual入力へ復元, 全対象focusedと公理print・scan]
  selection_reason: Cの未完構成を閉じて指定Wの同一手続き評価へ直接接続する
  expected_result_type: proof-obligation-discharged
  lean_targets: [FinitePathSearch.lean, FiniteReflectionSearch.lean, ActualSearchCounterinput.lean, FiniteSearchWitness.lean]
  risks: [choice-onlyデータ出力, same-table actual入力未接続, 表示順による辺欠落, default Fin topology, 非橋と成分数増加の不一致]
  unchecked: [Cの探索正確性と失敗データの全構成は本cycleで実装, W1–W3と全GOALcompletionは後続]
```

### Cycle 6 result proposal

```yaml
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta:
    path_enumeration: List.finRange/length recursion gives all walks; List.range chartCount gives every bounded path
    bridge: deletedPath_none_iff and bridgeTest_true_iff identify the required connected-component increase
    finite_scan: all source-generated labels × all actual raw edges; visibility decision plus computed deleted path
    success: checkAndSearch_actual_success is iff B1/B2/B3 on the same validated actual input
    failure: output λ/e/cycle support/full integer transition/state table; computed deleted-path provenance
    actual_connection: output_actual_transition and actual_state_zero retain original primitive Cech sections; computed actual cycle and original period; diagnostic cochain/class zero and existing class nonzero
  exit_criteria_status: [4 targeted files focused success, 97 explicit declarations source/list/print/output exact, runtime and kernel positive/negative/invalid outputs, scans clean]
  split_reason: none
  completion_candidate: no
  lean_artifacts: [FinitePathSearch.lean, FiniteReflectionSearch.lean, ActualSearchCounterinput.lean, FiniteSearchWitness.lean]
  evidence: [mem_walks, mem_boundedWalks, findPath_none_iff, cycleOfPath_isCycle, cycleOfPath_once, cycleOfPath_coefficient, bridgeTest_true_iff, searchFailure_none_iff, searchFailure_provenance, checkAndSearch_actual_success, SearchFailure.output_actual_transition, SearchFailure.actual_cycle_correct, SearchFailure.actual_period_ne_zero, checkAndSearch_actual_failure]
  claim_mapping:
    theorem_names: [checkAndSearch_actual_success, checkAndSearch_actual_failure]
    source_labels: [C, B1–B3, Bの同表実失敗構成]
    conjuncts: [computable T0 validation and finite reflection search, success iff all B conditions, failure λ/e/γ/x from enumeration with actual interpretation]
    undischarged_assumptions: []
    acceptance_point: C全体のproposal; W1–W3と全GOALcompletionは未完
    port_status: unported
audits:
  premise_delta:
    discharged: [finite enumeration termination and completeness, actual/raw B3 equivalence, actual B1/B2 comparison, raw/actual exact generated label and edge, failure output reconstruction and computed once-cycle]
    remaining: [W1–W3全指定データと結論, 全GOAL独立completion]
  certificate_provenance:
    discharged: [raw T0 checked by cycle5 validator, failure label from rawLabels.attach, invisible proof from finite decision, path from bounded List search, actual input from same original Cech normalization]
    unresolved: []
  proof_use:
    used: [source-generated code membership to actual label, actualGeometry_graph equality to transport computed edge/walk, accepted original basis transition and actual Cech inverse, computed chain coefficient -1 to original primitive period]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [4 selected file focused success, all97 source/list/print/output exact, standard3 axioms only, finite positive/negative/invalid kernel/runtime, diff/Unicode/privacy/placeholder/import/package scan]
  blocking_findings: []
  next_obligation: W1–W3の実Alexandrov幾何・原始入力・指定遷移・修復/gluing・同手続き評価
```

### Cycle 6 claim・前提・再利用・計算経路

`walks` は頂点code順に全隣接点を走査してwalkを前置する。零長は等号でnilを返す。
`mem_walks`は指定長の全walkと同値、`mem_boundedWalks`は長さが頂点数未満の全walkと同値である。
`asPath`はsupportのNodupを直接有限検査し、成功した証明からMathlib IsPathを構成する。
MathlibのIsPath Decidableを経るProp等号castがkernel評価を止めることを確認したため、このdata側の
検査は直接Nodupとした。経路条件の弱化ではなく `Walk.isPath_def` により同じ条件である。
`findPath_none_iff`は実Reachableの反証と双方向一致し、必要な探索上限は `IsPath.length_lt` で放電する。
存在した道をchoiceで選ぶ構成や非計算的Finset.toListは用いない。

削除道を `mapLe` で元graphへ戻し、逆向きの選定辺を前置する。削除graphの隣接性からその辺が
道に現れないこと、生成閉路がIsCycleであること、辺count=1、符号付きchain成分=-1を証明する。
`bridgeTest_true_iff`は受理cycle3の成分数同値へ接続する。連結graphに限定しない。

`searchPairs`はrawLabels.attach×全rawEdgesの有限列で、表示順に欠落や重複を許さないcycle5列を使う。
`failureAt`は同じtargetの可視性を検査して、不可視の場合だけ削除道を探索する。
`searchFailure_provenance`は返したfのlabel/edgeが列に属し、そのf.pathがdeletedPathの実出力であることを保持する。
`checkAndSearch`はT0不正表をinvalid、正表の反映条件をsuccess/failureとして分ける。

`FailureOutput`のxは全実辺・全生成ラベルの整数遷移表と全chart状態表である。
`output_transition_iff`・`output_state_iff`はすべてのrowとその値を特徴づけ、
`actual_transition_table`・`output_actual_transition`は同じ原始PresentationGroupの実Čech切断へ接続する。
`actualInput`はこの単一辺基底遷移を元のactual-section inverseで構成し、localStateは表と同じ零である。
rawとactual graphの証明済み等号で **計算済みの閉路そのもの** をtransportし、別の閉路を選ばない。
`actual_cycle_correct`は実cycle/once-count/signed-coefficientを保持する。
`actual_period`は原始係数のperiod=-basisを、`actual_period_ne_zero`はその非零性を証明する。
独立診断cochain零・類零・既存descent類非零は同じactualInputの定理である。

| material premise | 分類・入力からの生成 | 実使用 |
| --- | --- | --- |
| raw finite data | ambient-boundary; T0の表 | List列挙・有限decision |
| 全射/adequacy/Rq/geometry/target | discharge-required; cycle5 Valid↔有限check | actual P/q/K/target・labelBasis・actual比較と状態層 |
| 非橋/不可視 | 判定対象・failure構成義務; computed deleted path + visible decision | 原始basis遷移・zero diagnostic・period非零 |
| bounded completeness | 構成義務; mem_walks/IsPath.length_lt | success iff全label全edge条件 |
| actual label/edge/walk | 構成義務; generated code + actualGeometry_graph | 同表actualInputとperiod |
| ξ/p | 失敗時は計算表、成功条件は全actual ξ,p | B1全量化を維持 |

受理predecessorはcycle3 PR5255（GraphBridge、ActualCounterinput）、cycle5 PR5257（表検査と実復号）。
現在の型、必要定義、実適用引数を確認し、元係数商・独立診断・全ξ,p・same-target台を保持して適用した。
Mathlib使用版は既存固定版、Walks.mapLe/Path.cons_isCycle/Walk.isPath_def/IsPath.length_ltを確認した。
新規部分は有限List探索・成功同値・失敗データの計算provenance、接続部分はsame-table actual意味と生成閉路のtransportである。

### Cycle 6 検証と具体的出力

4対象fileのfocusedチェックが成功した。全97明示宣言をsourceから列挙し、print入力と実print出力の順序・件数・重複なしまで照合した。
公理は `propext`・`Classical.choice`・`Quot.sound` のみ。全対象 `#print axioms` 実出力SHA256:
`adced4835664153ae0b4f28bd01750e5c06e7dc42a6142cb91906941f579e354`。
printは依存proofの標準公理を示すもので、有限dataをchoiceで選ぶ計算手続きではない。

runtime: onePoint validate=true/reflection=true。valid nonreflectingTriangle validate=true/reflection=false。
三辺01/02/12はいずれもbridge=false。失敗はλ=(0,1)、e=(0,1)、γ=[1,0,2,1]。
遷移rowは01・λ1だけ1、他5rowは零、全6状態rowは零。
`triangleFailure_codes`が同じ出力をkernel確認し、`triangle_actual_failure`が同じ実入力の零診断・非零既存障害を確認する。
正例RawNonbridgeVisible/ActualHomologySurjectiveと、同じvalid負例の両否定を提供した。
missingOpens・missingPrimitiveRelation・emptyTargetはvalidate=false、前二つのcombined invalidをkernel確認した。

`git diff --check`、placeholder/hidden・bidi/privacy/語彙scan、Formal import方向（228modules）、package方向、
4新moduleのsource/import/registry一対一が成功。固定GOAL・設計・基準に差分なし。
Research full/aggregate/全file loopおよびlocal Formal full buildは未実行。Formalへの移植はunported。
PR正式4laneと固定head CIは次段階。全GOAL完了はW1–W3と独立completion後に判定する。

### Cycle 6 明示宣言spine

以下は4新sourceの全97明示宣言である。structure/inductiveの生成field/accessorは各fileのnamespace監査にも含まれる。

```text
AAT.AG.VisibleCycleReflection.FinitePathSearch.walks
AAT.AG.VisibleCycleReflection.FinitePathSearch.mem_walks
AAT.AG.VisibleCycleReflection.FinitePathSearch.boundedWalks
AAT.AG.VisibleCycleReflection.FinitePathSearch.mem_boundedWalks
AAT.AG.VisibleCycleReflection.FinitePathSearch.asPath
AAT.AG.VisibleCycleReflection.FinitePathSearch.asPath_none_iff
AAT.AG.VisibleCycleReflection.FinitePathSearch.findPath
AAT.AG.VisibleCycleReflection.FinitePathSearch.findPath_none_iff
AAT.AG.VisibleCycleReflection.FinitePathSearch.findPath_sound
AAT.AG.VisibleCycleReflection.Graph.withoutEdgeDecidable
AAT.AG.VisibleCycleReflection.Graph.restoredPath
AAT.AG.VisibleCycleReflection.Graph.restoredPath_avoids
AAT.AG.VisibleCycleReflection.Graph.cycleOfPath
AAT.AG.VisibleCycleReflection.Graph.cycleOfPath_isCycle
AAT.AG.VisibleCycleReflection.Graph.cycleOfPath_once
AAT.AG.VisibleCycleReflection.Graph.cycleOfPath_coefficient
AAT.AG.VisibleCycleReflection.Graph.not_bridge_of_deleted_path
AAT.AG.VisibleCycleReflection.FiniteInputTable.rawGraphEdge
AAT.AG.VisibleCycleReflection.FiniteInputTable.rawGraphEdge_val
AAT.AG.VisibleCycleReflection.FiniteInputTable.deletedPath
AAT.AG.VisibleCycleReflection.FiniteInputTable.deletedPath_none_iff
AAT.AG.VisibleCycleReflection.FiniteInputTable.bridgeTest
AAT.AG.VisibleCycleReflection.FiniteInputTable.bridgeTest_true_iff
AAT.AG.VisibleCycleReflection.FiniteInputTable.GeneratedRawLabel
AAT.AG.VisibleCycleReflection.FiniteInputTable.SearchFailure
AAT.AG.VisibleCycleReflection.FiniteInputTable.SearchFailure.cycle
AAT.AG.VisibleCycleReflection.FiniteInputTable.SearchFailure.transition
AAT.AG.VisibleCycleReflection.FiniteInputTable.SearchFailure.localState
AAT.AG.VisibleCycleReflection.FiniteInputTable.FailureOutput
AAT.AG.VisibleCycleReflection.FiniteInputTable.SearchFailure.output
AAT.AG.VisibleCycleReflection.FiniteInputTable.SearchFailure.output_codes
AAT.AG.VisibleCycleReflection.FiniteInputTable.SearchFailure.output_transition_iff
AAT.AG.VisibleCycleReflection.FiniteInputTable.SearchFailure.output_state_iff
AAT.AG.VisibleCycleReflection.FiniteInputTable.failureAt
AAT.AG.VisibleCycleReflection.FiniteInputTable.failureAt_none_iff
AAT.AG.VisibleCycleReflection.FiniteInputTable.searchPairs
AAT.AG.VisibleCycleReflection.FiniteInputTable.mem_searchPairs
AAT.AG.VisibleCycleReflection.FiniteInputTable.searchFailure
AAT.AG.VisibleCycleReflection.FiniteInputTable.RawNonbridgeVisible
AAT.AG.VisibleCycleReflection.FiniteInputTable.searchFailure_none_iff
AAT.AG.VisibleCycleReflection.FiniteInputTable.reflectsTest
AAT.AG.VisibleCycleReflection.FiniteInputTable.SearchFailure.cycle_correct
AAT.AG.VisibleCycleReflection.FiniteInputTable.SearchFailure.not_bridge
AAT.AG.VisibleCycleReflection.FiniteInputTable.failureAt_provenance
AAT.AG.VisibleCycleReflection.FiniteInputTable.searchFailure_provenance
AAT.AG.VisibleCycleReflection.FiniteInputTable.SearchResult
AAT.AG.VisibleCycleReflection.FiniteInputTable.checkAndSearch
AAT.AG.VisibleCycleReflection.FiniteInputTable.checkAndSearch_invalid_iff
AAT.AG.VisibleCycleReflection.FiniteInputTable.checkAndSearch_success_iff
AAT.AG.VisibleCycleReflection.FiniteInputTable.checkAndSearch_failure_iff
AAT.AG.VisibleCycleReflection.Graph.transportEdge
AAT.AG.VisibleCycleReflection.Graph.transportEdge_val
AAT.AG.VisibleCycleReflection.Graph.transportEdge_unoriented
AAT.AG.VisibleCycleReflection.Graph.transportEdge_bridge
AAT.AG.VisibleCycleReflection.Graph.transportWalk
AAT.AG.VisibleCycleReflection.Graph.transportWalk_cycle
AAT.AG.VisibleCycleReflection.Graph.transportWalk_edges
AAT.AG.VisibleCycleReflection.Graph.transportWalk_coefficient
AAT.AG.VisibleCycleReflection.FiniteInputTable.rawLabel_generated
AAT.AG.VisibleCycleReflection.FiniteInputTable.actualLabel
AAT.AG.VisibleCycleReflection.FiniteInputTable.actualLabel_code
AAT.AG.VisibleCycleReflection.FiniteInputTable.actualEdge
AAT.AG.VisibleCycleReflection.FiniteInputTable.actualEdge_raw
AAT.AG.VisibleCycleReflection.FiniteInputTable.raw_nonbridge_iff_actual
AAT.AG.VisibleCycleReflection.FiniteInputTable.reflectsTest_iff_actual_nonbridge
AAT.AG.VisibleCycleReflection.FiniteInputTable.reflectsTest_iff_actual_reflection
AAT.AG.VisibleCycleReflection.FiniteInputTable.SearchFailure.actualInput
AAT.AG.VisibleCycleReflection.FiniteInputTable.SearchFailure.actualCycle
AAT.AG.VisibleCycleReflection.FiniteInputTable.SearchFailure.actual_invisible
AAT.AG.VisibleCycleReflection.FiniteInputTable.SearchFailure.actual_not_bridge
AAT.AG.VisibleCycleReflection.FiniteInputTable.SearchFailure.actual_cycle_correct
AAT.AG.VisibleCycleReflection.FiniteInputTable.ActualHomologySurjective
AAT.AG.VisibleCycleReflection.FiniteInputTable.reflectsTest_iff_actual_homology
AAT.AG.VisibleCycleReflection.FiniteInputTable.actualLabel_eq_iff
AAT.AG.VisibleCycleReflection.FiniteInputTable.SearchFailure.actual_transition_table
AAT.AG.VisibleCycleReflection.FiniteInputTable.SearchFailure.actual_state_zero
AAT.AG.VisibleCycleReflection.FiniteInputTable.SearchFailure.actual_diagnostic_zero
AAT.AG.VisibleCycleReflection.FiniteInputTable.SearchFailure.actual_period
AAT.AG.VisibleCycleReflection.FiniteInputTable.SearchFailure.actual_period_ne_zero
AAT.AG.VisibleCycleReflection.FiniteInputTable.SearchFailure.actual_existing_nonzero
AAT.AG.VisibleCycleReflection.FiniteInputTable.checkAndSearch_actual_success
AAT.AG.VisibleCycleReflection.FiniteInputTable.SearchFailure.output_actual_transition
AAT.AG.VisibleCycleReflection.FiniteInputTable.checkAndSearch_actual_failure
AAT.AG.VisibleCycleReflection.FiniteSearchWitness.onePoint_search_success
AAT.AG.VisibleCycleReflection.FiniteSearchWitness.onePoint_raw_nonbridge
AAT.AG.VisibleCycleReflection.FiniteSearchWitness.onePoint_actual_homology
AAT.AG.VisibleCycleReflection.FiniteSearchWitness.onePoint_checked_success
AAT.AG.VisibleCycleReflection.FiniteSearchWitness.triangle_failure_generated
AAT.AG.VisibleCycleReflection.FiniteSearchWitness.triangleFailure
AAT.AG.VisibleCycleReflection.FiniteSearchWitness.triangleFailure_search
AAT.AG.VisibleCycleReflection.FiniteSearchWitness.triangleFailure_codes
AAT.AG.VisibleCycleReflection.FiniteSearchWitness.triangle_not_raw_nonbridge
AAT.AG.VisibleCycleReflection.FiniteSearchWitness.triangle_not_actual_homology
AAT.AG.VisibleCycleReflection.FiniteSearchWitness.triangle_checked_failure
AAT.AG.VisibleCycleReflection.FiniteSearchWitness.triangle_actual_failure
AAT.AG.VisibleCycleReflection.FiniteSearchWitness.missingOpens_checked_invalid
AAT.AG.VisibleCycleReflection.FiniteSearchWitness.missingRelation_checked_invalid
```
