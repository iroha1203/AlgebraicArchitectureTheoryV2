# G-132：可視閉路による修復障害の零性反映

一次仕様は `dd4e86f56cc1b64db8dfaf7eb2b0ed8e8293198d` の
[固定GOAL](../goals/G-132-aat-visible-cycle-reflection.md) T0・A–C・W1–W3。
共通基準・設計は `75319c99f8732c1993142735460334dcaed2c170`、既存宣言は
`7547b0d1dc9d523e63c0e8596180dd61e6119529` を参照する。現main
`a6f239eea22be47f1adec5f7200b081ef8b23320` まで参照対象のsource差分はない。

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

## 全targetの現proof obligation

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
