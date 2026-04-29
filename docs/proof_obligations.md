# 証明義務と実証仮説

この文書は、AAT v2 の Lean status、未解決 proof obligation、empirical hypothesis を
追跡するための索引である。詳細な定義や theorem 一覧は重複させず、第一級設計書、
Lean theorem index、個別 design / empirical protocol へ委任する。

過去の詳細 ledger は
[archive/proof_obligations_full_ledger.md](archive/proof_obligations_full_ledger.md)
に退避している。

## Source of Truth

| 対象 | Source of truth |
| --- | --- |
| 数学的定義、中心 theorem 候補、形式化ロードマップ | [AAT v2 数学設計書](aat_v2_mathematical_design.md) |
| Tooling、AIR、Feature Extension Report、claim taxonomy、CI / empirical 接続 | [AAT v2 ツール設計書](aat_v2_tooling_design.md) |
| 実装済み Lean API | [Lean 定義・定理索引](lean_theorem_index.md) |
| 零曲率 theorem package の Lean 化方針 | [アーキテクチャ零曲率定理 Lean 化設計](formal/flatness_obstruction_lean_design.md) |
| GitHub Issue の状態、優先度、milestone | GitHub Issues |
| empirical hypotheses と pilot protocol | [Signature 実証プロトコル](design/empirical_protocol.md), `docs/empirical/` |

この文書は GitHub Issues の完全な複製ではない。研究上の文脈に必要な status と
参照先だけを置く。

## Status 語彙

研究上の主張は次の status に分ける。

| Status | 意味 |
| --- | --- |
| `proved` | Lean で証明済みの命題。 |
| `defined only` | Lean 上の定義や executable metric はあるが、対応する正当性 theorem が未完了のもの。 |
| `future proof obligation` | Lean で証明すべき未解決命題。 |
| `empirical hypothesis` | 実コードベースや運用データで検証する仮説。Lean proof のブロッカーではない。 |

Tooling output、extractor output、AI generated code、未測定軸は、それだけで
`proved` にはならない。`unmeasured` と測定済み 0 も区別する。

## 現在の QED 境界

現時点で Lean proved と呼ぶ中核は、AAT v2 の **static structural core** である。
抽象 `LawFamily`、complete witness coverage、required axis exactness を前提に、
lawfulness と required axes zero を接続する bridge が証明済みである。

Signature 側では、selected required axes を concrete count で埋める constructor と、
projection / LSP / closed-walk / boundary policy / abstraction policy の direct
axis exactness bridge が証明済みである。中心的な読みは次である。

```text
ArchitectureLawful X
  <-> RequiredSignatureAxesZero (ArchitectureLawModel.signatureOf X)

ArchitectureLawful X
  <-> ArchitectureZeroCurvatureTheoremPackage X
```

この QED に含めないもの:

- runtime metrics と runtime edge metadata の完全性。
- general numerical curvature の Signature axis 化。
- relation complexity や empirical cost との相関。
- 実コード extractor が完全な `ComponentUniverse` を生成するという主張。

詳細な theorem 名は
[Lean 定義・定理索引](lean_theorem_index.md) を参照する。

## Lean Proof Obligation Index

| 領域 | 現在の status | 詳細 |
| --- | --- | --- |
| Generic witness-count kernel / zero-count bridge | `proved` | [Lean 化設計](formal/flatness_obstruction_lean_design.md), [Lean theorem index](lean_theorem_index.md#flatness) |
| Required law / axis exactness bridge | `proved` | [Lean theorem index](lean_theorem_index.md#signature-integrated-lawfulness) |
| FeatureExtension / StaticSplitFeatureExtension | `defined only` / `proved` | [AAT v2 数学設計書](aat_v2_mathematical_design.md#2-第一級対象-featureextension), [Lean theorem index](lean_theorem_index.md#feature-extension) |
| ArchitectureOperation / ProofObligation schema | `defined only` / `proved` for schema accessor theorems | [AAT v2 数学設計書](aat_v2_mathematical_design.md#3-architecture-calculus), [Lean theorem index](lean_theorem_index.md#architecture-operation) |
| ArchitecturePath / homotopy skeleton | `defined only` / `proved` | [Lean theorem index](lean_theorem_index.md#architecture-path) |
| DiagramFiller / obstruction as non-fillability | `defined only` / `proved` / `future proof obligation` | [Lean theorem index](lean_theorem_index.md#diagram-filler) |
| Projection / DIP bridge | `proved` for soundness bridges; exact projection refinements tracked separately | [Projection soundness と exact projection の使い分け](design/projection_exact_soundness.md), [Lean theorem index](lean_theorem_index.md#projection--dip) |
| Observation / LSP bridge | `proved` for finite violation-count bridges | [Observation bridge と projection bridge の関係](design/observation_projection_bridge.md), [Lean theorem index](lean_theorem_index.md#observation--lsp) |
| Matrix / nilpotence / spectral bridge | `proved` for finite structural bridges; cost interpretation is empirical | [spectral radius bridge 設計](design/spectral_radius_bridge.md), [Lean theorem index](lean_theorem_index.md#matrix-bridge) |
| Runtime propagation | `defined only` / `proved` for 0/1 runtime graph zero bridge; policy-aware coverage is separate | [runtimePropagation 設計](design/runtime_propagation_design.md), [Lean theorem index](lean_theorem_index.md#finite-universe--bridge-theorems) |
| SOLID-style counterexamples | `proved` for current Lean examples | [Lean theorem index](lean_theorem_index.md#solid-counterexamples) |

## Empirical Hypothesis Index

Empirical hypotheses は Lean theorem ではない。初期 protocol では H1a と H3 を primary
analysis とし、その他は必要データが揃う場合の exploratory analysis とする。

| ID | Tier | 仮説 | 詳細 |
| --- | --- | --- | --- |
| H1a | primary | PR 前の Signature risk が変更波及の増加と相関する。 | [Signature 実証プロトコル](design/empirical_protocol.md#検証する仮説) |
| H1b | exploratory | PR 前後の Signature delta が将来 co-change / repair scope と相関する。 | [Signature 実証プロトコル](design/empirical_protocol.md#検証する仮説) |
| H2 | exploratory | SCC / cycle risk が大きい領域では障害修正コストが増える。 | [Signature 実証プロトコル](design/empirical_protocol.md#検証する仮説) |
| H3 | primary | fanout risk が高い変更はレビューコストが増える。 | [Signature 実証プロトコル](design/empirical_protocol.md#検証する仮説) |
| H4 | exploratory | 境界違反や relation complexity が将来の変更・運用リスクと相関する。 | [empirical protocol](design/empirical_protocol.md), [relationComplexity 設計](design/relation_complexity_design.md) |
| H5 | exploratory | runtime exposure / blast radius が incident scope や障害修正コストと相関する。 | [runtimePropagation 設計](design/runtime_propagation_design.md), [Signature 実証プロトコル](design/empirical_protocol.md) |

## 現在の未解決カテゴリ

| カテゴリ | 扱い |
| --- | --- |
| SOLID の形式化は一意ではない | AAT では操作的形式化として扱う。自然言語としての SOLID 全体の唯一の形式化は主張しない。 |
| 静的依存と実行時依存の分離 | Lean core では `StaticDependencyGraph` と `RuntimeDependencyGraph` を graph role として分ける。edge metadata は tooling / empirical 側に置く。 |
| runtime policy-aware metrics | raw runtime graph の theorem と、Circuit Breaker coverage / timeout / retry policy を反映した extension axis を分ける。 |
| numerical curvature | finite diagram / zero-separating distance の proved bridge と、weighted / calibrated Signature axis や現実コストとの相関を分ける。 |
| operation calculus laws | `compose`, `replace`, `protect`, `repair` の schema はあるが、結合法則、置換の観測同値、保護の冪等性、repair monotonicity は別 Issue の proof obligation として扱う。 |
| extractor completeness | extractor output は tooling evidence であり、完全な proof-carrying universe とは同一視しない。 |
| relation complexity | 状態遷移代数層の empirical metric として扱い、構成要素ベクトルを残す。単一スコアだけで設計を評価しない。 |

## 更新ルール

- Lean theorem、定義、module path を追加・削除・rename した場合は、必要に応じて
  [Lean 定義・定理索引](lean_theorem_index.md) を更新する。
- 未解決 proof obligation が新しい設計判断を必要とする場合は、GitHub Issue へ分離し、
  この文書にはカテゴリとリンクだけを残す。
- empirical protocol や dataset schema の詳細は `docs/design/` または `docs/empirical/`
  に置き、この文書へ詳細表を複製しない。
- `proved`, `defined only`, `future proof obligation`, `empirical hypothesis` を混同しない。
