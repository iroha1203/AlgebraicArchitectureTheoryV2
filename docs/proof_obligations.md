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
`docs/aat_v2_mathematical_design.md` は数学面の第一級設計書として扱い、
Lean 実装 status や Issue 管理状態はこの文書と
[Lean 定義・定理索引](lean_theorem_index.md) で管理する。

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

claim level は、証明状態とは別に次の境界として扱う。

| Claim level | 扱い |
| --- | --- |
| `formal` | Lean theorem package と明示された前提の discharge によって支えられる claim。 |
| `tooling` | extractor、policy checker、CI report、validation report などの tooling-side evidence による claim。Lean theorem ではない。 |
| `empirical` | dataset、pilot、統計解析、case study による claim。Lean proof のブロッカーではない。 |
| `hypothesis` | 研究仮説または将来検証する設計仮説。証明済み claim として扱わない。 |

`nonConclusions` は claim level に関係なく必須である。特に `tooling` claim は、
「測定された範囲では violation がない」と「全 universe で obstruction がない」を区別し、
未測定軸を zero と読まないための non-conclusion を持つ。

## Lean status の読み方

`docs/aat_v2_mathematical_design.md` は純粋な数学設計書であり、Lean 実装の
進捗状態、QED 境界、Issue 管理状態を持たせない。この文書と
[Lean 定義・定理索引](lean_theorem_index.md) が、数学設計書に対応する
作業状態と Lean API の読み方を管理する。

したがって、数学設計書の theorem 候補は、そのまま現在の Lean proved claim とは
読まない。現在の Lean proved claim は、各 theorem package が明示する universe、
coverage assumptions、exactness assumptions、observation model、witness family に
相対化して読む。

`defined only` / `proved` が併記される領域では、通常、schema や carrier 定義は
`defined only`、soundness bridge、bounded completeness theorem、accessor theorem、
代表例 theorem の一部が `proved` であることを意味する。混同を避けるため、主要な
theorem package は次の粒度で読む。

| 粒度 | 意味 |
| --- | --- |
| Schema / carrier | 定義、構造体、predicate、measurement universe。単独では correctness claim ではない。 |
| Soundness theorem | witness、metric zero、operation package などから、対応する obstruction 不在や lawfulness 方向の結論を得る片方向 theorem。 |
| Bounded completeness theorem | coverage / exactness assumptions の下で、失敗や obstruction から selected witness を得る theorem。global completeness ではない。 |
| Accessor theorem | theorem package や schema の field を取り出す API 健全性 theorem。研究上の主定理とは区別する。 |
| Example / counterexample theorem | 有限 skeleton や canonical example 上で、定義の意図、非含意、境界を示す theorem。 |
| Non-conclusion | theorem package が主張しない範囲。extractor completeness、runtime / semantic completeness、global flatness、empirical cost correlation など。 |

第3章 Architecture Calculus の status は、特に次の分類で読む。

| API 群 | 主な粒度 | `proved` と読める範囲 | 読まない範囲 |
| --- | --- | --- | --- |
| `ArchitectureOperationKind`, `OperationProofObligation` | Schema / carrier + accessor theorem | operation tag と proof-obligation constructor の対応、generated obligation の kind accessor。 | operation tag だけからの preservation、improvement、operation law、global flatness preservation。 |
| `OperationRoleSchema` | Schema / carrier + accessor theorem + role bridge | role tag と generated obligation の対応、discharge wrapper、preserve role を selected invariant preservation として読む bridge、非 preserve role を明示的な witness / relation / assumption 境界として読む bridge。 | role tag だけからの reflection、improvement、localization、translation、transfer、assumption discharge。各 bridge は `roleConclusion` の形を明示前提として要求する。 |
| `ArchitectureCalculusLaw` constructors | Bounded law schema + accessor theorem | law package の kind / operation kind accessor、明示 assumption から package conclusion を取り出す wrapper。 | 無条件の associativity、全 operation の冪等性、uniform graph transform、global flatness preservation。 |
| concrete / observation / runtime / repair / synthesis entrypoint | Schema bridge / substantive theorem | finite graph kernel、selected observation contract、runtime universe、repair rule、valid synthesis package などの明示前提に相対化された bounded conclusion。 | runtime telemetry completeness、semantic completeness、extractor completeness、solver completeness、all obstruction removal。 |

このリポジトリ外の査読で Lean source を直接確認しない場合、`proved` の読みは
この文書と [Lean 定義・定理索引](lean_theorem_index.md) が Lean source を正しく
反映しているという前提つきである。Lean source の build、placeholder scan、
`axiom` / `admit` / `sorry` / `unsafe` scan は PR 前チェックで別途確認する。

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
| `Formal/Arch` module organization | module organization / API integration tracking | [Lean module 階層整理方針](formal/lean_module_organization.md), parent Issue [#423](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/423), facade / import policy Issue [#424](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/424). `Formal/Arch` 直下は互換 facade として残し、実体 module は leaf から core へ段階的に canonical subdirectory へ移す。これは import path / docs path の整理であり、新しい数学的 theorem claim ではない。 |
| Chapter 7 center theorem package entrypoints | docs index / API integration tracking | [Lean theorem index](lean_theorem_index.md#chapter-7-theorem-package-entrypoints), parent Issue [#419](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/419), completed entrypoint Issue [#420](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/420), schematic-name correspondence Issue [#421](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/421), docs index Issue [#422](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/422). `Formal/Arch/Evolution/Chapter7TheoremPackages.lean` が 7.1〜7.6 の代表 bounded theorem package を横断 import / docs-facing metadata として束ね、`Formal/Arch/Chapter7TheoremPackages.lean` は互換 facade として残す。`Chapter7TheoremPackages.Candidate.schematicCorrespondences` が設計書の schematic name と既存 bounded Lean API の読み替えを記録する。[Lean theorem index](lean_theorem_index.md#chapter-7-theorem-package-entrypoints) は、代表 entrypoint、schematic name correspondence、bounded reading / non-conclusion boundary を一箇所で追跡する。 |
| FeatureExtension / StaticSplitFeatureExtension | `defined only` / `proved` | [AAT v2 数学設計書](aat_v2_mathematical_design.md#2-第一級対象-featureextension), [Lean theorem index](lean_theorem_index.md#feature-extension), parent Issue [#371](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/371), related / completion Issues [#299](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/299), [#372](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/372), [#373](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/373), [#374](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/374), [#375](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/375) |
| SplitExtensionLifting / selected section law / featureView law package | `defined only` / `proved` | [AAT v2 数学設計書](aat_v2_mathematical_design.md#83-split-extension-as-lifting-and-section), [Lean theorem index](lean_theorem_index.md#split-extension-lifting), Issues [#264](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/264), [#372](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/372) |
| ArchitectureOperation / ProofObligation schema | `defined only` / `proved` for schema accessor theorems | [AAT v2 数学設計書](aat_v2_mathematical_design.md#3-architecture-calculus), [Lean theorem index](lean_theorem_index.md#architecture-operation) |
| Architecture Calculus laws | `defined only` / `proved` for bounded schema accessor theorems | [AAT v2 数学設計書](aat_v2_mathematical_design.md#32-calculus-laws), [Lean theorem index](lean_theorem_index.md#architecture-calculus-laws), Issue [#279](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/279) |
| Operation / invariant Galois correspondence | `defined only` / `proved` | [AAT v2 数学設計書](aat_v2_mathematical_design.md#4-ガロア的対応-operation-と-invariant), [Lean theorem index](lean_theorem_index.md#operation--invariant-galois), Issues [#276](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/276), [#382](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/382), [#383](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/383) |
| Repair step decreases / selected obstruction measure | `defined only` / `proved` | [AAT v2 数学設計書](aat_v2_mathematical_design.md#73-repair-as-re-splitting), [Lean theorem index](lean_theorem_index.md#repair), Issue [#266](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/266) |
| Repair termination / synthesis / no-solution certificate | `defined only` / `proved` for bounded schema accessor theorems | [AAT v2 数学設計書](aat_v2_mathematical_design.md#75-no-solution-certificate), [Lean theorem index](lean_theorem_index.md#repair-synthesis), Issue [#277](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/277) |
| Structural Architecture Extension Formula / obstruction classification | `defined only` / `proved` | [AAT v2 数学設計書](aat_v2_mathematical_design.md#84-structural-architecture-extension-formula), [Lean theorem index](lean_theorem_index.md#architecture-extension-formula), Issue [#262](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/262) |
| ArchitecturePath / homotopy skeleton | `defined only` / `proved` | [Lean theorem index](lean_theorem_index.md#architecture-path) |
| DiagramFiller / obstruction as non-fillability | `defined only` / `proved` | [Lean theorem index](lean_theorem_index.md#diagram-filler), Issues [#285](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/285), [#286](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/286) |
| Projection / DIP bridge | `proved` for soundness bridges; exact projection refinements tracked separately | [Projection soundness と exact projection の使い分け](design/projection_exact_soundness.md), [Lean theorem index](lean_theorem_index.md#projection--dip) |
| Observation / LSP bridge | `proved` for finite violation-count bridges | [Observation bridge と projection bridge の関係](design/observation_projection_bridge.md), [Lean theorem index](lean_theorem_index.md#observation--lsp) |
| Matrix / nilpotence / spectral bridge | `proved` for finite structural bridges; cost interpretation is empirical | [spectral radius bridge 設計](design/spectral_radius_bridge.md), [Lean theorem index](lean_theorem_index.md#matrix-bridge) |
| Runtime propagation | `defined only` / `proved` for 0/1 runtime graph zero bridge; policy-aware coverage is separate | [runtimePropagation 設計](design/runtime_propagation_design.md), [Lean theorem index](lean_theorem_index.md#finite-universe--bridge-theorems) |
| Analytic representation bridge / strength | `defined only` / `proved` for representation-strength accessor theorems | [AAT v2 数学設計書](aat_v2_mathematical_design.md#85-analytic-representation-layer), [Lean theorem index](lean_theorem_index.md#analytic-representation), Issue [#280](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/280) |
| SOLID-style counterexamples | `proved` for current Lean examples | [Lean theorem index](lean_theorem_index.md#solid-counterexamples) |

### Design principle classification boundary

Issue [#386](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/386)
は、数学設計書 4.1 の design principle classification を、Lean で
`DesignPattern` として証明する範囲、Lean schema 候補、future proof obligation、
empirical hypothesis に分ける設計境界として扱う。数学設計書本文には作業状態を
混ぜず、この表を status 管理の入口にする。

| 設計原則 / pattern | 層 | 現在の Lean status | `DesignPattern` として証明する範囲 | docs-only / empirical に残す範囲 |
| --- | --- | --- | --- | --- |
| SRP | 局所契約層 | `defined only` / `proved` via `responsibilityCohesionDesignPattern` | 責務境界を selected responsibility boundary として定義し、boundary totality / functional assignment / edge-local cohesion を invariant family として扱う。Issue [#417](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/417) で Lean 化済み。 | 自然言語としての SRP 全体、責務の意味的発見、組織的 ownership の良し悪し。 |
| OCP | 局所契約層 | `defined only` / `proved` via feature extension packages | 既存 core edge / policy / selected observation を壊さない bounded extension package。 | 任意の拡張が安全であるという主張、未測定 runtime / semantic axis の保存。 |
| LSP | 局所契約層 | `proved` for selected observation bridges | `LocalContractInvariant.lspCompatible` と `localContractDesignPattern` の selected invariant。 | すべての behavioral semantics の完全な置換可能性。 |
| ISP | 局所契約層 | `defined only` / `proved` via `interfaceProjectionRefinementDesignPattern` | interface projection の細分化を selected projection / observation boundary として定義した後の preservation。Issue [#414](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/414) で Lean 化済み。 | 自然言語としての ISP 全体、interface 粒度最適性、API usability。 |
| DIP | 局所契約層 | `proved` for projection / local contract bridges | `LocalContractInvariant.projectionSound` / `dipCompatible` と `localContractDesignPattern` の selected invariant。 | abstraction choice の完全性、すべての runtime / semantic dependency の捕捉。 |
| Layered Architecture | 大域構造層 | `defined only` / `proved` via `structuralLayerDesignPattern` | `StructuralRestrictionOperation` による edge-subset dependency operation family と、`StructuralLayerInvariant.strictLayered` / `decomposable` の selected invariant family。Issue [#403](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/403) で Lean 化済み。 | 層名や実務 convention の完全分類、runtime protocol や semantic contract の decomposability。 |
| Clean Architecture | 大域構造層 | `defined only` / `proved` via `structuralLayerDesignPattern` | 固定された boundary / abstraction policy に相対化した `StructuralLayerInvariant.boundaryPolicySound` / `abstractionPolicySound` の selected invariant family。Issue [#403](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/403) で Lean 化済み。 | すべての framework 境界、effect leakage、組織境界の網羅的検出。 |
| Event Sourcing | 状態遷移代数層 | `defined only` / `proved` via `eventSourcingDesignPattern` | `EventSequenceMonoidLawful`、selected replay law、selected projection law を `eventSourcingDesignPattern` の invariant family として扱う。Issue [#416](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/416) で Lean 化済み。 | 現時点では [relationComplexity 設計](design/relation_complexity_design.md) と pilot dataset 側で測る。実コード event log の完全性、projection completeness、運用コスト改善は主張しない。 |
| Saga | 状態遷移代数層 | `defined only` / `proved` via `sagaDesignPattern` | `SagaWeakRecoveryLawful` により、compensation / weak recovery law を selected finite law cases に相対化した invariant family として扱う。Issue [#416](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/416) で Lean 化済み。 | 補償が一般の逆射であるという主張、全 failure mode の網羅、運用回復コストの証明。 |
| CRUD | 状態遷移代数層 | empirical hypothesis | overwrite relation と履歴喪失 risk を relation-complexity axis として測る。 | CRUD が常に単純または悪いという単一評価、監査・復旧要件の意味的完全性。 |
| Circuit Breaker | 実行時依存層 | `defined only` / `proved` via `runtimeProtectionDesignPattern`; policy-aware metrics are empirical | `RuntimeProtectionInvariant.pathLocalized` / `interactionProtected` / `runtimeFlat` など selected runtime protection invariant を持つ `protect` / `isolate` pattern。Issue [#404](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/404) で Lean 化済み。 | incident reduction、障害修正コスト低下、telemetry completeness、policy-aware coverage の empirical validation。 |
| Replicated Log | 分散収束層 | `defined only` / `proved` via `replicatedLogDesignPattern` | failure model、quorum、ordering、convergence predicate、selected entries に相対化した conditional convergence pattern。Issue [#415](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/415) で Lean 化済み。 | 無条件の可用性・分断耐性・収束性、特定実装の protocol correctness 全体、実コード log completeness。 |

直近の Lean 化候補だった実行時依存層については、Circuit Breaker そのものの
経験的効果ではなく、`protect` / `isolate` の bounded runtime protection package を
selected runtime invariant family として `DesignPattern` schema へ接続する作業を
Issue [#404](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/404)
で完了済みである。

Event Sourcing / Saga は、Issue [#418](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/418)
で定義した `StateTransitionCarrier` / `stateTransitionDesignPattern` を前提に、
Issue [#416](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/416)
で `eventSourcingDesignPattern` / `sagaDesignPattern` として固有の operation family、
invariant family、closure law、non-conclusions を分離した。CRUD は引き続き
empirical / relation-complexity 側に留める。
Replicated Log は、Issue [#415](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/415)
で `ReplicatedLogState` / `ReplicatedLogOperation` / `replicatedLogDesignPattern`
として、failure model、quorum、ordering、convergence predicate、selected entries に
相対化した conditional convergence package を追加した。無条件の可用性、
分断耐性、収束性、特定実装 protocol correctness、実コード log completeness は
non-conclusions として残す。

### Architecture Calculus / Extension Formula task package

Issue [#261](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/261)
は、Architecture Calculus から Structural Architecture Extension Formula へ進む
Lean 証明タスクの親索引である。子 Issue の現在の扱いは次の通り。

| Issue | 対象 | Lean status | 次の扱い |
| --- | --- | --- | --- |
| [#265](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/265) | `ArchitectureOperation` / `ProofObligation` schema と witness mapping theorem | `defined only` / `proved` | 完了済み。実装済み API は [Lean theorem index](lean_theorem_index.md#architecture-operation) を参照する。 |
| [#266](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/266) | repair step decreases theorem / selected obstruction measure | `defined only` / `proved` | 完了済み。実装済み API は [Lean theorem index](lean_theorem_index.md#repair) を参照する。 |
| [#264](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/264) | SplitExtensionLifting / selected section law | `defined only` / `proved` | 完了済み。実装済み API は [Lean theorem index](lean_theorem_index.md#split-extension-lifting) を参照する。 |
| [#262](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/262) | `ArchitectureExtensionFormula_structural` classification theorem | `defined only` / `proved` | `ExtensionCoverage`, `ExtensionObstructionWitness`, classification predicate 群、bounded classification theorem は実装済み。後続の `LawfulExtensionPreservesFlatness` は Issue [#271](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/271) で完了済み。 |
| [#271](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/271) | `LawfulExtensionPreservesFlatness` bounded flatness preservation corollary | `defined only` / `proved` | 完了済み。extension coverage、runtime coverage / flatness、semantic coverage / flatness を明示前提として bounded `ArchitectureFlatWithin` を構成する。 |

#262 は disjoint decomposition ではなく coverage / classification theorem として扱う。
`LawfulExtensionPreservesFlatness` は runtime / semantic flatness と coverage assumptions
を明示前提にした bounded corollary として Issue
[#271](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/271)
で証明済みである。

### AAT calculus / evolution / representation follow-up task package

Issue [#275](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/275)
は、数学設計書の後続 theorem package 群の親索引である。子 Issue の現在の扱いは次の通り。

| Issue | 対象 | Lean status | 次の扱い |
| --- | --- | --- | --- |
| [#276](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/276) / [#383](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/383) / [#384](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/384) / [#411](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/411) / [#385](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/385) / [#414](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/414) / [#403](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/403) / [#404](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/404) / [#418](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/418) / [#416](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/416) / [#415](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/415) | operation family と invariant family の弱い Galois 対応、`Ops` / `Inv` closure API、`OperationRoleSchema` role bridge、local contract layer、ISP projection-refinement layer、global structural layer、runtime protection layer、state-transition algebra layer、Event Sourcing / Saga、および Replicated Log の `DesignPattern` bridge | `defined only` / `proved` | `PreservesInvariant`, `Ops`, `Inv`, `ClosedInvariantSet`, `ClosedOperationSet`, `DesignPattern`, `operationInvariant_galois`、`Ops_antitone`, `Inv_antitone`, `inv_ops_extensive`, `ops_inv_extensive`, `inv_ops_monotone`, `ops_inv_monotone`, `inv_ops_idempotent`, `ops_inv_idempotent` は実装済み。`OperationRoleSchema.operationInvariantSource`, `OperationRoleSchema.operationInvariantTarget`, `OperationRoleSchema.stateInvariantHolds`, `OperationRoleSchema.RoleConclusionIsSelectedPreservation`, `OperationRoleSchema.preservesInvariant_of_discharged_preserve`, `OperationRoleSchema.ops_mem_selectedInvariant_of_discharged_preserve`, `OperationRoleSchema.operationFamily_subset_ops_of_preserves_selected` により、preserve role package を selected invariant / selected operation family に相対化して `PreservesInvariant` / `Ops` へ接続できる。`OperationRoleSchema.RoleConclusionIsSelectedReflection`, `OperationRoleSchema.sourceWitness_exists_of_discharged_reflect`, `OperationRoleSchema.RoleConclusionIsSelectedImprovement`, `OperationRoleSchema.selectedImprovement_of_discharged_improve`, `OperationRoleSchema.RoleConclusionIsSelectedLocalization`, `OperationRoleSchema.selectedLocalization_of_discharged_localize`, `OperationRoleSchema.RoleConclusionIsSelectedTranslation`, `OperationRoleSchema.selectedTranslation_of_discharged_translate`, `OperationRoleSchema.RoleConclusionIsSelectedTransfer`, `OperationRoleSchema.selectedTransfer_of_discharged_transfer`, `OperationRoleSchema.RoleConclusionIsSelectedAssumption`, `OperationRoleSchema.selectedAssumption_of_discharged_assume` により、非 preserve role package を明示的な witness reflection、source-to-target relation、または explicit assumption boundary に相対化して読める。`LocalContractState`, `LocalReplacementOperation`, `LocalContractInvariant`, `localContractDesignPattern`, `localContractDesignPattern_closure_law`, `localContractDesignPattern_records_nonConclusion` により、`LocalReplacementContract` を projection soundness / LSP compatibility / DIP compatibility の selected invariant family を持つ representative `DesignPattern` として扱える。`InterfaceProjectionRefinementState`, `InterfaceProjectionRefinementOperation`, `InterfaceProjectionRefinementInvariant`, `interfaceProjectionRefinementDesignPattern`, `interfaceProjectionRefinementDesignPattern_closure_law`, `interfaceProjectionRefinementDesignPattern_records_nonConclusion` により、ISP を projection refinement / split と selected observation boundary factorization に相対化した representative `DesignPattern` として扱える。`StructuralLayerState`, `StructuralRestrictionOperation`, `StructuralLayerInvariant`, `structuralLayerDesignPattern`, `structuralLayerDesignPattern_closure_law`, `structuralLayerDesignPattern_records_nonConclusion` により、Layered / Clean Architecture を edge-subset operation と selected global structural invariants に相対化した representative `DesignPattern` として扱える。`RuntimeProtectionState`, `RuntimeProtectionOperation`, `RuntimeProtectionInvariant`, `runtimeProtectionDesignPattern`, `runtimeProtectionDesignPattern_closure_law`, `runtimeProtectionDesignPattern_records_nonConclusion` により、`protect` / `isolate` を selected runtime protection invariants に相対化した representative `DesignPattern` として扱える。`StateTransitionCarrier`, `StateTransitionPatternState`, `StateTransitionOperation`, `StateTransitionInvariant`, `stateTransitionDesignPattern`, `stateTransitionDesignPattern_closure_law`, `stateTransitionDesignPattern_records_nonConclusion` により、Event Sourcing / Saga の前提になる state-transition algebra carrier と selected replay / roundtrip / compensation law family の入口を扱える。`EventSequenceMonoidLawful`, `StateProjectionLawful`, `EventSourcingOperation`, `EventSourcingInvariant`, `eventSourcingDesignPattern`, `eventSourcingDesignPattern_closure_law`, `eventSourcingDesignPattern_records_nonConclusion`, `SagaWeakRecoveryLawful`, `SagaOperation`, `SagaInvariant`, `sagaDesignPattern`, `sagaDesignPattern_closure_law`, `sagaDesignPattern_records_nonConclusion` により、Event Sourcing / Saga 固有の bounded theorem package を selected finite law cases に相対化して扱える。`ReplicatedLogState`, `ReplicatedLogOperation`, `ReplicatedLogInvariant`, `replicatedLogDesignPattern`, `replicatedLogDesignPattern_closure_law`, `replicatedLogDesignPattern_records_nonConclusion` により、Replicated Log を failure model / quorum / ordering / convergence predicate / selected entries に相対化した conditional convergence package として扱える。role tag だけからの global preservation、reflection、improvement、localization、translation、transfer、assumption discharge、束同型、完全分類、selected preservation relation 外の保存性、局所契約層からの無条件の `Decomposable` / `StrictLayered`、自然言語としての ISP 全体、interface 粒度最適性、API usability、層名 convention の完全分類、runtime / semantic decomposability、global flatness preservation、incident reduction、障害修正コスト低下、runtime telemetry completeness、policy-aware coverage completeness、extractor completeness、実コード event log completeness、projection completeness、補償の一般逆射性、全 failure mode coverage、無条件の可用性、分断耐性、収束性、特定実装 protocol correctness、実コード log completeness、運用コスト改善、CRUD の一般 theorem 化は non-conclusions として扱う。 |
| [#279](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/279) | Architecture Calculus laws の bounded theorem package | `defined only` / `proved` | `ArchitectureCalculusLaw`, law kind、bounded assumption package、identity / associativity / edge-union / refinement-abstraction / edge-equivalence / protection idempotence / runtime localization / reverse involution / repair witness-mapping / synthesis soundness constructor、`conclusion_of_assumptions` は実装済み。無条件の結合法則、全 operation の冪等性、global flatness preservation は non-conclusions として扱う。 |
| [#277](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/277) | repair termination / synthesis / no-solution certificate soundness | `defined only` / `proved` | `BoundedRepairPlan`, `FiniteRepairPackage`, `SynthesisConstraintSystem`, `SynthesisSoundnessPackage`, `NoSolutionCertificate`, `ValidNoSolutionCertificate`, `NoSolutionCertificate.sound_of_valid` は実装済み。solver が `none` を返すだけでは非存在を主張しない。 |
| [#278](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/278) | ArchitectureEvolution transition theorem package | `defined only` / `proved` | `ArchitectureTransition`, `ArchitectureEvolution`, `TransitionPreservesFlatness`, `DriftObstructionSchema`, `MigrationSequence`, `EveryStepLawful`, `EventuallyFlat` は実装済み。実装済み API は [Lean theorem index](lean_theorem_index.md#architecture-evolution) を参照する。transition schema は bounded flatness predicate と selected witness reporting に相対化され、global extractor completeness や全 obstruction coverage は non-conclusions として扱う。 |
| [#280](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/280) | AnalyticRepresentation bridge と representation strength | `defined only` / `proved` | `AnalyticRepresentation`, `ZeroPreserving`, `ZeroReflecting`, `ObstructionPreserving`, `ObstructionReflecting`, `ObstructionValuation`, `ZeroReflectingSum` は実装済み。zero-reflecting / obstruction-reflecting は coverage、witness completeness、semantic contract coverage に相対化し、witness absence だけから flatness を主張しない。 |

### Mathematical design follow-up task package

Issue [#284](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/284)
は、数学設計書に残る小さな Lean theorem package の親索引である。
子 Issue の現在の扱いは次の通り。

| Issue | 対象 | Lean status | 次の扱い |
| --- | --- | --- | --- |
| [#285](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/285) | `NonFillabilityWitness` の bounded completeness theorem | `defined only` / `proved` | `WitnessUniverseComplete` と `obstructionAsNonFillability_complete_bounded` は実装済み。bounded completeness は有限 witness universe 完全性前提に相対化され、global semantic completeness は主張しない。 |
| [#286](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/286) | Coupon feature extension example の semantic witness / valuation theorem | `defined only` / `proved` | coupon / discount path skeleton、`roundingTrace`、selected filler contracts、trace 計算 theorem、`roundingOrder_refutes_selectedDiagramFiller`, `roundingOrder_nonFillabilityWitnessFor`, `roundingOrderValuation_obstruction`, `roundingOrderValuation_positive`, `roundingOrderValuation_recordsNonConclusions` は実装済み。valuation は selected rounding-order residual に限られ、未測定 semantic axis の zero 性や実コード extractor completeness は主張しない。 |
| [#288](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/288) | Complexity Transfer の bounded theorem package | `defined only` / `proved` | `ArchitectureTransform`, `SelectedComplexityMeasure`, `RequirementSchema`, `ComplexityTransferSchema`, `BoundedComplexityTransferPackage`, `complexityTransfer_alternative`, `no_free_elimination_bounded` は実装済み。empirical cost 改善、global complexity conservation、selected witness universe 外の completeness は non-conclusions として扱う。 |
| [#287](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/287) | ArchitectureCore / CertifiedArchitecture の proof-carrying schema | `defined only` / `proved` for accessor theorems | `ArchitectureCore`, `ArchitectureLawUniverse`, `ArchitectureTheoremPackage`, `CertifiedArchitecture` を実装済み。実コード extractor の完全性、runtime telemetry completeness、global semantic universe completeness は主張しない。 |

### Split / operation / runtime-semantic follow-up task package

Issue [#296](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/296)
は、数学設計書に残る split / operation / runtime-semantic Lean 実装の親索引である。
子 Issue の現在の扱いは次の通り。

| Issue | 対象 | Lean status | 次の扱い |
| --- | --- | --- | --- |
| [#299](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/299) | Static split failure witness の coverage-aware diagnostic theorem | `defined only` / `proved` | `SelectedStaticSplitExtension`, `StaticExtensionWitness`, `StaticSplitFailureCoverage`, soundness theorem、bounded completeness theorem、coverage 相対の同値 theorem は実装済み。runtime flatness、semantic flatness、global extractor completeness は non-conclusions として扱う。 |
| [#373](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/373) | ExtensionCoverageComplete failure witness package | `defined only` / `proved` | `ExtensionCoverageWitness`, `ExtensionCoverageWitnessExists`, `ExtensionCoverageFailureCoverage`、soundness theorem、bounded completeness theorem、coverage 相対の同値 theorem は実装済み。これは supplied `ComponentUniverse` 上の coverage-only 診断であり、`StaticExtensionWitness` が扱う static split law failure、runtime / semantic flatness、extractor completeness とは分離する。 |
| [#297](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/297) | `NonSplitExtensionWitness` の soundness / bounded completeness package | `defined only` / `proved` | `SelectedSplitExtension`, `SelectedExtensionObstructionWitness`, `NonSplitExtensionWitnessPackage`、soundness theorem、coverage / exactness assumptions 相対の bounded completeness theorem、同値版は実装済み。global witness completeness は主張しない。 |
| [#300](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/300) | Runtime / Semantic split preservation の bounded theorem package | `defined only` / `proved` | `RuntimeInteractionProtected`, `FeatureDiagramsCommute`, `RuntimeSemanticSplitPreservation`、runtime / semantic flatness discharge theorem、`LawfulExtensionPreservesFlatness` 接続 corollary は実装済み。runtime telemetry completeness、global semantic completeness、policy-aware runtime metrics は non-conclusions として扱う。 |
| [#338](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/338) | StaticSplit 由来の中間 preservation corollary | `proved` | `boundaryPolicySound_of_staticSplitExtension`, `abstractionPolicySound_of_staticSplitExtension`, `lspCompatible_of_staticSplitObservationFactorsThrough`, `projectionSound_of_staticSplitProjectionExact`, `projectionSound_of_staticSplitEdgeDecomposition` を実装済み。static split だけで acyclicity、projection soundness、LSP、runtime / semantic flatness、global flatness が出るとは主張しない。 |
| [#298](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/298) / [#339](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/339) | ArchitectureOperation の concrete graph transformation kernel | `defined only` / `proved` | `ConcreteGraphOperation`、`ArchGraph.reverse`、`FiniteArchGraph.reverse`、graph-level identity としての `FiniteArchGraph.protect`、edge union としての `ArchGraph.compose` / `FiniteArchGraph.compose`、edge equivalence precondition に相対化した `ArchGraph.replace` / `FiniteArchGraph.replace`、schema 接続 theorem、reverse involution / protect edge preservation / compose edge subset / replacement edge equivalence theorem は実装済み。無条件の全 operation laws、global flatness preservation、runtime / semantic preservation completeness は主張しない。 |

### FeatureExtension Lean API completion package

Issue [#371](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/371)
は、FeatureExtension / SplitExtension 周辺の公開 API を、bounded / selected /
coverage-aware な theorem package として読みやすくするための親索引である。
数学設計書本文には作業状態を混ぜず、実装済み API と残る non-conclusions は
[Lean theorem index](lean_theorem_index.md#feature-extension) とこの表で管理する。

| Issue | 対象 | Lean status | 次の扱い |
| --- | --- | --- | --- |
| [#372](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/372) | featureView の observation-relative law package | `defined only` / `proved` | `FeatureViewSound`, `FeatureObservationCoverage`, `FeatureViewSectionPackage`, `featureObservationCoverage_of_featureViewSound`, `featureViewSectionPackage_of_featureViewSound`, `SplitExtensionLiftingData.featureViewSectionPackage`, `SplitExtensionLiftingData.featureViewSectionPackage_observes` は実装済み。selected observation model に相対化し、strict equality、全 component の一意分解、global split completeness は主張しない。 |
| [#373](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/373) | `ExtensionCoverageComplete` failure witness package | `defined only` / `proved` | `ExtensionCoverageWitness`, `ExtensionCoverageWitnessExists`, `ExtensionCoverageFailureCoverage` と soundness / bounded completeness / iff theorem は実装済み。coverage-only 診断であり、`StaticExtensionWitness` の static split law failure、runtime / semantic flatness、extractor completeness とは分離する。 |
| [#374](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/374) | `SplitFeatureExtensionWithin` / preservation package の公開 API | `defined only` / `proved` | `SplitFeatureExtensionWithin`, `splitFeatureExtensionWithin_of_runtimeSemanticSplitPreservation`, `splitFeatureExtensionWithin_recordsNonConclusions`, `architectureFlatWithin_of_splitFeatureExtensionWithin` は実装済み。結論は bounded `ArchitectureFlatWithin` であり、global `ArchitectureFlat`、runtime / semantic completeness、extractor completeness は自動導出しない。 |
| [#375](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/375) | FeatureExtension 節の Lean theorem index / proof obligations 再整理 | docs index / design tracking | この表と [Lean theorem index](lean_theorem_index.md#feature-extension) で、#372 / #373 / #374 の API 配置、既存 `StaticSplitFeatureExtension` / `SplitExtensionLiftingData` / `LawfulExtensionPreservesFlatness` との対応、意図的な non-conclusions を分離して管理する。 |

### Architecture Calculus Chapter 3 completion package

Issue [#356](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/356)
は、第3章 Architecture Calculus の operation catalog、operation role、proof obligation、
calculus law を Lean public API として揃えるための親索引である。数学設計書には
作業状態を混ぜず、この文書と
[Lean theorem index](lean_theorem_index.md#architecture-operation) で Lean status と
残る non-conclusions を管理する。

| Issue | 対象 | Lean status | 次の扱い |
| --- | --- | --- | --- |
| [#409](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/409) | 第3章 theorem package の `proved` status 分類 | docs index / design tracking | この節と [Lean theorem index](lean_theorem_index.md#architecture-operation) で、schema / accessor theorem / schema bridge / substantive theorem / non-conclusion の読み分けを管理する。`proved` は無条件の operation law や global flatness preservation を意味しない。 |
| [#357](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/357) | `ArchitectureOperationKind` と `OperationProofObligation` の第3章 catalog 対応 | `defined only` / `proved` for existing schema accessor theorems | `compose`, `refine`, `abstract`, `replace`, `split`, `merge`, `isolate`, `protect`, `migrate`, `reverse`, `contract`, `repair`, `synthesize` の tag と proof-obligation constructor は実装済み。これらの tag / constructor だけから preservation、improvement、runtime / semantic completeness、global flatness preservation は主張しない。 |
| [#358](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/358) / [#411](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/411) | operation role schema | `defined only` / `proved` for schema accessor and bounded bridge theorems | `ArchitectureOperationRole` と `OperationRoleSchema` により、Preserve / Reflect / Improve / Localize / Translate / Transfer / Assume を theorem package から参照できる。preserve は selected invariant preservation、reflect は post-to-pre witness reflection、improve / localize / translate / transfer は selected source-to-target relation、assume は explicit assumption boundary に相対化した bridge を持つ。role tag / schema だけから preservation、reflection、improvement、localization、translation、transfer、assumption discharge は主張しない。 |
| [#359](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/359) | full catalog の concrete / semantic / runtime kernel 配置 | design / future proof obligation | [Architecture Calculus catalog placement](design/architecture_calculus_catalog_placement.md) で、operation ごとに graph-level kernel、contract / observation schema、runtime / semantic package、repair / synthesis package の配置を分ける。 |
| [#360](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/360) | calculus law package と concrete theorem の接続 | `defined only` / `proved` | `finiteComposeEdgeUnionLaw`, `finiteReplaceEdgeEquivalenceLaw`, `isolateRuntimeLocalizationLaw`, `protectRuntimeProtectionLaw`, `finiteProtectIdempotenceLaw`, `finiteReverseInvolutionLaw`, `repairStepDecreasesLaw`, `synthesisCandidateSoundnessLaw`, `noSolutionCertificateSoundnessLaw` により、bounded `ArchitectureCalculusLaw` entrypoint と concrete graph / runtime / repair / synthesis theorem を接続済み。無条件の associativity、全 operation の冪等性、global flatness preservation、runtime / semantic completeness、solver completeness、all obstruction removal は主張しない。 |
| [#381](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/381) | interface-mediated `compose` の bounded associativity package | `defined only` / `proved` | `InterfaceMediatedComposeCompatibility`, `InterfaceMediatedComposeCoverage`, `InterfaceMediatedComposeExact`, `InterfaceMediatedComposeObserved`, `interfaceMediatedComposeAssociativityLaw` により、declared interface、coverage、exactness、observation equivalence に相対化した compose associativity package を公開済み。結論は finite edge-union associativity と選択 observation equivalence に限り、runtime / semantic completeness、global flatness preservation、無条件の operation associativity は主張しない。 |
| [#378](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/378) | `refine` / `abstract` の observation equivalence package | `defined only` / `proved` | `refineObservationEquivalence`, `abstractObservationEquivalence`, `RefinementProjectionContract`, `RefinementObservationContract`, `AbstractionProjectionContract`, `AbstractionObservationContract`, `RefinementAbstractionObserved`, `refinementObservationEquivalenceLaw`, `abstractionObservationEquivalenceLaw` により、refinement soundness と abstraction soundness を selected projection / observation / external observation equivalence 前提に相対化して公開済み。strict equality、全 component の一意分解、global projection completeness、runtime / semantic completeness は主張しない。 |
| [#380](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/380) | `replace` と `LocalReplacementContract` の observation preservation 接続 | `defined only` / `proved` | `localReplacementPreservationLaw` と `localReplacementViolationZeroLaw` により、local contract replacement を bounded `replace` law package として公開済み。projection soundness、`LSPCompatible`、finite projection / LSP violation zero は explicit `LocalReplacementContract` 前提からのみ得る。edge equivalence replacement、global flatness preservation、runtime / semantic preservation completeness は結論しない。 |
| [#379](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/379) | `merge` / `contract` の external contract preservation package | `defined only` / `proved` | `mergeExternalContractPreservation`, `contractExplicitizationSoundness`, `MergedBoundaryContract`, `ExplicitContractSound`, `mergeExternalContractPreservationLaw`, `contractExplicitizationLaw` により、merged boundary と explicit contract を exact projection、representative stability、observation factorization、selected observation preservation に相対化して公開済み。extractor completeness、semantic completeness、global flatness は結論しない。 |
| [#377](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/377) | `isolate` / `protect` の runtime localization package | `defined only` / `proved` | `runtimeLocalization`, `RuntimePathLocalizedWithin`, `RuntimeProtectionContract`, `isolateRuntimeLocalizationLaw`, `protectRuntimeProtectionLaw` により、selected region / component universe に相対化した runtime path localization と policy-aware `RuntimeInteractionProtected` を bounded runtime flatness に接続済み。runtime telemetry completeness、semantic diagram completeness、global protection idempotence は主張しない。 |
| [#410](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/410) | `migrate` の bounded migration theorem package | `defined only` / `proved` | `migrationCompatibility`, `StagedMigrationPath`, `MigrationCompatibilityWindow`, `MigrationObserved`, `migrateObservationEquivalenceLaw` により、staged migration path、compatibility window、old / new observation equivalence を明示前提に相対化した bounded package を公開済み。runtime telemetry completeness、semantic completeness、global flatness preservation は結論しない。 |
| [#412](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/412) | `reverse` と upstream impact / blast radius 診断の接続 | `defined only` / `proved` | `ArchGraph.reachable_reverse_iff`, `ArchGraph.reverseReachableCone`, `ArchGraph.mem_reverseReachableCone_iff`, `FiniteArchGraph.reverse_reachableConeSizeAt_eq_reverseReachableConeSize_under_universe` により、reverse graph 上の reachable cone を source graph の incoming reachability として読む bounded bridge を追加済み。incident prediction、telemetry completeness、extractor completeness、runtime cost correlation は結論しない。 |

第3章 full catalog の配置は次の通りである。ここでの配置は Lean theorem package の責務境界であり、
operation tag だけから無条件の graph transform、runtime / semantic completeness、global flatness
preservation は結論しない。

| Operation | 配置 | Lean status / 境界 |
| --- | --- | --- |
| `compose` | concrete graph kernel + interface compatibility law | edge union kernel と finite edge associativity は実装済み。interface-mediated bounded associativity は declared interface、coverage、exactness、observation equivalence 前提に相対化し、runtime / semantic completeness や global flatness preservation は主張しない。 |
| `refine` | semantic / contract package | `RefinementProjectionContract`, `RefinementObservationContract`, `refinementObservationEquivalenceLaw` により、projection soundness と selected observation preservation を明示前提から得る bounded package を実装済み。strict equality、全 component の一意分解、global projection completeness は主張しない。 |
| `abstract` | projection / observation package | `AbstractionProjectionContract`, `AbstractionObservationContract`, `RefinementAbstractionObserved`, `abstractionObservationEquivalenceLaw` により、exact projection、selected observation preservation、external observation equivalence を明示前提から得る bounded package を実装済み。runtime / semantic completeness、global projection completeness は主張しない。 |
| `replace` | concrete graph kernel + local contract package | edge equivalence replacement は finite graph kernel 側、`LocalReplacementContract` による observation preservation は contract / observation 側の bounded law package として実装済み。いずれも explicit precondition に相対化し、global flatness preservation や runtime / semantic preservation completeness は主張しない。 |
| `split` | feature extension / split package | static split evidence と runtime / semantic split preservation を別前提として扱う。 |
| `merge` | contract / observation package | `MergedBoundaryContract`, `mergeExternalContractPreservationLaw` により、merged boundary の external contract preservation を exact projection、representative stability、observation factorization 前提から得る bounded package を実装済み。extractor completeness、semantic completeness、global flatness は主張しない。 |
| `isolate` | runtime / semantic localization package | `RuntimePathLocalizedWithin`, `isolateRuntimeLocalizationLaw` により、selected boundary / region 内への runtime path localization と bounded runtime flatness を explicit coverage / protection 前提から得る。runtime telemetry completeness、semantic diagram completeness は主張しない。 |
| `protect` | concrete graph identity kernel + runtime policy package | static graph kernel は identity。`RuntimeProtectionContract`, `protectRuntimeProtectionLaw` により policy-aware runtime protection を selected path localization、`RuntimeInteractionProtected`, bounded runtime flatness に接続する。global protection idempotence、runtime telemetry completeness は主張しない。 |
| `migrate` | runtime / semantic package | `StagedMigrationPath`, `MigrationCompatibilityWindow`, `MigrationObserved`, `migrateObservationEquivalenceLaw` により、migration sequence、compatibility window、old / new observation equivalence を explicit assumption として束ねる bounded package を実装済み。runtime telemetry completeness、semantic completeness、global flatness preservation は主張しない。 |
| `reverse` | concrete graph kernel + diagnostic bridge | graph reverse kernel と reverse involution は実装済み。reverse graph 上の reachable cone は source graph の incoming reachability と同値であり、finite universe 上の executable bounded cone と graph-level reverse cone の bridge を実装済み。incident prediction、telemetry completeness、extractor completeness は主張しない。 |
| `contract` | contract / observation package | `ExplicitContractSound`, `contractExplicitizationLaw` により、implicit expectation を interface-level explicit contract へ写す soundness を selected projection / observation model に相対化して実装済み。semantic completeness、global flatness、extractor completeness は主張しない。 |
| `repair` | repair package | selected obstruction universe と admissible rule 前提に相対化した measure decrease / finite clearing を使う。 |
| `synthesize` | synthesis package | `RepairSynthesis.lean` の candidate soundness / valid no-solution certificate soundness を入口にする。solver completeness は主張しない。 |

### Mathematical design completion audit package

Issue [#324](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/324)
は、数学設計書そのものに作業状態を混ぜず、Lean theorem index とこの proof obligation
index が最終的な Lean API、残る non-conclusions、empirical boundary を正しく分担しているかを
同期するための索引である。

現在の Lean source では、下表の theorem package は `docs/lean_theorem_index.md` に
公開 API として索引済みである。残る仕上げ Issue は、新しい global theorem を要求するもの
ではなく、入口 theorem、bounded / coverage assumptions、non-conclusions の読み方を
監査する docs / theorem-package tracking として扱う。

| Issue | 対象 | 現在の扱い | 残す境界 |
| --- | --- | --- | --- |
| [#321](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/321) / [#326](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/326) | Non-split witness / Architecture Extension Formula | `NonSplitExtensionWitnessPackage.not_selectedSplitExtension_of_selectedExtensionObstructionWitness`, `NonSplitExtensionWitnessPackage.selectedExtensionObstructionWitnessExists_of_not_selectedSplitExtension`, `NonSplitExtensionWitnessPackage.selectedExtensionObstructionWitnessExists_iff_not_selectedSplitExtension`, `ArchitectureExtensionFormula_structural` は索引済み。 | disjoint decomposition、global witness completeness、global obstruction completeness、extractor completeness は主張しない。 |
| [#337](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/337) | Architecture Extension Formula の multi-label classification layer | `MultiLabelExtensionObstructionWitness`, `ExtensionObstructionWitness.toMultiLabel`, `ExtensionObstructionWitness.toMultiLabel_label_iff`, `fillingFailureExtensionObstructionWitness_multilabel_classified`, `ArchitectureExtensionFormula_multilabel_structural` は索引済み。 | multi-label は同一 witness の複数分類を許す coverage layer であり、disjoint decomposition、global witness completeness、global obstruction completeness は主張しない。 |
| [#339](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/339) | Concrete graph operation kernel の compose / replace 拡張 | `EdgeEquivalent`, `ArchGraph.compose`, `FiniteArchGraph.compose`, `ArchGraph.replace`, `FiniteArchGraph.replace`, `ConcreteGraphOperation.compose`, `ConcreteGraphOperation.replace` と、それぞれの edge / kind / schema 接続 theorem は索引済み。 | `compose` は同一 component 型上の edge union kernel に限る。`replace` の source edge preservation は `EdgeEquivalent` precondition に相対化する。無条件の acyclicity preservation、global flatness preservation、runtime / semantic preservation は主張しない。 |
| [#340](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/340) | Diagram filling failure から Architecture Extension Formula への bounded bridge | `FillingFailureWitnessPayload`, `fillingFailureExtensionObstructionWitness`, `fillingFailureExtensionObstructionWitness_classified`, `FillingFailureRefutesSplit`, `not_selectedSplitExtension_of_fillingFailurePayload`, `FillingFailureBridgePackage.toNonSplitExtensionWitnessPackage` は索引済み。 | `NonFillabilityWitnessFor` 単独から `¬ SplitExtension` は結論しない。split failure への接続は `FillingFailureRefutesSplit` と selected payload coverage / exactness assumptions に相対化する。 |
| [#341](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/341) | coupon feature の static hidden dependency canonical example | `CouponStaticDependencyExample.goodStaticSplitFeatureExtension`, `hiddenDependencyWitness`, `hiddenDependencyWitnessExists`, `bad_not_selectedStaticSplitFeatureExtension`, `repairedStaticSplitFeatureExtension`, `repaired_selectedStaticSplitFeatureExtension` は索引済み。 | selected static hidden dependency witness に限る。runtime flatness、semantic flatness、extractor completeness は主張しない。 |
| [#372](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/372) | featureView の observation-relative law package | `FeatureViewSound`, `FeatureObservationCoverage`, `FeatureViewSectionPackage`, `featureObservationCoverage_of_featureViewSound`, `featureViewSectionPackage_of_featureViewSound`, `SplitExtensionLiftingData.featureViewSectionPackage`, `SplitExtensionLiftingData.featureViewSectionPackage_observes` は索引済み。 | selected observation model に相対化する。strict equality、全 component の一意分解、global split completeness、runtime / semantic flatness、extractor completeness は主張しない。 |
| [#322](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/322) / [#327](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/327) | Architecture Calculus / Repair / Synthesis | `ArchitectureOperation.generatedObligation_kind`, `ArchitectureOperation.exists_sourceWitness_of_targetWitness`, `ArchitectureCalculusLaw.conclusion_of_assumptions`, `ArchitectureCalculusLaw.finiteComposeEdgeUnionLaw_conclusion`, `ArchitectureCalculusLaw.finiteReplaceEdgeEquivalenceLaw_conclusion`, `ArchitectureCalculusLaw.isolateRuntimeLocalizationLaw_conclusion`, `ArchitectureCalculusLaw.protectRuntimeProtectionLaw_conclusion`, `ArchitectureCalculusLaw.finiteProtectIdempotenceLaw_conclusion`, `ArchitectureCalculusLaw.finiteReverseInvolutionLaw_conclusion`, `ArchitectureCalculusLaw.repairStepDecreasesLaw_conclusion`, `ArchitectureCalculusLaw.synthesisCandidateSoundnessLaw_conclusion`, `ArchitectureCalculusLaw.noSolutionCertificateSoundnessLaw_conclusion`, `repairStepDecreases_of_admissible`, `BoundedRepairPlan.selectedObstructionsCleared`, `FiniteRepairPackage.selectedObstructionsCleared`, `SynthesisSoundnessPackage.candidate_satisfies`, `NoSolutionCertificate.sound_of_valid` を代表入口として索引済み。 | unconditional operation laws、runtime / semantic completeness、solver completeness、global flatness preservation は主張しない。finite repair は selected obstruction universe と明示 plan assumptions に相対化する。 |
| [#323](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/323) / [#328](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/328) | Analytic Representation / Complexity Transfer | `AnalyticRepresentation.analyticZero_of_structuralZero`, `AnalyticRepresentation.structuralZero_of_analyticZero`, `AnalyticRepresentation.analyticObstruction_of_structuralObstruction`, `AnalyticRepresentation.structuralObstruction_of_analyticObstruction`, `ObstructionValuation.no_obstruction_of_value_zero`, `ObstructionValuation.noSelectedObstruction_of_zeroReflectingSum`, `BoundedComplexityTransferPackage.no_free_elimination_bounded` を代表入口として索引済み。 | analytic value だけから flatness を結論しない。empirical cost 改善、global complexity conservation、lower bound は無条件に主張しない。reflecting direction は coverage / completeness assumptions に相対化する。 |

### Reviewer follow-up theorem / counterexample package

Issue [#347](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/347)
は、公開 docs に基づく数学的査読で提案された追加 theorem / counterexample の
追跡親 Issue である。数学設計書には作業状態を混ぜず、この文書で Lean proof
obligation として管理する。

| Issue | 対象 | Lean status | 次の扱い |
| --- | --- | --- | --- |
| [#349](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/349) | StaticSplit の identity / composition theorem package | `defined only` / `proved` | `identityFeatureExtension`, `identityStaticSplitFeatureExtension`, `selectedStaticSplitExtension_identity`, `composeFeatureExtension`, `StaticSplitCompositionAssumptions`, `staticSplitFeatureExtension_compose`, `selectedStaticSplitExtension_compose` を追加済み。composition は graph compatibility、interface factorization、policy transport 前提に相対化する。runtime / semantic flatness、global `ArchitectureFlat`、無条件の global composition law は主張しない。 |
| [#351](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/351) | 有限 acyclic graph から strict layering を構成する theorem | proved | `ComponentUniverse.sourceDepthLayer`, `ComponentUniverse.sourceDepthLayer_strictLayering_of_acyclic`, `ComponentUniverse.strictLayered_of_acyclic`, `FiniteArchGraph.strictLayered_of_acyclic` を追加済み。finite universe と decidable edge relation に相対化する static graph-level bridge であり、semantic contract、runtime protocol、一般の contractual decomposability は結論しない。 |
| [#350](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/350) | selected witness universe の monotonicity theorem package | proved | `WitnessUniverseIncluded`, `MeasuredViolationExists`, `NoMeasuredViolation`, `mem_violatingWitnesses_of_witnessUniverseIncluded`, `measuredViolationExists_of_witnessUniverseIncluded`, `noMeasuredViolation_of_witnessUniverseIncluded`, `violationCount_eq_zero_of_witnessUniverseIncluded` を追加済み。witness existence は universe enlargement に対して保存され、no measured violation / count 0 は inclusion に沿って large から small へ保存される。set-like inclusion は重複を保存しないため、duplicate-sensitive count monotonicity や selected universe 外の global completeness は主張しない。 |
| [#352](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/352) | ProjectionExact と RepresentativeStable から quotient well-definedness への bridge | proved | `strongDIPCompatible_of_projectionExact_representativeStable`, `quotientWellDefined_of_projectionExact_representativeStable`, `projectedDeps_iff_abstractEdge_of_projectionExact_representativeStable`, `projectedDeps_iff_abstractEdge_of_strongDIPCompatible` を追加済み。soundness-only projection から completeness / quotient exactness は結論しない。 |
| [#348](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/348) | static flat だが semantic obstruction が残る canonical counterexample | proved | `StaticSemanticCounterexample.canonical_staticFlatWithin`, `canonical_not_semanticFlatWithin`, `canonical_not_architectureFlat`, `staticFlat_with_semanticObstruction`, `staticFlat_not_architectureFlat` を追加済み。selected repaired static skeleton と selected coupon / discount semantic diagram に相対化し、static split / static flatness から semantic flatness、runtime flatness、global `ArchitectureFlat`、extractor completeness は結論しない。 |
| [#353](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/353) | repair が selected measure を減らしても別軸 obstruction が増える counterexample | proved | `RepairTransferCounterexample.selectedRepairStep_decreases`, `selectedRepairStep_decreases_of_admissible`, `runtimeAxisMeasure_increases`, `runtimeAxisViolationCount_before`, `runtimeAxisViolationCount_after`, `selectedRepairStep_not_all_axes_nonincreasing`, `staticSplitRepair_transfers_runtime`, `counterexamplePackage` を追加済み。repair theorem は selected obstruction measure に相対化され、同じ endpoint で別軸 runtime obstruction / transferred complexity が増え得る。全 axis の単調改善、global flatness preservation、empirical cost 改善、global complexity conservation は主張しない。 |

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
| numerical curvature | finite diagram / zero-separating distance の proved bridge と、positive-weight bounded bridge を、calibrated Signature axis や現実コストとの相関から分ける。 |
| unconditional operation calculus laws | `compose`, `replace`, `protect`, `reverse`, `repair` の bounded law package と concrete entrypoint はあるが、無条件の結合法則、全 operation の冪等性、global flatness preservation、solver completeness、all obstruction removal は主張しない。 |
| extractor completeness | extractor output は tooling evidence であり、完全な proof-carrying universe とは同一視しない。 |
| relation complexity | 状態遷移代数層の empirical metric として扱い、構成要素ベクトルを残す。単一スコアだけで設計を評価しない。 |

## Bounded theorem package 強化ロードマップ

数学設計書の中心 theorem 候補は、現時点では無条件の global theorem ではなく、
coverage-aware / bounded theorem package として扱う。今後も
`ArchitectureFlatWithin` を主語にし、global `ArchitectureFlat` は coverage /
exactness / no-unmeasured-axis が閉じた場合の certificate-backed completion
corollary として扱う。

この方針により、AAT v2 は「アーキテクチャが無条件に良い」と主張するのではなく、
どの universe、coverage、observation model、witness family の下で、どの不変量が
保存・改善・移転されたかを明示する。

| 領域 | 次の扱い | Lean status |
| --- | --- | --- |
| flatness / feature extension theorem package | `ArchitectureFlatWithin` を primary な bounded theorem package とし、`SplitFeatureExtensionWithin` / `LawfulExtensionPreservesFlatness` / `LawfulExtensionPreservesFlatness_of_runtimeSemanticSplitPreservation` は coverage と runtime / semantic evidence を明示前提にする。global `ArchitectureFlat` は certificate-backed completion に限る。親 Issue [#320](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/320) の統合範囲で扱い、API 監査は子 Issue [#325](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/325) で完了済み。`SplitFeatureExtensionWithin` の公開 API 整理は Issue [#374](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/374) で完了済み。 | `defined only` / `proved` |
| global flatness completion | `GlobalFlatCertificate`, `ArchitectureFlat`, `globalFlat_of_within_exhaustive` を certificate theorem として定義する。`ArchitectureFlatWithin` を primary theorem とし、global theorem は exhaustive coverage / exact observation / recorded non-conclusions がそろう場合の completion corollary に限る。Issue [#308](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/308) | `defined only` / `proved` for completion accessors |
| claim / evidence boundary | `ClaimLevel`, `MeasurementBoundary`, `ArchitectureClaim` で `formal`, `tooling`, `empirical`, `hypothesis` の claim level と non-conclusions を明示する。tooling output と Lean theorem の境界、および unmeasured と measured-zero の区別を保つ。Issue [#309](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/309) | `defined only` / `proved` for boundary accessors |
| weighted numerical curvature | `PositiveCurvatureWeightOn` と `totalWeightedCurvature` により、positive weight 前提つきで weighted aggregate zero と measured numerical curvature obstruction 不在を接続する。cost correlation は empirical hypothesis に残す。Issue [#310](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/310) | `defined only` / `proved` |
| complexity transfer beyond bounded package | 既存の bounded complexity transfer package を土台に、selected runtime / semantic / policy target への移転 predicate、coverage / exactness residual gap predicate、`no_free_elimination_bounded` を定義する。global conservation / lower bound は将来拡張とする。Issue [#311](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/311) | `defined only` / `proved` |
| chapter 7 theorem package index | `Chapter7TheoremPackages.Candidate`、`representativeDeclarations`、`schematicCorrespondences`、`nonConclusionBoundary` を docs-facing metadata として扱い、`lean_theorem_index.md` とこの文書で 7.1〜7.6 の対応を追跡する。Issue [#419](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/419), [#420](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/420), [#421](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/421), [#422](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/422) | docs index / API integration tracking |
| cohomological obstruction candidate | AAT v2 core には混ぜず、core theorem package からの import 依存も追加しない。将来の experimental module として扱う場合は、`DiagramFiller` / `NonFillabilityWitness` / `PathHomotopy` への forgetful bridge、toy model、既存 bounded witness universe と矛盾しない exit criteria を先に満たす。Issue [#312](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/312) | future extension |

これらのタスクでは、実コード extractor の完全性、telemetry の完全性、empirical cost
correlation、incident zero は Lean theorem として直接主張しない。必要な場合は
bridge assumption、validation protocol、または empirical hypothesis として分離する。
追跡親 Issue は [#307](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/307)
である。

## 更新ルール

- Lean theorem、定義、module path を追加・削除・rename した場合は、必要に応じて
  [Lean 定義・定理索引](lean_theorem_index.md) を更新する。
- 未解決 proof obligation が新しい設計判断を必要とする場合は、GitHub Issue へ分離し、
  この文書にはカテゴリとリンクだけを残す。
- empirical protocol や dataset schema の詳細は `docs/design/` または `docs/empirical/`
  に置き、この文書へ詳細表を複製しない。
- `proved`, `defined only`, `future proof obligation`, `empirical hypothesis` を混同しない。
