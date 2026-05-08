# AAT 理論総合入口

この文書は、Algebraic Architecture Theory の第一級理論文書への入口である。
理論本文は次の三部構成に分ける。

1. [Part 1: AAT 基礎編](aat/part1_foundations.md)
2. [Part 2: AAT 発展編](aat/part2_advanced_theory.md)
3. [Part 3: Architecture Dynamics / Chaos Game 編](aat/part3_dynamics_chaos_game.md)

この入口文書は、旧来の参照先を受けるための薄い索引も兼ねる。実装、運用、実証、
作業管理の情報は持たない。AAT の第一級理論は、
feature extension、operation、invariant、obstruction witness、proof obligation、
certificate、signature trajectory を、管理情報から切り離した数学的語彙として扱う。

## 中心命題

AAT は、ソフトウェア開発を architecture extension の理論として扱う。

```text
software development
  = architecture extension
  + operation
  + invariant
  + obstruction witness
  + proof obligation
  + certificate
```

最初の問いは、ある feature addition が既存 architecture を lawful に拡大しているかである。
発展した問いは、反復される operation が architecture signature の軌道をどの方向へ曲げるか
である。

```text
architecture
  = future operation distribution を曲げる field

software quality
  = signature trajectory の安定性と方向
```

## 0. 中心命題

中心命題の詳細は [Part 1: AAT 基礎編](aat/part1_foundations.md#1-中心命題) を参照する。

## 0.1 Architecture Signature Dynamics

Architecture Signature Dynamics と chaos-game 的な進化の理論は
[Part 3: Architecture Dynamics / Chaos Game 編](aat/part3_dynamics_chaos_game.md) を参照する。

## 1. AAT の数学的役割

AAT の役割は、設計判断を経験則としてではなく、feature extension、operation、
invariant、obstruction の関係として記述することである。

基礎語彙は [Part 1](aat/part1_foundations.md) を参照する。

## 1.1 既存分野との差分

AAT は、architecture description、conformance checking、feature-oriented programming、
proof-carrying code を置き換えるものではない。AAT の中心は、機能追加が既存構造を
lawful に拡大しているか、split しないならどの obstruction が妨げているかを扱う
architecture extension theory である。

## 2. 第一級対象: FeatureExtension

`FeatureExtension`、`SplitFeatureExtension`、static split、hidden interaction の基礎は
[Part 1: FeatureExtension](aat/part1_foundations.md#3-featureextension) と
[Part 1: Split Extension](aat/part1_foundations.md#4-split-extension) を参照する。

## 2.1 Static Split Extension

static split は、split extension の static dependency、boundary policy、interface
factorization に関する selected reading である。

詳細は [Part 1](aat/part1_foundations.md#4-split-extension) と
[Part 1: Three-layer Flatness](aat/part1_foundations.md#13-three-layer-flatness) を参照する。

## 3. Architecture Calculus

Architecture Calculus は、operation がどの proof obligation を生成し、どの invariant を
保存し、どの obstruction を移動または減少させるかを扱う。

詳細は [Part 2: Architecture Calculus](aat/part2_advanced_theory.md#2-architecture-calculus)
を参照する。

## 3.1 Operation catalog

operation catalog は [Part 2: Architecture Calculus](aat/part2_advanced_theory.md#2-architecture-calculus)
を参照する。

## 3.2 Calculus laws

calculus laws は [Part 2: Calculus Laws](aat/part2_advanced_theory.md#3-calculus-laws)
を参照する。

## 4. ガロア的対応: operation と invariant

operation family と invariant family の対応は
[Part 2: Operation と Invariant の対応](aat/part2_advanced_theory.md#4-operation-と-invariant-の対応)
を参照する。

## 4.1 Design principle classification

設計原則の分類は [AAT 総合理論](aat/README.md#設計原則) を参照する。

## 5. 三層 flatness

static、runtime、semantic の三層 flatness は
[Part 1: Three-layer Flatness](aat/part1_foundations.md#13-three-layer-flatness) を参照する。

## 6. 形式的境界

形式的境界は、universe、observation、coverage、exactness、non-conclusion を明示することで
保たれる。基礎的な境界は [Part 1](aat/part1_foundations.md#10-proof-obligation) を参照する。

## 7. 中心 theorem 候補

中心 theorem schema は、feature extension、split preservation、non-split witness、
repair、complexity transfer、no-solution certificate、architecture evolution の形で読む。
作業管理上の情報はこの理論入口には置かない。

## 7.1 Split Extension Preservation

split extension preservation は [Part 1: Split Extension](aat/part1_foundations.md#4-split-extension)
と [Part 2: Split Extension as Lifting](aat/part2_advanced_theory.md#11-split-extension-as-lifting)
を参照する。

## 7.2 Non-split Extension Witness

non-split witness は [Part 1: Obstruction Witness](aat/part1_foundations.md#6-obstruction-witness)
を参照する。

## 7.3 Repair as Re-splitting

repair は [Part 2: Repair](aat/part2_advanced_theory.md#5-repair) を参照する。

## 7.4 Complexity Transfer

complexity transfer は [Part 2: Repair](aat/part2_advanced_theory.md#5-repair) と
[Part 2: Architecture Extension Formula](aat/part2_advanced_theory.md#15-architecture-extension-formula)
を参照する。

## 7.5 No-solution Certificate

no-solution certificate は [Part 2: Synthesis と No-solution Certificate](aat/part2_advanced_theory.md#6-synthesis-と-no-solution-certificate)
を参照する。

## 7.6 Architecture Evolution

architecture evolution は [Part 3](aat/part3_dynamics_chaos_game.md) を参照する。

## 8. Homotopy Skeleton and Architecture Paths

homotopy skeleton と architecture paths は
[Part 2: Architecture Paths](aat/part2_advanced_theory.md#7-architecture-paths) と
[Part 2: Homotopy Skeleton](aat/part2_advanced_theory.md#8-homotopy-skeleton) を参照する。

## 8.1 Architecture paths

architecture paths は [Part 2: Architecture Paths](aat/part2_advanced_theory.md#7-architecture-paths)
を参照する。

## 9. Diagram Filling and Split Extension

diagram filling と split extension の関係は
[Part 2: Diagram Filling](aat/part2_advanced_theory.md#10-diagram-filling) と
[Part 2: Split Extension as Lifting](aat/part2_advanced_theory.md#11-split-extension-as-lifting)
を参照する。

## 9.1 Diagram filling and obstruction

diagram filling と obstruction は [Part 2: Diagram Filling](aat/part2_advanced_theory.md#10-diagram-filling)
を参照する。

## 9.2 Split extension as lifting and section

split extension as lifting は
[Part 2: Split Extension as Lifting](aat/part2_advanced_theory.md#11-split-extension-as-lifting)
を参照する。

## 10. Structural Architecture Extension Formula

Architecture Extension Formula は
[Part 2: Architecture Extension Formula](aat/part2_advanced_theory.md#15-architecture-extension-formula)
を参照する。

## 8.4 Structural Architecture Extension Formula

旧参照互換用の見出しである。内容は
[Part 2: Architecture Extension Formula](aat/part2_advanced_theory.md#15-architecture-extension-formula)
を参照する。

## 8.5 Analytic Representation Layer

旧参照互換用の見出しである。内容は
[Part 2: Analytic Representation](aat/part2_advanced_theory.md#16-analytic-representation)
を参照する。

## 11. Analytic Representation and Canonical Example

analytic representation は [Part 2: Analytic Representation](aat/part2_advanced_theory.md#16-analytic-representation)
を参照する。

## 11.1 Analytic representation layer

analytic representation layer は
[Part 2: Analytic Representation](aat/part2_advanced_theory.md#16-analytic-representation)
を参照する。

## 11.2 Representation strength

representation strength は
[Part 2: Analytic Representation](aat/part2_advanced_theory.md#16-analytic-representation)
を参照する。

## 11.3 Canonical example: Coupon feature extension

canonical example は、feature extension、hidden interaction、repair、semantic residual を
説明するための例として読む。理論上の位置づけは
[Part 1](aat/part1_foundations.md) と [Part 2](aat/part2_advanced_theory.md) を参照する。

## 11.4 Non-goals of the homotopy / analytic extension

non-goals は [Part 2: 発展編の境界](aat/part2_advanced_theory.md#18-発展編の境界)
を参照する。

## 12. 型体系

型体系の基礎は [Part 1: ArchitectureCore](aat/part1_foundations.md#2-architecturecore)、
[Part 1: Proof Obligation](aat/part1_foundations.md#10-proof-obligation)、および
[Part 1: Certificate と Claim Boundary](aat/part1_foundations.md#11-certificate-と-claim-boundary)
を参照する。

## 12.1 ArchitectureCore

`ArchitectureCore` は [Part 1: ArchitectureCore](aat/part1_foundations.md#2-architecturecore)
を参照する。

## 12.2 CertifiedArchitecture

`CertifiedArchitecture` は、architecture object と law universe、invariant family、
witness universe、proof obligation discharge を束ねる proof-carrying object として読む。
作業管理上の情報ではなく、理論上の package boundary である。
詳細は [Part 1: Certificate と Claim Boundary](aat/part1_foundations.md#11-certificate-と-claim-boundary)
を参照する。

## 12.3 Proof obligation schema

proof obligation schema は [Part 1: Proof Obligation](aat/part1_foundations.md#10-proof-obligation)
を参照する。

## 12.4 Abstract Obstruction Valuation

obstruction valuation は [Part 2: Obstruction Valuation](aat/part2_advanced_theory.md#17-obstruction-valuation)
を参照する。

## 13. 形式化の分解

この入口文書では形式化の進捗を持たない。理論上の分解は、基礎編、発展編、力学編の
三部構成として読む。

## 13.1 型境界の固定

型境界は [Part 1](aat/part1_foundations.md) を参照する。

## 13.2 Three-layer flatness core

three-layer flatness は [Part 1: Three-layer Flatness](aat/part1_foundations.md#13-three-layer-flatness)
を参照する。

## 13.3 Feature Extension Core

feature extension core は [Part 1: FeatureExtension](aat/part1_foundations.md#3-featureextension)
を参照する。

## 13.4 Architecture Calculus Core

Architecture Calculus core は [Part 2: Architecture Calculus](aat/part2_advanced_theory.md#2-architecture-calculus)
を参照する。

## 13.5 Repair and Synthesis

repair and synthesis は [Part 2](aat/part2_advanced_theory.md#5-repair) を参照する。

## 13.6 Homotopy Skeleton and Extension Formula

homotopy skeleton and extension formula は [Part 2](aat/part2_advanced_theory.md) を参照する。

## 13.7 Representation Bridges

representation は [Part 2: Analytic Representation](aat/part2_advanced_theory.md#16-analytic-representation)
を参照する。

## 13.8 拡張候補

拡張候補は [Part 3](aat/part3_dynamics_chaos_game.md) を参照する。

## 14. 理論上の到達条件

到達条件を作業管理上の情報としてこの入口文書に置かない。AAT の理論上の到達点は、feature
extension、calculus、homotopy、representation、dynamics を同じ語彙で接続できることである。

## 15. 非目標

AAT の第一級理論文書は次を目標としない。

```text
- 実コードから理論対象を完全に抽出できると主張する。
- 具体的な運用 artifact の形式を定義する。
- 作業管理上の情報を記録する。
- empirical correlation を数学 theorem として扱う。
- architecture quality を単一スコアへ潰す。
- 任意の実コード変更の正しさを無条件に保証する。
```
