# AAT: 代数的アーキテクチャ論

このディレクトリは、Algebraic Architecture Theory, AAT の数学理論と
Lean 形式化 status を管理する。

AAT は、ソフトウェア変更を次の対象として扱う局所代数である。

```text
software architecture change
  = extension
  + operation
  + invariant
  + obstruction witness
  + proof obligation
  + certificate
```

AAT の役割は、要求、組織、AI、運用の力学を直接説明することではない。
それらが生成する変更を、どの universe、どの observation、どの coverage、
どの exactness assumption に相対化して、何を結論でき、何を結論しないかを
明確にすることである。

## 読む順序

1. [AAT 数学理論](mathematical_theory.md)
2. [証明義務と実証仮説](proof_obligations.md)
3. [Lean 定義・定理索引](lean_theorem_index.md)

互換入口:

- [旧 Part 1: AAT 基礎編](part1_foundations.md)
- [旧 Part 2: AAT 発展編](part2_advanced_theory.md)
- [旧 Part 3: Architecture Dynamics / Chaos Game 編](part3_dynamics_chaos_game.md)

旧 Part 文書の本文は
[`docs/archive/2026-05-09-aat-sft-reorg/`](../archive/2026-05-09-aat-sft-reorg/)
に退避した。新しい本文では、AAT と SFT の境界を明確にするため、
旧 Part 3 の力学・場・予測・制御の内容は [SFT](../sft/README.md) へ移した。

## AAT の中心対象

```text
ArchitectureObject
ComponentUniverse
ComponentCategory
FeatureExtension
StaticSplitFeatureExtension
SplitExtensionLiftingData
ArchitectureOperation
Invariant
LawUniverse
ObstructionWitness
ArchitectureSignature
ProofObligation
Certificate
RepairStep
Projection
Observation
DiagramFiller
PathHomotopy
AnalyticRepresentation
```

## AAT の問い

```text
この feature extension は split するか。
どの invariant が保存されるか。
どの obstruction witness が存在するか。
どの repair が selected obstruction を減らすか。
どの theorem precondition が満たされているか。
何を結論し、何を結論しないか。
```

## SFT との境界

```text
AAT = local / algebraic / formal / certifiable
SFT = global / dynamical / predictive / controllable
```

AAT に置くもの:

```text
FeatureExtension
SplitFeatureExtension
Invariant
ObstructionWitness
LawUniverse
Signature
ProofObligation
Certificate
RepairStep
DiagramFiller
PathHomotopy
Zero-count bridge
Lawfulness theorem
Theorem precondition
Non-conclusion
```

SFT に置くもの:

```text
PRD force
Forecast cone
Requirement pressure
Spec force shaping
Issue decomposition
Operation distribution
Attractor / basin
Dissipation
Organization field
AI generation pressure
Lifecycle trajectory
End-of-life dynamics
Empirical prediction
Control policy
```

## 証明済み主張の読み方

数学理論本文は、作業状態や Issue 管理状態を混ぜない。
現在 Lean に存在する定義・定理は [Lean 定義・定理索引](lean_theorem_index.md)、
未解決 proof obligation と empirical hypothesis は
[証明義務と実証仮説](proof_obligations.md) で管理する。

`proved`, `defined only`, `future proof obligation`, `empirical hypothesis`
を混同しない。特に、tooling output、extractor output、未測定軸、
empirical correlation は、それだけで Lean theorem にはならない。

## 非目標

AAT は次を主張しない。

```text
- 実コードから完全な ComponentUniverse を抽出できる。
- static split から runtime / semantic flatness が自動的に従う。
- architecture quality を単一スコアへ潰せる。
- measurement が 0 なら未測定軸も安全である。
- 設計原則の自然言語的意味をすべて形式化済みである。
- empirical cost correlation が Lean theorem である。
```
