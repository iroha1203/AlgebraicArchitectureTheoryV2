# AAT: 代数的アーキテクチャ論

このディレクトリは、Algebraic Architecture Theory, AAT の数学理論と
Lean 形式化 status を管理する。

AAT は、ソフトウェアアーキテクチャを bounded な `ArchitectureObject` として切り出し、
その上の操作がどの不変量を保存し、どの obstruction witness を生み、
どの signature axis に現れるかを扱う局所代数である。

```text
software architecture
  = ArchitectureObject
  + ArchitectureOperation
  + InvariantFamily
  + ObstructionWitness
  + ArchitectureSignature
  + theorem boundary / non-conclusions
```

AAT は、他の理論のための補助概念ではなく、ソフトウェアアーキテクチャの数学理論として
独立に成立する。後続理論は AAT を使えるが、AAT 側に逆依存を作らない。

## 読む順序

1. [AAT 数学理論](mathematical_theory.md)
2. [証明義務と実証仮説](proof_obligations.md)
3. [Lean 定義・定理索引](lean_theorem_index.md)

旧 Part 文書と旧互換入口は archive に退避済みである。
AAT の現行本文は [AAT 数学理論](mathematical_theory.md) に一本化する。
力学・場・予測・制御の内容は [SFT](../sft/software_field_theory.md) 側で扱う。

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
TheoremBoundary
NonConclusion
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
どの theorem boundary が満たされているか。
何を結論し、何を結論しないか。
```

## 後続理論との関係

```text
AAT = local / algebraic / theorem-boundary-aware
```

AAT に置くものは、architecture object、operation、invariant、obstruction witness、
signature、theorem boundary、non-conclusion である。

AAT が直接扱わないもの:

```text
PRD force
ForecastCone
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

SFT は AAT に依存する後続理論として、これらを扱う。
対応関係は [AAT / SFT Interface](../sft/aat_interface.md) に置く。

## 証明済み主張の読み方

数学理論本文は、作業状態や Issue 管理状態を混ぜない。
現在 Lean に存在する定義・定理は [Lean 定義・定理索引](lean_theorem_index.md)、
theorem boundary、未解決課題、empirical hypothesis は
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
