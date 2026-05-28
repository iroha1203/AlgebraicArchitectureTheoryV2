# AAT: 代数的アーキテクチャ論

このディレクトリは、Algebraic Architecture Theory, AAT の数学本文、
Lean 形式化 status、証明義務を管理する。

AAT は、primitive architectural fact を Atom として置き、その合成から
configuration、architecture object、law、obstruction、flatness、operation、
path / homotopy、analytic representation を構成する純粋な代数理論である。

```text
software architecture
  = Atom
  + AtomFamily
  + Configuration
  + ArchitectureObject
  + InvariantFamily
  + Law
  + ObstructionCircuit
  + ArchitectureOperation
  + ArchitectureSignature
```

AAT は、他の理論のための補助概念ではなく、ソフトウェアアーキテクチャの
数学理論として独立に成立する。後続理論は AAT を使えるが、AAT 側に
逆依存を作らない。

## 読む順序

1. [AAT 数学理論](mathematical_theory/README.md)
   - [第I部 Atom・対象・法則](mathematical_theory/part_1_atoms_objects_laws.md)
   - [第II部 平坦性・計算・幾何](mathematical_theory/part_2_flatness_calculus_geometry.md)
   - [第III部 解析表現・状態遷移代数・例](mathematical_theory/part_3_analytic_state_examples.md)
2. [証明義務と実証仮説](proof_obligations.md)
3. [Lean 定義・定理索引](lean_theorem_index.md)

Atom 起点の現行数学本文は `mathematical_theory/` に置く。
ArchitectureObject 中心に整理された旧本文は `docs/archive` に退避した。
力学・場・予測・制御の内容は [SFT](../sft/software_field_theory.md) 側で扱う。

## AAT の中心対象

```text
AtomKind
AtomPredicate
AtomAxiomSystem
AtomFamily
AtomConfiguration
ArchitectureObject
InvariantFamily
LawUniverse
ObstructionCircuit
ArchitectureSignature
ArchitectureOperation
FeatureExtension
RepairStep
Projection
Observation
DiagramFiller
PathHomotopy
AnalyticRepresentation
```

## AAT の問い

```text
どの Atom が architecture object を生成するか。
どの law が選ばれた invariant を保存するか。
どの obstruction circuit が law failure を witness するか。
どの flatness condition が obstruction zero と同値になるか。
どの operation が保存、修復、合成、拡張として読めるか。
どの path / homotopy が同じ architecture transformation を表すか。
どの analytic representation が lawfulness を計算可能にするか。
```

## 証明済み主張の読み方

数学本文は、作業状態や Issue 管理状態を混ぜない。
現在 Lean に存在する定義・定理は [Lean 定義・定理索引](lean_theorem_index.md)、
未解決課題と empirical hypothesis は
[証明義務と実証仮説](proof_obligations.md) で管理する。

`proved`, `defined only`, `future proof obligation`, `empirical hypothesis`
を混同しない。特に、tooling output、extractor output、未測定軸、
empirical correlation は、それだけで Lean theorem にはならない。

## 非目標

AAT は次を主張しない。

```text
- 実コードから完全な ComponentUniverse を抽出できる。
- static flatness から runtime / semantic flatness が自動的に従う。
- architecture quality を単一スコアへ潰せる。
- measurement が 0 なら未測定軸も安全である。
- 設計原則の自然言語的意味をすべて形式化済みである。
- empirical cost correlation が Lean theorem である。
```
