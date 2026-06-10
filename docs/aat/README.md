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
   - [第IV部 距離・測度・アーキテクチャ幾何](mathematical_theory/part_4_distance_measure_geometry.md)
2. [代数幾何的 AAT 拡張本文](algebraic_geometric_theory/README.md)
   - AAT を site、ringed topos、affine chart、scheme、derived / stacky geometry として読む拡張本文。
   - Lean 形式化との対応は、証明義務と Lean 索引で確認する。
3. [証明義務と実証仮説](proof_obligations.md)
4. [Lean 定義・定理索引](lean_theorem_index.md)
5. [AAT / Lean 編集ガイドライン](guideline.md)

Atom 起点の現行数学本文は `mathematical_theory/` に置く。
代数幾何的拡張本文は `algebraic_geometric_theory/` に置く。
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
DistanceBundle
BoundedDiagnosticConclusion
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
どの距離が architecture movement、repair cost、safe margin、filling cost を測るか。
```

## 証明済み主張の読み方

数学本文は、作業状態や Issue 管理状態を混ぜない。
現在 Lean に存在する定義・定理は [Lean 定義・定理索引](lean_theorem_index.md)、
未解決課題と empirical hypothesis は
[証明義務と実証仮説](proof_obligations.md) で管理する。

`proved`, `defined only`, `future proof obligation`, `empirical hypothesis`
を混同しない。特に、tooling output、source-observation output、未測定軸、
empirical correlation は、それだけで Lean theorem にはならない。

## ArchMap / ArchSig との責務境界

AAT は Atom を公理的出発点とする純粋数学理論である。
ArchMap がどの source artifact をどう観測し、どの Atom / molecule / evidence を記録するかは
AAT の内部 claim ではない。

ウィトゲンシュタイン的責務境界では、ArchSig は与えられた
`ArchMap + LawPolicy + evidence contract` から語れることだけを語り、
語れないことには沈黙する。selected universe の妥当性は
ArchMap author と LawPolicy author の責務であり、AAT / Lean はその選ばれた範囲内で
成立する theorem boundary を与える。

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
