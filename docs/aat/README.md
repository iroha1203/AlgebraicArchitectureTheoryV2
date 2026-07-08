# AAT: 代数的アーキテクチャ論

このディレクトリは、Algebraic Architecture Theory, AAT の数学本文、
Lean 形式化 status、証明義務を管理する。

AAT は、primitive architectural fact を Atom として公理化したうえで、
固定された vocabulary、law universe、coverage topology、係数環 / 係数 sheaf に相対化された
architecture geometry を構成する純粋な代数幾何理論である。

```text
AAT
  = Atom vocabulary
  + Atom axiom system
  + Atom family / configuration
  + Architecture object
  + Law universe
  + Coverage topology
  + Coefficient sheaf
  + AAT site
  + Sheaves
  + Law algebra
  + Obstruction ideal sheaf
  + Lawful locus
  + Architecture scheme
  + Čech descent
  + Derived law geometry
```

AAT は、他の理論のための補助概念ではなく、ソフトウェアアーキテクチャの
数学理論として独立に成立する。後続理論は AAT を使えるが、AAT 側に
逆依存を作らない。

## 読む順序

1. [代数幾何的 AAT 数学本文](algebraic_geometric_theory/README.md)
   - AAT 数学本文の正典。
   - AAT を site、ringed topos、affine chart、scheme、derived / stacky geometry として読む。
   - 標準代数幾何への埋め込み方と claim status は [付録](algebraic_geometric_theory/appendix.md) にまとめる。
   - Lean 形式化との対応があるものは、証明義務と Lean 索引で確認する。
   - Lean 形式化は部単位の PRD で進める。第I部は
     [Lean形式化 PRD-1](lean_ag_part_1_atoms_objects_laws_prd.md)、第II部は
     [Lean形式化 PRD-2](lean_ag_part_2_sites_sheaves_prd.md)、第III部は
     [Lean形式化 PRD-3](lean_ag_part_3_law_algebra_lawful_locus_prd.md)、第IV部は
     [Lean形式化 PRD-4](lean_ag_part_4_obstruction_cohomology_prd.md)、第V部は
     [Lean形式化 PRD-5](lean_ag_part_5_derived_law_geometry_repair_prd.md)。
2. [証明義務と実証仮説](proof_obligations.md)
   - 古典 AAT、代数幾何 AAT、研究ループの分割台帳への入口。
3. [Lean 定義・定理索引](lean_theorem_index.md)
   - 古典 AAT、代数幾何 AAT、研究ループの分割索引への入口。
4. [AAT / Lean 編集ガイドライン](guideline.md)
5. [Lean 品質基準](lean_quality_standard.md)
   - mathlib 型 statement review 基準と target statement 固定手続きの正本。

現行の AAT 数学本文の正典は `algebraic_geometric_theory/` に置く。
代数幾何版へ移行する前の先行ノートは `docs/archive` に退避した。
力学・場・予測・制御の内容は [SFT](../sft/software_field_theory.md) 側で扱う。

## AAT の中心対象

```text
Atom vocabulary
Atom axiom system
Atom family
Atom configuration
Architecture object
Law universe
Coverage topology
AAT site
Sheaf / coefficient sheaf
Ringed AAT topos
Law algebra
Obstruction ideal sheaf
Lawful locus
Affine AAT chart
Architecture scheme
Čech obstruction cohomology
Derived law geometry
Singularity / monodromy / stack
Representation / period / analytic reading
Measurement profile
Evolution geometry
```

## AAT の問い

```text
どの Atom vocabulary と Atom axiom system を固定しているか。
どの Atom family / configuration が architecture object を生成するか。
どの law universe / coverage topology / coefficient を固定しているか。
Atom から生成された architecture object の上に、どの AAT site と sheaf が立ち上がるか。
law algebra はどの零点条件を切り出すか。
obstruction ideal sheaf はどの law failure を表すか。
lawful locus はどの局所条件として定義されるか。
局所 lawful section は Čech descent によって大域化できるか。
derived law geometry はどの repair residue / Tor conflict を露出するか。
measurement profile はどの有限 regime で不変量を計算可能にするか。
```

## 証明済み主張の読み方

数学本文は、作業状態や Issue 管理状態を混ぜない。
現在 Lean に存在する定義・定理は [Lean 定義・定理索引](lean_theorem_index.md)、
未解決課題と empirical hypothesis は
[証明義務と実証仮説](proof_obligations.md) を入口に管理する。詳細行は、古典 AAT、
代数幾何 AAT、研究ループの分割台帳 / 分割索引へ置く。

`proved`, `defined only`, `future proof obligation`, `empirical hypothesis`
を混同しない。特に、tooling output、source-observation output、未測定軸、
empirical correlation は、それだけで Lean theorem にはならない。

## ArchMap / ArchSig との責務境界

AAT は代数幾何的数学本文を source of truth とする。
ArchMap がどの source artifact をどう観測し、どの evidence を記録するかは AAT の内部 claim ではない。

ウィトゲンシュタイン的責務境界では、ArchSig は与えられた
`ArchMap + LawPolicy + evidence contract` から語れることだけを語り、
語れないことには沈黙する。selected universe の妥当性は
ArchMap author と LawPolicy author の責務であり、AAT / Lean はその選ばれた範囲内で
成立する theorem boundary / measurement boundary を与える。

## 非目標

AAT は次を主張しない。

```text
- 実コードから完全な ComponentUniverse を抽出できる。
- static flatness から runtime / semantic flatness が自動的に従う。
- architecture quality を単一スコアへ潰せる。
- measurement が 0 なら未測定軸も安全である。
- SOLID や Layered などの設計語彙が AAT primitive である。
- empirical cost correlation が Lean theorem である。
```
