# AAT代数幾何版 Lean形式化 PRD-3: 第III部 Law Algebra・Obstruction Ideal・Lawful Locus

対象本文: [第III部 Law Algebra・Obstruction Ideal・Lawful Locus](algebraic_geometric_theory/part_3_law_algebra_obstruction_ideal_lawful_locus.md)

先行PRD:
[PRD-1 第I部](lean_ag_part_1_atoms_objects_laws_prd.md) /
[PRD-2 第II部](lean_ag_part_2_sites_sheaves_prd.md)

## 問い

第II部の局所性の舞台の上で、法則は方程式になるか。すなわち、

```text
O_X^U -> I_L -> I_Ob^U -> Flat_U(X) = V(I_Ob^U)
```

の構成が Lean 上で sorry なしに立ち上がり、

```text
lawfulness
  <-> obstruction ideal vanishing
  <-> factorization through lawful locus
  <-> zero obstruction valuation
  <-> required signature zero
```

の5項同値(定理11.1 Lawfulness-Ideal Correspondence)が、本文の仮定
(soundness / completeness / axis exactness / witness coverage / descent /
restriction compatibility)に相対化されて証明できるか。特に
`omega_U(s) = 0` との一致は、第I部の定理9.3 で形式化した obstruction
valuation との縦の整合性であり、塔が層ごとに別の理論へ分裂していないことの
機械検証である。

採否規律: この構成と、定理11.1・定理5.6C・定理8.3 に寄与する定義・命題だけを
形式化対象に採る。寄与しない要素(例、原則、coordinate の代表例リスト)は
対象外とする。実装中に、5項同値に必要な仮定が本文に不足している、または
第I部・第II部の形式化と接続できないことが見つかった場合、それは本文または
本PRDの欠陥であり、ループを停止して報告する。

## 中心方針

PRD-1 / PRD-2 で確立した方針を引き継ぐ。

- 本文の塔を下から積む。本PRDは第3段であり、第III部のみを対象とする。
- 忠実性契約: 定義・公理・条件は全数形式化(docstring に本文ラベル)、
  定理・命題・補題・系は sorry なしで証明、定理候補は statement のみ、
  例・原則は対象外。
- `Formal/AG` 以下へ実装し、`Formal/Arch` は import しない。
  `axiom` / `admit` / `sorry` / `unsafe` は導入しない。
- Mathlib への二段構えの橋: AAT 語彙の定義が一次、Mathlib 対応物は bridge
  theorem / instance を通じて資産を借りる。
- 台帳は `lean_theorem_index.md` と `proof_obligations.md` に統合する。

本PRDで新たに加わる方針が三つある。

**(1) 可換代数への橋の本格化。** 第III部から Mathlib の可換代数資産を
本格的に使う。

```text
FreeCommAlg_k(Coord)        --bridge-->  MvPolynomial Coord k
J_struct による quotient    --bridge-->  Ideal.Quotient
Spec_AAT(A,D)               --bridge-->  PrimeSpectrum A + decoration 構造体
V(I) / 零点集合             --bridge-->  PrimeSpectrum.zeroLocus
locally ringed reading      --bridge-->  AlgebraicGeometry.LocallyRingedSpace
```

`Spec_AAT(A,D)` は本文どおり「通常の `Spec(A)` に decoration `D` を付加した
もの」として定義し、新しい spectrum 理論を作らない。

**(2) 定理候補の statement-only 規律の初適用。** 第III部には本シリーズ初の
定理候補(7.2A Architecture Nullstellensatz)が現れる。忠実性契約に従い、
statement を Prop としてコンパイルが通る形で形式化し、証明しない。
Mathlib には Hilbert Nullstellensatz が存在するため、この候補は将来の昇格
(Lean 証明 → 本文で定理へ昇格)の最初の現実的な対象だが、昇格は本PRDの
スコープ外であり、別 Issue / PRD として扱う。

**(3) ラベル衝突の台帳規律。** 第III部には第II部と同じ枝番(7.2A / 7.2B /
7.2C)が存在する。Lean 側は部ごとの namespace で区別し、台帳の本文ラベル列は
`III.定理候補7.2A` のように部番号を付けて記載する(第I・II部の既存行も
この機会に部番号付きへ揃えてよい)。第II部と同様、枝番の振り直しが
ループ中に行われた場合は PRD 不変条件により停止し、人間の判断に委ねる。

## 背景

- PRD-1(マージ済み)のループは進行中であり、`Formal/AG/Atom` の最初の
  モジュール群が main に着地し始めている。PRD-2(マージ済み)のループは
  これから始まる。本PRDの実装は両者の成果物(architecture object、
  law universe、obstruction valuation、ArchCtx、J_U、sheaf 条件、AATSh)に
  依存するため、依存先未実装の要求は `blocked` として台帳に記録する(R0)。
  三本のループが並行しうるが、本PRDのループは先行PRDの実装を先取りしない。
- 第III部は第IV部(obstruction cohomology)の係数となる ideal sheaf と、
  第VIII部(measurement theory)の Stanley-Reisner / NSdepth 計測の理論的
  土台を供給する。特に定理5.6C は第VIII部 定理5.2(ArchSig v0.4.0 の
  square-free repair evaluator R4 が参照)の幾何側の根拠であり、
  定義7.2B NSdepth は ArchSig の NSdepth 計測量の定義そのものである。
- 第III部の定理(5.6C、8.3、11.1)には CBI マーカーが付いていないが、
  「定理」である以上、忠実性契約により全数証明対象である。

## アウトカム

本PRDの完了時点で、次が成り立つ。

1. 「法則は方程式である」が Lean 上の構成として存在する: 座標環
   `O_raw^U` / `O_X^U`、law witness ideal `I_L`、obstruction ideal sheaf
   `I_Ob^U`、lawful locus `Flat_U(X) = V(I_Ob^U)`。
2. 定理11.1 の5項同値が、仮定を明示した theorem package として証明され、
   `omega_U` 条項が第I部の定理9.3 の obstruction valuation と同一の定義を
   参照している。
3. 定理5.6C により、square-free regime の obstruction ideal が
   Stanley-Reisner ideal と一致することが証明され、ArchSig の repair
   evaluator が依拠する組合せ的読み(系5.6D)が機械検証されている。
4. 定理8.3 により、affine chart の moduli 読みが表現可能性として
   証明されている。
5. 定理候補7.2A が statement としてコンパイルされ、NSdepth(定義7.2B)と
   その単調性(命題7.2C)が形式化されている。
6. 第III部の本文ラベルと Lean 宣言の対応が両台帳で追跡できる。

## 第III部ラベルの処遇表

ギャップ分析はこの表を基準に行う。

| 本文ラベル | 処遇 | 備考 |
| --- | --- | --- |
| 定義2.1 Law Algebra Sheaf | 定義 | `O_X^U = (O_raw^U)^+`。代数値層は R3 |
| 原則2.2 Commutative Base | 対象外 | 係数環 `k : CommRing` を型パラメータとして設計に反映 |
| 定義3.1 Coordinate | 定義 | context 上の読み関数。型は抽象でよい |
| 例3.2–3.4 | 対象外 | |
| 定義4.1 Free Typed Commutative Algebra | 定義 | Mathlib `MvPolynomial` への橋(R1) |
| 定義4.2 Structural Relation | 定義 | `Rel_struct`(関係多項式族)と `J_struct`(生成 ideal)を本文どおり区別する |
| 定義4.3 Raw Ambient Law Algebra | 定義 | quotient `FreeCommAlg / J_struct` |
| 条件4.4 Restriction-Stable Structural Relations | 定義(仮定)+証明 | 仮定の下で restriction が quotient に降りることを補題にする(R2) |
| 条件4.5 Presentation-Stable AAT Site | 定義(仮定) | 仮定8.4 とともに R10 で使う |
| 原則4.6 Law Does Not Create Coordinates | 対象外 | 設計コメント |
| 定義5.1 Violation Witness Family / 定義5.2 Law Witness Ideal / 定義5.3 Defect Section | 定義 | primary encoding は ideal vanishing(`s^* I_L = 0` / `I_L ⊆ p`)。代表元 δ_L は no-cancellation 下の別読みとして置く |
| 例5.4 / 例5.5 | 対象外 | cycle / substitution ideal は R13 の有限モデルで実装する |
| 原則5.6 No-Cancellation Discipline | 対象外 | 設計コメント。lawfulness の定義を δ = 0 に置かないことで反映 |
| 補題5.6A Idempotent Coordinate Collapse | 証明 | `k[x_v]/(x_v² - x_v)` が `k` の有限直積であること、全 module の flatness(Tor 消滅)、`I/I² = 0`、`Ω_{A/k} = 0`(R5) |
| 定義5.6B Square-Free Witness Regime | 定義 | `E_W`、`Forb_U(W)`、square-free monomial `x_S` |
| 定理5.6C Stanley-Reisner Obstruction Theorem | 証明 | `I_Ob^U(W) = I_{Delta_U(W)}`。minimal でない `Forb` の縮約が同じ radical ideal を与えることを含む(R6) |
| 系5.6D Obstruction Invariants | 証明 | minimal generators ↔ minimal forbidden supports、faces ↔ admissible supports(R6) |
| 例5.6E Three-Witness Chart | 例 theorem | R13 の有限モデルで実装(第V部の monomial conflict 計算の先行例) |
| 原則5.7 Equation Relativity / 原則5.8 Law Condition Types | 対象外 | 5.8 の分類(open / constructible / descent / temporal / stacky)は非主張に記録し、closed equational law のみを ideal 化する |
| 定義6.1 Local Obstruction Ideal | 定義 | selected law witness ideal の和 |
| 定義6.2 Obstruction Ideal Sheaf | 定義+証明 | restriction compatibility `res_i(I_Ob(W)) ⊆ I_Ob(W')` を補題にする。sheaf-image 構成も形式化し、local sum 表示との一致条件を明示する(R7) |
| 原則6.3 | 対象外 | |
| 定義7.1 Lawful Locus / 定義7.2 Lawful Section | 定義 | `V(I_Ob^U)`、`s^* I_Ob^U = 0`、factorization(R8) |
| 定理候補7.2A Architecture Nullstellensatz | statement のみ | Prop としてコンパイルを通す。証明しない。昇格は別 Issue / PRD(R9) |
| 定義7.2B Nullstellensatz Depth | 定義 | unlawfulness certificate の最小表示次数(R9) |
| 命題7.2C Nullstellensatz Depth Monotonicity | 証明 | generator 追加で NSdepth は増えない(R9) |
| 例7.2D Unit Certificate | 例 theorem | `NSdepth = 1` の実例(R13) |
| 原則7.3 Lawful Locus Is Not Total Correctness | 対象外 | AAT-flatness と algebraic flatness の区別を非主張に記録 |
| 定義8.1 Affine AAT Chart | 定義 | `Spec_AAT(A,D) := (Spec A, O_{Spec A}, D)`。Mathlib `PrimeSpectrum` への橋(R10) |
| 定義8.2 R-Valued Local Configuration Functor | 定義 | `h_W^U : CommAlg_k -> Set`(R10) |
| 定理8.3 Raw Affine Chart Representability | 証明 | `h_W^U(R) ≅ Hom_{k-Alg}(O_raw^U(W), R)`。presentation の普遍性から(R10) |
| 仮定8.4 Sheafified Chart Presentation | 定義(仮定) | raw と sheafified の表現可能性を分けて読む |
| 定義8.5 Local Lawful Chart | 定義 | `V(I_Ob^U(W)) ⊆ Spec_AAT` |
| 例8.6 Boundary Chart | 対象外 | |
| 定義9.1 Ringed AAT Topos | 定義 | `(AATSh(A,U,J), O_X^U)`(R11) |
| 定義9.2 Chart Compatibility | 定義 | 7条件(open immersion / overlap representability / restriction / ideal / decoration / cocycle / locally ringed)の述語(R11) |
| 定義9.3 Architecture Scheme | 定義 | decorated locally ringed geometry。forgetful reading が Mathlib `LocallyRingedSpace` を与える橋を含む(R11) |
| 原則9.4 Scheme Relativity | 対象外 | 型パラメータとして反映 |
| 定義10.1 Ring Restriction / 定義10.2 Ideal Restriction | 定義+証明 | R2 / R7 の restriction 補題で実現 |
| 定義10.3 Scheme Gluing | 定義 | gluing data と、affine へ戻るための追加条件(glued affine / comparison iso / section 同定 / decoration 同定)を仮定として明示する。underlying 側は Mathlib の gluing 資産への橋に限定(R11) |
| 原則10.4 Local Lawful Sections Need Not Glue | 対象外 | 非主張に記録(第IV部への入口) |
| 定理11.1 Lawfulness-Ideal Correspondence | 証明 | 5項同値。仮定7点を theorem 引数として明示(R12) |
| 原則11.2 Exactness Is Assumption | 対象外 | 仮定の明示で反映 |

## 要求

### R0. 前提の確認と Formal/AG/LawAlgebra の立ち上げ

- 本PRDの実装は PRD-1(`Formal/AG/Atom`: law universe、obstruction valuation
  `omega_U`、有限モデル)と PRD-2(`Formal/AG/Site`: ArchCtx、J_U、sheaf
  条件、AATSh、有限 poset regime)の成果物に依存する。着手時に依存宣言の
  存在を確認し、未実装の場合はその要求を `blocked` として tracking Issue に
  記録する。先行PRDの実装を本PRDのループで先取りしない。
- 第III部のモジュールを `Formal/AG/LawAlgebra/` 以下に実装する。ファイル
  分割は本文の節構成に概ね対応させる(例: `Coordinate.lean`,
  `AmbientAlgebra.lean`, `StructureSheaf.lean`, `WitnessIdeal.lean`,
  `IdempotentCollapse.lean`, `StanleyReisner.lean`, `ObstructionIdeal.lean`,
  `LawfulLocus.lean`, `Nullstellensatz.lean`, `AffineChart.lean`,
  `Scheme.lean`, `Correspondence.lean`)。
- ルート import に追加し、CI の `lake build` 対象に含める。
- 完了条件: 空でない最初のモジュールが CI でビルドされ merge されている。

### R1. Coordinate と Free Typed Commutative Algebra(定義3.1、4.1)

- architecture coordinate を、context `W` 上の局所データから係数環 `R` への
  読み関数として定義する。coordinate の名前空間(atom / signature / state /
  effect / authority / semantic / runtime / boundary)は型レベルの label と
  して持たせてよい。
- `Coord_X(W)` を coordinate の集合(型)として定義し、
  `FreeCommAlg_k(Coord_X(W))` を Mathlib `MvPolynomial (Coord_X W) k` への
  橋として定義する。
- 完了条件: 定義と橋が sorry なしで存在する。

### R2. Raw Ambient Law Algebra と restriction-stability(定義4.2、4.3、条件4.4)

- structural relation の族 `Rel_struct(W)` と、それが生成する ideal
  `J_struct(W)` を本文どおり区別して定義する。
- raw ambient law algebra `O_raw^U(W) = FreeCommAlg_k(Coord_X(W)) / J_struct(W)`
  を定義する。law witness ideal をこの段階で quotient しないこと(本文
  「law equations are not all quotiented out at the ambient stage」)を
  設計コメントに記す。
- 条件4.4 restriction-stability(`res_i(J_struct(W)) ⊆ J_struct(W')`)を
  仮定として定義し、その下で typed coordinate restriction が quotient に
  降りて `O_raw^U(W) -> O_raw^U(W')` を与えることを補題として証明する。
  これにより `O_raw^U` が presheaf of commutative `k`-algebras になることを
  示す(定義10.1 Ring Restriction はこの補題で実現される)。
- 完了条件: 定義と quotient 降下補題が sorry なしで存在する。

### R3. 代数値層と Law Algebra Sheaf(定義2.1、条件4.5)

- PRD-2 の sheaf 条件(Type 値)を可換 `k`-代数値の presheaf へ拡張する。
  sheafification `O_X^U = (O_raw^U)^+` は Mathlib の sheafification 資産
  (代数値 presheaf に対する plus construction / `HasSheafify`)への橋で
  構成し、一般論を新規開発しない。
- 条件4.5 presentation-stability(sheafification が selected presentation を
  保つ)を仮定として定義する(検証は R10 の仮定8.4 で使う)。
- 有限 poset regime(PRD-2 定義7.2B)では sheafification が具体的に計算
  できることを利用してよい。
- 完了条件: `O_X^U` の定義と橋が sorry なしで存在する。

### R4. Law Witness Ideal と Defect Section(定義5.1–5.3)

- violation witness family `Viol_L(W)` と、対応する coordinate `x_v` を
  定義する。
- law witness ideal `I_L(W) = < x_v | v in Viol_L(W) >` を定義する。
- defect の primary encoding を ideal vanishing に置く: 点に沿った成立
  `I_L(W) ⊆ p` と section に沿った成立 `s^* I_L = 0` を定義する。
  代表元 `δ_L` による読み(`s^*(δ_L) = 0`)は、no-cancellation 条件を
  仮定として明示した別定義として置き、primary encoding と混同しない。
- 完了条件: 定義が sorry なしで存在する。

### R5. 補題5.6A Idempotent Coordinate Collapse

- 有限集合 `E` と体 `k` に対し `A = k[x_v | v in E] / < x_v² - x_v >` を
  定義し、次を証明する。
  (a) `A` は `k` の有限直積と同型である。
  (b) すべての `A`-module は flat であり、したがって
      `Tor_i^A(M,N) = 0`(`i > 0`)。Tor の表現は Mathlib の API を使う。
  (c) 任意の ideal `I ⊆ A` について `I/I² = 0`。
  (d) `Ω_{A/k} = 0`(Mathlib `KaehlerDifferential` への橋)。
- この補題は「Boolean 化した座標環では derived 情報が消える」ことの機械
  検証であり、定義5.6B が deformation 側を `k[E_W]` に保つ理由を与える。
  この設計意図を docstring に記す。
- 完了条件: (a)–(d) が sorry なしで証明されている。

### R6. Square-Free Regime と定理5.6C・系5.6D(定義5.6B、定理5.6C、系5.6D)

- square-free witness regime(`E_W`、`Forb_U(W) ⊆ FinSubsets(E_W)`、
  `x_S = ∏_{e in S} e`、`I_Ob^U(W) = < x_S | S in Forb_U(W) > ⊆ k[E_W]`)を
  定義する。
- 抽象単体複体を `Finset` ベースで定義し(下方閉な `Finset E_W` の族)、
  `Delta_U(W) = { T | no S in Forb_U(W), S ⊆ T }` と Stanley-Reisner ideal
  `I_Δ` を定義する。
- 定理5.6C を証明する: `Forb_U(W)` が inclusion-minimal なら
  `I_Ob^U(W) = I_{Delta_U(W)}`。minimal でない場合も inclusion-minimal への
  縮約が同じ radical ideal を与えることを証明する。
- 系5.6D を証明する: `I_{Delta_U(W)}` の minimal monomial generators が
  minimal forbidden supports と一対一対応すること、`Delta_U(W)` の face が
  「forbidden support を含まない witness support」と一致すること。
- `Flat_U(W) = V(I_Δ)` の coordinate subspace arrangement としての読みを
  定義する(主張は zeroLocus との一致まで)。
- 完了条件: 定理5.6C と系5.6D が sorry なしで証明され、
  `proof_obligations.md` で `proved` に昇格している。

### R7. Obstruction Ideal Sheaf(定義6.1、6.2)

- local obstruction ideal `I_Ob^U(W) = Σ_{L in U selected on W} I_L(W)` を
  定義する。
- restriction compatibility `res_i(I_Ob^U(W)) ⊆ I_Ob^U(W')` を、R2 の
  restriction-stability と witness family の整合性仮定から補題として
  証明する(定義10.2 Ideal Restriction はこの補題で実現される)。
- sheaf-image 構成(`⊕_L I_L -> O_X^U` の sheaf image)を形式化し、
  local sum 表示と一致する範囲を明示する。
- 完了条件: 定義と restriction 補題が sorry なしで存在する。

### R8. Lawful Locus と Lawful Section(定義7.1、7.2)

- lawful locus `Flat_U(X) = V(I_Ob^U)` を定義する(affine chart 上では
  Mathlib `PrimeSpectrum.zeroLocus` への橋、大域では section-wise の
  vanishing)。
- lawful section: `Lawful_U(s) iff s^* I_Ob^U = 0` と、`s` が `Flat_U(X)` を
  factor through することの同値を証明する(定理11.1 の部分同値として
  切り出してよい)。
- 完了条件: 定義と factorization 同値が sorry なしで存在する。

### R9. Nullstellensatz 枠(定理候補7.2A、定義7.2B、命題7.2C)

- 定理候補7.2A を statement として形式化する: `k` algebraically closed、
  Boolean ideal `B_W = < e² - e | e in E_bool >` の下で、
  `V(I_U(W) + B_W)(k) = ∅ iff 1 ∈ radical(I_U(W) + B_W)`、radical の場合の
  membership 簡約、unlawfulness certificate の定義を含む Prop 群として
  コンパイルを通す。証明はしない。
- NSdepth(定義7.2B)を定義する: chosen generators `F_U(W)` に対する
  `1 = Σ a_f f` の表示次数の最小値。
- 命題7.2C を証明する: `U ⊆ U'`、`I_U ⊆ I_{U'}`、generators の追加で
  `F_{U'}` が得られ、両方の lawful point set が空なら
  `NSdepth_{U'}(W) <= NSdepth_U(W)`。
- 定理候補7.2A の昇格(Mathlib の Nullstellensatz を使った証明)は本PRDの
  スコープ外であり、台帳に future proof obligation として登録する。
- 完了条件: statement 群がコンパイルされ、命題7.2C が sorry なしで証明
  されている。

### R10. Affine Chart と表現可能性(定義8.1、8.2、8.5、定理8.3、仮定8.4)

- `Spec_AAT(A,D) := (Spec A, O_{Spec A}, D)` を、Mathlib `PrimeSpectrum` と
  decoration 構造体(typed coordinate label、selected law reading、
  signature axis reading、obstruction ideal、interpretation map)の組と
  して定義する。
- `R`-valued local configuration functor `h_W^U` を定義する: typed
  coordinate への `R`-値割り当てのうち structural relations を満たすもの。
- 定理8.3 を証明する: 有限表示の coordinate / structural relation family と
  restriction の保存仮定の下、`h_W^U(R) ≅ Hom_{k-Alg}(O_raw^U(W), R)`。
  証明は `MvPolynomial` の評価の普遍性と `Ideal.Quotient.lift` による。
- 仮定8.4(sheafified chart presentation)を仮定として定義し、その下での
  sheafified 表現可能性を系として証明する。
- local lawful chart(定義8.5)`Flat_U(W) = V(I_Ob^U(W)) ⊆ Spec_AAT` を
  定義する。
- 完了条件: 定理8.3 が sorry なしで証明され、`proof_obligations.md` で
  `proved` に昇格している。

### R11. Ringed Topos・Architecture Scheme・Gluing(定義9.1–9.3、10.3)

- ringed AAT topos `T_X^U = (AATSh(A,U,J), O_X^U)` を定義する。
- chart compatibility(定義9.2)の7条件を述語として定義する。
- architecture scheme(定義9.3)を、chart-compatible chart atlas を持つ
  decorated locally ringed geometry として定義し、forgetful reading が
  Mathlib `LocallyRingedSpace` を与えることを橋として証明する。
- scheme gluing(定義10.3)は、gluing data の定義と、affine chart へ戻る
  ための追加条件(glued affine / canonical comparison iso /
  `O_X^U(W) = Γ(X_glue)` / decoration 同定)の仮定としての明示までを行う。
  underlying scheme 側の貼り合わせの存在は Mathlib の gluing 資産への橋に
  限定し、decorated gluing の一般論を新規開発しない。glued object が
  `Spec_AAT(O_X^U(W), D_W^U)` と一致するとは主張しない。
- 完了条件: 定義・述語・橋が sorry なしで存在する。

### R12. 定理11.1 Lawfulness-Ideal Correspondence

- 仮定を theorem 引数として明示する: obstruction soundness /
  obstruction completeness / axis exactness / witness coverage /
  U-adequate cover(cover を使う場合)/ sheaf descent for `Ob_U` /
  ring restriction compatibility。
- 5項同値を証明する:
  `Lawful_U(s)` ↔ `s^* I_Ob^U = 0` ↔ `s` factors through `Flat_U(X)` ↔
  `omega_U(s) = 0` ↔ required `Sig_U` axes vanish。
- `omega_U` 条項は第I部(PRD-1)の obstruction valuation・zero-reflecting
  aggregation の定義を import して使い、新しい valuation を定義しない。
  signature 条項は第I部の `RequiredSignatureAxesZero` を使う。これにより
  定理9.3(第I部)との縦の整合性が theorem の型レベルで保証される。
- 同値の各辺を独立の補題として切り出し、theorem package として束ねる
  (第VIII部 / ArchSig の verdict discipline が個別の辺を参照できる形)。
- 完了条件: 定理11.1 が sorry なしで証明され、`proof_obligations.md` で
  `proved` に昇格している。

### R13. 有限モデルの拡張

- PRD-1 / PRD-2 の有限モデル(`Formal/AG/Examples/`)を第III部の水準へ
  拡張する。
  (a) 例5.6E: `E_W = {x,y,z}`、`Forb = {{x,y}}` の Stanley-Reisner chart を
      実装し、`I_Ob = <xy>`、`Delta_U(W)` の faces を example theorem として
      検証する(第V部の monomial conflict 計算の先行例)。
  (b) 例7.2D: `I = <x>`、`B = <x-1>`、`1 = x - (x-1)`、`NSdepth = 1` を
      example theorem として検証する。
  (c) cycle law の witness ideal(例5.5 の `I_cycle`)を有限モデル上に
      実装し、lawful locus の点の有無と定理11.1 の同値の成立を example
      theorem として検証する。
- 完了条件: (a)–(c) が sorry なしで存在する。

### R14. 台帳整備

- `lean_theorem_index.md` の AG 節に第III部の宣言を追加する(本文ラベル列は
  `III.` 付き)。第I・II部の既存行も部番号付きへ揃える場合は同一 PR で
  行ってよい。
- `proof_obligations.md` に第III部の証明対象ラベル(補題5.6A、定理5.6C、
  系5.6D、命題7.2C、定理8.3、定理11.1、example theorem 群)を登録し、
  進行に応じて status を更新する。定理候補7.2A は future proof obligation
  として登録する(昇格は別作業)。
- 完了条件: 両台帳が最終実装と一致している。

## 非主張(claim boundary)

- 本PRDは第IV部以降の内容(obstruction cohomology、descent obstruction、
  derived 構成、measurement)を形式化しない。原則10.4(local lawful
  sections need not glue)の cohomological reading は第IV部の仕事である。
- 原則5.8 の law condition types のうち、closed equational law のみを
  ideal として形式化する。open / constructible / descent / temporal /
  stacky law の形式化は行わず、`I_Ob^U` がすべての law を表すとは
  主張しない。
- 定理11.1 は選ばれた law universe、witness family、signature axes、
  coverage、descent、exactness に相対化された同値であり(原則11.2)、
  無条件の全称主張ではない。soundness / completeness を欠く場合の同値は
  主張しない。
- `Flat_U(X)` の flatness は AAT-flatness(lawful locus の factorization)で
  あり、代数幾何の morphism flatness ではない(原則7.3)。Lean の命名でも
  両者を区別する。
- 定理候補7.2A は statement のみであり、本PRDの完了は Nullstellensatz の
  証明を含まない。
- scheme gluing について、glued object が単一 affine chart の `Spec_AAT` と
  一致することを主張しない(追加条件は仮定として明示する)。
- 係数環 `k` の選択に依存する読み(cancellation、rank、dimension)について、
  特定の `k` を超えた主張をしない。

## 完了条件(Acceptance Criteria)

- [ ] AC1. `Formal/AG/LawAlgebra` が新設され、CI の `lake build` でビルド
      される。先行PRD依存の blocked 判定が tracking Issue で運用されている(R0)
- [ ] AC2. 定義3.1 / 4.1 が形式化され、`MvPolynomial` への橋が存在する(R1)
- [ ] AC3. 定義4.2 / 4.3 と条件4.4 が形式化され、restriction の quotient
      降下補題(presheaf 性)が証明されている(R2)
- [ ] AC4. 代数値層への拡張と `O_X^U = (O_raw^U)^+` が橋経由で構成され、
      条件4.5 が仮定として定義されている(R3)
- [ ] AC5. 定義5.1–5.3 が形式化され、ideal vanishing が primary encoding に
      なっている(R4)
- [ ] AC6. 補題5.6A((a)有限直積 (b)Tor 消滅 (c)I/I²=0 (d)Ω=0)が sorry
      なしで証明されている(R5)
- [ ] AC7. 定義5.6B と抽象単体複体・Stanley-Reisner ideal が形式化されて
      いる(R6)
- [ ] AC8. 定理5.6C(minimal 縮約条項を含む)が sorry なしで証明されている(R6)
- [ ] AC9. 系5.6D が sorry なしで証明されている(R6)
- [ ] AC10. 定義6.1 / 6.2 が形式化され、ideal restriction 補題と sheaf-image
      構成が存在する(R7)
- [ ] AC11. 定義7.1 / 7.2 が形式化され、factorization 同値が証明されている(R8)
- [ ] AC12. 定理候補7.2A が statement としてコンパイルされ、証明されて
      いない(sorry でなく Prop 定義として)ことが確認できる(R9)
- [ ] AC13. 定義7.2B NSdepth が形式化され、命題7.2C が sorry なしで証明
      されている(R9)
- [ ] AC14. `Spec_AAT` decoration 構造体と `h_W^U` が形式化されている(R10)
- [ ] AC15. 定理8.3 が sorry なしで証明され、仮定8.4 下の sheafified 版が
      系として存在する(R10)
- [ ] AC16. 定義9.1–9.3 が形式化され、forgetful reading の
      `LocallyRingedSpace` 橋が証明されている(R11)
- [ ] AC17. 定義10.3 の gluing data と affine 復帰条件が仮定として明示
      されている(R11)
- [ ] AC18. 定理11.1 の5項同値が、仮定7点を明示した theorem package として
      sorry なしで証明され、`omega_U` / signature 条項が第I部の定義を
      参照している(R12)
- [ ] AC19. 有限モデル拡張(例5.6E / 例7.2D / cycle ideal と定理11.1 実例)が
      example theorem として検証されている(R13)
- [ ] AC20. `Formal/AG` 全体に `axiom` / `admit` / `sorry` / `unsafe` が
      存在しない
- [ ] AC21. `lean_theorem_index.md` の AG 節が第III部の宣言を `III.` 付き
      本文ラベルで含み、最終実装と一致している(R14)
- [ ] AC22. `proof_obligations.md` に第III部の証明対象ラベルが登録され、
      証明済み分が `proved`、定理候補7.2A が future proof obligation に
      なっている(R14)

## 実行順序の指針

prd-loop のギャップ分析で対象を選ぶ際は、次の依存順を推奨する。

```text
R0 -> R1 -> R2 -> (R3, R4 は並行可) -> (R5, R6 は並行可)
   -> R7 -> R8 -> (R9, R10 は並行可) -> R11 -> R12 -> R13 -> R14
```

R14(台帳)は各周回で増分更新してよい。R5(補題5.6A)と R6(定理5.6C)は
`k[E_W]` の単項式計算のみに依存し、層構成(R3)を待たずに着手できる。
R12(定理11.1)は R7 / R8 と PRD-1 の定理9.3 系列の merge が前提である。
R11 は本PRD最重量の橋であり、ループが stall した場合は定義9.2 / 9.3 の
述語化と forgetful 橋(gluing を除く)までを先に閉じる分割を許す。
