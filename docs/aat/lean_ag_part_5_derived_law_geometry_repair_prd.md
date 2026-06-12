# AAT代数幾何版 Lean形式化 PRD-5: 第V部 Derived Law Geometry と Repair

対象本文: [第V部 Derived Law Geometry と Repair](algebraic_geometric_theory/part_5_derived_law_geometry_repair.md)

先行PRD:
[PRD-1 第I部](lean_ag_part_1_atoms_objects_laws_prd.md) /
[PRD-2 第II部](lean_ag_part_2_sites_sheaves_prd.md) /
[PRD-3 第III部](lean_ag_part_3_law_algebra_lawful_locus_prd.md) /
[PRD-4 第IV部](lean_ag_part_4_obstruction_cohomology_prd.md)

## 問い

第III部で別々に切り出した lawful loci の同時実現は、交差の仕方まで語れるか。
すなわち、法則の衝突は

```text
LawConflict_i(U,V) = Tor_i(O_X/I_U, O_X/I_V)
```

として機械検証できるか。特に、

- U-safe かつ V-safe でも jointly safe でない現象が、共有 witness の
  `Tor_1 != 0` として現れること(定理6.1、命題9.2 の反例族)
- 修復が障害を別 axis へ転送することが、固定された pairing で読めること
  (定理10.5 / 10.6)

が Lean 上で sorry なしに証明できるか。

採否規律: LawConflict の構成と、CBI 6本(命題9.2 / 定理10.5 / 10.6 / 12.2 /
13.3 / 13.4)・定理6.1・定理7.3・命題5.5 に寄与する定義・命題だけを形式化
対象に採る。寄与しない要素(例、原則、標語)は対象外とする。実装中に、
derived 構成の仮定が本文に不足している、または第III部・第IV部の形式化と
接続できないことが見つかった場合、それは本文または本PRDの欠陥であり、
ループを停止して報告する。

## 中心方針

PRD-1〜4 で確立した方針を引き継ぐ(塔を下から積む / 忠実性契約 /
`Formal/AG` 新規実装 / `axiom`・`sorry` 禁止 / Mathlib 二段橋 / 台帳統合 /
先行PRD依存の blocked 規律 / 部番号付き台帳ラベル)。

本PRDで新たに加わる方針が四つある。

**(1) derived 機構は chart 水準の加群複体で実体化する。** derived category
`D(O_X)` の一般論は立てない。derived lawful locus は selected generators の
Koszul complex で、derived intersection は局所 chart 上の加群複体
`(O_X/I_U) ⊗^L (O_X/I_V)` で表現し、`LawConflict_i` は Mathlib の Tor
(左導来テンソル)への橋として定義する。grading 規約(homological `H_i` を
一次とし、本文の `H^{-1}` 読みは規約として記録)を固定する。

**(2) Taylor resolution が本PRD最重量の数学。** 命題5.5(monomial conflict
calculation)は、(a) 任意の有限自由分解が Tor を計算するという一般補題
(Mathlib 橋)と、(b) square-free monomial ideal の Taylor complex の構成と
それが自由分解であることの証明、の二段で形式化する。Scarf complex と
lcm-lattice resolution は対象外とする(非主張)。

**(3) PRD-4 placeholder の清算と境界の引き直し。** PRD-3 / PRD-4 が第V部へ
委譲した derived intersection(`⊗^L`、Koszul)は本PRDで実体化する。一方、
PRD-4 の `DerOb_U`(余接複体 `L_{Flat/X}` と `Ext¹`)は、第V部本文が余接
複体を展開しないため、本PRDでも placeholder のまま維持する。余接複体の
形式化はどの部の PRD にも割り当てられていない未来課題として台帳に記録する。

**(4) Hilbert 級数は最小限の自前定義を許す。** 定理12.2(干渉恒等式、
拡張考察ノートの大定理G5)に必要な Hilbert 級数は、Mathlib に十分な資産が
ない場合、有限生成次数付き加群の次数別次元から形式冪級数として定義する。
有理関数表示や Hilbert 多項式の一般論は開発しない。

## 背景

- 当初計画では第IV部の次に第VIII部(measurement)を予定していたが、
  第VIII部の定理4.2 が Tor 計算(Koszul / Taylor / monomial resolution)を
  含み、第V部の機構に依存するため、部の順序どおり第V部を先に積む方針へ
  変更した(2026-06-13 ユーザー判断)。これにより PRD-3 / PRD-4 が委譲した
  derived placeholder も部の順序で自然に解消される。
- 本PRDの実装は PRD-3(`O_X^U`、`I_Ob^U`、`Flat_U(X)`、square-free regime、
  Stanley-Reisner)と PRD-4(障害コホモロジー、有限モデル)の成果物に
  依存する。依存先未実装の要求は `blocked` として台帳に記録する(R0)。
- ArchSig v0.4.0 の LawConflict evaluator(R5)は本PRDの
  `LawConflict_i = Tor_i` と monomial 計算(命題5.5)が理論側の対応物で
  ある。定理12.2 は大定理G5 として数値検算済み(2026-06-12)であり、本PRDで
  完全証明化する。repair 側(§8–13)は ArchSig の repair 系読みと第VIII部の
  measurement synthesis の部品になる。
- flat base change(第VIII部 定理候補9.2 が参照)は第V部の範囲外である。

## アウトカム

本PRDの完了時点で、次が成り立つ。

1. 「法則の衝突は derived 非横断性である」が Lean 上の構成として存在する:
   Koszul 複体による derived lawful locus、chart 水準の derived
   intersection、`LawConflict_i = Tor_i`、横断性判定(定理7.3)。
2. 共有 witness 反例族(命題9.2)が証明され、「U-axis 改善は V-axis 非増加を
   含意しない」が反例つきで機械検証されている。
3. Taylor resolution により monomial law conflict が計算可能であること
   (命題5.5)が証明され、ArchSig LawConflict evaluator の理論アンカーが
   存在する。
4. Hilbert 級数干渉恒等式(定理12.2、大定理G5)が完全証明され、数値検算が
   機械証明に昇格している。
5. transfer pairing(定理10.5 / 10.6)と well-founded repair(定理13.3 /
   13.4)が証明され、repair の規律が形式化されている。
6. 第V部の本文ラベルと Lean 宣言の対応が両台帳で追跡できる。

## 第V部ラベルの処遇表

ギャップ分析はこの表を基準に行う。

| 本文ラベル | 処遇 | 備考 |
| --- | --- | --- |
| 定義2.1 Lawful Locus for a Law Universe | 定義 | PRD-3 の `I_Ob^U` の略記 `I_U` と pair `(U,V)` の記法整備 |
| 原則2.2 Law Universes Are Distinct Readings | 対象外 | 設計コメント |
| 定義2.3 Derived Lawful Locus | 定義+証明 | selected generators の Koszul complex で表現。`H_0(Kosz) = O/I`(truncation 補題、原則2.4 の内容)を証明する。生成系の選択は仮定として明示(R2) |
| 原則2.4 Classical Locus Is the Truncation | 証明 | R2 の truncation 補題で実現 |
| 定義3.1 Classical Joint Lawful Locus | 定義 | `V(I_U + I_V)` |
| 原則3.2 / 原則4.2 / 例4.3 | 対象外 | |
| 定義4.1 Derived Joint Lawful Locus | 定義 | chart 水準の加群複体。`D(O_X)` 一般論は立てない(R3) |
| 定義5.1 First Law Conflict Sheaf / 定義5.2 Higher Law Conflict Sheaves | 定義 | `LawConflict_i = Tor_i`(Mathlib 橋)。`H^{-1}` 読みは grading 規約として記録(R3) |
| 原則5.3 | 対象外 | |
| 定義5.4 Monomial Law Conflict Regime | 定義 | 共有 ambient `k[E_W]` 上の square-free monomial ideal 対(R4) |
| 命題5.5 Monomial Conflict Calculation | 証明 | (a) 有限自由分解が Tor を計算する一般補題、(b) Taylor complex の構成と分解能性。lcm の multidegree 読みを含む。Scarf / lcm-lattice は対象外(R4) |
| 例5.6 Shared Witness Factor Conflict | 例 theorem | `Tor_1(R/<xy>, R/<xz>) != 0` を principal resolution で直接計算(R11) |
| 定理6.1 Derived Law Conflict | 証明 | `LawConflict_1 != 0` → derived non-transverse(R5) |
| 定義7.1 / 7.2 / 7.4 Transversality | 定義 | (R5) |
| 定理7.3 Derived Transversality Criterion | 証明 | `Tor_i = 0 (i>0)` iff derived tensor が classical と quasi-iso(R5) |
| 原則7.5 | 対象外 | |
| 定義8.1 Repair Comparison Profile | 定義 | sec / geom 比較を持つ構造体。代表 profile(ideal-order / valuation / rank / support)を instance で与える(R6) |
| 定義8.2 Pullback Repair Profile / 定義8.3 Conflict Comparison Profile / 定義8.4 Repair Path | 定義 | (R6) |
| 原則8.5 / 原則9.1 / 9.1の読み | 対象外 | 9.1 の非含意の実証は命題9.2 が担う |
| 命題9.2 Shared-Witness Repair Counterexample [CBI] | 証明 | `s_t` 族の明示計算と一般化族 `<x y_1..y_m>, <x z_1..z_n>`。support-localized でない旨の注意も docstring に記録(R7) |
| 定義10.1 Transferred Obstruction | 定義 | (R8) |
| 例10.2 / 原則10.3 | 対象外 | |
| 定義10.4 Repair Direction and Transfer Pairing | 定義 | direction 空間・conflict class・support・residue target・zero predicate・pairing をデータとして固定(R8) |
| 定理10.5 Pairing-Based Transfer [CBI] | 証明 | 固定された pairing の下での nonzero → nontrivial residue(R8) |
| 定理10.6 Generic Transfer [CBI] | 証明 | `tau != 0` → `ker` は真部分空間。Mathlib 線形代数(R8) |
| 定義11.1 Structurally Lawful Repair | 定義 | `P_U` と `Q_{U,V}` に相対化した述語(R9) |
| 原則11.2 | 対象外 | |
| 系11.3 Refactoring Is Derived-Geometric | 対象外 | 数学的主張を含まない標語。docstring の設計コメントで反映 |
| 定義12.1 Graded Monomial Conflict Regime | 定義 | (R10) |
| 定理12.2 Hilbert Series Conflict Identity [CBI] | 証明 | 大定理G5。干渉級数 `Int_{U,V}(t)` の定義を含む(R10) |
| 原則12.3 | 対象外 | 非主張に記録 |
| 定義13.1 Well-Founded Repair Comparison Profile / 定義13.2 Sound Repair Step | 定義 | Mathlib `WellFounded` を使う(R11) |
| 定理13.3 Repair Termination [CBI] | 証明 | (R11) |
| 定理13.4 Sound Repair Synthesis [CBI] | 証明 | synthesis 規則を inductive に固定(R11) |

## 要求

### R0. 前提の確認と Formal/AG/Derived の立ち上げ

- 本PRDの実装は PRD-3(`Formal/AG/LawAlgebra`)と PRD-4
  (`Formal/AG/Cohomology`)の成果物に依存する。着手時に依存宣言の存在を
  確認し、未実装の場合は `blocked` として tracking Issue に記録する。
  先行PRDの実装を先取りしない。
- 第V部のモジュールを `Formal/AG/Derived/` 以下に実装する(例:
  `LawfulLoci.lean`, `Koszul.lean`, `DerivedIntersection.lean`,
  `LawConflict.lean`, `TaylorResolution.lean`, `Transversality.lean`,
  `RepairProfile.lean`, `Counterexample.lean`, `Transfer.lean`,
  `HilbertSeries.lean`, `WellFoundedRepair.lean`)。
- ルート import に追加し、CI の `lake build` 対象に含める。
- PRD-4 の `DerOb_U` placeholder は変更しない。余接複体の形式化が未割当の
  未来課題であることを `proof_obligations.md` に明記する。
- 完了条件: 空でない最初のモジュールが CI でビルドされ merge されている。

### R1. 記法と classical joint locus(定義2.1、3.1)

- `I_U` 略記と law universe pair `(U,V)` の記法を整備し、classical joint
  lawful locus `V(I_U + I_V)` を定義する(PRD-3 の `Flat_U` / zeroLocus を
  再利用する)。
- 完了条件: 定義が sorry なしで存在する。

### R2. Koszul 複体と derived lawful locus(定義2.3、原則2.4)

- selected defect sections(`I_U` の選ばれた生成系)に対する Koszul complex
  を定義する(Mathlib に Koszul complex の資産があれば橋として使い、
  なければ有限生成系に対する具体的な複体として構成する)。
- derived lawful locus `Flat_U^der(X)` を、生成系の選択を仮定として明示した
  上で、Koszul complex を structure sheaf 表現とする対象として定義する。
- truncation 補題を証明する: `H_0(Kosz(O_X; delta_U)) ≅ O_X / I_U`、
  すなわち `t_0 Flat_U^der(X) = Flat_U(X)`(原則2.4)。
- 完了条件: 定義と truncation 補題が sorry なしで存在する。

### R3. Derived Intersection と LawConflict(定義4.1、5.1、5.2)

- chart 水準の derived intersection を、加群複体
  `(O_X/I_U) ⊗^L (O_X/I_V)` として定義する(自由分解を一つ固定して tensor
  する形でよい。well-definedness は R4(a) の一般補題に委ねる)。
- `LawConflict_i(U,V) = Tor_i(O_X/I_U, O_X/I_V)` を Mathlib の Tor への橋と
  して定義する(`i > 0`)。`LawConflict_0 = O_X/(I_U + I_V)` を補題として
  証明する。
- grading 規約を固定する: homological `H_i` を一次とし、本文の
  `LawConflict_1 ≅ H^{-1}` 読みは規約として docstring に記録する。
- 大域読み(`H^0(X, LawConflict_1)` / hypercohomology)は、選択を明示した
  記法として定義する(無条件の大域理論は開発しない)。
- 完了条件: 定義と `LawConflict_0` 補題が sorry なしで存在する。

### R4. Monomial 計算と命題5.5(定義5.4、命題5.5)

- monomial law conflict regime(共有 ambient `R_W = k[E_W]` 上の
  square-free monomial ideal 対)を定義する(PRD-3 の square-free regime を
  pair へ拡張)。
- (a) 一般補題: `R/I_U` の任意の有限自由分解 `F` に対して
  `Tor_i(R/I_U, R/I_V) ≅ H_i(F ⊗ R/I_V)`(Mathlib の Tor API への橋)。
- (b) Taylor resolution: square-free monomial ideal の生成系に対する
  Taylor complex を構成し、それが `R/I` の自由分解であることを証明する。
  multidegree が forbidden support の lcm(`S ∪ T`)として読めることを
  補題にする。
- (a) + (b) を命題5.5 の theorem package として束ねる: monomial regime では
  `LawConflict_i` が有限自由複体の homology として計算できる。
- Scarf complex / lcm-lattice resolution は形式化しない。
- 完了条件: 命題5.5 package が sorry なしで証明され、
  `proof_obligations.md` で `proved` に昇格している。
  (b) が stall した場合は、principal monomial ideal と 2生成系の場合
  (例5.6 と命題9.2 に必要な範囲)を先に閉じる分割を許す。

### R5. 衝突定理と横断性(定理6.1、定義7.1 / 7.2 / 7.4、定理7.3)

- transverse / derived-transverse / non-transverse を定義する
  (`LawConflict_1 = 0` / `∀ i > 0, LawConflict_i = 0` / `∃ i > 0, ≠ 0`)。
- 定理6.1 を証明する: `LawConflict_1(U,V) != 0` ならば、derived
  intersection は次数 -1(homological 次数 1)の非零情報を持ち、joint
  lawfulness の読みは classical intersection に還元されない。
- 定理7.3 を証明する: `∀ i > 0, Tor_i = 0` と「derived tensor が classical
  tensor と quasi-isomorphic」の同値。
- 完了条件: 両定理が sorry なしで証明され、`proof_obligations.md` で
  `proved` に昇格している。

### R6. Repair Profile(定義8.1–8.4)

- repair comparison profile `P_U`(section-level / geometry-level 比較)を
  構造体として定義し、代表 profile(ideal-order / valuation / rank /
  support)を instance として与える。
- pullback repair profile(geometric repair `r : X -> X'` の比較を
  `r^{-1} I'_U · O_X <= I_U` または probe 経由で読む)を定義し、internal /
  geometric repair の二分を形式化する。
- conflict comparison profile `Q_{U,V}`(degree set `D`、comparison maps、
  order / vanishing predicate)を定義する。
- repair path(geometry morphism または section deformation)と「`U`-axis
  obstruction を減らす」述語を定義する。
- 完了条件: 定義群が sorry なしで存在する。

### R7. 命題9.2 Shared-Witness Repair Counterexample

- `R = k[x,y,z]`、`I_U = <xy>`、`I_V = <xz>`、section 族
  `s_t : R -> k[t]`(`x ↦ 1, y ↦ 1-t, z ↦ t`)を形式化し、次を証明する:
  (i) `s_t(xy) = 1-t`、`s_t(xz) = t`、したがって `t=0 → t=1` の path で
      U-residue は `1 → 0`、V-residue は `0 → 1`。
  (ii) この path は固定された residue 比較の下で U-axis を改善し V-axis を
       悪化させる(非含意の witness)。
  (iii) `Tor_1(R/<xy>, R/<xz>) != 0`(例5.6 の principal resolution 計算を
        使う)。
  (iv) 一般化族 `I_U = <x y_1, ..., x y_m>`、`I_V = <x z_1, ..., x z_n>` への
       拡張。
- この path が support-localized transfer の例ではないこと(`x ↦ 1` のため
  `V(x)` を通らない)を docstring に記録する(本文の注意)。
- 完了条件: (i)–(iv) が sorry なしで証明され、`proof_obligations.md` で
  `proved` に昇格している。

### R8. Transfer Pairing(定義10.1、10.4、定理10.5、10.6)

- transferred obstruction `TransOb_{U->V}(r)` の読みと、repair direction /
  transfer pairing のデータ(direction 空間、selected conflict class
  `kappa_{U,V}` とその support、support-localized 述語、residue target
  `TransRes` と zero / nontrivial predicate、pairing `< -, - >_{U,V}`)を
  定義する。
- 定理10.5 を証明する: 固定されたデータの下で
  `Nontrivial(< v, kappa >)` ならば `v` は非自明な transferred residue を
  持つ。`LawConflict_1 != 0` だけからは任意の direction の transfer を
  結論しないことを定理の形(support-localized 仮定の明示)で保つ。
- 定理10.6 を証明する: `k`-bilinear pairing と有限次元 direction 空間
  `T_rep` に対し、`tau_kappa != 0` ならば `ker(tau_kappa)` は真部分空間で
  あり、transfer-zero directions は真線形部分空間に含まれる。
- 完了条件: 両定理が sorry なしで証明され、`proof_obligations.md` で
  `proved` に昇格している。

### R9. Structurally Lawful Repair(定義11.1)

- structurally lawful repair を、`P_U` と `Q_{U,V}` に相対化した述語として
  定義する(selected obstruction decreases / required loci reachable /
  conflict non-increasing for selected degrees / transfer zero or
  controlled)。低次制限(`i = 1`)の読みを含む。
- 完了条件: 定義が sorry なしで存在する。

### R10. Hilbert 級数と定理12.2(定義12.1、定理12.2)

- graded monomial conflict regime を定義する。
- 有限生成次数付き `R`-加群の Hilbert 級数を形式冪級数として定義する
  (Mathlib に資産があれば橋、なければ次数別 `k`-次元から自前定義。
  有理関数表示は開発しない)。
- Hilbert 級数の部品補題を証明する: 短完全列での加法性、次数 shift 付き
  自由加群の級数、有限複体の Euler characteristic と homology の Euler
  characteristic の一致。
- 定理12.2 を証明する:
  `H_{R/I_U}(t) · H_{R/I_V}(t) / H_R(t) = Σ_i (-1)^i H_{LawConflict_i}(t)`
  (分母を払った form で形式化してよい: 両辺に `H_R(t)` を掛けた等式)。
  自由分解は R4(b) の Taylor resolution を使う。
- 干渉級数 `Int_{U,V}(t)` を定義する。
- 完了条件: 定理12.2 が sorry なしで証明され、`proof_obligations.md` で
  `proved` に昇格している(大定理G5 の数値検算の機械証明化)。

### R11. Well-Founded Repair と有限モデル拡張(定義13.1、13.2、定理13.3、13.4)

- well-founded repair comparison profile(Mathlib `WellFounded` の橋)と
  sound repair step(strict decrease / cleared / no-solution certificate の
  三分)を定義する。
- 定理13.3 を証明する: すべての step が減少するなら無限 repair sequence は
  存在しない。
- 定理13.4 を証明する: synthesis 規則(sound step または no-solution
  certificate のみを出す)は有限で停止し、出力は cleared または
  certificate のどちらかである。
- 有限モデル(`Formal/AG/Examples/`)を第V部の水準へ拡張する:
  (a) 例5.6 の `Tor_1(R/<xy>, R/<xz>) != 0` を example theorem として検証
      (PRD-3 の例5.6E の Stanley-Reisner chart と接続)。
  (b) 命題9.2 の `s_t` 族の数値挙動を example theorem として検証。
  (c) `I_U = <xy>`、`I_V = <xz>` に対する定理12.2 の両辺を具体的に計算し、
      数値例として一致を検証(G5 検算例の機械化)。
  (d) 小さな well-founded repair 列(2〜3 step で cleared に至る例と
      no-solution certificate に至る例)を検証。
- 完了条件: 定理13.3 / 13.4 と (a)–(d) が sorry なしで証明されている。

### R12. 台帳整備

- `lean_theorem_index.md` の AG 節に第V部の宣言を追加する(本文ラベル列は
  `V.` 付き)。
- `proof_obligations.md` に第V部の証明対象ラベル(命題5.5、定理6.1、7.3、
  命題9.2、定理10.5、10.6、12.2、13.3、13.4、truncation 補題、example
  theorem 群)を登録し、進行に応じて status を更新する。余接複体
  (`DerOb_U` の中身)を未割当の future proof obligation として明記する。
- 完了条件: 両台帳が最終実装と一致している。

## 非主張(claim boundary)

- 本PRDは derived category `D(O_X)` の一般論、∞-圏、spectral sequence を
  形式化しない。derived 構成は chart 水準の加群複体と Tor に限定される。
- 余接複体 `L_{Flat/X}` と `Ext¹`(PRD-4 の `DerOb_U` placeholder の中身)は
  本PRDでも形式化しない。第V部本文がこれを展開しないためであり、未割当の
  future proof obligation として台帳に記録する。
- Scarf complex、lcm-lattice resolution、minimal free resolution の一般論は
  形式化しない。命題5.5 は Taylor resolution(と任意の有限自由分解が Tor を
  計算する一般補題)の範囲で読む。
- `LawConflict_1 != 0` だけからは、特定の repair path / direction が transfer
  residue を持つことを結論しない(定義10.4 の support-localized 規律)。
  命題9.2 の path も support-localized transfer の例ではない。
- repair 定理は固定された comparison profile に相対化される。solver
  completeness、global repair optimality、全 law universe の同時改善、
  最短修復は主張しない(定理13.4 の非主張)。
- Hilbert 級数干渉は次数別の audit reading であり、law の優先度や実務上の
  repair 選好を決めない(原則12.3)。
- 系11.3 は標語であり、形式化対象としない。
- 第VI部の内容(特異点、monodromy、stack、obstruction の集中)は扱わない。

## 完了条件(Acceptance Criteria)

- [ ] AC1. `Formal/AG/Derived` が新設され、CI の `lake build` でビルドされる。
      先行PRD依存の blocked 判定が運用されている(R0)
- [ ] AC2. `I_U` 記法と classical joint locus が形式化されている(R1)
- [ ] AC3. Koszul complex と derived lawful locus が定義され、truncation 補題
      (`H_0 ≅ O/I`)が証明されている(R2)
- [ ] AC4. chart 水準 derived intersection と `LawConflict_i = Tor_i` 橋が
      定義され、`LawConflict_0` 補題が証明されている(R3)
- [ ] AC5. 有限自由分解が Tor を計算する一般補題が証明されている(R4)
- [ ] AC6. Taylor complex が構成され、自由分解であることが証明されている
      (R4)
- [ ] AC7. 命題5.5 package(lcm multidegree 読みを含む)が証明されている(R4)
- [ ] AC8. 定理6.1 と定理7.3 が sorry なしで証明されている(R5)
- [ ] AC9. repair / pullback / conflict comparison profile と repair path が
      形式化され、代表 profile の instance がある(R6)
- [ ] AC10. 命題9.2((i)–(iv))が sorry なしで証明されている(R7)
- [ ] AC11. transfer pairing のデータと定理10.5 / 10.6 が sorry なしで
      証明されている(R8)
- [ ] AC12. structurally lawful repair が形式化されている(R9)
- [ ] AC13. Hilbert 級数と部品補題(加法性 / shift / Euler characteristic)が
      形式化されている(R10)
- [ ] AC14. 定理12.2(大定理G5)が sorry なしで証明されている(R10)
- [ ] AC15. 定理13.3 / 13.4 が sorry なしで証明されている(R11)
- [ ] AC16. 有限モデル拡張((a) 例5.6 Tor 計算、(b) 命題9.2 数値挙動、
      (c) G5 数値例の機械化、(d) repair 列)が検証されている(R11)
- [ ] AC17. `Formal/AG` 全体に `axiom` / `admit` / `sorry` / `unsafe` が
      存在しない
- [ ] AC18. `lean_theorem_index.md` の AG 節が第V部の宣言を `V.` 付き
      本文ラベルで含み、最終実装と一致している(R12)
- [ ] AC19. `proof_obligations.md` に第V部の証明対象ラベルが登録され、
      証明済み分が `proved`、余接複体が未割当 future proof obligation と
      して明記されている(R12)

## 実行順序の指針

prd-loop のギャップ分析で対象を選ぶ際は、次の依存順を推奨する。

```text
R0 -> R1 -> R2 -> R3 -> R4 -> R5 -> (R6, R7 は並行可)
   -> R8 -> R9 -> (R10, R11 は並行可) -> R12
```

R12(台帳)は各周回で増分更新してよい。R11 の well-founded repair
(定理13.3 / 13.4)は Mathlib の `WellFounded` のみに依存し、R2〜R10 を
待たずに着手できる。R7(命題9.2)は R4 の Taylor resolution を待たず、
principal resolution の直接計算で着手できる。R4(b) と R10 が本PRDの重量級で
あり、stall した場合は R4 の分割規定(principal / 2生成系を先に閉じる)に
従い、R10 は分母を払った等式形での証明を優先する。
