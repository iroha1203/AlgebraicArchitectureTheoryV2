# AAT代数幾何版 Lean形式化 PRD-6: 第VI部 Singularity・Monodromy・Stack

対象本文: [第VI部 Singularity・Monodromy・Stack](algebraic_geometric_theory/part_6_singularity_monodromy_stack.md)

先行PRD:
[PRD-1 第I部](lean_ag_part_1_atoms_objects_laws_prd.md) /
[PRD-2 第II部](lean_ag_part_2_sites_sheaves_prd.md) /
[PRD-3 第III部](lean_ag_part_3_law_algebra_lawful_locus_prd.md) /
[PRD-4 第IV部](lean_ag_part_4_obstruction_cohomology_prd.md) /
[PRD-5 第V部](lean_ag_part_5_derived_law_geometry_repair_prd.md)

## 問い

第V部で構成した derived law conflict と repair geometry は、どこに集中し、
どの操作履歴で変化し、どの同型情報を保持して貼り合うのか。
すなわち、第VI部で導入される三つの構造

```text
singularity:
  obstruction が集中する場所。

monodromy:
  endpoint comparison では見えない経路依存 debt。

stack:
  refactor equivalence と decomposition non-uniqueness を保つ幾何。
```

を Lean 上で sorry なしに立ち上げられるか。特に、

- selected obstruction class が非零になる deformation が存在すれば stratum は
  `U`-singular であること(定理6.1 / 6.2 / 系6.5)
- selected operation homotopy presentation に対して、transport が fundamental group へ
  降りる条件を generator 2-cell の monodromy zero で特徴づけられること
  (定理10.5)
- endpoint-equivalent loop でも monodromy が非恒等なら hidden architecture debt を
  持つこと(定理11.1)
- refactor groupoid と invariant family が Galois connection をなすこと(定理12.4)
- local decompositions が存在しても gerbe obstruction が非零なら global canonical
  decomposition は存在しないこと(定理16.2)

が Lean 上で機械検証できるか。

採否規律: singularity / monodromy / stack の構成と、CBI 定理
(6.1 / 6.2 / 10.5 / 10.7 / 12.4)および定理11.1・定理16.2・系6.5に寄与する
定義・命題だけを形式化対象に採る。寄与しない要素(例、原則、標語、代表例リスト、
God object を大きさで読む否定の自然言語説明)は対象外とする。実装中に、cotangent / Ext / stack / monodromy
に必要な仮定が本文に不足している、または第III〜V部の形式化と接続できないことが見つかった場合、
それは本文または本PRDの欠陥であり、ループを停止して報告する。

## 中心方針

PRD-1〜5 で確立した方針を引き継ぐ(塔を下から積む / 忠実性契約 /
`Formal/AG` 新規実装 / `axiom`・`sorry` 禁止 / Mathlib 二段橋 / 台帳統合 /
先行PRD依存の blocked 規律 / 部番号付き台帳ラベル)。

本PRDで新たに加わる方針が五つある。

**(1) cotangent / tangent は deformation-obstruction interface として実体化する。**
第VI部は `L_{S/U}`、`T_{S/U}`、`Ext^i`、Kuranishi map を使うが、Illusie 型の余接複体一般論を
このPRDで構築しない。Lean では、選ばれた stratum と law universe に対して、

```text
CotangentData
TangentData
DeformationObstructionTheory
```

を構造体として置き、complex、cohomology group、Ext group、obstruction map、lift/fill predicate、
effectiveness / soundness をフィールドとして明示する。定理6.1 / 6.2 はこの interface の範囲で証明する。
余接複体の一般構成、derived deformation theory の一般定理、`RHom` の総合的形式化は未割当の future proof obligation として台帳に残す。

**(2) operation homotopy は combinatorial presentation として扱う。**
未指定の homotopy quotient や ∞-groupoid は立てない。operation graph、homotopy generator family、
presentation two-complex `K_H(X,U)` を一次対象とし、presented architecture fundamental group は
edge-path free group / free groupoid を generator 2-cell の relation で quotient して定義する。
逆向き edge は形式的逆元であり、実際の reverse architecture operation の存在を主張しない。

**(3) monodromy は自動構造ではなく transport data である。**
operation loop が obstruction / semantic / effect sheaf に作用するとは、
coefficient transport functor または representation

```text
rho : pi_1^AAT(X,U,H,A) -> Aut(Coeff_U)
```

が与えられた場合に限る。Transport Descent Criterion は quotient group の普遍性として証明し、
未選択の path や未構成の operation への monodromy claim は出さない。

**(4) stack は groupoid-valued descent object として先に形式化し、algebraicity は predicate に分ける。**
`ArchitectureStack` は groupoid-valued presheaf / sheaf と descent condition として定義する。
`AlgebraicArchitectureStack` は representable diagonal、atlas、structure descent を満たす強い predicate として置く。
Mathlib の stack / algebraic stack の一般論が不足する場合は、AAT 側のデータ構造と predicate を一次にし、
必要な bridge theorem のみを作る。

**(5) gerbe obstruction は non-abelian と banded abelian を分ける。**
`[gerbe_U(X)] in H^2(X, Aut(Dec_U))` は一般には ordinary abelian cohomology の元ではない。
Lean では non-abelian gerbe obstruction を abstract class として定義し、banded abelian sheaf `A` が固定された場合に限り
PRD-4 の abelian Čech `H^2` へ橋を張る。定理16.2 は、global decomposition があれば gerbe class が zero になるという
soundness 仮定と、concrete nonzero class を theorem 引数に取る。

## 背景

- PRD-5 は lawful loci の derived intersection、`LawConflict_i = Tor_i`、repair transfer、
  Hilbert series accounting、well-founded repair を形式化対象にした。第VI部はその次段で、
  derived obstruction が architecture geometry の中でどこに集中し、どの operation history によって
  residue を残し、decomposition の非一意性としてどう現れるかを扱う。
- PRD-4 は non-abelian torsor / gerbe / stack obstruction を第VI部の領分として非主張に置いていた。
  本PRDはそのうち、groupoid-valued stack、decomposition gerbe、monodromy transport の最小構造を形式化する。
- PRD-5 では余接複体 `L_{Flat/X}` と `Ext^1` の中身を未割当 future proof obligation とした。
  第VI部は `L_{S/U}` と `Ext^1` を使うため、本PRDでは抽象 interface として扱い、一般構成はまだ証明対象にしない。
- 第VII部は第VI部の singularity / monodromy を analytic representation として読むため、
  本PRDの `SingProfile` や `MonIndex` の土台になる構造を定義する。ただし representation / metric / measurement は
  PRD-7 / PRD-8 の範囲であり、本PRDでは構成済み geometry 内の構造に留まる。

## アウトカム

本PRDの完了時点で、次が成り立つ。

1. architecture stratum、cotangent / tangent interface、smooth / singular predicate、normal cone reading、
   Kuranishi data の型が Lean 上に存在する。
2. 定理6.1 / 6.2 / 系6.5 により、selected obstruction class の非零性から singularity を結論する低次 deformation-obstruction logic が証明されている。
3. operation category、operation path、homotopy generator family、presentation two-complex、
   presented architecture fundamental group が構成され、Transport Descent Criterion(定理10.5)が証明されている。
4. monodromy action、finite Gauss-Manin system、measured square monodromy、AMI が定義され、
   square monodromy nonfillability(定理10.7)と monodromy debt theorem(定理11.1)が証明されている。
5. refactor groupoid と operation-invariant Galois correspondence(定理12.4)が証明されている。
6. architecture stack、algebraic architecture stack predicate、quotient stack と codebase essence、decomposition stack、
   gerbe obstruction、No Canonical Decomposition(定理16.2)が形式化されている。
7. 第VI部の本文ラベルと Lean 宣言の対応が両台帳で追跡できる。

## 第VI部ラベルの処遇表

ギャップ分析はこの表を基準に行う。

| 本文ラベル | 処遇 | 備考 |
| --- | --- | --- |
| 定義2.1 Architecture Stratum | 定義 | `S ⊆ X` または selected subobject / locally closed subgeometry として定義(R1) |
| 原則2.2 Stratum Relativity | 対象外 | 型パラメータとして反映 |
| 定義3.1 Cotangent Complex | 定義(抽象 interface) | `CotangentData S U`。一般余接複体の構成は future obligation(R2) |
| 定義3.2 Tangent Complex | 定義(抽象 interface) | `T_{S/U} = RHom(L,O)` は interface のフィールド。cohomological grading convention を docstring に記録(R2) |
| 原則3.3 Tangent Is Not Operation List | 対象外 | 非主張に記録 |
| 定義4.1 U-Smooth Stratum | 定義 | `DefTest_U(S)`, `LiftFill_U`, `ob_U`、effectiveness / soundness を明示(R2) |
| 原則4.2 Smooth Does Not Mean Small | 対象外 | |
| 定義5.1 U-Singular Stratum | 定義 | `∃ eta, ob_U eta ≠ 0` を主定義とする。`not smooth` との同値は exactness 仮定下のみ(R2) |
| 定義5.2 Normal Cone Reading | 定義 | PRD-3 の `I_U` / `Flat_U` と接続。structural repair direction の predicate を置く(R2) |
| 原則5.3 Singularity Is Repair Difficulty | 対象外 | |
| 定理6.1 Architecture Singularity Criterion [CBI] | 証明 | 非零 selected obstruction class → `U`-singular(R3) |
| 定理6.2 Square-Zero Lifting Obstruction [CBI] | 証明 | square-zero extension と obstruction class の soundness interface に相対化(R3) |
| 定義6.3 Kuranishi Map | 定義 | `Tan`, `Obs`, `Defhat`, `kappa` のデータ構造(R3) |
| 定理候補6.4 Kuranishi Local Model | statement のみ | local model / zero locus statement。証明しない(R3) |
| 系6.5 Singular Boundary | 証明 | boundary stratum と `H^1(T_{B/U}) != 0` から singular boundary(R3) |
| 定義7.1 God Object | 定義 | singular stratum + multiple law loci non-transverse。size は参照しない(R3) |
| 原則7.2 Size Is Not Singularity | 対象外 | |
| 定義8.1 Operation Category | 定義 | operation graph / category。selected operation family に相対化(R4) |
| 定義8.2 Operation Path | 定義 | composable arrows / finite path(R4) |
| 定義9.1 Refactor-Equivalent Endpoint | 定義 | endpoint equivalence relation / selected invariants preservation(R4) |
| 定義9.2 Operation Loop | 定義 | endpoint-equivalent loop。homotopy class は R5 の presentation で扱う(R4) |
| 定義9.3 Homotopy Generator Family | 定義 | selected 2-cell relation family(R5) |
| 定義9.4 Presentation Two-Complex | 定義 | edge = operation、2-cell = generator relation(R5) |
| 定義9.5 Presented Architecture Fundamental Group | 定義+証明 | free group / free groupoid quotient。relation の universal property を補題化(R5) |
| 原則9.6 Homotopy Presentation Boundary | 対象外 | 非主張に記録 |
| 定義10.1 Monodromy Action | 定義 | `rho : pi_1 -> Aut(Coeff_U)` と induced actions(R6) |
| 定義10.2 Finite Gauss-Manin System | 定義 | finite operation groupoid から `Vect_k` への functor-like data(R6) |
| 定義10.3 Monodromy Debt | 定義 | `Mon_gamma(Ob_U) != id` を debt predicate として読む(R6) |
| 定義10.4 Measured Square Monodromy | 定義 | `mu_x(sigma)`。axis detecting equality data を含む(R6) |
| 定理10.5 Transport Descent Criterion [CBI] | 証明 | relation boundary transport zero iff transport descends to presented group(R7) |
| 定義10.6 Architectural Monodromy Index | 定義 | finite weighted sum。measurement は後続PRD(R6) |
| 定理10.7 Square Monodromy Nonfillability [CBI] | 証明 | `mu_x(sigma) != 0` → selected filling refuted(R7) |
| 定理11.1 Monodromy Debt | 証明 | endpoint-equivalent + nonidentity monodromy → hidden debt(R7) |
| 定義12.1 Refactor Groupoid | 定義 | selected essence preserving equivalences(R8) |
| 原則12.2 Refactor Is Equivalence, Not Equality | 対象外 | |
| 定義12.3 Operation-Invariant Galois Data | 定義 | `Inv(G)` / `Ops(I)` as polarities(R8) |
| 定理12.4 Operation-Invariant Galois Correspondence [CBI] | 証明 | inclusion orders で Galois connection(R8) |
| 原則12.5 Galois Relativity | 対象外 | |
| 定義13.1 Architecture Stack | 定義 | groupoid-valued presheaf / descent object(R9) |
| 原則13.2 Stack Keeps Equivalences | 対象外 | |
| 定義13.3 Algebraic Architecture Stack | 定義 | representable diagonal / atlas / descent of structure の predicate(R9) |
| 定義14.1 Codebase Essence | 定義 | quotient stack `[X^U / Ref_U]` as action groupoid stack / predicate(R10) |
| 原則14.2 Essence Is Not Text Identity | 対象外 | |
| 定義15.1 Decomposition Stack | 定義 | local decomposition groupoid-valued stack(R11) |
| 原則15.2 No Privileged Decomposition | 対象外 | 非主張に記録 |
| 定義16.1 Gerbe Obstruction | 定義 | non-abelian gerbe class、banded abelian bridge を分離(R11) |
| 定理16.2 No Canonical Decomposition | 証明 | nonzero gerbe class → no global canonical decomposition(R11) |
| 原則16.3 Decomposition Failure Is Not Confusion | 対象外 | |
| §17 Part6 の結論 | 対象外 | synthesis 文。台帳には登録しない |

## 要求

### R0. 前提の確認と Formal/AG/SingularityMonodromyStack の立ち上げ

- 本PRDの実装は PRD-3(`Formal/AG/LawAlgebra`)、PRD-4(`Formal/AG/Cohomology`)、
  PRD-5(`Formal/AG/Derived`)の成果物に依存する。着手時に依存宣言の存在を確認し、
  未実装の場合は `blocked` として tracking Issue に記録する。先行PRDの実装を本PRDのループで先取りしない。
- 第VI部のモジュールを `Formal/AG/SingularityMonodromyStack/` 以下に実装する。ファイル分割は本文の節構成に概ね対応させる。
  例:
  `Stratum.lean`, `CotangentInterface.lean`, `SmoothSingular.lean`,
  `Kuranishi.lean`, `OperationCategory.lean`, `OperationHomotopy.lean`,
  `Monodromy.lean`, `GaussManin.lean`, `RefactorGroupoid.lean`,
  `ArchitectureStack.lean`, `QuotientStack.lean`, `DecompositionGerbe.lean`。
- ルート import に追加し、CI の `lake build` 対象に含める。
- PRD-5 で未割当とされた余接複体一般構成は、本PRDでは interface としてのみ扱う。
  台帳には「interface 実装済み / general cotangent complex construction は future obligation」と明記する。
- 完了条件: 空でない最初のモジュールが CI でビルドされ merge されている。

### R1. Stratum と相対化(定義2.1)

- architecture stratum `S` を、architecture scheme / geometry `X` の selected subobject、locally closed subgeometry、
  または predicate-valued subfunctor として定義する。最初の実装では `S : Set X.Point` に decoration compatibility を添えた構造体でよい。
- stratum の reading parameter として、Atom vocabulary、law universe、coverage topology、signature axes、coefficient structure を持たせる。
- component / boundary / service / semantic boundary / runtime interaction などの代表例は carrier label として置けるが、実例証明は R12 に回す。
- 完了条件: 定義が sorry なしで存在する。

### R2. Cotangent / Tangent interface と smooth / singular(定義3.1、3.2、4.1、5.1、5.2)

- `CotangentData(S,U)` を構造体として定義する。少なくとも次を含む。

```text
L_{S/U}:
  selected cotangent complex object.

baseMap:
  S -> X_U or selected law-coordinate base map.

pullback:
  selected local base xi : T -> S に沿う pullback complex.
```

- `TangentData(S,U)` を定義し、`T_{S/U}`、`H^0(T_{S/U})`、`H^1(T_{S/U})`、
  obstruction class の target を明示する。`RHom` の一般構成はフィールドとして受ける。
- `DeformationTest_U(S)`、`LiftFill_U(eta)`、`ob_U(eta)`、effective obstruction theory
  (`ob=0 -> LiftFill`)、soundness (`LiftFill -> ob=0` / `ob≠0 -> not LiftFill`)を構造体で定義する。
- `USmooth(S,U)` を本文どおり `forall eta, LiftFill eta ∧ ob eta = 0` として定義する。
  `forall eta, ob eta = 0` による smoothness criterion は effectiveness / soundness 仮定下の補題にする。
- `USingular(S,U)` を `exists eta, ob eta != 0` として定義する。
  `not USmooth` との同値は、selected obstruction theory の exactness 仮定がある場合に限って補題にする。
- normal cone reading `C_{S/Flat_U}` と structural repair direction predicate
  (`pointsTowardVanishing I_U` など)を定義する。PRD-3 の `Flat_U` / `I_U` を再利用する。
- 完了条件: 定義群と smoothness criterion / singular-not-smooth 条件付き補題が sorry なしで存在する。

### R3. Singularity 定理群・Kuranishi・God Object(定理6.1、6.2、定義6.3、定理候補6.4、系6.5、定義7.1)

- 定理6.1を証明する: selected first-order deformation `eta` について `ob_U(eta) != 0` なら、
  定義5.1により `S` は `U`-singular である。`H^1(T_{S/U})` が obstruction target を計算する仮定は theorem 引数に明示する。
- 定理6.2を証明する: square-zero extension data、pullback cotangent complex、obstruction class、
  soundness field `ob_T(xi) != 0 -> not Lift` の下で、nonzero obstruction が lift failure を与える。
  `ob=0` の lift torsor / automorphism statement は effectiveness 仮定下の補題に分ける。
- Kuranishi data を定義する。

```text
Tan_{S,p}
Obs_{S,p}
Defhat_{S,p}
kappa_{S,p} : Defhat -> Obs
```

- 定理候補6.4を statement として形式化する。`lawful deformation germ = zero locus of kappa` と
  `kappa(v) != 0 -> v does not lift` を Prop としてコンパイル可能にする。証明はしない。
- 系6.5を証明する: boundary stratum `B` について、selected obstruction class family に `H^1(T_{B/U})` の
  nonzero class が与えられれば `B` は `U`-singular boundary` である。
- God object を `USingular(S,U)` と multiple law loci non-transverse predicate(PRD-5 の `NonTransverse`)の組として定義する。
- 完了条件: 定理6.1 / 6.2 / 系6.5 が sorry なしで証明され、定理候補6.4 が statement としてコンパイルされている。

### R4. Operation Category・Path・Endpoint Equivalence(定義8.1、8.2、9.1、9.2)

- selected architecture states / sections を object、selected operation を morphism とする `Op_U(X)` を定義する。
  Mathlib `Category` に載せられる場合は bridge instance を作る。難しい場合はまず finite operation graph と composable path を一次にする。
- operation path を finite list of composable operations として定義し、identity path、path concatenation、associativity 補題を証明する。
- refactor-equivalent endpoint `A ~_ref B` を、selected invariant / essence preservation predicate に相対化して定義する。
- operation loop を `gamma : A -> A'` と `A' ~_ref A` の組として定義する。
- 完了条件: 定義と path concatenation 補題が sorry なしで存在する。

### R5. Operation Homotopy Presentation と `pi_1^AAT`(定義9.3–9.5)

- homotopy generator family `H_U(X)` を、operation path pairs / loop relators の finite family として定義する。
- presentation two-complex `K_H(X,U)` を、vertices = architecture states、edges = selected operations、
  2-cells = homotopy generators として定義する。
- presented architecture fundamental groupを、base state `A` を固定した edge-path free group / free groupoid の quotient として定義する。
  Mathlib の `FreeGroup`、`PresentedGroup`、または quotient group API を橋として使う。
- quotient universal property を補題として証明する: free transport が relators を identity へ送る iff quotient group への homomorphism に因子化する。
- edge の形式的逆元は operation の逆操作を主張しないことを docstring に記録する。
- 完了条件: `pi_1^AAT(X,U,H,A)` と universal property 補題が sorry なしで存在する。

### R6. Monodromy Action・Gauss-Manin・Measured Square(定義10.1–10.4、10.6)

- coefficient object `Coeff_U` と automorphism group `Aut(Coeff_U)` を定義する。
  obstruction / semantic / effect sheaf への product action は、必要なら product group として扱う。
- monodromy representation

```text
rho_{U,H,A} : pi_1^AAT(X,U,H,A) -> Aut(Coeff_U)
```

を定義し、`Mon_gamma` を評価として定義する。
- finite Gauss-Manin system を、finite operation groupoid から finite-dimensional `k`-vector spaces への functor-like data として定義する。
  `GM_id = id`、`GM_{β ∘ α} = GM_β ∘ GM_α` をフィールドにする。
- monodromy debt predicate `Mon_gamma(Ob_U) != id` を定義する。
- measured square monodromy `mu_x(sigma)` を、boundary loop transport と selected axis equality-defect reading から定義する。
- AMI を finite measured square family と positive weights の weighted sum として定義する。
  `DistanceValue` / measurement verdict への接続は PRD-8 に回す。
- 完了条件: 定義群と basic functoriality 補題が sorry なしで存在する。

### R7. Transport Descent・Square Nonfillability・Monodromy Debt(定理10.5、10.7、11.1)

- 定理10.5を証明する: R5 の quotient universal property を使い、edge transport が relation boundary を
  selected detecting axes ですべて zero にする iff `pi_1^AAT` への representation に降りる。
  detecting axis family が equality-reflecting であることを theorem 引数に明示する。
- 定理10.7を証明する: selected axis `x` が transport equality を検出し、`mu_x(sigma) != 0` なら、
  `sigma` の boundary loop は selected x-axis filling として読めない。
- 定理11.1を証明する: endpoint-equivalent loop、monodromy action defined、`Mon_gamma(Ob_U) != id` の下で、
  hidden architecture debt predicate が成立する。debt predicate が nonidentity monodromy を含むように定義されていることを明示する。
- 完了条件: 定理10.5 / 10.7 / 11.1 が sorry なしで証明され、`proof_obligations.md` で `proved` に昇格している。

### R8. Refactor Groupoid と Galois Correspondence(定義12.1、12.3、定理12.4)

- refactor groupoid `Ref_U(X)` を定義する。対象は selected essence を持つ architecture objects / schemes、
  射は selected invariants を保存する refactor equivalence とする。
- groupoid laws(identity / inverse / composition)を構造体フィールドとして持たせ、Mathlib `Groupoid` へ bridge できる場合は instance を作る。
- `SubGpd(Ref_U(X))`、`InvFam_U(X)`、operation family が保存する invariant `Inv(G)`、
  invariant family を保存する operation `Ops(I)` を定義する。
- 定理12.4を証明する: preservation relation `Preserves(g, i)` に対して、

```text
Inv(G) = { i | forall g in G, Preserves(g,i) }
Ops(I) = { g | forall i in I, Preserves(g,i) }
```

と定義すると、inclusion order 上で

```text
G <= Ops(I) iff I <= Inv(G)
```

が成り立つ。Mathlib `GaloisConnection` への bridge theorem を作る。
- 完了条件: 定理12.4 が sorry なしで証明されている。

### R9. Architecture Stack と Algebraic Architecture Stack predicate(定義13.1、13.3)

- base category `AATBase` を固定し、groupoid-valued presheaf

```text
Arch_U : AATBase^op -> Groupoids
```

を定義する。
- local objects、overlap isomorphisms、cocycle condition、effective descent をまとめた `ArchitectureStack` predicate を定義する。
- `AlgebraicArchitectureStack` を、以下の predicate を持つ強い構造として定義する。

```text
representable diagonal
atlas from an ArchitectureScheme
descent of obstruction ideals / law sheaves / signature sheaves / structure sheaves
```

- algebraic stack の一般理論は開発せず、representability / atlas / descent of structure はデータと仮定として明示する。
- 完了条件: 定義と descent predicate が sorry なしで存在する。

### R10. Codebase Essence as Quotient Stack(定義14.1)

- refactor groupoid object `Ref_U ⇉ X^U` の action data を定義する。

```text
source, target
identity
inverse
composition
action compatibility with law / obstruction / signature / structure sheaf
```

- quotient stack / action groupoid stack `[X^U / Ref_U]` を `Ess_U(X)` として定義する。
  Mathlib の quotient stack 一般論に依存しない場合は、action groupoid の groupoid-valued presheaf と descent predicate として置く。
- `Ess_U(X)` が text identity や graph isomorphism ではなく、selected geometry modulo refactor equivalence であることを docstring に記録する。
- 完了条件: 定義が sorry なしで存在する。

### R11. Decomposition Stack・Gerbe・No Canonical Decomposition(定義15.1、16.1、定理16.2)

- decomposition stack `Dec_U(X)` を、local context `W` に admissible decomposition groupoid を返す groupoid-valued stack として定義する。
- decomposition equivalence(refactor equivalence / semantic equivalence / boundary-preserving equivalence)を groupoid の射として保持する。
- gerbe obstruction を定義する。
  - non-abelian gerbe class: abstract pointed obstruction type / nonzero predicate。
  - banded abelian gerbe: abelian sheaf `A` と PRD-4 の `H^2(X,A)` への bridge。
- `globalCanonicalDecomposition` と `localDecompositionsExist` を定義し、
  `globalCanonicalDecomposition -> gerbeClass = 0` を soundness hypothesis として明示する。
- 定理16.2を証明する: local decompositions、`Aut(Dec_U)`、gerbe class、soundness、`[gerbe_U(X)] != 0` の下で、
  global canonical decomposition は存在しない。
- 完了条件: 定理16.2 が sorry なしで証明され、`proof_obligations.md` で `proved` に昇格している。

### R12. 有限モデルの拡張

- PRD-1〜5 の有限モデル(`Formal/AG/Examples/`)を第VI部の水準へ拡張する。
  (a) singular boundary toy model: boundary stratum `B` と selected obstruction class を構成し、系6.5 を example theorem として検証する。
  (b) operation square toy model: commuting square と nonzero `mu_x` を持つ square を構成し、定理10.7 により filling refutation を検証する。
  (c) transport descent toy model: relator の boundary transport が zero の場合に representation が quotient へ降りること、
      nonzero の場合に降りないことを example theorem として検証する。
  (d) refactor Galois toy model: 2〜3個の operation と invariant から Galois connection を計算する。
  (e) decomposition gerbe toy model: local decompositions は存在するが selected obstruction class が nonzero で global canonical decomposition が存在しない例を検証する。
- これらは第VII部の singularity profile / monodromy index の golden examples として再利用できる形を保つ。
- 完了条件: (a)–(e) が sorry なしで存在する。

### R13. 台帳整備

- `lean_theorem_index.md` の AG 節に第VI部の宣言を追加する(本文ラベル列は `VI.` 付き)。
- `proof_obligations.md` に第VI部の証明対象ラベル(定理6.1、6.2、系6.5、定理10.5、10.7、11.1、12.4、16.2、
  Kuranishi Local Model statement、example theorem 群)を登録し、進行に応じて status を更新する。
- `CotangentComplexGeneralConstruction`、`RHomGeneralConstruction`、`AlgebraicStackGeneralTheory`、
  `NonAbelianGerbeCohomologyGeneralTheory` を未割当の future proof obligation として明記する。
- 処遇表で「対象外」のラベルは台帳に登録しない。
- 完了条件: 両台帳が最終実装と一致している。

## 非主張(claim boundary)

- 本PRDは余接複体の一般構成、`RHom` の一般構成、Ext の一般的導来関手理論を形式化しない。
  `L_{S/U}`、`T_{S/U}`、`Ext^i` は selected deformation-obstruction interface に相対化される。
- Kuranishi Local Model(定理候補6.4)は statement のみであり、本PRDの完了は Kuranishi 理論の一般証明を含まない。
- `H^1(T_{S/U}) != 0` は obstruction space が非自明であること、または selected obstruction class の存在可能性を読む。
  すべての deformation が obstructed であるとは主張しない。
- God object は大きさ、line count、method count、dependency count では定義しない。
  それらは representation / metric reading になりうるが、singularity そのものではない。
- `pi_1^AAT(X,U,H,A)` は選ばれた operation graph と homotopy generator family に相対化される。
  未選択の operation、未選択の semantic equivalence、未構成の path は含まない。
  形式的逆元は reverse architecture operation の存在を主張しない。
- monodromy は AAT geometry が自動的に持つ構造ではない。coefficient transport / representation が与えられた場合だけ定義される。
- `AMI_x` は measured square family に対する analytic / measurement-facing reading であり、measurement verdict は PRD-8 の範囲である。
- `ArchitectureStack` は groupoid-valued descent object であり、`AlgebraicArchitectureStack` と呼ぶには representable diagonal / atlas / descent of structure を別途仮定する。
  本PRDは algebraic stack 一般論を構築しない。
- non-abelian gerbe obstruction は ordinary abelian cohomology class ではない。
  banded abelian sheaf が固定された場合に限り、PRD-4 の abelian `H^2` へ橋を張る。
- No Canonical Decomposition は、選ばれた `U`、coverage、decomposition stack、gerbe obstruction に相対化される。
  すべての decomposition notion について唯一分解がないとは主張しない。
- 第VII部の representation / period / metric / analysis、第VIII部の measurement verdict、第IX部の temporal evolution は扱わない。

## 完了条件(Acceptance Criteria)

- [ ] AC1. `Formal/AG/SingularityMonodromyStack` が新設され、CI の `lake build` でビルドされる。
      先行PRD依存の blocked 判定が運用されている(R0)
- [ ] AC2. Architecture stratum と reading parameter が形式化されている(R1)
- [ ] AC3. Cotangent / tangent deformation-obstruction interface が形式化され、smooth / singular / normal cone reading が定義されている(R2)
- [ ] AC4. smoothness criterion と singular-not-smooth 条件付き補題が sorry なしで証明されている(R2)
- [ ] AC5. 定理6.1 Architecture Singularity Criterion が sorry なしで証明されている(R3)
- [ ] AC6. 定理6.2 Square-Zero Lifting Obstruction が sorry なしで証明されている(R3)
- [ ] AC7. Kuranishi data が定義され、定理候補6.4 が statement としてコンパイルされている(R3)
- [ ] AC8. 系6.5 Singular Boundary と GodObject 定義が形式化されている(R3)
- [ ] AC9. Operation category / path / endpoint equivalence / operation loop が形式化されている(R4)
- [ ] AC10. Homotopy generator family、presentation two-complex、`pi_1^AAT`、quotient universal property が形式化されている(R5)
- [ ] AC11. Monodromy action、finite Gauss-Manin system、measured square monodromy、AMI が形式化されている(R6)
- [ ] AC12. 定理10.5 Transport Descent Criterion が sorry なしで証明されている(R7)
- [ ] AC13. 定理10.7 Square Monodromy Nonfillability が sorry なしで証明されている(R7)
- [ ] AC14. 定理11.1 Monodromy Debt が sorry なしで証明されている(R7)
- [ ] AC15. Refactor groupoid と定理12.4 Operation-Invariant Galois Correspondence が sorry なしで証明されている(R8)
- [ ] AC16. Architecture stack と AlgebraicArchitectureStack predicate が形式化されている(R9)
- [ ] AC17. Codebase essence `Ess_U(X) = [X^U / Ref_U]` が形式化されている(R10)
- [ ] AC18. Decomposition stack、gerbe obstruction、banded abelian bridge が形式化されている(R11)
- [ ] AC19. 定理16.2 No Canonical Decomposition が sorry なしで証明されている(R11)
- [ ] AC20. 有限モデル拡張((a) singular boundary、(b) square monodromy、(c) transport descent、
      (d) refactor Galois、(e) decomposition gerbe)が検証されている(R12)
- [ ] AC21. `Formal/AG` 全体に `axiom` / `admit` / `sorry` / `unsafe` が存在しない
- [ ] AC22. `lean_theorem_index.md` の AG 節が第VI部の宣言を `VI.` 付き本文ラベルで含み、最終実装と一致している(R13)
- [ ] AC23. `proof_obligations.md` に第VI部の証明対象ラベルが登録され、証明済み分が `proved`、
      Kuranishi Local Model と一般余接複体 / stack / gerbe 理論が future proof obligation として明記されている(R13)

## 実行順序の指針

prd-loop のギャップ分析で対象を選ぶ際は、次の依存順を推奨する。

```text
R0 -> R1 -> R2 -> R3
   -> R4 -> R5 -> R6 -> R7
   -> R8 -> R9 -> R10 -> R11
   -> R12 -> R13
```

R8(refactor Galois)は集合・順序論に近いため、R4〜R7の monodromy 実装を待たずに並行着手できる。
R9〜R11(stack / gerbe)も、最初は groupoid-valued presheaf と abstract gerbe class で閉じられるため、
operation homotopy 実装と並行可能である。R3 の Kuranishi statement は、R2 の deformation-obstruction interface が固まった時点で
早めに台帳へ登録する。R12 の有限モデルは各ブロックが閉じるたびに増分追加してよい。
