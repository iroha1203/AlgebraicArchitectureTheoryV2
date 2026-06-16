# 第II部 平坦性・計算・幾何

## 1. Flatness

Flatness は、選ばれた law universe に対して obstruction が消えている状態である。

Architecture object `A`、law universe `U`、obstruction valuation `omega_U` を取る。

```text
Flat_U(A) iff omega_U(A) = 0
```

ただし、`omega_U(A) = 0` が `Lawful_U(A)` と同値になるには、obstruction family が
law failure を正しく読む必要がある。

### 定義 1.1 Flatness Model

Flatness model は次の組である。

```text
M = (Obj, U, Ob, omega)
```

ここで、

```text
Obj   : architecture objects
U     : law universe
Ob    : obstruction circuits
omega : Obj -> SignatureValue
```

### 定義 1.2 Flat Object

`A` が `M` において flat であるとは、

```text
Flat_M(A) iff omega(A) = 0
```

が成り立つことをいう。

### 命題 1.3 Flatness Soundness

`omega` が sound なら、

```text
Flat_M(A) -> Lawful_U(A)
```

が成り立つ。

### 命題 1.4 Flatness Completeness

`omega` が complete なら、

```text
Lawful_U(A) -> Flat_M(A)
```

が成り立つ。

### 定理 1.5 Flatness-Lawfulness Equivalence

`omega` が sound かつ complete なら、

```text
Flat_M(A) iff Lawful_U(A)
```

である。

## 2. Zero Curvature

Zero curvature は、flatness の幾何学的な読みである。

Architecture object 上の law failure は、diagram の非可換性、cycle、projection failure、
substitution failure、state transition mismatch などとして現れる。これらのずれを
curvature と呼ぶ。

### 定義 2.1 Curvature

law universe `U` に対する curvature は、obstruction valuation の幾何学的表現である。

```text
kappa_U(A) = omega_U(A)
```

値域は boolean、natural number、ordered monoid、vector、matrix、weighted sum などで
よい。

### 定義 2.2 Zero Curvature

```text
ZeroCurvature_U(A) iff kappa_U(A) = 0
```

### 定理 2.3 Architecture Zero Curvature Theorem

law universe `U`、required obstruction family `W`、signature axes `S`、
curvature valuation `kappa_U` が同じ law failure を exact に読むとする。
このとき、次の四つの読みは一致する。

```text
Lawful_U(A)
  <-> NoRequiredObstruction_W(A)
  <-> RequiredSignatureAxesZero_S(A)
  <-> ZeroCurvature_U(A)
```

ここで、

```text
ZeroCurvature_U(A) iff kappa_U(A) = 0
NoRequiredObstruction_W(A) iff required obstruction circuit が存在しない
RequiredSignatureAxesZero_S(A) iff required signature axes がすべて zero
```

である。

この定理が AAT における architecture zero curvature theorem の基本形である。
零曲率とは、選ばれた law universe に対する required obstruction-free condition の
幾何学的な名前である。

## 3. Architecture Signature

Architecture signature は、architecture object の構造的状態を多軸で読む。

### 定義 3.1 Signature Axis

Signature axis は、選ばれた law、invariant、obstruction、measure に対応する座標である。

```text
Axis = { x_1, x_2, ..., x_n }
```

### 定義 3.2 Signature

Architecture signature は次の関数である。

```text
Sig(A) : Axis -> Value
```

または有限軸なら、

```text
Sig(A) = (v_1, v_2, ..., v_n)
```

### 例 3.3 代表軸

```text
cycle
projection violation
substitution violation
dependency direction violation
state transition mismatch
effect replay mismatch
semantic inconsistency
diagram non-commutation
```

### 定義 3.4 Required Zero Axis

axis `x` が required zero axis であるとは、lawfulness のために

```text
Sig(A)(x) = 0
```

が必要な軸であることをいう。

### 命題 3.5 Signature Flatness

required zero axes の集合を `R` とする。各 required axis が exact なら、

```text
Flat(A) iff forall x in R, Sig(A)(x) = 0
```

が成り立つ。

## 4. Projection, Substitution, Dependency

AAT の代表的 law は、Atom configuration 上の projection、substitution、dependency
に現れる。

### 4.1 Projection

Projection は、詳細な architecture object から抽象 object への写像である。

```text
pi : A -> B
```

Projection soundness は、`A` の選ばれた関係が `B` の関係として正しく読めることをいう。

```text
ProjectionSound(pi)
```

Projection obstruction は、`A` では relation が存在するのに、`B` では対応する relation が
失われる、または異なる relation として読まれるときに生じる。

### 4.2 Substitution

Substitution は、ある component または module を別のものへ置き換える operation である。

```text
sub : A[X] -> A[Y]
```

Substitution compatible であるとは、置換後も選ばれた contract と invariant が保存される
ことをいう。

```text
SubstitutionCompatible(sub)
```

典型的な obstruction は、置換後の contract が弱くなる、必要な effect が消える、
状態遷移が異なる、semantic reading が変わる、といった形で現れる。

### 4.3 Dependency

Dependency law は、Atom configuration の dependency relation に対する制約である。

```text
depends(x, y)
```

代表的な law は次である。

```text
NoCycle
LayerRespecting
AllowedDirection
NoHiddenCoupling
```

dependency obstruction は、cycle、逆向き依存、未宣言 coupling、過剰な reachable cone
として現れる。

## 5. Three-Layer Flatness

architecture object は、複数の reading を持つ。

```text
static
runtime
semantic
```

static reading は dependency、module、type、import、call relation などを見る。
runtime reading は process、message、transaction、retry、timeout、resource usage などを見る。
semantic reading は contract、meaning、domain invariant、effect meaning などを見る。

### 定義 5.1 Layered Flatness

三つの reading それぞれに flatness model を置く。

```text
M_static
M_runtime
M_semantic
```

三層 flatness は次である。

```text
Flat_3(A)
  iff Flat_static(A)
  and Flat_runtime(A)
  and Flat_semantic(A)
```

### 命題 5.2 Non-Implication

一般には次は成り立たない。

```text
Flat_static(A) -> Flat_runtime(A)
Flat_static(A) -> Flat_semantic(A)
Flat_runtime(A) -> Flat_semantic(A)
```

static dependency が整っていても、runtime retry storm や semantic contract mismatch が
残ることがある。

### 命題 5.3 Layer Interaction

三層の reading は独立ではない。ある Atom は複数の layer に同時に関係する。

```text
contract(CreateUser, UserCreated)
```

は static API、runtime event、semantic meaning のすべてに影響しうる。

## 6. Architecture Calculus

Architecture calculus は、architecture object 上の operation と law の関係を扱う。

### 定義 6.1 Architecture Operation

Architecture operation は、architecture object を別の architecture object へ写す
support-indexed partial morphism である。

```text
op : A ⇀ B
```

より明示的には、architecture operation は次のデータを持つ。

```text
ArchitectureOperation(A,B)
  = support
  + precondition
  + atom transformation
  + transition relation
  + invariant preservation claim
  + obstruction transport
  + conclusion
  + excluded readings
```

Atom configuration 上では、operation は partial map または relation として与えられる。

```text
op_C : C_A ⇀ C_B
```

precondition が満たされない場合、operation は単なる tag であり、theorem を持たない。
operation の数学的内容は、何を支え、何を保存し、どの obstruction をどう写すかによって決まる。

### 定義 6.2 Operation Kind

代表的な operation kind は次である。

```text
Preserve
Reflect
Repair
Extend
Synthesize
Translate
Forget
Refine
Abstract
Split
Merge
Isolate
Protect
Migrate
Reverse
Contract
```

### 定義 6.3 Preservation

`op : A -> B` が invariant family `Inv` を保存するとは、

```text
forall I in Inv, I(A) = I(B)
```

が成り立つことをいう。

### 定義 6.4 Improvement

ordered valuation `m` に対して、`op` が improvement であるとは、

```text
m(B) <= m(A)
```

が成り立つことをいう。

### 定義 6.5 Strict Repair

`op` が obstruction valuation `omega` に対する strict repair であるとは、

```text
omega(B) < omega(A)
```

が成り立つことをいう。

### 命題 6.6 Composition

`op : A -> B` と `q : B -> C` が invariant `I` を保存するなら、

```text
q . op : A -> C
```

も `I` を保存する。

同じ selected reading の下で identity と composition が定義できる operation family は、
部分圏として読める。

```text
id_A : A -> A
q . op : A -> C
```

associativity は、同じ selected observation を保つ範囲で読む。

### 命題 6.7 Repair Composition

`op` と `q` が同じ obstruction valuation を増やさず、少なくとも一方が strict repair なら、
合成も strict repair である。

```text
omega(B) <= omega(A)
omega(C) <  omega(B)
----------------------
omega(C) <  omega(A)
```

### 命題 6.8 Architecture Calculus Laws

Architecture calculus の law は、operation kind だけからは得られない。
それぞれの law は precondition、selected observation、witness family、exactness
assumption に相対化される。

```text
identity law
composition law
associativity under observation
refinement / abstraction compatibility
replacement equivalence
protection idempotence
runtime localization
migration compatibility
reverse involution
repair monotonicity
synthesis soundness
no-solution soundness
```

### 定理 6.9 Operation-Invariant Galois Correspondence

operation family と invariant family の間には弱いガロア的対応がある。

`InvAll` を考えうる invariant の集合、`OpAll` を考えうる operation の集合とする。
invariant family `I subset InvAll` と operation family `O subset OpAll` に対して、

```text
Ops(I) = { op in OpAll | forall i in I, op preserves i }
Inv(O) = { i in InvAll | forall op in O, op preserves i }
```

と定める。このとき、

```text
O subset Ops(I) iff I subset Inv(O)
```

が成り立つ。

したがって、より強い invariant family を要求すれば許される operation は減る。
また、より多くの operation を許せば、すべての operation に保存される invariant は減る。

```text
I1 subset I2 -> Ops(I2) subset Ops(I1)
O1 subset O2 -> Inv(O2) subset Inv(O1)
```

この対応により、設計原則は「どの operation を許すか」と「どの invariant を保存するか」の
二重の指定として読める。

## 7. Feature Extension

Feature extension は、Atom family を拡張して新しい capability、state、effect、contract を
追加する operation である。

### 定義 7.1 Extension

Architecture object `A` に feature `f` を追加して `B` を得る operation を書く。

```text
ext_f : A -> B
```

Atom level では、

```text
F_B = F_A union F_f
```

である。

### 定義 7.2 Split Extension

feature extension が split するとは、元の selected law を壊さず、追加された Atom が
独立した subconfiguration として読めることをいう。

```text
Split(ext_f)
```

より細かくは、feature extension には次の層がある。

```text
FeatureExtension
  = core embedding と feature view を持つ拡大そのもの

StaticSplitFeatureExtension
  = static relation と permitted-dependency policy に関する split evidence

FeatureViewSectionPackage
  = feature view が selected observation 上で feature を正しく読む evidence

SplitExtensionLiftingData
  = feature step が declared interface を通って持ち上がるための lifting evidence

SplitFeatureExtensionWithin
  = selected universe、observation、runtime / semantic coverage に相対化された split claim
```

AAT が問うのは、この拡張を一つの局所操作として見たとき、元 core が保存されるか、
feature 部分が selected observation 上で取り出せるか、どの invariant が破れるかである。

### 命題 7.3 Bridge-Edge Split Obstruction Transfer

candidate split boundary をまたぐ bridge edge が shared Atom support を運び、selected
obstruction axis がその bridge 上に support を持つなら、split readiness は明示的な
filler / lifting / boundary-operation evidence に相対化される。

```text
Bridge(e)
Support(e, shared atoms)
ObstructionAxis(o, e)
--------------------------------
SplitReadyWithoutTransfer
  -> FillerEvidence or LiftingEvidence or BoundaryOperationEvidence
```

したがって、その evidence がない場合、split は obstruction を除去したとは読めない。
obstruction は消えるのではなく、別の boundary へ transfer される可能性が残る。

これは bridge edge があるだけで transfer を theorem として結論する主張ではない。
結論できるのは、selected bridge support と selected obstruction support を仮定したとき、
split claim に必要な boundary evidence が何であるかである。

### 命題 7.4 Extension Preservation

`ext_f` が selected law universe `U` に対して split し、必要な interaction law を満たすなら、

```text
Lawful_U(A) -> Lawful_U(B)
```

が成り立つ。

### 例 7.5 Coupon Extension

coupon feature は、price calculation、discount policy、rounding、tax、payment、
event emission に Atom を追加する。static dependency が増えなくても、rounding law や
payment amount law が壊れるなら semantic obstruction が生じる。

### 定義 7.5 Architecture Extension Formula

Architecture Extension Formula は、feature extension の obstruction を分類する構造式である。

```text
ExtensionObstruction
  = inherited core obstruction
  + feature-local obstruction
  + interaction obstruction
  + lifting failure
  + filling failure
  + complexity transfer
  + residual coverage gap
```

これは互いに素な分解を無条件に主張しない。同じ witness が複数の分類を持つことがある。
式の役割は、obstruction の由来を説明可能にすることである。

### 予想 7.6 Boundary Holonomy

Feature extension `ext_f : A -> B` に対し、core と feature の接触部分を

```text
Boundary(A, f)
```

と書く。この boundary は、core 側 Atom と feature 側 Atom の間に現れる contract、
state read/write、effect ordering、authority / trust、runtime interaction、semantic
interpretation の mixed subconfiguration である。

十分な coverage、witness completeness、axis exactness、semantic / runtime observation
exactness があるなら、拡張後の obstruction は次の相対式で読めると予想する。

```text
kappa_U(B)
  =
kappa_U(A)
  + kappa_U(f)
  + Hol_U(Boundary(A, f))
```

ここで `Hol_U(Boundary(A, f))` は core と feature の境界を横断する mixed diagram の
非可換性である。したがって、core も feature-local part も flat であるのに `B` が flat で
ない場合、残りの witness は boundary holonomy として局在化できる、という読みになる。

これは現在 conjecture であり、証明済み theorem ではない。既存 Lean API が持つのは
feature-extension attribution、diagram filling、selected observation refutation、そして
monodromy measurement の minimal guardrail である。`Boundary Holonomy` は、これらを束ねる
将来の exactness / coverage 仮定付き theorem candidate として扱う。

## 8. Repair

Repair は obstruction valuation を減らす operation である。

### 定義 8.1 Repair Step

`r : A -> B` が repair step であるとは、selected obstruction valuation `omega` に対して

```text
omega(B) <= omega(A)
```

が成り立つことをいう。

strict repair なら `<` が成り立つ。

Repair step は次のデータを持つ。

```text
RepairStep
  = source
  + target
  + selected obstruction measure
  + decrease proof
  + preserved invariant family
  + possible transferred obstruction
```

repair は総合的改善を意味しない。ある selected obstruction が減っても、別の axis へ
complexity が転送されることがある。

### 定義 8.2 Repair Strategy

Repair strategy は repair step の列である。

```text
A_0 -> A_1 -> ... -> A_n
```

### 命題 8.3 Termination

`omega` の値域が well-founded order を持ち、各 step が strict repair なら、
repair strategy は無限下降列を持たない。

### 命題 8.4 Repair Soundness

`omega(A_n) = 0` かつ `omega` が sound なら、

```text
Lawful_U(A_n)
```

である。

### 定義 8.5 Complexity Transfer

Complexity transfer は、ある axis の obstruction が減った一方で、別の axis に
obstruction、cost、coupling、semantic mismatch が移る現象である。

```text
omega_x(B) < omega_x(A)
omega_y(B) > omega_y(A)
```

AAT は obstruction の free elimination を無条件に認めない。repair theorem は少なくとも
次を指定する。

```text
減らす witness family
減らす measure
保存する invariant family
増加を主張しない axis
転送されうる obstruction
```

## 9. Synthesis

Synthesis は law universe を満たす architecture object を構成する operation である。

### 定義 9.1 Synthesis Problem

Synthesis problem は次の組である。

```text
P = (F_0, U, Cstr)
```

ここで、

```text
F_0   : required atoms
U     : law universe
Cstr  : additional constraints
```

### 定義 9.2 Solution

Solution は Atom family `F` と architecture object `A` であり、

```text
F_0 subset F
F => A
Lawful_U(A)
Cstr(A)
```

を満たす。

### 定義 9.3 No-Solution Certificate

No-solution certificate は、`F_0` と `Cstr` の下で `Lawful_U` を満たす object が存在しない
ことを示す obstruction family である。

no-solution soundness を主張するには、探索する Atom family、制約言語、decision procedure、
coverage、exactness が明示されている必要がある。単に candidate が見つからないことは、
no-solution certificate ではない。

## 10. Path

Architecture path は operation の列である。

### 定義 10.1 Architecture Path

```text
p : A_0 -> A_n
p = (op_1, op_2, ..., op_n)
```

ただし、

```text
op_i : A_{i-1} -> A_i
```

である。

### 定義 10.2 Path Observation

path に対する selected quantity は、各 step の signature 変化として読める。

```text
Sig(A_0), Sig(A_1), ..., Sig(A_n)
```

異なる path が同じ target object に到達しても、途中で保存される invariant、
導入される obstruction、signature trajectory は異なりうる。

```text
p, q : A -> B
target(p) = target(q)
SigTrajectory(p) != SigTrajectory(q)
```

### 定義 10.3 Path Cost

path cost は、operation cost、obstruction change、risk weight、complexity change などの
集約として定義できる。

```text
Cost(p) = sum_i cost(op_i)
```

## 11. Homotopy

Homotopy は、異なる operation 列が同じ architecture transformation として読めることを表す。

### 定義 11.1 Path Homotopy

二つの path

```text
p, q : A -> B
```

が homotopic であるとは、選ばれた generator によって相互に変形できることをいう。

```text
p ~ q
```

代表的 generator は次である。

```text
independent square
same contract replacement
repair filler
identity insertion / deletion
associativity reassociation
```

### 命題 11.2 Homotopy Preservation

homotopy generator が selected observation を保存するなら、homotopic path は同じ
selected observation を持つ。

```text
p ~ q -> Obs(p) = Obs(q)
```

逆向きは一般には成り立たない。同じ observation を持つ二つの path が、選ばれた
generator で変形できるとは限らない。

### 命題 11.3 Signature Trajectory Refutation

selected signature trajectory `T` が homotopy generator によって保存されるなら、
homotopic path は同じ trajectory を持つ。

```text
p ~ q
----------------
T(p) = T(q)
```

従って反対向きに、

```text
T(p) != T(q)
----------------
not (p ~ q)
```

が得られる。ただしこれは `T` を保存する selected homotopy に対する refutation である。
同じ endpoint を持つ path が一般に非同値であること、または operation が非可換であることを
無条件に主張しない。endpoint delta と trajectory disagreement は別の reading である。

### 例 11.4 Independent Square

二つの feature extension `f` と `g` が独立なら、

```text
A --f--> A_f
|        |
g        g
v        v
A_g --f--> A_fg
```

は可換 square を作り、`f` の後に `g` を行う path と `g` の後に `f` を行う path は
homotopic に読める。

## 12. Architecture Analytic Continuation and Monodromy

Flatness は object `A` 上の selected obstruction が消えていることを読む。一方で、operation
path を通って `A` から同じ target へ到達する二つの方法は、途中の selected signature
trajectory や continuation trace を変えることがある。これを architecture analytic
continuation として読む。

### 定義 12.1 Selected Continuation

Signature axis `x` と operation path `p : A -> B` に対し、`p` に沿って selected observation、
signature witness、state transition、effect trace、authority trace などを継続して読む写像を

```text
Cont_x(p)
```

と書く。`Cont_x` は selected ArchMap / LawPolicy / coverage universe に相対化された bounded
reading であり、完全な実行意味論や全 source extraction を意味しない。

### 定義 12.2 Monodromy Defect

二つの operation `f, g` が作る square に対し、

```text
p = g . f
q = f . g
```

と置く。axis `x` 上の monodromy defect は次である。

```text
mu_x(f,g;A)
  = d_x(Cont_x(p), Cont_x(q))
```

`d_x` は boolean mismatch、count、edit distance、semantic distance、state transition
distance、effect replay mismatch count、authorization mismatch count など、axis ごとの bounded
distance でよい。重要なのは、`mu_x > 0` を selected observation difference として読める
zero-reflecting / positive-witness boundary を持つことである。

### 定義 12.3 Architecture Monodromy Index

Finite measured square family `S` と selected axes `X` に対し、

```text
AMI_X(A)
  = sum_{sigma in S}
    sum_{x in X}
      w_{sigma,x} * mu_x(sigma)
```

と置く。`AMI_X(A)` は architecture quality の単一スコアではない。review prioritization の
ための aggregate reading であり、selected square family、selected axis family、weight policy、
coverage boundary、exactness assumption、top contributors を必ず伴う。

### 命題 12.4 Bounded Aggregate Soundness

重みが nonnegative で、positive-weight entry だけを local reading の対象にし、各 `mu_x` が
selected observation に対して sound であるなら、

```text
AMI_X(A) = 0
-----------------------------
forall positive-weight sigma,x,
  mu_x(sigma) = 0
```

が成り立つ。Lean では `MonodromyMeasurement.weightedAggregate` と
`localZero_of_weightedAggregate_zero` がこの bounded 方向を形式化する。zero-weight entry、
unmeasured square、coverage gap を zero と読むことはできない。

### 命題 12.5 Path-Monodromy Obstruction Soundness

`mu_x(sigma) > 0` なら、`Cont_x(p) != Cont_x(q)` である。さらに selected homotopy generator が
`Cont_x` を保存するなら、

```text
not (p ~ q)
```

が得られる。diagram filling API と接続すると、同じ selected observation difference は
non-fillability witness を与える。

Lean では `AxisDefect.observationDiff_of_nonzero`、
`nonzero_refutes_selectedPathHomotopy`、`nonzero_nonFillabilityWitnessFor` がこの bounded
soundness 部分を担う。これは path-monodromy obstruction theorem の安全な片方向であり、
covered operation complex 全体の completeness、all axes semantic completeness、extractor
completeness、ArchSig measurement correctness in the wild は主張しない。

### 例 12.6 Coupon / Tax / Rounding

`discount` と `tax` が粗い static graph では独立に見えても、selected semantic axis では

```text
round(tax(discount(subtotal)))
round(discount(tax(subtotal)))
```

が異なる場合がある。このとき final dependency graph は同じでも、semantic continuation は
同じ位置へ戻らない。

```text
mu_semantic(discount,tax;Checkout) > 0
```

であり、selected homotopy refutation、non-fillability witness、review focus cue として読める。
この例は ArchSig が計測できる diagnosis の典型であるが、ArchSig は theorem prover ではない。
report は measured witness、missing evidence、coverage gap、non-conclusion を運ぶ。

## 13. Diagram Filling

Diagram filling は、部分的に与えられた architecture diagram を完成できるかを問う。

### 定義 13.1 Diagram

Diagram `D` は architecture object と operation からなる図式である。

```text
D : Shape -> Obj
```

### 定義 13.2 Filler

filler は、欠けた object または operation を補い、図式を可換にするデータである。

```text
Fill(D)
```

### 定義 13.3 Non-Fillability

`D` が fill できないとは、要求される可換性や law を同時に満たす filler が存在しないことをいう。

```text
not exists fill, Fill(D, fill)
```

### 命題 13.4 Obstruction as Non-Fillability

ある law failure が diagram の非可換性として表されるなら、その obstruction は
non-fillability witness として読める。

```text
Obs(D_lhs) != Obs(D_rhs)
------------------------
no filler for D
```

任意の split failure が自動的に diagram filling failure へ還元されるわけではない。
還元するには、selected diagram family、lifting data、filling condition が必要である。

### 定理 13.5 Geometry of AAT

Atom から生成された architecture object 上で、law、obstruction、operation、path、
homotopy、diagram filling は一つの幾何を形成する。flatness は obstruction zero、
curvature は law failure の valuation、homotopy は operation path の同値、filling は
lawful completion の存在として読まれる。
