# Copying coalgebra、全Hom、無限totality

## 定理 N2.1 — Cartesian構造の係数化

集合 `X` に

```math
C_R(X)=\bigoplus_{x\in X}Re_x,\qquad
\Delta(e_x)=e_x\otimes e_x,\quad \epsilon(e_x)=1
```

を与える。これはcocommutative counital coalgebraである。関数 `f:X→Y` には `C_R(f)(e_x)=e_{f(x)}` を対応させる。basis上の検査でcoalgebraの三公理、関手の単位・合成が従う。

`e_(x,y)↦e_x⊗e_y` は `C_R(X×Y)≅C_R(X)⊗C_R(Y)`、`e_*↦1` は `C_R(1)≅R` を与える。ここでtensor積はcocommutative counital coalgebra圏の直積である。実際、射 `f:D→A,g:D→B` から `(f⊗g)Δ_D` を作れる。射影は `id⊗ε_B` と `ε_A⊗id`。counit式で二つの合成が `f,g` に戻る。任意の射 `h:D→A⊗B` はcoalgebra式によりその二射影からこの式で回復する。`R` への唯一の射はcounitである。

有限arity operationをこの関手で運ぶ。変数の重複は `Δ`、不使用は `ε` を用いるので、全cartesian termの評価が運ばれる。term帰納法で `C_R(τ_A)=τ_{C_R(A)}`。relationとpartial domainは対応する部分集合のcopying coalgebra包含で表し、射の保存はその包含への因子分解で表す。選択値は `R→C_R(X)` とする。

論理的Lawは、後述する `ΔX` のsheaf上で局所的に解釈する。これはmoduleの任意元やglobal sectionの集合上で同じ古典論理式を再評価する操作ではない。原始有限論理式 `φ` のnative真理集合を `T_φ⊆∏ X_i` とすると、解釈は部分sheaf `ΔT_φ⊆∏ΔX_i` である。このことは式に関する帰納法で証明できる。有限tupleは局所的にnative定数tupleなので、論理結合はその局所片で集合の結合に一致する。存在量化ではnative witnessをその片に置き、全称量化は全native定数で検査すれば任意の局所定数sectionにも成り立つ。否定はnative真理集合の補集合となる。従って成立するnative Lawはこの局所解釈で成立する。空scheme上では内部真理は退化し、native充足の反映は主張しない。存在だけのLawに選択sectionは付け加えない。

## 定理 N2.2 — Coalgebra Homの分類

任意環 `R`、集合 `X,Y` についてcoalgebra射は、各 `x` ごとの有限support族 `(a_xy)_y` で

```math
a_{xy}^2=a_{xy},\quad a_{xy}a_{xz}=0\ (y\ne z),\quad
\sum_y a_{xy}=1
```

を満たすものと全単射である。

**証明。** 線形射の各 `e_x` の像は直和の元なので有限和 `Σ_y a_xy e_y`。`Δf(e_x)=(f⊗f)Δ(e_x)` の `(y,y)` 成分と `(y,z)` 成分を比較すると冪等性と直交性、counit保存から和1を得る。逆にこれらの式は全coalgebra式を与える。basis上の等式なのでこの対応は単射でもある。□

有限冪等元分割は `Spec R` の有限clopen分割である。任意の `Spec R→⨿_Y Spec R` はquasi-compactnessから有限個の成分にしか交わらず、各成分上では `R`-射が一意である。従って

```math
\operatorname{Coalg}_R(C_R(X),C_R(Y))
\cong \operatorname{Hom}_R(\coprod_X\operatorname{Spec}R,
                            \coprod_Y\operatorname{Spec}R).
```

係数環の射は冪等元の各係数を送る。合成は

```math
c_{xz}=\sum_y a_{xy}b_{yz}.
```

有限和の式からscheme側のclopen分割の細分化と一致する。従って同型は対象、射、係数変更について自然である。

### 系 N2.3 — Native回復と零環

`R≠0` がconnectedなら、各行の非零係数はちょうど一つで値1。従って全coalgebra Homは `Set(X,Y)` に等しい。これを各sortに適用し保存式を読むと N1 の全model Homも回復する。

全可換環にわたるscalar extensionと可換な射族は、`ℤ→R` によって `ℤ` 成分から決まる。`ℤ` はconnectedな非零環なので、それは唯一の集合写像に由来する。逆に集合写像は全環にわたるこの族を与える。

零環では全 `C_0(X)=0`、全 `⨿_X Spec 0=∅`。全Homはsingletonであり、`X≠∅,Y=∅` でも同じである。冪等元分割の式は空和 `0=1` を許すため、この場合も N2.2 と整合する。零環一個の成分からnative射は回復できない。

### 定理 N2.4 — Nilpotent thickeningでの一意なlift

nilpotent ideal `J⊆R` について、上のHomの `R→R/J` によるmapは全単射である。

**証明。** 冪等元はnilpotent idealを法として一意にliftする。存在は、lift `a` の誤差 `a²-a` に対し `a↦3a²-2a³` で誤差のideal冪を倍にし、有限回で誤差を零にする。一意性は二つの可換冪等元 `e,f` の差がnilpotentなら、冪等元 `e(1-f)` と `f(1-e)` がnilpotentなので零、従って `e=f` であることによる。各行の有限個の冪等元をliftする。その異なる二つの積は零をliftする冪等元なので零。和は1をliftする冪等元なので1。零係数は一意に零にliftするため、新しいsupportを必要としない。□

この証明は局所nilpotent idealにも成り立つ。split構造間のoperation保存については、両辺が同じ集合間のcoalgebra射であることと一意性から、法 `J` で等しい両辺が `R` 上でも等しくなる。relationの部分copying coalgebraへの因子分解も、禁止された係数が零をliftすることから持ち上がる。従って離散的な全Homの接方向は零である。quantity `q:{*}→R` には `k[ε]/ε²` 上で `0,ε` があるので、量の方向とは異なる。

## 定理 N3.1 — 各入力の有限supportを持つ全表示

profileは `S=(S_x)_(x∈X)`、各 `S_x⊆Y` は有限集合とする。全profileの集合は点ごとの和集合で有向である。

```math
B_S=k[a_{xy}\mid x\in X,y\in S_x]/
(a_{xy}^2-a_{xy},\ a_{xy}a_{xz}\ (y\ne z),\ \sum_{y\in S_x}a_{xy}-1).
```

`H_S=Spec B_S` はそのprofileに収まる全Homを表す。`S⊆T` では新座標を零に送る全射 `B_T→B_S` があり、`H_S↪H_T` は閉埋込みである。任意環の任意Homの各行は有限supportを持つから

```math
\underset{S}{\operatorname{colim}}\ H_S(R)
\cong\operatorname{Coalg}_R(C_R(X),C_R(Y)).
```

二つの表示の等しさは和集合profileでの座標の等しさで判定できるので単射でもある。ここでcolimitはまずaffine test上の関手として取る。非affine testにはそのsheafificationを用い、全体を無条件に通常のschemeと呼ばない。

`X→Y` のprofile `S` と `Y→Z` のprofile `T` の合成profileは

```math
U_x=\bigcup_{y\in S_x}T_y.
```

これは有限であり、合成係数は N2.2 の有限和。直交性・和1を展開すれば `H_S×H_T→H_U` を得る。式の有限和の結合則が全表示上の合成則になる。恒等は `S_x={x}` であり、このchartの環は `k`、従って `H_S=Spec k`。

## N3.2 — 三つの反例とG-124の同じquery

**全false行。** `Y` を無限とする。Boolean表の各座標を `b_xy` とし、totalな行はちょうど一つがtrueである。固定した行の全false表はtotalでない。しかし任意の有限座標集合について、その外の一つだけをtrueにしたtotal行が同じ制限を持つ。従ってtotalな全行が満たす有限Boolean query上の閉条件をどれだけ同時に課しても、全false行を除けない。これは有限離散空間の積位相においてtotalな行の集合が閉でないことの直接証明でもある。

**共通の有限出力。** `id:ℕ→ℕ` の各行のsupportはsingletonだが、その和集合は `ℕ`。全入力で共通の有限出力集合を要求するとこの射を失う。

**モデルごとのsupportと一様support。** `g:{*}→ℕ`、`f:ℕ→{0,1}` を取り、`f(g(*))` を評価する。指定したモデルでは `g(*)=n` と `f(n)` の二つの値で決まる。一方、あらかじめ固定した有限graph queryの組に現れない `n` を選び、二つの `g` をともに `n`、二つの `f` を `n` 以外では同じ、`n` で0と1にすれば、全指定queryは一致するが評価は異なる。従って一様な有限段階への因子分解はない。

G-124の `IndependentCarrierGraphReadings` のqueryは `edge(S,T,x,y)`。`IsTyped` は非activeな型の行をfalse、`IsTotal` はactiveな型で `∀x ∃!y` を要求する。N2.3 のconnected環上の係数をBoolean値0/1と読むと、まさに同じgraphとなる。typedなtotal表のassemblyはその一意の `y` を返すため、graph化との二方向の合成は恒等である。

同ファイルの `compose_finite_support` で、activeなcomposite query `edge(α,γ,x,z)` に使うsupportは、**与えた**最初の表から組み立てた中間点 `y` に対する `edge(α,β,x,y)` と `edge(β,γ,y,z)` の各一個である。別のtotal表がこの二queryで一致すれば、最初のtrue queryと一意性から中間点が同じになり、二つ目がcomposite値を決める。非active queryは空supportで足りる。これは上のモデルごとの二query証明と同じであり、一様なquery集合の存在を述べていない。
