# Descent、係数的実現、通常の代数性

## B1 — Copyingと係数的実現

### 定義 B1.1 — 構造のstack

fppf topologyを固定する。scheme `T` 上のcopying構造は、N1の各sortにquasi-coherent cocommutative counital coalgebraを割り当て、fppf局所的に `⊕_X O_T` のbasisを複製する形になるものとする。relationとpartial domainには局所的にbasisの部分集合を張る部分coalgebra、operationには実際のcoalgebra射、選択値にはgroup-like sectionを割り当てる。sort、domain、relationの局所split性は宣言されたデータについて要求する。個々の射が大域的に一個の集合写像であるとは要求しない。

全structure-preserving射のfibered categoryを `B_copy^all`、その各fiberの最大部分groupoidを `B_copy` とする。splitな対象を与える被覆と、その上の同型cocycleを持つ降下形を全て含める。basisそのものを大域的なmarkingとして要求しない。

### 定理 B1.2 — 全Homと対象のdescent

`B_copy` はstackであり、`B_copy^all` の全Homもsheafである。

**証明。** fppf被覆とoverlap上の同型cocycleを与える。quasi-coherent moduleとそのすべての射はfpqc、従ってfppfでeffective descentを持つ（[Stacks 023T](https://stacks.math.columbia.edu/tag/023T)）。これを各sortとrelation/domainのmoduleに適用する。tensor積のbase change同型により `Δ,ε`、operation、domain包含のmapも降下する。faithfully flatなpullbackはmapの等式を検出するのでcoalgebra公理、operation式、Law式、単射性が降下する。局所split性は、元の被覆とその上のsplit被覆を合成して得られる。

N1・N2の一階論理式Lawは、降下したsort・relation・domainのfppf sheafにおける内部論理で解釈する。その充足は被覆上で検査できる。特に存在量化は被覆上のwitness、全称量化と含意は全base change後のsectionで解釈されるため、元の被覆へのpullbackとその細分化での充足から大域充足が従う。この局所性を、単にmodule射の等式を検出する議論と分けて用いる。

同じ議論を二つの構造間の全sort mapに適用すれば、局所mapの互換族が一意に降下し、その保存式も降下する。逆射を持つmapは逆射も一意に降下する。よって対象と全Homについてdescentが成立する。無限個のsort・mapは各々に同じ議論を適用する。無限rankのmoduleをZariski局所有限自由と結論する段階はない。□

### 定義 B1.3 — 原始係数構造からのσ

native module `M` とその加法・scalar作用を持つsortには `σ_M(R)=M⊗_k R`、scalar sortには `σ_k(R)=R` を与える。指定された多重線形operationはpure tensor上で係数を掛ける式で延長する。指定有限式は帰納的に延長する。moduleの関係式はtensorの普遍性、式の等式はその証明を同じ演算に解釈することで保たれる。

`B_σ` はこれらの原始係数宣言の実現と同型からなるfppf stackである。固定moduleのfamilyを使う場合はその局所同型降下形を含める。module自体を変動させる宣言では全指定module実現を含める。どちらもcategoryを先に定義し、quasi-coherent descentでstack条件を証明する。任意native関数について多項式延長を仮定せず、graphを保持するか C3 の拡張点を追加してから係数式を解釈する。

### 定理 B1.4 — Nativeとの比較

`Δ|M|(R)` の点は有限直交冪等元分割 `(e_i)` とnative元 `(m_i)` で表される。その像を

```math
\iota_R((e_i,m_i)_i)=\sum_i e_i(m_i\otimes1)\in M\otimes_kR
```

とする。同じ値の分割の併合や零係数の追加に依存せず、環射と可換である。指定された多重線形operationとは、積を展開して冪等元分割を共通細分化することで可換になる。有限式も帰納法で同じである。native定数pointは `m↦m⊗1`、基点 `R=k` では `m` に戻る。

nativeの係数作用を保つ全Homは実際の `k` 線形mapと指定operation保存である。各 `h:M→N` は `h⊗id_R` を定める。逆にscalar extensionと可換な `R` 線形mapの族は `k` 成分で決まり、`m⊗r↦h_k(m)⊗r` だからこの全Homを回復する。primitive operation保存もpure tensorで同値となる。固定基点の対象を読むと `M⊗k≅M` で同じ対象に戻る。

ただし非連結 `k` では `Δ|M|(k)` にnative定数以外の点がある。例えば `k=k₁×k₂`、冪等元 `(1,0),(0,1)` で二つの異なるnative定数を貼り合わせられる。`ι_k` はそれらを `M` の元へ送るが単射とは限らない。全copying Homを基点一個でnative Homと同定するのは N2.3 のconnected非零条件の下だけである。

`R=k[ε]/ε²` では `M⊗R≅M⊕εM`。`m` 上のliftは `m+εv` として `v∈M` 全てを持つ。一方、同じnative集合のcopying点は N2.4 により一意にliftする。この二つの係数familyは異なる。

点ごとのLawとfamily全体のLawも区別する。`F_p` のnative scalar上では `x^p=x` が全点で成立するが、`F_p[t]` の普遍点では成立しない。原始**式の証明**から延長できるLawと、native値を検査しただけのLawを同じにしない。後者の全延長とcoherenceは C3–C5 が分類する。

### 定理 B1.5 — 局所split構造の一次変形

`R→R/J` がnilpotent thickeningで、`A,B` が既に `R` 上にある局所split copying構造なら、その全Homの還元は全単射である。実際、各sortの二つのcoalgebraをsplitするfppf被覆上で N2.4 を使えば、還元後のmapは一意にliftする。被覆のoverlap上では同じmapを還元する二つのliftが一意性により等しいので、B1.2でglueできる。operation保存は二つの合成が同じ還元を持つこと、relation/domain保存はそれらの包含と同じ可換式から従う。有限arityの検査には関係する有限個のsplit被覆の共通細分化で足りる。逆射も一意にliftする。

`R=k[ε]/ε²` では `k→R` があるため、任意の `k` 上の構造 `S` に標準lift `S_R` が存在する。還元同型 `T⊗_R k≅S` を持つ任意deformation `T` は、上の全Homの結果で一意に `S_R` と同型になる。還元同型を固定した変形groupoidはcontractible、すなわちcopying構造には非零の一次変形がない。ここでは存在する二対象をsplitする被覆を用いたので、`R/J` 上の任意fppf被覆がそのままliftすると仮定していない。`σ` の `m+εv` という量の変形との違いが対象についても明確になる。

## 定理 B2 — 相対Specと独立quantityの表現

quantity domainとLaw入力を構造の宣言に含める。固定構造では任意集合をこのsortに置ける。構造を変動させるときは、それらのsort mapとLawの有限式も原始宣言に含める。任意の外在的集合操作が自動的にdescentと可換であるとは仮定しない。

`B_copy` のsplit chart上で A1 の `Q,ρ,I` を作る。残差map `ρ_ℓ:C(E_ℓ)→Sym Q` の構成はbasisに依存しない。構造termは指定coalgebra射の合成、quantity評価は `C(D_j)→Q→Sym Q`、定数 `c` は `cε`、二つの値の積は `m(f⊗g)Δ`、和と差は線形mapの和と差である。従ってcoalgebraの `Δ,ε` と構造射を保つmapについて、構文帰納法で `ρ_ℓ` の可換性が従う。

非連結なoverlap上でもこの計算を使う。N2.2の一入力に対する有限冪等元分割 `(e_y)` は、積では `e_y e_z=0`（`y≠z`）、定数では `Σe_y=1` により同じ残差を運ぶ。全入力共通の有限分割を選ぶ必要はない。従って構造同型は `Q` と `ρ` の同型を与え、そのcocycleは原始sort mapのcocycleとterm帰納法から従う。B1.2によって `Q` と各 `ρ` が降下し、`I` は普遍代数内の全 `ρ` の像が生成するquasi-coherent idealとして大域的に作れる。

ここで無限個の像を使ってもよい。idealは乗法map

```math
\bigoplus_\ell(\operatorname{Sym}Q\otimes C(E_\ell))
\longrightarrow\operatorname{Sym}Q
```

の像である。quasi-coherent moduleの直和、tensor、像（このmapのcokernelへの射のkernel）から構成できるためquasi-coherentである。

`M` を「構造と、その上の独立なlawful quantity」のgroupoidとして定義する。任意 `T→B_copy` とtest scheme `f:T'→T` を取る。まず構造をsplitするfppf被覆上でA1を適用する。各quantity domainの全関数はその自由moduleからの線形mapに対応し、lawfulnessは全 `ρ_ℓ` を消す条件に対応する。この同定は上のcoalgebraの計算により全overlapで可換である。B1.2のQC射descentから、独立quantityは一意な `f^*Q_T→O_(T')` へ降下し、残差の零性も忠実平坦に検出される。逆にこの線形mapをsplit被覆へ引き戻し、basisの値を読めば元のquantityを回収する。

次にZariski affine open上でA2のSymの普遍性と商環の普遍性を適用する。この段階の `Q_T` は任意のQC moduleでよく、Zariski局所でsplitしている必要はない。重なりで同じ線形mapを制限することにより、全test schemeに自然な同型

```math
M\times_{B_{\rm copy}}T
\cong\operatorname{Spec}_T(\operatorname{Sym}Q_T/I_T).
```

従って `M=Spec_(B_copy)(Sym Q/I)` は基底stackに相対的にaffineである。`B_copy` 自体の代数性をこの結論に含めない。左辺のquantityを右辺のscheme点として定義してから表現性を言う循環はない。

同じ証明は、原始係数宣言からQC module `Q` と有限式による `ρ` が生成される各 `B_σ` に適用できる。線形quantityなら A2、copying domainなら A1、両者の混合なら直和とそれらのLawを使う。

任意の基礎環変更で、Symとtensorの普遍性は

```math
(\operatorname{Sym}_kQ)\otimes_k k'
\cong\operatorname{Sym}_{k'}(Q\otimes_k k')
```

を与える。`ρ` の各生成元は原始式の係数を送った同じ残差へ移る。従って新idealは旧idealの**extended ideal**であり、商のbase changeはtensorの右完全性から成立する。idealそのもののtensorを部分加群と同定するためのflatnessは用いない。構造同型、宣言のcontext制限、term substitutionについても生成元の同じ計算が自然性を与える。

## B3 — 構造射、quantity引戻し、対応空間

構造保存射 `h:S→S'` からquantity domainのmap `d_j:D_j(S)→D_j(S')` と、Law入力のmap `e_ℓ:E_ℓ(S)→E_ℓ(S')` が指定sort mapとして生成され、Law式の評価を可換にするとする。`z_(j,d)↦z_(j,d_j(d))` が `A_S→A_S'` を定める。term帰納法により `r_(ℓ,e)` の像は対応する `r'_(ℓ,e_ℓ(e))`。従って `I_S` を `I_S'` に送り、

```math
M_{S'}\longrightarrow M_S,\qquad q'\longmapsto h^*q'
```

を得る。Lawの導出が複数式を使う場合は、その残差がtarget idealに属する同じ有限導出でよい。

Law入力を運べなくてもnative射 `h` を意味圏から削らない。quantity domainだけを運べるなら、両方の量を残し

```math
Z_h\subseteq M_S\times M_{S'},\qquad q_j(d)=q'_j(d_j(d))
```

を全 `j,d` の等式で切り出す。これは閉対応空間であり、`M_S'` への射影は `h^*q'` がsourceのLawを満たすlocusを表す。全target quantityからの射のgraphになることと、全残差の像がtarget idealで零であることは、targetの普遍quantityに代入すれば同値である。

**補集合Lawの反例。** 一元集合 `S={a}` に `P=∅`、`S'={b}` に `P'={b}` を付ける。唯一のmapはrelation保存である。quantityは各集合のscalar値、Lawは「`P` の補集合上で零」。sourceは `q(a)=0` を課すがtargetは無条件。`M_S=Spec k`、`M_S'=A¹_k`、対応はtarget座標 `t=0` である。`k≠0` ならtargetの普遍値 `t` を引き戻すmapはsourceのLawを満たさない。原始relation保存だけでは補集合Lawの保存は得られない。

## B4 — Sheafificationとscalar extensionの仮定

使用する交換はQC moduleのpullbackについてである。affine上でmodule `N` が与えるsheafを `Ñ` とし、環射 `B→B'`、`g:Spec B'→Spec B` を取る。principal openごとに

```math
B'_{g(s)}\otimes_{B_s}N_s
\cong (B'\otimes_BN)_{g(s)}
```

をpure tensorで作れる。両側のmapは分数の普遍性で互いに逆。ただし逆像 `D(g(s))` だけがtargetの基底になるとは限らない。全target点 `q∈Spec B'`、`p=g⁻¹(q)` についてstalkを取ると

```math
B'_q\otimes_{B_p}N_p\cong B'_q\otimes_BN
\cong (B'\otimes_BN)_q.
```

第一の同型は `B\setminus p` の像が `B'_q` でunitであることによる。この自然mapは全stalkで同型なので、sheafの同型

```math
g^*\widetilde N\cong\widetilde{B'\otimes_BN}
```

を得る。これは任意環射で成立する。任意openで「sectionを先に取りtensorする」と同じだとは主張しない。任意openの係数はsheafのsectionとして取る。

係数変更presheafをまず作る場合も、tensorはsheaf圏ではpresheaf tensorのsheafificationであり、sheafificationの普遍性と上のstalkの計算で同じ結果になる。Law idealは像、商はcokernelとしてsheaf化し、pullback後はextended idealを使う。flatnessが必要な既存APIに比較するときには、その仮定を満たす係数変更に限定して確認する。この論証は任意のsiteや任意のobservable presheafのsheaf性を無条件に宣言するものではない。

## 定理 D1 — Dualityから有限frameへ

module sort `M` に `N`、evaluation `N⊗M→R`、coevaluation `R→M⊗N` と二つのsnake等式が原始dataとしてあるとする。`coev(1)=Σ_(i=1)^r m_i⊗n_i` と書くとsnake式は

```math
m=\sum_i m_i\operatorname{ev}(n_i,m).
```

従って `R^r→M` と `M→R^r` の合成は `id_M`。`M` は有限自由moduleの直和因子、すなわち有限projectiveである。逆に有限dual basisがevaluation・coevaluationを与える（[Stacks 0FNJ](https://stacks.math.columbia.edu/tag/0FNJ)）。局所化して行列の可逆minorを選べば有限局所自由であり、rankは局所定数である（[Stacks 00NX](https://stacks.math.columbia.edu/tag/00NX)）。

有限個の基本sortについて局所frameを同時に選べる。各rankは有限で、全rank vectorの開閉成分を残す。有限tensor、有限直和、dualはfinite projectiveを保ち、frameの遷移はそれぞれtensor、block sum、逆転置である。指定retractはfinite projective `L` 上の冪等行列 `e²=e` として表せ、その像は直和因子である。可変のretractもこの多項式式でparametrizeし、像のrank成分ごとに同じframe構成を適用する。

有限projective `A,B` のoperation `A→B` は `Hom(A,B)` の元であり、これは `A^∨⊗B`。従ってoperationを加える空間は `Spec Sym(Hom(A,B)^∨)` で相対affine。任意個のoperationはこの双対の直和のSymで表す。Lawの差がfinite projective `L` のsectionなら、全 `λ∈L^∨` による `λ(residual)=0` でその零点を切り出せる。dual basisによりこれは元のsectionの零性と同値である。任意個のLawはそれらの生成idealで同時に課せる。

tensor式の入力と出力、有限直和の射入・射影、dualのevaluation・coevaluation、retractの `i,p,pi=id` はいずれもこの同じ有限projective Homと多項式Lawに入る。したがって各生成規則ごとに相対affine性が証明された。

## 定理 D2 — GL作用、商、schemeへの接着

固定rank成分でbasis付き宣言の解をaffine scheme `X` とする。基底変更の群は有限積 `G=∏ GL_(n_s)`。operationに対する作用は出力基底の逆変換と入力基底のtensor変換であり、原始Lawの等式を保つ。実現から全frameの `G` torsorを作り、その上の成分から `X` へのequivariant mapを得る。逆にこのmapを持つtorsor上の自由moduleとoperationはB1.2で降下する。二つの構成はframeの評価とdescentの一意性で互いに準逆であり、全同型も回復する。

`G` はsmooth affineで、`X` はscheme。action groupoidの二射影はsmoothであるから商stack `[X/G]` はalgebraic stackである（[Stacks 06PI](https://stacks.math.columbia.edu/tag/06PI)）。`X` の有限型性は使わない。

markingが全射 `q:R^m→Q` なら `u q=q` から `u=id` となる。しかしtrivial inertiaだけからschemeとは結論しない。さらにmarkingの一部が基底となるopen chart、その重なりのopen局所化、逆変換とcocycleを構成できれば、schemeをglueできる。これを P2 で実際に行う。trivial inertiaとこのopen overlapの両方が使われる。

## D3 — 通常の代数性を持たない二つのfamily

**独立なline quotient。** `k≠0` とする。可算個のsortごとに `R²↠L_i`、rank1の条件を置き、sort間のLawを置かない。P2の一sort版は `P¹` を与えるので、意味関手は `X=∏_(i∈N) P¹_k` である。以下ではこの関手がalgebraic spaceであると仮定し、[Stacks 078E](https://stacks.math.columbia.edu/tag/078E)の反証に必要な前提も構成する。

まず任意affine test `Spec R→X×X` について、対角の引戻しは各factorでの二射の一致条件を同時に課す。`P¹_k` は分離的なので、各条件はideal `I_i⊆R` による閉部分schemeであり、全条件は `Spec(R/Σ_i I_i)` である。従って `Δ_X` は閉埋込みで、`X` は分離的である。

次のaffine schemeから各factorへ、全射列 `(x_i,y_i)` を読む射を作る：

```math
Z=\operatorname{Spec}
k[x_i,y_i,a_i,b_i\mid i\in\mathbb N]/
(a_ix_i+b_iy_i-1\mid i\in\mathbb N)\longrightarrow X.
```

任意の体 `K/k` と `X(K)` の点について、各line quotientのbasisを選べば非零の対 `(x_i,y_i)` が得られ、`a_ix_i+b_iy_i=1` を解ける。従って `Z(K)→X(K)` は全射。algebraic spaceの各位相点はある体値点で表せるため、`|Z|→|X|` も全射である。affine schemeのquasi-compact性と連続性から `X` はquasi-compactとなる。

非零 `k` の剰余体 `K` へbase changeする。上で示したquasi-compact separated algebraic spaceには、QC cohomologyが消える有限の一様次数上界がある。一方、射影 `π_n:X_K→(P¹_K)^n` は残りのfactorを `[1:0]` に固定するsection `s_n` を持つ。`L_n=O(-2,…,-2)` に対するコホモロジーの引戻しの合成は `(π_n s_n)^*=id` だから、非零の `H^n((P¹_K)^n,L_n)≅K` は `H^n(X_K,π_n^*L_n)` に単射で入る。任意の `n` でこれが成り立ち、上界に矛盾する。従って元の関手はalgebraic spaceでない。`k=0` では空schemeとなる。

**無限自由moduleの全自己同型。** 体 `k` 上で `V=⊕_N k` とし、そのtensor familyと全線形自己同型を保持するgroupoidを取る。恒等自己同型のdual numbers上のliftは

```math
1+\varepsilon a,\qquad a\in\operatorname{End}_k(V),
\qquad (1+\varepsilon a)^{-1}=1-\varepsilon a.
```

従ってstabilizerの接空間は `End_k(V)` であり、各basis vectorへの独立な射影だけでも無限次元である。algebraic stackのIsom空間は基底上locally of finite typeである（[Stacks 04XR](https://stacks.math.columbia.edu/tag/04XR)）。体上のそのidentity点の接空間は有限次元なので矛盾する。この全自己同型groupoidはalgebraic stackにはならない。計算はtensor family `B_σ` で行ったもので、copying Homの接空間は N2.4 により零である。

## D4 — Operation profileの有効化

N3の各profileは具体的なaffine schemeである。例えばidentity profile `S_n={n}` は全座標が1と強制され `Spec k`。全profileの関手がschemeかどうかは別に判定する。

`X` が有限なら `Hom(ΔX,ΔY)=(ΔY)^X=Δ(Y^X)` はscheme。`Y` が有限なら各入力の選択はaffine finite disjoint union `ΔY` なので、その任意積は `Spec(⊗_(x∈X) k^Y)` というaffine schemeである。

両方が無限、`k≠0` の場合には全Hom関手はalgebraic spaceではない。次が直接の反証である。もしそうなら、ある体 `K` へのbase change後もalgebraic spaceとなる。constant function `f₀:X→Y` の点を覆うétale affine neighborhood `U` と、その上の点を選ぶ。必要ならその点の剰余体へさらに拡大する。各coordinate `U→ΔY` の像は、`U` のquasi-compactnessから有限集合 `S_x` に入る。

相異なる `x_i∈X` と `y_i∉S_(x_i)` を可算個選ぶ。affine scheme `T=∏_i Δ{0,1}` から全Homへのmapを、coordinate `x_i` の値がbit 0なら `f₀(x_i)`、1なら `y_i`、他のcoordinateはconstantとして作る。全0点は `U` にliftする。étale map `U×_H T→T` の像は全0点を含むopenである。`T` の座標環の元は有限個のbitにしか依存しないので、このopenは有限個のbitを0に固定したcylinderを含む。その外の一個のbitを1にした点が像に入るが、そのcoordinate値 `y_i` は `U` の可能な値集合 `S_(x_i)` に入らない。矛盾する。従って一個のprofileのaffine性から全profileの代数性は導けない。
