# 第X部 Semantic Repair Descent と SAGA 比較定理

第III部は、Atom-indexed architectural equation system `E` から
obstruction quotient presheaf

\[
Q_E(W)=O_E(W)/I_{\mathrm{Ob}}^E(W)
\]

を生成した。第IV部は、AAT cover 上の Čech cohomology と、局所 section の
貼り合わせ障害を定式化した。本部は、その二つとは独立に semantic repair の
係数と residual class を構成し、Atom と equation の一次対応から両者の比較を証明する。

SAGA の構成列は次である。

```text
semantic atoms + repair support + local repair relations
  -> semantic coefficient M_sem
  -> semantic Čech complex C_sem
  -> local semantic repairs の差 r_sem

Atom-indexed equation system E
  -> equation-generated coefficient Q_E
  -> geometric Čech complex C_E
  -> local equation lifts の差 r_E

primary Atom/equation interpretation
  -> coefficient isomorphism Phi : M_sem ≃ Q_E
  -> cochain isomorphism kappa
  -> H^1_sem ≃ Cech H^1(U,Q_E)
  -> [r_sem] ↦ [r_E]
```

二つの複体は同じ AAT cover 上に置かれるが、係数、local state、residual は
それぞれの一次データから構成する。比較写像、逆写像、微分可換性、
residual class の対応は定理の結論である。

---

## 1. 固定する対象と中心 statement

architecture object `X` の AAT site を `S_X` とし、`W` をその context とする。
有限添字集合 `I` と AAT cover

\[
\mathcal U=\{u_i:U_i\to W\}_{i\in I}
\]

を固定する。添字には全順序を選び、`i<j<k` に対して

\[
U_{ij}=U_i\times_W U_j,\qquad
U_{ijk}=U_i\times_W U_j\times_W U_k
\]

と書く。空の pullback は積から除く。以下の比較 core 自体には有限性は要らないが、
有限 cover は paper statement、finite witness、実行可能な realization を同じ記号で
扱うために固定する。

本部では入力、構成、帰結を次のように区別する。

| 種類 | 内容 |
| --- | --- |
| selected | AAT cover、semantic atom system、repair support、local repair relation、local repair atlas、equation system `E`、local equation-lift atlas、Atom/equation interpretation、local-state interpretation `β` |
| generated | `M_sem`、`Q_E`、二つの Čech complex、`r_sem`、`r_E`、係数写像 `Phi`、cochain map `kappa` |
| proved | `Phi` の同型性、微分可換性、cocycle / coboundary 保存、`H^1` 同型、residual class 対応、true sheaf descent |

### 定理 1.1 SAGA 中心定理（preprint fixed statement）

`𝒰` 上で次を固定する。

1. semantic atom、projection、repair support、restriction-stable な局所 repair relation
   から生成される可換群値 presheaf `M_sem`。
2. architectural equation system `E` から第III部 定理 11.4 により生成される
   可換群値 presheaf `Q_E`。
3. supported semantic atom を displayed Atom/equation residual class へ送る
   restriction-natural な一次写像。
4. その写像について、局所 repair relation の completeness と
   equation generator completeness。relation soundness は 5–7 の local-state data から
   補題 6.2A により導く。これらは cover intersection ごとに確認する。
5. repair words の作用から additive torsor structure を導く affine semantic repair system
   `P_sem` と、その selected local repair atlas。
6. `Q_E` が作用する equation-lift system `P_E` と、その selected local lift atlas。
7. semantic local states を equation local lifts へ送る restriction-natural かつ
   generator-equivariant な一次写像 `β:P_sem→P_E`。

selected local atlases を各 nonempty intersection へ restriction することで、
`P_sem(V)` と `P_E(V)` の元が得られる。したがって、以下で torsor の差と
補題 6.2A を用いる各 intersection 上の local-state system は非空である。

このとき一次写像は cover intersection diagram 上の自然同型

\[
\Phi:M_{\mathrm{sem}}\xrightarrow{\sim}Q_E
\]

を誘導する。`M_sem` と `Q_E` から別々に作った Čech complex の間には
degreewise cochain isomorphism

\[
\kappa^\bullet:
C^\bullet_{\mathrm{sem}}(\mathcal U)
\xrightarrow{\sim}
C^\bullet_E(\mathcal U)
\]

が構成され、`κ` は微分と可換する。したがって

\[
\kappa_*:
H^1_{\mathrm{sem}}(\mathcal U)
\xrightarrow{\sim}
\check H^1(\mathcal U,Q_E)
\]

が誘導される。

semantic local repair atlas から差として生成した `r_sem` と、equation local-lift
atlas から差として生成した `r_E` について、

\[
\kappa_*([r_{\mathrm{sem}}])=[r_E]
\]

である。二つの local atlas を一次対応そのもので選んだ場合は cochain 水準で
`κ¹(r_sem)=r_E` が成立する。独立に選んだ場合も、両 cochain の差は明示的な
`δ⁰`-像であり、class の等式が成立する。

さらに semantic repair object が AAT topology 上の true sheaf であり、
`𝒰` がその topology の cover ならば、

\[
\operatorname{Nonempty}P_{\mathrm{sem}}(W)
\iff
[r_{\mathrm{sem}}]=0
\iff
[r_E]=0.
\]

零類から得た correction で local repairs を一致させた後、true sheaf 条件が
その matching family を実際の global section へ一意に貼り合わせる。

定理 1.1 の各段を以下で構成し、証明する。

## 2. Cover-relative Čech complex

### 定義 2.1 三項 Čech complex

`F` を `S_X` 上の可換群値 presheaf とする。`𝒰` に相対的な cochain group を

\[
\begin{aligned}
C^0(\mathcal U,F)
  &=\prod_i F(U_i),\\
C^1(\mathcal U,F)
  &=\prod_{i<j}F(U_{ij}),\\
C^2(\mathcal U,F)
  &=\prod_{i<j<k}F(U_{ijk})
\end{aligned}
\]

と定義する。restriction を縦棒で表し、

\[
(\delta_F^0 a)_{ij}
  =a_j|_{U_{ij}}-a_i|_{U_{ij}},
\]

\[
(\delta_F^1 c)_{ijk}
  =c_{jk}|_{U_{ijk}}
   -c_{ik}|_{U_{ijk}}
   +c_{ij}|_{U_{ijk}}
\]

とする。

### 補題 2.2 `δ¹δ⁰=0`

任意の `a∈C⁰(𝒰,F)` に対して

\[
\delta_F^1(\delta_F^0a)=0
\]

である。

#### 証明

`i<j<k` を固定する。presheaf restriction の合成則により、三つの pairwise
restriction は同じ triple overlap 上で比較できる。そこで

\[
\begin{aligned}
(\delta_F^1\delta_F^0a)_{ijk}
&=(a_k-a_j)-(a_k-a_i)+(a_j-a_i)\\
&=0.
\end{aligned}
\]

各項は `U_{ijk}` へ restriction した値である。よって全成分が零である。∎

### 定義 2.3 Cover-relative `H¹`

\[
Z^1(\mathcal U,F)=\ker\delta_F^1,\qquad
B^1(\mathcal U,F)=\operatorname{im}\delta_F^0
\]

とし、補題 2.2 により

\[
\check H^1(\mathcal U,F)
  =Z^1(\mathcal U,F)/B^1(\mathcal U,F)
\]

を定義する。これは固定 cover に相対的な Čech `H¹` である。
sheaf cohomology との同一視には、別途その比較定理を要する。

## 3. Semantic atom から生成する係数

### 定義 3.1 Semantic repair presentation

semantic repair presentation は `S_X` の各 context `V` に対する次のデータからなる。
comparison core では、これを `𝒰` の chart、pairwise overlap、triple overlap からなる
intersection category `Int_{\le 2}(𝒰)` へ制限して使う。

```text
Lambda(V):
  V 上で区別する semantic atom の集合。

pi_V : Lambda(V) -> At(V):
  semantic atom を AAT Atom occurrence へ送る projection。

S(V) subset Lambda(V):
  V 上で repair に使用できる supported semantic atom。

Rel_rep(V) subset Z^(S(V)):
  局所的に作用が零になる elementary repair words。
```

各 context morphism `f:V'→V`（comparison core では各 face map）に対して、
semantic atom と Atom の restriction があり、

\[
\pi_{V'}(\lambda|_{V'})
  =\pi_V(\lambda)|_{V'}
\]

を満たす。support は restriction で保たれ、
free abelian group 上の induced map は

\[
\operatorname{res}_f(\operatorname{Rel}_{\mathrm{rep}}(V))
\subset
\langle\operatorname{Rel}_{\mathrm{rep}}(V')\rangle
\]

を満たす。

`Rel_rep(V)` の元は、supported atom の有限整数結合

\[
\sum_\lambda n_\lambda[\lambda]
\]

であり、「この局所 repair word は semantic state を変えない」という
一次的な local repair relation を表す。alias の同一視は
`[λ]-[μ]`、複数 Atom の相殺は一般の有限和として記録できる。

### 定義 3.2 Semantic coefficient

\[
F_{\mathrm{sem}}(V)=\mathbb Z^{(S(V))}
\]

を supported semantic atom 上の free abelian group とし、

\[
R_{\mathrm{rep}}(V)
  =\langle\operatorname{Rel}_{\mathrm{rep}}(V)\rangle
\subset F_{\mathrm{sem}}(V)
\]

と置く。semantic repair coefficient を

\[
M_{\mathrm{sem}}(V)
  =F_{\mathrm{sem}}(V)/R_{\mathrm{rep}}(V)
\]

と定義する。

### 命題 3.3 `M_sem` の presheaf 構成

`M_sem` は `S_X` 上の可換群値 presheaf をなす。

#### 証明

semantic atom restriction は free abelian group の準同型

\[
F_{\mathrm{sem}}(V)\longrightarrow F_{\mathrm{sem}}(V')
\]

へ一意に延長される。relation stability により
`R_rep(V)` の像は `R_rep(V')` に入るため、商の普遍性から

\[
M_{\mathrm{sem}}(V)\longrightarrow M_{\mathrm{sem}}(V')
\]

が誘導される。恒等則と合成則は generator `[λ]` 上で semantic atom restriction の
恒等則と合成則に一致し、generator が free group を生成することから全体で成立する。∎

### 定義 3.4 Semantic repair complex

定義 2.1 を `F=M_sem` に適用し、

\[
C^\bullet_{\mathrm{sem}}(\mathcal U)
  :=C^\bullet(\mathcal U,M_{\mathrm{sem}})
\]

と定義する。また

\[
H^1_{\mathrm{sem}}(\mathcal U)
  :=\check H^1(\mathcal U,M_{\mathrm{sem}})
\]

と置く。

この complex は semantic atom、support、local repair relation の presentation から
構成された。`Q_E`、geometric Čech complex、degreewise comparison map は
この定義に使われない。

## 4. Semantic mismatch から residual を生成する

### 定義 4.1 Affine semantic repair system

`P_sem` を semantic local repair state の presheaf とする。各 `V` で
`F_sem(V)` が `P_sem(V)` に作用し、restriction は作用と可換するとする。
局所 repair relation と作用の間に次を要求する。

```text
relation soundness:
  x in R_rep(V) なら x + p = p。

stabilizer completeness:
  P_sem(V) が非空で x + p = p なら x in R_rep(V)。

local transitivity:
  p,q in P_sem(V) なら、ある x in F_sem(V) が存在して q = x + p。
```

relation soundness により作用は `M_sem(V)` の作用へ降りる。
stabilizer completeness によりこの作用は free であり、local transitivity により
非空の `P_sem(V)` 上で transitive である。したがって、選ばれた cover の各
intersection 上の `P_sem` は `M_sem` による affine space、すなわち additive torsor になる。

ここで必要な semantic faithfulness は、relation と作用から導かれる定理である。
`x+p=y+p` なら `(x-y)+p=p` であり、stabilizer completeness から
`x-y∈R_rep(V)`、したがって `x=y` in `M_sem(V)` と証明される。

### 定義 4.2 Semantic local repair atlas と residual

各 chart で local semantic repair

\[
p_i\in P_{\mathrm{sem}}(U_i)
\]

を選ぶ。`U_{ij}` 上の二つの restriction は同じ `M_sem(U_ij)`-torsor に属するので、
一意な元 `r_sem,ij` が存在して

\[
p_j|_{U_{ij}}
  =r_{\mathrm{sem},ij}+p_i|_{U_{ij}}
\]

を満たす。これらを並べた

\[
r_{\mathrm{sem}}
  =(r_{\mathrm{sem},ij})_{i<j}
  \in C^1_{\mathrm{sem}}(\mathcal U)
\]

を semantic residual cochain と呼ぶ。

`r_sem` は local repair の mismatch から一意に構成される。

### 補題 4.3 Semantic cocycle

\[
\delta_{\mathrm{sem}}^1r_{\mathrm{sem}}=0.
\]

#### 証明

`i<j<k` とする。`U_{ijk}` 上で

\[
\begin{aligned}
p_k
  &=r_{\mathrm{sem},jk}+p_j\\
  &=r_{\mathrm{sem},jk}+r_{\mathrm{sem},ij}+p_i,
\end{aligned}
\]

一方で `p_k=r_sem,ik+p_i` である。作用の freeness から

\[
r_{\mathrm{sem},jk}
-r_{\mathrm{sem},ik}
+r_{\mathrm{sem},ij}=0.
\]

これは `δ¹r_sem` の `(i,j,k)` 成分である。∎

### 定理 4.4 Choice independence

別の local repair atlas `p'_i` を選び、

\[
p'_i=a_i+p_i,\qquad a_i\in M_{\mathrm{sem}}(U_i)
\]

と書く。このとき

\[
r'_{\mathrm{sem}}
  =r_{\mathrm{sem}}+\delta_{\mathrm{sem}}^0a.
\]

したがって class

\[
[r_{\mathrm{sem}}]\in H^1_{\mathrm{sem}}(\mathcal U)
\]

は local atlas の選択に依存しない。

#### 証明

`U_ij` 上で

\[
\begin{aligned}
p'_j
  &=a_j+p_j\\
  &=a_j+r_{\mathrm{sem},ij}+p_i\\
  &=(r_{\mathrm{sem},ij}+a_j-a_i)+p'_i.
\end{aligned}
\]

差の一意性から
`r'_sem,ij=r_sem,ij+a_j-a_i` である。これは表示式そのものである。∎

### 系 4.5 Zero class と matching correction

次は同値である。

1. `[r_sem]=0` in `H¹_sem(𝒰)`。
2. ある `a∈C⁰_sem(𝒰)` が存在して `r_sem=δ⁰_sem a`。
3. corrected local repairs
   \[
   p_i^{\mathrm{corr}}=(-a_i)+p_i
   \]
   がすべての pairwise overlap 上で一致する。

#### 証明

1 と 2 は quotient の定義である。2 の下で定理 4.4 を
`p_i^{corr}=(-a_i)+p_i` に適用すると、新しい residual は
`r_sem-δ⁰a=0` となる。逆に corrected atlas が一致すればその residual は零であり、
定理 4.4 を逆に読んで `r_sem` は `δ⁰`-像である。∎

## 5. Equation system から生成する幾何側

### 定義 5.1 Equation-generated coefficient

第III部 定義 11.3 の displayed equation source と architectural equation system `E`
を固定する。symbolic violation coordinates `ν` から witness ideals と
obstruction ideal が生成され、第III部 定理 11.4 により

\[
Q_E(V)=O_E(V)/I_{\mathrm{Ob}}^E(V)
\]

と restriction が構成される。`Q_E` は可換群値 presheaf である。
displayed Atom/equation coordinate `q=(A_q,i_q,a_q)` の equation interpretation は

\[
\operatorname{int}_E(q)
  =[\epsilon_{V,A_q,i_q,a_q}]\in Q_E(V)
\]

であり、residual restriction naturality を満たす。

### 定義 5.2 Geometric Čech complex

\[
C_E^\bullet(\mathcal U)
  :=C^\bullet(\mathcal U,Q_E),
\qquad
\check H_E^1(\mathcal U)
  :=\check H^1(\mathcal U,Q_E)
\]

と定義する。微分は `Q_E` の restriction の交代和であり、
補題 2.2 により `δ_E¹δ_E⁰=0` である。

この complex は `E` が生成する `Q_E` と AAT cover の pullback intersection から構成される。
semantic atom、semantic relation、`M_sem` はこの定義に使われない。

### 定義 5.3 `Q_E`-controlled equation lift problem

`P_E` を、選ばれた equation reading の local lift を記録する presheaf とする。
各 intersection `V` で `P_E(V)` は、非空なら `Q_E(V)` が free かつ transitively に
作用する affine space とし、restriction は作用と可換する。

典型例は、additive sheaf の short exact sequence

\[
0\longrightarrow Q_E\longrightarrow L_E\longrightarrow B_E\longrightarrow 0
\]

と global base reading `b∈B_E(W)` に対する local lift fiber である。
equation system は coefficient `Q_E` を生成し、base reading と local lifts は
解こうとする局所 equation-lift problem を選ぶ。

各 chart で local equation lift

\[
e_i\in P_E(U_i)
\]

を選び、差

\[
e_j|_{U_{ij}}
  =r_{E,ij}+e_i|_{U_{ij}}
\]

により

\[
r_E=(r_{E,ij})_{i<j}\in C_E^1(\mathcal U)
\]

を定義する。

したがって幾何側の入力は `E`、AAT cover、selected equation-lift problem と local lifts であり、
coefficient と complex は前二者から、residual cochain は local lifts の差から生成される。
`r_E` 自体を selected `1`-cocycle として供給しない。

### 補題 5.4 Geometric cocycle と choice independence

`r_E` は `1`-cocycle である。別の equation atlas
`e'_i=b_i+e_i` に対して

\[
r'_E=r_E+\delta_E^0b
\]

である。したがって `[r_E]∈Čech H_E¹(𝒰)` は local equation-lift atlas の
選択に依存しない。

#### 証明

`i<j<k` とする。triple overlap 上で

\[
e_k=r_{E,jk}+e_j
   =r_{E,jk}+r_{E,ij}+e_i,
\qquad
e_k=r_{E,ik}+e_i.
\]

equation torsor の freeness から
`r_E,jk-r_E,ik+r_E,ij=0` である。よって `δ_E¹r_E=0`。

また `e'_i=b_i+e_i` なら、pairwise overlap 上で

\[
\begin{aligned}
e'_j
&=b_j+e_j\\
&=b_j+r_{E,ij}+e_i\\
&=(r_{E,ij}+b_j-b_i)+e'_i.
\end{aligned}
\]

差の一意性から `r'_E,ij=r_E,ij+b_j-b_i`、したがって
`r'_E=r_E+δ_E⁰b` である。∎

## 6. Primary comparison core と equation realization

### 定義 6.1 Primary SAGA correspondence

`Q` を intersection diagram 上の可換群値 presheaf とする。
primary coefficient correspondence は、各 `V` で supported semantic atom を
target coefficient へ送る写像

\[
\chi_V:S(V)\longrightarrow Q(V)
\]

で、restriction naturality

\[
\chi_{V'}(\lambda|_{V'})
  =\chi_V(\lambda)|_{V'}
\]

を満たすものをいう。

free abelian group の普遍性により、`χ_V` は一意な準同型

\[
\widetilde\chi_V:
F_{\mathrm{sem}}(V)\longrightarrow Q(V)
\]

へ延長される。

### 命題 6.1A Equation semantic realization

`Q=Q_E`、`P_Q=P_E` とする。各 intersection `V` と supported semantic atom
`λ∈S(V)` に、required equation index `i_λ`、local architecture reading `A_λ`、
support Atom `π_V(λ)` を対応させる。これらが restriction と可換するとき、

\[
\chi^E_V(\lambda)
  :=
[\epsilon_{V,A_\lambda,i_\lambda,\pi_V(\lambda)}]
\in Q_E(V)
\]

と定義する。

第III部 定理 11.4 の residual restriction naturality により

\[
\chi^E_{V'}(\lambda|_{V'})
  =\chi^E_V(\lambda)|_{V'}
\]

である。したがって `χ^E` は定義 6.1 の primary coefficient correspondence を構成する。

displayed equation source と `ε` を使うのはこの realization statement である。
以下の presentation theorem 自体は、`E`、displayed source、sheaf condition、
global gluing data、finiteness を受け取らない。

### 定義 6.1B Primary state correspondence

`P_Q` を各 intersection で非空な `Q`-affine local-state system とする。
local state の一次対応とは、restriction-natural な写像

\[
\beta_V:P_{\mathrm{sem}}(V)\longrightarrow P_Q(V)
\]

で、各 supported atom に対して generator-level equivariance

\[
\beta_V([\lambda]+p)
  =\chi_V(\lambda)+\beta_V(p)
\]

を満たすものをいう。有限和と additive inverse への equivariance は作用則から従う。
`β` の逆写像や全単射性は入力に含めない。

equation realization では `Q=Q_E`、`P_Q=P_E` とし、semantic local state の
equation reading を `β:P_sem→P_E` に取る。

### 定義 6.2 SAGA presentation exactness

primary correspondence が `V` で exact であるとは、次の三条件をいう。

```text
repair-relation soundness:
  R_rep(V) subset ker(tilde chi_V).

repair-relation completeness:
  ker(tilde chi_V) subset R_rep(V).

target-generator completeness:
  im(tilde chi_V) = Q(V).
```

最初の二条件は、semantic 側で「同じ repair effect」と宣言した語と、
target coefficient で同じ class を持つ語が正確に一致することをいう。
三つ目は selected semantic support が `Q(V)` の全 coefficient direction を生成することをいう。
命題 6.1A の realization では、これが equation-generator completeness である。

これらは generator と relation に対する検証可能な条件である。
degreewise complex equivalence、inverse、微分可換性、`H¹` 同型を直接要求しない。

### 補題 6.2A Primary state interpretation generates soundness

`P_sem(V)` が非空で、semantic repair words の relation soundness、
`P_Q(V)` に対する `Q(V)`-作用の freeness、`β_V` の generator-level
equivariance が成立するとする。このとき

\[
R_{\mathrm{rep}}(V)
\subset
\ker(\widetilde\chi_V).
\]

#### 証明

`x∈R_rep(V)` と `p∈P_sem(V)` を取る。semantic action の relation soundness から
`x+p=p` である。free group へ延長した equivariance により

\[
\beta_V(p)
  =\beta_V(x+p)
  =\widetilde\chi_V(x)+\beta_V(p).
\]

`P_Q(V)` 上の作用は free なので `\widetilde χ_V(x)=0` である。∎

### 定理 6.3 Coefficient Presentation Theorem

primary correspondence がすべての intersection 上で exact なら、
intersection diagram 上の自然同型

\[
\Phi:M_{\mathrm{sem}}\xrightarrow{\sim}Q
\]

が構成される。exactness が `S_X` の全 context 上で成立すれば、同じ構成は
`S_X` 上の presheaf 自然同型を与える。

#### 証明

repair-relation soundness により `\widetilde χ_V` は商を通り、一意な準同型

\[
\Phi_V:
F_{\mathrm{sem}}(V)/R_{\mathrm{rep}}(V)
\longrightarrow Q(V)
\]

を誘導する。

`Φ_V([x])=0` とする。すると `x∈ker(\widetilde χ_V)` であり、
repair-relation completeness から `x∈R_rep(V)`、よって `[x]=0` である。
したがって `Φ_V` は単射である。

任意の `q∈Q(V)` に対し、generator completeness から
`\widetilde χ_V(x)=q` なる `x∈F_sem(V)` が存在する。よって
`Φ_V([x])=q` であり、`Φ_V` は全射である。

restriction naturality は generator `[λ]` 上で

\[
\Phi_{V'}([\lambda|_{V'}])
  =\chi_{V'}(\lambda|_{V'})
  =\chi_V(\lambda)|_{V'}
  =\Phi_V([\lambda])|_{V'}
\]

である。generator が `M_sem(V)` を生成するため全要素で成立する。
したがって `Φ` は presheaf の自然同型である。∎

### 系 6.4 Image comparison

target-generator completeness を外し、repair-relation soundness と completeness
だけを仮定すると、

\[
M_{\mathrm{sem}}(V)
\xrightarrow{\sim}
\operatorname{im}(\widetilde\chi_V)
\]

が得られる。full `Q` comparison に必要な追加条件は、正確に
`im(\widetilde χ_V)=Q(V)` である。命題 6.1A では `Q=Q_E` と読む。
`χ` の restriction naturality により `im(\widetilde χ)` は intersection diagram 上の
subpresheaf をなすので、この image comparison も自然である。

この image 版により、semantic vocabulary が読み取る coefficient scope と
full target coefficient を明示的に区別できる。命題 6.1A では target coefficient が
equation coefficient `Q_E` である。

### 系 6.5 Local state comparison の同型性

`P_sem(V)` と `P_Q(V)` が非空で、定理 6.3 の `Φ_V` があり、
`β_V` が generator-level equivariance を満たすとする。このとき `β_V` は
`Φ_V`-equivariant な全単射である。

#### 証明

generator-level equivariance は free group の有限和と additive inverse へ延長される。
action relation soundness と repair-relation soundness により、二つの代表元の差が
`R_rep(V)` に入ると semantic action と target action の両方で同じ結果になる。
したがって relation による商を経て

\[
\beta_V(m+p)=\Phi_V(m)+\beta_V(p)
\]

を与える。

`β_V(p)=β_V(q)` とする。semantic torsor の transitivity から `q=m+p` と書ける。
すると `Φ_V(m)+β_V(p)=β_V(p)` である。target torsor の freeness と
`Φ_V` の単射性から `m=0`、よって `p=q` である。

任意の `e∈P_Q(V)` と `p∈P_sem(V)` を取る。target torsor の transitivity から
`e=q+β_V(p)` となる `q∈Q(V)` がある。`Φ_V` の全射性から `q=Φ_V(m)` と書け、
`e=β_V(m+p)` である。∎

### 例 6.6 Exactness conditions are material

一 generator の free group `F=ℤ` で、三条件を一つずつ外す。

```text
soundness failure:
  R = 2Z, Q = Z, tilde chi(n) = n.
  relation 2 = 0 は Q で零にならず、map は F/R へ降りない。

completeness failure:
  R = 0, Q = Z/(2), tilde chi(n) = [n].
  map は降りて全射だが、2 が kernel に残るため単射でない。

generation failure:
  R = 2Z, Q = Z/(4), tilde chi(n) = [2n].
  kernel は R と一致するが、image は {0,[2]} で Q 全体ではない。
```

三つ目では

\[
M_{\mathrm{sem}}\cong\{0,[2]\}\subset\mathbb Z/(4)
\]

という image comparison は成立するが、full `Q` comparison は成立しない。
したがって定義 6.2 の三条件は、それぞれ map の存在、単射性、全射性という
異なる数学的仕事を担う。

### 系 6.7 Equation Coefficient Comparison

命題 6.1A の equation semantic realization を取る。affine local-state data と `β`
から補題 6.2A が repair-relation soundness を与え、
repair-relation completeness と equation-generator completeness が各 intersection で
証明されているとする。このとき定理 6.3 は

\[
\Phi_E:
M_{\mathrm{sem}}|_{\operatorname{Int}_{\le2}(\mathcal U)}
\xrightarrow{\sim}
Q_E|_{\operatorname{Int}_{\le2}(\mathcal U)}
\]

を構成する。

ここまでで equation semantics の役割は終わる。次節の cochain 計算は
この自然同型と二つの独立 Čech complex だけを使う。

## 7. Cochain comparison と SAGA `H¹` 同型

### 定義 7.1 Degreewise comparison map

系 6.7 の `Φ_E` から、各次数 `n=0,1,2` で

\[
\kappa^n:C^n_{\mathrm{sem}}(\mathcal U)\longrightarrow C_E^n(\mathcal U)
\]

を各 intersection 成分へ `Φ` を適用して定義する。例えば

\[
(\kappa^1c)_{ij}=\Phi_{U_{ij}}(c_{ij}).
\]

各 `Φ_V` が同型なので、`κ^n` も積上の同型である。

### 定理 7.2 Cochain commutation

次の diagram は可換である。

\[
\begin{array}{ccccc}
C^0_{\mathrm{sem}}(\mathcal U)
&\xrightarrow{\delta^0_{\mathrm{sem}}}&
C^1_{\mathrm{sem}}(\mathcal U)
&\xrightarrow{\delta^1_{\mathrm{sem}}}&
C^2_{\mathrm{sem}}(\mathcal U)\\
\downarrow\kappa^0&&\downarrow\kappa^1&&\downarrow\kappa^2\\
C^0_E(\mathcal U)
&\xrightarrow{\delta^0_E}&
C^1_E(\mathcal U)
&\xrightarrow{\delta^1_E}&
C^2_E(\mathcal U).
\end{array}
\]

すなわち

\[
\kappa^1\delta^0_{\mathrm{sem}}
  =\delta_E^0\kappa^0,
\qquad
\kappa^2\delta^1_{\mathrm{sem}}
  =\delta_E^1\kappa^1.
\]

#### 証明

`a∈C⁰_sem` と `i<j` に対し、

\[
\begin{aligned}
(\kappa^1\delta^0_{\mathrm{sem}}a)_{ij}
&=\Phi_{U_{ij}}(a_j|-a_i|)\\
&=\Phi_{U_j}(a_j)|-\Phi_{U_i}(a_i)|\\
&=(\delta_E^0\kappa^0a)_{ij}.
\end{aligned}
\]

二行目は `Φ` の加法性と restriction naturality である。

同様に `c∈C¹_sem` と `i<j<k` に対し、

\[
\begin{aligned}
(\kappa^2\delta^1_{\mathrm{sem}}c)_{ijk}
&=\Phi_{U_{ijk}}(c_{jk}|-c_{ik}|+c_{ij}|)\\
&=\Phi(c_{jk})|-\Phi(c_{ik})|+\Phi(c_{ij})|\\
&=(\delta_E^1\kappa^1c)_{ijk}.
\end{aligned}
\]

よって両方の正方形が可換である。∎

### 系 7.3 Cocycle と coboundary の保存・反映

1. `c∈Z¹(𝒰,M_sem)` なら `κ¹c∈Z¹(𝒰,Q_E)`。
2. `κ¹c∈Z¹(𝒰,Q_E)` なら `c∈Z¹(𝒰,M_sem)`。
3. `c-c'=δ⁰_sem a` なら
   `κ¹c-κ¹c'=δ⁰_E(κ⁰a)`。
4. `κ¹c-κ¹c'=δ⁰_E b` なら
   `c-c'=δ⁰_sem((κ⁰)^{-1}b)`。

#### 証明

1 と 3 は定理 7.2 を直接使う。2 は `κ²` の単射性、4 は `κ⁰` と `κ¹`
の全単射性、および定理 7.2 を使う。∎

### 定理 7.4 SAGA `H¹` Comparison

写像

\[
\kappa_*:
H^1_{\mathrm{sem}}(\mathcal U)
\longrightarrow
\check H_E^1(\mathcal U),
\qquad
[c]\longmapsto[\kappa^1c]
\]

は well-defined な可換群同型である。

#### 証明

系 7.3(1)により `κ¹c` は cocycle である。代表元を
`c'=c+δ⁰_sem a` に替えると、系 7.3(3)により

\[
\kappa^1c'
  =\kappa^1c+\delta_E^0(\kappa^0a)
\]

となるので class は変わらない。したがって `κ_*` は well-defined である。

逆向きは、定理 6.3 で構成した coefficient isomorphism の逆から得る
degreewise map `(κ^n)^{-1}` を用い、

\[
[d]\longmapsto[(\kappa^1)^{-1}d]
\]

と定義する。系 7.3(2),(4)の逆向きの計算により well-defined である。
cochain 水準で `κ^n` とその逆が互いに inverse なので、商上でも両側合成は恒等となる。∎

### 定理 7.5 Residual Correspondence

semantic atlas `p_i` と equation atlas `e_i` を独立に選ぶ。各 chart で
`β(p_i)` と `e_i` は同じ `Q_E(U_i)`-torsor に属するので、一意な
`h_i∈Q_E(U_i)` が存在して

\[
e_i=h_i+\beta(p_i)
\]

を満たす。`h=(h_i)` とすると

\[
r_E=\kappa^1(r_{\mathrm{sem}})+\delta_E^0h.
\]

したがって

\[
\kappa_*([r_{\mathrm{sem}}])=[r_E].
\]

特に `e_i=β(p_i)` を選べば `h=0` であり、

\[
\kappa^1(r_{\mathrm{sem}})=r_E
\]

が cochain 水準で成立する。

#### 証明

`U_ij` 上で、`β` の naturality と equivariance を使うと

\[
\begin{aligned}
e_j
&=h_j+\beta(p_j)\\
&=h_j+\beta(r_{\mathrm{sem},ij}+p_i)\\
&=h_j+\Phi(r_{\mathrm{sem},ij})+\beta(p_i)\\
&=(\Phi(r_{\mathrm{sem},ij})+h_j-h_i)+e_i.
\end{aligned}
\]

equation torsor における差の一意性から

\[
r_{E,ij}
  =\Phi(r_{\mathrm{sem},ij})+h_j-h_i.
\]

これは表示式の各成分である。`δ⁰h` は coboundary なので class の等式が従う。∎

### 定理 7.6 SAGA 比較定理

二つの affine local-state system、primary state correspondence `β`、
repair-relation completeness、equation-generator completeness の下で、
補題 6.2A が soundness を与える。したがって定理 6.3 の
SAGA presentation exactness が成立し、次がすべて従う。

```text
coefficient:
  M_sem ≃ Q_E

complex:
  C_sem^bullet(U) ≃ C_E^bullet(U)

cochain:
  kappa commutes with delta^0 and delta^1

cohomology:
  H^1_sem(U) ≃ Cech H^1(U,Q_E)

residual:
  kappa_*([r_sem]) = [r_E]

zero and nonzero:
  [r_sem] = 0 iff [r_E] = 0
  [r_sem] != 0 iff [r_E] != 0
```

#### 証明

係数同型は定理 6.3、complex と cochain 可換性は定義 7.1 と定理 7.2、
cohomology 同型は定理 7.4、residual 対応は定理 7.5 である。
零性と非零性は同型が zero を保存し反映することから従う。∎

comparison core が使うのは、cover intersection、二つの係数 presheaf、
generator/relation exactness、restriction naturality である。
global sheaf condition、global gluing datum、cover の有限列挙、
displayed equation fulfillment は定理 7.2–7.6 の仮定ではない。

## 8. True sheaf descent と actual global repair

### 定義 8.1 True semantic repair sheaf

`P_sem` が true semantic repair sheaf であるとは、次をいう。

1. `P_sem` は `S_X` の選ばれた topology のすべての cover に対して
   sheaf condition を満たす。
2. `M_sem` の作用は restriction と可換し、局所的に free かつ transitive である。
3. `𝒰` がその topology に属する AAT cover である。

この入力から `𝒰` に対する sheaf condition が導かれる。
per-cover amalgamation map を別データとして置かない。

global semantic repair を

\[
\operatorname{GlobalRepair}_{\mathrm{sem}}(W)
  :=P_{\mathrm{sem}}(W)
\]

と定義する。

### 定理 8.2 Grounded Global Gluing

定理 7.6 の設定に加え、`P_sem` が true semantic repair sheaf なら、

\[
\operatorname{Nonempty}P_{\mathrm{sem}}(W)
\iff
[r_{\mathrm{sem}}]=0
\iff
[r_E]=0.
\]

また `[r_sem]=0` の証明から得る correction `a` に対して、
corrected family

\[
p_i^{\mathrm{corr}}=(-a_i)+p_i
\]

を restriction として持つ global section が一意に存在する。

#### 証明

`[r_sem]=0` とする。系 4.5 により `r_sem=δ⁰a` なる `a` を取り、
`p_i^{corr}=(-a_i)+p_i` と置く。この family は pairwise overlap 上で一致する。
`𝒰` は topology の cover で、`P_sem` はその topology 上の sheaf なので、
sheaf amalgamation により一意な `p∈P_sem(W)` が存在し

\[
p|_{U_i}=p_i^{\mathrm{corr}}
\]

を満たす。ここで true sheaf 条件が実際に global section を構成した。

逆に `p∈P_sem(W)` が存在するとする。各 `i` で torsor の transitivity と
freeness により一意な `a_i∈M_sem(U_i)` が存在して

\[
p_i=a_i+p|_{U_i}
\]

となる。overlap 上で差を計算すると
`r_sem,ij=a_j-a_i`、すなわち `r_sem=δ⁰a` である。
よって `[r_sem]=0`。最後の同値は定理 7.6 の residual class 対応から従う。∎

ここで一意なのは、固定した corrected matching family の amalgamation である。
`P_sem(W)` 全体が subsingleton であるとは主張しない。異なる global repairs の差は、
存在する場合には global coefficient sections、すなわち degree-zero data が担う。

### 系 8.3 Equation-side global lift

SAGA presentation exactness と primary state correspondence が `S_X` 上で成立し、
`P_E` も選ばれた topology 上の sheaf であるとする。系 6.5 により
`β:P_sem→P_E` は `𝒰` 上で局所同型であり、selected base `W` 上の写像
`β_W:P_sem(W)→P_E(W)` は全単射である。したがって

\[
\operatorname{Nonempty}P_{\mathrm{sem}}(W)
\iff
\operatorname{Nonempty}P_E(W)
\iff
[r_E]=0.
\]

零類から構成した matching equation lifts は `P_E` の sheaf condition により
actual global equation lift へ貼り合わされる。

実際、`P_E(W)` の section は cover 上で `β` の一意な preimage を持つ。
それらは overlap 上で一致し、`P_sem` の sheaf condition により一つの section へ貼り合うので
`β_W` は全射である。二つの semantic sections の像が等しければ、
cover 上の local injectivity と separatedness から元も等しい。よって `β_W` は全単射である。

### 原則 8.4 Additive、torsor、higher の分離

定理 7.4 の `H¹` comparison は可換群値 presheaf の additive theorem である。
定義 4.1 と定義 5.3 の torsor structure は、selected local states から
additive residual class を生成するために使う。定理 8.2 は additive torsor の
effectivity と true sheaf descent を使う。

次の対象はそれぞれ独立の statement を要する。

```text
nonabelian torsor:
  pointed-set-valued nonabelian H^1 と twisted cocycle。

higher coherence:
  2-cocycle、gerbe、H^2 以後の obstruction。

stack:
  object と morphism の descent、および higher compatibility。
```

additive `H¹` comparison から、これらの結論を自動的に導かない。

## 9. G-07 との対応と循環しない依存

G-07 `Law-Generated Conormal First-Order Descent Theorem` は、
本部の local-lift、connecting cocycle、choice independence、actual sheaf gluing の
最も強い既存資産である。その役割を数学的構成単位で固定する。

| G-07 の数学的構成 | 本部での扱い | 数学的役割 |
| --- | --- | --- |
| local patch reading source | generalize | semantic local input と required-law support の一次 source |
| overlap law combination | generalize | pairwise reading difference を required-law generators で表す局所 relation |
| evaluated combination の obstruction-ideal membership | reuse pattern | generator relation が equation ideal で零になる soundness |
| raw quotient compatibility | specialization | required-law relation から `O/I` compatibility を生成 |
| explicit local-lift data | reuse | base section と local lifts だけを入力にする local-lift problem |
| kernel-valued local-lift difference | reuse | local lifts の差から residual を生成 |
| local-lift difference の cocycle identity | reuse | `d¹d⁰=0` と kernel identification による cocycle proof |
| connecting class の choice independence | reuse | local lift choice の変更が `δ⁰`-像になる証明 |
| corrected local-lift matching | reuse | zero class から matching correction を構成 |
| corrected family の sheaf amalgamation | reuse | true sheaf amalgamation による actual global lift |
| connecting class zero と global lift existence の同値 | reuse | class zero と global lift existence の同値 |
| conormal-valued semantic first-order repair | specialization | correction primitive を独立に定義 |
| semantic repair と global first-order lift の同値 | specialization | correction primitive と global first-order lift の構成的同値 |
| conormal class zero と semantic repair existence の同値 | specialization | first-order residual の effectivity |
| conormal first-order descent package | specialization | choice independence、effectivity、`H⁰` torsor、zero/nonzero witness の統合 |

### 定理 9.1 First-order conormal specialization

G-07 の short exact sequence

\[
0\longrightarrow I/I^2
\longrightarrow O/I^2
\longrightarrow O/I
\longrightarrow 0
\]

において、`O/I` の selected base section と各 chart 上の `O/I²` local lifts を取る。
pairwise difference は `I/I²` に一意に持ち上がり、

\[
r_{\mathrm{con}}\in
Z^1(\mathcal U,I/I^2)
\]

を生成する。G-07 の定理群は

\[
[r_{\mathrm{con}}]=0
\iff
\operatorname{Nonempty}(\text{global }O/I^2\text{ lift})
\iff
\operatorname{Nonempty}(\text{SemanticFirstOrderRepair})
\]

を証明する。これは定理 8.2 で使う local correction と true sheaf amalgamation の
first-order conormal specialization である。G-07 単独は定理 6.3 の
semantic presentation comparison や定理 7.6 の full SAGA comparison を instantiate しない。

一方、一般 SAGA の coefficient presentation theorem は
semantic atom presentation と full equation coefficient `Q_E` の間の exactness を扱う。
G-07 の conormal coefficient `I/I²` はその自動的な代替ではない。
一般 theorem へ再利用するのは local-lift construction と sheaf proof であり、
`I/I²`、`O/I²→O/I`、first-order lift は specialization に留める。

### 命題 9.2 Dependency audit

本部の論理依存は次である。

```text
Part III:
  E -> Q_E and residual restriction naturality

Part IV:
  cover-relative Cech construction and additive torsor reading

semantic primary data:
  atoms + support + local relations -> M_sem and r_sem

SAGA presentation exactness:
  M_sem -> Q_E -> cochain comparison -> H^1 comparison

true sheaf condition:
  zero class -> corrected matching family -> actual global section

first-order specialization:
  Q = I/I^2 and O/I^2 -> O/I local lifts
```

定理番号で書くと、依存は次である。

```text
Definition 3.1 + Definition 3.2
  -> Proposition 3.3
  -> Definition 3.4
  -> Definition 4.2
  -> Lemma 4.3 + Theorem 4.4

Part III Theorem 11.4
  -> Definition 5.1
  -> Definition 5.2 + Definition 5.3
  -> Lemma 5.4
  -> Proposition 6.1A

Definition 4.1 + Definition 5.3 + Definition 6.1 + Definition 6.1B
  -> Lemma 6.2A

Lemma 6.2A + relation completeness + generator completeness
  -> Theorem 6.3
  -> Corollary 6.7
  -> Definition 7.1
  -> Theorem 7.2
  -> Corollary 7.3
  -> Theorem 7.4

Theorem 4.4 + Lemma 5.4 + Theorem 6.3 + beta
  -> Theorem 7.5

Theorem 7.4 + Theorem 7.5
  -> Theorem 7.6

Theorem 7.6 + true semantic repair sheaf
  -> Theorem 8.2
```

一般 SAGA comparison の証明は G-07 の conormal theorem を premise とせず、
semantic presentation、equation-generated coefficient、presentation exactness から
定理 6.3–7.6 を構成する。G-07 から一般 theorem へ再利用するのは
local-lift difference、choice independence、matching correction、sheaf amalgamation の
証明 pattern である。定理 9.1 は一般 theorem の後に first-order conormal data を代入する。
したがって一般 theorem の証明と first-order specialization の間に循環はない。

## 10. Finite executable realization

有限性は定理 6.3–8.2 の論理には使わない。有限 semantic vocabulary、有限 relation list、
有限 cover を選んだとき、各条件を行列計算へ落とす。

### 定義 10.1 Finite SAGA presentation matrix

各 intersection `V` で supported atom を列、elementary repair relation を行に並べる。

```text
R_V:
  repair relation matrix

Chi_V:
  semantic generators -> equation coefficient の行列

D_sem^0, D_sem^1:
  semantic restriction から作る Cech differential

D_E^0, D_E^1:
  Q_E restriction から作る Cech differential
```

有限生成可換群の場合、Smith normal form により次を確認できる。

```text
im(R_V) = ker(Chi_V)
im(Chi_V) = Q_E(V)
kappa^1 D_sem^0 = D_E^0 kappa^0
kappa^2 D_sem^1 = D_E^1 kappa^1
```

最初の二式は SAGA presentation exactness、後二式は定理 7.2 の有限表示である。
finite realization は一般 theorem の仮定を具体的 input で検証し、
residual class を計算する層である。

### 例 10.2 Independently generated circle comparison

四つの chart と四つの nonempty overlap

\[
U_{01},U_{12},U_{23},U_{30}
\]

を持ち、nondegenerate triple overlap を持たない 4-cycle cover を取る。
各 nonempty intersection `V` で semantic support を一 generator
`S(V)={σ_V}`、restriction を `σ_V↦σ_{V'}` とし、local repair relation を

\[
2\sigma_V=0
\]

で生成する。すると semantic 側は独立に

\[
M_{\mathrm{sem}}(V)
  =\mathbb Z[\sigma_V]/(2\sigma_V)
  \cong\mathbb F_2
\]

を生成する。

equation 側では `O_E(V)=ℤ`、`I_Ob^E(V)=(2)` とし、第III部の構成から

\[
Q_E(V)=\mathbb Z/(2)
\]

を得る。一次 Atom/equation interpretation を

\[
\chi_V(\sigma_V)=[1]
\]

とする。

```text
soundness:
  2 sigma_V maps to [2] = 0.

completeness:
  ker(Z -> Z/(2)) = 2Z.

generation:
  [1] generates Z/(2).
```

よって定理 6.3 が `M_sem≃Q_E` を構成する。
これは一方の complex を他方から transport したものではなく、
semantic presentation `ℤ[σ]/(2σ)` と equation quotient `ℤ/(2)` の
presentation comparison である。

local state system も有限に構成できる。各 chart と nonempty overlap 上で
`P_sem=F₂` とし、`M_sem` は加法で作用する。oriented edge `e` の source chart から
overlap への restriction を恒等、target chart からの restriction を
`x↦x+t_e` とする。ここで

\[
(t_{01},t_{12},t_{23},t_{30})=(1,0,0,0).
\]

最後の edge は `U_03` を `3→0` に向けたものであり、`\mathbb F_2` では向きの反転による
符号は変わらない。triple overlap がないため、これらの restriction は必要な
functoriality 条件を満たす。各 chart で local state `p_i=0` を選ぶと、
semantic local repair atlas の residual は

\[
r_{\mathrm{sem}}=(1,0,0,0)\in\mathbb F_2^4
\]

である。equation 側も `P_E=F₂`、transition `Φ(t_e)` として別に構成し、
`β` を local coordinate 上の `Φ` とする。各 chart で `e_i=0` を選ぶと
`r_E=κ¹(r_sem)` である。
triple overlap がないため両 residual は cocycle である。4-cycle 上の任意の
`δ⁰`-像は oriented edge sum が零だが、`r_sem` の edge sum は `1` である。
したがって

\[
[r_{\mathrm{sem}}]\ne0,\qquad
[r_E]\ne0,\qquad
\kappa_*([r_{\mathrm{sem}}])=[r_E].
\]

この例の詳細な quotient arithmetic と AAT cover は付録 B.9 に置く。

## 11. SAGA の名称と結論

### 11.1 SAGA の名称

SAGA は **Sémantique Architecturale, Géométrie Algébrique** と読む。
本部の比較は、semantic repair cohomology と AAT site 上の algebraic Čech
cohomology の間にある。第VIII部の AAT-GAGA measurement comparison とは
別の theorem family である。

### 11.2 Part X の結論

第X部で確定した背骨は次である。

```text
semantic presentation
  -> M_sem
  -> semantic local-repair torsor
  -> r_sem in Z^1

equation presentation
  -> Q_E
  -> equation local-lift torsor
  -> r_E in Z^1

generator/relation exactness
  -> Phi : M_sem ≃ Q_E
  -> kappa delta = delta kappa
  -> H^1_sem ≃ Cech H^1(U,Q_E)
  -> [r_sem] maps to [r_E]

true sheaf descent
  -> zero class
  -> corrected matching family
  -> actual global repair
```

semantic complex は semantic presentation から、geometric complex は
equation-generated coefficient から、それぞれ構成された。
comparison map は Atom/equation generator map を商へ降ろして構成され、
その同型性は relation soundness、relation completeness、generation から証明された。
residual は両側で local state の差として生成され、その class の一致が計算された。

これが SAGA 中心定理の数学的 statement である。
