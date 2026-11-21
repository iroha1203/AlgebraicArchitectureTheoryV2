# 付録A 正の論理の導出と健全性

この付録は、[第1章](part_1/chapter_1_atoms_laws_theories.md)のLaw導出に用いる計算を定める。
構文は、変数の等式、関係・domain・graphを変数に適用した原子式、
$`\top,\bot,\wedge,\vee,\exists`$ からなる。
各式と各導出木は有限とする。Lawの族全体は小さい任意の集合でよい。

## A.1 導出規則

sequent $`\varphi\vdash_\Gamma\psi`$ は、
型付き変数文脈 $`\Gamma`$ の任意の割当てで、$`\varphi`$ の成立が $`\psi`$ の成立を含意することを表す。
次の規則から作られる有限の導出を $`\mathbb T\vdash(\varphi\vdash_\Gamma\psi)`$ と書く。

1. **前提と切断。** $`\varphi\vdash\varphi`$ を許す。
   $`\varphi\vdash\psi`$ と $`\psi\vdash\theta`$ から $`\varphi\vdash\theta`$ を得る。
   理論の必須Lawと、署名のgraphの構造公理を前提として使う。
2. **変数。** 文脈 $`\Gamma`$ の全変数から文脈 $`\Delta`$ の変数への型を保つ写像に沿う置換を許す。
   この写像は、式に自由出現しない $`\Gamma`$ の変数についても指定する。
   文脈への未使用変数の追加を許す。束縛変数は捕獲を避けて改名する。
3. **真偽。** $`\varphi\vdash\top`$、$`\bot\vdash\varphi`$ を許す。
4. **連言。** $`\varphi\wedge\psi\vdash\varphi`$、$`\varphi\wedge\psi\vdash\psi`$ を許す。
   $`\theta\vdash\varphi`$ と $`\theta\vdash\psi`$ から $`\theta\vdash\varphi\wedge\psi`$ を得る。
5. **選言。** $`\varphi\vdash\varphi\vee\psi`$、$`\psi\vdash\varphi\vee\psi`$ を許す。
   $`\theta\wedge\varphi\vdash\chi`$ と $`\theta\wedge\psi\vdash\chi`$ から
   $`\theta\wedge(\varphi\vee\psi)\vdash\chi`$ を得る。
6. **存在。** $`y`$ が $`\Gamma`$ 内の正しい型の変数なら、
   $`\varphi[y/x]\vdash_\Gamma\exists x\,\varphi`$ を許す。
   $`\theta\wedge\varphi\vdash_{\Gamma,x}\chi`$ から、
   $`\theta\wedge\exists x\,\varphi\vdash_\Gamma\chi`$ を得る。
   後者では $`x`$ は $`\theta,\chi,\Gamma`$ に自由出現しない。
7. **等号。** $`\top\vdash_x x=x`$ を許す。
   同じsortの $`x,y`$ について
   $`x=y\wedge\varphi(x,\boldsymbol z)\vdash\varphi(y,\boldsymbol z)`$ を許す。
   置換は捕獲を避けて行う。

有限個の連言・選言は二項の規則と $`\top,\bot`$ から扱う。
部分termの代入 $`\theta=(\theta_i)`$ では、第1章の定義1.7のように、
全ての $`\theta_i`$ の定義可能性をLawの入力へ加える。
導出上は、新しい変数 $`x_i`$ と値graphの連言
$`\bigwedge_iE_{\theta_i}(\boldsymbol d,x_i)`$ を使い、
元のsequentへ変数置換を施した後、その値を存在量化する。
graphの一価性と構文帰納法により
$`\exists\boldsymbol x\,(\bigwedge_iE_{\theta_i}\wedge\varphi(\boldsymbol x))`$ は
$`\mathrm{Def}_\theta\wedge\varphi[\theta]`$ と相互に導出できる。
原子式では同じ値を等号置換し、連言では一価性により二組のwitnessを合わせ、
選言では成立する枝へ、存在量化では捕獲を避けてwitnessを移す。
したがって $`\varphi\vdash_\Gamma\psi`$ の導出から
$`\mathrm{Def}_\theta\wedge\varphi[\theta]\vdash_\Delta\psi[\theta]`$ を得る。
全域性を導出できるtermでは、$`\mathrm{Def}_\theta`$ を導出してこの前提を除ける。
空の担体を許すため、未使用変数を文脈から取り除くことを無条件の規則にはしない。

## A.2 健全性

**命題A.1（導出の健全性）.**
構造 $`A`$ が $`\mathbb T`$ の全必須Lawを満たし、
$`\mathbb T\vdash(\varphi\vdash_\Gamma\psi)`$ なら、
任意の $`\gamma\in X_\Gamma(A)`$ について
$`A\models\varphi(\gamma)`$ から $`A\models\psi(\gamma)`$ が従う。

**証明.**
導出木の高さについて帰納する。Lawはモデルの仮定、
graphの構造公理は写像と部分写像の定義で成り立つ。
前提・切断は含意の反射性・推移性である。
変数規則では割当てを対応する成分で引き戻す。
文脈への追加では、与えられた割当ての制限を用いる。
真偽・連言の規則はそれぞれの充足の定義で成り立つ。
選言除去では成立する枝について帰納法を適用する。

存在導入では割当ての $`y`$ 成分をwitnessとする。
存在除去では、前提の存在量化のwitness $`a`$ を $`x`$ へ割り当て、
帰納法により $`\chi`$ を得る。$`x`$ が $`\theta,\chi`$ に自由出現しないので、
得られた $`\chi`$ は元の $`\Gamma`$ 上の主張である。
等号規則では、同じ値を割り当てた二変数の交換が式の充足を変えない。
これは原子式の集合としての解釈から、論理演算と量化について帰納して得られる。
以上ですべての最終規則を覆う。□

## A.3 翻訳と導出

**命題A.2（導出の翻訳）.**
定義1.9の解釈 $`u:\mathbb T\to\mathbb T'`$ について、
$`\mathbb T`$ で導出されたsequentの翻訳は $`\mathbb T'`$ で導出できる。

**証明.**
まず任意のterm $`t`$ について、
$`E_t(\boldsymbol x,y)\wedge E_t(\boldsymbol x,z)\vdash y=z`$ を構文木の帰納法で導出する。
変数の場合は等号規則を用いる。操作適用の場合は二組の存在witnessを取り出し、
各引数の帰納法でそれらを等しくする。等号置換の後、原始graphの一価性を使い、
最後に存在除去する。
この議論は部分操作の場合にも同じである。
束縛式では、先に評価されるtermの一価性で束縛値を等しくし、
本体の一価性を適用する。

全域操作のgraphを $`E_{\tau_f}`$ へ翻訳したとき、その一価性は直前の導出であり、
全域性は解釈が持つ $`\top\vdash\mathrm{Def}_{\tau_f}`$ の導出である。
部分操作の一価性も同じで、
graphからdomainへの含意とdomain上の値の存在は
$`\delta_p\dashv\vdash\exists y\,E_{\tau_p}`$ から得る。
これで全graph構造公理の翻訳が導出された。

任意の導出をその木で帰納する。必須Lawは解釈のLaw導出で置き換える。
切断・真偽・連言・選言・存在の規則は、翻訳後に同じ規則を適用する。
変数のsortは $`u`$ で送り、束縛変数の新鮮さを保つように改名する。
等号置換は、原子関係の翻訳が正の式であっても、式全体への同じ規則として適用できる。
これで導出の翻訳が得られる。□

**補題A.3（termと式の翻訳の比較）.**
解釈 $`u:\mathbb T\to\mathbb T'`$、$`v:\mathbb T'\to\mathbb T''`$ について、
次の相互導出が対応する翻訳先の理論で成り立つ。

```math
\begin{aligned}
E_{u(t)}&\dashv\vdash u(E_t),&
\mathrm{Def}_{u(t)}&\dashv\vdash u(\mathrm{Def}_t),\\
(v\circ u)(\varphi)&\dashv\vdash v(u(\varphi)),&
\mathrm{id}(\varphi)&\dashv\vdash\varphi.
\end{aligned}
```

ここで $`v\circ u`$ の翻訳データは定義1.9の合成候補である。
また、$`u,u':\mathbb T\to\mathbb T'`$ が定義1.9の等号の条件を満たすなら、
任意の正の式 $`\varphi`$ について $`u(\varphi)\dashv\vdash u'(\varphi)`$ であり、
任意のterm $`t`$ について $`E_{u(t)}\dashv\vdash E_{u'(t)}`$ である。

**証明.**
最初のgraph比較をtermの構文木で帰納する。変数の場合は同じsortの等号である。
操作適用 $`e(t_1,\ldots,t_m)`$ の翻訳は、全ての $`u(t_i)`$ を先に評価してから
$`\tau_e`$ を評価する束縛式である。そのgraphは

```math
\exists\boldsymbol z\,
\left(\bigwedge_iE_{u(t_i)}(\boldsymbol x,z_i)
 \wedge E_{\tau_e}(\boldsymbol z,y)\right)
```

と相互に導出できる。入れ子の存在量化からwitnessを順に取り出し、同じwitnessで
逆向きに存在導入すればよい。各引数の帰納法と $`u(G_e)=E_{\tau_e}`$ を使うと、
この式は $`u(E_{e(\boldsymbol t)})`$ となる。空の引数列にも同じ議論が成り立つ。
既存の束縛式については、変数を捕獲しないよう改名して

```math
\begin{aligned}
E_{u(\mathrm{let}\ z=a\ \mathrm{in}\ b)}
 &=\exists z\,(E_{u(a)}\wedge E_{u(b)})\\
 &\dashv\vdash\exists z\,(u(E_a)\wedge u(E_b))\\
 &=u(E_{\mathrm{let}\ z=a\ \mathrm{in}\ b})
\end{aligned}
```

を得る。存在量化して定義可能性の比較も得る。

式の合成比較では、変数の等号は同じ等号に、関係とdomainは定義により
$`v(u(r))`$ と $`v(u(D_p))`$ に送られる。
graph原子では、合成候補の翻訳 $`E_{v(\tau_e^u)}`$ と逐次翻訳
$`v(E_{\tau_e^u})`$ が、直前のgraph比較によって相互に導出できる。
恒等翻訳のgraph原子は $`E_{e(\boldsymbol x)}(\boldsymbol x,y)`$ となり、
式(1.3)の等号witnessを置換・除去すれば $`G_e(\boldsymbol x,y)`$ と相互に導出できる。
他の原子式はそのままである。

相互導出は論理構文子に関して合同的である。連言は各成分の導出を合わせ、
選言は各枝で導出して選言除去を用いる。存在量化はwitnessを取り出して
その文脈で導出し、同じwitnessを存在導入する。$`\top,\bot`$ はそのままである。
これを式の構文木で繰り返すと、合成比較と恒等比較を全ての正の式へ延長できる。

$`u,u'`$ の等号の条件は、各graph・関係・domain原子の翻訳の相互導出であり、
sort写像も等しい。したがって同じ合同性の帰納法で
$`u(\varphi)\dashv\vdash u'(\varphi)`$ を得る。
これを $`\varphi=E_t`$ に用い、最初のgraph比較を両側に合わせると、
$`E_{u(t)}\dashv\vdash E_{u'(t)}`$ となる。□

**命題A.4（理論の圏）.**
定義1.9の合成候補は解釈であり、解釈の等号は左右の合成で保たれる。
同値な解釈を同一視すると、恒等と合成は単位律と結合律を満たす。

**証明.**
合成候補 $`v\circ u`$ の操作termは $`v(\tau_f^u)`$ である。
$`u`$ の全域性の導出を命題A.2で翻訳すると
$`\top\vdash v(\mathrm{Def}_{\tau_f^u})`$ を得る。
補題A.3で右辺を $`\mathrm{Def}_{v(\tau_f^u)}`$ へ移せるので、合成termは全域である。
部分操作についても、翻訳した $`\delta_p^u\dashv\vdash\mathrm{Def}_{\tau_p^u}`$ と
同じ補題から $`v(\delta_p^u)\dashv\vdash\mathrm{Def}_{v(\tau_p^u)}`$ を得る。
各Lawの $`u`$ による導出を $`v`$ で翻訳すれば
$`v(u(\iota_\ell))\vdash v(u(\chi_\ell))`$ となる。
補題A.3の式の合成比較と切断で
$`(v\circ u)(\iota_\ell)\vdash(v\circ u)(\chi_\ell)`$ を得る。
よって合成候補は解釈の全条件を満たす。恒等候補の条件は元のLawとgraph構造公理から従う。

等号の反射性・対称性・推移性は相互導出のそれぞれの性質による。
内側の代表を $`u`$ から $`u'`$ へ取り替えるときは、その原子式の相互導出を
命題A.2で $`v`$ に沿って翻訳し、補題A.3で合成のgraphへ移す。
外側の代表を $`v`$ から $`v'`$ へ取り替えるときは、補題A.3の最後の主張を
$`u`$ の関係式・domain式・操作termのgraphに適用する。
これで合成の等号が両側の代表によらないことを得る。

恒等との合成について、関係式とdomain式には補題A.3の恒等比較を用いる。
操作graphでも、左から恒等を合成した場合は
$`E_{\mathrm{id}(\tau_e^u)}\dashv\vdash\mathrm{id}(E_{\tau_e^u})\dashv\vdash E_{\tau_e^u}`$ である。
右から恒等を合成した場合は
$`E_{u(e(\boldsymbol x))}\dashv\vdash u(E_{e(\boldsymbol x)})\dashv\vdash u(G_e)=E_{\tau_e^u}`$ となる。
後者の第二比較には $`E_{e(\boldsymbol x)}\dashv\vdash G_e`$ の導出を翻訳して用いる。
sort写像も等しいので単位律が成り立つ。

三つの解釈 $`u,v,w`$ の合成では、関係式・domain式の二つの括弧付けは、
補題A.3の合成比較により $`w(v(u(r)))`$、$`w(v(u(D_p)))`$ とそれぞれ相互に導出できる。
操作graphの二つの括弧付けについても

```math
\begin{aligned}
E_{(w\circ v)(\tau_e^u)}
 &\dashv\vdash (w\circ v)(E_{\tau_e^u})
 \dashv\vdash w(v(E_{\tau_e^u})),\\
E_{w(v(\tau_e^u))}
 &\dashv\vdash w(E_{v(\tau_e^u)})
 \dashv\vdash w(v(E_{\tau_e^u}))
\end{aligned}
```

を得る。第二行の最後ではgraph比較の導出を $`w`$ で翻訳する。
sort写像は写像の結合律で等しい。したがって両合成は定義1.9の射として等しく、
理論の圏 $`\mathbf{Th}`$ が得られる。□

[第1章](part_1/chapter_1_atoms_laws_theories.md) · [全体の構成](README.md)
