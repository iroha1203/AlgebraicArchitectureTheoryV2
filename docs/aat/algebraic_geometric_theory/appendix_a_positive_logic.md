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
2. **変数。** 型を保つ変数の改名・置換、文脈への未使用変数の追加を許す。
   束縛変数は捕獲を避けて改名する。
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
部分termの代入は、全ての代入termの値のgraphを前提に追加し、
その値を表す新しい変数を代入してから存在量化することで行う。
これが第1章の定義可能性を伴う代入である。
全域性を導出できるtermでは、その値の存在を証明して同じ規則を使える。
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
したがって、理論解釈の合成は再び理論解釈になる。

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
これで導出の翻訳が得られる。

合成では、操作termにもう一つの翻訳を施す。
原始操作の置換では、第1章の有限の束縛式によって全引数を先に評価する。
その値graphは、元の $`E_t`$ を翻訳した式と相互に導出可能である。
変数の場合は等号である。操作適用の場合には、
式(1.3)の引数のwitnessを順に取り出し、帰納法でそのgraphを置き換え、
翻訳された原始操作のgraphを適用して存在導入する。逆方向も同じwitnessを用いる。
この相互導出により、翻訳された全域性・domainの導出を合成termへ移せる。
Law導出も先の導出木の翻訳で得られるため、合成は定義1.9の全条件を満たす。□

式の同値の導出も翻訳される。したがって、翻訳をLawの下の同値で割った理論の射について、
恒等と合成は代表の選択によらず定まる。

[第1章](part_1/chapter_1_atoms_laws_theories.md) · [全体の構成](README.md)
