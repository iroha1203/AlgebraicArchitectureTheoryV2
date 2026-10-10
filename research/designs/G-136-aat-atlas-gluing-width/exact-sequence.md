# G-136：原始セルからのMayer–Vietoris列

記号と量化は[GOAL T0・A–D](../../goals/G-136-aat-atlas-gluing-width.md)に従う。
以下は新規構成の証明方針であり、既存の証明済み宣言は[再利用対応](reuse-map.md)で区別する。

## 1. セル集合の完全性

各セルの台Sについて、$`S\cap(A\cup B)\ne\varnothing`$ は
$`S\cap A\ne\varnothing\lor S\cap B\ne\varnothing`$ と同値である。
したがって和のcochainは、AとBのcochainのうち同じ交差セルで一致する組に対応する。
交差Iは二つの非空条件の積であり、一点が $`A\cap B`$ に属するという条件とは異なる。

SESの単射は二つの制限。核の貼り合わせは、A所属セルではx、残りではyを読む。
交差での一致から所属判定によらないことを証明する。
差制限の次数別全射性は、I上のzをAのセルへ零延長し、B側を零とすることで得る。
この零延長は**次数別の線形切断**であり、一般にはcochain射ではない。
微分との可換性は制限射だけに対し、incidence閉性から証明する。

粗細比較との正方形は、mappedセルの同じ値とcollapsedセルの零を次数別に照合する。
Iの台の二点は別々に輸送できるため、追加の「共通点を持つ」仮定を要しない。

## 2. 標準連結射と錐

零延長後のSESへ `CategoryTheory.ShortComplex.ShortExact` のコホモロジー列APIを適用する。
交差上のn-cocycle zを差制限で持ち上げた組(x,y)について、
$`(dx,dy)`$ は差制限の核に入り、U上の $`(n+1)`$-cocycle wに一意に貼り合う。
$`\delta_s[z]=[w]`$ とし、持ち上げ・代表元の変更によらないことを示す。
`δ_eq` と実微分を照合し、差制限を $`x|-y|`$ とした符号を固定する。

錐はG-133の `zeroExtensionMap` とmathlib `mappingCone` をそのまま使う。
`coneCoordinateEquiv` の座標順は $`C_f^m\times C_c^{m+1}`$ であり、
微分は $`(y,x)\mapsto(d_fy+u(x),-d_cx)`$ に対応する。
領域の制限・差制限を両座標へ適用すると錐のSESができる。
次数別完全性はfine側mとcoarse側m+1のSESから得る。
得た錐の連結射にも同じ持ち上げ式を与える。錐の支えは次数−1〜2だが、
長完全列のstatementは全整数次数で置く。

局所H¹同型だけでは $`\operatorname{coker}H^0(u_X)`$ や
$`\ker H^2(u_X)`$ の消滅は従わない。G-133の `cone_short_exact` が
この寄与を保持するので、錐を一次欠損そのものと定義し直す必要はない。

## 3. H⁰・H¹からの短完全列比較

MV列の該当部分は

```math
H^0C_{s,A}\oplus H^0C_{s,B}\xrightarrow{r_s^0}H^0C_{s,I}
\xrightarrow{\delta_s}H^1C_{s,U}
\xrightarrow{t_s}H^1C_{s,A}\oplus H^1C_{s,B}
\xrightarrow{r_s^1}H^1C_{s,I}.
```

`ShortExactFive` へこの三つの完全性を渡し、
$`Q_s=H^0C_{s,I}/\operatorname{im}r_s^0`$ と
$`P_s=\ker r_s^1`$ の間の短完全列を得る。
Qの包含は $`[z]\mapsto\delta_s[z]`$、Pへの射は $`[w]\mapsto t_s[w]`$ である。
qは $`H^0(u_I)`$ の商写像、pは局所H¹比較の直和をPへ制限した写像とする。
H⁰の局所比較を含む正方形が、qがwell-definedであることを保証する。

この二行の短完全列からsnakeを適用する。一般のsnake連結射は次の追跡で作る。
$`a\in\ker p`$ を $`b\in H^1C_{c,U}`$ に持ち上げると、$`T_U b`$ のP像は零なので、
一意な $`z\in Q_f`$ の像となる。$`\partial_{\rm sn}(a)=[z]\in\operatorname{coker}q`$。
選択の変更はqの像の差を生み、代表元によらない。
新しい完全性仮定を置かず、AのSESから得た列に標準snakeを接続する。

## 4. 局所一次診断保存の下での同定

$`T_A,T_B`$ が同型なら、その直和 $`L`$ も同型で、pは単射になる。
pの余核は次の写像で計算できる。

```math
P_f\longrightarrow H^1C_{c,I},\qquad
y\longmapsto r_c^1(L^{-1}y).
```

その像は $`Z=\operatorname{im}r_c^1\cap\ker H^1(u_I)`$、核は $`p(P_c)`$。
像への全射性は、$`z=r_c^1(x)`$ かつ $`H^1(u_I)z=0`$ なら
$`Lx\in P_f`$ となることから得る。
よって $`\operatorname{coker}p\cong Z`$。snakeの $`\ker p=0`$ を消去してGOAL Cの式を得る。

phantomの同定はQの包含の核への制限である。
hiddenへの $`\operatorname{coker}q`$ の包含は
$`[z]\mapsto[\delta_f z]`$、hiddenからZへの射は
$`[b_f]\mapsto r_c^1(L^{-1}t_f b_f)`$ である。
同次元のベクトル空間を選び直す構成に置き換えない。
短完全列の分裂を自然な構成として要求せず、射・完全性・次元加法を保持する。

局所J零に加えてq同型とZ零を証明できれば合併でもJ零になる。
逆方向も同じ短完全列から従う。
qの情報は交差H⁰比較と局所H⁰差制限をともに用いるので、Jの数値三つだけでは代替できない。

## 5. LawとG-135への接続

各ラベルλで領域を $`A\cap A_\lambda,B\cap A_\lambda`$ とし、
交差はその二つの**選択セルの交差**を取る。
有限ラベルごとにA–Cを適用し、直和を作る。
$`A_\lambda\subseteq A\cup B`$ のとき合併は既存λ-block全体であり、
G-134の `lawFiberH1Comparison_square` と全三次数同定から実Law比較へ戻せる。
空Law族は零複体、同じ台の異なるラベルは別の直和成分になる。

G-135から用いる式の記号は、MVの $`P_s,Q_s,q`$ と区別する。
通常領域XにおけるG-135の二射を $`\eta_X,\varepsilon_X`$、
順像複体を $`\mathcal P_X`$、fiber項を $`R_X`$、連結射を $`\tau_X`$ と書く。
既存の $`u_X=\varepsilon_X\eta_X`$、核同型、余核SESを同じT_Xへ輸送する。
特にUでは、領域方向の余核SESと係数・fiber方向の余核SESが
同じ $`H^1C_{f,U}/\operatorname{im}T_U`$ を中間項に持つことを示す。
二つのSESの両端を相互に同型とする主張は要求しない。

G-135の台包含自然性はU→A、U→Bの通常部分集合の制限に使える。
真のIは一つのtarget部分集合で表示できるとは限らないため、Iの比較とMVはAの構成で扱う。
