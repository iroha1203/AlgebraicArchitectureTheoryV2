# G-134：同じ実生成比較で評価する指定例

[GOAL W](../../goals/G-134-aat-face-relation-subdivision.md)の原始データと証明する値を定める。
以下の次元・余核は、セル表から生成する微分と比較についての証明義務である。
rank・同型・期待値を入力fieldとして供給しない。

## W1. 三角形追加と面削除のpaired witness

### 原始入力

$`\mathrm{Source}=\mathrm{Bool}\times\mathrm{Bool}`$、$`q_c(a,b)=a`$、
$`q_f(a,b)=(a,b)`$ とする。両readingは全射で、$`\pi(a,b)=a`$、
$`q_c\preceq q_f`$ かつ逆向きの順序は成立しない。
Lawは一つ、値型はBool、評価は $`\ell(a,b)=a`$ とする。
adequacyをこの式から証明し、異なる二つの発生ラベル $`\lambda_0,\lambda_1`$ を得る。
すべてのchart台は対応するtarget全体とする。

| セル | 粗側 $`K`$ | 面あり細側 $`K^+`$ | 面なし細側 $`K^-`$ |
| --- | --- | --- | --- |
| 頂点 | $`v,w`$ | $`v,w,v'`$ | $`K^+`$ と同じ |
| 辺 | $`e_1:v\to w,\ k:v\to v`$ | 旧辺と $`c:v\to v',e_2:v'\to w`$ | $`K^+`$ と同じ |
| 面 | なし | $`f=(c,e_1,e_2)`$ | $`f`$ だけを除く |

readingの台の逆像変更と[三角形追加](elementary-moves.md#2-三角形追加)を合成して $`K^+`$ を作る。
原始比較 $`r^+`$ は旧頂点・旧辺を同名へ送り、
$`v'\mapsto v,c\mapsto0,e_2\mapsto e_1,f\mapsto0`$ とする。
$`r^-`$ は同じ頂点・辺の表を使い、面型だけを空にする。
$`j:K^-\hookrightarrow K^+`$ に対して $`r^-=r^+j`$、
cochainでは $`u^- = j^*u^+`$ を証明する。

loop $`k`$ は $`v`$ に接続し、変更部分と同じ連結成分にある。
また異なる $`e_1,e_2`$ が同じ粗辺に写るため、辺の持ち上げの一意性C5の式が破れる。
`r^+` は旧比較型の退化面fieldを満たさず、新比較型で構成する。

### 同じ微分・比較での評価

各ラベルでcoarse cocycleのperiodを $`p_k(z)=z(k)`$ とする。
fine側ではこれに

```math
p_f(z)=z(c)+z(e_2)-z(e_1)
```

を加える。両periodは頂点差分で零になる。$`K^+`$ のcocycle条件は $`p_f=0`$、
$`K^-`$ では $`p_f`$ が独立のperiodになる。
$`k`$ 上だけ1のcochainは両側の非零H¹類を与え、同じ比較がその類を保つ。
$`e_2`$ 上だけ1のcochainは $`K^-`$ で追加の非零余核類を与え、
$`K^+`$ では微分の $`f`$ 成分が1なのでcocycleではない。

これらのperiodで商を同定し、実比較を評価する。

| 一ラベルの実比較 | H¹ | period座標での写像 | 実核・実余核 |
| --- | --- | --- | --- |
| $`u^+`$ | $`\mathbb Q\to\mathbb Q`$ | $`x\mapsto x`$ | $`0,0`$ |
| $`u^-`$ | $`\mathbb Q\to\mathbb Q^2`$ | $`x\mapsto(x,0)`$ | $`0,\mathbb Q`$ |

この座標行列は生成写像の評価結果として証明する。
全Lawでは二ラベルを別々に保持し、$`\operatorname{coker}H^1(u^-)\cong\mathbb Q^2`$、
`blockDefect` は $`(0,2)`$ となる。$`u^+`$ の欠損は $`(0,0)`$。
すべての非空 $`A\subseteq\mathrm{Bool}`$ のsubset複体はこの一ラベルのセル複体であり、
空 $`A`$ の比較は零複体の恒等である。

## W2. 分割の台・面・重複出現

W2a–cでは $`\mathrm{Source}=\{\alpha,\beta\}`$、readingは恒等、
一つのLawを恒等評価にする。各chart台からK1とラベル座標を作り、
[基本変形§3](elementary-moves.md#3-面に接する辺の分割と再三角形化)を適用する。

### W2a. 面に接する辺と一方だけに残る台

三頂点 $`v,w,u`$、辺 $`e:v\to w,a:v\to u,b:w\to u,k:v\to v`$、
面 $`F=(e,a,b)`$ とする。台は
$`S(v)=S(u)=\{\alpha,\beta\},S(w)=\{\alpha\}`$。
$`e`$ を分割し、新しい道の後半を $`b'`$ と書く。
新対角辺は $`d:v\to w`$、中心面は $`F^\circ=(d,a,b)`$、追加面は $`t=(c,d,b')`$。

ラベル $`\alpha`$ では全セルが選択され、$`s(F)=F^\circ+t`$、
$`h_0(v')=c,h_1(d)=-t`$ を実微分に適用する。
ラベル $`\beta`$ では $`w,e,b,F,d,b',t,F^\circ`$ が選択されず、
$`v',c`$ が選択される。ここでも同じ収縮式が成立することを証明する。
両ラベルでloop $`k`$ による非零H¹が保たれる。

### W2b. loopと一面内の三重出現

一頂点 $`v`$、二loop $`e,k`$、面 $`F=(e,e,e)`$、chart台は全体とする。
$`\partial F=e`$ なので $`k`$ が非零H¹を残す。
$`e`$ の分割では $`c:v\to v',b:v'\to v`$、三つの別名のloop $`d_0,d_1,d_2`$、
三つの追加面 $`t_i=(c,d_i,b)`$、中心面 $`F^\circ=(d_0,d_1,d_2)`$ を作る。

```math
s(F)=F^\circ+t_0-t_1+t_2,\qquad h_1(d_i)=-t_i.
```

この符号でchain式と支持条件を証明する。同じ辺の出現を集合として一回にまとめず、
三つの位置から同じ原始incidence係数 $`1-1+1`$ を生成する。
両側の各ラベルH¹は $`k`$ のperiodでℚ、実比較はその恒等になる。

### W2c. 空辺台

二頂点 $`v,w`$、辺 $`e:v\to w`$、面なし、
$`S(v)=\{\alpha\},S(w)=\{\beta\}`$ とする。
辺 $`e`$ のK1台は空であり、両ラベルで辺座標はない。
分割後は $`S(v')=S(c)=\{\alpha\}`$、$`S(b)=\varnothing`$。
$`\alpha`$ 成分の頂点・辺対と $`\beta`$ 成分の恒等から同じ収縮を証明する。
H¹は零であり、この例の義務は空辺台でも操作と生成写像が定義できることにある。

## W3. H¹を保ちH²を変える面の複製

W2aの頂点・辺・面を使い、chart台をすべて全体にする。
既存面 $`F=(e,a,b)`$ の複製 $`\widehat F=(e,a,b)`$ を追加する。
$`r(\widehat F)=F`$、旧セルは恒等とする。

各ラベルで $`k`$ のperiodによりH¹はℚで比較は恒等、H²は $`0\to\mathbb Q`$。
degree 2のcochainの差 $`z(\widehat F)-z(F)`$ は $`d^1`$ の像で零になり、
複製上だけ1のcochainがH²の非零余核類を与える。
同じ生成比較の標準錐はH²がℚとなる。
全Lawでは二成分を保持する。これをGOAL Eの一般操作へ接続する。

## 既存のC5例との関係

[論文例3.25](../../../outreach/paper/rising-sea/ja/06-resolution-invariance.md)のC5行では、
平行二辺を用いる二面が粗面へ写る。
既存 `R1ConditionC5Witness` は、重複した二loopを別々の面で消し、両面を粗面へ送る
別の原始表である。どちらも旧hereditary比較に属する。
W1は三角面を零へ送り、その三辺の像が $`0,-e_1,+e_1`$ と相殺する構成である。
既存のC5例はW1の混在退化・同一連結成分・paired比較の証拠には代用しない。
