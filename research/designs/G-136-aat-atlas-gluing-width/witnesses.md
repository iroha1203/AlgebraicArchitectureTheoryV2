# G-136：全有限幅の原始入力対

この文書の§1–4は[GOAL E](../../goals/G-136-aat-atlas-gluing-width.md)の指定データと
同時成立条件を定める。§5は証明を誤って強めた場合の検査例である。

## 1. 共通Source・reading・セル表

$`k\ge1`$ では $`n=k+1`$、$`k=0`$ では $`n=2`$ とする。
$`C=\mathbb Z/n\mathbb Z`$、$`\mathrm{Source}=C\times\mathrm{Bool}`$、
$`q_c(c,b)=c`$、$`q_f=\mathrm{id}`$。両readingは全射で、生成因子πはfstである。
粗nerveは台Cを持つ一つのchart、辺・面なしとする。

細nerveのchartは相異なる名前 $`v_i,w_i`$ ($`i\in C`$) で、台は

```math
S(v_i)=\{i\}\times\mathrm{Bool},\qquad
S(w_i)=\{i,i+1\}\times\mathrm{Bool}.
```

$`M_k^-`$ の細nerveの有向辺を
$`a_i:v_i\to w_i`$、$`b_i:w_i\to v_{i+1}`$ とし、面は空とする。
これは2n個のchartを持つ一周の有向閉路である。
$`M_k^+`$ は同じchartと台から辺 $`a_0`$ だけを除いた有向pathとする。
比較は全chartを粗chartへ、全辺をnoneへ送る。face写像は空写像。
端点像一致は一つの粗chartで成立し、chart台包含はfstによって成立する。
したがって両比較は旧hereditary条件も満たし、G-134の原始比較へ埋め込める。

K1が強制する辺台は、$`n\ge2`$ より

```math
S(a_i)=\{i\}\times\mathrm{Bool},\qquad
S(b_i)=\{i+1\}\times\mathrm{Bool}.
```

面のincidence条件は空の面型について成立する。期待するrankや欠損はfieldへ含めない。
旧候補のn角形で全chart台を隣接二概念にすると、n=2では両端台がともにCになり、
指定したsingleton辺台とK1が一致しない。singleton/pairを交互に置く上の表では、
n=2でも四角形の各辺台が正しいsingletonになる。

## 2. 全部分集合のH¹と比較

$`X\subseteq C`$ の細選択は $`\pi^{-1}X=X\times\mathrm{Bool}`$ とする。
原始表から次の選択式を導く。

| セル | 選択条件 |
| --- | --- |
| $`v_i`$ | $`i\in X`$ |
| $`w_i`$ | $`i\in X\lor i+1\in X`$ |
| $`a_i`$ | $`i\in X`$（plusではa₀を除く） |
| $`b_i`$ | $`i+1\in X`$ |

Xが真部分集合なら欠けた概念jのchart $`v_j`$ とその二つの接続辺が消える。
選択されたグラフは閉路から頂点と辺を除いたforestとなる。
plus側は全Xでpathの部分グラフである。
各連結成分の根から辺値を積分して、全1-cochainがd⁰の像であることを示す。
空Xでは全次数が零。粗側は非空Xで一点、空Xで空なので、常にH¹零である。

minus側の全Cでは

```math
\operatorname{per}(z)=\sum_{i\in C}(z(a_i)+z(b_i))
```

がd⁰の像で零になる。per=0のcochainに累積和で原始関数を与え、
$`H^1C_{f,C}\cong\mathbb Q`$ を構成する。
a₀に1、他の辺に0を置いたcochainのperiodは1で、非零生成元を与える。
粗H¹が零なので、比較は零からこのH¹への射である。
これにより全Xの実H¹比較と `blockDefect` を計算する。

| 入力 | Xが真部分集合 | X=C | 全Xで零欠損 |
| --- | --- | --- | --- |
| $`M_k^+`$ | H¹は粗細とも零、J=(0,0) | 同左 | 成立 |
| $`M_k^-`$ | H¹は粗細とも零、J=(0,0) | 粗H¹=0、細H¹≅ℚ、J=(0,1) | 不成立 |

$`|X|\le k<n`$ なら真部分集合なので、低幅の全H¹比較には一意な零空間同型がある。
もし一様性がこの観測を通る関数で決まれば、同じ観測値に二つの異なる真偽値を与えることになり矛盾する。
k=0はn=2の同じ四角形/pathを用い、観測対象X=∅の零複体と、全Cの非零periodを別々に評価する。

## 3. Law・値クラス・幅

任意の粗adequate LawはC上の値写像に降下する。
λ=(law,value)の値クラスを $`A_\lambda\subseteq C`$ とすると、
細値クラスは $`A_\lambda\times\mathrm{Bool}`$。
Boolの二つの発生点から同じcell/law/value座標が二つ生じることはなく、
既存 `CellCoordinate.ext` と `LawValueLabel` の等号で一つに同定される。
一方、lawまたはvalueが異なるラベルは台が等しくても別成分である。

Law族の幅k条件は、**全発生ラベルλについて $`|A_\lambda|\le k`$** とする。
この条件から§2を各blockに適用し、G-134の全Law同定・欠損和で両入力のH¹とJが一致する。
空Law族も含む。k=0では発生値クラスは非空なので、許容Law族は空族になる。
H¹ block観測のk=0の主張は、これとは別に§2のX=∅で成立する。

`indicator` Law $`\ell_X(c,b)=1_X(c)`$ の粗adequacyをfst分解で証明する。
真の値クラスはX、偽の値クラスはC\Xであり、発生する両方を数える。
$`0<|X|<n=k+1`$ なら両クラスは幅k以下。
X=∅またはCのとき、唯一の発生値クラスはCで、幅kの観測には入らない。
述語の短い記述や指定されたXだけをLaw族全体の観測幅と数えない。

非一様性の証拠には一つの定数Law $`\ell(c,b)=\star`$ を固定する。
唯一の値クラスがCであり、実 `generatedComparisonH1Map` の欠損は
plusで(0,0)、minusで(0,1)になる。同じSource、readingと生成比較から得る値である。

## 4. 同じ閉路によるMVの非零生成元

minus入力を使い、$`A=\{0\}`$、$`B=C\setminus A`$ とする。
細Aは $`w_{-1}\to v_0\to w_0`$ のpath、細Bは残りのpathで、両方が連結である。
細交差Iは $`w_{-1},w_0`$ の二点、粗A・B・Iは全て一点。
辺台はsingletonなので、交差に辺はない。
しかしA∩B=∅なので、そのtarget部分集合が選ぶ細nerveは空である。

H⁰差制限は粗側 $`\mathbb Q^2\to\mathbb Q,(x,y)\mapsto x-y`$、
細側 $`\mathbb Q^2\to\mathbb Q^2,(x,y)\mapsto(x-y,x-y)`$。
従って $`Q_c=0`$、$`Q_f=\mathbb Q^2/\Delta\mathbb Q\cong\mathbb Q`$、qは0→ℚ。
局所・交差のH¹は全て零なのでP_c=P_f=Z=0である。

交差の順序を $`(w_{-1},w_0)`$ とし、z=(0,1)を取る。
A上の0-cochain xを $`x(w_{-1})=x(v_0)=0,x(w_0)=1`$、B側を0とすれば、
差制限はzである。dxはa₀に1、b₋₁に0、B側微分は全零となる。
Uへの貼り合わせは§2のperiod=1のcochainであり、標準δの符号もここで固定できる。
よってCのhidden包含は、この同じ非零H¹類を生む。

G-135の固定U分解でも、粗chart上の順像係数は連結成分関数ℚでH¹零、
chart逆像fiberは全閉路、面なしでτ=0となる。
その `ker τ` の生成元と、MVから得たhiddenの生成元を既存実商で照合する。
局所A・Bではfiberがpathで、同じ固定領域の保存条件が成立する。

## 5. 強すぎる推論を検出する検査例

低幅観測をH⁰やcochain全体の一致に強めると上の族は使えない。
例えばn=2、X={0}で、minus細部は三頂点のpath、plusはa₀を除いて孤立点を一つ持つ。
細H⁰の次元はそれぞれ1と2、H¹は両方零である。
これは本目標の観測定義を特定するための実計算である。

また、全台を同じ非空集合とした二点・辺なしのfineを一点のcoarseへ送れば、
H¹比較は同型0→0だがH⁰は対角写像ℚ→ℚ²である。
標準錐H⁰はその余核ℚを持つので、一次零欠損から錐acyclicを推論する補題は偽になる。
新規SESの証明時は、この入力を構成的な回帰例として用いる。
