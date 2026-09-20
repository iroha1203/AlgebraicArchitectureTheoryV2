# 準備と記法

集合、群、環、加群の基本事項と、圏、関手、自然変換を前提とする。

## P.1 集合と圏の大きさ

自然数は $`\mathbb{N}=\{0,1,2,\ldots\}`$ とし、整数環と有理数体をそれぞれ
$`\mathbb{Z}`$、$`\mathbb{Q}`$ と書く。集合 $`I`$ で添字づけられた族を
$`(X_i)_{i\in I}`$ と表す。有限族とは、添字集合 $`I`$ が有限である族をいう。
各 $`X_i`$ の有限性は、添字集合の有限性とは別の条件である。

集合の大きさは、選択公理を含む古典的な集合論と Grothendieck 宇宙で扱う。
必要な宇宙 $`\mathbb{U}\in\mathbb{V}`$ を固定し、$`\mathbb{U}`$ に属する集合を
$`\mathbb{U}`$-小さい集合と呼ぶ。小さい集合と写像の圏を
$`\mathbf{Set}_{\mathbb{U}}`$ と書き、この圏自体は大きい宇宙 $`\mathbb{V}`$ で扱う。
用いる宇宙が明らかな箇所では、添字を省いて $`\mathbf{Set}`$ と書く。

圏 $`\mathcal{C}`$ が $`\mathbb{U}`$-小さいとは、その対象全体と射全体が
$`\mathbb{U}`$-小さい集合をなすことをいう。各対象対 $`X,Y`$ の射集合が
$`\mathbb{U}`$-小さいとき、$`\mathcal{C}`$ は局所的に $`\mathbb{U}`$-小さいという。
$`\mathbb{U}`$-小さい圏と同値な圏を、本質的に $`\mathbb{U}`$-小さい圏と呼ぶ。
関手圏を含む構成には、その対象と射を収める大きさの宇宙を用いる。

## P.2 写像、射、合成

写像 $`f:X\to Y`$ と $`g:Y\to Z`$ の合成は

```math
gf=g\circ f:X\longrightarrow Z,
\qquad (gf)(x)=g(f(x))
```

と書く。右側の写像が先に作用する。圏の射と関手にも同じ合成順序を用いる。
対象 $`X`$ の恒等射は $`\mathrm{id}_X`$、圏 $`\mathcal{C}`$ の恒等関手は
$`\mathrm{Id}_{\mathcal{C}}`$ と表す。

写像 $`f:X\to Y`$、部分集合 $`S\subseteq X`$、$`T\subseteq Y`$ に対し、
像を $`f(S)`$、原像を $`f^{-1}(T)`$、制限を $`f|_S:S\to Y`$ と書く。
$`y\in Y`$ 上の fiber は

```math
X_y=f^{-1}(\{y\})=\{x\in X\mid f(x)=y\}
```

である。全単射は $`f:X\xrightarrow{\sim}Y`$ と表し、その逆写像を
$`f^{-1}:Y\to X`$ と書く。

圏 $`\mathcal{C}`$ の対象全体を $`\mathrm{Ob}(\mathcal{C})`$、
$`X`$ から $`Y`$ への射集合を $`\mathrm{Hom}_{\mathcal{C}}(X,Y)`$ とする。
圏が明らかな場合には後者を $`\mathrm{Hom}(X,Y)`$ と略す。
射 $`f:X\to Y`$ が同型であるとは、$`f^{-1}:Y\to X`$ が存在して
$`f^{-1}f=\mathrm{id}_X`$、$`ff^{-1}=\mathrm{id}_Y`$ となることをいう。
同型な対象を $`X\cong Y`$、$`X`$ の自己同型群を
$`\mathrm{Aut}_{\mathcal{C}}(X)`$ と書く。

図式の可換性は、同じ始域と終域を持つ経路の合成が等しいことを表す。
たとえば $`f:X\to Y`$、$`f':X'\to Y'`$、$`a:X\to X'`$、$`b:Y\to Y'`$
からなる正方形の可換条件は $`bf=f'a`$ である。
自然同型を介する比較では、その自然同型を図式のデータとして指定する。

## P.3 関手、自然変換、圏同値

関手 $`F:\mathcal{C}\to\mathcal{D}`$ の対象と射への作用を、それぞれ $`F(X)`$、
$`F(f)`$ と書く。反対圏を $`\mathcal{C}^{\mathrm{op}}`$ と表し、反変関手は
$`\mathcal{C}^{\mathrm{op}}`$ を始域とする関手として記述する。

関手 $`F,G:\mathcal{C}\to\mathcal{D}`$ の間の自然変換 $`\alpha:F\Rightarrow G`$ は、
各対象 $`X`$ に射 $`\alpha_X:F(X)\to G(X)`$ を対応させる族であり、
各射 $`f:X\to Y`$ に対して

```math
G(f)\alpha_X=\alpha_YF(f)
```

を満たす。各 $`\alpha_X`$ が同型であるとき、$`\alpha`$ を自然同型と呼び、
$`\alpha:F\xRightarrow{\sim}G`$ と表す。自然変換
$`\alpha:F\Rightarrow G`$、$`\beta:G\Rightarrow H`$ の合成は、
$`(\beta\alpha)_X=\beta_X\alpha_X`$ で与えられる。

関手 $`F:\mathcal{C}\to\mathcal{D}`$ が充満忠実であるとは、すべての対象対 $`X,Y`$ について

```math
F_{X,Y}:\mathrm{Hom}_{\mathcal{C}}(X,Y)
\longrightarrow\mathrm{Hom}_{\mathcal{D}}(F(X),F(Y)),
\qquad f\longmapsto F(f)
```

が全単射であることをいう。すべての $`D\in\mathrm{Ob}(\mathcal{D})`$ が
ある $`F(X)`$ と同型であるとき、$`F`$ は本質的全射であるという。

圏同値 $`\mathcal{C}\simeq\mathcal{D}`$ は、関手
$`F:\mathcal{C}\to\mathcal{D}`$、$`G:\mathcal{D}\to\mathcal{C}`$ と自然同型

```math
\eta:\mathrm{Id}_{\mathcal{C}}\xRightarrow{\sim}GF,
\qquad
\varepsilon:FG\xRightarrow{\sim}\mathrm{Id}_{\mathcal{D}}
```

によって与える。$`G`$ を $`F`$ の準逆と呼ぶ。
圏、関手、自然変換、圏同値の標準的な定義は
[Stacks, Tag 0013](https://stacks.math.columbia.edu/tag/0013) に従う。

## P.4 係数と代数の記法

係数環 $`k`$ は単位元を持つ可換環とし、環準同型は単位元を保つものとする。
可換環の圏を $`\mathbf{CommRing}`$、アーベル群の圏を $`\mathbf{Ab}`$ と書く。
$`k`$-加群では $`1m=m`$ を仮定し、その圏を $`\mathrm{Mod}_k`$ と表す。
可換 $`k`$-代数は、可換環 $`A`$ と構造準同型 $`k\to A`$ の組である。
環には零環も含める。可換単位環と単位的加群の規約は
[Stacks, Tag 0006](https://stacks.math.columbia.edu/tag/0006)、
[Tag 00AQ](https://stacks.math.columbia.edu/tag/00AQ) と同じである。

環 $`A`$ のイデアル $`I`$ による商環を $`A/I`$、加群 $`M`$ の部分加群 $`N`$ による
商加群を $`M/N`$ と書く。加群の間の線形写像全体を $`\mathrm{Hom}_k(M,N)`$、
準同型 $`u`$ の核と像を $`\ker u`$、$`\mathrm{im}\,u`$ と表す。
アーベル群と加群の演算は加法記法を用い、零元と零写像を文脈に応じて $`0`$ と書く。
一般の群と自己同型群は乗法記法を用い、単位元を $`1`$ と書く。

係数環を固定したテンソル積は $`M\otimes_k N`$ と表す。
係数環の変更には環準同型 $`\varphi:k\to k'`$ を指定し、これに沿う加群の
スカラー拡大を $`k'\otimes_k M`$ と書く。

## P.5 番号と文献の参照

定義・定理・補題・命題・系・例には、本論の章ごとに共通の通し番号を付ける。
たとえば「定義2.1」「補題2.2」「定理2.3」は、いずれも第2章の項目を指す。
節、式、図、表はそれぞれ章ごとに番号を付け、「§2.1」「式(2.1)」「図2.1」「表2.1」
と参照する。準備節の番号には P、付録の番号には A、B、C を章番号の代わりに用いる。

文献は [Stacks] のような識別子と、参照する節・定理番号などを併記する。
The Stacks Project の参照には、節番号に加えて固定識別子である Tag を用いる。
書誌情報は[文献一覧](14-references.md)にまとめる。
