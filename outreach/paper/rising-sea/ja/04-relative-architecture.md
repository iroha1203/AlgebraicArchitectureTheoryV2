# 第1章 相対的アーキテクチャの構成

## 本章の概要

本章では、ソフトウェアの構造を比較するための対象と写像を構成する。
何を構造として読み、どの操作や法則を保つかという選択を明示することが、その出発点となる。

たとえば、表示値と内部値からなる状態を考える。読取りは表示値を返し、
更新は内部値を保って表示値を差し替える。状態の表し方を変更しても表示が同じなら、
読取りは保たれる。しかし、変更してから更新する場合と、更新してから変更する場合とで、
最終状態まで一致するとは限らない。読取りと更新の両方を保つには、
二つの順序で同じ結果になることも必要である。

このような比較には、対象の構造と、操作がその構造にどう作用するかの両方が要る。
AATでは、型付きの原始的事実をAtom、その族に関係を加えたものをconfiguration、
さらに状態集合や操作の解釈などを保持したものをarchitecture objectと呼ぶ。
対象が満たすべき方程式をLawとして定め、部分ごとに情報を読み、貼り合わせるための
局所構造を与える。これらの構成で用いる語彙、抽出規則、対象形成、方程式、操作、
局所性の選択をreadingと呼ぶ。アーキテクチャをreadingに相対化するとは、
この選択を対象とともに明示することである。

本章の構成と主要な結果は、次のとおりである。

| 問い | 構成 | 得られるもの |
| --- | --- | --- |
| 何を対象とし、どの操作を許すか | Atom族に関係・構造・操作を与える | 操作で閉じた対象族を持つcore（§§1.1–1.4、定理1.18） |
| どの情報を局所的に読み、貼り合わせるか | 文脈・被覆・係数を選ぶ | siteと文脈ごとの環を備えた幾何（§§1.5–1.6） |
| readingを変えるとき、何を保つか | 各段階のデータを比較する射を定める | 抽出・core・幾何を結ぶ射影の塔（§1.7、定理1.31） |
| 既存のCSの意味論をどう表すか | lensとプロトコルから対象・操作・Lawを構成する | 法則の成立の同値と意味保存射の回復（§§1.8–1.10、命題1.41・1.43） |

## 1.1 Atomと相対的な抽出

一つの事実を識別するには、その内容に加えて、何について、どの観点から述べた事実かを
指定する必要がある。Atomは、この情報を五つの座標で持つ。

**定義1.1（Atomの語彙）.**
種別、軸、対象、述語、内容の集合を、それぞれ
$`K`$、$`X`$、$`S`$、$`P`$、$`T`$ とする。
Atomの集合 $`\mathrm{At}`$ は空でない集合であり、写像

```math
\begin{aligned}
\mathrm{kind}&:\mathrm{At}\to K,&
\mathrm{axis}&:\mathrm{At}\to X,&
\mathrm{subject}&:\mathrm{At}\to S,\\
\mathrm{predicate}&:\mathrm{At}\to P,&
\mathrm{payload}&:\mathrm{At}\to T
\end{aligned}
```

を持つ。これらをまとめた
$`\mathrm{At}\to K\times X\times S\times P\times T`$ は単射とする。
したがって、五つの座標がすべて等しいことと、二つのAtomが等しいことは同値である。
種別は事実の種類、軸は着目する構造、対象はその事実が何について述べるかを表す。
述語と内容は、その対象について何を述べるかを与える。
たとえば、構成要素の存在、名前付き操作、ある対象の状態量、
二つの対象の間の関係を、それぞれ異なる種別のAtomで表せる。
内容には名前、型、値などを置く。
同時に扱う事実はAtomの族へ、それらの関係はconfigurationへまとめる。

**定義1.2（Atom族）.**
Atom族は部分集合 $`F\subseteq\mathrm{At}`$ である。そのsupportと、
軸 $`x\in X`$ への制限を

```math
\mathrm{supp}(F)=\{\mathrm{subject}(a)\mid a\in F\},
\qquad
F|_x=\{a\in F\mid \mathrm{axis}(a)=x\}
```

と定める。Atom族の有限性は $`F`$ の有限性をいう。
抽出される族は一般には無限でもよい。§1.2のcomposition readingには、有限な族を入力する。

抽出元のデータをsourceと呼ぶ。同じsourceでも、語彙や解像度の選択によって
抽出する事実は変わり得る。その選択と、Atomを採用する条件をまとめたものが抽出doctrineである。

**定義1.3（抽出doctrine）.**
抽出doctrine $`D`$ は、sourceの集合 $`\mathrm{Src}_D`$、
語彙・意味・解像度のパラメータ $`v_D,\gamma_D,\rho_D`$、
sourceの正規化写像 $`N_D:\mathrm{Src}_D\to\mathrm{Src}_D`$ と、
次の四つの述語からなる。

| 述語 | 意味 |
| --- | --- |
| $`V_D(v,a)`$ | 語彙 $`v`$ がAtom $`a`$ を許す |
| $`M_D(\gamma,s,a)`$ | 意味reading $`\gamma`$ がsource $`s`$ で $`a`$ を許す |
| $`R_D(\rho,s,a)`$ | 解像度 $`\rho`$ が $`s`$ で $`a`$ を許す |
| $`E_D(s,a)`$ | sourceの意味論で $`a`$ が成立する |

sourceを正規化した後、四つの条件をすべて満たすAtomを採用する。
抽出述語と抽出族を

```math
\begin{aligned}
\mathrm{Extracts}_D(s,a)
&\Longleftrightarrow
V_D(v_D,a)\land M_D(\gamma_D,N_D(s),a)\\
&\hspace{2em}\land R_D(\rho_D,N_D(s),a)\land E_D(N_D(s),a),\\
\mathrm{Atomize}_D(s)
&=\{a\in\mathrm{At}\mid \mathrm{Extracts}_D(s,a)\}
\end{aligned}
```

で定める。$`N_D`$ にはこの段階で写像としての構造を用い、冪等性が必要な構成では
それを追加の条件として明記する。

**命題1.4（抽出族の存在と一意性）.**
$`D`$ と $`s\in\mathrm{Src}_D`$ を固定する。このとき

```math
\forall a\in\mathrm{At},\qquad
a\in F\ \Longleftrightarrow\ \mathrm{Extracts}_D(s,a)
```

を満たすAtom族 $`F`$ がただ一つ存在する。

**証明.**
定義1.3の $`\mathrm{Atomize}_D(s)`$ がこの条件を満たす。
二つの族 $`F,G`$ が条件を満たすなら、任意のAtomについて
$`a\in F\Longleftrightarrow a\in G`$ であるから、集合の外延性により $`F=G`$ となる。□

この一意性が固定するのは、sourceとdoctrineに対する事実の族である。
その族の読取りは別の写像 $`o:F\to Y`$ として与えられる。
$`o(a)=o(b)`$ となる異なるAtomがあれば、この読取りでは両者が区別されない。
したがって、抽出族の構成と、その族からどれだけの情報を読み取るかを、別々に記述できる。

## 1.2 Configuration、対象、操作

Atom族は、採用した事実の集まりである。それらを一つの対象として扱うには、
事実同士の関係と、状態集合や操作の解釈を加える。
関係までをconfigurationに、具体的な構造データまでをarchitecture objectに保持する。

**定義1.5（Configuration）.**
configurationは三つ組 $`C=(F_C,R_C,I_C)`$ である。
ここで $`F_C\subseteq\mathrm{At}`$、
$`R_C,I_C\subseteq\mathrm{At}\times\mathrm{At}`$ とする。
$`R_C`$ は関係、$`I_C`$ は指定された同一視を表す。
同一視を同値関係として使う場合は、その反射性・対称性・推移性を要求する。
$`R_C,I_C\subseteq F_C\times F_C`$ のとき、関係と同一視は族に支えられているという。

composition readingは、各有限族 $`F`$ に

```math
\mathrm{Comp}(F)=(F,R_F,I_F),
\qquad R_F,I_F\subseteq F\times F
```

を対応させる規則である。有限な部分族へ関係と同一視を制限したconfigurationをmoleculeと呼ぶ。
これは、局所的な構造を比較する際に、複数のAtomを関係ごと扱うための有限単位である。

**定義1.6（Architecture object）.**
architecture objectは $`A=(C_A,S_A,Q_A)`$ である。
$`C_A`$ はconfiguration、$`S_A`$ は選んだ型の構造データ、
$`Q_A`$ は選んだ型の量であり、それぞれの型も対象のデータに含める。
構造データには、状態集合と遷移写像、グラフ、図式、代数などを置ける。
量には、指定値や評価結果を置ける。
このような対象全体を、必要な大きさの宇宙で $`\mathrm{ArchObj}(\mathrm{At})`$ と書く。

object readingは、configuration $`C`$ を
$`C_{\mathrm{Form}(C)}=C`$ を満たす対象 $`\mathrm{Form}(C)`$ へ送る規則である。
この規則を固定すると、有限族から

```math
F\longmapsto \mathrm{Comp}(F)\longmapsto
\mathrm{Form}(\mathrm{Comp}(F))
```

という構成を得る。configurationを同じに保ったまま、状態集合や操作の解釈を変える
こともでき、その場合は異なるarchitecture objectになる。

**定義1.7（Configurationの射とoperation）.**
対象間の操作には、Atom・関係・同一視への作用が伴う。
この作用を表すのがconfigurationの射である。

configurationの射 $`h:C\to D`$ は写像
$`h_{\mathrm{At}}:\mathrm{At}\to\mathrm{At}`$ であって、

```math
\begin{aligned}
a\in F_C&\Longrightarrow h_{\mathrm{At}}(a)\in F_D,\\
(a,b)\in R_C&\Longrightarrow
(h_{\mathrm{At}}(a),h_{\mathrm{At}}(b))\in R_D,\\
(a,b)\in I_C&\Longrightarrow
(h_{\mathrm{At}}(a),h_{\mathrm{At}}(b))\in I_D
\end{aligned}
```

を満たすものをいう。恒等写像と写像の合成によりconfigurationは圏をなす。
実際、三つの含意はいずれも恒等写像で成立し、合成について閉じている。

operation readingは、対象対ごとの集合 $`\mathrm{Op}(A,B)`$ と写像

```math
d_{A,B}:\mathrm{Op}(A,B)\longrightarrow
\mathrm{Hom}(C_A,C_B)
```

からなる。$`o\in\mathrm{Op}(A,B)`$ を $`A`$ から $`B`$ へのoperationと呼ぶ。
operationは自身の名前や追加データを保持し、$`d_{A,B}`$ はそのconfigurationへの
作用を与える。二つのoperationの作用が等しい場合にも、operation自体は区別して扱う。
恒等operationと合成を指定して単位則・結合則を満たし、$`d`$ がそれらを保つなら、
対象とoperationは圏をなす。

**例1.8（同じ作用を持つ名前付き操作）.**
状態集合 $`\{0,1\}`$ 上の二つの操作を $`e_1,e_2`$ とし、
どちらも恒等写像として作用するとする。操作集合を
$`\{e_1,e_2\}`$ としておけば、その実行結果が等しくても
$`e_1`$ に対して指定した条件と $`e_2`$ に対して指定した条件を区別できる。
§1.10では、操作名をAtomに含めたconfigurationの射を実際に構成する。

**定義1.9（Invariantとsignature）.**
操作で保ちたい値や性質をinvariantとして指定し、
比較に使う値の組をsignatureとしてまとめる。

関数型のinvariantは写像 $`I:\mathrm{ArchObj}(\mathrm{At})\to V_I`$、
述語型のinvariantは対象上の述語 $`P(A)`$ である。
operation $`o:A\to B`$ による保存とは、それぞれ
$`I(A)=I(B)`$、$`P(A)\Rightarrow P(B)`$ をいう。
順序付き量については、$`I(B)\leq I(A)`$ という条件も別に指定できる。
invariant readingは、添字集合を選び、各添字に関数型または述語型のinvariantを指定する。

signature readingは、軸の集合 $`\Lambda`$、各軸の値域 $`V_\lambda`$、
選択された軸の部分集合 $`\Lambda_{\mathrm{sel}}`$ と、
各対象についての値 $`q_\lambda(A)\in V_\lambda`$ からなる。
対象のsignatureは $`(q_\lambda(A))_{\lambda\in\Lambda_{\mathrm{sel}}}`$ である。
有限個の軸を選べば有限の多軸表現を得る。

## 1.3 局所文脈とLaw

対象の全情報を一度に扱う代わりに、一部の構造や観測値を取り出すことを考える。
どの位置で、どの軸に沿って、何を読めるかを指定するものが文脈である。
文脈上の方程式を、値が零なら成立する「残差」の形で表すことで、局所的にLawを評価できる。

**定義1.10（文脈と制限）.**
対象 $`A`$ の文脈 $`W`$ は、三つの集合
$`\mathrm{Supp}(W)`$、$`\mathrm{Ax}(W)`$、$`\mathrm{Obs}(W)`$ と、

```math
\mathrm{reads}_W\subseteq\mathrm{Supp}(W)\times\mathrm{At},
\quad
\mathrm{readAx}_W\subseteq\mathrm{Ax}(W),
\quad
\mathrm{readObs}_W\subseteq\mathrm{Obs}(W)
```

を持つ。$`\mathrm{Obs}(W)`$ の元をobservableと呼ぶ。
$`\mathrm{reads}_W(s,a)`$ なら $`a\in F_{C_A}`$ とする。
supportの元はAtomを読む位置であり、定義1.2のsubjectの集合とは役割が異なる。
必要な追加データも文脈に含める。

文脈readingは、文脈の小さい前順序を選ぶ。
$`W'\leq W`$ は、$`W`$ で得たデータを $`W'`$ へ制限できる向きを表す。
各 $`W'\leq W`$ に対して、写像

```math
\mathrm{Supp}(W')\longrightarrow\mathrm{Supp}(W),\qquad
\mathrm{Ax}(W')\longrightarrow\mathrm{Ax}(W),\qquad
\mathrm{Obs}(W)\longrightarrow\mathrm{Obs}(W')
```

を指定する。supportの写像は同じAtomの読みを保ち、軸の写像は読める軸を保ち、
observableの制限は読めるobservableを読めるものへ送る。
三つの写像は、それぞれの向きで恒等と合成に従う。
この前順序を圏とみなし、$`W'\leq W`$ に対応する射を $`W'\to W`$ と書く。
文脈圏を $`𝒞_A`$ とする。

**例1.11（部分集合による文脈）.**
有限族 $`F`$ に対して部分集合 $`U\subseteq F`$ を文脈とし、
射を包含とする。$`\mathrm{Supp}(U)=U`$ として各元をそのAtomとして読み、
軸を一元集合、$`\mathrm{Obs}(U)`$ を集合 $`B`$ への関数集合
$`B^U`$ とすれば、observableの制限は関数の制限である。
二つの文脈の共通部分は $`U\cap V`$ で与えられる。

方程式を扱うには、局所的な値を足し引きできる環を選ぶ。
等式の両辺の差を取ると、その等式の成立を残差の消滅として表せる。
以下では、方程式を表示するための記号的座標と、対象で評価する残差の両方を保持する。

**定義1.12（Architectural equation system）.**
文脈圏 $`𝒞`$ とarchitecture objectの集合を固定する。
方程式系 $`E`$ は次のデータからなる。

- 方程式添字の集合 $`K_E`$ と、各添字への役割
  $`\mathrm{role}_E:K_E\to\{\mathrm{required},\mathrm{optional},\mathrm{derived}\}`$。
- 可換環値の前層 $`O_E:𝒞^{\mathrm{op}}\to{𝐂𝐨𝐦𝐦𝐑𝐢𝐧𝐠}`$。
  射 $`j:W'\to W`$ に沿う制限を $`\mathrm{res}_j:O_E(W)\to O_E(W')`$ と書く。
- 各文脈・添字・Atomに対する記号的座標 $`\nu_{W,i,a}\in O_E(W)`$。
- さらに対象 $`A`$ に依存する残差 $`\varepsilon_{W,A,i,a}\in O_E(W)`$。

前層とは、ここでは環と制限準同型が
$`\mathrm{res}_{\mathrm{id}}=\mathrm{id}`$、
$`\mathrm{res}_{jk}=\mathrm{res}_k\mathrm{res}_j`$ を満たすことをいう。
二つの座標族には

```math
\mathrm{res}_j(\nu_{W,i,a})=\nu_{W',i,a},
\qquad
\mathrm{res}_j(\varepsilon_{W,A,i,a})=\varepsilon_{W',A,i,a}
\qquad\text{(1.1)}
```

を課す。$`\nu`$ は方程式を代数的に表示するための座標、
$`\varepsilon`$ は対象で方程式が成立するかを評価する残差である。
Law $`L_i`$ は、添字 $`i`$ の方程式とその意味の呼び名とする。

**定義1.13（Lawfulness）.**
方程式の成立と、必須の方程式をすべて満たす条件を

```math
\begin{aligned}
E_i(A)
&\Longleftrightarrow
\forall W\in\mathrm{Ob}(𝒞)\ \forall a\in\mathrm{At},\
\varepsilon_{W,A,i,a}=0,\\
\mathrm{Lawful}_E(A)
&\Longleftrightarrow
\forall i\in K_E^{\mathrm{req}},\ E_i(A),\\
K_E^{\mathrm{req}}
&=\{i\in K_E\mid\mathrm{role}_E(i)=\mathrm{required}\}
\end{aligned}
```

で定める。すなわち、必須の各方程式について、すべての文脈・Atomで残差が零になることを
lawfulnessと呼ぶ。全添字での成立は $`\mathrm{FullyLawful}_E(A)`$ と書く。
requiredは必須、optionalは任意、derivedは導出する方程式としての指定である。
derivedの成立を他の方程式から結論するには、その含意を証明する。

## 1.4 有限の検出とcoreの生成

方程式の失敗が、少数のAtomや関係を調べることで分かる場合がある。
この有限な検出を記述するため、構造についての問合せと、その組合せを定める。
さらに、対象・操作・方程式・検出方法をまとめ、操作で到達できる対象の全体をcoreとして構成する。

**定義1.14（符号付き有限query）.**
configurationに対するqueryは、Atom $`a`$ の所属、
関係 $`R(a,b)`$ の成立、同一視 $`I(a,b)`$ の成立のいずれかとする。
関係と同一視のqueryは、両端のAtomが族に属することも要求する。
対象 $`A`$ 上でquery $`q`$ が成立することを $`\mathrm{Holds}_A(q)`$ と書く。

符号付き有限query列は $`Q=((q_1,b_1),\ldots,(q_n,b_n))`$、
$`b_j\in\{0,1\}`$ であり、

```math
\mathrm{Matches}(Q,A)
\Longleftrightarrow
\forall j,\quad \mathrm{Holds}_A(q_j)\Longleftrightarrow b_j=1
```

と定める。符号 $`0`$ によって、Atomや関係の不在も有限条件として表せる。
たとえば、「$`a`$ が属する」「$`b`$ が属する」「$`R(a,b)`$ が成立する」
という三つのqueryに順に $`1,1,0`$ を付けると、
二つのAtomは存在するが、その間に指定した関係がないというパターンを表す。

**定義1.15（有限detectorとcircuit）.**
detector codeは、空の選択を表す $`\mathrm{reject}`$、
一つの列を指定する $`\mathrm{exact}(Q)`$、二つのcodeの選言
$`\mathrm{any}(c,d)`$ から有限回の構成で得られるものとする。
その受理する列は、それぞれ空集合、$`\{Q\}`$、受理集合の和集合である。
各 $`i\in K_E`$ にcode $`c_i`$ を指定し、その有限受理集合を
$`T_i`$ と書く。

対象 $`A`$ におけるcircuitの集合を

```math
\mathrm{Circ}_E(A,i)=\{Q\in T_i\mid\mathrm{Matches}(Q,A)\}
```

とする。つまり、codeが指定した有限パターンのうち、対象上で実際に成立するものがcircuitである。
これを方程式の失敗の証拠として使うために、次の健全性を要求する。
さらに、すべての必須方程式の失敗を検出できる条件を完全性と呼ぶ。
各条件は、すべての対象 $`A`$、添字 $`i`$、query列 $`Q`$ について要求する。

```math
\begin{aligned}
Q\in\mathrm{Circ}_E(A,i)&\Longrightarrow \neg E_i(A),\\
i\in K_E^{\mathrm{req}}\ \land\ \neg E_i(A)
&\Longrightarrow\mathrm{Circ}_E(A,i)\ne\varnothing.
\end{aligned}
```

健全性は、受理した構造的パターンから方程式の失敗が従うことを述べる。
完全性は、必須方程式の失敗にそのような有限パターンが必ず存在することを述べる。
いずれも、指定した方程式系とdetectorについて証明する条件である。

**命題1.16（Circuitによるlawfulnessの判定）.**
detectorが健全なら、lawfulな対象の必須circuitはすべて空である。
さらに必須方程式について完全なら、

```math
\mathrm{Lawful}_E(A)
\Longleftrightarrow
\forall i\in K_E^{\mathrm{req}},\
\mathrm{Circ}_E(A,i)=\varnothing.
```

**証明.**
lawfulな対象に必須circuitがあれば、健全性からその必須方程式が失敗し、矛盾する。
逆に、必須方程式が一つでも失敗すれば、完全性から対応するcircuitが存在する。□

失敗の有無を量 $`\omega_i(A)`$ で表す場合も同様である。
$`E_i(A)\Longleftrightarrow\omega_i(A)=0`$ と、
集約 $`\mathrm{Agg}((v_i)_i)=0\Longleftrightarrow\forall i,\ v_i=0`$ があれば、
必須添字上の集約が零であることとlawfulnessが同値になる。
この同値は二つの同値の合成から従う。

**定義1.17（Core reading）.**
core reading $`r`$ は、次の選択を含む。

- **抽出**：doctrineとsource $`(D,s)`$ を選び、
  抽出族 $`F_r=\mathrm{Atomize}_D(s)`$ が有限であることを要求する。
- **対象形成**：composition readingとobject readingを選ぶ。
- **操作と比較する値**：operation reading、invariant reading、signature readingを選ぶ。

これらから出発点となるconfigurationと対象を

```math
C_r=\mathrm{Comp}_r(F_r),\qquad A_r=\mathrm{Form}_r(C_r)
```

と定める。さらに、基点 $`A_r`$ の文脈圏 $`𝒞_r`$、
その上の方程式系 $`E_r`$ と健全なdetectorを選ぶ。
残差は $`\mathrm{ArchObj}(\mathrm{At})`$ の各対象で評価できるものとし、
基点から選んだ文脈圏を、生成する対象族の評価にも共通して用いる。

対象の部分集合 $`Z\subseteq\mathrm{ArchObj}(\mathrm{At})`$ が
operationについて閉じているとは、
$`A\in Z`$ かつ $`o\in\mathrm{Op}_r(A,B)`$ なら $`B\in Z`$ となることをいう。
基点を含むこのような部分集合全体の共通部分を $`\mathrm{Obj}_r`$ とする。
core $`\mathrm{Core}(r)`$ は、この対象族、基点、文脈圏、方程式系、
circuitの族、operationの族、invariantとsignatureを合わせたデータである。

**定理1.18（相対的coreの生成）.**
core reading $`r`$ から $`\mathrm{Core}(r)`$ が構成される。
その初期configurationの族は $`F_r`$ に等しく、基点のconfigurationは $`C_r`$ に等しい。
また、$`\mathrm{Obj}_r`$ は基点を含む最小のoperationで閉じた対象族であり、
次の有限到達可能性によっても特徴づけられる。

```math
B\in\mathrm{Obj}_r
\Longleftrightarrow
\exists n\inℕ,\
A_r=A_0\xrightarrow{o_1}A_1\xrightarrow{o_2}
\cdots\xrightarrow{o_n}A_n=B.
\qquad\text{(1.2)}
```

長さ $`0`$ の列も許す。

**証明.**
抽出族は命題1.4で得られ、readingの有限性条件によりcompositionに入力できる。
compositionとobject readingの条件から、二つのconfiguration成分の等式が得られる。
対象全体の集合は基点を含みoperationで閉じているため、
定義1.17の共通部分を取る族は空でない。

共通部分は基点を含む。$`A`$ がその共通部分に属し $`o:A\to B`$ があれば、
共通部分を定めるどの部分集合にも $`B`$ が属するので、共通部分もoperationで閉じている。
最小性は共通部分の定義から従う。

基点から有限列で到達する対象の集合を $`Z_{\mathrm{fin}}`$ とする。
長さ $`0`$ の列と列の末尾へのoperationの追加により、
$`Z_{\mathrm{fin}}`$ は基点を含みoperationで閉じている。
したがって $`\mathrm{Obj}_r\subseteq Z_{\mathrm{fin}}`$ である。
逆の包含は列の長さについての帰納法で得られる。
最後に、指定した方程式・detector・invariant・signatureをこの対象族へ制限し、
対象対のoperationを取れば、coreの全成分が得られる。□

式(1.2)の有限性は到達の各証拠の長さについての条件である。
operationで閉じた対象族全体の大きさは、指定したoperation readingによって決まる。

## 1.5 被覆からsiteへ

部分ごとに構造を読むには、全体を覆う文脈の族と、二つの部分で読んだ情報を比べる場所が要る。
例1.11の部分集合では、後者は共通部分である。
一般の文脈ではこの重なりを引き戻しとして選び、
Atom・方程式・signatureのうち必要な情報を共同で読める族を被覆の出発点とする。

**定義1.19（Overlapと被覆要件）.**
文脈圏 $`𝒞`$ の二つの射からなる各図式 $`U\to W\leftarrow V`$ に、
対象 $`U\times_W V`$ と射影 $`\pi_U,\pi_V`$ を選ぶ。
二つの射影をそれぞれ $`U\to W`$、$`V\to W`$ と合成した射は等しいとする。
さらに、この可換条件を満たす任意の $`T\to U`$ と $`T\to V`$ は、
ただ一つの $`T\to U\times_W V`$ を射影と合成することで得られるとする。
この引き戻しをoverlapと呼び、その選択を $`\mathrm{Ov}`$ と書く。
文脈の前順序が半順序の場合、overlapは $`W`$ 以下での二つの文脈の最大下界である。

被覆要件 $`ℛ`$ は、方程式系 $`E`$ とsignatureを固定した上で、次を選ぶ。

- 必要なAtomの部分集合 $`A_{\mathrm{req}}\subseteq\mathrm{At}`$。
- 必要な方程式座標 $`C_{\mathrm{req}}\subseteq K_E^{\mathrm{req}}\times\mathrm{At}`$。
- 記号的座標 $`\nu_{W,i,a}`$ のうち、witness（違反の証拠）として読む添字の部分集合
  $`C_{\mathrm{wit}}\subseteq K_E\times\mathrm{At}`$。
- 必要なsignature軸 $`\Lambda_{\mathrm{req}}\subseteq\Lambda`$。
- 各文脈でこれらを読めることを表す四つの可視性述語と、
  overlap上で必要な相互作用を読めることを表す述語 $`B_{ℛ}(U,W)`$。

選択した座標とwitnessの添字は、指定した制限に沿って保持する。
たとえば式(1.1)の制限は、$`(i,a)`$ という添字を保って値を制限する。
可視性は、文脈がその添字のデータを実際に読むための別の条件である。

射の族 $`𝒰=(u_\alpha:W_\alpha\to W)_{\alpha\in I}`$ が
$`(E,ℛ,\mathrm{Ov})`$-admissibleであるとは、次の条件を満たすことをいう。

- **各部分で読む情報**：必要なAtomとsignature軸は、それぞれ少なくとも一つの
  $`W_\alpha`$ で読める。
- **部分または重なりで読む情報**：必要な方程式座標と選択したwitnessは、
  それぞれ少なくとも一つの $`W_\alpha`$ または
  $`W_{\alpha\beta}=W_\alpha\times_W W_\beta`$ で読める。
- **重なりでの相互作用**：すべての $`\alpha,\beta`$ について
  $`B_{ℛ}(W_{\alpha\beta},W)`$ が成立する。
- **対象との対応**：各脚のsupportの写像が読むAtomは、もとの対象の族に属する。

被覆の体系には、別の文脈への制限と、各部分をさらに被覆する操作に対する閉性を要求する。
この体系を、次のsieveを使って定める。

**定義1.20（SieveとGrothendieck topology）.**
$`W`$ 上のsieve $`S`$ は、終域が $`W`$ の射の集まりで、
$`f:V\to W`$ が属すれば、任意の $`g:V'\to V`$ に対して $`fg`$ も属すものとする。
射 $`u:W'\to W`$ による引き戻しは
$`u^*S=\{g:V\to W'\mid ug\in S\}`$ である。
族 $`𝒰`$ が生成するsieve $`\langle 𝒰\rangle`$ は、
少なくとも一つの $`u_\alpha`$ を経由する射全体である。

Grothendieck topology $`J`$ は、各 $`W`$ に被覆sieveの集合 $`J(W)`$ を
対応させ、次を満たすものをいう。

1. $`W`$ を終域とするすべての射からなる最大sieveは $`J(W)`$ に属する。
2. $`S\in J(W)`$ なら $`u^*S\in J(W')`$ である。
3. $`S\in J(W)`$ であり、別のsieve $`T`$ がすべての $`u:W'\to W`$、
   $`u\in S`$ について $`u^*T\in J(W')`$ を満たせば、$`T\in J(W)`$ である。

この定義は [Stacks, §7.47, Tag 00YW](https://stacks.math.columbia.edu/tag/00YW) のものを用いる。

**命題1.21（被覆要件からの位相の生成）.**
すべてのadmissibleな族が生成するsieveを含む最小のGrothendieck topologyが存在する。
これを $`J_{E,ℛ,\mathrm{Ov}}`$ と書く。

**証明.**
各対象のすべてのsieveを被覆とする位相は、指定したsieveをすべて含む。
それらを含む位相全体の共通部分を対象ごとに取る。
最大sieveの条件と引き戻しによる安定性は、各位相で成立するので共通部分でも成立する。
推移性についても、その前提が共通部分で成立すれば各位相で成立し、
結論のsieveがすべての位相に属する。したがって共通部分は位相であり、定義から最小である。□

siteとは、小さい圏とGrothendieck topologyの組をいう。
基点 $`A_r`$ から得る
$`(𝒞_r,J_{E_r,ℛ,\mathrm{Ov}})`$ をAAT siteと呼ぶ。
方程式系、signature、被覆要件、overlapの選択も、その構成データとして保持する。
生成位相の被覆族のうち、指定した可視性と相互作用の要件も満たすものを
$`(E,ℛ,\mathrm{Ov})`$-adequateと呼ぶ。
位相は局所的な貼り合わせの規則を与え、adequacyは定理で使う情報が被覆上にあることを表す。
第2章で、局所的な方程式の成立と貼り合わせの整合性を結びつける際に用いる。

## 1.6 前層、層、係数を備えた幾何

前層は、各文脈にデータを割り当て、より小さい文脈へ制限する規則を持つ。
層はさらに、重なりで一致する局所データから、全体のデータがただ一つ得られるという条件を満たす。

**定義1.22（前層と層）.**
集合値の前層は反変関手 $`F:𝒞^{\mathrm{op}}\to{𝐒𝐞𝐭}`$ である。
$`F(W)`$ の元を $`W`$ 上の切断と呼ぶ。
族 $`𝒰=(u_\alpha:W_\alpha\to W)_\alpha`$ 上のmatching familyとは、
$`s_\alpha\in F(W_\alpha)`$ の族で、

```math
F(\pi_\alpha)(s_\alpha)=F(\pi_\beta)(s_\beta)
\quad\text{in }F(W_{\alpha\beta})
\qquad\text{(1.3)}
```

をすべての $`\alpha,\beta`$ について満たすものをいう。
その集合を $`\mathrm{Match}(𝒰,F)`$ と書く。
前層 $`F`$ が $`J`$ に関する層であるとは、
$`\langle 𝒰\rangle\in J(W)`$ となるすべての族に対して

```math
F(W)\longrightarrow\mathrm{Match}(𝒰,F),
\qquad s\longmapsto(F(u_\alpha)(s))_\alpha
\qquad\text{(1.4)}
```

が全単射となることをいう。単射性を分離性、全射性を貼り合わせの存在と呼ぶ。
層の射は前層の自然変換であり、層の圏を $`\mathrm{Sh}(𝒞,J)`$ と書く。

sieve $`S`$ 上のmatching familyは、
各 $`u:V\to W`$、$`u\in S`$ に $`s_u\in F(V)`$ を与え、
$`s_{uv}=F(v)(s_u)`$ を満たす族である。
被覆族上のmatching familyは、$`u_\alpha`$ を通る射へ制限することで、
生成するsieve上のmatching familyになる。二通りの因子分解から得る値は、
引き戻しの普遍性と式(1.3)によって等しい。
逆に、sieve上の族を各 $`u_\alpha`$ で読むと式(1.3)が得られる。
したがって、被覆sieveによる層の定義とも一致する。

層の条件が必要になる例として、二点集合 $`\{p,q\}`$ の部分集合を文脈とし、
和集合で覆う族を被覆とする。空文脈上では一元集合、空でない文脈上では $`\{0,1\}`$ を取り、
空でない文脈間の制限を恒等写像とする前層 $`F`$ を考える。
一元文脈上の値 $`s_p=0`$、$`s_q=1`$ は重なりで一致するが、
二点上のどちらの元にも貼り合わない。
このような不足を埋めるため、整合する局所データを新しい切断として加える操作が層化である。

**命題1.23（層化）.**
任意の前層 $`F`$ に、層 $`a_JF`$ と自然変換
$`\eta_F:F\to a_JF`$ が存在する。任意の層 $`G`$ と自然変換
$`t:F\to G`$ に対して、$`t=\bar t\eta_F`$ を満たす
$`\bar t:a_JF\to G`$ がただ一つ存在する。

**構成と証明.**
被覆上のmatching familyを一つの切断として扱い、局所的に一致する表示を同一視する。
この操作を二度行うと、必要な貼り合わせをすべて備えた層が得られる。

$`F^+(W)`$ の元を、被覆sieve $`S\in J(W)`$ 上のmatching familyで表す。
二つの表示は、両sieveに含まれる被覆sieve上で一致するとき同値とする。
被覆sieveの有限共通部分も被覆である。
これは定義1.20の推移性を、一方のsieveの射に沿う引き戻しへ適用すれば従う。
したがってこの同値関係は推移的である。
引き戻しにより $`F^+`$ の制限が定まり、大域切断の制限族から
$`F\to F^+`$ が得られる。

$`F^+`$ の二つの元が被覆上で等しければ、その等しさを表す局所的な被覆sieveを
集められる。位相の推移性により得られる被覆上で表示が一致するため、二つの元は等しい。
よって $`F^+`$ は分離的である。
$`F`$ 自身が分離的なとき、$`F^+`$ のmatching familyの各元を局所的な
$`F`$ の切断で表示する。重なりでの等しさはさらに局所的に成立し、
$`F`$ の分離性によってその重なり上で成立する。
これらの表示を集めた被覆sieve上の族が貼り合わせを与える。
ゆえに $`F`$ が分離的なら $`F^+`$ は層である。

そこで $`a_JF=(F^+)^+`$ と置く。
$`t:F\to G`$ は各表示を $`G`$ のmatching familyへ送り、
$`G`$ の一意な貼り合わせによって $`F^+\to G`$ を定める。
同じ操作を二度行うと $`\bar t`$ を得る。
各元は局所的な表示から定まり、$`G`$ は分離的なので延長は一意である。□

これは標準的な層化である
（[Stacks, §7.49, Tag 00ZG](https://stacks.math.columbia.edu/tag/00ZG)）。
特に、もとの $`F`$ が層であれば、普遍性から $`\eta_F`$ は同型である。

**例1.24（局所切断を追加する層化）.**
上の二点集合の前層 $`F`$ の層化は $`U\mapsto\{0,1\}^U`$ である。
一点ごとに異なる値を取る族も、一つの関数として保持される。
実際、関数は各一点への制限で一意に決まり、一点ごとの任意の値を貼り合わせられる。
もとの前層からは、各値を定数関数へ送る。
任意の層への自然変換は一点文脈での値によって決まり、
それらを貼り合わせることで $`U\mapsto\{0,1\}^U`$ から一意に延長される。
したがって命題1.23の普遍性も満たす。

方程式を代数的に扱うため、局所データに環の構造を与える。
各文脈の座標を変数とし、構造関係を多項式の等式として課すと、その文脈で使う環を作れる。
さらに文脈間の制限を定めることで、環値の前層を得る。

**定義1.25（文脈ごとの環と制限）.**
係数環 $`k`$ を選ぶ。各文脈 $`W`$ に座標の集合 $`Z_W`$、
各座標の種別と局所データの型、構造関係の添字集合 $`H_W`$、
多項式 $`r_{W,h}\in k[x_z\mid z\in Z_W]`$ を指定する。
多項式環の各元は、有限個の変数についての有限和である。
構造関係の生成するイデアルと商を

```math
I_W^{\mathrm{str}}=(r_{W,h}\mid h\in H_W),
\qquad
B_{\mathrm{raw}}(W)=k[x_z\mid z\in Z_W]/I_W^{\mathrm{str}}
```

とする。射 $`j:W'\to W`$ には、変数を多項式へ送る $`k`$-代数準同型
$`\rho_j:k[x_z\mid z\in Z_W]\to k[x_z\mid z\in Z_{W'}]`$ を与え、

```math
\rho_j(I_W^{\mathrm{str}})\subseteq I_{W'}^{\mathrm{str}},
\qquad
\rho_{\mathrm{id}}=\mathrm{id},
\qquad
\rho_{jk}=\rho_k\rho_j
\qquad\text{(1.5)}
```

を要求する。座標、関係、これらの多項式の制限をまとめてraw restriction system
$`ℬ`$ と呼ぶ。式(1.5)により、制限は商に降り、
$`B_{\mathrm{raw}}`$ は可換 $`k`$-代数値の前層になる。
この主張は、同じ剰余類の二つの代表の差が制限後も構造イデアルに属すること、
恒等と合成が多項式上で成立することから従う。

係数を備えたarchitecture geometryは

```math
G=(r,ℛ,\mathrm{Ov},k,ℬ)
```

である。基点、文脈、方程式、signatureは $`r`$ から、位相は命題1.21から得る。
構造関係は、各文脈で局所データを表す環を定める。
第2章では、この環の前層と方程式系を結ぶ実現を与え、
記号的座標の評価が対象ごとの残差に対応する条件を明示する。

**補題1.26（Raw systemの係数変更）.**
環準同型 $`\varphi:k\to k'`$ により、座標と関係の添字を保ったまま、
すべての多項式の係数へ $`\varphi`$ を適用してraw system $`\varphi_!ℬ`$ を得る。
この構成は恒等準同型と準同型の合成に従う。

**証明.**
変数 $`x_z`$ を同じ変数へ、係数 $`c`$ を $`\varphi(c)`$ へ送る。
構造関係の像が生成するイデアルを新しい構造イデアルとする。
もとの制限が構造イデアルを保つことは、各生成関係の像を有限な
イデアル結合として表す等式であり、その等式に係数写像を適用しても成立する。
式(1.5)の恒等・合成の等式も同様である。
係数写像の逐次適用はその合成の適用と等しいので、最後の主張が従う。□

## 1.7 Readingの射と三段の射影

readingを変更すると、抽出するAtom、対象の作り方、方程式や局所性の選択が変わる。
変更の前後を比較するには、それぞれのデータを結ぶ写像と、それらが満たす条件が要る。
比較するデータの範囲に応じて、三つの圏を定める。

| 圏 | 対象が持つデータ | 射が比較するもの |
| --- | --- | --- |
| $`B`$ | 抽出doctrineとsource | sourceとAtom |
| $`E_{\mathrm{core}}`$ | core reading | 抽出に加え、対象形成・操作・方程式・検出・invariant・signature |
| $`E_{\mathrm{geom}}`$ | 係数を備えた幾何 | coreに加え、被覆・重なり・係数・環の表示・文脈のデータ |

抽出の成立と方程式の成立は、変更の前後で同値になるように要求する。
この保存と反映を備えた変更をexactな変更と呼ぶ。

**定義1.27（抽出の底の圏）.**
Atomの語彙を固定する。圏 $`B`$ の対象は抽出doctrineと選択sourceの組
$`(D,s)`$ とする。射 $`(D,s)\to(D',s')`$ は、
写像 $`f:\mathrm{Src}_D\to\mathrm{Src}_{D'}`$ と全単射
$`e:\mathrm{At}\xrightarrow{\sim}\mathrm{At}`$ であって、

```math
\begin{aligned}
f(s)&=s',&
N_{D'}f&=fN_D,\\
\mathrm{Extracts}_D(t,a)
&\Longleftrightarrow
\mathrm{Extracts}_{D'}(f(t),e(a))
&&\text{for all }t,a
\end{aligned}
\qquad\text{(1.6)}
```

を満たすものとする。恒等射は二つの恒等写像、合成は
$`(f',e')(f,e)=(f'f,e'e)`$ である。
式(1.6)の等式と同値を合成すれば、合成後も同じ条件が成立する。

族の直像を $`e_*F=\{e(a)\mid a\in F\}`$ と書く。
式(1.6)と $`e`$ の全単射性から

```math
\mathrm{Atomize}_{D'}(f(t))=e_*\mathrm{Atomize}_D(t)
\qquad\text{(1.7)}
```

が従う。実際、右辺の元は抽出の保存によって左辺に属する。
左辺の元 $`b`$ には $`a=e^{-1}(b)`$ を取り、抽出の反映を使えばよい。
sourceの写像 $`f`$ は一般の写像であり、たとえば異なる状態を一つに送る写像も含む。

configurationの直像は、族と二つの関係のすべてに $`e`$ を作用させて定める。
有限query列とdetector codeにも、出現するすべてのAtomへ $`e`$ を作用させる。
これらも $`e_*`$ と書く。

次の条件では、対象の表示を変更しても、Lawの成否と、その失敗を示す有限パターンが対応するように各写像を選ぶ。

**定義1.28（Coreの射）.**
Atomの語彙を固定したcore readingを $`E_{\mathrm{core}}`$ の対象とする。
$`r`$ から $`r'`$ への射は、その底の射 $`(f,e)`$ と次のデータ・条件からなる。

**対象形成とoperation.**
Atomを写してから対象を作る経路と、対象を作ってから写す経路が一致することを要求する。
写像 $`H:\mathrm{ArchObj}(\mathrm{At})\to\mathrm{ArchObj}(\mathrm{At})`$ を与え、
任意の有限族 $`F`$、configuration $`C`$、対象 $`A`$ について

```math
\begin{aligned}
\mathrm{Comp}_{r'}(e_*F)&=e_*\mathrm{Comp}_r(F),\\
H(\mathrm{Form}_r(C))&=\mathrm{Form}_{r'}(e_*C),\\
C_{H(A)}&=e_*C_A
\end{aligned}
\qquad\text{(1.8)}
```

を要求する。operationの写像
$`\Phi_{A,B}:\mathrm{Op}_r(A,B)\to\mathrm{Op}_{r'}(H(A),H(B))`$ には、
configurationへの作用 $`d(o)`$ について

```math
d(\Phi(o))_{\mathrm{At}}\,e=e\,d(o)_{\mathrm{At}}
\qquad\text{(1.9)}
```

を課す。$`e`$ 自身も $`C_A\to C_{H(A)}`$ のconfigurationの射を与えるため、
式(1.9)はconfigurationの可換平方でもある。

**方程式と検出.**
文脈、方程式添字、値を取る環を対応づけ、その対応の下で座標・残差・detector codeを保つ。
指定した準逆を持つ圏同値
$`\theta:𝒞_r\simeq𝒞_{r'}`$、添字の全単射
$`\lambda:K_{E_r}\xrightarrow{\sim}K_{E_{r'}}`$、
各文脈の環同型 $`\alpha_W:O_{E_r}(W)\xrightarrow{\sim}O_{E_{r'}}(\theta W)`$
を与える。これらは

```math
\begin{aligned}
\mathrm{role}_{E_{r'}}(\lambda i)&=\mathrm{role}_{E_r}(i),\\
\alpha_{W'}\mathrm{res}_j&=\mathrm{res}'_{\theta j}\alpha_W,\\
\alpha_W(\nu_{W,i,a})&=\nu'_{\theta W,\lambda i,e(a)},\\
\alpha_W(\varepsilon_{W,A,i,a})
&=\varepsilon'_{\theta W,H(A),\lambda i,e(a)},\\
c'_{\lambda i}&=e_*c_i
\end{aligned}
\qquad\text{(1.10)}
```

を満たすものとする。最後の等式はdetector codeの構文としての等式である。

**Invariantとsignature.**
invariantの種類を保つ添字写像 $`\mu`$ を与える。
対応する関数型invariantについては、値域のある全単射 $`t_i`$ により、
すべての対象 $`A`$ で
$`t_i(I_i(A))=I'_{\mu i}(H(A))`$ となることを要求する。
述語型については $`P_i(A)\Longleftrightarrow P'_{\mu i}(H(A))`$ を要求する。
signatureには軸の写像 $`\sigma:\Lambda_r\to\Lambda_{r'}`$ と
各値域の全単射 $`\beta_\ell:V_\ell\xrightarrow{\sim}V'_{\sigma\ell}`$ を与え、

```math
\ell\in\Lambda_{\mathrm{sel}}
\Longleftrightarrow \sigma\ell\in\Lambda'_{\mathrm{sel}},
\qquad
\beta_\ell(q_\ell(A))=q'_{\sigma\ell}(H(A))
\qquad\text{(1.11)}
```

を課す。射はこれらの構成写像をすべて保持する。
同じconfigurationへの作用を持つ場合も、対象・operation・軸などの写像が異なれば異なる射である。

**命題1.29（Exactなcore変更の作用）.**
定義1.28の射は、$`A_r`$ を $`A_{r'}`$ へ送り、
$`H(\mathrm{Obj}_r)\subseteq\mathrm{Obj}_{r'}`$ を満たす。
任意の対象 $`A`$ と方程式添字 $`i`$ について

```math
E_{r,i}(A)\Longleftrightarrow E_{r',\lambda i}(H(A)),
\qquad
\mathrm{Lawful}_{E_r}(A)\Longleftrightarrow
\mathrm{Lawful}_{E_{r'}}(H(A)).
\qquad\text{(1.12)}
```

また、$`Q\mapsto e_*Q`$ は
$`\mathrm{Circ}_{E_r}(A,i)`$ と
$`\mathrm{Circ}_{E_{r'}}(H(A),\lambda i)`$ の全単射を与える。

**証明.**
式(1.7)と(1.8)を順に使うと基点の等式が得られる。
基点からの有限operation列に $`H,\Phi`$ を作用させ、
式(1.2)を用いれば、生成対象族の包含が従う。

式(1.10)の残差比較と環同型の零の保存・反映により、
$`W`$ での残差の消滅は $`\theta W`$ での消滅と同値である。
$`e`$ は全単射なので、Atom全体にわたる量化も対応する。
変更後の任意の文脈 $`V`$ はある $`\theta W`$ と同型であり、
その同型に沿う制限は環同型である。式(1.1)をこの同型へ適用すれば、
$`V`$ 上の残差にも同じ同値が成立する。
添字の全単射と役割の保存を使うとlawfulnessの同値を得る。

式(1.8)から、Atomの所属、関係、同一視の成立は $`e`$ に沿って保存・反映される。
よって真偽の両符号について
$`\mathrm{Matches}(Q,A)\Longleftrightarrow\mathrm{Matches}(e_*Q,H(A))`$ である。
codeの等式から、受理集合は $`T'_{\lambda i}=e_*T_i`$ となる。
$`e^{-1}`$ によるquery列の逆写像と合わせて、circuitの全単射を得る。□

**定義1.30（幾何の射）.**
幾何 $`G=(r,ℛ,\mathrm{Ov},k,ℬ)`$ から
$`G'=(r',ℛ',\mathrm{Ov}',k',ℬ')`$ への射は、coreの射 $`h:r\to r'`$ と、
以下のデータ・条件からなる。$`\theta`$ の指定した準逆を $`\bar\theta`$ と書く。

**1. 被覆要件の保存。** 必要なAtomには $`e`$、
方程式座標とwitnessには $`(i,a)\mapsto(\lambda i,e(a))`$、
signature軸には $`\sigma`$ を用い、各要件を前向きに保存する。
四つの可視性述語も $`W\mapsto\theta W`$ とこれらの写像に沿って保存され、
$`B_{ℛ}(U,W)\Rightarrow B_{ℛ'}(\theta U,\theta W)`$ が成立する。

**2. 重なりの比較。** 変更後の文脈圏の各図式 $`U\to W\leftarrow V`$ に対して、
変更前に選んだoverlapを運んだものと、変更後に選んだoverlapの同型を指定する。すなわち
$`\theta(\bar\theta U\times_{\bar\theta W}\bar\theta V)\cong U\times_W V`$ である。
射影との比較には圏同値の余単位を用いる。

**3. 係数の変更。** 環準同型 $`\varphi:k\to k'`$ を指定する。

**4. 環の表示の一致。** 変更後のraw systemは、変更前のraw systemの係数を $`\varphi`$ で変更し、
$`\bar\theta`$ に沿って再添字づけしたものと等しい：

```math
ℬ'=\bar\theta^{\,*}(\varphi_!ℬ).
\qquad\text{(1.13)}
```

右辺は、変更後の文脈 $`V`$ に $`\bar\theta V`$ の座標・種別・局所データ型・
関係添字を置き、多項式の係数を変更したものである。
制限は $`\bar\theta`$ が送る射での制限から作る。
等式はこれらの表示データをすべて含む。

**5. 文脈に含まれるデータの比較。** 各 $`W`$ に、support、軸、observableの比較写像

```math
s_W:\mathrm{Supp}(W)\to\mathrm{Supp}'(\theta W),\quad
a_W:\mathrm{Ax}(W)\to\mathrm{Ax}'(\theta W),\quad
o_W:\mathrm{Obs}(W)\to\mathrm{Obs}'(\theta W)
```

を指定する。supportの読みはAtomを $`e`$ で移して保存し、
軸とobservableの読める元も保存する。
$`j:W'\to W`$ に対し、supportと軸の共変な構造写像を $`S_j,A_j`$、
observableの反変な制限を $`O_j`$ と書けば、

```math
S'_{\theta j}s_{W'}=s_WS_j,\qquad
A'_{\theta j}a_{W'}=a_WA_j,\qquad
O'_{\theta j}o_W=o_{W'}O_j
\qquad\text{(1.14)}
```

が成立する。

文脈圏は前順序圏なので、存在する二つの平行射は等しい。
したがって、項目2の射影の可換性と、overlapの比較の単位・合成の整合性は一意に決まる。
supportなどの比較写像は実際の写像として保持され、項目5の条件を別に満たす。

**定理1.31（三段の圏と射影）.**
定義1.27、1.28、1.30の対象と射は、それぞれ圏
$`B`$、$`E_{\mathrm{core}}`$、$`E_{\mathrm{geom}}`$ をなし、関手

```math
E_{\mathrm{geom}}
\xrightarrow{\,p\,}
E_{\mathrm{core}}
\xrightarrow{\,q\,}
B
\qquad\text{(1.15)}
```

を持つ。$`p`$ は幾何の選択とその比較を忘れてcoreを取り出し、
$`q`$ は抽出doctrine・選択sourceとその写像を取り出す。

**証明.**
$`B`$ については定義1.27で確認した。
coreの射は、source・Atom・対象・添字・operationの各写像を順に合成する。
文脈の圏同値には合成同値を、各文脈の環同型には順に適用した環同型を用いる。
式(1.8)–(1.11)は、それぞれ二つの等式を代入することで合成後にも成立する。
関数型invariantの値域の全単射は合成でき、述語型の同値も合成できる。
恒等射には各恒等写像を用いる。写像の合成則と、前順序圏内の比較射の一意性から
単位則と結合則を得る。

幾何の射の係数写像は環準同型として合成する。
supportなどの比較は、たとえば $`s''_W=s'_{\theta W}s_W`$ と合成する。
可視性の含意と式(1.14)はその合成について閉じている。
raw systemについて、再添字づけは係数の変更と可換し、補題1.26により
二度の係数変更は合成準同型による変更と等しい。
したがって、二つの式(1.13)から合成射の式(1.13)が得られる。
恒等・結合則も座標、関係多項式、制限写像の各成分で成立する。

二つの射影は以上の合成の対応する成分を取り出す。
よって対象と射に定義され、恒等と合成を保つ。□

式(1.15)は、同じ抽出を持つ異なる対象形成や、同じcoreを持つ異なる局所幾何を
一つの図式で扱うための構成である。第4章では、底の変更から上段の対象と射を
作る輸送を、その存在と普遍性から調べる。

## 1.8 モデル同期：読取りと更新の意味論

§1.7では、抽出や方程式など、readingの選択を比較した。
ここからは、AATとは独立に定めた意味論のもとで状態と操作を比較する。
読取りと更新の整合性を扱うlensと、名前付き操作をつないだ実行とその観測を扱うプロトコルを取り上げる。

§1.10では、両者から役割別の対象・操作・Lawを構成し、
Lawの成立と元の法則の成立が同値になることを示す。
さらに、構成された対象間の型付き射と、元の意味保存射が一対一に対応することを確かめる。
この対応を用いて、後続の章で共通の定理から得られる変更の分類や局所再構成の結果を、
元の意味論へ戻す。

まずlensについて、状態の分解と、読取り・更新を保つ写像を求める。
モデル同期では、内部状態の一部を表示し、表示値に対する変更を内部状態へ反映する。
この表示される部分をviewと呼ぶ。読取りと更新の整合性をlensの三法則で定めると、
状態を「表示値」と「更新で保たれる成分」に分解できる。

**定義1.32（全域lensとその射）.**
viewの集合 $`V`$ と基準値 $`v_0\in V`$ を固定する。
全域lensは、状態集合 $`C`$、読取り $`g:C\to V`$、
更新 $`p:C\times V\to C`$ であって、

```math
p(c,g(c))=c,\qquad
g(p(c,v))=v,\qquad
p(p(c,v),w)=p(c,w)
\qquad\text{(1.16)}
```

をすべての $`c,v,w`$ について満たすものとする。
三つの等式は、順に次のことを表す。

1. 現在の表示値をそのまま書き戻しても、状態は変わらない。
2. 更新後に読み出すと、指定した表示値が得られる。
3. 続けて二度更新した結果は、最後の表示値で一度だけ更新した結果と等しい。

標準的なlensの用語では、全域でvery well-behavedなlensに当たる
（[FGMPS04, §3.1](https://www.cis.upenn.edu/~bcpierce/papers/newlenses-full.pdf)）。
以下で扱うlensでは基準fiber
$`K_L=\{c\in C\mid g(c)=v_0\}`$ を有限とする。
これは、表示を基準値に固定したときに残る状態の集合である。
表示値の集合 $`V`$ 自体は無限でもよい。
基準fiberの有限性は、後に意味保存射を有限の表で記述するために用いる。

固定view上の射 $`h:L\to L'`$ は、状態の写像 $`h:C\to C'`$ で、

```math
g'h=g,\qquad h(p(c,v))=p'(h(c),v)
\qquad\text{(1.17)}
```

を満たすものとする。恒等と合成は状態写像の恒等と合成であり、
式(1.17)の代入によって再び式(1.17)を満たす。
この圏を $`\mathrm{Lens}(V,v_0)`$ と書く。

**命題1.33（Lensの積表示）.**
全域lens $`L=(C,g,p)`$ に対し、

```math
\begin{aligned}
\eta_L:C&\longrightarrow V\times K_L,
&c&\longmapsto(g(c),p(c,v_0)),\\
\zeta_L:V\times K_L&\longrightarrow C,
&(v,k)&\longmapsto p(k,v)
\end{aligned}
\qquad\text{(1.18)}
```

は互いに逆な全単射である。この表示で読取りは第一射影、更新は
$`((v,k),w)\mapsto(w,k)`$ となる。

**証明.**
$`g(p(c,v_0))=v_0`$ なので $`\eta_L`$ は定義できる。
三法則から

```math
p(p(c,v_0),g(c))=p(c,g(c))=c
```

である。よって $`\zeta_L\eta_L=\mathrm{id}`$ が成り立つ。一方、$`k\in K_L`$ について
$`g(p(k,v))=v`$、
$`p(p(k,v),v_0)=p(k,v_0)=p(k,g(k))=k`$ となるので、
$`\eta_L\zeta_L=\mathrm{id}`$ も成立する。
読取りの式は第一成分から従う。更新後の第二成分は
$`p(p(c,w),v_0)=p(c,v_0)`$ で変わらず、第一成分は $`w`$ となる。□

積表示の第二成分は、表示値を変えても保持される情報を表す。
読取りと更新を保つ写像も、この成分にどう作用するかだけで決まる。

**命題1.34（基準fiberからの射の回復）.**
任意の二つのlensに対し、制限

```math
\mathrm{res}:\mathrm{Hom}(L,L')
\longrightarrow\mathrm{Map}(K_L,K_{L'}),\qquad
h\longmapsto h|_{K_L}
```

は全単射である。ここで $`\mathrm{Map}(K,K')`$ は集合間の写像全体を表す。
逆写像は、任意の $`t:K_L\to K_{L'}`$ に対し

```math
\mathrm{ext}(t)(c)=p'\bigl(t(p(c,v_0)),g(c)\bigr)
\qquad\text{(1.19)}
```

で与えられる。これは、いったん基準viewへ更新し、その状態へ $`t`$ を適用した後、
もとの表示値へ更新する操作である。

**証明.**
射 $`h`$ は読取りを保つので、基準fiberを基準fiberへ送る。
命題1.33の積表示で、$`\mathrm{ext}(t)`$ は
$`(v,k)\mapsto(v,t(k))`$ であり、読取りと更新を保つ。
よって式(1.19)は実際にlensの射を与える。

$`k\in K_L`$ なら $`p(k,v_0)=k`$ かつ
$`p'(t(k),v_0)=t(k)`$ なので、$`\mathrm{res}(\mathrm{ext}(t))=t`$ である。
逆方向は式(1.17)と三法則によって

```math
\begin{aligned}
\mathrm{ext}(\mathrm{res}(h))(c)
&=p'(h(p(c,v_0)),g(c))\\
&=p'(p'(h(c),v_0),g(c))\\
&=p'(h(c),g(c))
=p'(h(c),g'(h(c)))=h(c)
\end{aligned}
```

となる。制限も延長も恒等と合成を保つことは、積表示から分かる。□

可視変更を含む正規形として、ここでは有限集合 $`K`$ の同じ積lens
$`V\times K`$ の自己変更を扱う。
$`u:V\xrightarrow{\sim}V`$ と $`h:V\times K\xrightarrow{\sim}V\times K`$ が

```math
gh=ug,\qquad h(p(c,v))=p(h(c),u(v))
\qquad\text{(1.20)}
```

を満たすとき、一意な置換 $`\phi:K\xrightarrow{\sim}K`$ があり、

```math
h(v,k)=(u(v),\phi(k))
```

となる。更新の保存は、各view上で得られる隠れた成分の置換が、
基準viewでの置換に等しいことを与える。
$`v=v_0`$ で第二成分を読むと、その置換の一意性も得られる。

**例1.35（読取りだけを保つ変更）.**
$`V=K=\{0,1\}`$ の積lensを考える。$`\oplus`$ は $`2`$ を法とする加法を表す。
全単射 $`h(v,k)=(v,k\oplus v)`$ は読取りを保つが、

```math
h(p((0,0),1))=(1,1),\qquad
p(h(0,0),1)=(1,0)
```

となる。固定view上で読取りを保つ全単射は、二つのfiberで独立に恒等か交換を選ぶ
$`2\cdot2=4`$ 個である。更新も保つものは、両fiberで同じ選択をする $`2`$ 個となる。
更新が異なるfiberを結びつけることによって、許される変更が制約される。

## 1.9 プロトコル：名前付き操作と全実行

プロトコルには、一回ごとの操作と、それらをつないだ実行列がある。
閉路を繰り返せる場合、有限個の操作から任意の長さの実行列が生じる。
各操作の作用と、等しい実行として扱う経路対を指定することで、全実行の意味を定める。
この記述には、グラフと経路等式による圏の表示、集合値関手による実現という標準的な構成を用いる
（[Spivak12, §§3.2, 3.4–3.5](https://arxiv.org/pdf/1009.1166v3)）。

**定義1.36（プロトコルの実現）.**
有限有向多重グラフ $`Q`$ を、頂点集合 $`Q_0`$、名前付き辺集合 $`Q_1`$、
始点・終点写像で与える。経路は合成可能な有限辺列であり、各頂点の空列を恒等経路とする。
同じ始点と終点を持つ有限個の経路対
$`\Pi=\{(\ell_j,r_j)\}_{j\in J_\Pi}`$ を指定する。

経路全体に、指定した対を同一視し、前後の合成で保たれる最小の同値関係を入れる。
頂点を対象、経路の同値類を射とする圏を $`𝒞_Q`$ と呼ぶ。
合成は経路の連結から定まり、合同性によって同値類上で定義できる。
結合則と単位則は経路の連結から従う。

観測先の関手 $`O:𝒞_Q\to{𝐒𝐞𝐭}`$ を固定する。
プロトコルの実現は、各頂点の状態集合 $`X(v)`$ が有限である関手
$`X:𝒞_Q\to{𝐒𝐞𝐭}`$ と自然変換 $`o_X:X\Rightarrow O`$ の組である。
辺 $`e:v\to w`$ に対して $`X(e)`$ は状態の遷移を表し、
$`o_X(v)`$ は頂点 $`v`$ の状態から読める観測値を与える。
観測の自然性は、状態を遷移させてから観測することと、
観測値を $`O(e)`$ で移すことが一致するという条件である。

射 $`a:(X,o_X)\to(Y,o_Y)`$ は自然変換 $`a:X\Rightarrow Y`$ で
$`o_Ya=o_X`$ を満たすものとする。その成分 $`a_v`$ は一般の状態写像である。
自然性によって実行を保ち、後者の等式によって観測を保つ。
成分ごとの恒等と合成によって圏 $`\mathrm{Prot}(Q,\Pi,O)`$ を得る。

**命題1.37（有限の操作表からの実現）.**
各頂点に有限集合 $`S_v`$、各辺 $`e:v\to w`$ に写像
$`T_e:S_v\to S_w`$、各頂点に観測 $`b_v:S_v\to O(v)`$ を与える。
経路の作用を辺写像の合成で定め、次を仮定する。

```math
T_{\ell_j}=T_{r_j}\quad(j\in J_\Pi),\qquad
b_wT_e=O(e)b_v\quad(e:v\to w).
\qquad\text{(1.21)}
```

このとき、これらの状態・辺・観測を持つ実現がただ一つ定まる。

**証明.**
空経路には恒等写像、$`e_n\cdots e_1`$ には
$`T_{e_n}\cdots T_{e_1}`$ を割り当てる。
これは自由な経路圏から集合の圏への関手である。
同じ写像になる経路対は、同値関係をなし前後の合成で保たれ、式(1.21)の
宣言関係を含む。したがって $`𝒞_Q`$ の経路の同値類上で作用が定まる。

観測の可換性も経路の長さについて帰納的に従う。
実際、$`p:v\to w`$ と $`e:w\to z`$ について
$`b_wT_p=O(p)b_v`$ なら、
$`b_zT_eT_p=O(e)b_wT_p=O(e)O(p)b_v`$ である。
よって $`b`$ は自然変換になる。
すべての経路は辺の合成なので、延長の一意性も従う。□

**命題1.38（頂点写像からの意味保存射の回復）.**
実現 $`X,Y`$ に対し、頂点ごとの写像 $`a_v:X(v)\to Y(v)`$ が

```math
a_wX(e)=Y(e)a_v,\qquad o_Y(v)a_v=o_X(v)
\qquad\text{(1.22)}
```

をすべての名前付き辺 $`e:v\to w`$ と頂点について満たせば、
ただ一つのプロトコルの射に延長される。

**証明.**
空経路での可換性は恒等写像の性質であり、
経路 $`p:v\to w`$ と辺 $`e:w\to z`$ に対しては

```math
a_zX(e)X(p)=Y(e)a_wX(p)=Y(e)Y(p)a_v
```

となる。帰納法で全経路との自然性を得る。
両実現の作用は経路の同値類に依存するので、商圏のすべての射についても自然性が成立する。
観測の保存は式(1.22)そのものである。自然変換は対象ごとの成分で決まるので、一意である。□

頂点、名前付き辺、宣言関係、各状態集合が有限であるため、
命題1.37と1.38の入力は有限個の表で与えられる。
一方、閉路を繰り返す経路は任意の長さを取り得る。
全実行についての結論は、その列挙によらず、経路帰納と合同関係から得られる。

二つの実現をつなぐ意味保存射をadapterとして考える。
adapter $`q:X\to Y`$ と $`q':X'\to Y'`$ を比較するとき、
変更 $`a:X\to X'`$、$`b:Y\to Y'`$ がadapterを保つ条件は

```math
bq=q'a.
\qquad\text{(1.23)}
```

つまり、adapterを適用してから変更することと、
変更してから変更後のadapterを適用することが一致する。
自然変換の等式なので、これは各頂点での $`b_vq_v=q'_va_v`$ と同値である。
式(1.22)から、両辺はすべての実行と可換する。
可逆変更を調べる場合は $`a,b`$ を同型に制限する。
adapter $`q,q'`$ 自体は、引き続き一般の意味保存射として扱う。

## 1.10 意味論からAtom、操作、Lawを構成する

lensとプロトコルをAATの対象として表すには、操作名、状態値、状態集合、
操作の意味を、それぞれどこに保持するかを決める必要がある。
ここでは、型の役割と操作名をAtomに、個々の状態値をsourceに置く。
状態集合はarchitecture objectに、読取り・更新・遷移などの関数はoperationに保持する。
語彙を有限に保ちながら、状態を他の状態へ送る一般の写像も扱える配置である。

**構成1.39（型の役割と名前付き操作）.**
対象の役割の違いを関係の行き先に、操作名の違いを特別なAtomの像に記録する。
これにより、同じ状態関数として作用する操作も区別しながら、各操作にconfigurationの射を与える。

lens $`L=(C,g,p)`$ のAtom集合を、互いに異なる七つの記号

```math
\mathrm{At}_L=
\{*,\mathrm{state},\mathrm{view},\mathrm{read},
\mathrm{write},\mathrm{get},\mathrm{put}\}
```

とする。五つの座標の値域をすべてこの集合とし、座標写像を恒等写像とすれば、
定義1.1を満たす。プロトコルの語彙も同じ方法で、互いに異なる記号

```math
\mathrm{At}_Q=
\{*\}\sqcup
\{\mathrm{state}_v,\mathrm{observation}_v,\mathrm{observe}_v
\mid v\in Q_0\}
\sqcup\{\mathrm{edge}_e\mid e\in Q_1\}
```

から作る。いずれも空でない有限集合である。

選択された役割 $`t\in\mathrm{At}`$ に対し、configurationを

```math
C_t=(\mathrm{At},R_t,\varnothing),\qquad
R_t(a,b)\ \Longleftrightarrow\ b=t
```

と定める。すべてのAtomは族に含まれ、その関係は選択された役割へ向かう。
したがって、どの役割を表すconfigurationかは、関係の到達先 $`t`$ から分かる。
役割に対応する集合を構造データ $`S_{A_t}`$ に置き、
lensでは $`Q_{A_t}=v_0`$、プロトコルでは $`Q_{A_t}=*`$ とする。
役割ごとの集合は次のとおりである。

| 意味論 | 役割 | 保持する集合 |
| --- | --- | --- |
| lens | $`\mathrm{state}`$ | 状態 $`C`$ |
| lens | $`\mathrm{view}`$ | 表示値 $`V`$ |
| lens | $`\mathrm{read}`$ | 読取りの入力 $`C`$ |
| lens | $`\mathrm{write}`$ | 更新の入力 $`C\times V`$ |
| プロトコル | $`\mathrm{state}_v`$ | 頂点 $`v`$ の状態 $`X(v)`$ |
| プロトコル | $`\mathrm{observation}_v`$ | 頂点 $`v`$ の観測値 $`O(v)`$ |

lensのstateとreadには同じ集合 $`C`$ を置く。
その集合を、更新結果の役割と読取り入力の役割にそれぞれ使う。
writeには現在の状態と指定する表示値の組を置く。

これらの対象の間に、次の名前付き操作を与える。

| 操作名 | 始域と終域の役割 | 意味を与える関数 |
| --- | --- | --- |
| $`\mathrm{get}`$ | $`\mathrm{read}\to\mathrm{view}`$ | $`g`$ |
| $`\mathrm{put}`$ | $`\mathrm{write}\to\mathrm{state}`$ | $`(c,v)\mapsto p(c,v)`$ |
| $`\mathrm{edge}_e`$（$`e:v\to w`$） | $`\mathrm{state}_v\to\mathrm{state}_w`$ | $`X(e)`$ |
| $`\mathrm{observe}_v`$ | $`\mathrm{state}_v\to\mathrm{observation}_v`$ | $`o_X(v)`$ |

名前 $`m`$ を持つ操作 $`s\to t`$ には、Atom上の写像

```math
d_m(a)=
\begin{cases}
m & a=*,\\
t & a\ne *
\end{cases}
\qquad\text{(1.24)}
```

を割り当てる。表の始域の役割 $`s`$ はすべて $`*`$ と異なる。
したがって $`R_s(a,b)`$ なら $`b=s`$ であり、
$`d_m(b)=t`$、すなわち $`R_t(d_m(a),d_m(b))`$ となる。
族の保存は全Atomを含むことから、同一視の保存は空であることから従う。
よって $`d_m:C_s\to C_t`$ は実際にconfigurationの射である。

operationを、その名前、両端の対象、$`d_m`$、表の意味を与える関数の組として取る。
これは定義1.7のoperation readingを与える。$`d_m(*)=m`$ なので、
異なる名前は異なるconfigurationの射としても区別される。

**構成1.40（状態値を持つ抽出source）.**
lensとプロトコルのsourceを、それぞれ

```math
\begin{aligned}
\mathrm{Src}_L
&=1\sqcup C\sqcup V\sqcup(C\times V),\\
\mathrm{Src}_X
&=1\sqcup\bigsqcup_{v\in Q_0}X(v)
 \sqcup\bigsqcup_{e\in Q_1}X(\mathrm{src}(e))
\end{aligned}
\qquad\text{(1.25)}
```

とする。各直和の成分には、点、状態、view、更新入力、または辺入力というタグを付ける。
正規化は恒等、語彙・意味・解像度のパラメータは一元集合とする。
定義1.3の述語 $`V_D,M_D,R_D`$ は常に真とし、
$`E_D`$ を次の表で定める。

| sourceのタグ | 抽出するAtom |
| --- | --- |
| 点（両意味論） | 語彙のすべてのAtom |
| lensの状態 $`c`$ | $`\mathrm{state},\mathrm{read},\mathrm{get}`$ |
| lensのview $`v`$ | $`\mathrm{view}`$ |
| lensの更新入力 $`(c,v)`$ | $`\mathrm{write},\mathrm{put}`$ |
| プロトコルの頂点 $`v`$ の状態 $`c`$ | $`\mathrm{state}_v,\mathrm{observation}_v,\mathrm{observe}_v`$ |
| プロトコルの辺 $`e`$ の入力状態 $`c`$ | $`\mathrm{edge}_e`$ |

点を選択sourceとすれば、その抽出族は語彙全体であり、有限である。
状態値は式(1.25)のsourceに保持され、抽出述語はそのタグを読む。

lensの射 $`h:L\to L'`$ は、sourceの各成分上で
恒等、$`h`$、恒等、$`h\times\mathrm{id}_V`$ を用いる写像を定める。
プロトコルの射 $`a:X\to Y`$ は、状態成分で $`a_v`$、
辺入力成分で $`a_{\mathrm{src}(e)}`$ を用い、点を点へ送る。
これらとAtom上の恒等写像は、定義1.27の射を与える。
正規化との可換性は恒等写像の性質であり、抽出の同値はタグを保存することから従う。

source写像の恒等と合成は、各成分での恒等と合成に一致する。
さらに、source写像から状態成分を読み出せば $`h`$ またはすべての $`a_v`$ が得られる。
したがってこの対応は射に関して忠実であり、非単射の意味保存写像も保持する。

**命題1.41（意味論の法則を表すLaw）.**
lensの集合 $`C,V`$、またはプロトコルの状態集合族 $`(S_v)`$ を固定する。
法則をまだ課していない操作データ $`d`$ を考える。
lensでは $`d=(g,p)`$、プロトコルでは $`d=((T_e),(b_v))`$ である。
このデータから、Lawfulであることがそれぞれの意味論の法則と同値になる
architecture object $`A_d`$ とequation systemを構成できる。

**証明と構成.**
各法則を入力値ごとの等式に分け、その等式が成立するときに零、
成立しないときに一となる残差を作る。

$`A_d`$ のconfigurationを $`C_*`$、構造データを操作データ $`d`$ とする。
lensでは基準view、プロトコルでは一元集合の元を量として保持する。
方程式の添字集合 $`K`$ の添字は、次の各等式とその入力値の組とする。

```math
\begin{array}{ll}
\text{lens:}&
p(c,g(c))=c,\quad
g(p(c,v))=v,\quad
p(p(c,v),w)=p(c,w),\\[2pt]
\text{プロトコル:}&
T_{\ell_j}(c)=T_{r_j}(c),\quad
b_w(T_e(c))=O(e)(b_v(c)).
\end{array}
\qquad\text{(1.26)}
```

lensではそれぞれ $`c`$、$`(c,v)`$、$`(c,v,w)`$ を走らせる。
プロトコルでは宣言関係とその始点の状態、および辺 $`e:v\to w`$ と
$`c\in S_v`$ を走らせる。すべての添字をrequiredとする。

文脈は一つ $`W`$ とし、そのsupportは一元集合から全Atomを読むものとする。
軸とobservableも一元集合とする。この文脈は、全Atomを族に含む $`A_d`$ の文脈になる。
定数環前層と方程式座標を

```math
O_E(W)=ℤ[x_{(i,a)}\mid (i,a)\in K\times\mathrm{At}],
\qquad \nu_{W,i,a}=x_{(i,a)}
```

で与える。評価する対象 $`A`$ が同じ型の操作データを持つとき、そのデータに対する
添字 $`i`$ の等式を $`P_i(A)`$ とする。
対応する型の構造データを持たない対象では $`P_i(A)`$ を偽と定める。
残差を定数多項式

```math
\varepsilon_{W,A,i,a}=
\begin{cases}
0 & P_i(A),\\
1 & \text{それ以外}
\end{cases}
\qquad\text{(1.27)}
```

とする。制限は恒等なので、式(1.1)は成立する。

式(1.26)がすべて成立すれば、$`A_d`$ のすべての残差は零である。
逆にLawfulなら、各 $`i`$ について文脈 $`W`$ とAtom $`*`$ で評価する。
$`ℤ`$ 上の多項式環では $`0\ne1`$ なので、
式(1.27)の消滅は $`P_i(A_d)`$ を含意する。
これで式(1.26)のすべての等式を得る。
プロトコルの場合は、命題1.37により、これらが関手と自然な観測を定める条件に一致する。□

たとえば $`C=V=\{0,1\}`$、$`g(c)=c`$、$`p(c,v)=c`$ とすると、
$`g(p(0,1))=0\ne1`$ である。この入力に対応する残差は実際に $`1`$ となり、
構成された対象はLawfulではない。

**定義1.42（構成された型付き対象の間の射）.**
構成1.39の役割、対象、意味を持つ名前付き操作をまとめて $`𝒯(L)`$ または
$`𝒯(X)`$ と書く。その間の型付き射を、各役割の集合上の写像で、次の条件を満たすものとする。

- **lens**：stateとreadの写像を同じ $`h:C\to C'`$ とし、
  viewの写像を恒等、writeの写像を $`h\times\mathrm{id}_V`$ とする。
  getとputの二つの可換性を要求する。
- **プロトコル**：stateの写像を $`a_v:X(v)\to Y(v)`$、
  observationの写像を恒等とし、各edgeとobserveの可換性を要求する。

成分ごとの恒等と合成によって、これらの対象と型付き射は圏をなす。

構成1.40は、この型付き射が与える状態写像を、抽出doctrineのsource写像へ結びつける。

**命題1.43（意味保存射の回復）.**
構成した対象から役割の集合と操作の意味を読み出すと、もとの状態集合、読取り、更新、
辺の作用、観測を得る。さらに、次の自然な全単射が成り立つ。

```math
\begin{aligned}
\mathrm{Hom}_{\mathrm{Lens}(V,v_0)}(L,L')
&\simeq\mathrm{Hom}_{\mathrm{typ}}(𝒯(L),𝒯(L')),\\
\mathrm{Hom}_{\mathrm{Prot}(Q,\Pi,O)}(X,Y)
&\simeq\mathrm{Hom}_{\mathrm{typ}}(𝒯(X),𝒯(Y)).
\end{aligned}
\qquad\text{(1.28)}
```

**証明.**
対象については、構成1.39で格納した集合と関数をそのまま射影すればよい。
操作名も式(1.24)の $`*`$ での値から回復する。

lensの意味保存射 $`h`$ は、定義1.42の四つの役割上の写像を定める。
getとputの可換性は式(1.17)なので、型付き射を得る。
逆に型付き射からstateの写像を取れば、二つの可換性によりlensの射となる。
他の役割上の写像はstateの写像から定まるので、二つの操作は互いに逆である。

プロトコルでも、意味保存射の頂点成分をstateの写像とすれば型付き射を得る。
逆に型付き射のedgeとobserveの可換性は式(1.22)であり、
命題1.38によって全経路についての自然変換が一意に回復する。
この二つの構成も、各頂点の成分で互いに逆である。

いずれも恒等を恒等へ、合成を成分ごとの合成へ送る。
したがって式(1.28)は両端の前合成・後合成に関して自然である。□

lensの型付き射は、命題1.34によって基準fiber間の写像だけから回復できる。
プロトコルの型付き射は、有限個の頂点写像と生成辺の可換性から全実行へ延長される。
可視変更 $`u`$ を含むlensでは、viewの写像を $`u`$、
writeの写像を $`h\times u`$ とすれば、二つの操作の可換性は式(1.20)になる。
プロトコルのadapterとの可換性も、頂点成分を読み戻すことで式(1.23)と一致する。

## 本章のまとめ

本章では、抽出、対象形成、操作、Law、局所性の選択を明示したうえで、
相対的なアーキテクチャとその比較を構成した。主要な結果は次の四点である。

- **対象の生成。** 抽出した有限Atom族から基点となる対象を作る。その対象を含み、
  許された操作で閉じた最小の対象族は、有限列の操作で到達できる対象全体に等しい（定理1.18）。
  Lawの成立は、detectorの健全性と必須方程式についての完全性の下で、
  必須circuitの不在と同値になる（命題1.16）。
- **局所構造の構成。** 文脈と被覆からsiteを、座標・構造関係と整合する制限写像から
  環の前層を構成した。局所データの貼り合わせを与える層化も構成した（§§1.5–1.6）。
- **readingの比較。** 抽出・core・幾何の各段階に対象と射を定め、
  それらを結ぶ射影関手を構成した（定理1.31）。
- **CSの意味論の回復。** 本章で扱うlensとプロトコルを、共通の対象・操作・Lawの枠組みで
  記述した。構成したLawの成立は元の法則の成立と同値であり（命題1.41）、
  型付き射は元の意味保存射と一対一に対応する（命題1.43）。

次章では、記号的な方程式座標からイデアルを構成する。
座標の評価と対象ごとの残差を結ぶ実現の条件の下で、
Lawを満たす部分を局所幾何の中で記述する。
