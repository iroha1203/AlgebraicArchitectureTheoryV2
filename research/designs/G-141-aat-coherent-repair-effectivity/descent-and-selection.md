# 合法な局所修復、Čech複体、選択のdescent

## E7 — 観測の全参照を保持する修復係数

原始宣言のcontextに、各Law・観測式・語翻訳・固定宣言の全参照を含める。許容変更域は、変更可能と指定した成分を自由とし、固定成分を零とした加群から生成する。そのうち局所Lawと固定観測を保つ部分は、原始微分のkernelを取って作る。affine Lawでは同じ線形式を有限変位へ使える。

参照に閉じたcontext間の制限は成分射影であり、各残存Law・観測式の全入力も残る。従って微分の可換式を原始term帰納法で検査でき、合法補正の制限が定まる。作用は成分ごとの加法、制限との可換性は同じ加法の式である。matchingする局所補正を各成分で貼れば、各Lawは全参照を含むcontextで成立するため、大域でも合法な実修復になる。

必要性を具体的に確認する。reading `T↦X+Y`、基点0、`Q[ε]/(ε²)` では `(δX,δY)=(ε,−ε)` は観測を保つ。ところが `{X}` と `{Y}` だけに分けてそれぞれ `T↦X`、`T↦Y` と読めば、観測固定の局所係数は零となり、この合法な大域差分を制限できない。観測条件を単に落とせば `(ε,0)` もmatchingして組み立つが、観測を `ε` だけ変えてしまう。

正しい被覆では `T=X+Y` を `{X,Y,T}` のcontextに置き、そこに `δX+δY=0` を保持する。小さいcontextには、全参照を持たない観測式を別の式へ改変せず、定義される宣言だけを制限する。この合併contextを含むcoverなら上記の制限と組立てが成立する。

## 定理 E8 — 全宣言Čechと全syzygy

参照に閉じた宣言被覆 `(U_i)` を取り、全多重交差を保持する。自由な変数係数とLaw残差係数の二項複体にČechを適用する：

```math
T_{\mathrm{raw}}^{p,q}
=\prod_{i_0<\cdots<i_p}
\begin{cases}
\prod_{\text{変数 }\xi\in U_{i_0}\cap\cdots\cap U_{i_p}}M_\xi&q=0,\\
\prod_{\text{Law }\ell\in U_{i_0}\cap\cdots\cap U_{i_p}}M_\ell&q=1.
\end{cases}
```

縦微分は原始Jacobian、横微分はrestrictionの交代和とする。Lawを含むcontextはその全変数を含むので両微分は可換し、total微分 `d_tot=δ_Cech+(-1)^p d_vert` の平方は零である。

各宣言label `ξ` について、それを含むchart集合 `I_ξ` は非空。`ξ` が一つの多重交差に属す条件は、その全添字が `I_ξ` に属すことである。従ってこのlabelのČech支持はfull simplex。`i_ξ∈I_ξ` を一つ選び、cochainへその添字を挿入する標準の符号付きmapが、拡大Čech複体の収縮を与える。全labelの積を取っても完全性を保つ。

横方向のコホモロジーを先に計算すると、大域二項複体 `D⁰→D¹` だけが残る。したがって自然に

```math
H^0(T_{\mathrm{raw}})\cong\ker d^0,\qquad
H^1(T_{\mathrm{raw}})\cong\operatorname{coker}d^0.
```

E1のlawfulな基準と平方零拡大を固定すると、全大域syzygyを使うE2の `d¹` は `d⁰` の像を消すので

```math
0\longrightarrow H^1(D)
\longrightarrow H^1(T_{\mathrm{raw}})
\xrightarrow{\ [r]\mapsto(\sum_i s_i(x)r_i)_s\ }
\prod_{s\in S}M
```

は完全である。右端への全射性は主張しない。実残差は原始syzygy恒等式により右mapのkernelに入り、その一意な逆像はE3の `o_P` である。Law値とJacobianだけで任意の `coker d⁰` の元を実障害とみなすことはできない。

被覆の細分化は各labelの同じ値を新しい交差へ制限する。global augmentationと可換なので、上の同定と指定類も可換になる。細分化の添字選択を変えたmapは、同じsimplexの挿入homotopyで比較できる。

K0/K1のincidenceも同じ宣言supportから生成できるが、supportだけでは縦微分・syzygyを決めない。診断複体との同型を使う際はこの二つのmapも同定する必要がある。Gのadapter族ではその係数と微分を実式から作り、同じ指定類をG-142へ渡す。

## C7 — 補完、固定長経路、状態移送のdescent

G-140 Fの有限図式補完・固定長経路、Gの移送liftを取る。対象、全state map、語翻訳、固定部分の同型、phase・domainを原始dataとして保持する。宣言coverはE7のsupportから、係数coverはZariski被覆から別に作る。

局所候補と各二重交差の実際の同型、三重交差のcocycleを与える。G-139の対象と全Homのdescentで各頂点と各射を貼る。各固定部分との比較同型も貼り、恒等・合成・可換四角形・移送の `hm=ι` は局所で同じ二辺が一致することから大域で成立する。domainは同じ指定部分域のpullback、語翻訳はG-140 C3.1の選択blockとして運ぶ。

従って大域補完とその全比較同型から局所descent dataへの関手は同値である。大域dataの全fieldを制限してから貼ると元へ戻り、局所dataから貼って戻すと指定された同型を通して戻るためである。規則を大域入力として固定した場合はその同じ規則を制限し、任意のraw規則名を局所で別々に選んだものが自動的に大域規則となるとはしない。任意集合値の評価部分関手を追加した場合の局所性も、G-140 Eで区別した条件に従う。

図式の制限は頂点・辺を落とし、経路の連結は辺を並べ、移送の合成はG-140 G3の実際のfiber productで行う。これらの各fieldへの作用は制限と可換なので、descentの一意性から組立てとの比較も可換となる。matchingしていない候補の補正は次項で構成する。

## C8 — Affine・平方零問題の全修復groupoid

まずlawfulな基準と指定された平方零kernelを固定する。宣言coverについてはE8の全宣言と全syzygyを用いる。係数の有限principal affine coverでは、各実際のopen上でE4のconormalを使い、層の複体

```math
\mathscr D^0=\mathcal Hom(E_x,\widetilde M)
\longrightarrow
\mathscr D^1=\mathcal Hom(N_x,\widetilde M)
```

を作る。右項は各open上で全syzygyを消す残差mapの層である。unmarked版ではE6の還元が恒等の同型の層 `\mathscr D^{-1}` とその無限小作用も加える。以下のČech totalには、この層の各交差上の**実section**を用いる。全syzygyを添字とする無限積 `D²=∏_(s∈S)M` を大域で作ってから局所化する操作は使わない。

大域加群複体とのE4の準連接比較には、さらに `N_x` の有限表示が必要である。例えば `k` がNoetherianで `P` が有限表示ならこれが成立し、両Homの局所化同型と各項のČech非輪状性から、大域 `bar D` とこのtotalを比較できる。同じ条件ではE2のsyzygy加群に有限生成系を取り、次数2を有限積 `M^q` とした複体も使える。一般の係数環での全修復分類は、上で定義した実sectionのtotalについて述べるため、この追加条件を要求しない。

局所ambient実現 `tilde x_i` と、還元上の同型をliftしたambient同型 `g_ij`（jからiへ）を選ぶ。有限局所自由module間の同型は、Homのprojectivityによりliftでき、還元で可逆なliftはnilpotent性により可逆である。基底chartでは同じ事実は可逆matrixのliftで確認できる。還元同型で係数を同定した上で、局所Law残差を `r_i`、操作保存の失敗を `Δ_ij=g_ij(tilde x_j)−tilde x_i`、三重交差の合成の失敗を

```math
\omega_{ijk}=1-g_{ij}g_{jk}g_{ik}^{-1}
```

とする。最後の差は平方零kernelに値を持つ無限小自己同型である。これらはそれぞれČech bidegree `(0,1),(1,0),(2,−1)` に属す。横微分を `δ`、縦微分を `d` とし、`d_tot=δ+(-1)^p d` を使う。

E2の局所全syzygy表示も併記すると、cycle条件の四成分は

```math
d^1r=0,\qquad
\delta r-d^0\Delta=0,\qquad
\delta\Delta+d^{-1}\omega=0,\qquad
\delta\omega=0.
```

第一式は原始syzygy恒等式をambient liftへ代入して得られ、`r` が上の `\mathscr D¹` に入る理由である。第二式は二重交差上のTaylor式で、二個のkernel因子の積は零。第三式は三重交差で `g_ij g_jk` と `g_ik` の作用差を展開した式で、上の `ω` の負号と一致する。第四式は **四重交差** で `(g_ij g_jk)g_kl=g_ij(g_jk g_kl)` を展開した式である。無限小自己同型同士の積の誤差は零なので、還元同型による係数の移送の下で交代和が零になる。

局所ambient選択を `a∈C^{0,0}` だけ変え、同型liftを `g'_ij=(1−b_ij)g_ij`、`b∈C^{1,−1}` とする規約では、defectの変化は

```math
(r,\Delta,\omega)\longmapsto
(r+d^0a,\ \Delta+\delta a-d^{-1}b,\ \omega+\delta b).
```

これは `d_tot(a,b)` である。従って指定類は選択に依存しない。

従って指定類 `o∈H¹(Tot D)` を得る。`o=0` なら実際の補正tupleを選んでdefectを消し、C7で実補完へ貼れる。逆に実補完を制限して元の選択との差を取れば、その微分がdefectとなる。二つの補正の差はtotal 0-cycle、還元同型による比較はtotal次数−1の微分だから、非空な全修復の同型類は `H⁰(Tot D)` のtorsor、各自己同型群は `H^(−1)(Tot D)` となる。

marked版では還元同型の自由が消えて集合版となる。一般のaffine有限変位にはE6の二項複体 `[H→V]` を使う。そのČech totalでは、局所残差の差が `L` を適用した局所補正の差に等しく、三重差が零になるため、同じcycle・補正・貼合せの証明が厳密に成立する。次数2を追加する場合は `d¹L=0` と `d¹(b−Lp)=0` を別に原始式から導く。lawfulでない基準での多項式syzygyの評価は使わない。

affine版の加法分類はmarked集合版、または許容同型そのものが原始的に加法作用として指定された場合に適用する。一般のunmarked有限変位ではG-140の実fiber groupoidを保持する。例えばLawなしrank1実現の全自己同型は乗法群 `Q×` であり、加法群 `End(Q)` ではない。非線形の有限変位へも、この加法複体だけで全修復を分類する結論を拡張しない。

全mapは原始保存式・restriction・合成から生成されるため、C7の図式制限、連結、移送合成にも同じ指定類と全修復を比較できる。

## C9 — 指定有限étale被覆と選択

原始Lawで定義された選択family `E→B` と有限étale被覆 `V→B` に対し、局所選択は `E(V)` の実際の点である。二つのpullbackは `V×_BV` で原始式を評価して比較する。これらが一致し三重交差で整合すれば、表現可能関手のfaithfully flat descentにより一意の大域sectionを得る。groupoid値の場合は一致の代わりに実同型とcocycleを保持し、G-139の同じdescentを使う。

G-142 W5の指定familyでは、代数閉体 `k`、`char k≠2` とし

```math
B=\operatorname{Spec}k[t,t^{-1}],\qquad
E=\operatorname{Spec}k[z,z^{-1}],\qquad t=z^2.
```

これは基底 `1,z` を持つrank2の有限free拡大で、微分 `2z` がunitなのでétaleかつ全射である。`μ₂` は `z↦ζz` で作用し、

```math
E\times\mu_2\longrightarrow E\times_BE,\qquad
(z,\zeta)\longmapsto(z,\zeta z)
```

は逆 `(z₁,z₂)↦(z₁,z₂/z₁)` を持つ。従って原始Law `z²=t` からtorsor条件を得る。被覆 `E→B` 上では `z` 自身が選択を与える。

一般のこの局所選択 `z_i` の比 `ζ_ij=z_j/z_i` は `μ₂` に入り、`ζ_ik=ζ_jkζ_ij`。`z'_i=η_i z_i` と修正すると新しい比は `η_jζ_ijη_i^{-1}`。従ってcocycleがcoboundaryであることと、局所選択を修正して一致させ、大域regular sectionを得ることが同値である。

全幾何点では非零 `t` の平方根が存在する。しかし大域sectionがあれば `k[t,t^{-1}]` のunit `z` が `z²=t` を満たす。この環のunitは `ct^m` であり、指数の式 `2m=1` は不可能。よって大域sectionはなく、指定cocycleはcoboundaryでない。点ごとの存在・被覆上の選択・大域選択を、同じ原始Lawの三つの存在問題として比較できる。
