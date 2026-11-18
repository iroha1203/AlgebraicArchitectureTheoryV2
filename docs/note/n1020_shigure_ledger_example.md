# SHIGUREの台帳例 — n1020 §16

本頁は[n1020](n1020_shigure_polynomial_specializations.md)の§16を収める。
節番号を共有し、一般の多項式構成と診断は本編の§1–15、
ArchSig側の解釈と応用は[§17](n1020_shigure_polynomial_specializations.md#archsig-application)を参照する。

<a id="ledger-example"></a>
## 16. 主例 — 単一台帳からbase＋delta台帳への移行

この例の台帳・snapshot・commitは、以下で指定する状態空間と演算に付けた名称である。
before・afterは二つの原始表示を区別する添字とする。命題は、その表示、係数環、
操作語、phase、観測写像について述べ、同じ入力を持つすべての実現を量化する。

### 16.1 原始表示から全操作語の意味保存へ

beforeの状態は$`D=R`$、公開操作$`\mathrm{apply}_u(x)=x+u`$、$`\mathrm{read}(x)=x`$とする。
afterの状態は$`B\oplus C=R^{2}`$で、$`B`$がbase、$`C`$がdelta。生成元を固定したrank1型$`D,B,C`$と
単項演算$`p_B,p_C,i_B,i_C,j_B,j_C`$をAtomから生成する。

```math
p(v_B,v_C)=av_B+bv_C,\quad i(u)=(cu,du),\quad j(t)=(rt,st),
\qquad ac+bd=1,\quad ar+bs=0.
```

applyは$`v\mapsto v+i(u)`$、compactは$`v\mapsto v+j(t)`$。加法と単項演算から作用を作る。
初期状態で$`p(v_{0})=x_{0}`$とし、compactをbeforeの空語へ送れば、生成Lawからapply/compactの
全有限語でreadが一致する。非零環$`R`$では$`p`$は非単射であり、同じ公開readを持つ内部状態を一つのfiberへまとめる。

係数実現のmoduliは、$`(p,i)\mapsto\begin{pmatrix}c&-b\\d&a\end{pmatrix}`$により$`\mathrm{SL}_{2}`$と同定する。
さらに$`\ker p=R(b,-a)`$から$`j=\mu (b,-a)`$を一意に得て、全体は$`\mathrm{SL}_{2}\times \mathbb{A}^{1}`$になる。
$`p=(1,1)`$を固定した族は$`i=(\lambda ,1-\lambda )`$、$`j=\mu (1,-1)`$で、$`B_0=\mathbb{A}^2_{(\lambda,\mu)}`$である。
変換係数$`\lambda ,\mu`$の自由と、一実現の状態fiber $`p^{-1}(x)`$の自由は別の対象として保持する。

この固定$`p`$は、異なる型の$`p_B,p_C`$をそれぞれの名前付き生成元で読むmarked fiberである。
このfiberを表すため、rank 1・生成元数1の一型$`D`$と単項$`\lambda ,\mu`$だけの
係数表示$`O`$を作る。$`D`$の三つのコピー上で$`p=(\mathrm{id},\mathrm{id})`$、$`i=(\lambda ,\mathrm{id}-\lambda )`$、$`j=(\mu ,-\mu )`$を生成すると、
$`\mathrm{Sem}_O`$とこのmarked fiberの自然同型を構成できる。以下の消去はこの$`O`$に対して行う。
生成元を忘れた三型のgroupoidとの比較では、さらに型ごとの自己同型を追う必要がある。
このコピー同定の下で、現在のdeltaを引数に取る派生原子操作を

```math
\mathrm{compact}_{\mathrm{all}}(B,C)=\mathrm{compact}_{C}(B,C)=(B+\mu C,(1-\mu )C)
```

と定める。
これは$`p`$を保つが、固定引数のtranslation $`\mathrm{compact}_t`$とは別の操作である。

### 16.2 局所実現と修復

共有型$`D`$に演算$`\lambda`$を置き、base文脈には$`p_Bi_B=\lambda`$、delta文脈には$`p_Ci_C=\mathrm{id}-\lambda`$を置く。
各文脈は式の全参照を含み、共有実現$`\lambda`$が一致すれば合成Law $`pi=\mathrm{id}`$を導ける。
$`R=\mathbb{Q}`$、$`p_B=p_C=\mathrm{id}`$の下でbaseの局所実現を$`c=0,\lambda _B=0`$、deltaの局所実現を$`d=0,\lambda _C=1`$とすると、
各局所Lawは成立しても組立て不能になる。共有する演算$`\lambda`$の実現が一致しないためである。

許容変更を係数の加法として指定すると、修復は$`\Delta c+\Delta d=1`$。
両係数を変更できるとき全解は$`(t,1-t)`$、自由方向は$`(1,-1)`$。base固定なら$`(0,1)`$だけ、
両方固定なら不存在となる。修復の許容域・残差・全解を同じ原始表示から生成し、
G-141 Eのaffine特殊化として比較する。

### 16.3 観測を細かくすると失敗する

上の意味はapply/compact完了点のreadに相対的である。
$`R=\mathbb{Q}`$でwriteBとwriteCの間にもreadを許すと、$`\lambda =1/2,u=2`$で途中値は$`x+1`$になり、beforeの
atomic $`\mathrm{apply}(2)`$が許す$`x`$または$`x+2`$と一致しない。compactも二書込みの間には非零の値を
見せ得る。細粒度操作を含むprotocolには、その観測言語での保存Lawが必要になる。
$`pi=\mathrm{id},pj=0`$は完了点の保存Lawであり、途中readの保存を細粒度のLawとして追加する。

### 16.4 独立には安全な二変更が更新を失う

compactをsnapshot取得とcommitへ分ける。$`\delta =1-\lambda`$をdeltaへの書込み係数とし、
Idleは$`(B,C)`$、Busyは$`(B,C,h)`$で$`h`$がsnapshotを保持する。一つのcompactorだけを許す。

```math
\begin{aligned}
\mathop{\mathrm{begin}}\nolimits (B,C)&=(B,C,C),\\
\mathop{\mathrm{apply}}\nolimits ^{\rm Busy}_u(B,C,h)&=(B+(1-\delta)u,C+\delta u,h),\\
\mathop{\mathrm{finish}}\nolimits (B,C,h)&=(B+\mu h,(1-\mu)C).
\end{aligned}
```

applyは両phaseで可能、beginは$`\mathrm{Idle}\to \mathrm{Busy}`$、finishは$`\mathrm{Busy}\to \mathrm{Idle}`$の原子操作とする。
readは$`B+C`$。begin・finishをbeforeの空語へ送る。snapshot後のapplyの総和$`U`$について、
finish後の公開値の誤差は$`-\mu \delta U`$となる。従って全ての許可有限経路で意味を保つ条件は
$`\mu \delta =0`$である。十分性はBusyの不変量$`\mu (h-C)=0`$、必要性は$`\mathrm{begin};\ \mathrm{apply}_1;\ \mathrm{finish}`$から得る。

deltaへの書込みだけを導入する変更（$`\mu =0`$）と、集約だけを導入する変更（$`\delta =0`$）は安全だが、
組合せには積の制約が生じる。同じ原始操作から意味保存族$`\mathrm{Spec}\,k[\delta ,\mu ]/(\mu \delta )`$を生成する。
体上では二つの座標軸の合併で、原点の接空間は二次元だが、二次の条件が同時変更を妨げる。
$`\delta =\mu =\varepsilon`$は$`k[\varepsilon ]/(\varepsilon ^{2})`$では合法、$`k[\varepsilon ]/(\varepsilon ^{3})`$ではどの二次補正を加えても残差$`\varepsilon ^{2}`$が残り、
公開readは$`1-\varepsilon ^{2}`$になる。G-141 Fの初回次数$`\nu =2`$と、この失われた更新を同じ式で同定する。
左文脈$`E=\mu \delta`$と右文脈$`E=0`$の局所liftの差も、共有部の同じ$`\varepsilon ^{2}`$である。

演算の変更$`\mathrm{finish}_{\mathrm{snap}}(B,C,h)=(B+\mu h,C-\mu h)`$では、Busyの状態Law $`\mu (h-C)=0`$も除き、
全$`R^{3}`$を状態とする。比較関係$`x=B+C`$でreadを厳密に保存し、全$`\delta ,\mu`$が許される。
$`R=\mathbb{Q}`$で旧状態Lawを残すと$`\delta =\mu =1`$の$`\mathrm{begin};\ \mathrm{apply}_1`$が閉じないので、遷移と状態表示の両方を変更する。
旧合法Busy上では両finish自体が一致し、旧状態の包含が遷移と可換になる。
applyを挟まないbeginとの合成は、両finishとも$`\mathrm{compact}_{\mathrm{all}}`$に一致する。
$`R=\mathbb{Q}`$、$`\mu =1`$で$`\mathrm{compact}_{\mathrm{all}}`$は非単射なので、固定引数$`\mathrm{compact}_t`$やその固定有限語とは同一視できない。
係数の閉埋め込み
$`V(\mu \delta )\to \mathbb{A}^{2}`$と状態の包含から、snapshot量だけを差し引く修正で制約が消えることを説明する。

<a id="design-search"></a>
#### 保存条件と評価条件から変更を分類する

原始式の代入からschemeの射を計算する過程も固定する。
Busyのideal生成元を$`g=\mu (h-C)`$と書くと、
$`\mathrm{begin}^*(g)=0`$、$`\mathrm{apply}_u^*(g)=g-\mu\delta u`$であり、finishによるread差は$`g`$になる。
従って$`k[\delta ,\mu ]/(\mu \delta )`$上では全遷移が指定された状態schemeを結び、
公開readと操作語の翻訳を保つ。必要性は同じ原始経路のread差$`-\mu \delta`$から従う。
このidealの計算が、状態の射・全操作語・係数の解空間を結ぶ。

基礎体$`k`$を固定し、beforeを§16.1の単一台帳、比較を$`p`$、語翻訳を§16.4のものに固定する。
候補の基準係数を$`\delta =\mu =0`$とし、許容変換をまず係数$`\delta ,\mu`$の変更とする。
評価条件として、集約係数に$`D(\mu )`$、deltaへの書込み係数に$`D(\delta )`$を指定する。
体上では、それぞれの係数が非零であるという条件になる。
schemeの全$`R`$点では、これらは単元条件になる。

| 許容変換と評価条件 | 意味を保つ変更の全解 |
| --- | --- |
| 係数変更、評価条件の追加なし | $`V(\mu \delta )`$：二つの軸と原点のscheme構造 |
| 係数変更、集約を有効化 | $`V(\delta )\cap D(\mu )\cong \mathbb{G}_m`$：delta書込みを止める必要がある |
| 係数変更、delta書込みを有効化 | $`V(\mu )\cap D(\delta )\cong \mathbb{G}_m`$：集約を止める必要がある |
| 係数変更、両方を有効化 | 空。$`\mu ,\delta`$を可逆にすると$`\mu \delta =0`$から$`1=0`$ |
| 差し引く量とBusyの状態表示も変更可能にし、両方を有効化 | 下の変換族では$`\rho =1`$が強制され、全解は$`\mathbb{G}_m^{2}`$ |

最後の行では、差し引く量を現在値とsnapshot値のaffineな組合せに変更する規則を許す。
その係数$`\rho`$を探索変数とし、次を原始変換式にする。

```math
 \mathop{\mathrm{finish}}\nolimits _\rho(B,C,h)
   =\bigl(B+\mu h,\ C-\mu((1-\rho)C+\rho h)\bigr).
```

read差は$`g_\rho =\mu (1-\rho )(h-C)`$である。Busyの状態Lawをこの$`g_\rho =0`$として生成すると、
$`\mathrm{begin}^*(g_\rho)=0`$、$`\mathrm{apply}_u^*(g_\rho)=g_\rho-\mu\delta(1-\rho)u`$となる。
同じ必要性の経路から、全許可語を保つ係数族は正確に

```math
\mathrm{Spec}\,k[\delta ,\mu ,\rho ]/(\mu \delta (1-\rho ))
```

である。$`\rho =0`$のfiberは旧方式、$`\rho =1`$のfiberは$`\mathrm{finish}_{\mathrm{snap}}`$である。
評価条件$`D(\mu \delta )`$を課すと、座標環内で$`\rho =1`$が従う。従って許した変換式の族から、
両方を有効にする修正としてsnapshot値だけを差し引く式を導ける。
$`\mu ,\delta`$の自由は残り、全解は$`\mathbb{G}_m^{2}`$となる。

$`\rho =1`$では$`g_\rho =0`$が恒等式なのでBusyは全$`R^{3}`$になる。
旧合法状態からの包含と遷移の可換性は既述の$`g=0`$から証明する。
保存する意味は公開readと全許可語であり、Busy不変量は変更可能な状態表示に属する。
旧Busy Law自体を固定した許容変換域ではapplyの閉性が$`\mu \delta =0`$を要求し、
同じ評価条件$`D(\mu \delta )`$の解空間は空のままである。
この探索の完全性は宣言したaffine変換式について証明し、式の許容域を表示とともに残す。

解空間の出力には、係数点、公開状態への比較$`p`$、phase・操作語の翻訳を保持する。
原点の二つの一次方向は自由でも、同時方向には既述の二次障害がある。
ここでの障害は二つの係数変化を同時に実現する問題から生じる。
同じ中間対象を持つ意味保存射の合成は、各射の保存方程式から保存則を導く。

<a id="operational-descent"></a>
### 16.5 局所adapterから実際の障害と診断類を結ぶ

同じ台帳を複数の局所実現へ分ける。$`p=(1,1)`$、$`v=(1,-1)^{T}`$、$`i_\lambda =(\lambda ,1-\lambda )^{T}`$とし、
局所実現を結ぶadapterを$`g_b=I+bvp`$とする。$`pv=0`$から
$`g_cg_b=g_{b+c}`$、$`g_b^{-1}=g_{-b}`$、$`pg_b=p`$、$`g_bi_\lambda=i_{\lambda+b}`$、$`g_bj_\mu=j_\mu`$を導く。
公開read・$`\mathrm{apply}_u`$・$`\mathrm{compact}_t`$を、同じ外部引数$`u,t`$で保つ具体的な状態比較である。

この節の操作言語は§16.1の固定引数の原子操作とする。$`\mathrm{compact}_{\mathrm{all}}`$の引数選択とsnapshot phaseへの
輸送は追加の証明義務である。$`R=\mathbb{Q}`$、$`\mu =1`$では$`g_1\,\mathrm{compact}_{\mathrm{all}}(1,0)=(2,-1)`$だが、
$`\mathrm{compact}_{\mathrm{all}}\,g_1(1,0)=(1,0)`$なので、派生操作の可換性は固定引数の比較からは得られない。
例えば$`\lambda =\mu =1`$は§16.4で安全だが、$`g_1`$で移した$`\lambda' =2,\mu' =1`$では同じsnapshot protocolのreadが
$`\mathrm{begin};\ \mathrm{apply}_1;\ \mathrm{finish}`$で2となる。原子操作を保つadapterだけでは、$`h`$とphaseの比較は得られない。

三つの局所実現をcycleでつなぎ、固定したadapter値$`b_{01},b_{12},b_{20}`$を持たせる。
原始比較Lawは$`\lambda _j-\lambda _i=b_{ij}`$。各局所比較は作れても、一周の和$`b_{01}+b_{12}+b_{20}`$が
非零なら、同じ大域update $`i`$を組み立てられない。有限比較表示から局所系$`E_b`$と
$`0\to R\cdot v\to E_b\to R\to 0`$を構成し、操作$`i`$を$`p`$のsplittingとして読む。
underlyingな状態の図式と、操作$`i`$を追加した図式の実現を分ける。

局所splittingの修復係数は$`\ker p=R\cdot v`$であり、第1成分から$`R`$との同型を作る。
既存SAGAの増加pairからgraphの向きへ符号付きで移した残差は$`\lambda _j-\lambda _i-b_{ij}`$、指定類は$`[-b]`$。
三角形では$`(c_{01},c_{02},c_{12})\mapsto (c_{01},c_{12},-c_{02})`$を使い、SAGAの微分とgraphの微分を可換にする。
G-142では同じ被覆とinterface sourceをK0/K1へ送り、readoutを補正$`v`$の公開値$`p(v)=0`$
から生成する。整数上の指定障害類を既存$`\mathbb{Q}`$診断へ送り、cycleの$`H^{1}`$のtorsion-free性から
零性を反映する。次元$`H^{1}=1`$という数だけでなく、この指定類が零かどうかが組立てを判定する。
既存G-125の比較写像は使うが、既存反映定理の共通target支持条件はcycleでは満たされない。
各cellの同じlabelとspanning treeから、新しい反映証明を構成する。

和が零なら全splittingは共通の$`\lambda`$の平行移動を持ち、和が非零でもadapterを変更できれば
$`\sum \Delta b=-\sum b`$で修復できる。全adapter可変なら二つの自由、一本だけ可変なら一意、全固定なら
和が非零のとき不存在となる。零adapterの挿入による細分化では同じ実現と障害類を輸送し、
同じprimitive supportからAtlasのC0–C6を証明する。これをSAGA・既存G-125・Atlasへの
正の比較の必須例とする。

### 16.6 同じ意味保存族の上で診断が変わる

$`B_{0}`$上で三chart・三edge・一faceのnerveを固定し、次の有限readoutを指定する。

| source | chart支持 | 読む式 |
| --- | --- | --- |
| $`s_{01}`$ | 0,1 | 0 |
| $`s_{12}`$ | 1,2 | $`\lambda`$ |
| $`s_{20}`$ | 2,0 | 0 |
| $`s_*`$ | 0,1,2 | $`\mu`$ |

K1でedge/face支持を生成し、K0で同じ値をまとめると、$`\beta _{1}=1`$は$`\lambda =0`$かつ$`\mu \ne 0`$のときだけ。
$`\mu =1`$で$`\lambda`$を0へ動かすとcycleが生じ、$`\lambda =0`$で$`\mu`$を0へ動かすとcycleが消える。
全点で指定操作と公開readの保存Lawは成立し、$`B_{0}`$はsmoothである。したがってこの診断値だけから
意味の変形自由度や移行不能を判定することはできない。§14のétale診断層と§13の
実現liftを同じ入力から区別して返す必要がある。

<a id="diagram-completion"></a>
### 16.7 指定された変更を保つ図式補完

小さい圏 $`J`$ を図式の形、部分圏 $`K\hookrightarrow J`$ を固定する部分とし、
独立な実現と全actual sort mapの圏 $`\mathcal C_R`$ に図式 $`d:K\to\mathcal C_R`$ を与える。
補完は $`J`$ 上の実現図式と、その $`K`$ への制限を $`d`$ と同定する自然同型からなる。
各辺の許容変換 $`H`$ と各頂点・辺・合成のLawを、原始表示から評価する。
これにより、独立に定義した補完groupoidと、制限関手

```math
\mathop{\mathrm{Fun}}\nolimits(J,\mathcal C_R)^\simeq
 \longrightarrow
\mathop{\mathrm{Fun}}\nolimits(K,\mathcal C_R)^\simeq
```

の $`d`$ 上の2-fiberに同じ評価条件を課した族との同値を構成する。
図式内の射は非可逆な比較も含み、補完同士は全頂点・全辺を保つ自然同型で比較する。
有限生成元・有限関係を持つ $`J`$ では、その生成辺と関係を使って方程式を生成する。
一般の小さい形は、G-139の全実現・全Homの幾何に同じ制限関手を作って扱う。

二つの変更を組み合わせる図式では、$`K`$ に指定された比較射 $`b\to a\leftarrow c`$ と、
公開read、固定する操作を置く。$`J`$ に $`b\leftarrow z\to c`$ を追加し、
各変更の保持条件と、二つの合成 $`z\to a`$ の一致を評価する。
完成した四角形は、指定した二変更の内容と選んだ意味を保つ組合せを表す。
台帳の§16.4では、まず係数と共通の公開対象への比較から候補を生成する。
候補から公開対象への比較の保存条件は、係数変更だけを許すと残差 $`\mu\delta`$、
差し引く規則も許すと残差 $`\mu\delta(1-\rho)`$ で表される。
この係数解から四角形へ進むときは、候補から各分枝への実際の状態写像と操作翻訳を
原始規則から構成し、G-140 Fの全補完に必要な可換式を照合する。
鎖状の $`J`$ は各段の条件を保つ変更列、多面体の $`J`$ は複数の合成の整合条件を表す。
局所補完の貼り合わせ、障害、全修復は、同じ図式をG-141のdescentへ通して構成する。

<a id="paths-and-state-transfer"></a>
### 16.8 係数経路、状態移送、許可された操作列

原始規則が生成する一段の変更族を $`E`$、始点・終点写像を $`s,t:E\to\mathcal M`$ とする。
長さ $`n`$ の変更列は、各段の評価条件を持つ
$`E\times_{\mathcal M}\cdots\times_{\mathcal M}E`$ の指定端点上のfiberである。
各中間実現、実際の比較射、操作語翻訳を保持して連結を構成し、
原始規則で指定された細分化の操作翻訳と比較する。
この変更列と実際の状態移送を結ぶため、§12の意味保存射 $`h:X_1\to X_0`$ に対し、
許容状態の包含 $`\iota_D:D\hookrightarrow X_0`$ と

```math
m:D\longrightarrow X_1,\qquad h\,m=\iota_D
```

を満たすliftを分類する。$`m`$ の候補は原始の許容移送規則から生成する。
§12の生成操作の保存式と帰納法から、許可される新側の全操作語 $`w`$ に対して

```math
h\,\mathop{\mathrm{eval}}\nolimits_1(w)\,m
 =\mathop{\mathrm{eval}}\nolimits_0(\tau(w))\,\iota_D
```

を導く。phaseを持つ場合は両辺の定義域を同じ許可経路で揃える。
旧側の指定操作列を実行する問題には、その語の $`\tau`$ によるliftと定義域条件を加える。
二つの移送の合成では、一つ目の像が二つ目の許容状態に入る条件を評価する。
局所的に得た $`m`$ の貼り合わせと全自由も、このlift問題としてG-141へ接続する。

体 $`k`$ 上で§16.4の係数を $`0,1`$ に制限し、$`(\delta,\mu,\rho)=(0,0,0)`$ から
$`(1,1,1)`$ へ各係数を一回ずつ有効化する。全中間点で
$`\mu\delta(1-\rho)=0`$ を満たす順序は次の四つである。

| 順序 | 各段の係数Law |
| --- | --- |
| $`\rho,\delta,\mu`$ | 成立 |
| $`\rho,\mu,\delta`$ | 成立 |
| $`\delta,\rho,\mu`$ | 成立 |
| $`\mu,\rho,\delta`$ | 成立 |
| $`\delta,\mu,\rho`$ | 二段目の $`(1,1,0)`$ で残差1 |
| $`\mu,\delta,\rho`$ | 二段目の $`(1,1,0)`$ で残差1 |

実際の状態を含む経路は、係数を状態の成分に加えたphase protocolで構成する。
Idleでだけ一係数を切り替える原始操作を追加し、$`(B,C)`$ をそのまま移す。
切替先の係数にも $`\mu\delta(1-\rho)=0`$ を要求し、許される辺をその評価条件から生成する。
通常のapply・begin・finishは現在の係数で作用し、Busyでは係数を固定する。
公開比較 $`p=B+C`$ の下で、切替・begin・finishは空語、applyは同じ引数のapplyへ送る。
切替は $`p`$ を保ち、Busyでは $`g_\rho=0`$ が全遷移で保たれるため、
全許可語の観測保存を生成操作から導ける。上の四順序は、このprotocolのIdle状態上で実現する。
係数点間の比較射、状態を移す操作、protocol全体の公開比較をそれぞれ構成対象とする。

Busyで係数だけを替えると、この保存則は失われ得る。
$`R=\mathbb Q`$、$`(\delta,\mu,\rho)=(1,0,0)`$ で
$`\mathrm{Idle}(0,0)`$ からbegin、$`\mathrm{apply}_1`$を行うと $`\mathrm{Busy}(0,1,0)`$、公開値1となる。
同じ状態を保って係数を $`(0,0,0)`$、次に $`(0,1,0)`$ へ替えると、係数Lawは各点で成立するが、
後者の状態Lawは $`g_0=-1`$ となる。この状態に$`\mathrm{finish}_0`$の式を適用すると
$`\mathrm{Idle}(0,0)`$、公開値0となる。許容phaseと状態移送の条件がこの失敗を検出する。

<a id="reading-robustness"></a>
### 16.9 同じ観測に整合する実現と共通の変更

実現の族から観測への写像を $`q:U\to B`$、指定した許容変換規則の共通parameterを
$`C\to B`$ とする。原始操作・Law・評価から
$`E\subseteq U\times_B C`$ を生成し、$`E(u,c)`$ を実現 $`u`$ に候補 $`c`$ を適用した保存条件とする。
候補が比較射などの解を要求する場合は、その証人を持つ解族を別に保持し、$`E`$ をその像として定める。
共有parameterによる比較と§12の全actual Homは、この解族への写像で結ぶ。

固定した係数域の観測値 $`b`$ と非空な整合実現集合 $`U_b`$ に対し、次を区別する。

```math
\begin{aligned}
&\text{指定候補 }c\text{ の保存}: &&\forall u\in U_b,\ E(u,c),\\
&\text{各実現での可解性}: &&\forall u\in U_b,\ \exists c\in C_b,\ E(u,c),\\
&\text{共通候補の存在}: &&\exists c\in C_b,\ \forall u\in U_b,\ E(u,c).
\end{aligned}
```

$`U_b=\varnothing`$ は、観測と原始条件の充足不能として返す。
固定した $`R`$ 値点の判定を行う場合は、その係数域を出力に保持する。
base changeで安定な全称条件を作る場合は、全 $`R`$ 代数 $`S`$ と
観測 $`b_S`$ に整合する全 $`S`$ 値実現に対して $`E_S(u,c_S)`$ を検査する。
この全称条件と整合実現の存在は、それぞれの量化を明記して組み合わせる。

Noetherian scheme $`B`$ 上で $`U,C`$ を有限型schemeとする特殊化では、
幾何点の判定をconstructible集合で扱える。
$`Z=U\times_B C`$、$`\pi:Z\to C`$ とし、$`E`$ がconstructibleなら、
$`P=\pi(E)`$ と $`N=\pi(Z\setminus E)`$ は
[Chevalleyの定理](https://stacks.math.columbia.edu/tag/054K)によってconstructibleである。
$`P\setminus N`$ は非空な整合実現の全てで成立、$`N\setminus P`$ は全てで不成立、
$`P\cap N`$ は判定が混在、$`C\setminus(P\cup N)`$ は整合実現が空、という四分類を与える。
G-141 Dの有効な有限還元と消去・開条件の算法により、この分類と証人を計算へ移す。
この幾何点分類、全 $`R`$ 値でのLaw保存、指定した有理点・整数点での可解性は、それぞれの点関手で比較する。

量化の差は小さい例にも現れる。$`U_b=C_b=\{0,1\}`$、$`E(u,c)\Longleftrightarrow c=u`$ では
各実現に解があり、共通の候補は存在しない。さらに代数閉体 $`k`$、$`\mathrm{char}(k)\ne2`$ 上で
$`z^2=t`$ を $`\mathbb G_m`$ 上の候補族とすると、各幾何fiberに根が存在する。
大域regular sectionがあれば $`k[t,t^{-1}]`$ の単元 $`a t^n`$ が $`(a t^n)^2=t`$ を満たし、
$`2n=1`$ となるため不存在である。有限étaleな $`\mu_2`$-torsorのétale局所sectionと
係数側のdescentが、各fiberの可解性から一貫した選択へ進む際の障害を表す。

判定が混在するfiberでは、同じ $`q`$ 値を持つ異なる判定の対を分離する観測を求める。
有限な整合実現集合と有限な観測候補 $`e_i`$ を与えれば、全てのそのような対を分離する
包含極小の添字部分集合を列挙できる。例として $`U=\mathbb F_2^2`$、$`q`$ は定値、
固定候補 $`c=0`$ の成立条件を $`u_1=0`$ とし、
$`e_1=u_1`$、$`e_2=u_2`$、$`e_3=u_1+u_2`$ を取る。
包含極小の分離族は $`\{e_1\}`$ と $`\{e_2,e_3\}`$ の二つである。
G-142では、追加後のreadingのkernelが判定のkernelに含まれることと、
そのreading上へ判定が因子分解することを比較し、Atlasのadequacyへ接続する。

<a id="interaction-support"></a>
### 16.10 相互作用に参加する変更数と無限小次数

独立な変更parameter $`t_1,\ldots,t_n`$ と、その零化による部分変更を指定する。
原始操作の保存式から残差ideal $`J\subseteq k[t_1,\ldots,t_n]`$ を生成し、
$`i_S`$ は $`S`$ の外のparameterを零にする座標面とする。
G-141 Fの相互作用の定理は、任意の可換環 $`k`$ と $`0\le r\le n`$ に対して

```math
\left(\forall S,\ \lvert S\rvert\le r,\ i_S^*J=0\right)
\quad\Longleftrightarrow\quad
J\subseteq\bigcap_{\lvert S\rvert\le r}(t_j:j\notin S)
=\left(\prod_{i\in T}t_i:\lvert T\rvert=r+1\right)
```

を示す。$`r=n`$ の右辺は零idealとする。
多項式の単項式支持から証明し、指定した変更のlabelと零化図式を保つ比較に自然な形にする。
左辺は各座標面上の全係数でのLaw恒等式であり、全 $`R`$ 値の代入を保持する。
有限個のon/off点の検査は、別途そのBoolean係数環で評価する。

$`t^m`$ は一つのparameterだけを持ち、原点での無限小次数は $`m`$ である。
$`\mu\delta`$ は二つのparameterを同時に使い、各一変数面で零となる。
この二例により、§15の初回次数 $`\nu`$ と、相互作用に参加する異なる変更の数を区別する。
§16.4の $`\mu\delta(1-\rho)`$ では、$`\mu=\delta=1,\rho=0`$ の失敗は
$`\rho=1`$ の追加で修復される。修復可能性を部分変更間で運ぶときは、
指定条件を保つ解族の制限写像を構成し、その写像で存在・不存在の含意を証明する。

Boolean係数環 $`k[b_1,\ldots,b_n]/(b_i^2-b_i)_i`$ は各切替状態を保持する。
冪等元は冪零idealによる商から一意にliftする
([Stacks 00J9](https://stacks.math.columbia.edu/tag/00J9))ので、
Boolean係数の切替は離散的な状態の選択を、§15の冪零parameterは固定点での変形を記述する。
両者の比較では、その係数環と点関手の写像を指定する。
