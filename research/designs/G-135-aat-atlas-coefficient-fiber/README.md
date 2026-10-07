# G-135：原始セルからの順像係数

[GOAL T0・A–E・W](../../goals/G-135-aat-atlas-coefficient-fiber.md)の構成を定める。
完全列の式は[完全列と保存条件](exact-sequence.md)、原始例は[指定例](witnesses.md)、
既存宣言と新規義務は[再利用対応表](reuse-map.md)に置く。

## 1. 支持セルと退化の分類

GOAL T0のMを細→粗、cochain比較を粗→細とする。以下のセルはすべて
細側の $`\pi^{-1}A`$ または粗側のAで選択したセルである。
chainの符号は $`\partial e=\mathrm{right}(e)-\mathrm{left}(e)`$、
$`\partial f=e_0-e_1+e_2`$。G-134の自由ℚchainと既存subset複体を使う。

細辺を、`edgeMap = none` の集合 $`E_v`$ と、`some` の集合 $`E_h`$ に分ける。
細面は次の三種に分ける。

| 種類 | 原始条件 | carrier |
| --- | --- | --- |
| $`F_v`$ | 面と全三辺がnone | 三頂点が写る粗chart |
| $`F_m`$ | 面がnone、二辺が同じ粗辺へ写り、残る一辺がnone | その粗辺 |
| $`F_h`$ | 面がsome | その粗面 |

`optionCell_incidence_iff`により退化面は上の最初の二種で尽きる。
混在面は $`(\mathrm{none},e,e)`$ または $`(e,e,\mathrm{none})`$ の形であり、
符号の異なる二つのmapped辺が相殺する。細辺が同名の二出現である場合も残す。
pure classは $`F_m=\varnothing`$、すなわち旧hereditary比較からの像とする。

粗chart cの**セル逆像fiber** $`\Phi_c^A`$ は、cへ写る細chart、c上の
$`E_v`$、c上の $`F_v`$ から作る部分chain複体である。
粗loopへ写る辺は、端点がともにcでもこのfiberの辺に入らない。
一方、$`A_\lambda=\mathrm{labelValueFiber}`$ はLaw降下値のtarget逆像集合であり、
セルを選択する添字である。$`\Phi_c^{A_\lambda}`$ はその選択後のセル逆像fiberである。

粗辺eごとに有限有向多重グラフ $`\Gamma_e^A`$ を作る。
頂点はeへ写る細辺、グラフの辺はeをcarrierに持つ混在面である。
そのincidence列は $`\partial f`$ の $`E_h`$ 成分とする。
同じ細辺が二回現れる混在面はloop、別名の同じ関係は平行辺として残す。
粗面Fの持ち上げは $`\Lambda_F^A=\{f\in F_h\mid M(f)=F\}`$ とする。

## 2. 順像の対象と普遍性

`Inc(N_A)`の対象は名前付きセル、生成射は辺の左右の端点incidenceと
面の三つの辺incidenceである。面の各頂点へ至る二経路を同一視する。
同じセル名を指す異なる出現の射は保持する。この有限圏を作り、
G-134の原始incidenceからcarrier関手
$`\phi_A:\mathrm{Inc}(N'_{\pi^{-1}A})\to\mathrm{Inc}(N_A)`$ を構成する。
退化辺はchart、垂直面はchart、混在面は辺へ送る。射は、各退化パターンの
端点または恒等射へ送る。三角形の関係を保存することを証明する。

細側の定数係数functor $`\underline{\mathbb Q}`$ の右Kan拡張

```math
\mathcal P_A=\operatorname{Ran}_{\phi_A}\underline{\mathbb Q},\qquad
\mathcal P_A(\sigma)=
 \lim_{(\sigma\downarrow\phi_A)}\underline{\mathbb Q}
```

を順像係数とする。comma圏の連結成分を原始セルから計算し、次を証明する。

```math
\mathcal P_A(c)\cong\mathbb Q^{\pi_0\Phi_c^A},\qquad
\mathcal P_A(e)\cong\mathbb Q^{\pi_0\Gamma_e^A},\qquad
\mathcal P_A(F)\cong\mathbb Q^{\Lambda_F^A}.
```

空のfiberの係数は零。これは有限diagramの極限としての順像であり、
各成分上で一定な関数を与えることの普遍性を持つ。
`CategoryTheory.Functor.IsRightKanExtension`への接続まで証明する。
comma圏から上の連結成分への対応は、全射・単射とincidence自然性を含む構成義務である。

chart→edgeの係数射は、細辺の該当端点が属する $`\Phi`$ の成分で評価する。
混在面の垂直辺によって、この成分は同じ $`\Gamma`$ 成分内で一定である。
edge→faceは、持ち上げ面の該当辺が属する $`\Gamma`$ 成分で評価する。
これらは右Kan拡張の射と一致し、三角形の二経路の関係も保つ。

## 3. 中間複体と二射の式

$`P_A=C^\bullet(N_A;\mathcal P_A)`$ の次数nは粗nセルの係数の直積とする。
微分は§2の係数射による端点差分・三辺の符号付き和である。
有限性により直積と有限直和を同定できる。$`d^1d^0=0`$ を原始incidenceから証明する。

$`\eta_A`$ は各粗セルのℚ値を、そのセルの全fiber成分上の定数関数へ送る。
$`\varepsilon_A`$ は次のcell評価で作る。

| 次数 | 細セル上の評価 |
| --- | --- |
| 0 | chartが属する $`\Phi_c^A`$ の成分で評価 |
| 1 | mapped辺は $`\Gamma_e^A`$ の成分で評価、垂直辺は0 |
| 2 | mapped面はその持ち上げで評価、退化面は0 |

垂直辺での $`d^0`$ と退化面での $`d^1`$ の零性を示し、両射をcochain Homにする。
全次数で $`\varepsilon_A\eta_A=u_A`$ を既存生成式へ照合する。
$`\varepsilon_A`$ は次数ごとに単射だが、そのH¹単射性には§4の構成を使う。

## 4. 退化セル生成部分複体

$`K'_A`$ を細側の支持chain複体、$`a=\partial_1|_{\mathbb Q[E_v]}`$ とする。
次の部分空間を、元の $`K'_A`$ の部分複体として構成する。

```math
L_2=\mathbb Q[F_v\sqcup F_m],\quad
L_1=\mathbb Q[E_v]+\partial_2\mathbb Q[F_m],\quad
L_0=\operatorname{im}a.
```

$`\partial L_2\subseteq L_1`$、$`\partial L_1=L_0`$ はincidenceと
$`\partial^2=0`$ から導く。Mのchain比較はLを零に送る。
§3の評価写像がLをannihilateするcochain全体を像に持つことを証明し、

```math
P_A\cong(K'_A/L_A)^*,\qquad Q_A=L_A^*,\qquad
0\to P_A\xrightarrow{\varepsilon_A}C'_A\to Q_A\to0
```

を標準複体の短完全列へ接続する。次数別全射性には体上の有限次元双対の完全性を使う。
$`H_0L_A=0`$ から $`H^0Q_A=0`$ を導く。
Pは§2で独立に構成した順像複体であり、この商との同型は証明する出力である。

## 5. Law、台、比較の整合

すべての構成を先にAごとに行い、発生ラベル $`\lambda`$ について
$`A=A_\lambda`$ とした有限直和を取る。G-134の
`labelFiberComparison_naturality0/1/2`、`lawFiberH1Comparison_square`、
`lawSubsetConeDirectSumIso`へ接続する。これらの宣言中のfiberはLaw値のfiberを指す。
新しく同定する項は $`\Phi_c^{A_\lambda}`$、$`\Gamma_e^{A_\lambda}`$、
順像、L、R、transgressionである。

$`A\subseteq A'`$ では選択セルの包含が、$`\Phi,\Gamma,L,K'`$ の写像を作る。
成分は合流し得るが、小さい側の各成分の大きい側での行き先は一意である。
関数の制限からPの反変写像を作り、二射・短完全列・連結射・Law分解と可換にする。
Kan拡張のbase changeを仮定する代わりに、この同じ制限を§2の成分式から証明する。

## 6. 構成の依存関係と有限表示

| 構成 | 使う入力 | 出力と接続先 |
| --- | --- | --- |
| carrier・局所fiber | 原始M、K1、選択セル | Inc関手、Φ、Γ、Λ |
| 順像・二射 | 有限comma圏と局所成分 | P、η、ε、実uとの全次数等号 |
| 退化部分複体 | 原始incidence行列 | L、商双対、標準短完全列 |
| 低次数の分解 | Lの垂直部分と混在関係 | R、τ、完全性、消滅判定 |
| 最終診断 | 同じ二射・既存H¹商 | 核・余核、錐、保存条件 |
| Law・台・基本変形 | 既存自然性と同じM | 全Lawの式、G-134への適用 |

有限計算ではSource・セル・発生ラベルの列挙、評価表、台membership表、Mの表を用いる。
連結成分と有理行列の核・像・商を計算し、表示の基底変更に自然な同型を付ける。
式を任意行列として入力するのでなく、各行列要素をセルの出現と符号から生成する。
結果のrank、代表元、零性判定が同じ `blockDefect` の値を返すことを証明する。
