---
status: idea
origin: NT-47
tags: [optimal-transport, harmonic, lower-bound, essential-debt]
created: 2026-06-14
---

# NT-47 輸送下界=調和質量: 本質負債の輸送的不可避性

_〔定理候補・証明可能見込み〕 / 出典: docs/note の候補50_

## 主張

固定 finite cellular sheaf measurement model $M$(cochain 複体 $(C^n, d_n)$、内積、sheaf Laplacian $L_1$、mismatch 1-cocycle $g$)で、obstruction measure $\Omega_U$ が cochain $g$ の係数を support 上の非負質量へ写す calibration($c^{-1}|g_e| \le \Omega_U\text{-mass}_e \le c|g_e|$、定数 $c$)を固定する。lawful 状態への任意の repair op $A \to A'$ が局所調整(profile 不変な 0-cochain 張り替え)のみで到達されるとき、輸送コストの下界
$$W_1(\Omega_U(A), \Omega_U(A')) \ \ge\ \kappa_M \cdot \|h(g)\|$$
が成立する($\|h(g)\|$ は $g$ の調和代表元ノルム = G3 の本質負債質量、$\kappa_M > 0$ は ground 距離・calibration・複体形から定まる定数)。特に $\|h(g)\| > 0$ のとき、いかなる局所調整 repair も $W_1$ で正の輸送コストを払わざるを得ず、調和成分は局所調整では輸送先で消えず別 support へ移送されるのみである。すべて $M$(内積/calibration/ground 距離)に相対化される。

## 依拠

拡張ノート G3 調和的負債分解定理(本質修復下界 $\|h(g)\|$)、第VIII部 定理8.5 Finite Hodge Decomposition / 定理8.6 Harmonic Debt Minimality / 系8.7 Essential Repair Lower Bound、定義10.6 Wasserstein Transfer Cost / 定理候補10.7、定義8.3 Distance-to-Flatness Reading、拡張ノート B9 Wasserstein・B3+ harmonic hotspot。

## 非自明性

G3 / 系8.7 は repair cost が cochain ノルムに $L$-Lipschitz という抽象 cost model 仮定の下で $\|h(g)\|/L$ 下界を出すが、輸送($W_1$)という具体的・計算可能・双対付きの cost に対しては未確立である。本候補は Hodge 理論(調和分解)と最適輸送($W_1$)という二つの異なる強構造を結ぶ比較定理で、harmonic mass という代数的不変量が transport cost という解析的・組合せ的量の下界になることを主張する。これは標準数学でも非自明な calibration を要する(調和性は内積、輸送は ground 距離、両者を $c$ で結ぶ)。G3 の Lipschitz 仮定を、輸送の場合の calibration 不等式へ置き換えて具体化する点が新しい。

## CS / SWE 帰結

「局所 patch をいくら重ねても、本質負債質量 $\|h(g)\|$ の分は必ず輸送コストとして現れる」ことを、LP で計算できる $W_1$ の下界として与える。すなわち調和質量(LAPACK で計算)が輸送コスト(LP ソルバで計算)の下限を保証し、spectral と transport という二つの独立な計測パイプラインの整合検算ができる。CS 的には「この負債を局所修正で動かそうとすると最低でも $\kappa_M\cdot\|h(g)\|$ のコストがかかる。それ未満で消えたと報告されたら calibration か coverage に穴がある」という下界付き監査を可能にする(移植仮定: calibration 不等式と ground 距離を固定した cellular sheaf profile 内)。near-miss 検出(spectral gap)と輸送コストを結ぶ実務指標になる。

## 証明・根拠の見込み

(1) G3(b) より局所調整後の残差 $\min_c \|g - d_0 c\| = \|h(g)\|$。(2) calibration 不等式で cochain ノルムと $\Omega$-mass を比較。(3) 調和代表元 $h(g)$ の符号構造から 1-Lipschitz potential $\varphi_h$ を構成し、Kantorovich 双対(NT-46)に代入して $\sum \varphi_h\cdot(\Omega(A)-\Omega(A')) \ge \kappa_M\|h(g)\|$ を下から評価する。鍵は「調和成分は coboundary(局所調整)で消えないのでその質量は support 間で必ず再配置される $\Rightarrow$ 正の輸送」という直交性と双対の組合せ。有限次元 Hilbert 複体での直交射影(定理8.5)は無条件成立、双対(NT-46)も有限 LP で厳密。擬円周 model で $h(g)$ を明示計算でき($H^1 \cong \mathbb{Z}$ の生成元)、対応する $\Omega$ 差の $W_1$ を LP で解いて下界の成立を数値確認できる。難所は $\kappa_M$ の最適定数(calibration constant と ground 距離の幾何の積)で、これが定理候補に留める要因である。

## 関連

G3、NT-46、B9。

## 進捗ログ

- 2026-06-14: docs/note の候補50(NT-47)から転記。定式化・証明見込みは記載済み、in-repo の証明・数値検算はこれから。
