---
status: idea
origin: NT-49
tags: [heat-flow, sheaf-laplacian, spectral, convergence]
created: 2026-06-14
---

# NT-49 AAT 熱流リファクタ収束定理: sheaf 熱方程式の指数収束と本質負債への単調減衰

_〔定理候補・証明可能見込み〕 / 出典: docs/note の候補50_

## 主張

固定有限計測 profile $M$(内積付き cellular sheaf model、$L_1 = $ sheaf Laplacian)と mismatch 1-cochain $g_0 \in C^1$ を相対化基底とする。離散熱流 refactor を勾配流 $dg/dt = -L_1 g$(連続時間)または $g_{t+1} = (I - \eta L_1) g_t$($0 < \eta < 2/\lambda_{\max}(L_1)$ の明示ステップ)で定義する。これは harmonic 成分を保ち coboundary 方向のみを減衰させる勾配降下である。このとき(単調 + 指数収束):
(i) Lyapunov 量 $\|g_t - h(g_0)\|^2$ は $t$ に沿って単調非増加、
(ii) $g_t \to h(g_0)$($g_0$ の調和代表元、G3 の本質負債成分)へ収束し、残差は $\|g_t - h(g_0)\| \le e^{-\lambda_1^+(L_1)\, t}\,\|g_0 - h(g_0)\|$(離散版は $(1-\eta\lambda_1^+)^t$)、
(iii) 収束後の harmonic 質量 $\|h(g_0)\|$ は熱流で不変(局所修正では消えない G3 の本質下界を熱流が動的に証明)。
さらに spectral gap $\lambda_1^+(L_1)$ が混合時間 $t_{\mathrm{mix}} = O\big(\tfrac{1}{\lambda_1^+}\log\tfrac{1}{\varepsilon}\big)$ を支配する。結論は profile / 内積 / step $\eta$ に相対化され、未測定 axis の収束は主張しない(計測絡みは移植仮定付き)。

## 依拠

第VIII部 定義8.2 Sheaf Laplacian $L_n$、定義8.8 Spectral Gap $\lambda_1^+(L_1)$、定理8.5 / 8.6 Finite Hodge Decomposition / Harmonic Debt Minimality、G3 調和的負債分解定理(本質修復下界)、第IX部 定義6.1 AAT Lyapunov reading / 定理5.3 Finite Dissipation Stopping。

## 非自明性

本文には sheaf Laplacian も harmonic debt も spectral gap も定義されているが、これらを結ぶ時間発展(熱流)が完全に欠けている。第IX部の Lyapunov reading は $\Phi_M=\|h(g)\|$ を Lyapunov 候補として挙げるが、熱方程式 $dg/dt=-L_1 g$ という具体的な勾配流もその指数収束率も混合時間との関係も無い。G3 は本質負債の静的な下界(直交射影による min)を与えるが、本定理は「局所調整列を熱流として明示し、それが調和成分へ指数収束し本質質量は熱流不変」という動的な再証明を与え、収束率を spectral gap で定量化する。これは標準のグラフ/sheaf 熱核理論と勾配流の AAT 類似で、B12(力学系)と B11(spectral gap)を熱流という一本の方程式で束ねる新しい大定理核であり、既存の力学定理 G8(停止性のみ)とは収束率・指数評価の点で本質的に異なる。

## CS / SWE 帰結

「連続リファクタ(local patch を反復適用する CI loop)を熱流として設計し、その収束速度を spectral gap で予測する」という新しい設計言語を与える。具体的に測れるもの: (1) local-adjustment refactor を反復したとき何ステップで本質負債だけが残るか(混合時間 $t_{\mathrm{mix}} \approx 1/\lambda_1^+$)、(2) spectral gap が小さいモジュール構造は「リファクタが収束しにくい = 技術的負債の解消が遅い」ことの定量予測、(3) 熱流の不動点が G3 の本質負債 $h(g_0)$ と一致するので「どれだけ patch を重ねても残る負債」を動的シミュレーションで可視化。これにより「この CI ポリシーは何 commit で安定するか」「どこを直すと収束が速くなるか(spectral gap を上げる境界変更)」という予測・最適化が初めて可能になる。LAPACK の固有値計算 + 行列冪で実装でき、移植仮定は内積選択と有限 regime。

## 証明・根拠の見込み

$L_1$ は半正定値対称($d d^* + d^* d$、自己随伴)ゆえ固有分解 $L_1 = \sum_i \lambda_i P_i$($\lambda_0=0$ の固有空間が $\ker L_1 = \mathrm{Harm}^1$、定理8.5)。熱流の解は $g_t = \sum_i e^{-\lambda_i t} P_i g_0$ で、harmonic 成分($\lambda_0=0$)は不変、それ以外は $e^{-\lambda_i t}$ で減衰し最小正固有値 $\lambda_1^+$ が律速。よって $g_t \to P_0 g_0 = h(g_0)$、収束率は $e^{-\lambda_1^+ t}$ で標準の有限次元勾配流の指数安定性そのもの。離散版は $(I-\eta L_1)$ のスペクトル半径制御($0<\eta<2/\lambda_{\max}$ で全固有値の絶対値 $<1$、ただし $\lambda=0$ は固定点)から従う。Lyapunov 単調性は $\frac{d}{dt}\|g_t-h(g_0)\|^2 = -2\langle g_t-h(g_0), L_1 g_t\rangle = -2\sum_{i>0}\lambda_i e^{-2\lambda_i t}\|P_i g_0\|^2 \le 0$。harmonic 質量不変は $P_0 L_1 = 0$ から。第IX部 定理5.3(有限散逸停止)が離散版の停止を保証し、本定理がその収束率と極限の harmonic 一致を精密化する。すべて有限次元 Hilbert complex の標準理論で証明可能。

## 関連

G3、NT-48、B11。

## 進捗ログ

- 2026-06-14: docs/note の候補50(NT-49)から転記。定式化・証明見込みは記載済み、in-repo の証明・数値検算はこれから。
