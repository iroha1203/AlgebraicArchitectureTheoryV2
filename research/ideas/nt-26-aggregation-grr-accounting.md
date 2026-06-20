---
status: idea
origin: NT-26
tags: [grothendieck-riemann-roch, euler-characteristic, aggregation, cohomology]
created: 2026-06-14
---

# NT-26 集約 GRR 会計定理: 粒度変更に沿う負債 Euler 標数の押し出し保存

_〔定理候補・証明可能見込み〕 / 出典: docs/note の候補50_

## 主張

有限 poset site の集約射 π: X_fine → X_coarse(module → package のような粒度変更)と有限階数 abelian obstruction sheaf Ob を固定する。各 sheaf F に対し Euler 標数 χ(F) := Σ_n (−1)^n dim_k H^n(−, F) と、次元の交代和を成分とする負債キャラクター ch(F) := Σ_n (−1)^n [H^n(−, F)] ∈ K_0 を置く。π の高次順像 R^q π_* Ob を係数とするとき、(i) GRR 型会計恒等式 χ_coarse( Σ_q (−1)^q R^q π_* Ob ) = χ_fine(Ob) が成立する(π に沿った負債 Euler 標数の押し出し保存)。(ii) より精密に、各次数で dim H^n(fine, Ob) = Σ_{p+q=n} dim E_∞^{p,q}(Leray)、E_2^{p,q} = H^p(coarse, R^q π_* Ob) であり、両尺度の負債キャラクターの差は Leray 微分の像/核(集約単位内に局在する成分)で完全に勘定される。(iii) cover shape と stalk 次元を保つ refactor は両尺度の χ を同時に保存し、E_∞ の次数分布(尺度安定負債の重み)のみを動かしうる。すべて選ばれた aggregation family / coefficient / cover に相対化される。

## 依拠

第IV部 系12.5 Euler Accounting、第IV部 定義14.1 / 定理候補14.2 Leray Five-Term Debt Sequence、第IV部 定義14.3 Scale-Stable Debt、G6 集約五項完全列、G5 法則干渉の Hilbert 級数恒等式、第VIII部 定理4.2 Finite AAT Computability。

## 非自明性

G6 は Leray 五項完全列(H^1, H^2 の低次のみ)を与えるだけで、全次数を束ねる保存則・指数定理型恒等式には到達していない。本定理は Grothendieck–Riemann–Roch の核心「高次順像の Euler 標数が押し出しで保存される(ch と Todd の整合)」の AAT 類似を立て、全次数の負債 Euler 標数が aggregation で恒等的に保たれること、その差が Leray スペクトル系列の E_∞ で完全に会計されることを主張する。系12.5 の Euler 保存(単一尺度)を二尺度間の押し出し保存へ昇格させ、G5 の Hilbert 級数交代和(law conflict 方向)と相補的な「尺度方向の交代和保存」を与える。これは焼き直しではなく、保存則を尺度変換の関手性として深めるものである。

## CS / SWE 帰結

「負債は粒度を変えても総量(Euler 標数)が保存され、ただ次数間・集約単位内へ移動するだけ」を全次数で会計できる。これまで module 粒度と package 粒度で測った H^1 を直接比較する手段がなく、粒度依存の artifact(ズームの産物)と真の構造的負債を分離できなかった。本定理は χ_fine(Ob) = χ_coarse(押し出し) という整数恒等式を検算として与え、両辺の食い違いを「集約写像の coverage 不整合」の検出器にする(G4 の複式簿記の尺度版)。実務では monorepo のサブシステム再編やマイクロサービス境界の粒度変更時に「負債総量が保存したか、どの次数へ移ったか、どれが集約単位内に局在したか(R^1 π_*)」を完全列の精度で監査でき(移植仮定付き: aggregation family と coefficient 固定を要する)、「境界を増やしたのに統合バグが減らない」現象を尺度間 Euler 会計で説明する。

## 証明・根拠の見込み

(i) は有限 poset 射の Leray スペクトル系列 E_2^{p,q} = H^p(coarse, R^q π_* Ob) ⇒ H^{p+q}(fine, Ob)(有限なので収束は自明、G6 五項列の全次数版)の Euler 標数が各ページで保存される標準事実による: Σ (−1)^{p+q} dim E_r^{p,q} は r に依らず一定で、E_2 と E_∞ で等しいから Σ_n (−1)^n dim H^n(fine, Ob) = Σ_{p,q} (−1)^{p+q} dim H^p(coarse, R^q π_* Ob)。(ii) は同スペクトル系列の次数別収束。(iii) は系12.5(cover shape と stalk 保存で χ 不変)を π の両側に適用。証明経路は有限線形代数 + 標準スペクトル系列のみで、定理候補14.2 を超える高次項も有限性から E_∞ で止まるため厳密に勘定できる。Macaulay2 / 有限次元計算で検算可能。残る設計: R^q π_* Ob の具体計算手続きを EffCoeff_M に追加すれば即実装できる。

## 関連

G6、G4、NT-27。

## 進捗ログ

- 2026-06-14: docs/note の候補50(NT-26)から転記。定式化・証明見込みは記載済み、in-repo の証明・数値検算はこれから。
