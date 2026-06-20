---
status: idea
origin: NT-18
tags: [stanley-reisner, local-cohomology, hochster, commutative-algebra]
created: 2026-06-14
---

# NT-18 AAT Hochster 公式: 局所コホモロジーの多重次数分解と link の組合せ位相

_〔定理候補・証明可能見込み〕 / 出典: docs/note の候補50_

## 主張

square-free witness regime で obstruction ideal $I_{\mathrm{Ob}}^U=I_{\Delta_U}\subset R_W=k[E_W]$ を固定し、law algebra structure sheaf の chart 環として商環 $S_W:=R_W/I_{\Delta_U}$(= lawful locus $\mathrm{Flat}_U(W)$ の座標環)をとる。$S_W$ の多重次数付き局所コホモロジー $H^i_{\mathfrak m}(S_W)$ の Hilbert 級数は、$\Delta_U$ の各 face $\sigma$(= 同時に許容される witness support、系5.6D の admissible witness support)の link $\mathrm{link}_{\Delta_U}(\sigma)$ に対する reduced simplicial 障害コホモロジー $\dim_k \tilde H^{i-|\sigma|-1}(\mathrm{link}_{\Delta_U}(\sigma);k)$ の和として閉形式で表される(Hochster の局所コホモロジー公式の AAT 版):
$$\mathrm{Hilb}\bigl(H^i_{\mathfrak m}(S_W);t\bigr)=\sum_{\sigma\in\Delta_U}\dim_k \tilde H^{\,i-|\sigma|-1}\bigl(\mathrm{link}_{\Delta_U}(\sigma);k\bigr)\cdot\prod_{e\in\sigma}\frac{t_e^{-1}}{1-t_e^{-1}}.$$
相対化: 選ばれた witness regime / 定数係数 $k$ / chart $W$ に相対化される。link は系5.6D の context refinement / boundary-local reading に対応する。

## 依拠

第III部 定理5.6C(Stanley-Reisner Obstruction Theorem)、系5.6D(Obstruction Invariants: faces = admissible support, links = context refinement)、定義7.1(Lawful Locus $\mathrm{Flat}_U(X)=V(I_{\mathrm{Ob}}^U)$)、第IV部 意味4.2(Cohomological Degrees)、拡張ノート B1(Hochster 公式、スポークとして名指しのみ)。

## 非自明性

拡張ノートの橋マップは Hochster 公式を B1 スポークとして名指しするだけで、AAT 定理化されていない。本候補は「lawful locus 座標環の局所コホモロジー」という代数的に深い不変量を、$\Delta_U$ の face ごとの link の reduced 障害コホモロジーへ完全分解する。これは G5(Hilbert 級数干渉 = Tor 質量の交代和)とは別物で、G5 が二法則の Tor 交代和を勘定するのに対し、本候補は単一 law universe の lawful locus の Cohen-Macaulay 性・depth・regularity を link の組合せ位相で読む。link = context refinement という系5.6D の reading に厳密な代数的意味(局所コホモロジーへの寄与)を与える点が新しく、第III部と第IV部を Hochster 公式で接続する橋になる。

## CS / SWE 帰結

lawful locus 座標環の depth(= Cohen-Macaulay までの距離)を、各 admissible witness support $\sigma$ の link の reduced 位相だけから判定できる新しい道が開く。CS 読み: $\mathrm{link}_{\Delta_U}(\sigma)$ が非自明な $\tilde H$ を持つ最小次数が、support $\sigma$ を固定した(= その設計要素群を保持したまま)context refinement で初めて現れる「隠れた統合障害の最小次元」を与える。これは「どの設計要素の組を固定すると、どの次元の障害が局所的に立ち上がるか」という、従来 measure できなかった boundary-local な障害局在を組合せ計算へ落とす。移植仮定付き計測接続として、Macaulay2 の局所コホモロジー / link 計算でツール出力可能(B1 で Macaulay2 予告済み)。verdict 規律: link が acyclic な次数では unmeasured ではなく measured_zero の structural reading とする。

## 証明・根拠の見込み

AAT 側の仮定($I_{\mathrm{Ob}}^U=I_{\Delta_U}$、$S_W=R/I_{\Delta_U}$、定数係数、square-free)を満たせば $S_W$ はちょうど Stanley-Reisner 環であり、古典的 Hochster の局所コホモロジー公式(Stanley『Combinatorics and Commutative Algebra』定理 II.4.1、Bruns-Herzog 5.3.8)がそのまま適用できる。AAT の仕事は三点: (i) 第III部 定理5.6C により obstruction ideal が SR ideal であることの確認、(ii) face = admissible support / link = context refinement の AAT reading(系5.6D)を Hochster 公式の組合せ項へ対応づけること、(iii) reduced simplicial cohomology を第IV部の定数係数障害コホモロジーと同一視する regime 固定。証拠: 最小例 $\Delta_U$ に頂点 $\{p,q,r\}$、$\mathrm{MinForb}=\{\{p,q\},\{q,r\}\}$(付録B の $I_{\mathrm{Ob}}=\langle pq,qr\rangle$)では $\mathrm{link}_{\Delta_U}(q)$ 近傍が非連結となり $\tilde H^0\neq 0$ が $q$ に局在する。これは付録B で $q$ が共有 witness factor として conflict を担う事実(B.5/B.8.4)と一致する。

## 関連

G5、G2、NT-17。

## 進捗ログ

- 2026-06-14: docs/note の候補50(NT-18)から転記。定式化・証明見込みは記載済み、in-repo の証明・数値検算はこれから。
