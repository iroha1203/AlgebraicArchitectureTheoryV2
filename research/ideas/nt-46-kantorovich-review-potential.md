---
status: idea
origin: NT-46
tags: [optimal-transport, kantorovich, lipschitz, review-priority]
created: 2026-06-14
---

# NT-46 負債輸送の Kantorovich 双対と 1-Lipschitz レビュー優先ポテンシャル

_〔定理候補・証明可能見込み〕 / 出典: docs/note の候補50_

## 主張

固定 finite measurement regime $M$(support グラフ $G_S$、ground 距離 $d_S$、obstruction measure $\Omega_U$)において、repair operation $\mathrm{op}\colon A \to B$ が総質量保存 $|\Omega_U(A)| = |\Omega_U(B)|$ を満たすとき、Kantorovich-Rubinstein 双対が厳密に成立する:
$$W_1(\Omega_U(A), \Omega_U(B); d_S) = \max\Big\{ \textstyle\sum_{v \in \mathrm{Support}} \varphi(v)\cdot(\Omega_U(A) - \Omega_U(B))(v) \ :\ \varphi\ \text{は}\ d_S\ \text{に関し 1-Lipschitz} \Big\}.$$
最大化子 $\varphi^*$ を review-priority potential と呼ぶ。(1) $\varphi^*$ は有限 LP の双対解として計算可能で、$\varphi^*(v) - \varphi^*(w) = d_S(v,w)$ を満たす緊張辺 (tight edge) の集合 $T(\varphi^*)$ は質量が実際に流れた transport 経路を含む。(2)【検出規律】全 1-Lipschitz $\varphi$ で $\sum \varphi\cdot(\Omega_U(A)-\Omega_U(B)) = 0$ なら $\Omega_U(A) = \Omega_U(B)$、すなわち measured: 負債は一切移動していない(op は debt について構造的に no-op)。$\varphi^*(v)$ の大きい support $v$ が「負債が最も大きく出入りした review focus」を与える。結論は $M$ に相対化され、未計測 axis の potential は unmeasured として沈黙する。

## 依拠

第VIII部 定義10.6 Wasserstein Transfer Cost、定義3.1 Measurement Verdict(5値)、定理候補10.7 Transfer Cost Lower Bound(双対は未定式化)、拡張ノート B9(「有限なので LP で厳密に解ける」とのみ述べ双対定理・potential 読みは不在)、第VII部 定義15.3 U-Detecting Representation Family、個別予想 ACTS Theorem 3 Spectral Review Focus(固有ベクトル版、双対 potential 版は新規)。

## 非自明性

B9 は「LP で解ける」と一言述べるだけで、(a) 双対が AAT debt measure 上で厳密に成立する条件(総質量保存)を定理化しておらず、(b) 双対解 $\varphi^*$ を review-priority potential として CS 的に読む橋を与えず、(c) tight-edge による transport 経路の特徴づけと no-op 検出規律(双対側からの measured_zero certificate)を全く持たない。Kantorovich 双対は最適輸送の中心定理であり、その AAT 移植は「主問題=どれだけ移ったか」と「双対問題=どの方向に negotiation したか」の二面性を初めて AAT verdict に持ち込む。ACTS Theorem 3 が対称 Laplacian の固有ベクトルで focus を読むのに対し、本候補は非対称な輸送の双対 potential で読み、原理が異なる。

## CS / SWE 帰結

「この修復で負債が移ったか/消えたか/単に名前が変わっただけか」に、双対 potential $\varphi^*$ という証拠付きの判定を与える。$\varphi^*$ の大きい support = 「次に review すべき優先箇所」が、ヒューリスティックではなく LP 双対解として算出される(ArchSig の review focus 出力の数学的裏づけ)。tight edge 集合は「負債が実際に通った経路」を可視化し、ArchSig 観測の pressure chain(request-authority → transaction → domain-artifact → AI-surface)を双対 potential の緊張辺として説明できる。全 1-Lipschitz テストで 0 という双対 certificate は「この op は debt について measured no-op」という肯定的・沈黙整合な verdict を与える(移植仮定: ground 距離と obstruction measure を固定した profile 内)。

## 証明・根拠の見込み

有限離散最適輸送では $W_1 = \min\text{-cost-flow}$ であり、その LP 双対が Kantorovich-Rubinstein 双対そのもの(強双対定理は有限 LP で無条件、相補性条件が tight-edge を与える)。総質量保存は signed measure $\Omega_U(A)-\Omega_U(B)$ の総和を $0$ に保ち、双対の定数シフト不変性と整合して双対値を finite かつ達成可能にする(保存がないと $W_1$ は $\infty$ または不平衡輸送になり双対形が変わるため、保存が本質的仮定)。tight edge の特徴づけは LP 相補性スラックネス、no-op 検出は「全 1-Lipschitz テストで pairing $0$ $\Rightarrow$ 測度差 $0$」で、$d_S$ が距離ゆえ 1-Lipschitz 関数が点を分離することから従う。証拠として、擬円周 cover 上で $\Omega$ 差 $(1,0)$ に対し $\varphi^*(P)-\varphi^*(Q)=d_S(P,Q)$ を満たす potential を手計算で構成でき、$W_1 = d_S(P,Q)$ と一致する。

## 関連

B9、G4、NT-47。

## 進捗ログ

- 2026-06-14: docs/note の候補50(NT-46)から転記。定式化・証明見込みは記載済み、in-repo の証明・数値検算はこれから。
