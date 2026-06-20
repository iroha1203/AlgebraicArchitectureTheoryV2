---
status: idea
origin: NT-17
tags: [stanley-reisner, free-resolution, betti, commutative-algebra]
created: 2026-06-14
---

# NT-17 Hochster-Betti 冗長制約定理: minimal free resolution が制約の冗長度を局在化する

_〔定理候補・証明可能見込み〕 / 出典: docs/note の候補50_

## 主張

固定 reading $p=(V,U,J,k)$ の square-free witness regime(第III部 定義5.6B)を仮定し、witness 変数集合 $E_W$、forbidden support 族 $\mathrm{Forb}_U(W)$、SR-ideal $I_{\mathrm{Ob}}^U(W)=I_{\Delta_U}(W)\subset R_W=k[E_W]$ をとる(定理5.6C)。$R_W/I_{\mathrm{Ob}}^U(W)$ の minimal graded free resolution の $i$ 番目の multigraded Betti 数を $\beta_{i,S}$($S\subseteq E_W$ は multidegree)とおくとき、次が成り立つ。
- (A) [Hochster 公式] $\beta_{i,S}\bigl(R_W/I_{\mathrm{Ob}}^U(W)\bigr)=\dim_k \tilde H_{|S|-i-1}(\Delta_U|_S;\,k)$。ここで $\Delta_U|_S$ は witness 集合 $S$ 上の induced 部分複体(= $S$ に制限した admissible witness support の族)、$\tilde H$ は reduced simplicial homology。
- (B) [冗長度=射影次元] $\mathrm{pdim}_{R_W}\bigl(R_W/I_{\mathrm{Ob}}^U(W)\bigr)=\max\{\,i\mid \exists S,\ \beta_{i,S}\neq 0\,\}=:\mathrm{RedDepth}_U(W)$ と定義すると、これは「forbidden pattern を切り出す制約族が、一次の独立 witness を超えて何段の syzygy(冗長関係の関係)を持つか」を局在化する。Hilbert syzygy 定理により $\mathrm{RedDepth}_U(W)\le |E_W|$。
- (C) [Auslander-Buchsbaum 会計] $\mathrm{RedDepth}_U(W)=|E_W|-\mathrm{depth}_{R_W}\bigl(R_W/I_{\mathrm{Ob}}^U(W)\bigr)$。
- 相対化: 結論はすべて選ばれた $V/U/J/k$ と square-free witness regime に相対化され、regime 外の witness/axis には $\beta$ も depth も主張しない。

## 依拠

第III部 定義5.6B(Square-Free Witness Regime)、定理5.6C(Stanley-Reisner Obstruction Theorem)、系5.6D(Obstruction Invariants)、第VIII部 定理5.2(Stanley-Reisner / Alexander Dual Repair Theorem)、付録 B.4(Stanley-Reisner reading)。

## 非自明性

G5(Hilbert 級数 Euler 恒等式)は二つの law universe の Tor 質量の交代和を読むが、単一 obstruction ideal の minimal free resolution の各 Betti 数を induced 部分複体の reduced homology へ完全に同定すること(Hochster 公式)は AAT 本文・拡張ノート・既存予想のどこにも無い。系5.6D は minimal generators(= irreducible witness)までしか読まず、higher syzygy(generator 間の冗長関係、さらにその関係)を一度も定式化していない。射影次元・depth・Auslander-Buchsbaum 会計は obstruction ideal sheaf に対して未着手であり、定義の言い換えではなく minimal resolution の存在と一意性(可換代数の非自明定理)に依拠する。

## CS / SWE 帰結

従来の lint/policy は「禁止パターンが何個あるか(generator 数=violation count)」までしか測れなかった。本定理は「制約族がどれだけ冗長か」を $\beta_{i,S}$ の higher $i$ 成分として初めて数値化する。$\beta_1$(generator)=禁止パターン、$\beta_2$=禁止パターン同士の重複(同じ witness を共有する forbidden support の syzygy)、$\beta_i$=$i$ 段重なった冗長制約、と読める。$\mathrm{RedDepth}_U(W)$ は「統合レビューで independent に潰せず、連鎖して効いてくる制約の段数」=どこまで遡って修正の波及を追うべきかの上界を与える。Hochster 公式により各冗長度は特定 witness 集合 $S$ 上の induced 部分複体のホールに局在するので、レビュー対象を「どの witness クラスタの何段目の冗長か」まで絞れる。depth が低い(= RedDepth が高い)ほど制約族が深く絡み合っており、局所修正が困難であることを Auslander-Buchsbaum 会計が定量保証する。

## 証明・根拠の見込み

(A) は square-free monomial ideal に対する Hochster 公式そのもの(Bruns-Herzog 定理5.5.1)であり、$I_{\mathrm{Ob}}^U=I_{\Delta_U}$(定理5.6C)が成り立つ regime で適用できる。戦略は Taylor 複体(generators から作る上界 resolution)を出発点に、multigraded structure で各 squarefree degree $S$ の部分を取り出すと Koszul 双対により $\Delta_U|_S$ の reduced chain complex が現れ、その homology が Betti 数を与える、というもの。(B) の Hilbert syzygy 上界は $R_W=k[E_W]$ が多項式環であることから即従う。(C) は $R_W$ が Cohen-Macaulay 多項式環で $I_{\mathrm{Ob}}^U$ が graded のとき Auslander-Buchsbaum 公式 $\mathrm{pdim}+\mathrm{depth}=\mathrm{depth}(R_W)=|E_W|$ から従う。検算: $E=\{p,q,r\}$、$\mathrm{Forb}=\{\{p,q\},\{q,r\}\}$ の例では $\Delta_U$ の faces $=\{\varnothing,p,q,r,pr\}$、reduced Euler char $=1$、generators $=2$($pq,qr$)、共有 witness $q$ による1段の syzygy が存在し $\mathrm{pdim}=2$($=|E|-\mathrm{depth}$、$\mathrm{depth}=1$)。path graph $P_4$ の独立複体例でも $f$-vector と Euler char が一致した。いずれも Macaulay2 で Betti 数まで即検算可能な finite regime である。

## 関連

G5、第III部 square-free witness、NT-20。

## 進捗ログ

- 2026-06-14: docs/note の候補50(NT-17)から転記。定式化・証明見込みは記載済み、in-repo の証明・数値検算はこれから。
