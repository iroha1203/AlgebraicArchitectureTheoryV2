---
status: idea
origin: NT-22
tags: [castelnuovo-mumford, regularity, review-depth, commutative-algebra]
created: 2026-06-14
---

# NT-22 Castelnuovo-Mumford レビュー地平定理: regularity が修正波及の打ち止め witness サイズを与える

_〔定理候補・証明可能見込み〕 / 出典: docs/note の候補50_

## 主張

固定 reading $p$ の square-free witness regime で $I_{\mathrm{Ob}}^U(W)=I_{\Delta_U}(W)\subset R_W=k[E_W]$ とし、Castelnuovo-Mumford regularity を $\mathrm{reg}(I_{\mathrm{Ob}}^U(W)):=\max\{\,j-i\mid \beta_{i,j}(I_{\mathrm{Ob}}^U(W))\neq 0\,\}$($j$ は total degree)で定義する。次が成り立つ。
- (A) [Terai 公式] $\mathrm{reg}(I_{\mathrm{Ob}}^U(W))=\mathrm{pd}(k[\Delta_U^\vee])=|E_W|-\mathrm{depth}(k[\Delta_U^\vee])$。ここで $\Delta_U^\vee$ は Alexander dual 複体(第VIII部 定理5.2)。
- (B) [レビュー地平] $m_W:=\mathrm{reg}(I_{\mathrm{Ob}}^U(W))$ とおくと、サイズ $>m_W$ の任意の witness support 結合に新しい「本質的に新規な」minimal syzygy は現れない: すべての高次冗長関係は $m_W$ 以下のサイズの forbidden support と minimal repair hitting set の組合せから線形に生成される。形式的には、$R_W$ の $m_W$-truncation 以降で minimal resolution の差分が線形(linear strand に乗る)。
- (C) [双対会計] $\mathrm{reg}(I_{\mathrm{Ob}}^U(W))+\mathrm{depth}(k[\Delta_U^\vee])=|E_W|$ が常に成り立ち、repair hitting set 側(Alexander dual)の depth が低いほどレビュー地平が遠い。
- 相対化: $m_W$ は選ばれた witness regime / $U/J$ に相対化され、未測定 witness を含む拡張 regime では別の $m_{W'}$ になりうる。

## 依拠

第III部 定理5.6C(Stanley-Reisner Obstruction Theorem)、第VIII部 定理5.2(Stanley-Reisner / Alexander Dual Repair Theorem)、原則5.3(Repair Hitting Set Is Not Repair Semantics)、拡張ノート B10(修復計画 = collapse 列)。

## 非自明性

regularity は「resolution がいつ線形に安定するか」を測る代数幾何の中心不変量(sheaf cohomology の twisting vanishing を統御する Castelnuovo-Mumford regularity)だが、AAT には $\mathrm{reg}$ を読む定理が一切無い。Terai の定理($\mathrm{reg}(I_\Delta)=\mathrm{pd}(k[\Delta^\vee])$)は SR-ideal の regularity を Alexander dual の射影次元へ厳密に転送する非自明な双対定理であり、第VIII部 定理5.2 が repair hitting set として導入済みの Alexander dual に新しい定量的意味(= レビュー地平の双対量)を与える。これは定義の言い換えではなく、regularity と射影次元の双対(可換代数の深い結果)に依拠する。

## CS / SWE 帰結

「修正の波及をどこまでの witness サイズまで追えば打ち止めになるか」を初めて鋭い数で与える。従来は「大きな pattern も小さな pattern も全部見るしかない」という無限地平だったが、$\mathrm{reg}(I_{\mathrm{Ob}}^U(W))$ より大きい witness 結合には本質的に新しい障害が生まれないことが保証される。これは静的解析の探索深さ(combinatorial blow-up の打ち切り点)に証明付き上界を与え、レビュー / CI の解析バジェットを安全に有限化する。さらに (C) の双対会計により、repair hitting set 側の構造(Alexander dual の depth)が浅いほど地平が遠い =「直すべき箇所は少ないが、波及を追う深さは深い」という非自明なトレードオフを数値で読める。B10 の collapse 列(離散 Morse 修復)の最大長とも regularity が上界関係を持つと期待され、修復手数の地平とも接続する。

## 証明・根拠の見込み

(A) は Terai (1999) の定理 $\mathrm{reg}(I_\Delta)=\mathrm{pd}_R(R/I_{\Delta^\vee})$。戦略は Hochster 公式(NT-17 の (A))で $I_\Delta$ の Betti 数を $\Delta$ の induced 部分複体の reduced homology で表し、Alexander 双対性 $\tilde H_i(\Delta|_S)\cong \tilde H^{|S|-i-3}(\Delta^\vee|_S)$ を介して $\Delta^\vee$ の Betti 数へ移す、というもの。これにより $\mathrm{reg}(I_\Delta)=\max$ linear shift が $\mathrm{pd}(k[\Delta^\vee])$ に一致する。(B) は regularity の定義(Eisenbud-Goto)から、$\mathrm{reg}$ を超える degree では resolution の generator が linear strand のみになることが従う。(C) は (A) と Auslander-Buchsbaum を組合せる。検算: $E=\{p,q,r\}$、$\mathrm{Forb}=\{\{p,q\},\{q,r\}\}$ の例で $I_{\mathrm{Ob}}=\langle pq,qr\rangle$ は degree-2 generator と共有 $q$ による degree-3 first syzygy を持ち $\mathrm{reg}=2$、Alexander dual の hitting set は $\{q\},\{p,r\}$(定理5.2 の最小被覆)で $\mathrm{pd}(k[\Delta^\vee])=2$ となり (A)(C) と整合する。Macaulay2 の regularity / Alexander dual コマンドで finite regime 即検算可能。

## 関連

NT-17、NT-21、B10。

## 進捗ログ

- 2026-06-14: docs/note の候補50(NT-22)から転記。定式化・証明見込みは記載済み、in-repo の証明・数値検算はこれから。
