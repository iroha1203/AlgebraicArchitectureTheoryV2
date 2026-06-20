---
status: idea
origin: NT-37
tags: [vanishing-theorem, forest-cover, local-review]
created: 2026-06-14
---

# NT-37 AAT 消滅定理: 森型 cover での高次障害コホモロジー消滅と局所完全性

_〔定理候補・証明可能見込み〕 / 出典: docs/note の候補50_

## 主張

固定有限計測 profile M を相対化基底とする。cover nerve N(U) の clique complex(nerve simplicial complex)Nrv(U) を、頂点 = chart、k-単体 = (k+1) 個の chart の共通 overlap が非空、として構成する。obstruction sheaf Ob_M が各 overlap 上で flabby/acyclic(各 overlap 上で H^{>0} = 0、すなわち overlap が Leray acyclic)であり、かつ Nrv(U) の simplicial cohomology が H^n(Nrv(U); k) = 0 for n ≥ n_0(nerve が n_0 − 1 次元以下にホモロジー的に縮む)であるとき、(消滅)Čech-to-derived 比較が成立し H^n(X_M, Ob_M) = 0 for all n ≥ n_0。特に Nrv(U) が collapsible(可縮)なら全 n ≥ 1 で H^n = 0、Nrv(U) が森(1次元かつ無閉路)なら G2(c) と整合して H^1 = 0。系として、acyclic cover regime では cover-relative Čech cohomology が sheaf cohomology を計算する(Leray の十分条件が AAT site で初めて固定される)。結論は profile / 係数 / cover の acyclicity 仮定に相対化される。

## 依拠

第II部 命題7.2C Finite Poset Computation(nerve dimension d で n > d で C^n = 0)、第II部 開放端(Leray 条件 / acyclic cover / refinement limit が未固定)、第IV部 定理12.4 Local Gluing Sufficiency(forest cover で H^1 = 0)、第IV部 定義12.1 Cover Nerve、G2(c) 局所レビュー十分性(消滅定理)。

## 非自明性

第II部の開放端で「Čech が sheaf cohomology を計算するための Leray 条件 / acyclic cover の十分条件は別途固定する、AAT site での acyclic cover の十分条件が空白」と明記されている。G2(c) と定理12.4 は H^1 = 0 の森ケースのみで、全次数 H^{≥n_0} = 0 の高次消滅は誰も述べていない。これは標準代数幾何の Leray の定理(acyclic cover で Čech = sheaf cohomology)と Cartan-Leray 消滅、さらに Grothendieck の「次元 > 位相次元で消える」消滅定理の AAT 類似であり、第II部が未固定とした Leray comparison を nerve の clique complex の acyclicity という具体条件で初めて確立する。命題7.2C(nerve 次元による消滅)を係数の acyclicity と組み合わせて真の sheaf cohomology 消滅へ昇格させる点が非自明。

## CS / SWE 帰結

「どんなモジュール分割なら高次の統合障害(H^2 以上の多 feature coherence 障害)が原理的に存在しえないか」を nerve の組合せ的形だけで判定できる。具体的には: 三重 overlap が無く各 overlap が単純(acyclic)な cover では H^{≥2} = 0 が保証され、ペアワイズ・レビューだけで coherence 障害の不在が証明できる(三つ組同時検査が不要)。clique complex が collapsible な分割では全高次障害が消える = 「この分割は構造的にバグの高次結合を許さない」という設計保証。実コードでは nerve の clique complex を組合せ的に計算し collapsibility を判定するだけ(小規模なら自前、GUDHI でも可)。これは「どこまでローカルにレビューすれば大域安全か」のレビュー深度の上限を nerve から読む新しい道。

## 証明・根拠の見込み

Leray spectral sequence E_2^{p,q} = H^p(Nrv(U), R^q(Ob)) ⇒ H^{p+q}(X_M, Ob_M) を用いる。overlap acyclicity 仮定により R^q(Ob) = 0 for q > 0 なので E_2 は q = 0 行に集中し退化、H^n(X_M, Ob_M) ≅ H^n(Nrv(U), Ob_M^0) が従う(これが AAT site での Leray comparison の固定)。次に Nrv(U) の simplicial cohomology が n ≥ n_0 で消えるなら右辺が消える。森ケースは clique complex が 1 次元 contractible 成分の disjoint union で H^{≥1} = 0、定理12.4 を回収する。命題7.2C は nerve dimension d で C^n = 0 (n > d) を既に与えており、本定理は「次元による消滅」を「acyclicity + simplicial 消滅による真の cohomology 消滅」へ精密化する。有限なので spectral sequence は有限ページで収束し全て厳密。特別な場合の collapsible nerve では discrete Morse(B10)の collapse 列が simplicial 消滅の構成的証拠を与える。

## 関連

G2、NT-33、B10。

## 進捗ログ

- 2026-06-14: docs/note の候補50(NT-37)から転記。定式化・証明見込みは記載済み、in-repo の証明・数値検算はこれから。
