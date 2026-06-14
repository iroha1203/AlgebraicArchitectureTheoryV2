---
status: idea
origin: NT-30
tags: [massey-product, formality, higher-coherence, a-infinity]
created: 2026-06-14
---

# NT-30 高次法則整合定理: Massey 積による隠れ結合の段階障害

_〔予想・予想(強)〕 / 出典: docs/note の候補50_

## 主張

固定された AAT site Site_AAT(S, V, U, J)、abelian 係数 obstruction sheaf Ob_U(coefficient ring k は体)、有限 poset regime(命題7.2C / 定義7.2B)を相対化基底とする。feature 拡張族 {f_1, …, f_n} に対し、各境界 mismatch class [g_i] ∈ H^1(X, Ob_U) を考える。このとき次が成り立つと予想する。(A) pairwise の隠れ結合類がすべて消える([g_i] = 0 ∀i、すなわち定理7.1 の H^1 障害が個別に存在しない)にもかかわらず、n 個の feature を同時に統合すると n 重 overlap 上に高次整合障害が現れることがあり、その第一非自明障害はちょうど Massey 積 ⟨[g_{i_1}], …, [g_{i_m}]⟩ (3 ≤ m ≤ n) で測られ、これは(下位 Massey 積の不定性で割った)剰余類として H^{m−1}(X, Ob_U) の元を well-defined に定める。(B) すべての m 重(3 ≤ m ≤ n)Massey 積が(不定性込みで)零 ⇔ DG 代数 (C^•(𝒰, Ob_U), d, ∪) が n 次まで形式的(n-formal)⇔ pairwise compatible な局所 lawful section 族が n 重 overlap まで両立する coherent gluing data へ持ち上がる。Massey 積の値は cup product ∪ と nerve N(𝒰) の組合せ構造に相対化され、選ばれていない係数・cover・law には沈黙する。

## 依拠

第IV部 定理7.1 Local Flatness Gap / hidden coupling class [hc_U(X)] ∈ H^1、第IV部 定義10.1 Triple Overlap Coherence Failure 2-cocycle h_{ijk} / [h] ∈ H^2、第IV部 定理候補10.4 Multi-Feature Mayer–Vietoris Spectral Sequence(E_2^{2,0} ≠ 0)、第IV部 意味4.2 H^2 = coherence obstruction / H^n = n-fold coherence obstruction、付録 Čech complex の cup product と nerve N(𝒰)、個別予想ノート: pairwise boundary holonomy / higher Massey product 的高次干渉が未着手と明記された開放端。

## 非自明性

既存の H^1(隠れ結合)・H^2(三重 overlap)は「個別 class の非零」しか測れず、map の開放端は「三つ以上の feature の higher syzygy / Massey product が未着手」と明記している。本予想は pairwise = 0 でも triple 以上で初めて現れる障害を、Čech DG 代数の Massey 積として明示的に構成し、しかも「n-formality ⇔ coherent gluing への持ち上げ可能性」という ∞-コヒーレンス的同値を与える。これは G2(容量)・定理10.4(spectral sequence の E_2^{2,0} が残りうる、という存在主張)を超え、残る class が具体的に Massey 積として計算可能であることを主張する点で非自明である。標準代数幾何 / 位相幾何の Massey product・形式性(formality, Deligne–Griffiths–Morgan–Sullivan)の AAT 類似であり、d_2 微分を Massey 積として読む点で定理10.4 の d_2 を初めて具体化する。

## CS / SWE 帰結

これまで「二つずつ整合する feature は全体でも整合する」と暗黙に仮定されてきた多 feature 統合(feature flag の組合せ、plugin 三つ以上の相互作用、DDD aggregate の三者結合)に対し、pairwise レビューでは原理的に検出不能な「三項以上でのみ壊れる」整合障害を Massey 積という具体的 cocycle として計算・局在化できる。CI / レビューに対し「何項まで同時に見ればよいか(= n-formality の最小 n)」という新しい下界を与える。例: round(tax(discount)) 型の semantic 非可換が二項では消えても三項(tax / discount / loyalty)で復活する状況を、係数・cover 相対の Massey 残基として測れる(移植仮定: Čech DG 代数の cup と Massey 積が有限線形代数で計算可能であること、有限 poset regime)。

## 証明・根拠の見込み

(1) 有限 poset regime で C^•(𝒰, Ob_U) は cup product を持つ有限次元 DG 代数(各 C^n が overlap 上の有限直積、∪ は overlap 制限の組合せ)。(2) [g_i] = 0 なら g_i = d c_i と書け、古典的 Massey 積構成(⟨a, b, c⟩ = a·s + t·c 型、s, t は中間 cochain の選択)がそのまま定義でき、不定性は下位積の生成するイデアル。(3) Massey 積が d_2 微分と一致することは Mayer–Vietoris spectral sequence(定理10.4)の標準理論(Massey product は spectral sequence の higher differential を計算する、という既知の対応)から従う。(4) (B) の同値は「DG 代数が formal ⇔ minimal A_∞ 構造の高次積 m_k (k ≥ 3) が消える ⇔ Massey 積が消える」という A_∞ 形式性の標準結果の有限版 decoration による。支持証拠: 擬円周モデル(例9.3, H^1 ≅ Z)を二重に張り合わせた「擬トーラス」cover で、二つの H^1 generator の Massey 積が H^2 の非零 class を生む有限線形代数例が構成できる(下位 cup が消える non-formal な最小例)。境界: m ≥ 3 の Massey 積の well-defined 性には cup product の高次結合性(A_∞ 構造)の固定が必要で、これを相対化パラメータとして明示する。

## 関連

第IV部 H^1 障害、NT-31、NT-28。

## 進捗ログ

- 2026-06-14: docs/note の候補50(NT-30)から転記。定式化・証明見込みは記載済み、in-repo の証明・数値検算はこれから。
- 2026-06-14: 検討メモ — Massey 積の well-defined 性は A∞ / DG 構造の固定を要する。双子の NT-31(スペクトル系列退化, B)と対であり、棚卸しで両者まとめて B(高次コヒーレンス束)へ移す可能性あり。
