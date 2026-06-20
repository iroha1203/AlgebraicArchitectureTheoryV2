---
status: idea
origin: NT-27
tags: [kunneth, derived-conflict, tor, vanishing]
created: 2026-06-14
---

# NT-27 法則干渉の Künneth 公式と衝突消滅: 変数分離なら全次 derived conflict が消える

_〔定理候補・証明可能見込み〕 / 出典: docs/note の候補50_

## 主張

common ambient (X, O_X) 上で、square-free monomial obstruction ideal I_U ⊂ k[E_U]、I_V ⊂ k[E_V] を持つ二つの law universe を取る。witness 変数集合が交わらない(E_U ∩ E_V = ∅)、すなわち law universe が変数分離的に独立であるとき、テンソル分解 R = k[E_U] ⊗_k k[E_V] の下で
LawConflict_i(U, V) = Tor_i^R(R/I_U^e, R/I_V^e) = 0 (全 i ≥ 1)
が成り立つ(変数分離なら全次の derived conflict が消える = derived-transverse)。より一般に E_U ∩ E_V = S ≠ ∅ のとき、共有変数だけの ambient k[S] 上の Tor で Künneth 型分解
LawConflict_i(U, V) ≅ ⊕_{a+b=i} Tor_a^{k[S]}( Ī_U, Ī_V ) ⊗ (自由部分)
が成り立ち、derived conflict は共有 witness support S に局在する(共有因子のみが Tor を生む)。すべて選ばれた common ambient / grading / witness family に相対化される。

## 依拠

第V部 定義5.1 First Law Conflict Sheaf、第V部 命題5.5 Monomial Conflict Calculation、第V部 例5.6 Shared Witness Factor Conflict、第V部 定理7.3 Derived Transversality Criterion、第V部 定理12.2 Hilbert Series Conflict Identity、第VIII部 定理候補9.2 Flat Base Change Stability for LawConflict。

## 非自明性

既存 G5(Hilbert 級数干渉恒等式)は H_{R/I_U}·H_{R/I_V}/H_R = Σ(−1)^i H_{LawConflict_i} という Euler 標数(交代和)レベルの会計に留まり、各次 Tor が個別に消えるか・どこに局在するかは言わない(交代和ゼロでも個々の Tor は非零でありうる)。本候補は変数分離独立性から全次 Tor の消滅(= derived-transverse、定理7.3 の充足十分条件)を立て、共有変数があるときは Tor が共有 support に完全局在するという Künneth 分解を与える。これは Euler 標数より強い「各次の精密会計」であり、例5.6(共有因子 x が Tor_1 ≠ 0 を生む)を一般法則へ昇格する。標準 Künneth(独立な空間の Tor は分解する)の monomial AAT 版で、定理候補9.2(base change)とも整合する独立構造定理である。

## CS / SWE 帰結

二つの設計ポリシー(例: layering 規約 U と authority 規約 V)が「同じ witness を共有しないなら、合成しても derived な相互干渉(片方を直すと他方が悪化する隠れた conflict)は一切生じない」ことを証明できる。これは「U-safe ∧ V-safe ⇒ jointly safe」(原則3.2 が一般には否定する命題)が成り立つ十分条件を初めて構造的に与える。逆に共有 witness がある場合、本候補は「干渉はその共有 witness 上だけに局在する」ことを保証するので、ポリシー間の衝突を全コードでなく共有 support に限定して監査できる。実務的には「どのポリシー対が安全に独立合成でき、どの対は共有 witness で衝突するか」のポリシー直交性マトリクスを Tor 計算で自動生成できる(移植仮定: witness 変数の分離 / 共有を ArchMap が判定可能なこと)。

## 証明・根拠の見込み

戦略は次の通り。(1) 変数分離 E_U ∩ E_V = ∅ の場合、R = k[E_U] ⊗_k k[E_V] は両因子上 flat で、R/I_U^e と R/I_V^e はそれぞれ片因子からの base change だから、flat base change(定理候補9.2)で Tor_i^R(R/I_U^e, R/I_V^e) ≅ ⊕ Tor_a^{k[E_U]}(R/I_U, k[E_U]) ⊗ Tor_b^{k[E_V]}(k[E_V], R/I_V) = 0 (i ≥ 1)(各因子で片方が自由)。これは標準的代数 Künneth である。(2) 共有 S の場合は k[S] へ base change して相対 Künneth スペクトル系列を取り、free 部分が縮約して共有 Tor へ局在する。(3) 例5.6(I_U = ⟨xy⟩, I_V = ⟨xz⟩, 共有 x)で Tor_1 ≠ 0 が z-class として現れ共有 x support に局在する既存計算が、共有 = 非自明・非共有 = 消滅という本候補の予測を支持する。(4) G5 との整合検算: 変数分離なら H_{R/I_U}·H_{R/I_V}/H_R = H_{R/(I_U+I_V)}(干渉級数 Int = 0)で全 Tor 消滅と一致する。未確立: 一般 monomial(square-free でない)や非 flat ambient での補正項は候補として残る。

## 関連

G5、NT-28、原則3.2。

## 進捗ログ

- 2026-06-14: docs/note の候補50(NT-27)から転記。定式化・証明見込みは記載済み、in-repo の証明・数値検算はこれから。
