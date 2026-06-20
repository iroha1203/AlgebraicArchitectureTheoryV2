---
status: idea
origin: NT-33
tags: [acyclic-cover, cech, comparison, leray]
created: 2026-06-14
---

# NT-33 適格 cover の消滅・比較定理: acyclic cover で Čech が sheaf cohomology を計算する

_〔定理候補・証明可能見込み〕 / 出典: docs/note の候補50_

## 主張

AAT site Site_AAT(S,V,U,J) と obstruction sheaf Ob_U を固定する。cover U = {W_i → W} が U-acyclic、すなわち全ての有限 overlap W_{i_0…i_p} 上で H^q(W_{i_0…i_p}, Ob_U) = 0 (q ≥ 1) であるとする。このとき (A 比較) 自然写像 Ȟ^n(U, Ob_U) → H^n(W, Ob_U) は全 n で同型(Leray/acyclic-cover 定理の AAT 版で、Čech が sheaf cohomology を計算する)。さらに (B 消滅) nerve N(U) の組合せ次元が d なら全 n > d で H^n(W, Ob_U) = 0。とくに N(U) が森(b_1 = 0)かつ acyclic cover なら H^n(W, Ob_U) = 0 (n ≥ 1) で、local lawful sections は(effective torsor regime で)常に大域へ貼り合う。仮定は U-adequate cover、restriction-stable witness ideal、coefficient descent に相対化される。

## 依拠

第II部 命題7.2C Finite Poset Computation、第II部 補題7.2A Witness-Closure Cover、第IV部 定理12.4 Local Gluing Sufficiency、第IV部 定理4.1 Obstruction Cohomology、第III部 定義6.2 Obstruction Ideal Sheaf。

## 非自明性

本文は命題7.2C 末尾と第II部 line 631–632 で「Čech が sheaf cohomology を計算するには Leray/acyclic cover/refinement limit を別途固定する」と繰り返し明示し、これを未確立の開放端として残している。G2(c)/定理12.4 は「森+全射 restriction で H^1 = 0」という H^1 限定・combinatorial 限定の十分条件にすぎず、(i) 高次 H^n の消滅、(ii) Čech と真の sheaf cohomology の一致(比較定理)を扱っていない。本候補はこの二つを acyclic-cover 条件で同時に確立し、AAT の cohomological 結論が cover 選択に依らない「真の不変量」として読める基盤を与える。これは「どの cover で測っても同じ」という比較定理であり、measurement の cover 非依存性の鍵で、単なる定義の言い換えではない。

## CS / SWE 帰結

現状 ArchSig 等は固定 cover 上の Čech H^1 を出すが、別の module 分割(別 cover)で測れば違う値が出るかもしれず、結論が分割依存だった。本定理は acyclic cover を選べば Čech 値が cover 非依存の sheaf cohomology に一致することを保証するので、「この分割で隠れ結合ゼロ」が「どんな細分でもゼロ」へ昇格する(分割依存 artifact と真の構造障害の判別)。さらに消滅条件は「nerve を組合せ次元 d 以下に保てば d より高い coherence 障害(多重 feature 同時破綻)は原理的に発生しない」という設計指針を与え、三重以上の feature 相互作用バグの不在を分割の形だけで保証できる(移植仮定: overlap 上の acyclicity をツールが検証可能なこと)。

## 証明・根拠の見込み

(1) acyclic cover に対する Čech-to-derived spectral sequence E_1^{p,q} = ⊕ H^q(W_{i_0…i_p}, Ob_U) ⇒ H^{p+q}(W, Ob_U)(定理候補10.4 の枠組み)を使い、acyclicity から E_1^{p,q} = 0 (q ≥ 1) ゆえ p-行に退化、E_2^{p,0} = Ȟ^p へ collapse して比較同型 (A) を得る。(2) 消滅 (B) は finite poset nerve の組合せ次元 d で C^n = 0 (n > d) ゆえ Ȟ^n = 0、(A) で H^n(W) = 0。命題7.2C の「n > d で C^n = H^n = 0」を sheaf cohomology へ持ち上げた形。(3) 森+acyclic は d を 1 に落とし b_1 = 0 で H^1 = 0、定理12.4 と整合(本候補が定理12.4 を acyclicity 込みで一般化・高次化することを確認)。証拠: 第VIII部の finite measurement regime は overlap が局所 affine で高次 Čech が消える典型例を多く含むため、acyclicity は square-free/Boolean regime で自然に成立しやすい。未確立: 一般 site での acyclicity 充足条件(どの coefficient/cover で overlap acyclic か)の特徴づけは候補のまま残す。

## 関連

G2、NT-34、第II部 site。

## 進捗ログ

- 2026-06-14: docs/note の候補50(NT-33)から転記。定式化・証明見込みは記載済み、in-repo の証明・数値検算はこれから。
