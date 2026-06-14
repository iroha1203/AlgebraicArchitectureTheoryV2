---
status: idea
origin: NT-45
tags: [semicontinuity, betti, moduli, refactor-family]
created: 2026-06-14
---

# NT-45 AAT 半連続性・Betti 跳躍定理: refactor 族における障害 Betti 数の上半連続性

_〔予想・予想(強)〕 / 出典: docs/note の候補50_

## 主張

refactor 族を有限 base B 上の平坦な architecture geometry の族 𝔛 → B(各 fiber X_b が reading p で square-free witness regime、第VI部 evolution family pi: 𝔛 → B / 第VIII部 定義7.1 refactor morphism の族版)とし、obstruction ideal sheaf I_Ob^U が族上で定義されているとする。このとき:
- (A) [Betti 上半連続性] 各 (i, S) に対し b ↦ beta_{i,S}(R_{W,b} / I_Ob^U(W_b)) は B 上で上半連続(upper semicontinuous): generic な b で最小値を取り、特殊な b(より singular な refactor 状態)で跳ね上がる。
- (B) [Tor ジャンプ軌跡] 二つの law universe U, V に対し b ↦ dim_k H^0(X_b, LawConflict_1(U,V)_b) も上半連続で、その跳躍軌跡 Jump_{U,V} := {b | dim が generic 値を超える} ⊆ B は閉部分集合であり、「どの refactor 状態で derived law conflict が顕在化するか」を局在化する。
- (C) [Euler 標数の局所定数性] それに対し交代和 χ = Σ_i (−1)^i dim H^?(LawConflict_i) は平坦族で局所定数(G5 の Euler 恒等式が族で安定)であり、Betti の跳躍は次数間で相殺してのみ起こる(質量保存の精密化)。
- 相対化: 平坦性・有限性・係数固定に相対化。base change が非平坦なら新しい Tor 生成で (A)(C) が破れうる(第VIII部 定理候補9.2 の境界)。

## 依拠

第V部 定義5.1 First Law Conflict Sheaf、第V部 定理12.2 Hilbert Series Conflict Identity、第VI部 evolution family pi: 𝔛 → B、第VIII部 定理候補9.2 Flat Base Change Stability for LawConflict、第VIII部 定理7.3 Refactor Invariance under Equivalence、拡張ノート G5 / G6。

## 非自明性

定理7.3 は「同型 refactor で verdict が保存される」という離散不変性しか述べず、refactor を連続族(base B 上の変形)として捉えて Betti 数や Tor 次元の変動を統御する半連続性は AAT に皆無。定理候補9.2 は単一 base change の flat 安定性までで、族全体での semicontinuity・跳躍軌跡の閉性・Euler 標数の局所定数性(Grauert の連接層 base change 半連続性、Hilbert 関数の半連続性の AAT 類似)は未着手。これは可換代数/代数幾何の深い定理(graded Betti 数の半連続性、平坦族での Hilbert 多項式の局所定数性)に依拠し、定義の言い換えでない。族 𝔛 → B 自体は第VI部に名前があるが、その上の semicontinuity は誰も書いていない。

## CS / SWE 帰結

「リファクタリングの途中経過(部分的な変形)で、設計障害がどの段階で跳ね上がるか」を初めて閉軌跡として局在化する。(A) は「generic な refactor 状態では障害の冗長度(Betti)が最小だが、特定の中間状態で構造的に跳ね上がる」= リファクタの危険な中間ステップを Betti の半連続性で検出。(B) の Jump_{U,V} は「二つのポリシーの衝突がどの refactor 段階で顕在化するか」を閉部分集合として与え、段階的 migration(incremental rollout)で「この中間コミットで初めて conflict が表面化する」点を事前に局在化できる。(C) は「障害の総量(Euler 標数)は平坦な refactor では保存され、Betti の跳躍は必ず別次数の減少と相殺する」= G5 の質量保存を族へ拡張し、リファクタが障害を消すのでなく次数間・段階間で移すという経験則(系12.5 の精神)を連続変形で精密化する。CI で「どのコミットが Betti を跳ね上げたか」を半連続性の破れとして自動検出する道を開く。

## 証明・根拠の見込み

(A) 平坦族上の連接層のコホモロジー次元の上半連続性は Grauert / Hartshorne III.12 の半連続性定理の有限類似。square-free regime では Betti 数 beta_{i,S} が Hochster 公式で induced 部分複体の reduced homology 次元なので、族で witness の incidence が変わると homology が generic に最小・特殊点で跳ねる。証明戦略: multigraded Betti を fiber ごとに Koszul homology の rank として表し、行列式階数の下半連続性(= 次元の上半連続性)を使う。(B) LawConflict_1 = Tor_1 の fiber 次元の半連続性は Tor の base change スペクトル系列と平坦性から(定理候補9.2 の族版)、跳躍軌跡が閉なのは rank が落ちる行列式軌跡(determinantal locus)が閉だから。(C) 平坦族で Euler 標数(Hilbert 多項式の交代和)が局所定数なのは古典的(平坦 ⟺ Hilbert 多項式が一定)で、G5 の Tor-Euler 恒等式が族で係数ごとに安定することから従う。証拠: 検算済みの I_U = ⟨xy⟩, I_V = ⟨xz⟩ の Tor_1 が共有 witness x の有無でジャンプする(命題9.2 の shared-witness 反例 s_t: x ↦ 1, y ↦ 1−t, z ↦ t で U-residue が 1 → 0、V-residue が 0 → 1)は、base parameter t に沿った Tor 次元のジャンプの1次元 family の実例で、本予想の最小モデルになる。Macaulay2 で parametric に Betti を追えば finite regime で検証可能。

## 関連

G5、NT-17、第VIII部 定理候補9.2。

## 進捗ログ

- 2026-06-14: docs/note の候補50(NT-45)から転記。定式化・証明見込みは記載済み、in-repo の証明・数値検算はこれから。
