---
status: idea
origin: NT-29
tags: [base-change, leray, pushforward, cohomology, incremental]
created: 2026-06-14
---

# NT-29 集約射の障害コホモロジー base change 定理: PR-local 計算可能性の転送

_〔定理候補・要設計〕 / 出典: docs/note の候補50_

## 主張

固定パラメータ p と有限計測 regime のもとで、集約射 π: X_fine → X_coarse(第IV部 定義14.1: module grouping / runtime grouping の有限 site 射)を取り、abelian coefficient Ob を固定する。coarse 側の点(集約単位)w ∈ X_coarse に対し fiber X_w = π^{−1}(w)(その集約単位に属する fine charts と overlaps)と base-change map φ^q_w: (R^q π_* Ob)_w → H^q(X_w, Ob) を考える。次が成り立つ。(i) 半連続性: q = 1 で w ↦ dim_k (R^1 π_* Ob)_w は X_coarse 上半連続。(ii) base-change 同型条件: ある w で φ^q_w が全射ならば近傍の全 w′ で φ^q_{w′} は同型(かつ R^q π_* Ob は w 近傍で局所自由)、すなわち集約単位内部の H^q が coarse 側 stalk として忠実に読める。(iii) cohomology-and-base-change: φ^q_w が全射 iff φ^{q−1}_w が全射、という連結条件のもとで R^q π_* Ob のファイバー値が点ごとの H^q(X_w) と一致する。これは G6(Leray 五項完全列)とは独立で、五項列の項 H^0(coarse, R^1 π_* Ob) が実際に fiberwise H^1 として計算可能になる条件を与える。すべて p / aggregation family / coefficient に相対化される。

## 依拠

第IV部 定義14.1 Leray Five-Term Debt Sequence / R^q π_* Ob、第IV部 定義14.3 Scale-Stable Debt、第VIII部 定理候補9.2 Flat Base Change Stability for LawConflict、第VIII部 定義8.1 Cellular sheaf measurement model、付録 Parameter Functoriality (A.2.1) coverage refinement comparison map、拡張ノート G6 集約五項完全列(尺度安定負債)。

## 非自明性

G6 は Leray 五項完全列で fine の隠れ結合を coarse 可視成分と集約単位内局在成分(R^1 π_*)へ「分配」するが、その R^1 π_* Ob の項が実際に集約単位ごとの H^1 として計算できるか(stalk = fiber cohomology)は保証しない。本候補は Grothendieck の「コホモロジーと基底変換」定理(R^q f_* が点でファイバーコホモロジーを計算する全射条件と局所自由性)の AAT 類似を与え、(1) 集約単位ごとに局所計算した H^1 を貼り合わせれば coarse 側 R^1 π_* が復元できる十分条件、(2) その値が近傍で安定(局所自由)になる条件、を明示する。第VIII部 定理候補9.2(LawConflict の flat base change)は Tor の base change で、本候補は障害コホモロジーの pushforward base change なので対象が異なる。G6 とも「分配 vs ファイバー計算可能性」で役割が異なる。

## CS / SWE 帰結

(a) 分散検証の核心として、「各集約単位(チーム所有のサブシステム / サービス群)で局所に計算した隠れ結合 H^1 を、再集計するだけで全体の集約レベル隠れ結合 R^1 π_* が正しく得られる」ための十分条件(base-change 全射 + 連結条件)を与える。これにより全コードベースを一度に解析せず、PR が触れた集約単位だけ再計算 → 貼り合わせ、という incremental / 分散な障害計算が健全になる(条件が満たされる限り)。(b) 局所自由性(近傍で dim 一定)は「この集約単位の隠れ結合容量は隣接変更で勝手に変わらない」という安定性を意味し、PR-local な計算結果の再利用可能性を保証する。(c) base-change が破れる集約単位(φ が全射でない w)は「そこだけは局所計算が全体を反映しない = 全体再解析が必要なホットスポット」として特定でき、分散計算の例外箇所を明示できる(移植仮定: aggregation の有限 site 射と abelian coefficient が ArchMap grouping 契約から取れること)。

## 証明・根拠の見込み

有限 poset site 上の π は各 fiber が有限複体なので、R^q π_* Ob は coarse 側の poset 上の presheaf で stalk が fiber Čech cohomology の colimit。(i) 半連続性は前候補と同じ rank 半連続論法を fiber ごとに適用する。(ii)(iii) は Grothendieck の base-change 定理の有限版を、cellular cochain 複体の完全列 0 → C^•(X_coarse, R^• π_*) → Čech double complex → fiber complexes の spectral sequence 比較として書く: double complex の一方の filtration が Leray(G6)、他方が fiber 方向で、φ^q 全射 ⇔ spectral sequence の該当 differential が退化、という標準的同値による。連結条件(φ^q 全射 iff φ^{q−1} 全射)は半完全列の長完全列追跡(Grothendieck の元の証明の有限線形代数版)。証拠: 有限次元 k-線形代数では base-change map は明示行列で、全射性チェックは rank 計算に帰着し決定可能。pseudo-circle を二つの集約単位に分けた最小 family で R^1 π_* の stalk が各単位の H^1 と一致することは有限計算で確認可能(本タスクでは Euler / 半連続の核は検算済み、base-change の明示 family 検算は今後の worked example)。完全定理化には spectral sequence の退化条件の精密化が必要である。

## 関連

G6、NT-26、原則4.4。

## 進捗ログ

- 2026-06-14: docs/note の候補50(NT-29)から転記。定式化・証明見込みは記載済み、in-repo の証明・数値検算はこれから。
