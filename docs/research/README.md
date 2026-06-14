# 研究アイデアの蓄積(research inbox)

このディレクトリは、AAT / SFT 研究で得た数学的アイデアを帰納的に貯める場である。
完成した体系ではなく、定理候補・予想・反例・数値実験・部分証明・小さな観察を、
粒度を問わず継続的に蓄積する。一定量たまったら棚卸し(stocktaking)し、
数学本文への取り込みと Lean 形式化をそこで判断する。

## 狙い

帰納法的に進める。先に体系を決めてから埋めるのではなく、発見を書き溜め、
後から整理して体系化する。だから個々のエントリは未完成・暫定でよい。
誤りや棄却も記録として残す(なぜ落ちたかが次の発見の材料になる)。

## docs/note / 本文との関係

- `docs/note/`: 完結した設計考察ノート・フルレビューなど中〜大の文書。
- `docs/research/`(ここ): 進行中の粒度の小さいアイデアを貯める inbox。
- `docs/aat/mathematical_theory/`, `docs/aat/algebraic_geometric_theory/`: 体系化された数学本文(取り込み先)。
  **保護ファイルであり、取り込みはユーザーの明示承認を要する。**
- `docs/aat/proof_obligations.md`, `docs/aat/lean_theorem_index.md`: Lean 形式化の台帳(取り込み先)。

## 1エントリの規約

- 1ファイル1テーマ(または1アイデア)。ファイル名は `<slug>.md`(kebab-case)。
- 冒頭に YAML frontmatter を置く:

  ```yaml
  ---
  status: idea        # idea | developing | vetted | promoted | archived
  origin: NT-17       # 出典(候補50なら NT-番号、新規なら new)
  tags: [stanley-reisner, cohomology]
  created: 2026-06-14
  ---
  ```

- 本文は [`TEMPLATE.md`](TEMPLATE.md) に従う(主張 / 依拠 / 非自明性 / CS・SWE 帰結 / 証明・根拠の見込み / 進捗ログ)。
- claim discipline は [AAT guideline](../aat/guideline.md) に従う。相対化されたパラメータ(vocabulary / law universe / coverage topology / 係数 / profile)を保ち、
  神の視点・現実コード全体・意味宇宙全体・全未来予測のような無制限 claim を持ち込まない。
  計測絡みの帰結は「移植仮定付き」と明記し、acyclic / 障害なしの箇所は unmeasured ではなく measured_zero の structural reading として書く。

## status の意味

- `idea`: 着想のみ。定式化はこれから。
- `developing`: 定式化・証明・反例を試している最中。
- `vetted`: 数学的に確からしい(証明設計が立つ、または数値検算が通る)。本文 / Lean 取り込みの候補。
- `promoted`: 数学本文または Lean 台帳に取り込み済み(取り込み先をリンクする)。
- `archived`: 棄却または長期保留(理由を残す)。

## 棚卸し(stocktaking)

一定量たまったら次を行い、結果を下の「棚卸しログ」に追記する。

1. 各エントリの `status` を更新する。
2. `vetted` を仕分ける: (a) 数学本文へ取り込む候補、(b) Lean 形式化候補、(c) 保留。
3. (a) は本文の章立てのどこに入るかを設計する(本文は保護ファイル。更新はユーザー承認後)。
4. (b) は `proof_obligations.md` / `lean_theorem_index.md` に proof obligation 行を起こす。
5. 関連エントリを束ね、必要なら `docs/note/` の考察ノートや PRD に昇格する。

## 現在のエントリ

- バッチ起点: [`docs/note/aat_ag_new_theorem_conjecture_candidates_50.md`](../note/aat_ag_new_theorem_conjecture_candidates_50.md)
  — AAT 代数幾何版の新定理候補・予想 50(NT-01〜50)。A / B / C 優先度分類済み。
  ここから個別に育てるものを本ディレクトリへ切り出していく。

### A 束(2026-06-14 候補50 から切り出し、すべて `status: idea`)

道具立てで 3 束に分かれる。棚卸しでは束ごとに本文取り込み / Lean 形式化を判断する。

**α 組合せ可換代数**(SR 環 + minimal free resolution + Macaulay2)

- [NT-17 Hochster-Betti 冗長制約定理](nt-17-hochster-betti-redundancy.md) — 制約の冗長度を Betti 数で局在化
- [NT-18 AAT Hochster 公式](nt-18-hochster-local-cohomology.md) — 局所コホモロジーの多重次数分解
- [NT-22 Castelnuovo-Mumford レビュー地平定理](nt-22-castelnuovo-mumford-review-horizon.md) — regularity = 修正波及の打ち止め
- [NT-24 代数的 Morse 縮約](nt-24-algebraic-morse-lawconflict.md) — LawConflict 最小化と Betti 下界
- [NT-45 AAT 半連続性・Betti 跳躍定理](nt-45-betti-semicontinuity.md) — refactor 族での Betti 上半連続性

**β コホモロジー会計の関手性**(Euler 標数 / Čech / 有限線形代数)

- [NT-26 集約 GRR 会計定理](nt-26-aggregation-grr-accounting.md) — 粒度変更に沿う Euler 標数保存
- [NT-27 法則干渉の Künneth 公式と衝突消滅](nt-27-kunneth-conflict-vanishing.md) — 変数分離で derived conflict 消滅
- [NT-28 アーキテクチャ Künneth 定理](nt-28-architecture-kunneth.md) — 合成系の障害 = 因子のテンソル積
- [NT-29 集約射の base change 定理](nt-29-cohomology-base-change.md) — PR-local 計算可能性の転送
- [NT-33 適格 cover の消滅・比較定理](nt-33-acyclic-cover-comparison.md) — acyclic cover で Čech = sheaf cohomology
- [NT-37 AAT 消滅定理](nt-37-forest-cover-vanishing.md) — 森型 cover で高次障害消滅

**γ 輸送・スペクトル下界**(LP 双対 + sheaf Laplacian + 凸最適化)

- [NT-46 負債輸送の Kantorovich 双対](nt-46-kantorovich-review-potential.md) — 1-Lipschitz レビュー優先ポテンシャル
- [NT-47 輸送下界 = 調和質量](nt-47-transport-lower-bound-harmonic.md) — 本質負債の輸送的不可避性
- [NT-49 AAT 熱流リファクタ収束定理](nt-49-heat-flow-refactor-convergence.md) — sheaf 熱方程式の指数収束

**高次コヒーレンス**(A∞ 前提のため棚卸しで B へ移す可能性、NT-31(B) と対)

- [NT-30 高次法則整合定理](nt-30-massey-higher-coherence.md) — Massey 積による段階障害

## 棚卸しログ

- （まだなし）
