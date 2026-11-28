# ArchSig v0.6.0 Phase 6 PRD：実用運用基盤・分断解消・CLI 品質刷新

| 項目 | 内容 |
| --- | --- |
| 状態 | Draft |
| 対象配置 | `tools/archsig_v0.6.0/**`, `docs/tool/archsig_v0_6_0_io/**` |
| 親計画 Issue | GitHub Issue `#6376`（Phase 6） |
| 基準仕様・数学本文 | [ArchSig v0.6.0 製品コンセプト](../tool/archsig_v0_6_0_concept.md), [ArchSig v0.6.0 I/O 仕様](../tool/archsig_v0_6_0_io/README.md)（`definitions.md`, `inputs.md`, `law.md`, `computations.md`, `execution.md`, `results.md`）, [第19章 観測の改訂・無効化範囲と多源統合](../aat/algebraic_geometric_theory/part_6/chapter_19_observation_revision_and_source_integration.md)（19.2, 19.4, 19.5） |
| 適用ガイドライン | [Tool guideline](../tool/guideline.md), [Workflow guideline](../workflow/guideline.md), [PRD guideline](guideline.md), [語彙ルール](../workflow/vocabulary.md) |
| CI 変更要否 | 不要（既存の ArchSig v0.6.0 Cargo workspace テスト・Clippy・fmt で検証する） |

---

## 1. 問い

Phase 1〜5 によって、ArchSig v0.6.0 には Observed 計算核（`crates/computation`）と 17 種の SHIGURE 計算核（`crates/shigure`）がそろった。しかし現状のままでは、二つの計算系が分断されており、CLI ツールとしての操作性・出力設計・性能・異常系処理にも現場導入を阻む課題が残っている。

本 PRD では次の問いに答える。

> 既存の 3 つの入力形式（`archsig.atom-definition/1`, `archsig.law/2`, `archsig.archmap/2`, `semantics "archsig/0.6.0"`）と計算の健全性を保ったまま、Observed 系と SHIGURE 系の分断を解消し、実リポジトリの開発ループで日常的に安全・高速・快適に使える実用基盤を確立できるか。

---

## 2. 現状診断

現行の実装をコードレベルで確認したところ、実リポジトリでの運用を始める前に解消すべき課題が 3 つの領域に整理できた。

### 2.1 Observed 系と SHIGURE 系の分断

| 課題 | 現状の実装と影響 |
| --- | --- |
| 混在実行ができない | `src/run/evaluate.rs` と `src/run/shigure.rs` が `--ask` を Observed 専用と SHIGURE 専用に二分しているため、同じ `archsig run` で両方を使うと即座に `usage` エラー（exit 64）になる。 |
| 問いの連鎖・`needed`・`reobserve` が使えない | `src/run/shigure/deliver.rs` は `dependencies: []` を固定出力しており、前の問いの結果を `$id.field` で次へ渡せない。`needed($id)` による不足スロット確認や `reobserve` での前後比較にも SHIGURE は対応していない。 |
| 同じ型の対象が複数あると動かない | `crates/shigure/src/convert/lower_expr.rs` の `observed` 解決は、スナップショット内に該当する `entity` 型の subject が 1 個だけであることを前提にしている。複数のアカウントや複数サービスを含む現実の ArchMap では `ambiguous observed subjects` エラーになる。 |
| 仕様を二重に書く必要がある | 通常の `reading`（`view` / `law` / `change`）で書いた対象に SHIGURE 計算をかけようとすると、別に `shigure presentation` 等を手で書き直さなければならない。 |

### 2.2 リポジトリ運用（鮮度検証・差分影響・多源トリアージ）の不足

- **`evidence` の手動指定が重い**: `src/observe.rs` の `archsig evidence` は、`--atom` と `--source ID=FILE` を 1 件ずつ手で列挙する必要がある。リポジトリ全体に対して古い観測を一括検出したり、変更ファイルから陳腐化（stale）した Atom 集合 $\Delta$ を抜き出して AAT 第19章 19.2 の無効化錐 $\operatorname{Cone}(\Delta)$ へ渡したりする経路がない。
- **語彙 digest の更新に手間がかかる**: Atom 定義を編集するたびに、一時ファイル `bootstrap.law` を作って `archsig check --out` を実行し、出力 JSON から digest を手で転記する必要がある。
- **多源証拠の食い違いを ArchMap のまま扱えない**: 現行の ArchMap（`inputs.md`）は同じ `(subject, field)` への重複記録を `duplicate_fact` で即拒否する。そのため、静的解析・実行観測・LLM 読解候補・人間採用の食い違いをそのまま入力し、AAT 第19章 19.4–19.5（高次衝突の抽出と最小由来支持の算出）でトリアージする日常フローが成立していない。

### 2.3 CLI 品質・出力・性能・例外処理の課題

- **コマンド体系と操作性**
  - `src/run/args.rs` は `--flag value` ペア専用の手書きパーサであり、`--flag=value` 形式、複数問いをまとめた `--ask-file`、3 入力を束ねる明示マニフェスト（`--project`）に対応していない。
  - `reobserve` では、定義ファイルや Law が変わっていなくても `--before-*` 側をすべて二重に指定する必要がある。
  - `evidence` と `law-fibers` だけが `src/main.rs` で別分岐（`archsig::observe::handles`）になっており、引数処理・ヘルプ・エラー形式が二系統に割れている。
- **出力の過剰さと読みにくさ**
  - Observed 系（`crates/computation/src/observed/summary.rs`）の stdout は、件数要約・反例最大 3 件・文字列 256 byte 上限・ネスト深さ 2 でうまく抑えられている。一方、SHIGURE 系（`src/run/shigure/deliver.rs`）は `outcome.to_json()`（82 構造体・185 箇所の JSON フィールド）の全量を一切削らず stdout にダンプし、さらに同じ全量を `saved_nodes` にも複製している。
  - 具体的には、意思決定に必要な結論に紛れて、通過済みの `applicability[]` 全件、内部の自己検算フラグ群（`*_verified`）、巨大な証明データ（`residual_ideal[]`, `empty_witness.cofactors[]`, `syzygy_generators[][]`）、全件列挙（`distinguishing_pairs[]`, `rejected_candidates[]`, 全 `provenance`）が毎回 stdout に流れ込み、受け手（開発者・AI エージェント）を困らせている。
  - 出力形式も 1 行の compact JSON 固定であり、人間や PR レビューでそのまま読める形式（`pretty` / `human`）がない。また、Observed の `--out`（`result.json`）は `nodes: [n0, n1, ...]` の正規化 DAG になっているため、特定の反例や根拠だけを取り出す手段がない。
- **I/O・メモリ・リソース暴走**
  - `src/run.rs` の `Outcome::receipt()` が `summary` を `clone()` して全文 `String` に展開してから書き出しており、ストリーミング出力になっていない。`--reuse` 実行時も旧 `result.json` の全バイト列、現在の評価結果、保存用 DOM、要約、入力コピーが同時にメモリへ並存する。
  - `std::fs::read` にファイルサイズ上限がなく、`crates/common/src/json.rs` と `canonical.rs` にも明示的なネスト深度上限がない。
  - `crates/shigure/src/algebra/groebner.rs` には S-pair 個数上限はあるが、有理数 `Rat`（`BigInt`）のビット長膨張や多項式の項数に対する上限ガードがない。また `crates/shigure/src/` 全体に `DEFAULT_MAX_*` / `const MAX_*` が 29 箇所散在しており、一覧確認も調整もできない。
  - `--out` 保存時に毎回 5〜10 回以上の `sync_all()`（`fsync`）を直列発行している。一時ディレクトリ名には乱数がなく、終了時は `std::process::exit` を直呼びして `Drop` を飛ばしている。
  - `nix`（POSIX シグナル）、`rustix`（`renameat_with`）、`OsStrExt` が各所に直書きされており、クロスプラットフォーム対応が分離されていない。
- **並列化・中断・計算時間**
  - 複数の `--ask` や多数ファイルの `evidence` 検証が完全シングルスレッドで直列実行される。
  - `src/run/shigure.rs` は問いと問いの間でしか `Control`（協調中断）を確認していない。Gröbner 基底や全列挙などの重い計算中に `SIGINT` / `SIGTERM` を送っても止まらず、`--timeout` オプションもない。
  - Phase 3 の代表規模ベンチマーク（301 subjects / 3,001 atoms）では、`observed+global_check` が約 30 秒かかっている。また `Cargo.toml` に `[profile.release]` の最適化設定がない。
- **例外処理とエラー診断**
  - `src/main.rs` が空の `panic::set_hook` を設定し、`src/run.rs` の `catch_unwind` もパニックの原因メッセージと発生位置を捨てて `"internal failure during computation"` のみを返すため、障害原因を追跡できない。
  - 入力検査が最初の 1 エラーで即終了（fail-fast）するため、複数の記述ミスを直すのに何度も再実行する必要がある。ソースの抜粋スニペット、類似名の提案、および `SilenceReason` ごとの対処案内もない。

### 2.4 肥大化ファイル一覧（先行分割の基準）

[Tool guideline](../tool/guideline.md) の「単一ファイル目安 1,000 行」に従い、以下のファイルには無条件に追記せず、必要な場合は先に責務分割するか独立モジュールへ分離する（2026-11-28 時点、テスト除く）。

- **1,000 行超（直接追記禁止）**:
  `crates/input/src/law/expr.rs`（1,839 行）, `crates/input/src/law/parser.rs`（1,579 行）, `crates/input/src/input/comparison.rs`（1,552 行）, `crates/input/src/definition/primitive.rs`（1,340 行）, `crates/input/src/archmap/complete.rs`（1,294 行）, `crates/input/src/definition/reader.rs`（1,088 行）、および `crates/computation/src/observed/` 配下の既存大型ファイル群。
- **900 行台（追記前に分割を検討）**:
  `crates/shigure/src/solver/artin.rs`（981 行）, `crates/input/src/archmap/value.rs`（944 行）, `crates/shigure/src/solver/family_eval.rs`（942 行）, `crates/shigure/src/solver/occurrence.rs`（925 行）, `crates/shigure/src/ir/atlas.rs`（919 行）, `crates/shigure/src/solver/chevalley.rs`（909 行）, `crates/shigure/src/solver/common_solve.rs`（905 行）, `crates/shigure/src/solver/chevalley_sections.rs`（903 行）, `crates/shigure/src/solver/preservation.rs`（901 行）, `crates/shigure/src/solver/diagnostics.rs`（900 行）。

---

## 3. 全体設計と不変条件

### 3.1 守るべき不変条件

1. **既存入力と終了コードの互換**
   - 入力形式（`archsig.atom-definition/1`, `archsig.law/2`, `archsig.archmap/2`, `semantics "archsig/0.6.0"`）と終了コード体系（0 / 1 / 2 / 64 / 65 / 69 / 70 / 74 / 130 / 141 / 143）は維持する。
   - ただし stdout の既定詳細度は、意思決定に必要な情報だけを返す `--detail concise` へ統一する（Observed 系の `summary.rs` と同じ考え方）。SHIGURE の監査用全量エビデンスは `--detail full` または `--out` の `result.json` で取得する。
   - 既存の Phase 1〜5 全量検証 E2E テストは、`--detail full` または `--out` の `result.json` を検証する形へ明示的に移行し、数学的な検証項目自体は一切弱めない。
2. **結論注入の禁止と由来分離**
   - 自動 lowering、多源トリアージ、差分影響分析のいずれでも、判定結論を外部入力から注入させない。
   - 由来種別（`static_analysis`, `runtime_observation`, `llm_candidate`, `human_adopted`）とソース参照を型レベルで区別し続ける。
3. **判断不能（`undetermined`）の原則**
   - ファイルサイズ上限、JSON ネスト深度、`BigInt` 桁数、多項式項数、`--timeout`、自動 lowering の対象外構文に当たった場合は、暗黙の近似や誤った `established` / `refuted` を返さない。必ず理由コード付きの `undetermined`（または入力上限エラー／`interrupted`）を返す。
4. **出力の決定性**
   - `--jobs N` による並列実行や複数エラー一括収集を有効にしても、出力 JSON・エラー順序・回答順序は入力と問いの指定順に対して常に決定的とする。

### 3.2 モジュール配置の方針

`crates/computation/src/observed/` へは直接機能を追加しない。新設機能は次の独立モジュール境界へ配置し、新規 `.rs` ファイルは目安 1,000 行未満（目標 700 行以下）に保つ。

```text
tools/archsig_v0.6.0/
├── crates/
│   ├── common/src/
│   │   ├── limits.rs             # ファイルサイズ・JSON 深度・共通上限の定義
│   │   └── diagnostic.rs         # スニペット・サジェスト・複数診断の共通表現
│   ├── input/src/
│   │   ├── archmap/candidates.rs # 多源候補（由来別ファクト）の後方互換読込・検査
│   │   └── manifest.rs           # 明示マニフェスト（--project）の読込・検査
│   └── shigure/src/
│       ├── limits.rs             # 散在 29 上限を一元化する ShigureLimits と BigInt/項数ガード
│       ├── bridge/               # 通常 reading から SHIGURE IR への自動 lowering 変換層
│       └── summary.rs            # SHIGURE concise 要約・結論と監査エビデンスの分離
└── src/
    ├── platform/                 # OS 依存層（シグナル・原子的リネーム・OsStr）
    ├── cli/                      # 統一コマンドパーサ・出力フォーマット・ヘルプ
    ├── commands/                 # digest / inspect / impact / evidence 一括検証
    └── run/
        ├── unified.rs            # Observed + SHIGURE 混在実行・依存解決・並列実行
        └── shigure/              # ストリーミング配送・reobserve 接続
```

---

## 4. 受け入れ条件（Acceptance Criteria）

本節を本 PRD の一次仕様とする。

### AC1：OS 依存分離・統一上限・リソース暴走ガード

- **プラットフォーム分離**: `src/main.rs`, `src/run.rs`, `src/observe.rs` にある Unix 固有呼び出し（`nix` シグナル操作、`rustix` 原子的リネーム、`OsStrExt`）を `src/platform/` へ分離する。起動時のシグナル初期化に失敗しても無言パニックせず、`Result` で構造化エラーを返す。
- **上限の一元化（`ShigureLimits`）**: `crates/shigure/src/` に散在する 29 箇所の `DEFAULT_MAX_*` / `MAX_*` 定数を `ShigureLimits` 構造体へ集約する。既定値は維持しつつ、適用上限の参照と明示調整、および上限到達時の診断出力ができるようにする。
- **暴走ガード**:
  1. 全ファイル読込（`run`, `check`, `evidence`, `law-fibers`, `--reuse`）に既定ファイルサイズ上限（例：64 MiB、明示指定で変更可）を設け、超過時はメモリ展開前にエラーを返す。
  2. JSON パーサとエンコーダ（`crates/common/src/json.rs`, `canonical.rs`）に明示的なネスト深度上限（例：256）を設け、無制限再帰を防ぐ。
  3. `crates/shigure/src/algebra/`（Gröbner 基底・syzygy・SNF）に `BigInt` ビット長上限と多項式項数上限を導入する。超過時は誤判定せず、`AlgebraError::ResourceLimitExceeded` を経由して理由付き `undetermined` を返す。

### AC2：Observed 系と SHIGURE 系の分断解消

- **混在実行と問い間の連携**:
  - Observed 問い（`build`, `evaluate`, `check`, `solve`, `prepare`, `apply`, `needed` 等）と SHIGURE 17 問いを、同じ `archsig run` コマンドで並べて実行できる。
  - 問い同士の `$id.field` 参照による依存グラフを統一的に解決し、循環依存は従来どおり exit 64 で拒否する。Observed 問いの出力（スカラー値や `apply` 後の `Architecture` 状態など）を SHIGURE 問いの入力束縛へ渡せる。
- **SHIGURE での複数 subject 指定**:
  - 同じスナップショット内に同じ `entity` 型の subject が複数あっても、`observed @snapshot/subject.field` または CLI の `bind` 引数（例：`shigure_solve(Task, bind.acc=@snap/acc1)`）で一意に指定できる。
  - 同型 subject が 1 個だけの既存 `observed Entity.field` 記法はそのまま動く。2 個以上あるのに未指定なら、候補の subject ID 一覧を添えたエラーを返す。
- **通常 `reading` からの自動 lowering**:
  - 通常の `reading` のうち多項式・アフィン表現に収まる `view` / `law` / `change` 宣言から、手動で `shigure presentation` を書き直さずに SHIGURE 計算核（まずは `shigure_preservation`, `shigure_solve`, `shigure_interaction`, `shigure_revision`）へ変換する最小垂直スライスを `crates/shigure/src/bridge/` に用意する。
  - 再帰 `data` や非多項式演算など対象外の式を含む場合は、暗黙に近似せず、該当箇所と理由を示して `undetermined`（または変換不可エラー）を返す。
- **`needed` と `reobserve` の SHIGURE 対応**:
  - `needed($shigure_id)` が SHIGURE 問いの未観測スロットと未決理由を通常の `ObservationPlan` 形式で返せる。
  - `archsig reobserve` で SHIGURE 問いの前後比較ができ、作用素不変時の SNF 再利用（AAT 19.3 / `shigure_revision`）を活用できる。

### AC3：コマンド体系・I/O 刷新と発見性サブコマンド

- **統一 CLI パーサと入力の省力化**:
  - 既存コマンド（`check`, `run`, `reobserve`, `evidence`, `law-fibers`, `version`, `help`）と新設コマンドを `src/cli/` の共通パーサへ統合する。
  - `--flag=value` 形式、`--ask-file PATH`（1 行 1 問い、コメントと空行を無視、`-` で stdin 読込）、明示マニフェスト `--project PATH`（3 入力と既定問いを束ねる。暗黙のファイル探索は行わない）をサポートする。
  - `reobserve` で `--before-atom-definition` や `--before-law` を省略した場合は、現在側と同じファイルを使う。
- **発見性サブコマンドと保存結果の参照**:
  - `archsig digest --atom-definition D ...`：語彙 manifest と canonical SHA-256 digest を直接出力し、一時 `bootstrap.law` の手順を不要にする。
  - `archsig inspect --atom-definition D --law L [--archmap A]`：通常宣言・SHIGURE 宣言・snapshot・subject・未観測スロットの一覧を表示する。
  - `archsig inspect --result DIR [--answer ID] [--evidence]`：`--out` に保存した `result.json` から、指定した回答の結論・反例・詳細エビデンス・ソース位置だけを引き出す。Observed 系の `nodes` 参照（`n0` / `n1` 等）も自動で解決して見やすく返す。
- **出力フォーマット・詳細度・保存と終了の行儀**:
  - `--format json|pretty|human`（既定は 1 行 canonical JSON の `json`）と、`--detail concise|full`（既定は `concise`）を提供する。`human` モードでは反例・修復案・欠測・由来・ソース位置を人がそのまま読める形で表示する。
  - `--out` は既定の「親既存・出力先未存在」の安全規則を保ったまま、`--create-parents`（親ディレクトリ自動作成）、`--overwrite`（明示上書き）、`--no-fsync`（一時実行・CI 向けの高速保存）を追加する。
  - 一時ディレクトリ名にランダムサフィックスを付けて衝突を防ぎ、失敗・中断時は確実に削除する。`main` は `std::process::exit` を直呼びせず `ExitCode` でクリーンに終了する。
  - `--verbose` / `--progress` 指定時は、実行中のフェーズと問いの進捗を stderr へ出す（stdout の JSON contract を汚さない）。

### AC4：リポジトリ一括鮮度検証・無効化錐差分影響分析・ArchMap 多源トリアージ

- **リポジトリ一括鮮度検証（`archsig evidence --root REPO_DIR --all`）**:
  - ArchMap に登録された全 `sources` と全 `observed` Atom について、`REPO_DIR` 基準のローカルファイルと SHA-256・UTF-8 byte span を一括照合する。
  - 一致・変更（digest 不一致）・ファイル欠落・span 逸脱を一覧で報告する（従来の `--atom` / `--source ID=FILE` 個別指定もそのまま残す）。
- **無効化錐による差分影響分析（`archsig impact`）**:
  - ローカルリポジトリと ArchMap の差分から陳腐化（stale）した Atom 集合 $\Delta$ を抽出し、AAT 第19章 19.2 の無効化錐 $\operatorname{Cone}(\Delta)$ へ接続する。
  - 「再観測・再検証が必要な Atom・Law・問い」と、「錐外にあるため既存の確定評価がそのまま有効な範囲」を根拠付きで返す。
- **ArchMap レベルの多源トリアージ**:
  - 既存 `archsig.archmap/2` の後方互換（新フィールド未記述時の `model_digest` 不変）を保ちつつ、同じ `(subject, field)` に対する複数由来候補（`static_analysis`, `runtime_observation`, `llm_candidate`, `human_adopted`）を保持できる拡張を導入する。
  - この多源候補を `shigure_multisource`（AAT 第19章 19.4–19.5）へ直結し、(1) ペアワイズでは整合するのに 3 源以上で破綻するケースを含む全包含極小矛盾集合、および (2) 結論を確定するために人間が確認すべき最小由来支持（特に `llm_candidate` の優先確認リスト）を、元のソース位置（ファイル・span・行番号）付きで返す。

### AC5：例外処理とエラー診断の刷新

- **パニック原因の構造化保持**:
  - 空の `panic::set_hook` と `catch_unwind` による原因破棄を解消する。パニック発生時はメッセージと発生位置（`file:line`）をスレッドローカルで捕捉し、内部エラー `receipt`（exit 70）の `details` に `panic_message` と `panic_location` を必ず含める（`--verbose` または `RUST_BACKTRACE=1` 時は stderr にもバックトレース要約を出す）。
- **複数エラーの一括収集**:
  - `check` と `run` の入力検査（定義・Law・ArchMap・問い構文）で、独立した構文・参照・型エラーを 1 件目で打ち切らず、上限（例：50 件）までまとめて収集して決定的順序で返す。
  - 単一エラー時の既存 `code`・`location`・終了コード（64 / 65 / 69）の互換性は維持する。
- **分かりやすい診断と対処ガイド**:
  - `--format human`（および JSON の `details.hint` / `details.suggestions`）で、該当箇所の行・列・ソース抜粋、未定義識別子に対する類似候補の提案、および `SilenceReason` ごとの推奨アクション（欠測スロットの確認先、上限調整対象、モデル分割の案内など）を返す。

### AC6：出力の結論／エビデンス分離・メモリ削減・協調中断・並列化・性能改善

- **SHIGURE stdout の結論／監査エビデンス分離（既定 `--detail concise`）**:
  - `src/run/shigure/deliver.rs` の無制限ダンプ（`outcome_json.clone()`）を廃止し、出力を 2 層に分ける。

| 出力モード | 想定する受け手 | 含める情報 | 省略する情報 |
| --- | --- | --- | --- |
| **`--detail concise`**（既定 stdout） | 日常開発・AI エージェント・CI 要約 | `status` / `verdict`、結論の要点（復元された主要変更、上位の最小観測集合／最小由来支持）、代表反例・矛盾 1〜3 件と総件数、不足スロット、**失敗した** `applicability` 条件のみ、省略件数と `--detail full` / `--out` への案内 | 通過済み（`satisfied: true`）の `applicability[]`、内部自己検算フラグ群（`*_verified`）、`residual_ideal[]`、`empty_witness.cofactors[]`、`syzygy_generators[][]`、`distinguishing_pairs[]` 全件、`rejected_candidates[]` 全件、全 `provenance` のフル展開 |
| **`--detail full`** または **`--out` の `result.json`** | 数学的監査・詳細デバッグ・再現検証 | 上記すべての証明データ・全検算フラグ・全件列挙・全 `provenance` を完全保持 | なし |

  - 配列件数や文字列バイト数も Observed 系の `summary.rs` と整合する上限で抑える。全量 `ShigureOutcome` は `--out` 保存時のみ 1 回だけ書き出し、メモリ上の二重保持をなくす。
  - 既存の Phase 1〜5 全量検証 E2E テストは、`--detail full` または `--out` の `result.json` を見る形へ明示的に移行し、検証内容は弱めない。
  - `Outcome::receipt()` の全文 `String` 化をやめ、`BufWriter` + `write_canonical` 等で stdout / stderr へ直接ストリーミング出力する。
- **メモリ多重保持の削減**:
  - `--reuse` 照合が終わった旧 `result.json` のバイト列を即座に解放し、`--out` 保存時の DOM と入力コピーの生存期間を最小化してピーク RSS を抑える。
- **SHIGURE 計算核への協調中断貫通と `--timeout`**:
  - `Control` を `archsig-shigure` のソルバと主要ループ（Gröbner 基底、syzygy、Chevalley 層別、全列挙、hitting set、partition 等）の内部へ通す。計算途中の `SIGINT` / `SIGTERM` でも速やかに停止し、確定済みの他問いの回答を残して `interrupted` を返す。
  - `--timeout <DURATION>`（例：`10s`, `500ms`）を追加し、時間超過時も同じ協調中断経路で確定済み回答と `timeout` 理由を安全に返す。
- **並列実行とホットパス最適化**:
  - `--jobs <N>` により、依存関係のない複数 `--ask` と `evidence --root --all` の多数ファイル SHA-256 検証を並列実行する（出力順序は決定的に保つ）。
  - Phase 3 実測で約 30 秒かかった Observed 300+ subjects 経路をプロファイリングしてホットパスを改善し、`Cargo.toml` に `[profile.release]` の最適化設定（LTO 等）を加える。

### AC7：恒久仕様書同期・テスト・代表規模ベンチマーク

- **恒久文書の同期**: `docs/tool/archsig_v0_6_0_io/`（`README.md`, `inputs.md`, `law.md`, `computations.md`, `execution.md`, `results.md`）と `tools/archsig_v0.6.0/README.md` を本 PRD の全変更と同期する。
- **テストと品質ゲート**:
  - 単体テスト・代数的性質テスト・実バイナリ E2E テストを整備し、新設機能（混在実行、多重 subject、自動 lowering、一括 `evidence`、`impact` 無効化錐、多源トリアージ、`concise`/`full` 分離、`inspect --result`、パニック診断、複数エラー収集、SHIGURE 中断・`--timeout`・`--jobs` 決定性、暴走ガード）を網羅する。
  - `cargo fmt --check`、`cargo clippy`、`cargo test --workspace`、`cargo test --doc --workspace`、および [Workflow guideline](../workflow/guideline.md) の PR 前共通確認（`git diff --check`、不可視 Unicode 検査）がすべて通ること。
- **代表規模ベンチマーク実測（Mac release `/usr/bin/time -l`）**:
  - 固定の代表入力（300〜400+ subjects / 2,000〜3,000+ atoms 級、多問 SHIGURE、大出力 SHIGURE、多ファイル `evidence`）で変更前後を各 3 回実測し、次を確認して記録する。
    1. 既存経路に退行がなく、Observed 300+ subjects 経路の実行時間が有意に短縮されていること。
    2. SHIGURE 大出力ケースで既定 stdout のバイト数が大幅に抑えられ、ピーク RSS が削減されていること。
    3. `--jobs` 並列実行でスループットが向上し、単一スレッド時と出力が完全一致すること。

---

## 5. Failure Contract（失敗判定条件）

次のいずれかに当てはまる場合、本 PRD は**未達（Reject）**とする。

1. AC6 で明示移行する SHIGURE stdout 既定の `--detail concise` 化を除き、既存の入力形式、終了コード、または既存 Phase 1〜5 テストの数学的検証項目に無断の破壊的変更や弱化がある。
2. 肥大化した `crates/computation/src/observed/` や 1,000 行超の既存ファイルへ、先行分割なしに新機能をそのまま追記している。
3. 自動 lowering、リソース上限ガード、タイムアウト、または多源トリアージで、対象外入力・上限超過・未観測依存を暗黙に近似したり、誤った `established` / `refuted` に丸めたりしている。
4. 既定の `--detail concise` stdout に過剰エビデンス（通過済み `applicability`、内部 `*_verified` フラグ群、`residual_ideal`、`empty_witness.cofactors`、`syzygy_generators`、全件列挙ダンプ）が残っている。または SHIGURE 計算核の内部で `SIGINT` / `SIGTERM`・`--timeout` が効かない。
5. パニック捕捉で原因メッセージと発生位置が依然として捨てられている、または `--jobs` 並列実行で出力順序が非決定的になる。
6. 恒久仕様書・README の同期漏れ、代表規模ベンチマークの実測記録漏れ、または完了前の時点で本 PRD への参照がリポジトリ内の他文書・コードに残っている。

---

## 6. 対象外（Non-Goals）

以下は本 PRD では扱わず、#6376 の後続フェーズ（Phase 7〜9）へ送る。

- **Phase 7 対象**: 整数線形不等式（`Z` の `<=`, `>=`）修復、有限参照再配線（`Ref` / `Map` 更新）を許す構造変更 `change`、AAT 付録E（移行幅・一時接続ピーク・費用最適経路）、AAT 第21章 21.10–21.14（パレート最適化・上書き置換・適応的観測決定木・整数剰余観測）。
- **Phase 8 対象**: AAT 第20章 20.9–20.11（最小公開インターフェース補完）、AAT 第12章 12.8–12.10（ペア・三重混合障害・要求変更耐性）、AAT 第23章 23.4（有限ハンケル表からの最小実現復元）、AAT 第24章（最大安全初期状態スキーム）。
- **Phase 9 対象**: Phase 1〜8 を束ねた同梱 `archsig-observe` SKILL の全面統合、代表 OSS 通し実測 QA、実測に基づく高度な永続キャッシュ戦略とメモリ予算制御の細部調整、外部手法接続、配布パッケージング。
- **アーキテクチャ上の非対象**: プログラミング言語固有の AST 解析器を ArchSig 計算核へ組み込むこと、およびカレントディレクトリや環境変数から入力ファイルを暗黙に探索すること。

---

## 7. 実装計画（依存順のステップ）

Issue や PR の実際の分割・統合粒度は `$prd-loop` 側で判断する。各変更は `tool-review`（独立 1 lane）と CI を通してマージし、最終完了は独立 2 lane の `prd-completion-review` で判定する。

1. **Step 1（土台整理・AC1）**: OS 依存層（`src/platform/`）の分離、`ShigureLimits` への 29 上限集約、ファイルサイズ・JSON ネスト深度・`BigInt` 桁数・多項式項数の暴走ガード実装、および必要な先行分割。
2. **Step 2（コマンド体系・I/O・例外処理・AC3 / AC5）**: 統一 CLI パーサ（`src/cli/`）、`digest` / `inspect` / `inspect --result` サブコマンド、`--format`・`--detail`・`--out` 保存行儀改善・`ExitCode` クリーン終了、構造化パニック診断・複数エラー一括収集・スニペットとサジェストの実装。
3. **Step 3（Observed / SHIGURE 統合・AC2）**: 統一ランナー（`src/run/unified.rs`）による混在実行と `$id` 依存解決、SHIGURE の複数 subject 明示指定、通常 `reading` からの自動 lowering 変換層（`crates/shigure/src/bridge/`）、`needed`・`reobserve` の SHIGURE 接続。
4. **Step 4（鮮度・差分影響・多源トリアージ・AC4）**: `evidence --root --all` 一括鮮度検証、`archsig impact` による陳腐化 Atom 抽出と無効化錐 $\operatorname{Cone}(\Delta)$ 接続、ArchMap 多源候補と `shigure_multisource` 連携による最小矛盾集合・最小由来支持・ソース位置逆写像出力。
5. **Step 5（出力分離・中断・並列化・性能改善・AC6）**: SHIGURE stdout の既定 `--detail concise` 化と既存全量検証テストの移行、stdout ストリーミング配送と `--reuse` 重複保持削減、SHIGURE 計算核への `Control` 貫通と `--timeout`、`--jobs` 並列実行、Observed 300+ subjects ホットパス改善と `[profile.release]` 最適化。
6. **Step 6（仕様同期・ベンチマーク・完了検証・AC7）**: 恒久仕様書と README の同期、代表規模 Mac release ベンチマーク実測比較、全テスト・lint・PR 前共通確認、および最終完了レビュー後の PRD 整理。

---

## 8. 停止条件

次のいずれかに当たった時点で作業を止め、状況を整理して人間へ判断を求める。

1. 既存入力形式や `archsig.summary/1`・`archsig.result/4` の後方互換（AC6 で明示合意した `concise` 化を除く）を破らなければ解決できない設計衝突が見つかった場合。
2. 通常 `reading` からの自動 lowering や ArchMap 多源候補の仕様について、既存仕様書にない意味境界（変換対象の式クラスや `model_digest` の扱いなど）の設計判断が必要になった場合。
3. Observed 300+ subjects ホットパスの改善にあたり、`crates/computation/src/observed/` の大規模な構造変更や既存計算仕様の意味変更が避けられないと判断された場合。
4. クロスプラットフォーム分離（Windows 向けシグナルや原子的リネーム）のために、新規クレート依存の追加や CI 環境の変更が必要になった場合。
5. 代表規模ベンチマークで既存経路の明確な性能退行やメモリ増加が解消できない場合、または CI 合計 3 分以内の条件（[Tool guideline](../tool/guideline.md#ci-への追加)）を圧迫する兆候が出た場合。
