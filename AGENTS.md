# リポジトリ運用ガイド

## 言語と GitHub 運用

- ユーザーへの応答は日本語で行う。
- コミットメッセージは日本語で書く。
- Pull Request のタイトルと本文は日本語で書く。
- GitHub Issue のタイトルと本文は日本語で書く。
- Lean の識別子、ファイル名、コマンド名、定理名、既存の英語技術用語を引用する場合は、名前をそのまま残してよい。必要に応じて日本語で補足する。

## Codex 作業 Rules

- 作業は原則として GitHub Issue 起点で進める。
- 次タスクを選ぶときは、`priority:blocking`, `status:ready`, milestone の依存順を優先する。
- Issue が前提タスクの完了で着手可能になった場合は、必要に応じて `status:blocked` を外し、`status:ready` を付ける。
- 実装作業は `main` を最新化してから専用ブランチを切る。
- ブランチ名は Issue 番号または作業内容が分かる名前にする。
- PR 本文には対象 Issue を `Closes #N` 形式で明記する。
- PR 本文は `.github/pull_request_template.md` に沿って、概要、証明した定理、編集したドキュメント、実施したテスト、チェックリストを埋める。
- 既存の未コミット変更がある場合は、ユーザーの変更として扱い、勝手に戻さない。
- `git reset --hard` や `git checkout --` のような破壊的操作は、明示的な依頼なしに実行しない。

## PR 前チェック

- Lean 変更を含む PR では、必ず `lake build` を実行する。
- ドキュメントのみの PR でも、Lean status や import に影響しないか確認する。迷う場合は `lake build` を実行する。
- PR 前に `git diff --check` を実行する。
- PR 前に hidden / bidirectional Unicode scan を実行し、bidi control や zero-width 文字が混入していないことを確認する。
- Lean ソースに `axiom`, `admit`, `sorry`, `unsafe` が混入していないか、必要に応じて確認する。
- GitHub PR 作成後は `gh pr checks --watch` などで CI の `lake build` が通ることを確認する。

## プロジェクト構成

- Lean ライブラリの root は `Formal.lean`。
- 中核となる形式化は `Formal/Arch` 以下に置く。
- 研究ノートは `docs` 以下に置く。
- `Main.lean` は実行ターゲット `aatv2` を提供する。
- build 設定は `lakefile.toml`。
- Lean バージョンは `lean-toolchain` で固定する。

## Build コマンド

- `lake build`: すべてのターゲットを build する。
- `lake build Formal`: Lean ライブラリだけを build する。
- `lake exe aatv2`: 実行ターゲットを実行する。
- `lake env lean Formal/Arch/Layering.lean`: 単一ファイルを type-check する。

## 形式化ポリシー

- 明示的な相談なしに `axiom`, `admit`, `sorry`, `unsafe` を導入しない。
- 定義は小さく保ち、同値性や対応関係は定理として育てる。
- 現在の `Decomposable` は `StrictLayered` を意味する。
- acyclicity, finite propagation, nilpotence, spectral conditions は `Decomposable` の定義に混ぜない。これらは別個の定理または将来の proof obligation として扱う。
- `ComponentCategory` は thin category であり、path count や walk length を意図的に忘れる。
- 定量指標は `Walk`, `Path`, adjacency matrix, または将来の free-category construction 側で扱う。
- executable metrics は、まず有限な測定 universe 上の計算として定義し、graph-level facts との接続は別 theorem として証明する。
- `ComponentUniverse` は proof-carrying measurement universe として扱う。実コードベース抽出器の完全性を直接主張しない。

## ドキュメントポリシー

- `docs` の研究主張を変更する場合は、対応する Lean status を明確にする。
- Lean status は、proved, defined only, future proof obligation, empirical hypothesis を区別する。
- Lean で証明済みの主張と、実証研究で検証する主張を混同しない。
- `proof_obligations.md` は GitHub Issues への索引としても使う。
- theorem や定義を追加した場合は、必要に応じて `docs/proof_obligations.md` の Lean status を更新する。
- 研究の大目標は「設計原則はアーキテクチャ不変量を保存・改善する操作であり、品質は不変量の破れを多軸シグネチャとして評価する」ことである。この主張と矛盾する説明を追加しない。
- Architecture Signature は単一スコアではなく、多軸診断として扱う。
- 設計原則の分類では、SOLID を万能原理として扱わない。SOLID は局所契約層、Layered / Clean Architecture は大域構造層、Event Sourcing / Saga / CRUD は状態遷移代数層、Circuit Breaker / Replicated Log は実行時依存・分散収束層として整理する。

## タスク管理

- 未解決課題は GitHub Issues で管理する。
- Issue は研究の依存構造に沿って milestone に割り当てる。
- Issue の label は `type:*`, `area:*`, `priority:*`, `status:*` を使って整理する。
- empirical extractor や実証研究の Issue は Lean proof の進行をブロックしないように扱う。
