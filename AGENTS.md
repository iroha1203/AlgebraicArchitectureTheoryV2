# リポジトリ運用ガイド

## 言語と GitHub 運用

- ユーザーへの応答は日本語で行う。
- コミットメッセージは日本語で書く。
- Pull Request のタイトルと本文は日本語で書く。
- GitHub Issue のタイトルと本文は日本語で書く。
- Lean の識別子、ファイル名、コマンド名、定理名、既存の英語技術用語を引用する場合は、名前をそのまま残してよい。必要に応じて日本語で補足する。

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

## ドキュメントポリシー

- `docs` の研究主張を変更する場合は、対応する Lean status を明確にする。
- Lean status は、proved, defined only, future proof obligation, empirical hypothesis を区別する。
- Lean で証明済みの主張と、実証研究で検証する主張を混同しない。
- `proof_obligations.md` は GitHub Issues への索引としても使う。

## タスク管理

- 未解決課題は GitHub Issues で管理する。
- Issue は研究の依存構造に沿って milestone に割り当てる。
- Issue の label は `type:*`, `area:*`, `priority:*`, `status:*` を使って整理する。
- empirical extractor や実証研究の Issue は Lean proof の進行をブロックしないように扱う。

