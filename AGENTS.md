# リポジトリ作業ガイド

このファイルは、このモノレポで Codex が迷わず作業を始めるための入口である。
詳細な編集方針は各領域の `guideline.md` に分ける。

- [AAT / Lean guideline](docs/aat/guideline.md)
- [SFT guideline](docs/sft/guideline.md)
- [Tooling guideline](docs/tool/guideline.md)
- [Website guideline](docs/website/guideline.md)

## 基本運用

- ユーザーへの応答は日本語で行う。
- コミットメッセージ、Pull Request のタイトルと本文、GitHub Issue のタイトルと本文は日本語で書く。
- Lean の識別子、ファイル名、コマンド名、定理名、既存の英語技術用語はそのまま残してよい。
- 作業は原則として GitHub Issue 起点で進める。次タスクを選ぶ場合は `priority:blocking`, `status:ready`, milestone の依存順を優先する。
- このリポジトリは個人開発であり、常に最小実装・最小差分を選ぶ必要はない。目的に対して自然に必要な設計、実装、docs、tests、website surface まで広げてよい。
- ただし、無関係な既存変更の巻き戻し、claim boundary を越える主張、根拠のない互換性維持、不要な抽象化は避ける。
- AAT / SFT の数学本文は根幹文書である。ユーザーの明示的な指示なしに `docs/aat/mathematical_theory/`、`docs/sft/software_field_theory.md`、`docs/sft/aat_interface.md` を更新しない。
- 実装作業は `main` を最新化してから専用ブランチを切る。ブランチ名は Issue 番号または作業内容が分かる名前にする。
- PR 本文には対象 Issue を `Closes #N` 形式で明記し、`.github/pull_request_template.md` に沿って書く。
- 既存の未コミット変更はユーザーの変更として扱い、勝手に戻さない。
- `git reset --hard` や `git checkout --` のような破壊的操作は、明示的な依頼なしに実行しない。

## モノレポの地図

このリポジトリは Lean 形式化、Rust tooling、公開 website、研究 docs が同居する。
同じ語でも領域によって責務が違うため、作業前に対象領域を確認する。

| 領域 | 主な場所 | 役割 | 詳細 |
| --- | --- | --- | --- |
| Lean / AAT | `Formal/Arch`, `Formal.lean`, `Main.lean` | AAT / SFT の形式化、定義、定理、例。 | [AAT guideline](docs/aat/guideline.md) |
| AAT docs | `docs/aat` | AAT 数学本文、Lean status、proof obligation。 | [AAT guideline](docs/aat/guideline.md) |
| SFT docs | `docs/sft` | Software Field Theory と AAT / SFT interface。 | [SFT guideline](docs/sft/guideline.md) |
| Tooling | `tools/archsig`, `tools/fieldsig`, `docs/tool` | ArchMap / LawPolicy / ArchSig / FieldSig の CLI、schema、workflow。 | [Tool guideline](docs/tool/guideline.md) |
| Website | `website`, `docs/website` | Cloudflare Pages 向け public reading surface と内部運用メモ。 | [Website guideline](docs/website/guideline.md) |
| Archive | `docs/archive` | 過去文書の退避先。現行 source of truth として扱わない。 | [docs README](docs/README.md) |

## 基礎概念

- AAT は Atom から architecture object、law、obstruction circuit、operation、flatness、path / homotopy、analytic representation を構成する局所代数の核である。
- Lean で証明済みの主張、定義のみの概念、将来の証明義務、実証仮説は混同しない。
- SFT は artifact、practice、AI、review、CI、operational feedback が software evolution の reachable future をどう変えるかを扱う。
- ArchMap は source-grounded Atom observation map であり、law-independent な観測を記録する。
- LawPolicy / interpretation profile は選ばれた law universe、witness rule、signature axis、coverage requirement を与える profile であり、AAT そのものではない。
- ArchSig は ArchMap と interpretation profile から `archsig-analysis-packet-v0` を作る AAT structural analysis layer である。Lean 証明器ではない。
- FieldSig は ArchSig analysis packet と workflow evidence を SFT 側の evolution measurement / governance input として読む。raw ArchMap を forecast truth として読まない。
- Website は docs の複製ではなく、AAT / SFT / ArchSig を公開向けに読むための web-native publication surface である。

## 主要な入口

- `docs/README.md`: 研究 docs 全体の読み方。
- `docs/aat/mathematical_theory/README.md`: AAT 数学本文の入口。
- `docs/aat/proof_obligations.md`: Lean proof obligation と empirical hypothesis の台帳。
- `docs/aat/lean_theorem_index.md`: Lean 定義・定理索引。
- `docs/sft/software_field_theory.md`: SFT 本文。
- `docs/sft/aat_interface.md`: AAT / SFT 境界。
- `docs/tool/README.md`: ArchMap / LawPolicy / ArchSig / FieldSig の現行 tooling 境界。
- `docs/website/README.md`: website の運用メモ。

## よく使う検証

変更範囲に応じて必要な検証を選ぶ。迷う場合は広めに実行する。

```bash
lake build
cargo test --manifest-path tools/archsig/Cargo.toml
cargo test --manifest-path tools/fieldsig/Cargo.toml
git diff --check
rg -nP "[\x{200B}-\x{200F}\x{202A}-\x{202E}\x{2066}-\x{2069}]" <changed-files>
```

ArchSig の現行一次 workflow は `analyze` である。

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- analyze \
  --archmap tools/archsig/tests/fixtures/minimal/archmap.json \
  --law-policy tools/archsig/tests/fixtures/minimal/law_policy.json \
  --out-dir .lake/archsig-analyze
```

website は no-build static stack として扱う。directory route、asset path、`sitemap.xml`、`robots.txt` を確認する場合は local server で preview する。

```bash
python3 -m http.server 0 --directory website
```

Codex から Playwright を実行する場合、macOS のブラウザ起動権限により通常の sandbox 内実行で Chromium が固まることがある。必要に応じて sandbox 外実行を使う。

## PR 前の確認

- Lean 変更を含む場合は `lake build` を実行する。
- ArchSig 変更を含む場合は `cargo test --manifest-path tools/archsig/Cargo.toml` を実行する。
- FieldSig 変更を含む場合は `cargo test --manifest-path tools/fieldsig/Cargo.toml` を実行する。
- Website 変更を含む場合は Playwright などで主要ページの title、link、asset path、layout を確認する。
- docs-only 変更でも Lean status、tool schema、website copy への影響を確認する。
- PR 前に `git diff --check` と hidden / bidirectional Unicode scan を実行する。
- GitHub PR 作成後は `gh pr checks --watch` などで CI を確認する。
