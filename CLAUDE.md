# CLAUDE.md

Claude Code がこのモノレポで作業するための入口。
エージェント共通の正式な作業ガイドは [AGENTS.md](AGENTS.md) であり、両者が食い違う場合は AGENTS.md を正とする。
領域別の詳細な編集方針は各 `guideline.md` に分かれている。

- [AAT / Lean guideline](docs/aat/guideline.md)
- [SFT guideline](docs/sft/guideline.md)
- [Tooling guideline](docs/tool/guideline.md)
- [Website guideline](docs/website/guideline.md)

## Claude の役割分担

このリポジトリの開発パイプラインは役割分担制で動いている。

- **Claude**: PRD 作成、フルレビュー、設計考察ノート。大きい作業の依頼を受けたら、まず PRD 化を提案する。
- **Codex**: PRD を受けた prd-loop による実装。実装タスクを Claude が抱え込まない。
- **ユーザー**: 受け入れテストと最終判断。

PRD を書くときは冒頭に「## 問い」節を置き、その問いを採否の判定規律として機能させる。
候補(問いの立て方、スコープの切り方)は複数提示してユーザーに選んでもらう。

## 基本運用

- ユーザーへの応答、コミットメッセージ、PR / Issue のタイトルと本文は日本語で書く。
  Lean 識別子、ファイル名、コマンド名、定理名、既存の英語技術用語はそのままでよい。
- 作業は原則 GitHub Issue 起点。次タスク選定は `priority:blocking`, `status:ready`, milestone の依存順を優先する。
- 個人開発リポジトリであり、常に最小差分を選ぶ必要はない。目的に自然に必要な設計・実装・docs・tests・website surface まで広げてよい。
  ただし、無関係な既存変更の巻き戻し、claim boundary を越える主張、根拠のない互換性維持、不要な抽象化は避ける。
- 実装は `main` を最新化してから専用ブランチを切る。ブランチ名は Issue 番号か作業内容が分かる名前にする。
- PR 本文は `.github/pull_request_template.md` に沿い、`Closes #N` で対象 Issue を明記する。PR 作成後は `gh pr checks --watch` で CI を確認する。
- 既存の未コミット変更はユーザーの変更として扱い、勝手に戻さない。`git reset --hard` / `git checkout --` などの破壊的操作は明示的な依頼なしに実行しない。
- `.lake` は Lake の build / dependency cache 専用。一時出力は `.tmp/` または `/private/tmp` に置く。
- **保護ファイル**: `docs/aat/algebraic_geometric_theory/`、`docs/sft/software_field_theory.md`、`docs/sft/aat_interface.md` の更新は3条件(人間の明示的な編集指示・実装者以外の LLM によるレビュー・人間による差分確認と merge)がすべて揃う場合に限る。正本は AGENTS.md「作業規律」。
- **レビュー体制**: AGENTS.md の「レビュー体制」を正とする(分野別敵対レビュー SKILL、観点の正本は `.codex/skills/_shared/refutation-checklist.md`、Lean 変更は1行でも math-lean-review 4並列)。

## 境界規律(最重要)

AAT / Lean / ArchSig の責務境界を作業前に必ず分ける。

- **AAT** は Atom を公理とする純粋数学理論。source observation、measurement、tooling validation の境界を AAT 内部に持ち込まない。測定境界は ArchMap / ArchSig / FieldSig 側の artifact contract として扱う。
- **Lean 形式化**は神様の視点ではない。語れる命題だけを形式化し、全 runtime・全 semantic universe・全未来予測のような証明対象を勝手にスコープへ入れない。
- **ArchSig** は `ArchMap + LawPolicy + evidence contract` から選ばれた語彙内の肯定的な diagnostic conclusion を計算する Rust tooling。結論の相対性は入力契約に由来する帰結であり、identity を「Lean 証明器ではない」のような否定形で書かない。Rust と Lean の対応は要求しない。
- **ウィトゲンシュタイン的責務境界**: ArchSig は与えられた入力 contract から語れることだけを語り、語れないことには沈黙する。入力 contract を補完・推測・拡張しない。語り得ない領域は残タスクや失敗ではなく沈黙として扱い、必要な場合だけ結論の近くに最小限の boundary として書く。
- 完了レビューや残タスク整理では、対象 Issue / PRD / acceptance test が実際に要求している concrete condition だけを判定する。無制限 claim(現実コード全体、意味宇宙全体、未来予測)を勝手に残タスク化しない。
- **禁止**: AAT の完了レビューで source extraction / ArchMap observation / tooling validation の完全性を「未完了部分」「残タスク」「証明不能な限界」として持ち出さない。必要なら tooling / SFT 側の具体的な artifact・fixture・schema・validator・Issue acceptance として別に扱う。
- 出力では `SAFE_WITHIN_POLICY` のような肯定的結論を中心にし、未観測領域の長い non-conclusion 一覧を主役化しない。

## モノレポの地図

| 領域 | 場所 | 役割 |
| --- | --- | --- |
| Lean / AAT | `Formal/AG`, `Formal/Arch`, `Formal.lean` | AAT / SFT の形式化(定義・定理・例) |
| AAT docs | `docs/aat` | AAT 数学本文、Lean status、proof obligation |
| SFT docs | `docs/sft` | Software Field Theory と AAT / SFT interface |
| Tooling | `tools/archsig`, `tools/fieldsig`, `docs/tool` | ArchMap / LawPolicy / ArchSig / FieldSig の CLI・schema・workflow |
| Website | `website`, `docs/website` | Cloudflare Pages 向け no-build static surface |
| Reports | `docs/reports` | 実験報告の正本(論文引用用。証拠束+再現手順付き、note と区別) |
| 研究プログラム | `research/`, `research/lean/ResearchLean/` | 研究 GOAL の下で候補探索 → 三審判 → Lean 検証 / 証拠固定 → SCORE 監査 → フェーズ区切り判定を回すループ engine と検証 sandbox |
| Archive | `docs/archive` | 過去文書の退避先。現行 source of truth ではない |

主要な入口:

- `docs/README.md` — 研究 docs 全体の読み方
- `docs/aat/algebraic_geometric_theory/README.md` — 代数幾何的 AAT 数学本文の入口
- `Formal/` — Lean 形式化の実体
- `research/goals/` / GitHub Issues — 作業状態と未解決課題
- `docs/tool/README.md` — 現行 tooling 境界
- `research/README.md` — ループ研究 engine の入口(`$research-loop`)

## 検証コマンド

変更範囲に応じて選ぶ。迷う場合は広めに実行する。

```bash
lake env lean <target-file>                          # 単一ファイルの focused check
lake build <module>                                  # 変更範囲に応じた targeted build
# 本体のroot全体のフル lake build は PR 作成後の CI で確認
cargo test --manifest-path tools/archsig/Cargo.toml   # ArchSig 変更
cargo test --manifest-path tools/fieldsig/Cargo.toml  # FieldSig 変更
git diff --check                                      # PR 前に常に
rg -nP "[\x{200B}-\x{200F}\x{202A}-\x{202E}\x{2066}-\x{2069}]" <changed-files>  # hidden Unicode scan
```

ArchSig の現行一次 workflow は `analyze`:

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- analyze \
  --archmap tools/archsig/tests/fixtures/ag_measurement/archmap_v2.json \
  --law-policy tools/archsig/tests/fixtures/ag_measurement/law_policy_ag.json \
  --measurement-profile tools/archsig/tests/fixtures/ag_measurement/measurement_profile_ag.json \
  --law-surface tools/archsig/tests/fixtures/ag_measurement/law_surface_ag_v052.json \
  --out-dir .tmp/archsig-analyze
```

website の preview(Eleventy。初回は `cd website && npm install`):

```bash
cd website && npx @11ty/eleventy --serve
```

docs-only 変更でも Lean status、tool schema、website copy への影響を確認する。
