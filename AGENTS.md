# リポジトリ作業ガイド

このファイルは、このモノレポで Codex が迷わず作業を始めるための入口である。
詳細な編集方針は各領域の `guideline.md` に分ける。

- [AAT / Lean guideline](docs/aat/guideline.md)
- [SFT guideline](docs/sft/guideline.md)
- [Tooling guideline](docs/tool/guideline.md)
- [Website guideline](docs/website/guideline.md)

## 基礎概念

- AAT は、Atom を primitive architectural fact として公理化し、law を方程式系として重ねる
  代数幾何的アーキテクチャ論である。Atom family から生成される architecture object を、
  lawful locus、obstruction、sheaf、cohomology、derived / stacky structure として読む。
- AAT は比喩ではなく、Atom を基礎単位としてアーキテクチャを本物の代数幾何の対象にする。
  そのため、特定のプログラミング言語、フレームワーク、ADL、実装形態に依存せず、
  言語を越えた architectural fact を同じ数学的基盤で扱える。
- AAT は本気で代数幾何を行う。Atom を土台に、site、Grothendieck topology、sheaf、
  ringed topos、scheme、Čech cohomology、derived / stacky structure などの本物の
  代数幾何概念へ接続していく。Lean 形式化でも、AAT 専用の仮置き wrapper や
  名前だけの analogue に留めず、定義、comparison map、同値、boundary theorem を通じて
  既存の数学的構造へ接続する方向を優先する。
- AAT の強みは、アーキテクチャを geometry として扱い、局所性、貼り合わせ、obstruction、
  変形、高次構造、repair 可能性を site / sheaf / law algebra / cohomology の同じ土台で
  分析できる点にある。既存の設計パターンも、経験則ではなく local model、幾何構造、
  gluing condition、singularity、obstruction、cohomological phenomenon として再解釈できる。
- semantic atom は、静的解析では扱いにくい意味論、責務、補償、不変条件、業務意味、
  side-effect discipline を AAT の対象へ持ち込むための基礎単位である。局所的には整合する
  architectural data、certificate、repair が大域的に貼り合わない問題は、必要に応じて
  `H^1` obstruction などの cohomological obstruction として読む。
- SFT は、artifact、practice、AI、review、CI、operational feedback が software evolution の
  reachable future をどう変えるかを扱う。AAT が構造の幾何を扱い、SFT が実践と進化の場を扱う。
- SFT の強みは、個別の artifact や workflow を、software evolution の reachable future を変える
  場の操作として統一的に読める点にある。
- ArchMap は、選ばれた Atom vocabulary と evidence contract の中で architecture evidence を記録する
  有限 artifact である。
- LawPolicy / MeasurementProfile は、law reading、cover、witness、measurement regime を固定する
  contract である。
- ArchSig は ArchMap と LawPolicy から bounded diagnostic / analysis packet を計算する tooling である。
- ArchSig の強みは、AAT の強力な幾何的理論を tooling 上で活かし、ArchMap と LawPolicy から
  lawful locus、obstruction、coverage、witness を読む高度な architecture analysis を計算できる点にある。
- ArchView は ArchSig の結果を可視化し、FieldSig は analysis packet と workflow evidence を
  SFT 側の evolution measurement / governance input として読む。
- Website は、AAT / SFT / tooling を公開向けに読むための publication surface である。
- Lean status は、証明済みの主張、定義のみの概念、将来の証明義務、実証仮説を区別して読む。

## モノレポの地図

このリポジトリは Lean 形式化、Rust tooling、公開 website、研究 docs が同居する。
同じ語でも領域によって責務が違うため、作業前に対象領域を確認する。

| 領域 | 主な場所 | 役割 | 詳細 |
| --- | --- | --- | --- |
| Lean / AAT | `Formal/AG`, `Formal/Arch`, `Formal.lean`, `Main.lean` | AAT / SFT の形式化、定義、定理、例。 | [AAT guideline](docs/aat/guideline.md) |
| AAT docs | `docs/aat` | AAT 数学本文、Lean status、proof obligation。 | [AAT guideline](docs/aat/guideline.md) |
| SFT docs | `docs/sft` | Software Field Theory と AAT / SFT interface。 | [SFT guideline](docs/sft/guideline.md) |
| Tooling | `tools/archsig`, `tools/archview`, `tools/fieldsig`, `docs/tool` | ArchMap / LawPolicy / ArchSig / ArchView / FieldSig の CLI、schema、visualization、workflow。 | [Tool guideline](docs/tool/guideline.md) |
| Website | `website`, `docs/website` | Cloudflare Pages 向け public reading surface と内部運用メモ。 | [Website guideline](docs/website/guideline.md) |
| 研究プログラム | `research/`, `Formal/AG/Research` | 研究 GOAL の下で候補探索 → 三審判 → Lean 検証 / 証拠固定 → SCORE 監査 → フェーズ区切り判定を回すループ engine と検証 sandbox。 | [research README](research/README.md) |
| Archive | `docs/archive` | 過去文書の退避先。現行 source of truth として扱わない。 | [docs README](docs/README.md) |

## 責務境界

- AAT は Atom と law から立つ純粋理論である。ArchSig は ArchMap と LawPolicy から
  bounded diagnostic を計算する。観測者境界は ArchMap author と evidence contract の責務として
  一括して扱う。
- ウィトゲンシュタイン的責務境界を守る。選ばれた vocabulary、policy、evidence contract から
  語れることだけを語る。語れない領域は、失敗や残タスクではなく沈黙として扱う。
- AAT / Lean theorem の説明・レビューでは、定理が語る選択済み vocabulary、仮定、対象だけを
  肯定形で述べる。ユーザーや対象 artifact が明示していない限り、
  「この定理は実コードベース全体を対象としません」のような外側の否定 claim を付け足さない。
  外側は補足 caveat ではなく沈黙で扱う。

## 作業規律

- ユーザーへの応答、commit message、PR / Issue の title と本文は日本語で書く。
  Lean 識別子、ファイル名、コマンド名、定理名、既存の英語技術用語はそのまま扱う。
- `docs/aat/algebraic_geometric_theory/`、`docs/sft/software_field_theory.md`、
  `docs/sft/aat_interface.md` は、明示的な本文編集タスクの対象になった場合だけ更新する。
- 完了レビューや残タスク整理では、対象 Issue / PRD / 計画書 / acceptance test が要求する
  concrete condition だけを判定する。
- 作業は原則として GitHub Issue 起点で進める。次タスクは `priority:blocking`、`status:ready`、
  milestone の依存順を優先する。
- 目的に対して自然に必要な設計、実装、docs、tests、website surface まで広げてよい。
  ただし、無関係な既存変更の巻き戻し、claim boundary を越える主張、根拠のない互換性維持、
  不要な抽象化は避ける。
- 実装作業は `main` を最新化してから専用ブランチを切る。ブランチ名は Issue 番号または作業内容が
  分かる名前にする。PR 本文には `Closes #N` を明記し、`.github/pull_request_template.md` に沿って書く。
- 既存の未コミット変更はユーザーの変更として扱い、勝手に戻さない。
  `git reset --hard` や `git checkout --` は明示的な依頼なしに実行しない。
- `.lake` は Lake の build / dependency cache 専用とし、一時出力は `.tmp/` または `/private/tmp` に置く。

## 主要な入口

- `PHILOSOPHY.md`: プロジェクトの核となる思想と問い(なぜ)。
- `docs/README.md`: 研究 docs 全体の読み方。
- `docs/aat/algebraic_geometric_theory/README.md`: 代数幾何的 AAT 数学本文の入口。
- `docs/aat/proof_obligations.md`: Lean proof obligation と empirical hypothesis の台帳。
- `docs/aat/lean_theorem_index.md`: Lean 定義・定理索引。
- `docs/sft/software_field_theory.md`: SFT 本文。
- `docs/sft/aat_interface.md`: AAT / SFT 境界。
- `docs/tool/README.md`: ArchMap / LawPolicy / ArchSig / ArchView / FieldSig の現行 tooling 境界。
- `docs/website/README.md`: website の運用メモ。
- `research/README.md`: 研究ループ engine(`$research-loop`)の入口。

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
  --archmap tools/archsig/tests/fixtures/ag_measurement/archmap_v2.json \
  --law-policy tools/archsig/tests/fixtures/ag_measurement/law_policy_ag.json \
  --measurement-profile tools/archsig/tests/fixtures/ag_measurement/measurement_profile_ag.json \
  --out-dir .tmp/archsig-analyze
```

website は Eleventy で authoring し、配信 artifact は純静的とする(詳細は [Website guideline](docs/website/guideline.md))。directory route、asset path、`sitemap.xml`、`robots.txt` を確認する場合は dev server で preview する。

```bash
cd website && npx @11ty/eleventy --serve   # 初回は npm install
```

Codex から Playwright を実行する場合、macOS のブラウザ起動権限により通常の sandbox 内実行で Chromium が固まることがある。必要に応じて sandbox 外実行を使う。

## PR 前の確認

- Lean 変更を含む場合は `lake build` を実行する。
- ArchSig 変更を含む場合は `cargo test --manifest-path tools/archsig/Cargo.toml` を実行する。
- ArchView 変更を含む場合は `tools/archview/archview.html` を local server 経由で確認し、必要に応じて `cargo test --manifest-path tools/archsig/Cargo.toml archview` を実行する。
- FieldSig 変更を含む場合は `cargo test --manifest-path tools/fieldsig/Cargo.toml` を実行する。
- Website 変更を含む場合は Playwright などで主要ページの title、link、asset path、layout を確認する。
- docs-only 変更でも Lean status、tool schema、website copy への影響を確認する。
- PR 前に `git diff --check` と hidden / bidirectional Unicode scan を実行する。
- GitHub PR 作成後は `gh pr checks --watch` などで CI を確認する。
