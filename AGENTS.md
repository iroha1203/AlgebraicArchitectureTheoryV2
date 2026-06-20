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
- AAT / Lean / ArchSig の境界は作業前に必ず分ける。
  - 現行 AAT は代数幾何的アーキテクチャ論である。Atom は primitive architectural fact
    として公理化され、Atom family / configuration から architecture object が生成される。
    その上に architecture geometry、AAT site、sheaf、ringed AAT topos、law algebra、
    obstruction ideal sheaf、lawful locus、architecture scheme、Čech descent、
    derived law geometry が立つ。
  - AAT 自体に source observation、measurement、tooling validation の境界を持ち込まない。
    測定境界は ArchMap / ArchSig / FieldSig 側の artifact contract として扱う。
  - Lean 形式化は神様の視点ではない。語れる命題だけを形式化し、全 runtime、全 semantic universe、
    全未来予測のような証明対象を勝手にスコープへ入れない。
  - ArchSig は Rust tooling であり Lean 証明器ではない。Rust と Lean の対応を要求しない。
    ArchSig は `ArchMap + LawPolicy + evidence contract` に相対化して、選ばれた語彙内の肯定的な
    diagnostic conclusion を出す。
- ウィトゲンシュタイン的責務境界:
  ArchSig は、与えられた `ArchMap + LawPolicy + evidence contract` から語れることだけを語る。
  語れないことには沈黙する。ArchMap の観測・Atom mapping・evidence の正しさは ArchMap author の責務であり、
  law / axis / witness / coverage の選択は LawPolicy author の責務である。ArchSig は入力 contract を補完・推測・拡張せず、
  その範囲内で一貫した bounded diagnostic conclusion を出す。
- 完了レビューや残タスク整理では、対象 Issue / PRD / 計画書 / acceptance test が実際に要求している
  concrete condition だけを判定する。現実コード全体、意味宇宙全体、未来予測全体のような
  無制限 claim を勝手に残タスク化しない。
- claim boundary は、現在の主張を正確に保つための制約として扱う。ユーザーが求めていない限り、
  「証明できない巨大 claim」や一般的限界を列挙して作業計画の中心にしない。
- 語り得ない領域は、残タスクや失敗ではなく沈黙として扱う。必要な場合だけ、結論の近くに
  最小限の boundary として書く。ArchSig / website / report では `SAFE_WITHIN_POLICY`、
  `NO_SELECTED_OBSTRUCTION`、`ACCEPTABLE_UNDER_EVIDENCE_CONTRACT` のような肯定的結論を中心にし、
  外側の未観測領域を長い `non-conclusion` 一覧として主役化しない。
- 禁止: AAT の完了レビューで source extraction / ArchMap observation / tooling validation の完全性を
  「未完了部分」「非主張」「残タスク」「証明不能な限界」として持ち出さない。
  source-observation layer の性質は AAT の内側の claim ではない。必要な場合は tooling / SFT 側の
  具体的な artifact、fixture、schema、validator、Issue acceptance として別に扱う。
- AAT / SFT の数学本文は根幹文書である。ユーザーがはっきりと明示的に本文編集を指示した場合のみ、
  `docs/aat/algebraic_geometric_theory/`、`docs/sft/software_field_theory.md`、
  `docs/sft/aat_interface.md` を更新してよい。
  - 例: 「数学本文を編集して」「`docs/aat/algebraic_geometric_theory/...` を修正して」。
  - 「読み直して」「理解して」「レビューして」「差分を確認して」「常識の観点で見て」
    「PR 作成して」は本文編集の許可ではない。
  - 本文に問題を見つけても、明示的な本文編集指示がない限り、提案、PR コメント、Issue、
    周辺 docs / 台帳の修正として扱い、数学本文は read-only とする。
- 実装作業は `main` を最新化してから専用ブランチを切る。ブランチ名は Issue 番号または作業内容が分かる名前にする。
- PR 本文には対象 Issue を `Closes #N` 形式で明記し、`.github/pull_request_template.md` に沿って書く。
- 既存の未コミット変更はユーザーの変更として扱い、勝手に戻さない。
- `git reset --hard` や `git checkout --` のような破壊的操作は、明示的な依頼なしに実行しない。
- `.lake` は Lake の build / dependency cache 専用として扱い、検証出力、PR / Issue 下書き、一時 JSON などの temp 置き場に使わない。一時出力は `.tmp/` または `/private/tmp` などに置く。

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

## 基礎概念

- 現行 AAT は、Atom 公理系から Atom family、configuration、architecture object を構成し、
  そこに law universe、coverage topology、係数環 / 係数 sheaf を載せて architecture geometry、
  site、sheaf、law algebra、obstruction ideal sheaf、lawful locus、Čech cohomology、
  derived / stacky geometry として読む純粋数学理論である。
- Atom、law、obstruction、flatness、signature は代数幾何版の基礎データや局所 presentation
  として現れる。外部設計パターン語彙へ潰して説明しない。
- source extraction / ArchMap observation / tooling validation は、AAT 入力を提示・検査する
  前段または後段 surface であり、AAT の完了条件や残タスクではない。
- Lean で証明済みの主張、定義のみの概念、将来の証明義務、実証仮説は混同しない。
- SFT は artifact、practice、AI、review、CI、operational feedback が software evolution の reachable future をどう変えるかを扱う。
- ArchMap は source-grounded observation artifact であり、AAT site / measurement profile へ渡す
  有限 evidence surface を記録する。AAT の source of truth ではない。
- LawPolicy / MeasurementProfile は選ばれた policy、law reading、cover、係数、witness family、
  measurement regime を与える artifact contract であり、AAT そのものではない。
- ArchSig は Rust tooling であり、ArchMap、LawPolicy、MeasurementProfile、evidence contract から
  bounded diagnostic / measurement artifact を出す。Lean 証明器ではない。
- ArchView は ArchSig が出力した viewer data / summary / manifest を読む可視化レイヤーである。
  新しい structural verdict を作らず、測定済み artifact の AAT geometry projection として表示する。
  release bundle では `archview/archview.html` と README を同梱する。
- ウィトゲンシュタイン的責務境界では、ArchSig は入力された世界の中で語れることだけを出力し、語れない領域を診断・安全・失敗として作らない。
- FieldSig は ArchSig analysis packet と workflow evidence を SFT 側の evolution measurement / governance input として読む。raw ArchMap を forecast truth として読まない。
- Website は docs の複製ではなく、AAT / SFT / ArchSig を公開向けに読むための web-native publication surface である。

## 主要な入口

- `PHILOSOPHY.md`: プロジェクトの核となる思想と問い(なぜ)。旧 VISION.md を統合。
  原理を述べるのが役割で、作業規律としての規範効力はこの AGENTS.md を正とし、両者が食い違う場合は AGENTS.md に従う。
  数学的精密さは AG版本文(`docs/aat/algebraic_geometric_theory/`)が担う。
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
  --archmap tools/archsig/tests/fixtures/minimal/archmap.json \
  --law-policy tools/archsig/tests/fixtures/minimal/law_policy.json \
  --out-dir .tmp/archsig-analyze
```

website は no-build static stack として扱う。directory route、asset path、`sitemap.xml`、`robots.txt` を確認する場合は local server で preview する。

```bash
python3 -m http.server 0 --directory website
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
