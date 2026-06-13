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
  - AAT は Atom を公理とする純粋数学理論である。AAT 自体に source observation、measurement、
    tooling validation の境界を持ち込まない。測定境界は ArchMap / ArchSig / FieldSig 側の
    artifact contract として扱う。
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
  「未完了部分」「非主張」「残タスク」「証明不能な限界」として持ち出さない。AAT は Atom を公理とするため、
  source-observation layer の性質は AAT の内側の claim ではない。必要な場合は tooling / SFT 側の
  具体的な artifact、fixture、schema、validator、Issue acceptance として別に扱う。
- AAT / SFT の数学本文は根幹文書である。ユーザーの明示的な指示なしに `docs/aat/mathematical_theory/`、`docs/sft/software_field_theory.md`、`docs/sft/aat_interface.md` を更新しない。
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
| Lean / AAT | `Formal/Arch`, `Formal.lean`, `Main.lean` | AAT / SFT の形式化、定義、定理、例。 | [AAT guideline](docs/aat/guideline.md) |
| AAT docs | `docs/aat` | AAT 数学本文、Lean status、proof obligation。 | [AAT guideline](docs/aat/guideline.md) |
| SFT docs | `docs/sft` | Software Field Theory と AAT / SFT interface。 | [SFT guideline](docs/sft/guideline.md) |
| Tooling | `tools/archsig`, `tools/fieldsig`, `docs/tool` | ArchMap / LawPolicy / ArchSig / FieldSig の CLI、schema、workflow。 | [Tool guideline](docs/tool/guideline.md) |
| Website | `website`, `docs/website` | Cloudflare Pages 向け public reading surface と内部運用メモ。 | [Website guideline](docs/website/guideline.md) |
| Archive | `docs/archive` | 過去文書の退避先。現行 source of truth として扱わない。 | [docs README](docs/README.md) |

## 基礎概念

- AAT は Atom から architecture object、law、obstruction circuit、operation、flatness、path / homotopy、analytic representation を構成する局所代数の核である。
- AAT は Atom を公理的出発点とする純粋理論である。source extraction / ArchMap observation / tooling validation は
  Atom 入力を提示・検査する前段または後段 surface であり、AAT の完了条件や残タスクではない。
- Lean で証明済みの主張、定義のみの概念、将来の証明義務、実証仮説は混同しない。
- SFT は artifact、practice、AI、review、CI、operational feedback が software evolution の reachable future をどう変えるかを扱う。
- ArchMap は source-grounded Atom observation map であり、law-independent な観測を記録する。
- LawPolicy / interpretation profile は選ばれた law universe、witness rule、signature axis、coverage requirement を与える profile であり、AAT そのものではない。
- ArchSig は ArchMap と interpretation profile から `archsig-analysis-packet-v0` を作る AAT structural analysis layer である。Lean 証明器ではない。選ばれた LawPolicy と evidence contract の中で語れることを確かに語り、その外側は証明不能な限界として騒がず沈黙する。
- ウィトゲンシュタイン的責務境界では、ArchSig は入力された世界の中で語れることだけを出力し、語れない領域を診断・安全・失敗として作らない。
- FieldSig は ArchSig analysis packet と workflow evidence を SFT 側の evolution measurement / governance input として読む。raw ArchMap を forecast truth として読まない。
- Website は docs の複製ではなく、AAT / SFT / ArchSig を公開向けに読むための web-native publication surface である。

## 主要な入口

- `VISION.md`: プロジェクト全体の VISION。
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
- FieldSig 変更を含む場合は `cargo test --manifest-path tools/fieldsig/Cargo.toml` を実行する。
- Website 変更を含む場合は Playwright などで主要ページの title、link、asset path、layout を確認する。
- docs-only 変更でも Lean status、tool schema、website copy への影響を確認する。
- PR 前に `git diff --check` と hidden / bidirectional Unicode scan を実行する。
- GitHub PR 作成後は `gh pr checks --watch` などで CI を確認する。
