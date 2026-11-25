# docs 読み方

このディレクトリは、AAT の数学理論、AAT / SFT インタフェース、SFT の場の理論、
Lean 形式化の定義・定理、ツールと実証プロトコルに関する文書を分けて管理する場所である。
公開 website の本文・読者導線・ランディングページ向けの説明は `website/` 側で独立に管理し、
website 側の文章はここの研究上の主張規律を参照する。

文書のステートレス性と作業記録の置き場は
[Workflow guideline「ドキュメントをステートレスに保つ規則」](workflow/guideline.md#ドキュメントをステートレスに保つ規則)に従う。

## 文書階層と拘束力

このリポジトリの文書は、次の Tier 順に優先度と拘束力を持つ。

1. **Tier 1: 根本資料**
   - [研究の全体目標](research_goal.md)
   - [代数幾何的 AAT 数学本文](aat/algebraic_geometric_theory/README.md)
   - リポジトリが扱う根本の目標と数学的主張を定める。
2. **Tier 2: 領域基準**
   - [Workflow guideline](workflow/guideline.md)（横断作業規律の基準）
   - [語彙ルール](workflow/vocabulary.md)（語彙の基準）
   - [PRD guideline](prd/guideline.md)（PRD のライフサイクル基準）
   - [AAT / Lean guideline](aat/guideline.md)
   - [SFT guideline](sft/guideline.md)
   - [Tooling guideline](tool/guideline.md)
   - [Website guideline](website/guideline.md)
   - [Paper guideline](paper/guideline.md)
   - [ブログ執筆ガイドライン](outreach/guideline.md)
   - Tier 1 に従って、領域ごとの編集規律・運用規律・現行基準を定める。
3. **Tier 3: 作業用文書**
   - `docs/prd/` の PRD 本文など（`docs/prd/guideline.md` は Tier 2）
   - 実装・検証のための一時的な作業仕様であり、恒久仕様の基準にはしない。役目を終えた文書は削除する。
4. **Tier 4: メモ**
   - `docs/note/` など
   - 拘束力を持たないメモ書きであり、恒久仕様の根拠にはしない。

下位 Tier の文書は上位 Tier の内容に従う。Tier 間の恒久的な参照は、下位 Tier から上位 Tier への方向だけを許可する。
上位 Tier の文書が下位 Tier の文書を参照してはならず、Tier 1 の数学本文から Tier 3 の PRD を参照することも禁止する。
特に Tier 3 以下の文書を、Tier 1 または Tier 2 の規律・仕様の代わりとして扱ってはならない。

## 文書構成のメタ規律

エージェント向けの作業文書に適用する。

- 文書は3層で構成する。**入口**（AGENTS.md）、**規律の基準**（各ガイドライン）、
  **実行手順**（`.codex/skills` の SKILL と `_shared` の共有定義）。
- 各必須規則（hard rule）の記述はちょうど1箇所に置く。他の文書や SKILL はリンクで参照し、
  言い換えて再掲しない。
- SKILL には手順・判断基準・入出力の条件だけを置く。作業規律の本文は参照先のガイドラインを読む。

## 更新ルール

- **Tier 1** の文書を更新するには、人間の明示的な編集指示、実装者とは別の LLM モデルによる PR 経由の敵対レビュー、人間の判断によるマージを必要とする（詳細は [Workflow guideline](workflow/guideline.md#保護対象3条件) および [レビュー体制](workflow/guideline.md#レビュー体制) を参照）。
- **Tier 2** の文書を更新するには、人間の明示的な編集指示を必要とする。
- **Tier 3 以下** の文書には、共通の更新ルールを定めない。ただし、実装中の PRD など、個別の作業規律が定められている文書はその規律に従う。

主要な理論本文は次の 3 文書である。

1. [代数幾何的 AAT 数学本文](aat/algebraic_geometric_theory/README.md)
2. [AAT / SFT Interface](sft/aat_interface.md)
3. [ソフトウェアの場の理論](sft/software_field_theory.md)

## 初めて読む順序

1. [研究の全体目標](research_goal.md)
2. [代数幾何的 AAT 数学本文](aat/algebraic_geometric_theory/README.md)
3. [AAT / SFT Interface](sft/aat_interface.md)
4. [ソフトウェアの場の理論](sft/software_field_theory.md)
5. [Lean 形式化](../Formal/)
6. [AAT Tooling Documentation](tool/README.md)
7. 必要に応じて [AAT directory guide](aat/README.md), [SFT directory guide](sft/README.md)

## 全体文書

- [研究の全体目標](research_goal.md): 研究の全体目標。現在の姿ではなく、目指す姿を書く。理論はこの目標に追いつくように進め、研究の全体目標を現在の理論に合わせて弱めることはしない。
- [代数幾何的 AAT 数学本文](aat/algebraic_geometric_theory/README.md): 全7部21章と付録A–E。Atom・Lawから意味の対象と射を定め、係数的実現、条件付き変更、descentと修復、輸送と診断、観測と再構成を扱う。
- [AAT / SFT Interface](sft/aat_interface.md): SFT が AAT から借りる概念と、片方向依存のインタフェースを整理する。
- [ソフトウェアの場の理論](sft/software_field_theory.md): PRD、仕様書、Issue、PR、レビュー、CI、組織、AI、ライフサイクルを力・場・軌道・制御として整理する。
- [Lean 形式化](../Formal/): 現在 Lean に実装されている定義・定理のソース。
- [PRD](prd/): 実装・検証中の一時的な PRD を格納する。PRD の責務、参照禁止、完了後削除の規律は [PRD guideline](prd/guideline.md) に従う。
- [AAT directory guide](aat/README.md): AAT 配下の補助文書の読み方。
- [SFT directory guide](sft/README.md): SFT 配下の補助文書の読み方。
- [Website operations](website/README.md): 公開されない website 運用メモ、ルート索引、設計文書。

外部記事、翻訳、記事用素材は研究 docs ではなく、リポジトリ直下の
[`outreach/`](../outreach/README.md) で管理する。公開 website の `/outreach/` ルートは
`website/src/outreach/` が管理する。

## 層の分担

```text
AAT gives algebraic-geometric architecture.
ArchSig measures selected evidence.
SFT predicts trajectories.
AI proposes operations.
Review / CI controls transitions.
```

| 層 | 役割 | 主な文書 |
| --- | --- | --- |
| AAT | Atom 公理系から生成される architecture object を、AAT site、sheaf、law algebra、obstruction ideal sheaf、lawful locus、architecture scheme、Čech descent へ持ち上げる代数幾何的・形式的・証明可能な核。 | `docs/aat/algebraic_geometric_theory/README.md` |
| AAT / SFT Interface | AAT から SFT への片方向依存と主張範囲の規律。 | `docs/sft/aat_interface.md` |
| ArchSig | 共通の Atom 定義・Law・ArchMap から対象・操作・対応・局所構造・診断・修復候補を計算する Rust ツール基盤。 | `docs/tool/` |
| SFT | 大域的・力学的・予測的・制御的な上位理論。 | `docs/sft/software_field_theory.md` |
| AI-driven Development | SFT の予測と AAT の定理の仮定の中で変更操作を生成する制御対象。 | `docs/sft/software_field_theory.md`, tooling / AIR docs |

Lean で証明済みの構造的事実、定義のみの概念、将来の証明義務、実証仮説は混同しない。

## Lean 形式化

- [Lean 形式化](../Formal/): 実装済み Lean API のソース。

## Tooling

- [AAT Tooling Documentation](tool/README.md): ArchSig v0.6.0 の製品コンセプト・I/O 仕様・実装入口、および ArchView / FieldSig のツール側総合入口。

## Reports

- [実験報告の基準文書](reports/README.md): 外部文書（論文・記事）から引用する前提で、数値・結論・
  主張範囲・証拠一式を固定した実験報告。`docs/note/`（探索メモ）と区別する。
  現行: [train-ticket ドッグフーディング系列](reports/train_ticket_dogfooding/README.md)。

## Website

- [Website operations](website/README.md): `website/` 公開ディレクトリには置かない運用メモ、ルート索引、設計文書、sitemap 方針。

## 編集ガイドライン

- [Workflow guideline](workflow/guideline.md): 言語、エージェントの役割分担、Issue 運用、ブランチ・PR、保護対象、CI、完了レビューの判定範囲、レビュー体制、PR 前の共通確認の横断規律。
- [PRD guideline](prd/guideline.md): PRD の責務、参照禁止、完了後削除の規律。
- [AAT / Lean guideline](aat/guideline.md): `Formal/AG`、AAT 数学本文、Lean の状態管理、証明義務の編集方針。
- [SFT guideline](sft/guideline.md): SFT 本文、AAT / SFT インタフェース、予測・ガバナンスの主張範囲に関する編集方針。
- [Tooling guideline](tool/guideline.md): ArchSig をはじめとするツールの作り方の規律。
- [Website guideline](website/guideline.md): Cloudflare Pages 公開面、ルート、トーン、アセットパス、sitemap の編集方針。
- [Paper guideline](paper/guideline.md): 論文の執筆、品質基準、検証、投稿・公開。
- [ブログ執筆ガイドライン](outreach/guideline.md): 研究・実務・思想記事の執筆と読者向け品質のレビュー基準。
