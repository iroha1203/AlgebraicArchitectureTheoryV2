# docs 読み方

このディレクトリは、AAT の数学理論、AAT / SFT interface、SFT の場の理論、
Lean 形式化 status、tooling / empirical protocol を分けて管理する。
公開 website の本文、読者導線、landing page 向け説明は、この研究 docs の責務ではない。
website 側の説明は、ここに置いた研究上の claim discipline を参照してよいが、docs を website copy の
source of truth として扱わない。

## 文書階層と拘束力

このリポジトリの文書は、次のTier順に権威と拘束力を持つ。

1. **Tier 1: 根本資料**
   - [研究の全体目標](research_goal.md)
   - [代数幾何的 AAT 数学本文](aat/algebraic_geometric_theory/README.md)
   - リポジトリが扱う根本の目標と数学的主張を定める。
2. **Tier 2: 領域基準**
   - [PRD guideline](prd/guideline.md)（PRD lifecycleの領域基準）
   - [AAT / Lean guideline](aat/guideline.md)
   - [SFT guideline](sft/guideline.md)
   - [Tooling guideline](tool/guideline.md)
   - [Website guideline](website/guideline.md)
   - Tier 1に従って、領域ごとの編集規律・運用規律・現行基準を定める。
3. **Tier 3: 作業用文書**
   - `docs/prd/` のPRD本文など（`docs/prd/guideline.md` はTier 2）
   - 実装・検証のための一時的な作業契約であり、恒久仕様のsource of truthではない。完了後は `docs/archive/` に移す。
4. **Tier 4: メモ**
   - `docs/note/` など
   - 拘束力を持たないメモ書きであり、恒久仕様の根拠にはしない。
5. **Tier 5: archive**
   - `docs/archive/` など
   - 過去資料の保管場所であり、現行source of truthとして扱わない。将来的に完全削除する。

下位Tierの文書は上位Tierの内容に従う。Tier間の恒久的な参照は、下位Tierから上位Tierへの方向だけを許可する。
上位Tierの文書が下位Tierの文書を参照してはならず、Tier 1の数学本文からTier 3のPRDを参照することも禁止する。
特にTier 3以下の文書を、Tier 1またはTier 2の規律・仕様の代替として扱ってはならない。

## 更新ルール

- **Tier 1** の文書を更新するには、人間の明示的な編集指示、実装者とは別のLLMモデルによる敵対レビュー、人間の判断によるマージを必要とする。
- **Tier 2** の文書を更新するには、人間の明示的な編集指示を必要とする。
- **Tier 3以下** の文書には、共通の更新ルールを定めない。ただし、実装中のPRDなど、個別の作業規律が定められている文書はその規律に従う。

第一級本文は次の 3 文書である。

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

- [研究の全体目標](research_goal.md): AAT / SFT / ArchSig / AI-driven Development の全体像を示す入口文書。
- [代数幾何的 AAT 数学本文](aat/algebraic_geometric_theory/README.md): AAT 数学本文の正典。Atom 公理系から architecture object を構成し、AAT site、sheaf、ringed topos、law algebra、obstruction ideal sheaf、lawful locus、architecture scheme、Čech descent、derived / stacky geometry、measurement、evolution geometry へ進む。
- [AAT / SFT Interface](sft/aat_interface.md): SFT が AAT から借りる概念と、片方向依存の interface を整理する。
- [ソフトウェアの場の理論](sft/software_field_theory.md): PRD / Spec / Issue / PR / Review / CI / organization / AI / lifecycle を force, field, trajectory, control として整理する。
- [Lean 形式化](../Formal/): 現在Leanに存在する定義・定理のsource。
- [PRD](prd/): 実装・検証中の一時的なPRDを格納する。PRDの責務、参照禁止、完了後archiveの規律は [PRD guideline](prd/guideline.md) を正本とする。
- [AAT directory guide](aat/README.md): AAT 配下の補助文書の読み方。
- [SFT directory guide](sft/README.md): SFT 配下の補助文書の読み方。
- [Website operations](website/README.md): 公開されない website 運用メモ、route 索引、設計文書。

外部記事、翻訳、記事用素材は研究 docs ではなく、リポジトリ直下の
[`outreach/`](../outreach/README.md) で管理する。公開 website の `/outreach/` route は
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
| AAT / SFT Interface | AAT から SFT への片方向依存と claim discipline。 | `docs/sft/aat_interface.md` |
| ArchSig | supplied evidence と MeasurementProfile から bounded diagnostic / measurement artifact を作り、SFT 的予測・制御へ渡す計測層。 | `docs/tool/` |
| SFT | 大域的・力学的・予測的・制御的な上位理論。 | `docs/sft/software_field_theory.md` |
| AI-driven Development | SFT の forecast と AAT の theorem assumptions の中で operation を生成する制御対象。 | `docs/sft/software_field_theory.md`, tooling / AIR docs |

Lean で証明済みの構造的事実、定義のみの概念、将来の証明義務、実証仮説は混同しない。

## Lean 形式化

- [Lean 形式化](../Formal/): 実装済みLean APIのsource。

## Tooling

- [AAT Tooling Documentation](tool/README.md): AIR、claim discipline、signature artifact、report、extractor、workflow、schema compatibility の tool 側総合入口。

## Reports

- [実験報告の正本](reports/README.md): 外部文書(論文・記事)から引用する前提で数値・結論・
  claim boundary・証拠束を凍結した実験報告。`docs/note/`(探索メモ)と区別する。
  現行: [train-ticket ドッグフーディング系列](reports/train_ticket_dogfooding/README.md)。

## Website

- [Website operations](website/README.md): `website/` 公開ディレクトリには置かない運用メモ、route 索引、設計文書、sitemap 方針。

## 編集ガイドライン

- [PRD guideline](prd/guideline.md): PRDの責務、参照禁止、完了後archiveの規律。
- [AAT / Lean guideline](aat/guideline.md): `Formal/AG` / `Formal/Arch`、AAT 数学本文、Lean status、proof obligation の編集方針。
- [SFT guideline](sft/guideline.md): SFT 本文、AAT / SFT interface、forecast / governance claim boundary の編集方針。
- [Tooling guideline](tool/guideline.md): ArchMap、LawPolicy、ArchSig、FieldSig、schema、CLI、fixture の編集方針。
- [Website guideline](website/guideline.md): Cloudflare Pages 公開面、route、tone、asset path、sitemap の編集方針。
