# docs 読み方

このディレクトリは、AAT の数学理論、AAT / SFT interface、SFT の場の理論、
Lean 形式化 status、tooling / empirical protocol を分けて管理する。
公開 website の本文、読者導線、landing page 向け説明は、この研究 docs の責務ではない。
website 側の説明は、ここに置いた研究上の claim discipline を参照してよいが、docs を website copy の
source of truth として扱わない。

第一級本文は次の 3 文書である。

1. [AAT 数学理論](aat/mathematical_theory/README.md)
2. [AAT / SFT Interface](sft/aat_interface.md)
3. [ソフトウェアの場の理論](sft/software_field_theory.md)

## 初めて読む順序

1. [研究の全体目標](research_goal.md)
2. [AAT 数学理論](aat/mathematical_theory/README.md)
3. 必要に応じて [代数幾何的 AAT 拡張本文](aat/algebraic_geometric_theory/README.md)
4. [AAT / SFT Interface](sft/aat_interface.md)
5. [ソフトウェアの場の理論](sft/software_field_theory.md)
6. [証明義務と実証仮説](aat/proof_obligations.md)
7. [Lean 定義・定理索引](aat/lean_theorem_index.md)
8. [AAT Tooling Documentation](tool/README.md)
9. 必要に応じて [AAT directory guide](aat/README.md), [SFT directory guide](sft/README.md)

## 全体文書

- [研究の全体目標](research_goal.md): AAT / SFT / ArchSig / AI-driven Development の全体像を示す入口文書。
- [AAT 数学理論](aat/mathematical_theory/README.md): Atom から `ArchitectureObject`, law, obstruction circuit, operation, flatness, path, homotopy, analytic representation, distance / measure を構成する。
- [代数幾何的 AAT 拡張本文](aat/algebraic_geometric_theory/README.md): AAT を site、ringed topos、affine chart、scheme、derived / stacky geometry として読む拡張本文。Lean 形式化との対応は Lean 索引と証明義務で確認する。
- [AAT / SFT Interface](sft/aat_interface.md): SFT が AAT から借りる概念と、片方向依存の interface を整理する。
- [ソフトウェアの場の理論](sft/software_field_theory.md): PRD / Spec / Issue / PR / Review / CI / organization / AI / lifecycle を force, field, trajectory, control として整理する。
- [証明義務と実証仮説](aat/proof_obligations.md): theorem assumption、未解決課題、empirical hypothesis の台帳。
- [Lean 定義・定理索引](aat/lean_theorem_index.md): 現在 Lean に存在する主要な定義・定理の索引。
- [AAT directory guide](aat/README.md): AAT 配下の補助文書の読み方。
- [SFT directory guide](sft/README.md): SFT 配下の補助文書の読み方。
- [Website operations](website/README.md): 公開されない website 運用メモ、route 索引、設計文書。
- [AAT / Lean guideline](aat/guideline.md): AAT docs と Lean 形式化の編集方針。
- [SFT guideline](sft/guideline.md): SFT docs と AAT / SFT 境界の編集方針。
- [Tooling guideline](tool/guideline.md): ArchMap / LawPolicy / ArchSig / FieldSig の編集方針。
- [Website guideline](website/guideline.md): website public surface と内部運用メモの編集方針。

## 層の分担

```text
AAT gives laws.
ArchSig measures state.
SFT predicts trajectories.
AI proposes operations.
Review / CI controls transitions.
```

| 層 | 役割 | 主な文書 |
| --- | --- | --- |
| AAT | Atom から立ち上がる局所的・代数的・形式的・証明可能な核。 | `docs/aat/mathematical_theory/README.md`, `docs/aat/algebraic_geometric_theory/README.md` |
| AAT / SFT Interface | AAT から SFT への片方向依存と claim discipline。 | `docs/sft/aat_interface.md` |
| ArchSig | AAT 的観測量を抽出し、SFT 的予測・制御に渡す計測層。 | `docs/tool/` |
| SFT | 大域的・力学的・予測的・制御的な上位理論。 | `docs/sft/software_field_theory.md` |
| AI-driven Development | SFT の forecast と AAT の theorem assumptions の中で operation を生成する制御対象。 | `docs/sft/software_field_theory.md`, tooling / AIR docs |

Lean で証明済みの構造的事実、定義のみの概念、将来の証明義務、実証仮説は混同しない。

## Lean 形式化

- [Lean 定義・定理索引](aat/lean_theorem_index.md): 実装済み Lean API の入口。
- [証明義務と実証仮説](aat/proof_obligations.md): theorem assumptions、未解決課題、empirical hypothesis の台帳。

## Tooling

- [AAT Tooling Documentation](tool/README.md): AIR、claim discipline、signature artifact、report、extractor、workflow、schema compatibility の tool 側総合入口。

## Website

- [Website operations](website/README.md): `website/` 公開ディレクトリには置かない運用メモ、route 索引、設計文書、sitemap 方針。

## 編集ガイドライン

- [AAT / Lean guideline](aat/guideline.md): `Formal/Arch`、AAT 数学本文、Lean status、proof obligation の編集方針。
- [SFT guideline](sft/guideline.md): SFT 本文、AAT / SFT interface、forecast / governance claim boundary の編集方針。
- [Tooling guideline](tool/guideline.md): ArchMap、LawPolicy、ArchSig、FieldSig、schema、CLI、fixture の編集方針。
- [Website guideline](website/guideline.md): Cloudflare Pages 公開面、route、tone、asset path、sitemap の編集方針。

## Archive

- [2026-05-09 AAT/SFT reorg archive](archive/2026-05-09-aat-sft-reorg/): AAT/SFT 階層へ再編する前の旧 AAT Part 文書、旧数学設計書、旧 proof obligations、旧 theorem index、旧 Architecture Signature Dynamics 設計。
- [2026-05-09 first-class docs archive](archive/2026-05-09-first-class-docs/): 後方互換のためだけに残っていた facade 文書、薄い索引、旧 PRD、旧 design note、旧 empirical pilot の退避先。
- [AAT v2 research requirements revised split](archive/aat_v2_research_requirements_revised_split.md): 数学設計書とツール設計書へ分割する前の原本。
- [Flatness-Obstruction Conjecture](archive/Flatness%E2%80%93Obstruction%20Conjecture.md): AAT 数学理論へ整理する前の数学草案。
- [証明義務と実証仮説 full ledger](archive/proof_obligations_full_ledger.md): `docs/aat/proof_obligations.md` を索引化する前の詳細 ledger。
