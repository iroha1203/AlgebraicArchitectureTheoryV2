# AAT: 代数的アーキテクチャ論

このディレクトリは、AATの数学本文とLean形式化の編集基準を案内する。
理論本体は[代数幾何的アーキテクチャ論](algebraic_geometric_theory/README.md)の
全6部19章と付録A–Eにある。

AATは、AtomとLawによって意味の対象と射を定め、その実現・変更・修復の全体を調べる。
共通の語彙で状態・操作・関係・量を持つモデルを構成し、その族の幾何、局所からの組立て、
障害、観測に必要な情報へ進む。

## 数学本文を読む

[序論](algebraic_geometric_theory/introduction.md)で三つの到達点と論証の順序を確認し、
[共通記号](algebraic_geometric_theory/notation.md)を参照しながら各部へ進む。
章・節・付録へのリンクは[数学本文の目次](algebraic_geometric_theory/README.md)にある。

| 部 | 章 | 主題 |
| --- | --- | --- |
| I | 1–3 | Lawと意味の基礎 |
| II | 4–6 | 実現の族とLawの幾何 |
| III | 7–9 | 意味を保つ変更の全体 |
| IV | 10–13 | 局所変更・修復・障害 |
| V | 14–16 | 輸送・比較・診断 |
| VI | 17–19 | 観測・必要情報・再構成 |

付録A–Eは、正の論理、係数とdescent、関係・解消・逆極限、有限root schemeとstalk、
変更経路と費用を扱う。定義・定理・証明と、それらに必要な仮定は数学本文の中で確認できる。

## 編集と形式化の参照先

- [AAT / Lean 編集ガイドライン](guideline.md)
- [Lean 品質基準](lean_quality_standard.md)

Lean 形式化との対応があるものは、`Formal/` のLean sourceで直接確認する。
Part X theorem-7.5のtarget claimは、taskが指定する一次仕様と
`Formal/` の実装 declaration を直接突合して確認する。

数学本文は、作業状態や Issue 管理状態を混ぜない。
現在 Lean に存在する定義・定理は `Formal/` のLean sourceで確認する。
未解決課題とResearchの進行状態は、数学本文を変更せずGitHub Issues・GOAL・PRDで管理する。

`proved`, `defined only`, `future proof obligation`, `empirical hypothesis`
を混同しない。特に、tooling output、source-observation output、未測定軸、
empirical correlation は、それだけで Lean theorem にはならない。

SFTの理論は[SFT](../sft/software_field_theory.md)、ArchMap・ArchSigなどの入力と計算は
[Tooling](../tool/README.md)で扱う。
