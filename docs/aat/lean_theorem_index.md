# Lean 定義・定理索引

この文書は、現在 Lean 側に存在する主要な定義・定理の索引入口である。
詳細索引は、古典 AAT、代数幾何 AAT、研究ループを混ぜないために分割して管理する。

`proof_obligations.md` は未解決課題と実証仮説の入口として扱い、この文書は実装済みの
Lean API を確認する入口として扱う。

## 分割索引

| 索引 | 対象 | 主な用途 |
| --- | --- | --- |
| [古典 AAT / downstream Lean API 索引](lean_theorem_index_classical_aat.md) | `Formal/Arch`、finite static structural core、Atom-generated kernel、SFT / ArchSig / tooling bridge | 既存 bounded theorem package、古典 AAT 由来 API、downstream bridge API を確認する。 |
| [代数幾何 AAT Lean API 索引](lean_theorem_index_ag_aat.md) | `Formal/AG`、AG 版 AAT Part I〜10 | 現行 AAT 数学本文に対応する Lean declaration、本文ラベル、status を確認する。 |
| [研究ループ Lean API 索引](lean_theorem_index_research.md) | `Formal/AG/Research`、target-theorem / research-loop theorem package | 研究ループで追加された theorem package と review 境界を確認する。 |

## 索引の読み方

この索引は、数学設計書の theorem 候補をそのまま現在の Lean proved claim に
昇格するための文書ではない。Lean 実装済み API の入口であり、Lean status と
未解決 proof obligation の境界は
[証明義務と実証仮説](proof_obligations.md) と分割台帳で管理する。

各表の `Status` は declaration 単位の状態である。`proved` には、主定理だけでなく、
schema field を取り出す accessor theorem、定義間の bridge theorem、有限例の
example theorem、bounded completeness theorem が含まれる。研究上の主張として読む場合は、
各節の Non-conclusions と `proof_obligations.md` / 分割 proof obligation 台帳の
coverage / exactness assumptions を併せて確認する。

## 更新ルール

- `Formal/Arch`、SFT bridge、tooling-side theorem metadata、古典 Atom-generated kernel を更新した場合は、原則として [lean_theorem_index_classical_aat.md](lean_theorem_index_classical_aat.md) を更新する。
- `Formal/AG` の AG 版 AAT PRD / 本文ラベル対応を更新した場合は、[lean_theorem_index_ag_aat.md](lean_theorem_index_ag_aat.md) を更新する。
- `Formal/AG/Research` や target-theorem / research-loop theorem package を更新した場合は、[lean_theorem_index_research.md](lean_theorem_index_research.md) を更新する。
- 未解決 proof obligation、empirical hypothesis、Issue tracking は [proof_obligations.md](proof_obligations.md) 入口から対応する分割台帳へ置く。
- この入口は分割方針とリンクだけを持つ。詳細な declaration 表は分割索引へ置く。
