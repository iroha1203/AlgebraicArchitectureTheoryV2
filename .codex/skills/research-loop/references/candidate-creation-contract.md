# Candidate Creation Contract

## 作成時の必須フィールド

候補カードは `research/ideas/TEMPLATE.md` のfield集合を唯一のschema正本として
`research/ideas/` に置く。このcontractへfield一覧を複製しない。

`planned_lean_statement` には、定理候補の予定 Lean statement(theorem 名+完全な signature。statement が参照する新規 def の signature を含む)を Lean コードブロックで固定する(`docs/aat/lean_quality_standard.md` §5)。G2 審判 A はこの固定 statement を審査対象とし、G3 は実装 declaration との一致を合格条件とする。反例・計算例など Lean proof を要求しない候補は `planned_lean_statement: none(証拠 artifact 型)` と書く。

`material_premises` には、予定 statement の各仮定(明示引数、typeclass、structure field、certificate field)を三分類(本文由来 / 放電済み / 未放電。同 §1.1)で申告する。申告のない仮定は未放電として扱われる。

`candidate_type` は `closure`、`orientation`、`unification`、`computability`、`bridge`、`genius`、`genius-target`、`genius-support` のいずれかにする。大定理証明用の `target-support` などは `$target-theorem-loop` の候補種別であり、この skill では使わない。
