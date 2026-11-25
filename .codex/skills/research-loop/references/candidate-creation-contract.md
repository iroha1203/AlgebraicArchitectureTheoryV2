# Candidate Creation Contract

## 作成時の必須フィールド

候補カードは `research/ideas/TEMPLATE.md` の field 定義（スキーマ定義）に従って
`research/ideas/` に置く。

`planned_lean_statement` には、定理候補のtarget claim、必要な結論、明示された仮定を記録するか、同内容を持つ一次仕様の正確な位置を記録する(`docs/aat/lean_quality_standard.md` §5)。theorem名+完全なsignatureと、statementが参照する新規defのsignatureをLeanコードブロックで記録してよいが必須ではない。G2評価Aは指定された一次仕様を審査対象とし、G3は実装declarationとの直接照合を合格条件とする。反例・計算例などLean proofを要求しない候補は`planned_lean_statement: none(証拠 artifact 型)`と書く。

`material_premises` には、予定 statement の各仮定(明示引数、typeclass、structure field、certificate field)を三分類(本文由来 / 解消済み / 未解消。同 §1.1)で申告する。申告のない仮定は未解消として扱われる。

`candidate_type` は `closure`、`orientation`、`unification`、`computability`、`bridge`、`genius`、`genius-target`、`genius-support` のいずれかにする。大定理証明用の `target-support` などは `$target-theorem-loop` の候補種別であり、この skill では使わない。
