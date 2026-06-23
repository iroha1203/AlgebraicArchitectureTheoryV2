---
status: idea
goal:
candidate_type:
capability_category:
expected_base_score:
expected_evidence_multiplier:
expected_final_score:
evidence_stage:
rival_advantage:
genius_potential:
genius_target:
genius_support_role:
target_theorem:
target_support_node:
target_progress:
proof_obligation_delta:
target_completion_role:
origin: NT-XX
tags: []
created: 2026-06-14
# 以下はループが picked 以降に付ける(任意)。語彙は README を参照。
# cycle: 1
# lean: none
# archived_reason:
---

# <タイトル>

## 主張

(命題を正確に述べる。相対化のパラメータ、仮定、結論を明らかにする。)

## 候補種別

`closure` / `orientation` / `unification` / `computability` / `bridge` / `genius` / `genius-target` / `genius-support` / `target-support` / `target-obstruction` / `target-refinement` / `target-proof` のいずれかを選ぶ。

## 依拠

(よりどころとする AAT の既存対象や既存定理。`docs/aat` の章、大定理の番号、NT 番号などを挙げる。)

## 非自明性

(なぜ定義の言い換えや自明な系ではないのかを述べる。)

## 数学的興味

(この候補が数学としてなぜ面白いか。驚き、圧縮、反例性、新しい不変量、構成、比較、古典理論との接続などを述べる。)

## GOAL への前進

(この候補が GOAL のどの能力カテゴリをどう増やすかを一文で述べる。)

## ライバルに対する有効性

(GOAL の `rival` がすでに持つ能力を踏まえ、この候補がどの点で優位性、新規性、統合力、分離力、検証可能性を持つかを書く。静的解析器、ADL 解析器、architecture conformance checker、metric dashboard の言い換えに留まる場合は picked にしない。)

## SCORE 見込み

- `score_reason`:
- `dullness_risk`:
- `proof_or_evidence_plan`:

## Target Theorem 寄与

(`research mode: target-theorem` の GOAL で使う。通常 GOAL では `not-applicable` と書く。target theorem を弱めず、どの support node / proof obligation を進めるかを書く。)

- `target_theorem`:
- `target_support_node`:
- `target_progress`:
- `proof_obligation_delta`:
- `target_completion_role`:

## CS / SWE への帰結

(これまで測れなかった、あるいは言えなかった何が言えるようになるか。計測にかかわる場合は移植の仮定を添える。)

## 証明・根拠の見込み

(証明の筋道。予想であれば、支持する証拠・特別な場合・有限例・数値による検算を挙げる。Lean で形式化する場合は、狙う statement と必要な claim boundary を書く。)

## 審判メモ

- 厳密性:
- 研究価値:
- repo 全体価値:
- ライバル比較:

## 関連

(関連する候補や既存の結果。)

## 進捗ログ

- 2026-06-14: 作成
