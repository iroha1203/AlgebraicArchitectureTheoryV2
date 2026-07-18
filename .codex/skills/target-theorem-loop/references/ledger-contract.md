# Target Theorem Loop Ledger Contract

## 原則

- GOAL card は target theorem の自然言語 claim と completion criteria の正本にする。task固有のLean statement contractは、target-theorem-loopの既定ではtracking Issueのversion付きcommentを正本にし、Issue本文またはproof-state commentからactiveな`statement_contract` blockでそのpermalinkとversionを参照する。別の許可されたartifactを選ぶ場合も、同じblockから正確な位置とversionを解決する。これは他workflowのcontract保存場所を固定する規律ではない。
- statement contractは1つだけを正本とし、GOAL、report、git管理docsへsignatureを複製しない。comment templateとcanonical blockのschemaは[Target GOAL Card Contract](target-goal-contract.md)を正とし、contract commentが対象theoremの完全signatureと参照する新規def signature(なければ`none`)を持つこと、4本の事前auditが同じversionを承認していること、cycle開始前のpreflight記録があることをT0で確認する。
- tracking Issue には runtime state、proof obligation delta、blocker、PR、次 obligation を置く。
- report には証拠索引、Lean declarations、premise_delta、completion 判定材料を置く。
- SCORE と candidate card は使わない。
- `Closes #N` は人間が明示した場合だけ使う。通常は `Refs #N`。
- local path、private path、machine-specific identifier を public comment に入れない。
- `$math-lean-review` の正式 verdict なしに `target-theorem-proved` ledger を書かない。
