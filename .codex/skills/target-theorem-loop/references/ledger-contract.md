# Target Theorem Loop Ledger Contract

## 原則

- target theorem の statement と completion criteria は `research/goals/<goal-id>.md` を正本にする。
- tracking Issue には runtime state、proof obligation delta、blocker、PR、次 obligation を置く。
- report には証拠索引、Lean declarations、premise_delta、completion 判定材料を置く。
- SCORE と candidate card は使わない。
- `Closes #N` は人間が明示した場合だけ使う。通常は `Refs #N`。
- local path、private path、machine-specific identifier を public comment に入れない。
- `$math-lean-review` の正式 verdict なしに `target-theorem-proved` ledger を書かない。
