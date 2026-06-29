# Target GOAL Card Contract

T0 で `research mode: target-theorem` の GOAL card を検査するときだけ読む。

## 必須項目

- `id` と `status: active`。
- `research mode: target-theorem`。
- `research aim`: target theorem が代表する研究能力。
- `rival`: target theorem が差分を作る比較対象。
- `claim boundary`: 通常の GOAL claim boundary。
- `target theorem`: 証明したい大定理の名前と自然言語 statement。
- `target theorem boundary`: 語彙、有限性、law universe、coverage topology、係数、site / cover、Lean 置き場所、証拠段階。
- `target proof artifacts`: 完了時に存在すべき Lean theorem / theorem package / finite witness / concrete certificate / report section。
- `target proof strategy`: support lemma、normalization、counterexample exclusion、bridge、既存成果の利用 map。
- `target theorem completion criteria`: sorry なし Lean proof、対象 declaration の axiom audit、material premise / hypothesis discharge audit、certificate provenance audit、proof-use audit、structure-field escape audit、T3 audit、report / tracking Issue 同期、final review packet、4 並列査読すべての veto なし、final `$math-lean-review` を含む完了条件。
- `target premise discharge policy`: target theorem の実質的前提を target boundary として残すのか、completion までに theorem / finite witness / concrete certificate で discharge するのか。
- `target material premise ledger`: 各 premise について、名前、支える結論、role (`direction-hypothesis` / `ambient-boundary` / `discharge-required` / `conclusion-equivalent-risk`)、必要 discharge artifact、certificate provenance requirement、proof-use requirement、結論相当 premise ではない理由。
- `target anti-weakening rule`: 結論相当の仮定を theorem argument、typeclass、structure field、certificate field、opaque membership に移して成功扱いしない規則。
- `target route integrity gate`: selected / canonical / free / realization / certificate / finite witness / class-boundary を target proof で使う場合、それが target-fitting な ad hoc construction ではなく入力境界、canonical/free construction、universal property、finite witness、または reviewed predecessor theorem から来ることを監査する規則。該当する構成を使わない GOAL では省略可。
- `target failure policy`: `target-refuted` / `target-blocked` / GOAL 改訂提案の扱い。

## 欠陥判定

次のいずれかに当たる場合は T1 へ進まない。

- GOAL が active ではない。
- `research mode: target-theorem` ではない。
- target theorem / boundary / proof artifacts / proof strategy / completion criteria が不足している。
- completion criteria が SCORE threshold、candidate card、PR merge だけになっている。
- completion criteria に final `$math-lean-review` の正式 4 並列査読 gate が含まれていない、またはこの skill 側で gate を実行できない。
- target theorem の結論に必要な実質的前提があるのに、target boundary として残すのか completion までに discharge するのかが不明。
- target material premise ledger または anti-weakening rule がなく、completion 時に premise を監査できない。
- material premise ledger が faithfulness、exactness、coverage、sheaf condition、effectivity、triviality、representation adequacy などを `ambient-boundary` として残しているのに、結論相当 premise ではない理由がない。
- `discharge-required` premise の certificate provenance requirement がなく、explicit certificate / structure field / theorem argument を放電済みと誤読できる。
- completion criteria が proof-use audit と structure-field escape audit を含まず、未使用 premise や field への結論逃がしを検出できない。
- selected / canonical / free / realization / certificate / finite witness / class-boundary を使うのに route integrity gate がなく、target-fitting construction、vacuity、one-way-as-equivalence、GOAL/report 後追い読み替えを検出できない。
- target theorem が GOAL の research aim や rival delta と切り離され、ただの定理一覧項目になっている。

欠陥を見つけたら GOAL 本文は編集せず、tracking Issue コメントまたは別 Issue に改訂案を残す。
