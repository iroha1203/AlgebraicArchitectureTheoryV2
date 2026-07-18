# Target GOAL Card Contract

`research mode: target-theorem` の GOAL card が満たすべき契約。

## 必須項目

- `id` と `status: active`。
- `research mode: target-theorem`。
- `research aim`: target theorem が代表する研究能力。
- `rival`: target theorem が差分を作る比較対象。
- `claim boundary`: 通常の GOAL claim boundary。
- `target theorem`: 証明したい大定理の名前と自然言語 statement。
- `target statement contract reference`: GOAL cardのtarget statement sectionは固定statementまたはcontractへの正確な参照を持つ。target-theorem-loopの既定ではtracking Issueのversion付きstatement contract commentを正本とし、Issue本文またはproof-state commentからactiveな`statement_contract` blockでそのpermalinkとversionを一意に参照する。別の許可されたartifactを正本にする場合も、Issueから正確な位置とversionを解決できることを要求する。contractは対象theoremの名前・完全Lean signature・参照する新規def signature(なければ`none`)を含み、同じversionを対象とするmath-A、math-B、lean-A、lean-Bの各1本のaudit commentが受理根拠になる。external artifactでは、差し替え不能なcommit/ref/hash等の`source_revision`も必須とする。
- `target theorem boundary`: 語彙、有限性、law universe、coverage topology、係数、site / cover、Lean 置き場所、証拠段階。
- `target proof artifacts`: 完了時に存在すべき Lean theorem / theorem package / finite witness / concrete certificate / report section。
- `target proof strategy`: support lemma、normalization、counterexample exclusion、bridge、既存成果の利用 map。
- `target theorem completion criteria`: sorry なし Lean proof、対象 declaration の axiom audit、material premise / hypothesis discharge audit、certificate provenance audit、proof-use audit、structure-field escape audit、T3 audit、report / tracking Issue 同期、final review packet、final `$math-lean-review` の正式判定を含む完了条件。
- `target premise discharge policy`: target theorem の実質的前提を target boundary として残すのか、completion までに theorem / finite witness / concrete certificate で discharge するのか。
- `target material premise ledger`: 各 premise について、名前、支える結論、role (`direction-hypothesis` / `ambient-boundary` / `discharge-required` / `conclusion-equivalent-risk`)、必要 discharge artifact、certificate provenance requirement、proof-use requirement、結論相当 premise ではない理由。
- `target anti-weakening rule`: 結論相当の仮定を theorem argument、typeclass、structure field、certificate field、opaque membership に移して成功扱いしない規則。
- `target route integrity gate`: selected / canonical / free / realization / certificate / finite witness / class-boundary を target proof で使う場合、それが target-fitting な ad hoc construction ではなく入力data、canonical/free construction、universal property、finite witness、または reviewed predecessor theorem から来ることを監査する規則。該当する構成を使わない GOAL では省略可。
- `target failure policy`: `target-refuted` / `target-blocked` / GOAL 改訂提案の扱い。

## 欠陥判定

次のいずれかに当たる場合は T1 へ進まない。

- GOAL が active ではない。
- `research mode: target-theorem` ではない。
- target theorem / boundary / proof artifacts / proof strategy / completion criteria が不足している。
- activeな`statement_contract` blockがない、version・正本permalink・source・`source_revision`・active reference permalink・`supersedes`・cycle・実装開始前記録・baseline ref・target file listがない、正本の対象theoremの完全signatureまたは参照する新規def signature(なければ`none`)がない、GOAL cardの正確な参照またはIssue本文/proof-state commentからのactive referenceが一意でない、旧active referenceが失効していない、cycle開始前の受理記録がない、または同じversionと正本を対象とするmath-A、math-B、lean-A、lean-Bの各1本のaudit commentがなく、いずれかが`decision: approve`・`unchecked: none`・`finding: none`・lane固有確認・独立入力snapshot・独立実行記録を満たさない。
- completion criteria が SCORE threshold、candidate card、PR merge だけになっている。
- completion criteria に final `$math-lean-review` の正式 gate が含まれていない、またはこの skill 側で gate を実行できない。
- target theorem の結論に必要な実質的前提があるのに、target boundary として残すのか completion までに discharge するのかが不明。
- target material premise ledger または anti-weakening rule がなく、completion 時に premise を監査できない。
- material premise ledger が faithfulness、exactness、coverage、sheaf condition、effectivity、triviality、representation adequacy などを `ambient-boundary` として残しているのに、結論相当 premise ではない理由がない。
- `discharge-required` premise の certificate provenance requirement がなく、explicit certificate / structure field / theorem argument を放電済みと誤読できる。
- completion criteria が proof-use audit と structure-field escape audit を含まず、未使用 premise や field への結論逃がしを検出できない。
- selected / canonical / free / realization / certificate / finite witness / class-boundary を使うのに route integrity gate がなく、target-fitting construction、vacuity、one-way-as-equivalence、GOAL/report 後追い読み替えを検出できない。
- target theorem が GOAL の research aim や rival delta と切り離され、ただの定理一覧項目になっている。

欠陥を見つけたら GOAL 本文は編集せず、tracking Issue コメントまたは別 Issue に改訂案を残す。

## Tracking Issue comment templates

task固有のsignatureはこのtemplateへ書き込まず、実際のtracking Issue commentを正本にする。

### Statement contract comment

`````text
## Statement contract v<N>

goal: <goal-id>
contract_version: v<N>
contract_status: proposed
contract_source: issue-comment | external-artifact

target_theorems:
```lean
-- 各対象theoremの名前と完全signature
```

new_definitions_referenced_by_target:
```lean
-- statementが参照する新規defの名前と完全signature。なければ `none`
```

implementation_scope:
  baseline_ref: <preflight-base-commit>
  target_files:
    - <repo-relative-target-Lean-file>
`````

`contract_source: issue-comment`が既定であり、このcommentに完全signatureと実装対象scopeを置く。Issue commentのpermalink・author・作成時刻・本文hashは投稿後にIssue/API metadataから取得し、active gateと後段のpacketへ`source_permalink`と`source_revision`として記録する。contract comment自身へ自己参照URLを書き足さず、受理後に本文を編集しない。`external-artifact`は§5.1で許可された別の正本を選ぶ必要があるtaskだけで使い、`source_permalink`が解決できるstable locationを持ち、`source_revision`にcommit/ref/hash等の差し替え不能な版を記録し、artifact側に同じ完全signatureと実装対象scopeを置く。Issue comment、GOAL、report、git管理docsへsignatureを重複記載しない。

`contract_status: proposed`は、4本のaudit前のimmutableなcontract comment状態である。4本すべてのauditが同じversionを承認した後、同じcontract permalinkを指すactive gate commentの`statement_contract.status: active`が受理状態を表す。T0はactive gate、contract comment、4本のauditのversion/permalinkを突合し、active gateだけでは受理しない。

### Active statement contract reference comment

```text
## Statement contract gate v<N>

statement_contract:
  status: active
  version: v<N>
  permalink: <canonical-contract-permalink>
  source: issue-comment | external-artifact
  source_revision: <issue-comment-url-author-created-at-body-hash-or-immutable-artifact-revision>
  supersedes: <previous-active-reference-permalink | none>
  preflight_cycle: <N>
  preflight_recorded_at: <tracking-Issue-comment-timestamp>
  contract_accepted_before_implementation: true
  implementation_start_ref: none
  implementation_scope:
    baseline_ref: <preflight-base-commit>
    target_files:
      - <repo-relative-target-Lean-file>
  audits:
    math_a: <audit-comment-permalink>
    math_b: <audit-comment-permalink>
    lean_a: <audit-comment-permalink>
    lean_b: <audit-comment-permalink>
```

Issue本文またはproof-state commentからこのblockを一意に参照する。active gate comment自身のURLは本文へ自己参照として書かず、Issue/API metadataから取得したcomment permalinkをactive referenceとして後段のT0 state、final packet、completion ledgerへ記録する。旧versionのreferenceは編集せず、新versionでは新しいgate commentを追加して`supersedes`で旧referenceを失効させる。T0は最新の未失効blockだけをactiveとして採用し、複数active・未解決の`supersedes`・`implementation_start_ref`が`none`でないpreflight記録・実装開始後のpreflight記録を拒否する。

### Four-lane audit comment

```text
## Statement contract audit v<N>

contract_version: v<N>
contract_permalink: <canonical-contract-or-external-artifact-permalink>
input_snapshot: <contract permalink + source_revision + GOAL/source refs or hashes>
lane: math-A | math-B | lean-A | lean-B
reviewer_ref: <independent-reviewer-reference>
independence: independent-input
independence_evidence: <how this reviewer received the source without another audit output>
decision: approve | reject

checked:
- item: <goal_claim | quantification | coefficient | conclusion_strength | premise | elaboration | additional_premise | definitional_escape | api_connection>
  result: <concrete observation for this item>
  evidence_ref: <source or execution evidence for this item>
unchecked: none
finding: none
refutation_attempts:
- <少なくとも1件の具体的な反証試行と結果>
evidence:
- <少なくとも1件の具体的な確認sourceまたは実行証拠>
```

`lane`はmath-A、math-B、lean-A、lean-Bを各1本だけ許可する。4本のaudit permalink、`reviewer_ref`、comment metadataのauthor、`input_snapshot`、`independence_evidence`は確認可能な形で記録し、permalink・reviewer_ref・author・input_snapshotは相互に異ならなければならない。math laneの`checked`は`goal_claim`、`quantification`、`coefficient`、`conclusion_strength`、`premise`を各1件、Lean laneの`checked`は`elaboration`、`additional_premise`、`definitional_escape`、`api_connection`を各1件、各々`result`と`evidence_ref`付きで記録する。`refutation_attempts`と`evidence`は各1件以上の具体的な内容を持つ。`approve`には`unchecked: none`、`finding: none`、lane固有の全項目、`independence: independent-input`、placeholderでない具体的な独立入力記録を必須とする。T0は4本のaudit本文がmetadataだけ異なる同一内容でないことも確認する。受理済みcommentは編集して差し替えない。signatureを変更するときは実装を停止し、新versionのcontract comment、active reference、4本のaudit、preflight記録を追加してから再開する。
