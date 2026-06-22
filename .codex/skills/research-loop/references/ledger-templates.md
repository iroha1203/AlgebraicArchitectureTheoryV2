# Research Loop Ledger Templates

この参照は、tracking Issue に cycle / merge / phase / genius target コメントを書くときだけ読む。
テンプレートは GOAL 非依存で使う。GOAL 固有の理論語彙は、各 GOAL の `rival`、`reward rubric`、`claim boundary`、候補カード、report から埋める。

## 原則

- tracking Issue は runtime state の正本である。GOAL 定義、report、候補カードだけで SCORE 台帳を進めない。
- `Closes #N` は人間が明示した場合だけ使う。通常は `Refs #N`。
- コメントは、人間向け要約と、後続 G6 が再構成できる ledger block の両方を持つ。
- local path、private path、machine-specific identifier を public comment に入れない。
- phase boundary は、phase summary コメント URL を残し、tracking Issue が open のままであることを確認して完了とする。

## Cycle SCORE Update

````text
Cycle <N> SCORE update

picked: <candidate>
type: <candidate_type>
evidence: <evidence_stage>
score: +<final_score> = base <base_score> x multiplier <multiplier> - penalty <penalty>
category: <category>
total: <before> -> <after> / active threshold <threshold>
remaining: <max(threshold-after, 0)>
genius: <not-applicable | downgraded-to-normal | target-seed | support-cycle | unlock>

GOAL delta: <one or two sentences>
Rival delta: <one or two sentences comparing against each named rival at the right granularity>

Evidence:
- <changed or fixed evidence artifact>

Checks:
- <local build / evidence check / axiom audit / sync audit summary>
- G3 formalization quality audit: <pass | revise | fail | not-applicable>
- G4 SCORE audit: <confirm | reduce | reject | seed-only>

Ledger:
```yaml
ledger_type: cycle_score
goal: <goal-id>
cycle: <N>
candidate: <candidate>
candidate_type: <candidate_type>
evidence_stage: <evidence_stage>
base_score: <base_score>
evidence_multiplier: <multiplier>
penalty: <penalty>
final_score: <final_score>
total_before: <before>
total_after: <after>
active_threshold: <threshold>
remaining: <remaining>
genius_state: <state>
stop_state: <continue | phase-boundary-candidate | blocked>
```
````

## Merge Update

````text
Cycle <N> merge update

picked: <candidate>
PR: #<number> <merged | open | blocked>
merge commit: <oid or none>
score: +<final_score>
new total: <after> / active threshold <threshold>
remaining: <remaining>

CI:
- <check name>: <pass | fail | pending | not-run>

Independent G5 review: <mergeable | needs changes | blocked | not-run>, <short reason>

Stop state before G6: <continue candidate | phase-boundary candidate | blocked>. <why>

Ledger:
```yaml
ledger_type: merge_update
goal: <goal-id>
cycle: <N>
pr: <number>
pr_state: <merged | open | blocked>
merge_commit: <oid or null>
final_score: <final_score>
total_after: <after>
active_threshold: <threshold>
remaining: <remaining>
checks_state: <pass | fail | pending | mixed>
g5_review: <mergeable | needs-changes | blocked | not-run>
stop_state_before_g6: <continue | phase-boundary-candidate | blocked>
tracking_issue_closed: false
```
````

If `gh pr merge` exits nonzero, do not decide from the local exit code alone. Run:

```bash
gh pr view <PR> --json state,mergedAt,mergeCommit
```

Treat the PR as merged only if GitHub reports `state: MERGED` and a merge commit.

## Genius Target Seed

Use this when a `genius-target` is selected as a research-program seed. Do not add SCORE unless G4 returns normal `confirm` / `reduce`; `seed-only` is `0`.

````text
Genius target seed

target: <target theorem / conjecture / program>
claim boundary: <boundary>
why rare: <why this could be breakthrough-grade if unlocked>
support map:
- <needed support theorem / counterexample / construction>
unlock condition: <what evidence would unlock genius scoring>
current score effect: <+0 seed-only | normal score if confirmed>

Ledger:
```yaml
ledger_type: genius_target_seed
goal: <goal-id>
target: <target>
claim_boundary: <boundary>
support_nodes:
  - <node>
unlock_condition: <condition>
score_effect: <seed-only | normal-score>
tracking_issue_closed: false
```
````

## Genius Support Update

````text
Genius support update

target: <target>
support node advanced: <node>
cycle: <N>
score: +<final_score> / normal SCORE
unlock distance: <closer | unchanged | target revised | target rejected>

Ledger:
```yaml
ledger_type: genius_support_update
goal: <goal-id>
target: <target>
cycle: <N>
support_node: <node>
final_score: <final_score>
unlock_distance: <closer | unchanged | revised | rejected>
tracking_issue_closed: false
```
````

## G6 Phase Summary

````text
G6 phase-boundary judgment / phase summary

verdict: <phase-boundary | continue | blocked | goal-defect>
total_score: <total>
active_threshold: <threshold>
portfolio_constraint: <satisfied | not-satisfied | cannot-determine>
coherent_report_or_paper_seed: <satisfied | not-satisfied | cannot-determine>
rival_phase_delta: <satisfied | not-satisfied | cannot-determine>
research_kiri: <yes | no>
tracking_issue_remains_open: true

Phase summary:
- merged PRs / merge commits: <list or compact table>
- cycle SCOREs: <list or compact table>
- CI / independent review: <summary>
- report current position: <report section / paper seed status>
- next frontier: <frontier proposals from GOAL/report/G6>
- human decision requested: <end phase | set next threshold | revise GOAL | paper/canonicalization | continue>

Ledger:
```yaml
ledger_type: phase_summary
goal: <goal-id>
verdict: <phase-boundary | continue | blocked | goal-defect>
total_score: <total>
active_threshold: <threshold>
portfolio_constraint: <state>
rival_phase_delta: <state>
merged_prs:
  - pr: <number>
    merge_commit: <oid>
    cycle: <N>
    final_score: <score>
phase_summary_comment_url: <url>
tracking_issue_closed: false
```
````

After posting the phase summary, verify:

```bash
gh issue view <issue> --json state,url
```

The expected state is `OPEN` unless the human explicitly requested closure.

## Report Drift Checklist

Before PR creation and again before G6 phase summary, search the report for stale runtime state:

```bash
rg -n "total SCORE|active threshold|remaining|Next Frontier|Phase Boundary|proved-in-research|Cycle [0-9]+" research/reports/<goal-id>.md
```

Confirm that current totals, active threshold, remaining SCORE, proof portfolio counts, and phase-boundary language agree with the tracking Issue ledger.
