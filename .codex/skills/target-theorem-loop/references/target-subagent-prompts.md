# Target Theorem Loop Subagent Prompts

このファイルは `$target-theorem-loop` の subagent 標準プロンプト集である。必要なゲートの見出しだけ読む。

期待する結論、本体の推測、採点意図、成功させたい候補は追記しない。

## T1 候補生成

```text
Use the target-theorem-loop criteria to generate proof-progress candidates for GOAL <goal-id>.
Your T1 role is: <premise-discharge | statement-audit | proof-dag | obstruction>.
Inputs: research/GOALS.md target theorem section, tracking Issue proof state summary, material premise ledger, anti-weakening rule, support map, relevant Lean files named by the GOAL.
Do not edit files. Do not weaken the target theorem to make an easy success.
Return at least one candidate:
candidate_type: target-support | target-obstruction | target-refinement | target-proof
target_theorem:
target_support_node:
claim:
proof_obligation_delta:
material_premises:
premise_discharge_plan:
anti_weakening_risk:
planned_theorem_names:
proof_or_evidence_plan:
target_progress:
expected_base_score:
expected_evidence_multiplier:
expected_final_score:
rival_advantage:
checked:
unchecked:
```

## T2 審判 A: 数学的厳密性

```text
Judge this target-theorem candidate only for mathematical rigor and claim boundary fidelity.
Inputs: GOAL target theorem, candidate card <path>, target boundary, support map, material premise ledger, anti-weakening rule.
Reject if the candidate weakens the target theorem or hides a conclusion-equivalent premise.
Return:
verdict: accept | revise | reject
target_progress: support-node | blocker-found | target-refined | target-proof-candidate | target-proof-checkpoint-candidate | target-refuted
base_score:
reason:
boundary_fidelity:
statement_strength:
proof_risk:
required_evidence:
checked:
unchecked:
```

## T2 審判 B: proof distance

```text
Judge whether this candidate materially shortens the proof distance to the GOAL target theorem or exposes a real blocker/refutation.
Inputs: GOAL target theorem, candidate card <path>, tracking Issue proof state, support map.
Return:
verdict: accept | revise | reject
target_progress:
base_score:
proof_distance_delta:
support_node_value:
blocker_value:
reason:
checked:
unchecked:
```

## T2 審判 C: premise / anti-weakening

```text
Judge only material premises and anti-weakening.
Inputs: GOAL material premise ledger, anti-weakening rule, candidate card <path>, planned Lean statement.
Reject or require revise if a required premise remains as an undischarged theorem argument, typeclass, structure field, certificate field, or opaque membership condition.
Return:
verdict: accept | revise | reject
target_progress:
material_premises:
premise_discharge_status:
new_material_premise:
anti_weakening_verdict:
reason:
checked:
unchecked:
```

## T2 審判 D: project / rival value

```text
Judge project-level and rival value of this target-proof candidate.
Inputs: GOAL, rival field, candidate card <path>, current report if any, tracking Issue proof state.
Return:
verdict: accept | revise | reject
target_progress:
base_score:
repo_wide_value:
rival_delta:
future_surface: docs | Lean | paper | tooling | website | none
reason:
checked:
unchecked:
```

## T3 公理検査

```text
Check the Lean evidence for target candidate <candidate>.
Inputs: candidate card <path>, Lean file <path>, target theorem claim boundary, reported declaration names.
Run or inspect #print axioms for every reported declaration.
Return:
verdict: pass | fail | cannot-determine
build_status:
axioms:
has_sorryAx:
allowed_axioms_only:
fidelity_to_target_candidate:
formal_ag_boundary_ok:
reason:
checked:
unchecked:
```

## T3 Lean 形式化品質監査

```text
Audit whether the Lean formalization captures the target candidate at the right strength.
Inputs: candidate card <path>, Lean file <path>, GOAL target claim, material premise ledger, anti-weakening rule.
Inspect theorem arguments, typeclass arguments, structure fields, certificate fields, and class membership.
Return:
verdict: pass | revise | fail | cannot-determine
statement_matches_candidate:
not_too_weak:
not_too_strong_or_vacuous:
material_premises_visible:
no_hidden_conclusion_premise:
claim_boundary_encoded:
formal_ag_boundary_ok:
reason:
checked:
unchecked:
```

## T3.5 候補カード同期

```text
Audit whether candidate card <path>, Lean/evidence files, judge memos, tracking Issue proof state, and report entry agree.
Return:
verdict: synced | revise | fail | cannot-determine
target_theorem_synced:
proof_obligation_delta_synced:
premise_discharge_status_synced:
anti_weakening_audit_synced:
lean_declarations_match:
math_lean_review_scope_ready:
reason:
checked:
unchecked:
```

## T4 target progress / SCORE 監査

```text
Audit target proof progress and auxiliary SCORE for candidate <candidate>.
Inputs: GOAL target theorem, synchronized candidate card <path>, evidence files, T2 judge outputs, T3 audits, T3.5 sync audit, tracking Issue proof state, current diff.
Do not return target-proved. T6 and $math-lean-review decide completion.
Return:
score_verdict: confirm | reduce | reject | seed-only
base_score:
evidence_multiplier:
penalty:
final_score:
target_progress: support-node | blocker-found | target-refined | target-proof-candidate | target-proof-checkpoint-candidate | target-refuted
proof_obligation_delta:
material_premises:
premise_discharge_status:
material_premise_ledger_delta:
new_material_premise:
anti_weakening_verdict:
reason:
checked:
unchecked:
```

## T5 PR レビュー

```text
Use $review-pr <PR-number> and apply the review-pr skill.
In addition to the normal PR review, check target-theorem-loop gates:
- target proof state and proof_obligation_delta are represented faithfully
- material premise ledger, premise discharge status, new or hidden material premise findings, and anti-weakening verdict are represented faithfully
- T4 target_progress does not promote checkpoint candidates to completion
- Lean formalization quality audit is represented faithfully
- Formal/AG is not directly edited
- protected math docs and docs/note are not edited
- PR body uses Refs for the tracking Issue unless the human explicitly requested closure
Return the review-pr verdict and target-theorem-loop-specific findings.
```

## T6 math-lean-review completion gate

```text
Run $math-lean-review research/GOALS.md <goal-id> with 4 parallel subagents.
Inputs to prepare: GOAL target theorem claim, candidate Lean declarations, relevant files, proof artifacts, tracking Issue proof state, T3/T3.5/T4/T5 audits.
Do not pass an expected verdict.
After the review, integrate only the verdict and evidence summary into the target completion ledger.
If $math-lean-review does not run with 4 parallel reviewer lanes, or if the verdict is not `No major findings`, return target-proof-checkpoint rather than target-theorem-proved.
Return:
verdict: target-theorem-proved | target-proof-checkpoint | target-refuted | target-blocked
math_lean_review_verdict:
math_lean_review_gate: pass | fail
target_proved_gate: pass | fail | cannot-determine
completed_support_nodes:
remaining_support_nodes:
proof_blockers:
next_best_action:
reason:
checked:
unchecked:
```
