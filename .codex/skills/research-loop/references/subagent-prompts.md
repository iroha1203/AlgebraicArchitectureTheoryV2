# Research Loop Subagent Prompts

このファイルは `$research-loop` のサブエージェント標準プロンプト集である。サブエージェントを起動するときだけ、対応するゲートの見出しを読んで使う。

期待する結論、本体の推測、採点意図、成功させたい候補は追記しない。必要なパス、PR 番号、候補名だけを置換する。

## G1 候補生成

四体に `closer`、`obstruction`、`unifier`、`wildcard` を一つずつ割り当てる。

```text
Use the research-loop criteria to generate candidate research contributions for score-phase GOAL <goal-id>.
Your G1 exploration role is: <closer | obstruction | unifier | wildcard>.
Read only: research/GOALS.md, research/ideas/TEMPLATE.md, research/reports/<goal-id>.md if it exists, the tracking Issue summary supplied by the main agent, and source references explicitly named by the GOAL.
Do not edit files. Do not handle `research mode: target-theorem`; that belongs to $target-theorem-loop.
Generate mathematically nontrivial candidates that create visible progress toward the GOAL. Avoid definition unfolding, immediate corollaries, renaming, vague conjectures, and candidates whose value is only that they look easy to formalize.
Also consider whether there is a rare genius candidate. Do not force one. If you propose `genius`, `genius-target`, or `genius-support`, apply `references/genius-scoring.md`.
For each candidate, provide:
exploration_role:
title:
candidate_type: closure | orientation | unification | computability | bridge | genius | genius-target | genius-support
capability_category:
claim:
why_nontrivial:
mathematical_interest:
goal_advancement:
rival_advantage:
expected_base_score:
expected_evidence_multiplier:
expected_final_score:
genius_potential: yes | no
genius_target:
genius_support_role:
score_reason:
dullness_risk:
proof_or_evidence_plan:
planned_theorem_names:
visible_projection:
protected_structure:
exactness_or_minimality_claim:
nonfaithfulness_or_failure_mode:
previous_cycle_delta:
rival_stress_test:
checked:
unchecked:
```

## G2 審判 A: 厳密性

```text
Judge this candidate only for rigor and boundary fidelity.
Inputs: score-phase GOAL <goal-id>, candidate card <path>, reward rubric, dullness filter, tracking Issue genius target/support summary when relevant, and named source references.
Do not assume the candidate should pass. If the candidate asks for genius scoring, apply `references/genius-scoring.md` and judge whether it is mathematically rigorous enough to be a rare 1000-point breakthrough without crossing the claim boundary.
Return:
verdict: accept | revise | reject
base_score:
genius_eligibility: yes | no | cannot-determine
category:
reason:
boundary_fidelity:
is_immediate_corollary_or_rename:
proof_or_counterexample_risk:
required_evidence:
checked:
unchecked:
```

## G2 審判 B: 研究価値

```text
Judge this candidate only for research value toward GOAL <goal-id>.
Inputs: GOAL, candidate card <path>, reward rubric, dullness filter, current report if any, and tracking Issue genius target/support summary when relevant.
Do not judge by ease of proof. Judge by surprise, compression, leverage, and GOAL capability gain. If the candidate asks for genius scoring, apply `references/genius-scoring.md`.
Return:
verdict: accept | revise | reject
base_score:
genius_eligibility: yes | no | cannot-determine
category:
reason:
goal_delta:
surprise:
compression:
leverage:
paper_section_potential:
dullness_risk:
required_evidence:
checked:
unchecked:
```

## G2 審判 C: プロジェクト全体価値

```text
Judge this candidate from the viewpoint of the whole repository and research program.
Inputs: GOAL <goal-id>, candidate card <path>, reward rubric, dullness filter, tracking Issue genius target/support summary when relevant, research/README.md, research/GOALS.md, docs/README.md, references/genius-scoring.md when genius scoring is proposed, and other repo overview files explicitly named by the GOAL.
Return:
verdict: accept | revise | reject
base_score:
genius_eligibility: yes | no | cannot-determine
category:
reason:
repo_wide_value:
alignment_with_project_sources:
future_surface: docs | Lean | paper | tooling | website | none
strategic_risk:
dullness_risk:
required_evidence:
checked:
unchecked:
```

## G2 審判 D: ライバル比較

```text
Judge this candidate only against the GOAL's rival field.
Inputs: GOAL <goal-id>, its rival field, candidate card <path>, reward rubric, dullness filter, current report if any, and tracking Issue genius target/support summary when relevant.
Compare against each named rival separately before giving the overall verdict. If the candidate asks for genius scoring, apply `references/genius-scoring.md` and judge whether it creates or rewrites a rival comparison axis rather than merely outperforming a rival on an existing metric.
Return:
verdict: accept | revise | reject
base_score:
genius_eligibility: yes | no | cannot-determine
category:
reason:
rival_understanding:
rival_by_rival_delta:
advantage_over_rival:
novelty_against_rival:
recoverability_gap:
not_merely_rival_rephrasing:
required_evidence:
checked:
unchecked:
```

## G3 公理検査

```text
Check the Lean evidence for candidate <candidate>.
Inputs: candidate card <path>, Lean file <path>, GOAL claim boundary.
Run or inspect #print axioms for every declaration that will be reported as evidence.
For finite witness, computability, trace/support, repair frontier, or minimal counterexample claims, do not automatically treat propext/Classical.choice/Quot.sound as clean. If standard axioms remain, explain why the construction still deserves its evidence multiplier.
Confirm that Formal/AG is only imported/referenced and not edited by this loop.
Return:
verdict: pass | fail | cannot-determine
build_status:
axioms:
has_sorryAx:
allowed_axioms_only:
standard_axiom_justification:
fidelity_to_candidate:
formal_ag_boundary_ok:
reason:
checked:
unchecked:
```

## G3 Lean 形式化品質監査

```text
Audit whether the Lean formalization is an appropriate formal expression of the candidate's mathematical claim.
Inputs: candidate card <path>, Lean file <path>, GOAL claim boundary, and the relevant theorem / definition names.
Do not judge only whether Lean builds. Check whether the statement captures the intended proposition at the right strength.
Return:
verdict: pass | revise | fail | cannot-determine
statement_matches_candidate:
not_too_weak:
not_too_strong_or_vacuous:
parameters_and_assumptions_explicit:
claim_boundary_encoded:
definitions_fit_for_reuse:
names_and_structure_clear:
formal_ag_boundary_ok:
reason:
checked:
unchecked:
```

## G3.5 候補カード同期

```text
Audit whether candidate card <path>, Lean/evidence files, judge memos, and the planned report entry agree.
Inputs: GOAL <goal-id>, candidate card <path>, evidence files, G2 judge outputs including judge D rival comparison, G3 axiom check, G3 formalization quality audit, and tracking Issue SCORE/support ledger when relevant.
Do not change the score. Check synchronization only.
Return:
verdict: synced | revise | fail | cannot-determine
status_is_picked:
evidence_stage_matches:
lean_declarations_match:
expected_scores_not_stale:
proof_plan_reflects_actual_evidence:
exactness_minimality_or_failure_mode_reflected:
rival_separation_reflected:
axiom_and_formalization_audits_summarized:
resolved_revises_recorded:
genius_evidence_synced:
genius_target_or_support_synced:
report_names_match:
reason:
checked:
unchecked:
```

## G4 SCORE 監査

```text
Audit the final SCORE for candidate <candidate>.
Inputs: GOAL <goal-id>, GOAL rival, synchronized candidate card <path>, evidence files, G2 judge A/B/C/D outputs, G3 axiom check, G3 formalization quality audit, G3.5 sync audit, tracking Issue SCORE/support ledger, and current diff.
Do not preserve the proposed score unless the evidence supports it. If genius scoring is proposed, apply `references/genius-scoring.md`; confirm it only when all four G2 judges returned `genius_eligibility: yes`, the evidence shows a rare 1000-point breakthrough, and support-cycle SCORE is not being double-counted as the unlock score.
Return:
score_verdict: confirm | reduce | reject | seed-only
base_score:
evidence_multiplier:
penalty:
final_score:
category:
genius_verdict: confirm | downgrade-to-normal | reject | not-applicable
goal_delta:
rival_delta:
rival_stress_test:
project_value_delta:
formalization_quality:
research_kiri_contribution:
reason:
checked:
unchecked:
```

## G5 PR レビュー

```text
Use $review-pr <PR-number> and apply the review-pr skill.
In addition to the normal PR review, check the research-loop gates:
- candidate card, evidence, report, and tracking Issue SCORE update agree
- SCORE audit is represented faithfully
- G2 judge D rival comparison and G4 rival_delta are represented faithfully
- Lean formalization quality audit is represented faithfully
- Formal/AG is not directly edited
- protected math docs and docs/note are not edited
- git diff --check, git diff --cached --check, and untracked-file hygiene were checked
- PR body uses Refs for the tracking Issue unless the human explicitly requested closure
- GitHub merge state is verified after merge attempts
Return the review-pr verdict and any research-loop-specific findings.
```

## G6 フェーズ区切り判定

```text
Judge whether the current work forms a good research phase boundary for score-phase GOAL <goal-id>.
Inputs: GOAL, GOAL rival, tracking Issue active threshold, tracking Issue SCORE ledger, research/reports/<goal-id>.md, category scores, evidence stages, and phase boundary criteria.
If total_score >= active_threshold, treat this as `score-threshold reached` and judge whether it is a phase boundary. Do not judge the GOAL as completely achieved. Do not close the tracking Issue. Judge whether this phase is coherent enough to stop and return to the human with a phase summary. If you return `continue` despite threshold reach, state the exact missing portfolio constraint, report coherence, rival delta, or phase-boundary criterion.
Return:
verdict: phase-boundary | continue | blocked | goal-defect
total_score:
active_threshold:
threshold_reached: yes | no
portfolio_constraint:
coherent_report_or_paper_seed:
rival_phase_delta:
research_kiri:
phase_summary_required_fields:
tracking_issue_remains_open:
next_best_action:
reason:
checked:
unchecked:
```
