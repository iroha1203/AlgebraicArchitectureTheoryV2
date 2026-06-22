# Research Loop Subagent Prompts

このファイルは `research-loop` skill のサブエージェント標準プロンプト集である。サブエージェントを起動するときだけ、対応するゲートの見出しを読んで使う。

期待する結論、本体の推測、採点意図、成功させたい候補は追記しない。必要なパス、PR 番号、候補名だけを置換する。

## サブエージェント標準プロンプト

各サブエージェントには、次のプロンプトを必要なパス、PR 番号、候補名に置換して渡す。期待する結論や本体の推測は追記しない。

**G1 候補生成**

G1 では四体に次の探索ロールを一つずつ割り当てる。同じ agent に複数ロールを渡さない。

- `closer`: 既存 frontier、report、open gap を読み、最も強い closure / computability / exactness 候補を探す。ただし定義展開や小補題量産は避ける。
- `obstruction`: spine や直近成果の弱点を壊す counterexample、nonfaithfulness、failure mode、必要条件、no-go result を探す。
- `unifier`: 複数の現象を一つの構成、不変量、duality、coherence criterion、bridge として圧縮する候補を探す。
- `wildcard`: 高リスク高リターンの orientation / genius-target / rival-axis rewrite を探す。証拠計画がない願望は出さない。

```text
Use the research-loop criteria to generate candidate research contributions for GOAL <goal-id>.
Your G1 exploration role is: <closer | obstruction | unifier | wildcard>.
Read only: research/GOALS.md, research/ideas/TEMPLATE.md, research/reports/<goal-id>.md if it exists, the tracking Issue summary supplied by the main agent, and the source references explicitly named by the GOAL.
Do not edit files.
Search from your assigned role. Do not imitate the other G1 roles, and do not converge to the safest obvious spine-filling candidate unless your role makes it genuinely strongest.
Generate mathematically nontrivial, interesting candidates that create visible progress toward the GOAL. Avoid definition unfolding, immediate corollaries, renaming, vague conjectures, and candidates whose value is only that they look easy to formalize.
Also consider whether there is a rare genius candidate. Do not force one; return `genius_potential: no` for ordinary candidates.
If an open `genius target theorem` exists in the tracking Issue, include at least one candidate that advances that target, or explain why another candidate should take priority.
If the user explicitly asked for breakthrough / genius work and no open target exists, include at least one `genius-target` candidate or explain why no credible target exists.
For each candidate, stress-test it against every rival named by the GOAL, including any strong rival. Do not assume a fixed rival list.
Return at least 1 candidate and preferably 3 candidates.
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

**G2 審判 A: 厳密性**

```text
Judge this candidate only for rigor and boundary fidelity.
Inputs: GOAL <goal-id>, candidate card <path>, reward rubric, dullness filter, tracking Issue genius target/support summary when relevant, and named source references.
Do not assume the candidate should pass.
If the candidate asks for genius scoring, judge whether it is mathematically rigorous enough to be a rare 1000-point breakthrough without crossing the claim boundary.
If this is a genius-target or genius-support candidate, judge whether the target theorem, support map, and current support role are mathematically coherent.
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

**G2 審判 B: 研究価値**

```text
Judge this candidate only for research value toward GOAL <goal-id>.
Inputs: GOAL, candidate card <path>, reward rubric, dullness filter, current report if any, and tracking Issue genius target/support summary when relevant.
Do not judge by ease of proof. Judge by surprise, compression, leverage, and GOAL capability gain.
If the candidate asks for genius scoring, judge whether it changes AAT's view or research program enough to deserve rare 1000-point treatment.
If this is a genius-target or genius-support candidate, judge whether the target theorem creates a strong research game board and whether this cycle advances it.
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

**G2 審判 C: プロジェクト全体価値**

```text
Judge this candidate from the viewpoint of the whole repository and research program.
Inputs: GOAL <goal-id>, candidate card <path>, reward rubric, dullness filter, tracking Issue genius target/support summary when relevant, research/README.md, research/GOALS.md, docs/README.md, and other repo overview files explicitly named by the GOAL.
Do not judge only local mathematical interest. Judge whether this is valuable for AAT / SFT / Tooling / Website / Research as a whole.
If the candidate asks for genius scoring, judge whether it creates a project-level bridge across multiple domains rather than an isolated local result.
If this is a genius-target or genius-support candidate, judge whether the target/support structure is useful for the broader research program rather than bookkeeping.
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

**G2 審判 D: ライバル比較**

```text
Judge this candidate only against the GOAL's rival field.
Inputs: GOAL <goal-id>, its rival field, candidate card <path>, reward rubric, dullness filter, current report if any, and tracking Issue genius target/support summary when relevant.
Do not judge by mathematical elegance alone. Judge whether the candidate creates a capability that the named rival(s) do not provide, combines rival capabilities into a stronger object, or gives a precise failure / nonfaithfulness / obstruction that the rival misses.
If the GOAL names multiple rivals or a strong rival, compare against each named rival separately before giving the overall verdict.
If the candidate asks for genius scoring, judge whether it rewrites the comparison axis itself rather than merely outperforming the rival on an existing metric.
If this is a genius-target or genius-support candidate, judge whether the target theorem would create a new comparison axis against the rival, and whether this support cycle materially advances that axis.
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

**G3 公理検査**

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

**G3 Lean 形式化品質監査**

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

**G3.5 候補カード同期**

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

**G4 SCORE 監査**

```text
Audit the final SCORE for candidate <candidate>.
Inputs: GOAL <goal-id>, GOAL rival, synchronized candidate card <path>, evidence files, G2 judge A/B/C/D outputs, G3 axiom check, G3 formalization quality audit, G3.5 sync audit, tracking Issue SCORE/support ledger, and current diff.
Do not preserve the proposed score unless the evidence supports it.
If genius scoring is proposed, confirm it only when all four G2 judges returned `genius_eligibility: yes` and the evidence shows a rare 1000-point breakthrough. Otherwise set `genius_verdict: downgrade-to-normal` and score on the normal 0-100 base scale.
If the candidate is a genius-target or genius-support cycle, audit target/support accounting separately from SCORE: target seeding does not unlock 1000 points by itself, support cycles score normally, and genius unlock requires the target theorem evidence to pass G2/G3/G4. If a genius-target is useful only as a research-program seed and has insufficient evidence for normal SCORE, return `score_verdict: seed-only`, `base_score: 0`, `final_score: 0`, and record the target/support map to the tracking Issue only.
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

**G5 PR レビュー**

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

**G6 フェーズ区切り判定**

```text
Judge whether the current work forms a good research phase boundary for GOAL <goal-id>.
Inputs: GOAL, GOAL rival, tracking Issue active threshold, tracking Issue SCORE ledger, research/reports/<goal-id>.md, category scores, evidence stages, phase boundary criteria.
Treat research/GOALS.md as a read-only invariant. If status, threshold policy, rubric, frontier, or spine should change, return that as a human action proposal. Treat active threshold changes as tracking-Issue state changes, not GOALS.md edits.
Do not judge the GOAL as completely achieved. Do not close the tracking Issue. Judge whether this phase is coherent enough to stop and return to the human with a phase summary.
Return:
verdict: phase-boundary | continue | blocked | goal-defect
total_score:
active_threshold:
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
