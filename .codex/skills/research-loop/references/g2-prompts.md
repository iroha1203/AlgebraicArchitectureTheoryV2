# Research Loop G2 Prompts

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
