# Research Loop G3 Prompts

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
