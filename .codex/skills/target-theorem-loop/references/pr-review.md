# Target Theorem Loop PR Review

## PR review

`$review-pr <PR-number>` を実行するときは、通常の PR review に加えて
次の target-theorem-loop gate を確認対象として渡す。

- cycle result is represented faithfully in report and tracking Issue
- proof obligation delta, premise_delta, blocking_findings, and next_obligation are represented faithfully
- no candidate card or SCORE state is introduced
- completion_candidate is not promoted to target-theorem-proved without $math-lean-review
- Lean evidence, axiom audit, placeholder scan, and anti-weakening audit are represented faithfully
- certificate provenance, proof-use audit, and structure-field escape audit are represented faithfully
- route-integrity and cheat-route audit are represented faithfully
- explicit certificate arguments are not promoted to premise discharge without a construction theorem / finite witness / reviewed predecessor theorem
- selected object / cover / coefficient / certificate choices are not accepted as completion without input-boundary construction, canonical/free characterization, universal property, or nonvacuity/adequacy evidence
- Formal/AG is not directly edited
- protected math docs and docs/note are not edited
- accepted Research evidence is registered in docs/aat/research_evidence_index.md
- PR body uses Refs for the tracking Issue unless the human explicitly requested closure
Return the review-pr verdict and target-theorem-loop-specific findings.
