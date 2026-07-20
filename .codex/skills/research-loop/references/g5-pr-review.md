# Research Loop G5 PR Review

## G5 PR レビュー

`$review-pr <PR-number>` を実行するときは、通常の PR review に加えて
次の research-loop gate を確認対象として渡す。

- candidate card, evidence, report, and tracking Issue SCORE update agree
- SCORE audit is represented faithfully
- G2 judge D rival comparison and G4 rival_delta are represented faithfully
- Lean formalization quality audit is represented faithfully
- Formal/AG is not directly edited
- protected math docs and docs/note are not edited
- accepted Research evidence is recorded in the tracking Issue or acceptance report
- git diff --check, git diff --cached --check, and untracked-file hygiene were checked
- PR body uses Refs for the tracking Issue unless the human explicitly requested closure
- GitHub merge state is verified after merge attempts
Return the review-pr verdict and any research-loop-specific findings.
