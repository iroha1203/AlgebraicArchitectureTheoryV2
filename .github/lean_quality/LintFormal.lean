import Formal.AG

/-!
Lean quality-standard lint entrypoint for `docs/aat/lean_quality_standard.md` §7.

The CI wrapper compares this output against
`.github/lean_quality/lint-formal-baseline.txt`, so existing findings remain
fixed as baseline and only output drift fails the check.
-/

#lint- only unusedArguments docBlame synTaut unusedHavesSuffices dupNamespace impossibleInstance defLemma in Formal
