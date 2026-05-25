---
name: aat-reviewer
description: Review ArchSig AAT Observable Bundle artifacts and translate AAT concept evidence into bounded design review actions. Use when Codex is asked to review AAT-facing ArchSig artifacts, explain invariant/witness/signature/operation/boundary evidence, or decide next evidence for architecture review.
---

# AAT Reviewer

## Purpose

Read `aat-observable-bundle-v0` and related ArchSig artifacts as AAT-facing review evidence.
This skill turns deterministic evidence into review cues while preserving the boundary between
tooling evidence, LLM judgment, human review, and Lean proof.

## Inputs To Prefer

- `aat-observable-bundle-v0` and validation report
- AIR and AIR validation
- `archmap-v0` and ArchMap validation report
- theorem-check report
- Feature Extension Report
- `obstruction-witness-v0`
- PR quality analysis and policy decision reports

## Workflow

1. Validate the bundle before using it.

```bash
${ARCHSIG_BIN:-archsig} aat-observable-bundle \
  --input .archsig/aat/aat-observable-bundle.json \
  --out .archsig/aat/aat-observable-bundle-validation.json
```

2. Read the AAT concept coverage.
   - Check `conceptMappings` for ArchitectureObject / ComponentUniverse, ObstructionWitness,
     TheoremBoundary / NonConclusion, ArchitectureOperation, Projection / Observation / LSP / DIP,
     FeatureExtension, semantic diagram, state/effect law, repair/synthesis, and analytic axis.
   - Treat out-of-scope concepts as explicit boundaries, not missing implementation failures.

3. Separate evidence states.
   - `measuredZero` means measured zero only inside the selected universe.
   - `measuredNonzero` means selected evidence found a witness or nonzero axis.
   - `unmeasured`, `outOfScope`, `private`, `unavailable`, `unsupported`, and `dynamicBlindSpot`
     are not measured zero.

4. Translate `nonConclusions`.
   - Evidence gap: ask for the next artifact or measurement.
   - Non-finding: state that no selected evidence was found without claiming global absence.
   - Blocked formal claim: do not promote tooling evidence to Lean proof.
   - Review guardrail: keep semantic, runtime, static, and analytic surfaces separate.
   - Next evidence: name the smallest artifact that would improve the review.

5. Produce bounded review output.
   - Tie every finding to `sourceRefs`, `witnessCatalog`, `operationCandidates`,
     `theoremBoundaries`, or `reviewActions`.
   - Use `llmReviewSurface.reviewQuestions` as the question template.
   - Leave risk acceptance, product decision, and merge approval to human review.

## Output Shape

```text
AAT review state
- ...

Measured witnesses
- ...

Evidence gaps and guardrails
- ...

Operation / repair interpretation
- ...

Next evidence
- ...

Non-conclusions
- ...
```

Use Japanese for user-facing reports in this repository, unless the user asks otherwise.
