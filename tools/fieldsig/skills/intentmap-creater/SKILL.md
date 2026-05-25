---
name: intentmap-creater
description: Create bounded IntentMap artifacts from Epic, PRD, Spec, Issue, or proposal text. Use when Codex is asked to draft, generate, update, or validate an intentmap-v0 JSON file, extract product or planning intent, record missing decisions or ambiguous intents, or prepare input for IntentMap x ArchMap planning forecast.
---

# IntentMap Creater

## Purpose

Create `intentmap-v0` as bounded LLM-authored intent evidence. Treat IntentMap as a source-to-intent mapping artifact for Epic / PRD / Spec planning workflows, not as implementation plan completeness, forecast correctness, product truth, or causal diagnosis.

## Inputs

Collect only evidence the user allows and record the boundary explicitly:

- Epic, PRD, Spec, Issue, proposal, meeting note, or planning text
- included refs, excluded refs, private refs, unavailable refs, and known blind spots
- requested planning scope and horizon when provided
- model or prompt provenance when reproducibility matters

This skill must work with only the skill bundle and a built `archsig` executable. Do not require the ArchSig source repository, `docs/tool`, or test fixtures to be present.

Use this command form by default:

```bash
${ARCHSIG_BIN:-archsig} <command> ...
```

## Workflow

1. Establish the source universe.
   - List the source documents and sections that were read.
   - Preserve excluded, private, and unavailable refs.
   - Do not infer product decisions from documents that were not read.
   - Read `references/intent-extraction-guide.md` for non-trivial PRD / Epic extraction.
   - Read `references/schema-cheatsheet.md` when field values are unclear.
   - Compare with `references/examples.md` when checking output shape.

2. Draft `intentmap-v0`.
   - Use `items[]` as the unit of requirement, operation, workflow, state, transition, invariant, acceptance, non-goal, or ambiguity.
   - Keep `intentItemId`, `intentKind`, `sourceRefs`, `targetIntentRef`, `preserves`, `forgets`, `claimClassification`, `confidence`, `requiredAssumptions`, `missingDecisions`, `missingEvidence`, and `nonConclusions` explicit.
   - Put unresolved product choices in `missingDecisions[]`; do not fill them with guesses.
   - Put ambiguous wording in `ambiguousIntents[]`; do not convert it to measured support.
   - Keep confidence as review priority, not probability.

3. Validate the result.

```bash
${ARCHSIG_BIN:-archsig} intent-map \
  --input <intentmap.json> \
  --out .archsig/intent/intentmap-validation.json
```

4. Read the validation report before handing the artifact downstream.
   - Treat failures as schema or boundary problems to fix.
   - Treat warnings as review cues.
   - Preserve missing decisions, ambiguous intents, missing evidence, and non-conclusions.

## Writing Rules

- Preserve uncertainty in fields; do not erase it in prose.
- Never claim that IntentMap is the correct interpretation of the PRD.
- Never claim that IntentMap is an implementation plan.
- Never put forecast cone results, effort estimates, future probabilities, resolved product decisions, or PR merge advice into IntentMap.
- Do not write implementation progress into PRDs. Use issues, roadmaps, or PRs for status.

## Handoff

Use `$arch-intent-forecaster` after this skill when the user asks to align IntentMap with current ArchMap, generate forecast artifacts, or interpret planning consequences.
