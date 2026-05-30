---
name: law-policy-creater
description: Create and validate ArchSig law-policy-v0 artifacts from repository coding conventions, architecture rules, review policies, and user decisions. Use when Codex is asked to draft, update, or review a LawPolicy / interpretation_profile.json for ArchSig; derive laws, witness rules, signature axes, coverage requirements, and exactness assumptions from repo docs or coding standards; ask the user to decide missing architecture laws when no documentation exists; or prepare a project-specific LawPolicy before running ArchMap through ArchSig.
---

# LawPolicy Creater

## Purpose

Create a project-specific `law-policy-v0` artifact for ArchSig.

LawPolicy is not a harmless default. It selects the law universe, witness rules, signature axes, coverage requirements, exactness assumptions, and non-conclusions used by ArchSig. Changing LawPolicy changes what ArchSig can read as obstruction, nonzero signature axis, flatness pressure, repair candidate, or non-conclusion.

This skill must work with only:

- this skill directory, including `references/`
- a built `archsig` executable when validation is requested
- the user's repository files, ArchMap, docs, and direct answers

Do not require the ArchSig source repository, AAT mathematical documents, test fixtures, Cargo project files, or Git history. Those may help during development, but they are not runtime dependencies for the released skill bundle.

## Inputs

Collect:

- target repository root
- intended LawPolicy path, usually `.archsig/<scope>/law_policy.json` or `.archsig/<scope>/interpretation_profile.json`
- ArchMap path if available
- repository docs or coding convention files
- user goal: strict review, baseline diagnosis, release gate, migration planning, subsystem-specific analysis, or exploratory research
- human intent for ACTS readings: what architectural pressure should be measured, which review decision the spectrum report should support, and which claims must be excluded
- repository evidence for ACTS: source refs, docs, tests, traces, ArchMap observations, selected axes, witness rules, and known coverage gaps

If no output path is supplied, prefer `.archsig/<scope>/law_policy.json` next to the ArchMap.

## Convention Discovery

Search repository-owned evidence before asking broad questions.

Read `references/convention-survey.md` when the repo is unfamiliar. Look for:

- `AGENTS.md`, `CLAUDE.md`, `.cursorrules`, `.github/copilot-instructions.md`
- `README*`, `CONTRIBUTING*`, `ARCHITECTURE*`, `docs/**`
- coding style configs such as `pyproject.toml`, `ruff.toml`, `.eslintrc*`, `tsconfig.json`, `go.mod`, `Cargo.toml`
- framework routing / dependency conventions
- security / permission / tenancy / transaction / provider-boundary docs
- test strategy docs and CI workflow files

Classify evidence:

- **Normative**: must/shall/required, architectural decision records, coding standards, policy docs, CI gates.
- **Conventional**: repeated patterns in source, framework idioms, naming conventions, review habits.
- **Observed only**: current implementation without a stated rule.
- **Missing**: no repo evidence.

Only normative or explicitly user-approved conventions should become selected laws. Conventional or observed-only evidence can become coverage requirements, review assumptions, or question prompts.

For ACTS / spectrum work, do not ask the user to hand-author a large JSON profile. Build the profile from:

- human intent: which review decision the report should support
- repository evidence: docs, source refs, tests, traces, and ArchMap observations
- selected laws and axes: only repo/user-approved rules become law obligations
- inferred measurement fields: selected axis refs, measured witness rule refs, distance kinds, weight policy, support projection, transfer edge rule, clustering/ranking, report focus
- unresolved questions: missing law approval, missing source evidence, missing runtime traces, uncalibrated weights, or ambiguous zero-reflection assumptions

Keep these as explicit authoring notes in the delivery, and encode them in the LawPolicy fields that carry scope, descriptions, coverage boundaries, exactness assumptions, excluded readings, and non-conclusions. Do not add ad hoc top-level JSON fields outside `law-policy-v0`.

## Ask When Docs Are Missing

If no clear normative source exists, stop before inventing laws and ask the user targeted questions. Use `references/question-bank.md`.

Ask for decisions such as:

- Which dependency directions must hold?
- Which permission / tenancy boundaries are mandatory?
- Which state/effect ordering, idempotency, retry, and finalization contracts matter?
- Which provider / LLM / external integration outputs must be mediated?
- Which semantic contracts are important enough to count as selected laws?
- Which evidence is required before a zero axis can be trusted?

Record user answers as source evidence in the LawPolicy scope or in an accompanying note. Do not silently promote your own preference into LawPolicy.

## Authoring Workflow

1. Define scope.
   - Write `lawPolicyId`, `policyVersion`, `scope`, and `archmapSchemaRef`.
   - Make the scope narrow enough to be defensible. Prefer subsystem-specific policy over vague repository-wide policy when evidence is partial.

2. Select laws.
   - A selected law is a user/repo-approved architectural expectation, not a detected violation.
   - Each law needs `lawId`, `lawFamily`, `description`, `enforcementBoundary`, `appliesToAtomFamilies`, `requiredWitnessRefs`, `requiredAxisRefs`, and non-conclusions.

3. Define axes.
   - Add one `requiredZeroAxes[]` entry for each law-backed axis expected to be zero.
   - Use `optionalAxes[]` for auxiliary review dimensions that are useful but not selected zero obligations.
   - Zero means "no witness constructed under declared evidence and exactness assumptions", not global correctness.

4. Define witness rules and obstruction circuits.
   - Witness rules describe what ArchSig may construct from observed ArchMap atoms.
   - Obstruction circuit definitions connect witness rules to circuit kinds and signature axes.
   - Do not put concrete findings or ArchMap observation ids into the policy unless the policy is intentionally scoped to a fixed fixture. Normally leave `atomObservationRefs` empty.

5. Define molecule patterns.
   - Use molecule patterns to name role interpretations over atoms, such as layered component, operation contract, tenant boundary, provider mediation, transaction boundary, or source-domain artifact.
   - A molecule pattern is not a primitive atom.

6. Define coverage and exactness.
   - Coverage requirements are first-class. They say what evidence must be present before zeros reflect the selected policy.
   - Missing coverage must report a gap and block zero-reflection.
   - Add exactness assumptions that limit witness completeness.

7. Define measurement policy and ACTS spectrum profile.
   - `measurementPolicy` selects the axis set, distance kind, weight policy, ArchMapStore ref kinds, measurement boundary, exactness assumptions, and non-conclusions for general ArchSig readings.
   - Add `spectrumMeasurementProfile` when the user wants Architecture Curvature Transfer Spectrum / ArchitectureSpectrumReport readings.
   - Select `selectedAxisRefs` from LawPolicy axes, not from a desired finding.
   - Select `measuredWitnessRuleRefs` from witness rules that are backed by repo/user-approved laws.
   - Choose `distanceKinds[]` per axis, such as boolean mismatch, witness mismatch count, support overlap, or project-specific calibrated distance.
   - Keep `weightPolicy` conservative unless calibration evidence exists. Prefer unit weights or explicitly bounded weights over invented severity scores.
   - Use `supportProjectionRule` to explain how witness support is projected to Atom refs and selected axes.
   - Use `transferEdgeRule` to explain when transfer edges may be constructed. Do not use source proximity alone as transfer evidence unless the user/repo selected that rule.
   - Use `clusteringRankingOptions` and `reportFocusOptions` to state how ArchSig should surface top modes, witness clusters, coverage gaps, and review focus.
   - Preserve unmeasured axes and missing evidence as coverage gaps. Do not treat absent support as zero.

8. Add non-conclusions.
   - Preserve these boundaries: LawPolicy is selected analysis policy, not AAT itself; validation does not prove architecture lawfulness or atom truth; missing coverage is not measured zero; signature zero requires ArchSig analysis with coverage and exactness assumptions.

9. Validate.
   - Run `archsig law-policy`.
   - Treat ArchSig validation as the authoritative schema, reference, uniqueness, coverage, exactness, and non-conclusion check.

## Commands

Resolve the ArchSig binary only when validation or fixture emission is needed:

1. use `ARCHSIG_BIN` when set
2. use `archsig` from `PATH`
3. look for released binaries near the skill bundle, such as `bin/archsig`, `../bin/archsig`, or `../../bin/archsig`
4. if working inside a source checkout, optionally use an already-built checkout binary such as `tools/archsig/target/release/archsig` or `tools/archsig/target/debug/archsig`

ArchSig validation:

```bash
${ARCHSIG_BIN:-archsig} law-policy \
  --input <law_policy.json> \
  --out <law-policy-validation.json>
```

If no binary exists, report that validation was not performed. Do not substitute a separate local checker for ArchSig validation.

Use `references/starter_law_policy.json` as a structural starting point, not as an analysis default. Replace ids, laws, axes, witness rules, coverage requirements, and scope with project-specific decisions.

## Output Shape

When delivering a LawPolicy, include:

1. LawPolicy path
2. Evidence summary: docs read, conventions found, user answers used
3. Intent summary: review decision, ACTS measurement goal, and excluded claims
4. Selected laws and why they are in scope
5. Signature axes and zero-reading boundaries
6. `spectrumMeasurementProfile`: selected axes, witness rules, distance kinds, support projection, transfer edge rule, ranking/report focus, coverage boundary
7. Inferred fields and evidence used for each inference
8. Coverage requirements and exactness assumptions
9. Open questions / unresolved policy decisions
10. Validation result

Use concise Japanese when working in this repository.

Avoid:

- using a generic policy as project analysis
- turning current code shape into law without docs or user approval
- inventing selected laws, selected axes, distance kinds, weights, or transfer rules without repo evidence, ArchMap evidence, or explicit user intent
- treating LawPolicy validation as architecture lawfulness
- treating absent evidence as measured zero
- mixing FieldSig forecast / governance claims into ArchSig LawPolicy

## References

- `references/schema-guide.md`: LawPolicy field guide and cross-reference rules
- `references/convention-survey.md`: how to find repo coding conventions
- `references/question-bank.md`: questions to ask when docs are missing
- `references/starter_law_policy.json`: structural JSON starter template

## Maintainer Validation

When editing this skill inside a source checkout, validate the starter policy with ArchSig:

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- law-policy \
  --input tools/archsig/skills/law-policy-creater/references/starter_law_policy.json \
  --out .lake/law-policy-creater-starter-validation.json
```

If the skill-creator validator is available, run it too. If it is missing dependencies such as `PyYAML`, report that as an environment issue rather than a skill runtime blocker.
