# Diagnosis Playbook

Use this playbook to decide how to analyze ArchSig / ArchMap artifacts.

## Decision Table

| User asks for | Primary artifacts | Diagnosis focus |
| --- | --- | --- |
| "current architecture state" | Sig0, validation, ArchMap validation, feature report | measured structure, semantic coverage, conflicts, unmeasured axes |
| "what changed" | signature diff, snapshots, feature report | deltas, regressions, improvements, unmeasured deltas |
| "is this ArchMap trustworthy" | ArchMap validation | source refs, missing evidence, conflicts, guardrails, non-conclusions |
| "can this become Lean proof" | theorem-check, ArchMap validation | precondition status, blocked fields, required assumptions |
| "future evolution" | operation support, forecast cone, consequence envelope | bounded path classes, pressure directions, unknown remainder |
| "what should we do next" | consequence envelope, policy decision, feature report | actions that reduce risk or uncertainty |
| "calibrate forecast" | calibration hook, observed refs, consequence envelope | forecast item refs and observed outcome refs |

## Current-State Diagnosis

1. Identify artifact set and versions.
2. Summarize measured axes and measured layers.
3. Summarize unmeasured axes, unsupported constructs, private/unavailable refs.
4. List conflicts and validation warnings.
5. Identify architecture invariants or policies touched.
6. State what is known, what is assumed, and what is unknown.

Do not infer health from absence of measured violations if key axes are unmeasured.

## Evolution Forecast Diagnosis

1. Read `operation-support-estimate-v0`.
   - operation families
   - workflow/state/event candidates
   - unknown remainder
   - forbidden or unsupported supports

2. Read `forecast-cone-skeleton-v0`.
   - path class candidates
   - bounded horizon
   - forecast boundary
   - missing support

3. Read `consequence-envelope-report-v0`.
   - consequence surfaces
   - obstruction candidates
   - recommendations
   - CI/review implications

4. Produce bounded forecast language.
   - "likely pressure direction"
   - "bounded consequence surface"
   - "review priority"
   - "needs calibration"

Do not produce point predictions, probabilities, incident causality, or quality rankings unless a separate artifact explicitly supports them, and even then preserve its boundary.

## Recommendation Strategy

Prioritize actions in this order:

1. Fix validation failures that block artifact trust.
2. Add missing evidence that would change interpretation.
3. Reduce unmeasured high-risk axes.
4. Address clear policy or architecture conflicts.
5. Add tests or runtime traces for semantic/runtime claims.
6. Split or clarify components when feature reports show hidden interaction or mixed responsibility.
7. Create Lean proof obligations only when theorem preconditions are close and source evidence is stable.
8. Add calibration hooks for forecast items that will be observable later.

Each recommendation should include:

- evidence source or artifact id
- expected effect
- boundary or assumption
- whether it is code, docs, tests, runtime evidence, policy, or Lean work

## Handling Missing Artifacts

If artifacts are missing:

- If the user wants execution and `archsig` is available, hand off to `$archsig-executer`.
- If execution is not requested or the binary is unavailable, analyze only supplied artifacts.
- Make missing artifact impact explicit.

Example:

```text
No forecast cone artifact is supplied, so I can analyze operation support candidates but cannot describe path-class evolution.
```

## Stop Conditions

Stop analysis when:

- the artifact boundary has been summarized
- major risks and missing evidence are identified
- recommendations are tied to evidence
- non-conclusions are explicit

Do not keep expanding into code review unless the user asks for implementation-level investigation.
