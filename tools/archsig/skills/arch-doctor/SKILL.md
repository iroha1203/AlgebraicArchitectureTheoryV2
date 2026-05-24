---
name: arch-doctor
description: Diagnose architecture state and likely evolution from ArchSig, ArchMap, AIR, SFT, ForecastCone, ConsequenceEnvelope, policy, and calibration artifacts. Use when Codex is asked to interpret tool outputs, explain current architecture health, identify risks or missing evidence, forecast codebase evolution, or recommend bounded next design actions from ArchSig / ArchMap results.
---

# Arch Doctor

## Purpose

Read ArchSig and ArchMap artifacts as bounded architecture evidence. Produce a concise diagnosis of current architecture state, likely evolution, missing evidence, and next design actions without turning tool outputs into proofs or causal claims.

## Inputs To Prefer

Use the richest available artifacts first:

- `archmap-validation-report-v0`
- `operation-support-estimate-v0`
- `forecast-cone-skeleton-v0`
- `consequence-envelope-report-v0`
- `signature-diff-report-v0`
- `feature-extension-report-v0`
- `policy-decision-report-v0`
- `theorem-precondition-report-v0`
- `forecast-calibration-hook-v0`
- Sig0 and validation reports

If artifacts are missing, ask to run `$archsig-executer` or run it when appropriate.

This skill must work from generated artifacts and the skill bundle alone. Do not require the ArchSig
source repository, docs, fixtures, or Rust code to be present.

For non-trivial diagnosis:

- read `references/artifact-reading-guide.md` to identify what each artifact can and cannot support
- read `references/diagnosis-playbook.md` to choose the diagnosis path
- read `references/report-template.md` to format the final diagnosis

## Diagnosis Workflow

1. Establish evidence boundary.
   - Identify source artifacts, measured axes, unmeasured axes, private or unavailable refs, unknown remainders, and non-conclusions.
   - Separate current-state observations from forecast or recommendation.

2. Read current architecture state.
   - Use measured structural axes, policy violations, semantic coverage, conflicts, theorem precondition status, and feature report split status.
   - Treat missing evidence as uncertainty, not as a clean bill of health.
   - Treat warnings as review cues.

3. Read SFT-facing evolution signals.
   - Use operation families, candidate supports, forecast cone path classes, consequence envelope recommendations, and calibration refs.
   - Describe likely pressure directions and bounded consequences, not point predictions.
   - Do not claim incident causality, global safety, quality ranking, or forecast correctness.

4. Recommend next actions.
   - Prefer actions that reduce uncertainty or preserve architecture invariants.
   - Distinguish code changes, documentation changes, tests, runtime evidence collection, policy calibration, and Lean proof work.
   - Tie each recommendation to artifact evidence or mark it as an assumption.

## Output Shape

Use this structure for non-trivial diagnoses:

```text
Current state
- ...

Evolution forecast
- ...

Evidence gaps
- ...

Recommended next actions
- ...

Non-conclusions
- ...
```

Keep the answer direct. Cite artifact paths and important ids when available. Do not dump raw JSON unless the user asks for it.

## Interpretation Rules

- `metricStatus.measured = false` means unmeasured, even if the numeric value is `0`.
- `archmap-v0` is LLM-authored mapping evidence, not ground truth.
- `archmap` validation checks structure, references, and boundary; it does not prove semantic preservation.
- `theorem-check` reports precondition status; it does not discharge Lean proofs.
- `ForecastConeSkeleton` is a bounded forecast artifact; it is not a probability distribution or point prediction.
- `ConsequenceEnvelope` is a report projection; it is not a causal proof.
- Calibration artifacts connect predictions to observations; they do not by themselves establish causality.

## Escalation

Recommend creating issues when the diagnosis finds:

- a high-risk architecture conflict with clear evidence
- missing runtime or framework evidence that blocks interpretation
- repeated unmeasured axes that make the report misleading
- theorem preconditions that are close enough to formalize
- forecast items that need calibration after implementation

Use Japanese for user-facing reports in this repository, unless the user asks otherwise.
