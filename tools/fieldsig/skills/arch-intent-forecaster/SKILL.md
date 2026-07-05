---
name: arch-intent-forecaster
description: Analyze Epic, PRD, Spec, or proposal planning forecast from IntentMap, ArchMap, AlignmentMap, operation support, ForecastConeSkeleton, ConsequenceEnvelope, and intent calibration artifacts. Use when Codex is asked to forecast likely codebase evolution, align product intent to architecture evidence, inspect missing decisions, or recommend planning actions from IntentMap x ArchMap evidence.
---

# Arch Intent Forecaster

## Purpose

Analyze Epic / PRD / Spec planning forecast. This skill simplifies ArchSig's IntentMap forecast surface for Codex: it may run the necessary `fieldsig` commands, read generated artifacts, and describe bounded evolution pressure without treating output as forecast correctness, implementation plan completeness, probability, or causal proof.

## Inputs To Prefer

- `intentmap-v0` and `intentmap-validation-report-v0`
- current ArchMap observation artifact and ArchMap validation report
- `intent-archmap-alignment-v0` and validation report
- `operation-support-estimate-v0`
- `forecast-cone-skeleton-v0`
- `consequence-envelope-report-v0`
- `sft-review-summary-v0`
- `intent-calibration-record-v0`

Do not use PR quality analysis as planning forecast unless the user explicitly asks to compare planning evidence with PR evidence.

## Minimal Execution Rules

- Use `${FIELDSIG_BIN:-fieldsig}` by default.
- Keep generated files under `.archsig/` unless the user specifies another directory.
- If `${FIELDSIG_BIN:-fieldsig} --help` fails, ask for `FIELDSIG_BIN=/path/to/archsig`.
- Stop downstream commands after an upstream failure.
- Do not require the ArchSig source repository.

## Workflow

1. Establish planning evidence boundary.
   - Identify source planning documents, current ArchMap, alignment artifact, missing decisions, ambiguous intents, unaligned intents, unsupported intents, private refs, and non-conclusions.
   - Read `references/forecast-playbook.md` for non-trivial forecast analysis.
   - Read `references/artifact-reading-guide.md` when artifact meaning is unclear.

2. Validate IntentMap and AlignmentMap.

```bash
${FIELDSIG_BIN:-fieldsig} intent-map \
  --input .archsig/intent/intentmap.json \
  --out .archsig/intent/intentmap-validation.json

${FIELDSIG_BIN:-fieldsig} intent-archmap-alignment \
  --input .archsig/intent/intent-archmap-alignment.json \
  --intent-map .archsig/intent/intentmap.json \
  --archmap .archsig/archmap/archmap.json \
  --out .archsig/intent/alignment-validation.json
```

3. Run bounded planning forecast when inputs are valid enough.

```bash
${FIELDSIG_BIN:-fieldsig} intent-forecast \
  --intent-map .archsig/intent/intentmap.json \
  --archmap .archsig/archmap/archmap.json \
  --alignment .archsig/intent/intent-archmap-alignment.json \
  --out-dir .archsig/intent/forecast
```

If only a ConsequenceEnvelope is available, project it to reviewer-facing SFT judgement input:

```bash
${FIELDSIG_BIN:-fieldsig} sft-review-summary \
  --consequence-envelope .archsig/intent/forecast/consequence-envelope-report.json \
  --out .archsig/intent/forecast/sft-review-summary.json
```

4. Validate or read calibration records when observed implementation refs are available.

```bash
${FIELDSIG_BIN:-fieldsig} intent-calibration-record \
  --input .archsig/intent/intent-calibration-record.json \
  --out .archsig/intent/intent-calibration-validation.json
```

5. Produce the forecast analysis.
   - Trace forecast signals back to IntentMap item refs and AlignmentMap boundaries.
   - Keep missing decisions, ambiguous intents, unsupported intents, and missing evidence separate.
   - Describe likely pressure directions and bounded consequences, not point predictions.
   - Translate unknown remainder, missing invariant, non-conclusion, and typed boundary failure into reviewer next actions.
   - For bounded LLM judgement, cite `sft-review-summary-v0` evidence refs and boundary refs.

## Output Shape

```text
Planning state
- ...

Evolution forecast
- ...

Evidence gaps
- ...

Recommended next actions
- ...

SFT review judgement
- opened futures:
- closed futures:
- boundary failures:
- next actions:

Non-conclusions
- ...
```

Use Japanese for user-facing reports in this repository, unless the user asks otherwise.
