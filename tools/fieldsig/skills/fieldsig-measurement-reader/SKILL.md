---
name: fieldsig-measurement-reader
description: Read FieldSig software-field-measurement and run manifest artifacts while preserving SFT claim boundaries.
---

# FieldSig Measurement Reader

Use FieldSig artifacts as workflow and software evolution measurement evidence. Treat ArchSig inputs as JSON artifact refs, not direct structural truth.

## Commands

```bash
${FIELDSIG_BIN:-fieldsig} software-field-measurement --input .fieldsig/software-field-measurement.json --out .fieldsig/software-field-measurement-validation.json
${FIELDSIG_BIN:-fieldsig} fieldsig-run-manifest --input .fieldsig/fieldsig-run-manifest.json --out .fieldsig/fieldsig-run-manifest-validation.json
```

## Boundaries

- Do not read FieldSig validation as forecast correctness.
- Do not treat correlation or operational feedback as causal proof.
- Do not replace CI, tests, or human review with FieldSig output.
