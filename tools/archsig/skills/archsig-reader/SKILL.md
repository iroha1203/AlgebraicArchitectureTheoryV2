---
name: archsig-reader
description: Run or read current ArchSig measurement output, then translate summary, insight, viewer, manifest, compare, and gate artifacts into bounded source-level review language.
---

# ArchSig Reader

Use this skill to read current `archsig analyze` output.

## Workflow

1. Run `archsig analyze --archmap <archmap> --policy-bundle <bundle> --out-dir <run-dir>` when a bundle is supplied. Otherwise run `archsig analyze --archmap <archmap> --law-policy <policy> --measurement-profile <profile> --law-surface <law-surface> --out-dir <run-dir>`.
2. Read `archsig-analysis-summary.json`, `archsig-insight-report.json`, `archsig-atom-viewer-data.json`, `archsig-run-manifest.json`, and `archsig-measurement-packet.json`.
3. If comparing runs, read `archsig-comparison-report.json`.
4. If a gate report exists, read `archsig-gate-report.json`.
5. Compare high-priority findings with source evidence before recommending changes.
6. Check `componentFingerprints` in the packet and run manifest against the
   supplied policy bundle when one was used.

## Boundaries

- Do not infer beyond supplied ArchMap, LawPolicy, law-equation-surface, MeasurementProfile or policy-bundle, run output, and inspected source.
- Do not treat measurement output as merge approval, forecast truth, causal proof, or global architecture safety.
- Preserve unknown, unmeasured, not-computed, and violated-assumption states.
