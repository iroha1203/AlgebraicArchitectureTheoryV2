# ArchSig Artifacts And Boundaries

ArchSig owns the LLM Atom ArchMap analysis surface:

```text
archmap-observation-map-v0
  + law-policy-v0
  -> archsig-analysis-summary.json
  -> archsig-atom-viewer-data-v0
  -> archsig-run-manifest-v0
  -> optional archsig-analysis-packet-v0 for FieldSig handoff
```

Git history is the archive for pre-Atom scan, projection, report, and PR-review
surfaces. They are not current ArchSig artifacts or commands.

ArchMap is LLM-authored source reading, not an AST extractor result. Static
artifacts such as ASTs, symbol indexes, import graphs, route lists, and
framework registries may support navigation, source inventory selection, and
gap discovery. They do not by themselves certify observed atoms, semantic
dependencies, runtime interactions, authority coverage, or extractor
completeness.

For large repositories, parallel agents may survey bounded surfaces and return
candidate observations. The final ArchMap still requires an integration pass
that deduplicates candidates, resolves source refs, preserves gaps, and promotes
only primitive source-grounded facts to `atomObservations`.

Large ArchMaps may be authored as horizontal bounded observation slices. This is
a review and authoring layout headed by `archmap-shard-manifest-v0`; the current
compatibility contract remains exported `archmap-observation-map-v0`. Current
ArchSig analysis commands consume the exported monolithic artifact, not slice
fragments.

## Current Artifacts

| artifact | schemaVersion | role |
| --- | --- | --- |
| ArchMap observation map | `archmap-observation-map-v0` | Source-grounded Atom observation evidence. It records `atomObservations`, `moleculeObservations`, `semanticObservations`, `observationGaps`, `projectionInfo`, `concernHints`, provenance, and non-conclusions. It is law-independent and does not own obstruction circuits, lawfulness, zero curvature, repair conclusions, or Lean theorem discharge. |
| ArchMap shard manifest | `archmap-shard-manifest-v0` | Planned authoring-side manifest for splitting large ArchMaps into horizontal bounded observation slices such as authority, state, effects, providers, runtime, domain, and governance. It is not a LawPolicy, runtime trace, or source inventory. It must bundle/export to `archmap-observation-map-v0` before current analysis. |
| ArchMap validation report | `archmap-validation-report-v0` | Checks schema support, identity, references, provenance, source refs, observation / concern guardrails, projection separation, gap boundaries, and formal-promotion non-conclusions. |
| LawPolicy | `law-policy-v0` | Selected LawUniverse / witness-rule / molecule-pattern / obstruction-definition / signature-axis policy for one review context. |
| LawPolicy validation report | `law-policy-validation-report-v0` | Checks LawPolicy identity, uniqueness, cross references, witness / obstruction guardrails, coverage requirements, exactness assumptions, and non-conclusions. |
| ArchSig analysis summary | `archsig-analysis-summary.json` | LLM-readable compact reading surface emitted by default from `analyze`. It summarizes verdict, validation, measurement status, findings, action queue, coverage, measurement basis, and artifact metadata without reprinting raw packet detail. |
| ArchSig Atom Viewer data | `archsig-atom-viewer-data-v0` | Bounded browser projection emitted by default from `analyze`. It records source refs as count plus samples, layout settings, priority-selected atom nodes, molecule groups, molecule-to-atom edges, overlays, report pane sections, omitted counts / reasons, truncation policy, and non-conclusions. It is not a raw packet copy. |
| ArchSig run manifest | `archsig-run-manifest-v0` | Run navigation artifact emitted by default from `analyze`. It records command name, input paths, output mode, generated / omitted artifacts, validation report paths, optional raw artifact paths, and validation result summary. |
| ArchSig analysis packet | `archsig-analysis-packet-v0` | Raw evidence artifact emitted only when raw artifact retention is requested. It records molecule readings, law-relative obstruction circuits, signature axes, flatness reading, repair candidates, coverage gaps, child-level `missingEvidence` / `excludedReadings`, evidence boundaries, LLM interpretation notes, and non-conclusions. |
| ArchSig analysis validation report | `archsig-analysis-packet-validation-report-v0` | Checks the analysis packet boundary without proving lawfulness, source completeness, flatness, or repair safety. |
| LLM interpretation packet | `archsig-analysis-packet-v0` | Optional raw artifact: a second serialization of the packet's structured LLM interpretation surface. |

## Removed Surfaces

The current CLI and schema catalog expose only the current artifacts above.
Pre-Atom surfaces were removed rather than kept as compatibility shims. If one
is needed again, rebuild it as a new feature on top of
`archsig-analysis-packet-v0`.

## FieldSig Handoff

FieldSig consumes the serialized `archsig-analysis-packet-v0` through
`fieldsig archsig-analysis-sft-input`. FieldSig projects obstruction circuits,
signature axes, repair candidates, and coverage gaps into
`operation-support-estimate-v0` as bounded refs and unknown remainder. Raw
ArchMap observation files are not the current FieldSig handoff. When `analyze`
runs in the default summary / viewer / manifest mode, rerun it with explicit raw
artifact retention before invoking FieldSig handoff.

ArchSig does not own SFT forecast, IntentMap, workflow evidence, operational
feedback, dynamics, governance, or calibration.

## Claim Boundary

Validation pass is not a Lean proof, forecast correctness proof, probability
claim, causal theorem, global safety guarantee, semantic correctness proof,
extractor-completeness proof, certified atom truth, zero-curvature proof, or
replacement for CI / tests / human review.
