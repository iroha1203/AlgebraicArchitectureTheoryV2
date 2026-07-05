# ArchSig Artifacts And Boundaries

ArchSig owns the ArchMap v1 analysis surface:

```text
archmap/v0.5.0
  + law-policy/v0.5.0
  -> normalized-archmap/v0.5.0
  -> typed-evaluator-results/v0.5.0
  -> archsig-architecture-distance/v1
  -> archsig-analysis-summary.json
  -> archsig-atom-viewer-data.json
  -> archsig-run-manifest.json
  -> optional archsig-analysis-packet/v0.5.0 for raw evidence / FieldSig handoff
```

Git history is the archive for pre-Atom scan, v0 packet-builder, standalone
summary, codebase-inspection, and legacy PR-review surfaces. They are not
current ArchSig artifacts or commands.

ArchMap is LLM-authored source reading, not an AST extractor result. Static
artifacts such as ASTs, symbol indexes, import graphs, route lists, and
framework registries may support navigation, source inventory selection, and
gap discovery. They do not by themselves certify observed atoms, semantic
dependencies, runtime interactions, authority coverage, or extractor
completeness.

For large repositories, parallel agents may survey bounded surfaces and return
candidate observations. The final ArchMap still requires an integration pass
that deduplicates candidates, resolves source refs, preserves explicit molecule
candidates, and promotes only primitive source-grounded facts to `atoms`.

Large ArchMaps may be authored as horizontal bounded observation slices, but
current ArchSig analysis commands consume an exported monolithic `archmap/v0.5.0`
artifact, not slice fragments.

## Current Artifacts

| Artifact | Schema / file | Role |
| --- | --- | --- |
| ArchMap | `archmap/v0.5.0` | Source-grounded Atom observations and explicit molecule candidates. Removed v0 helper fields are not positive diagnostic input. ArchMap remains law-independent and does not own obstruction circuits, lawfulness, zero curvature, repair conclusions, or Lean theorem discharge. |
| ArchMap validation report | `archmap-validation-report/v1` | Checks schema support, identity, source refs, atom kind / predicate boundary, molecule support, removed v0 fields, legacy aliases, and unresolved refs before analysis. |
| Normalized ArchMap | `normalized-archmap/v0.5.0` | Canonicalized Atom and molecule support used by typed evaluators. This is an internal analysis artifact, not a new authoring schema. |
| LawPolicy | `law-policy/v0.5.0` | Selected evaluator manifests, basis refs, law ids, distance profile refs, and non-conclusions for one review context. It is evaluator selection, not AAT itself. |
| LawPolicy validation report | `law-policy-validation-report/v1` | Checks evaluator ids, basis refs, selected laws, profile refs, unknown packs, and unsupported legacy v0 DSL fields. |
| Typed evaluator results | `typed-evaluator-results/v0.5.0` | Selected evaluator statuses, support refs, basis refs, replacement evaluator results, and positive bounded conclusions. `blocked`, `unknown`, and `unmeasured` are blockers, not measured zero. |
| Architecture distance | `archsig-architecture-distance/v1` | Current-state diagnostic distance readings derived from typed evaluator output and the selected distance profile. It is not a forecast or merge-safety score. |
| ArchSig analysis summary | `archsig-analysis-summary.json` | Default compact reading surface emitted by `analyze`. It reports conclusion, typed evaluator status, architecture distance, `distanceDiagnosis`, dominant findings, action queue, rich packet refs, measurement basis, and metadata without reprinting raw packet detail. |
| ArchSig viewer data | `archsig-atom-viewer-data.json` | Bounded browser projection emitted by default from `analyze`. It mirrors summary / packet refs into a visual inspection surface. Viewer layout distance remains visual support, not diagnostic metric. |
| ArchView | `archview/archview.html` | Visualization layer for emitted ArchSig measurement artifacts. It reads `archsig-atom-viewer-data.json`, optional same-directory summary / manifest files, and optional `archview-sequence/v1` manifests. It projects measured AAT geometry and does not create structural verdicts. |
| ArchSig run manifest | `archsig-run-manifest.json` | Run navigation artifact emitted by default from `analyze`. It records command name, input paths, generated / omitted artifacts, validation report paths, optional raw artifact paths, and validation result summary. |
| ArchSig analysis packet | `archsig-analysis-packet/v0.5.0` | Optional raw evidence artifact emitted with `--emit-raw-artifacts`. It records generated law inputs, signature axes, generated obstructions, generated repair targets, replacement registry / replacement evaluator results, spectrum / homotopy / structural readings, bounded judgements, LLM interpretation refs, and non-conclusions. |
| ArchSig detail index | `archsig-analysis-detail-index/v1` | Optional raw lookup artifact for packet refs and detail refs. It lets summary / viewer users stay compact while preserving evidence lookup. |
| LLM interpretation packet | `llm-interpretation-packet.json` | Optional raw artifact carrying compact reading guidance, action queue summary, distance diagnosis summary, and rich packet refs for LLM readers. |
| PR review report | `archsig-pr-review-report/v0.5.0` | Lightweight PR review surface over base `archmap/v0.5.0`, optional head / path `archmap/v0.5.0`, PR-local `archmap-delta/v0.5.0`, and `law-policy/v0.5.0`. It emits report-local v1 snapshots, delta packet intersections, movement / hidden-excursion boundaries, safe-change budget, and review focus. |

Release archives include ArchView under `archview/`, including its README.
ArchView reads `archsig-atom-viewer-data.json` projection data, not raw packet
detail. It also reads same-directory `archsig-analysis-summary.json` /
`archsig-run-manifest.json` when available, and enters sequence mode when an
`archview-sequence.json` manifest sits beside the viewer. Sequence frames are
independent emitted ArchSig measurements; ArchView compares frame conclusions
only to show adjacent measured conclusion changes and does not interpolate or
invent verdicts.

## Removed v0 Fields

The v1 path rejects removed v0 ArchMap helper fields as input:

- `semanticObservations`
- `projectionInfo`
- `operationSquareEvidence`
- `concernHints`
- `observationGaps`

These concepts reappear only as evaluator output replacement surfaces:
semantic interpretation, projection readings, operation-square / homotopy
readings, missing-evidence readings, concern boundaries, generated
obstructions, spectrum / homotopy reports, and structural review refs. Removed
fields are not ignored silently and are not reintroduced as ArchMap primary
input.

## Removed Commands

The current CLI and schema catalog expose only the v1 artifacts above.
`llm-native-workflow`, `north-star-workflow`, `archsig-analysis`,
`aat-analysis`, `analysis-summary`, `summary`, `codebase-inspection`, and
`archmap-generate` are removed current runtime surfaces. If one is needed
again, rebuild it as a new v1 feature instead of treating old packet equality
as completion evidence.

## FieldSig Handoff

FieldSig consumes the serialized `archsig-analysis-packet/v0.5.0` through
`fieldsig archsig-analysis-sft-input`. FieldSig projects ArchSig current-state
structural refs into `operation-support-estimate/v0.5.0` as bounded refs and
unknown remainder. Raw ArchMap files are not the current FieldSig handoff. When
`analyze` runs in the default summary / viewer / manifest mode, rerun it with
`--emit-raw-artifacts` before invoking FieldSig handoff.

Do not treat `distanceDiagnosis`, spectrum hotspots, homotopy holes,
structural review refs, or PR review safe-change budget as FieldSig forecasts.
They are ArchSig current-state diagnoses under the selected
`ArchMap + LawPolicy + evidence contract`.

ArchSig does not own SFT forecast, IntentMap, workflow evidence, operational
feedback, dynamics, governance, or calibration.

## Claim Boundary

Validation pass is not a Lean proof, forecast correctness proof, probability
claim, causal theorem, global safety guarantee, semantic correctness proof,
extractor-completeness proof, certified atom truth, zero-curvature proof, or
replacement for CI / tests / human review.
