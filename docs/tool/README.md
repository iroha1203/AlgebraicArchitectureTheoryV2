# Tool Docs

`docs/tool/` is built around the ArchMap / interpretation profile / ArchSig
`analyze` workflow.

The previous mixed tool documents are archived under:

- `docs/archive/2026-05-26-tool-docs-pre-archmap-primary/`

Current source-of-truth boundaries:

- ArchMap starts from supplied `archmap-observation-map-v0` evidence read as a source-grounded Atom observation map. It records `atomObservations`, `moleculeObservations`, `semanticObservations`, `observationGaps`, `projectionInfo`, `concernHints`, provenance, and non-conclusions.
- ArchMap authoring is complete-first as a product workflow. The LLM-native authoring pass should collect the source inventory, primitive atoms, molecules, semantic readings, ACTS support, homotopy path candidates, filler evidence, non-fillability witnesses, canonical Atom projection hints, and targeted gaps before presenting ArchSig output. `blockedByCoverageGap` is a repair target during authoring unless the evidence is truly private, unavailable, or out of scope.
- ArchMapStore is the forward storage boundary for ArchMap history. It models `ArchMapDelta`, `ArchMapCommit`, `ArchMapSnapshot`, `ArchMapIndex`, and validation reports so PR review can read ArchMap-level deltas instead of raw language diffs. Raw diffs are not ArchSig PR-review inputs.
- The selected interpretation profile currently uses the `law-policy-v0` JSON schema. It selects laws, witness rules, molecule patterns, obstruction circuit definitions, signature axes, coverage requirements, exactness assumptions, optional ACTS spectrum measurement profiles, and optional homotopy path / filler / loop measurement profiles separately from ArchMap. It is a profile, not AAT itself.
- ArchSig reads ArchMap + interpretation profile and computes the North Star AAT analysis packet: AAT concept surfaces, architecture state, design pressure, change impact, architecture object projections, invariant family readings, LawUniverse reading, obstruction circuits, signature axes, analytic representations, semantic coupling/cohesion, workflow risk readings, spectral analysis readings, spectral mode readings, spectral drilldown readings, ACTS curvature support / transfer readings, `ArchitectureSpectrumReport`, transfer bridge readings with edge source refs / review focus / cut recommendations, v0.3.0 measurement expansion readings (Atom support, Atom compatibility, LawUniverse coverage, feature extension formula axes, operation calculus laws, path signature trajectory, homotopy / order sensitivity, diagram fillability), AAT observation-axis readings (`observationProjectionFidelityReadings`, `atomOriginClosureDebtReadings`, `effectRelationAlgebraReadings`, `synthesisBlockageReadings`, `operationPreconditionReadinessReadings`, `pathMultiplicityLossReadings`), monodromy / boundary holonomy readings (`operationSquareCandidates`, `pathContinuationTraces`, `axisWiseMonodromyDefects`, `amiAggregateReadings`, `nonzeroMonodromyWitnesses`, `featureBoundaryResidualReadings`, `featureExtensionDiagnosisReadings`), representation strength, local curvature diagrams, three-layer flatness, canonical observation projection coordinates, state transition algebra, operation / invariant Galois readings, split readiness, structural reading review surface, current-state/evolution boundary, design principle readings, bounded judgements, repair operation deltas, path / homotopy / diagram readings, and LLM interpretation. Obstruction circuits, spectral readings, spectral modes, spectral drilldowns, ACTS curvature / transfer readings, transfer bridges, structural readings, v0.3.0 measurement expansion readings, AAT observation-axis readings, monodromy / boundary holonomy readings, and zero-curvature readings are not first-class ArchMap outputs.
- `analyze` is the primary ArchSig workflow entry point. `llm-native-workflow` / `north-star-workflow` remain compatibility aliases for the same workflow, and `archsig-analysis` / `aat-analysis` remain step commands for building a packet from supplied inputs. Removed pre-Atom workflows remain available only through Git history; they are not current ArchSig surface or compatibility inputs.
- `pr-review` is the lightweight CI / PR surface. It reads base `archmap-observation-map-v0`, PR-local `archmap-delta-v0`, and required `law-policy-v0` as canonical inputs. No LawPolicy, no ArchSig judgement. Raw diff, `archmap-commit-v0`, and base/head analysis packets are not PR-review inputs.
- `analysis-summary` is the LLM-native compact reading surface for an `archsig-analysis-packet-v0`. It reports `verdict`, `qualityMeasurement`, `measurementStatusSummary` (measured / partial / proxy / unmeasured / blocked / `schemaFoundationOnly` counts), reader-mode summaries (`trendDiagnosis` and `reviewSupport`), `dominantFindings`, compact full `actionQueue`, `axisSummary`, `aatObservationAxisSummary`, `workflowRiskSummary`, `architecturalHoleSummary`, `bridgeSummary`, `coverageGapSummary`, `detailIndex`, `measurementBasis`, and metadata so users first see what the supplied ArchMap + LawPolicy measured without reprinting raw packet detail or promoting proxy/schema-only rows to measured claims. `trendDiagnosis` is the repository-wide tendency view for concentrated law-axis / workflow / bridge / path pressure and now includes `trendInsights`: cross-axis co-occurrence, operation freedom loss, selected path continuation defects, boundary residual localization, and repair transfer risk computed by intersecting existing packet readings rather than by recounting ArchMap fields. `reviewSupport` is the review queue view for action items, blockers, coverage gaps, and detail lookup. Full evidence remains in `archsig-analysis-packet.json` and is reached through `detailRefs` / `packet:<json-pointer>` refs. The added AAT observation axes distinguish projection loss from coverage gaps, source-backed Atom closure from inferred or missing expected atoms, effect relation pressure from state transition pressure, synthesis blockers from solver certificates, operation candidates from satisfied preconditions, and one observed path from full reachability.
- `codebase-inspection` is the current-state architecture health surface. It reads latest `archmap-snapshot-v0`, `archmap-index-v0`, optional recent deltas, optional LawPolicy provenance, and an `archsig-analysis-packet-v0`; it does not perform PR / diff evolution analysis.
- `ArchitectureSpectrumReport` is the primary ACTS codebase-inspection surface. It measures hotspots, bounded modes, witness clusters, recurrent obstruction supports, coverage gaps, measured boundary, and review focus for the supplied ArchMap + LawPolicy.
- `ArchitectureHomotopyReport` is the primary Homotopy / Holonomy / Stokes codebase-inspection surface. It measures filled loops, unfilled loops, nonzero holonomy loops, local curvature cells, bounded aggregate readings, coverage gaps, measured boundary, and review focus for the supplied ArchMap + LawPolicy.
- `concernHints` are review cues. They are not obstruction circuits, not law violations, and not theorem evidence.
- ArchMap validation rejects non-current root fields. Authoring must use the Atom observation fields above; pre-Atom ArchMap shapes are not compatibility inputs.
- The ArchSig schema catalog contains only ArchMap, interpretation profile (`law-policy-v0`), ArchSig analysis packet, and their validation reports.
- ArchSig keeps non-conclusions as metadata rather than as the lead diagnosis. Reports should state the measured conclusion first, then preserve measurement boundaries for downstream interpretation.
- ArchSig validation separates surface checks from measurement-depth and proxy-regression checks. It still does not prove extractor completeness, semantic correctness, architecture lawfulness, global safety, certified universal atom truth, zero curvature, SFT forecast correctness, or Lean theorem discharge.
- ArchSig is the CI / PR-review / lightweight structural diagnosis surface. FieldSig is the batch / longitudinal monitoring / evolution-quality diagnosis surface. FieldSig consumes `archsig-analysis-packet-v0` and future ArchMapStore / packet chains as bounded current and historical AAT structural state for PR / diff / change-vector evolution analysis. It does not read raw ArchMap observations as forecast truth, and ArchSig reports do not replace FieldSig forecast, governance, calibration, operational feedback, or longitudinal monitoring.

Atom handoff checklist:

- [Tooling Editing Guideline](guideline.md)
- [Atom Handoff Checklist](atom_handoff.md)
- [ArchMapStore Delta / Snapshot / Index Model](archmap_store.md)
- [LawPolicy](law_policy.md)
- [ArchSig Analysis Packet](archsig_analysis_packet.md)
- [LLM-Native Golden Corpus](golden_corpus.md)
- [ArchSig Analyze E2E Workflow](llm_native_e2e_workflow.md)

Forward design PRDs:

- [LLM-native ArchMap / ArchSig PRD](llm_native_archmap_archsig_prd.md)
- [ArchSig AAT Analysis Engine PRD](archsig_aat_analysis_engine_prd.md)
- [ArchSig v0.3.0 Measurement Expansion PRD](archsig_v0_3_0_measurement_expansion_prd.md)
- [ArchSig Monodromy / Boundary Holonomy Measurement PRD](archsig_monodromy_boundary_holonomy_prd.md)
- [ArchSig Curvature / Transfer Spectrum PRD](archsig_curvature_transfer_spectrum_prd.md)
- [ArchSig Homotopy / Holonomy Stokes PRD](archsig_homotopy_holonomy_stokes_prd.md)
- [ArchSig Monodromy / Boundary Holonomy Validation](archsig_monodromy_boundary_holonomy_validation.md)
- [ArchSig Curvature / Transfer Spectrum Validation](archsig_curvature_transfer_spectrum_validation.md)
- [ArchSig Homotopy / Holonomy Stokes Validation](archsig_homotopy_holonomy_stokes_validation.md)

New implementation-facing specification documents should be added here only when they match the implementation and keep those boundaries explicit. Forward PRDs should keep future schema and migration work separate from the current source-of-truth boundaries above.
