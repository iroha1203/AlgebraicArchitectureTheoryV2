# Tool Docs

`docs/tool/` is built around the ArchMap / interpretation profile / ArchSig
`analyze` workflow.

The previous mixed tool documents are archived under:

- `docs/archive/2026-05-26-tool-docs-pre-archmap-primary/`

Current source-of-truth boundaries:

- ArchMap v1 starts from supplied `archmap/v1` evidence read as a source-grounded Atom map. It records only `sources`, `atoms`, and `molecules` as primary input. Removed v0 fields such as `semanticObservations`, `projectionInfo`, `operationSquareEvidence`, `concernHints`, and `observationGaps` are not v1 input surfaces.
- ArchMap authoring should produce the source-grounded atoms and explicit molecule membership needed for the requested ArchSig measurement. Private, unavailable, and out-of-scope evidence belongs in authoring notes, CI reports, or review notes, not ArchMap primary JSON.
- ArchMapStore is the forward storage boundary for ArchMap history. It models `ArchMapDelta`, `ArchMapCommit`, `ArchMapSnapshot`, `ArchMapIndex`, and validation reports so PR review can read ArchMap-level deltas instead of raw language diffs. Raw diffs are not ArchSig PR-review inputs.
- LawPolicy v1 uses the `law-policy/v1` JSON schema. It is a selector over repository policies, evaluator ids, policy packs, basis refs, scope, and severity. It does not carry witness rules, signature axes, coverage requirements, exactness assumptions, `part4DistanceProfile`, spectrum profiles, or homotopy profiles; those calculation rules belong to the ArchSig evaluator registry.
- ArchSig reads ArchMap v1 + LawPolicy v1 and computes a typed evaluator artifact chain: `normalized-archmap/v1`, `typed-evaluator-results/v1`, `archsig-analysis-packet/v1`, `archsig-analysis-summary/v1`, and `archsig-atom-viewer-data-v1`. Positive bounded conclusions are generated from typed evaluator results, support refs, basis refs, and detail refs.
- Wittgensteinian responsibility boundary: ArchSig says only what can be said from the supplied `ArchMap + LawPolicy + evidence contract`, and remains silent about what cannot be said from that input. The ArchMap author is responsible for observation, Atom mapping, and evidence correctness. The LawPolicy author is responsible for law / axis / witness / coverage selection. ArchSig does not complete, infer, or validate the outside world; it emits a consistent bounded diagnostic conclusion within the input contract.
- `analyze` is the primary ArchSig workflow entry point. `llm-native-workflow` / `north-star-workflow` remain compatibility aliases for the same workflow, and `archsig-analysis` / `aat-analysis` remain step commands for building a packet from supplied inputs. Removed pre-Atom workflows remain available only through Git history; they are not current ArchSig surface or compatibility inputs.
- `pr-review` is the lightweight CI / PR surface. The v1 path reads `archmap/v1` and `law-policy/v1` and reports typed evaluator status without reconstructing v0 witness rules, signature axes, coverage requirements, or distance formulas.
- `analyze` emits summary / viewer / manifest first. For v1 input, default output includes v1 validation reports, `normalized-archmap.json`, `typed-evaluator-results.json`, `archsig-analysis-summary.json`, `archsig-atom-viewer-data.json`, and `archsig-run-manifest.json`; raw v1 packet, detail index, and LLM interpretation packet are saved only with `--emit-raw-artifacts`. `--strict-distance` rejects blocked / unknown / unmeasured typed distance.
- `analysis-summary` is the LLM-native compact reading surface. In v1 it reports typed evaluator status counts, `distanceDiagnosis`, dominant findings, action queue, measurement basis, and metadata from typed evaluator results without promoting label-only, removed-field-only, schema-only, blocked, unknown, or unmeasured rows to measured claims.
- `archsig-atom-viewer.html` is the human first surface shipped in ArchSig release bundles. It reads `archsig-atom-viewer-data.json` for bounded 3D Atom / molecule / overlay projection and uses same-directory summary / manifest files to populate the report pane with verdict, top findings, distance diagnosis, action queue, coverage boundaries, validation status, generated / omitted artifact state, and optional raw artifact links. Diagnostic distance overlays are bounded Part IV evaluator projections; `viewerDistanceInputs` remain visual layout support, not ArchSig diagnostic metrics.
- `codebase-inspection` is the current-state architecture health surface. It reads latest `archmap-snapshot-v0`, `archmap-index-v0`, optional recent deltas, optional LawPolicy provenance, and an `archsig-analysis-packet-v0`; it does not perform PR / diff evolution analysis.
- `ArchitectureSpectrumReport` is the primary ACTS codebase-inspection surface. It measures hotspots, bounded modes, witness clusters, recurrent obstruction supports, coverage gaps, measured boundary, and review focus for the supplied ArchMap + LawPolicy.
- `ArchitectureHomotopyReport` is the primary Homotopy / Holonomy / Stokes codebase-inspection surface. It measures filled loops, unfilled loops, nonzero holonomy loops, local curvature cells, bounded aggregate readings, coverage gaps, measured boundary, and review focus for the supplied ArchMap + LawPolicy.
- Legacy `concernHints` remain outside the v1 input contract. Review cues belong in review notes or report surfaces, not in ArchMap primary JSON.
- ArchMap validation rejects non-current root fields. Authoring must use the Atom observation fields above; pre-Atom ArchMap shapes are not compatibility inputs.
- The ArchSig schema catalog contains v1 ArchMap, LawPolicy, evaluator registry, normalized ArchMap, typed evaluator results, analysis packet, run manifest, Atom Viewer data, schema catalog, compatibility policy, and validation report artifacts. Legacy pre-Atom outputs are not current schema catalog surfaces.
- ArchSig keeps non-conclusions as metadata rather than as the lead diagnosis. Reports should state the measured conclusion first, then preserve measurement boundaries for downstream interpretation.
- ArchSig validation separates surface checks from measurement-depth and proxy-regression checks. It still does not prove source-observation layer, semantic correctness, architecture lawfulness, global safety, certified universal atom truth, zero curvature, SFT forecast correctness, or Lean theorem discharge.
- ArchSig is the CI / PR-review / lightweight structural diagnosis surface. FieldSig is the batch / longitudinal monitoring / evolution-quality diagnosis surface. FieldSig consumes opt-in `archsig-analysis-packet-v0` raw artifacts and future ArchMapStore / packet chains as bounded current and historical AAT structural state for PR / diff / change-vector evolution analysis. It does not read raw ArchMap observations as forecast truth, and ArchSig summary / Viewer reports do not replace FieldSig forecast, governance, calibration, operational feedback, or longitudinal monitoring.

Atom handoff checklist:

- [Tooling Editing Guideline](guideline.md)
- [Atom Handoff Checklist](atom_handoff.md)
- [ArchMapStore Delta / Snapshot / Index Model](archmap_store.md)
- [LawPolicy](law_policy.md)
- [ArchSig Analysis Packet](archsig_analysis_packet.md)
- [ArchSig v1 Migration Note](archsig_v1_migration_note.md)
- [LLM-Native Golden Corpus](golden_corpus.md)
- [ArchSig Analyze E2E Workflow](llm_native_e2e_workflow.md)

Forward design PRDs:

- [ArchMap Atom-to-AAT Presentation Contract PRD](archmap_minimal_observation_contract_prd.md)
- [LLM-native ArchMap / ArchSig PRD](llm_native_archmap_archsig_prd.md)
- [ArchSig AAT Analysis Engine PRD](archsig_aat_analysis_engine_prd.md)
- [ArchSig Output / Viewer PRD](archsig_output_report_prd.md)
- [ArchSig v0.3.0 Measurement Expansion PRD](archsig_v0_3_0_measurement_expansion_prd.md)
- [ArchSig Monodromy / Boundary Holonomy Measurement PRD](archsig_monodromy_boundary_holonomy_prd.md)
- [ArchSig Curvature / Transfer Spectrum PRD](archsig_curvature_transfer_spectrum_prd.md)
- [ArchSig Homotopy / Holonomy Stokes PRD](archsig_homotopy_holonomy_stokes_prd.md)
- [ArchSig Monodromy / Boundary Holonomy Validation](archsig_monodromy_boundary_holonomy_validation.md)
- [ArchSig Curvature / Transfer Spectrum Validation](archsig_curvature_transfer_spectrum_validation.md)
- [ArchSig Homotopy / Holonomy Stokes Validation](archsig_homotopy_holonomy_stokes_validation.md)

New implementation-facing specification documents should be added here only when they match the implementation and keep those boundaries explicit. Forward PRDs should keep future schema and migration work separate from the current source-of-truth boundaries above.
