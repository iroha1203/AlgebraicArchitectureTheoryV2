# Tool Docs

`docs/tool/` is built around the ArchMap / LawPolicy / MeasurementProfile /
ArchSig `analyze` workflow. Tooling documents describe artifact contracts; they
are not the source of truth for AAT mathematics.

The previous mixed tool documents are archived under:

- `docs/archive/2026-05-26-tool-docs-pre-archmap-primary/`

Current source-of-truth boundaries:

- ArchMap v2 is the v0.4.0 AG measurement input contract. It records
  `sources`, subject / axis-decorated `atoms`, finite-poset `contexts`,
  and selected `covers`. The extraction doctrine is fixed by ArchSig as
  `doctrine:aat-canonical@1`; `molecules` are not a v2 primary field, and
  context membership replaces them for AG measurement.
- `aat-atom-vocabulary/v1` is the artifact-side projection of allowed ArchMap
  atom kind tokens with provenance back to the AAT doctrine. ArchMap v2
  validation resolves this vocabulary from the fixed AAT canonical doctrine and
  checks that `atoms[].kind` is a member before measurement; the check does not
  prove source extraction soundness, semantic correctness, or whether a new atom
  kind should be added to the doctrine.
- 観測と判定の責務境界の理論的根拠は
  [ArchMap・LawPolicy・ArchSig 責務憲章](archmap_lawpolicy_archsig_responsibility_charter.md) を見る。
  [ArchMap 観測純化 PRD](archmap_observation_purity_prd.md) は、旧 `extractionDoctrineRef` を
  author 入力ではなく固定定数として扱い、AG 入力から判定語(`mismatch` / `obstructionGenerator` /
  計算済み certificate)を排する改修を提案している。AAT 本文の A8 Essential Uniqueness 定理そのものは
  不変であり、tool 側の単一固定 doctrine 化はその一特殊化(compute 側の cross-doctrine 比較の退化)である。
- MeasurementProfile v1 is the first-class selected measurement regime. It
  declares site / cover refs, coefficient, EffCoeff procedure, witness family,
  resolution selector, Dom / Zero / NonZero / Cert predicates, and the
  five-valued verdict discipline. AG evaluators fail validation when this
  profile is not selected.
- ArchSig v0.4.0 emits `archsig-measurement-packet/v1` as the AG measurement
  packet. The packet has `profile`, `structuralVerdict`,
  `computedInvariants`, `analyticReadings`, `assumptions`,
  `boundaryStatements`, and legacy-compatible `nonConclusions`. Structural
  verdict rows may carry `dependsOnAssumptions` refs into the packet assumption
  ledger. Verdict values are limited to `measured_zero`, `measured_nonzero`,
  `unmeasured`, `unknown`, and `not_computed`; analytic readings, including
  theorem-candidate readings, are separate from structural verdicts.
  `boundaryStatements` carries typed scoped qualifiers, while `nonConclusions`
  remains a string compatibility view.
- v0.4.0 non-compatibility is scoped to the AG measurement path: `archmap/v2`
  plus `measurement-profile/v1` produces `archsig-measurement-packet/v1` and
  does not accept or emit the v1 typed evaluator artifact chain as that path's
  primary surface. The existing `archmap/v1` + `law-policy/v1` structural
  analysis runtime remains available as bounded legacy compatibility until a
  dedicated removal issue changes that surface.
- The v0.4.0 assumption ledger records checked / assumed / violated CBI
  assumptions once at packet time. If an assumption is violated, dependent AG
  structural verdicts fall to `not_computed`; conclusion text stays
  ledger-relative and conclusion-first.
- ArchView is the visualization layer for ArchSig measurement artifacts under
  `tools/archview`. It consumes emitted `archsig-atom-viewer-data.json`
  plus same-directory summary / manifest files, or an `archview-sequence/v1`
  manifest whose frames are independent `archsig analyze` runs. It projects
  measured finite-site / cover / gluing geometry and never creates a new
  structural verdict.
- FieldSig validates serialized `archsig-measurement-packet/v1` handoff
  semantics before projection. Measured structural verdict rows must carry a
  `certRef` or matching computed invariant evidence. Because the current packet
  does not encode row-level assumption dependencies, a violated assumption next
  to any measured structural verdict is treated as a conservative fail-fast
  packet-level contradiction rather than a success-looking SFT input.

- ArchMap v1 starts from supplied `archmap/v1` evidence read as a source-grounded Atom map. It records only `sources`, `atoms`, and `molecules` as primary input. Removed v0 fields such as `semanticObservations`, `projectionInfo`, `operationSquareEvidence`, `concernHints`, and `observationGaps` are not v1 input surfaces.
- ArchMap authoring should produce the source-grounded atoms and explicit molecule membership needed for the requested ArchSig measurement. Private, unavailable, and out-of-scope evidence belongs in authoring notes, CI reports, or review notes, not ArchMap primary JSON.
- ArchMapStore is the forward storage boundary for ArchMap history. It models `ArchMapDelta`, `ArchMapCommit`, `ArchMapSnapshot`, `ArchMapIndex`, and validation reports so PR review can read ArchMap-level deltas instead of raw language diffs. Raw diffs are not ArchSig PR-review inputs.
- LawPolicy v1 uses the `law-policy/v1` JSON schema. It is a selector over repository policies, evaluator ids, policy packs, basis refs, scope, severity, and optional `distanceProfileRef`. It does not carry witness rules, signature axes, coverage requirements, exactness assumptions, `part4DistanceProfile`, spectrum profiles, homotopy profiles, distance weights, operation costs, or distance DSLs; those calculation rules belong to the ArchSig evaluator registry / selected distance profile.
- ArchSig's legacy v1 structural path reads ArchMap v1 + LawPolicy v1 and computes a typed evaluator artifact chain: `normalized-archmap/v1`, `typed-evaluator-results/v1`, `archsig-architecture-distance/v1`, `archsig-analysis-packet/v1`, `archsig-analysis-summary/v1`, and `archsig-atom-viewer-data-v1`. Positive bounded conclusions are generated from typed evaluator results, architecture distance readings, support refs, basis refs, and detail refs.
- Wittgensteinian responsibility boundary: ArchSig says only what can be said from the supplied `ArchMap + LawPolicy + evidence contract`, and remains silent about what cannot be said from that input. The ArchMap author is responsible for Atom mapping and evidence correctness. The LawPolicy author is responsible for policy, evaluator, and restricted measurement profile selection. Axis, witness, coverage, and missing-blocker rules belong to the evaluator registry. ArchSig does not complete, infer, or validate the outside world; it emits a consistent bounded diagnostic conclusion within the input contract.
- `analyze` is the primary ArchSig workflow entry point. `llm-native-workflow` / `north-star-workflow`, `archsig-analysis` / `aat-analysis`, `analysis-summary`, `codebase-inspection`, and `archmap-generate` are not current runtime surfaces. Old command behavior remains available only through Git history or historical fixtures, not through the v1 CLI contract.
- `pr-review` is the lightweight CI / PR surface. The v1 path reads base `archmap/v1`, optional head / intermediate `archmap/v1`, PR-local `archmap-delta-v0`, and `law-policy/v1`; it reports typed evaluator status plus report-local refs to derived obstruction, spectrum, homotopy, structural reading, and architecture distance surfaces. It does not reconstruct v0 witness rules or accept raw diff / base packet inputs.
- `analyze` emits summary / viewer / manifest first. For v1 input, default output includes v1 validation reports, `normalized-archmap.json`, `typed-evaluator-results.json`, `architecture-distance.json`, `archsig-analysis-summary.json`, `archsig-atom-viewer-data.json`, and `archsig-run-manifest.json`; raw v1 packet, detail index, and LLM interpretation packet are saved only with `--emit-raw-artifacts`. `--strict-distance` rejects missing `distanceProfileRef`, blocked / unknown / unmeasured typed or direct architecture distance readings, missing canonical distance families, and canonical family bundles whose `measurementStateSummary.status` is not `measured`.
- `architecture-distance.json` is the primary distance artifact. In v1 it exposes `familySummaries`, `measurementStateSummary`, and `primaryInsightsRefs` for the canonical distance-family bundle. Its `summary.measuredTotal` is scoped by `summary.measuredTotalScope`: atom, configuration, signature, and operation geometry are the numeric architecture-distance-point aggregate, while foundation, curvature, homotopy, representation, measurement-boundary, and bounded-diagnostic families remain visible as non-aggregated canonical family states. Blocked, partial, unmeasured, and not-applicable family states are explicit states, not measured zero; not-applicable scoped families are marked as eligible scope without measured contribution.
- Atom / configuration geometry in `architecture-distance.json` is definition-row based. Atom pair readings expose Fiber, Carrier, Valence, Semantic Anchor, and composed Atom Layout rows. Configuration readings expose configuration-indexed shortest paths through explicit molecule hypergraphs plus context distance from molecule membership overlap, with top atom-pair / molecule insight refs surfaced through `distanceDiagnosis.atomConfigurationInsights`. Missing semantic anchors and missing configuration evidence are blockers, not zero values.
- Operation geometry in `architecture-distance.json` exposes profile-resolved operation cost, target distance decrease, distance to selected flatness, repair-route state, and side-effect bound. Missing operation cost is blocked rather than guessed, and repair-route candidates remain diagnostic readings, not automatic safe refactorings or Atom-generation claims.
- Curvature geometry in `architecture-distance.json` exposes obstruction measure, curvature support, curvature transport, curvature mass, and `distanceDiagnosis.curvatureInsights`. Measured zero is selected-support zero only; blocked witness support remains blocked and is not treated as zero curvature or global lawfulness.
- Homotopy / filling geometry in `architecture-distance.json` exposes selected homotopy distance, filling cost, observation gap lower bound, selected Dehn area, `ArchitectureHomotopyReport`, and `distanceDiagnosis.homotopyInsights`. Missing filler evidence and selected-axis coverage gaps remain source-linked blockers and are not treated as zero filling cost or global path equivalence.
- Representation metric in `architecture-distance.json` exposes selected structural distance, analytic-distance state, Lipschitz upper-bound state, bi-Lipschitz faithfulness state, and `distanceDiagnosis.representationInsights`. Bounded proxy telemetry remains partial / blocked support and is not treated as measured analytic distance or representation faithfulness.
- `distanceInsights` is the engineer-facing reading of `architecture-distance.json`: it exposes structural center, change-sensitive areas, selected policy-obstruction state, blocked evidence, recommended reading refs, and baseline-dependent `comparisonNeeded` claims without turning a single run into a trend or proof.
- `archsig-analysis-summary.json` is the LLM-native compact reading surface emitted by `analyze`. In v1 it reports a conclusion-first `conclusion`, typed evaluator status, `architectureDistance`, `distanceInsights`, `distanceDiagnosis`, dominant findings, action queue, measurement basis, and metadata without promoting label-only, removed-field-only, schema-only, blocked, unknown, or unmeasured rows to measured claims. Public summary / viewer / LLM surfaces use architecture distance naming rather than AAT mathematics section names.
- `archview.html` is the human visualization surface shipped in tool release bundles. It reads `archsig-atom-viewer-data.json` for bounded AAT geometry projection and uses same-directory summary / manifest files to populate the report pane with verdict, top findings, assumption boundary, validation status, and generated artifact state. If `archview-sequence.json` is present, it enters sequence mode and replays measured frames without interpolating new verdicts. Viewer geometry remains projection support, not an ArchSig diagnostic metric.
- `ArchitectureSpectrumReport` and `ArchitectureHomotopyReport` are legacy packet reading families, not v1 CLI commands. New runtime reporting should flow through typed evaluator results, summary, viewer data, and optional raw v1 packet artifacts.
- Legacy `concernHints` remain outside the v1 input contract. Review cues belong in review notes or report surfaces, not in ArchMap primary JSON.
- ArchMap validation rejects non-current root fields. Authoring must use the Atom observation fields above; pre-Atom ArchMap shapes are not compatibility inputs.
- The ArchSig schema catalog contains v1 ArchMap, LawPolicy, evaluator registry, normalized ArchMap, typed evaluator results, architecture distance, analysis packet, run manifest, viewer projection data, schema catalog, and validation report artifacts.
- ArchSig keeps non-conclusions as metadata rather than as the lead diagnosis. Reports should state the measured conclusion first, then preserve measurement boundaries for downstream interpretation.
- ArchSig validation separates surface checks from measurement-depth and proxy-regression checks. It still does not prove source-observation layer, semantic correctness, architecture lawfulness, global safety, certified universal atom truth, zero curvature, SFT forecast correctness, or Lean theorem discharge.
- ArchSig is the CI / PR-review / lightweight selected-evidence diagnosis surface. FieldSig is the batch / longitudinal monitoring / evolution-quality diagnosis surface. FieldSig consumes explicit ArchSig handoff artifacts as bounded current and historical architecture-evidence state for PR / diff / change-vector evolution analysis. It does not read raw ArchMap observations as forecast truth, and ArchSig summary / Viewer reports do not replace FieldSig forecast, governance, calibration, operational feedback, or longitudinal monitoring.

Atom handoff checklist:

- [Tooling Editing Guideline](guideline.md)
- [Atom Handoff Checklist](atom_handoff.md)
- [ArchMap v1 Output Replacement Gap Ledger](archmap_v1_output_replacement_gap_ledger.md)
- [ArchMapStore Delta / Snapshot / Index Model](archmap_store.md)
- [LawPolicy](law_policy.md)
- [ArchSig Analysis Packet](archsig_analysis_packet.md)
- [ArchSig v1 Migration Note](archsig_v1_migration_note.md)
- [LLM-Native Golden Corpus](golden_corpus.md)
- [ArchSig Analyze E2E Workflow](llm_native_e2e_workflow.md)
- [ArchView](../../tools/archview/README.md)

Forward design PRDs:

- [ArchSig v0.5.0 PRD-1 — レガシー破棄(前半)と契約基盤](archsig_v0_5_0_prd1_legacy_purge_and_foundation.md)
  (設計の正本は [v0.5.0 再設計ノート](../note/archsig_v0_5_0_redesign_note.md))
- [ArchSig v0.5.0 PRD-2 — measurement packet 新形と CI 面(gate / compare)](archsig_v0_5_0_prd2_artifact_ci.md)
- [ArchMap Atom-to-AAT Presentation Contract PRD](archmap_minimal_observation_contract_prd.md)
- [ArchSig v0.4.0 Algebraic Geometry Measurement PRD](archsig_v0_4_0_algebraic_geometry_measurement_prd.md)
- [ArchSig v0.4.0 改善 PRD(measured_zero 純度 / 行レベル assumption 依存 / 境界の機械可読化 / ArchMap atom 語彙 lint)](archsig_v0_4_0_improvement_prd.md)
- [ArchSig 計測忠実性補強と AG-faithful Viewer 統合 PRD(計測=主 / 可視化=従、M0-M15 + V0-V18)](archsig_measurement_faithfulness_and_ag_viewer_prd.md)
- [ArchSig Monodromy / Boundary Holonomy Measurement PRD](archsig_monodromy_boundary_holonomy_prd.md)
- [ArchSig Curvature / Transfer Spectrum PRD](archsig_curvature_transfer_spectrum_prd.md)
- [ArchSig Homotopy / Holonomy Stokes PRD](archsig_homotopy_holonomy_stokes_prd.md)
- [ArchSig Monodromy / Boundary Holonomy Validation](archsig_monodromy_boundary_holonomy_validation.md)
- [ArchSig Curvature / Transfer Spectrum Validation](archsig_curvature_transfer_spectrum_validation.md)
- [ArchSig Homotopy / Holonomy Stokes Validation](archsig_homotopy_holonomy_stokes_validation.md)

New implementation-facing specification documents should be added here only when they match the implementation and keep those boundaries explicit. Forward PRDs should keep future schema and migration work separate from the current source-of-truth boundaries above.
