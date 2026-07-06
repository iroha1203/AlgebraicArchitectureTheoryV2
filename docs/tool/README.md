# Tool Docs

`docs/tool/` describes current ArchMap / LawPolicy / MeasurementProfile /
ArchSig / FieldSig artifact contracts. It is not the source of truth for AAT
mathematics.

Historical tool documents are archived under:

- `docs/archive/2026-05-26-tool-docs-pre-archmap-primary/`
- `docs/archive/2026-07-05-archsig-v1-retirement/`

Current source-of-truth boundaries:

- ArchMap records source-grounded Atom evidence with finite-poset contexts and
  selected covers.
- LawPolicy selects evaluators, basis refs, scope, and severity.
- MeasurementProfile selects the concrete finite measurement regime.
- ArchSig `analyze` emits the current measurement packet, validation reports,
  summary, insight report, viewer data, and run manifest.
- ArchSig compare + gate are the current PR / CI decision surfaces.
- FieldSig reads ArchSig measurement packets as bounded current SFT handoff
  state. Raw ArchMap files and retired raw packets are not current handoff
  inputs.
- ArchView visualizes emitted viewer data and same-directory summary / manifest
  files. It projects measured geometry and does not create a new verdict.

Current entry points:

- [Tooling Editing Guideline](guideline.md)
- [Atom Handoff Checklist](atom_handoff.md)
- [LawPolicy](law_policy.md)
- [ArchSig Analyze E2E Workflow](llm_native_e2e_workflow.md)
- [ArchSig gate-policy authoring guide](archsig_gate_policy.md)
- [ArchSig compare report guide](archsig_compare.md)
- [ArchMapStore Notes](archmap_store.md)
- [LLM-Native Golden Corpus](golden_corpus.md)
- [ArchView](../../tools/archview/README.md)

Forward design PRDs:

- [ArchSig v0.5.0 PRD-1](archsig_v0_5_0_prd1_legacy_purge_and_foundation.md)
- [ArchSig v0.5.0 PRD-2](archsig_v0_5_0_prd2_artifact_ci.md)
- [ArchSig v0.5.0 PRD-3](archsig_v0_5_0_prd3_v1_retirement_and_sync.md)
- [ArchSig v0.5.0 PRD-4](archsig_v0_5_0_prd4_lawpolicy_stage1_saga_stage1.md)
- [ArchSig v0.5.0 PRD-5](archsig_v0_5_0_prd5_archmap_skill.md)
- [Archived ArchMap observation purity PRD](../archive/2026-07-07-archsig-v0-legacy-prds/archmap_observation_purity_prd.md)
- [Archived ArchMap Atom-to-AAT Presentation Contract PRD](../archive/2026-07-07-archsig-v0-legacy-prds/archmap_minimal_observation_contract_prd.md)
- [Archived ArchSig v0.4.0 Algebraic Geometry Measurement PRD](../archive/2026-07-07-archsig-v0-legacy-prds/archsig_v0_4_0_algebraic_geometry_measurement_prd.md)

New implementation-facing specification documents should be added here only
when they match implementation and keep AAT, ArchSig, FieldSig, and website
boundaries explicit.
