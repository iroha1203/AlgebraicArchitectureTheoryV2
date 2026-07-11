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
- [AG measurement evidence contract](ag_measurement_evidence_contract.md): fixtureのsource sectionと入力責務。
- [ArchView gluing geometry contract](archview_gluing_geometry_contract.md): golden projection caseとfidelity規律。
- [ArchView](../../tools/archview/README.md)

New implementation-facing specification documents should be added here only
when they match implementation and keep AAT, ArchSig, FieldSig, and website
boundaries explicit.
