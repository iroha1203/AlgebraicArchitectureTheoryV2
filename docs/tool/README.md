# Tool Docs

`docs/tool/` describes current ArchMap / LawPolicy / law-equation-surface /
MeasurementProfile / policy-bundle / ArchSig / FieldSig artifact contracts. It is not the source of truth for AAT
mathematics.

Historical tool documents are archived under:

- `docs/archive/2026-05-26-tool-docs-pre-archmap-primary/`
- `docs/archive/2026-07-05-archsig-v1-retirement/`

Current source-of-truth boundaries:

- ArchMap records source-grounded Atom evidence with finite-poset contexts and
  selected covers.
- LawPolicy selects explicit law / lawPair entries, evaluators, basis refs, scope, and severity.
- law-equation-surface declares the selected law universe and witness variables.
- policy-bundle fixes LawPolicy, law-equation-surface, and MeasurementProfile
  with canonical component fingerprints for one run.
- MeasurementProfile selects the concrete finite measurement regime.
- RepairPlan (`archsig-repair-plan/v0.5.4`) is the SAGA Stage 1 input side:
  `repair-plan` validates it, and `analyze --repair-plan` consumes it when
  `ag.saga-descent` is selected. Without it the row stays `not_computed` with
  `silence_by_design`.
- ArchSig `analyze` emits the current measurement packet, validation reports,
  summary, insight report, viewer data, and run manifest.
- ArchSig compare + gate are the current PR / CI decision surfaces.
- The bundled skills under `tools/archsig/skills` (`archmap-creater`,
  `law-policy-creater`, `archsig-reader`, `archsig-pr-reviewer`,
  `repair-plan-creater`) are the primary product interface for LLM agents; the
  CLI is the stable runtime they call.
- FieldSig reads ArchSig measurement packets as bounded current SFT handoff
  state. Raw ArchMap files and retired raw packets are not current handoff
  inputs.
- ArchView renders the display-independent measurement view model
  (`archsig-measurement-view-model.json`) and the optional diagnosis dossier
  (`archsig-diagnosis-dossier.json`) as the weather-lens survey map. It never
  creates a new verdict; weather vocabulary stays on the display side.

Current entry points:

- [Tooling Editing Guideline](guideline.md)
- [One-cent drift demo](../../tools/archsig/examples/practical-rust-service/README.md): 実行可能なend-to-endデモ(SAGA診断階段: grounding→residual class実測→h1-transfer→harmonic debt→gate BLOCK→修復→PASS)。
- [Atom Handoff Checklist](atom_handoff.md)
- [LawPolicy](law_policy.md)
- [ArchSig Analyze E2E Workflow](llm_native_e2e_workflow.md)
- [ArchSig skills](../../tools/archsig/skills/): 5本のバンドルSKILL(一次product interface)。
- [ArchSig gate-policy authoring guide](archsig_gate_policy.md)
- [ArchSig compare report guide](archsig_compare.md)
- [ArchSig measurement view model contract](archsig_view_model_contract.md)
- [ArchMapStore Notes](archmap_store.md)
- [LLM-Native Golden Corpus](golden_corpus.md)
- [AG measurement evidence contract](ag_measurement_evidence_contract.md): fixtureのsource sectionと入力責務。
- [ArchView 忠実性契約(気象図 lens)](archview_gluing_geometry_contract.md): 視覚語彙・fidelity・沈黙・時間軸の恒久規律。
- [ArchView](../../tools/archview/README.md)

New implementation-facing specification documents should be added here only
when they match implementation and keep AAT, ArchSig, FieldSig, and website
boundaries explicit.
