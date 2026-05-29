# Tool Docs

`docs/tool/` is built around the LLM-native ArchMap / interpretation profile /
ArchSig AAT analysis workflow.

The previous mixed tool documents are archived under:

- `docs/archive/2026-05-26-tool-docs-pre-archmap-primary/`

Current source-of-truth boundaries:

- ArchMap starts from supplied `archmap-observation-map-v0` evidence read as a source-grounded Atom observation map. It records `atomObservations`, `moleculeObservations`, `semanticObservations`, `observationGaps`, `projectionInfo`, `concernHints`, provenance, and non-conclusions.
- The selected interpretation profile currently uses the `law-policy-v0` JSON schema. It selects laws, witness rules, molecule patterns, obstruction circuit definitions, signature axes, coverage requirements, and exactness assumptions separately from ArchMap. It is a profile, not AAT itself.
- ArchSig reads ArchMap + interpretation profile and computes the North Star AAT analysis packet: AAT concept surfaces, architecture state, design pressure, change impact, architecture object projections, invariant family readings, LawUniverse reading, obstruction circuits, signature axes, analytic representations, semantic coupling/cohesion, workflow risk readings, spectral analysis readings, spectral mode readings, spectral drilldown readings, transfer bridge readings with edge source refs and cut recommendations, representation strength, local curvature diagrams, three-layer flatness, observation projection, state transition algebra, operation / invariant Galois readings, split readiness, design principle readings, bounded judgements, repair operation deltas, path / homotopy / diagram readings, and LLM interpretation. Obstruction circuits, spectral readings, spectral modes, spectral drilldowns, transfer bridges, structural readings, and zero-curvature readings are not first-class ArchMap outputs.
- `llm-native-workflow` / `north-star-workflow` and `archsig-analysis` / `aat-analysis` are the normal ArchSig entry points. Removed pre-Atom workflows remain available only through Git history; they are not current ArchSig surface or compatibility inputs.
- `concernHints` are review cues. They are not obstruction circuits, not law violations, and not theorem evidence.
- ArchMap validation rejects non-current root fields. Authoring must use the Atom observation fields above; pre-Atom ArchMap shapes are not compatibility inputs.
- The ArchSig schema catalog contains only ArchMap, interpretation profile (`law-policy-v0`), ArchSig analysis packet, and their validation reports.
- ArchSig validation does not prove extractor completeness, semantic correctness, architecture lawfulness, global safety, certified universal atom truth, zero curvature, SFT forecast correctness, or Lean theorem discharge.
- FieldSig / SFT forecast and governance surfaces are not owned by ArchSig. FieldSig consumes `archsig-analysis-packet-v0` as bounded local AAT state and projects obstruction circuits, signature axes, repair candidates, and coverage gaps into SFT input boundaries. It does not read raw ArchMap observations as forecast truth.

Atom handoff checklist:

- [Atom Handoff Checklist](atom_handoff.md)
- [LawPolicy](law_policy.md)
- [ArchSig Analysis Packet](archsig_analysis_packet.md)
- [LLM-Native Golden Corpus](golden_corpus.md)
- [LLM-native E2E Workflow](llm_native_e2e_workflow.md)

Forward design PRDs:

- [LLM-native ArchMap / ArchSig PRD](llm_native_archmap_archsig_prd.md)
- [ArchSig AAT Analysis Engine PRD](archsig_aat_analysis_engine_prd.md)

New implementation-facing specification documents should be added here only when they match the implementation and keep those boundaries explicit. Forward PRDs should keep future schema and migration work separate from the current source-of-truth boundaries above.
