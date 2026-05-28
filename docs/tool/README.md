# Tool Docs

`docs/tool/` is being rebuilt around the LLM-native ArchMap / LawPolicy / ArchSig workflow tracked by Issue #1328 and its child Issues.

The previous mixed ArchSig / ArchMap / AIR / theorem-precondition / FieldSig-transition documents are archived under:

- `docs/archive/2026-05-26-tool-docs-pre-archmap-primary/`

Current source-of-truth boundaries:

- ArchMap starts from supplied `archmap-observation-map-v0` evidence read as a source-grounded Atom observation map. It records `atomObservations`, `moleculeObservations`, `semanticObservations`, `observationGaps`, `projectionInfo`, `concernHints`, provenance, and non-conclusions.
- LawPolicy selects laws, witness rules, molecule patterns, obstruction circuit definitions, signature axes, coverage requirements, and exactness assumptions separately from ArchMap.
- ArchSig reads ArchMap + LawPolicy and computes law-relative obstruction / signature analysis. Obstruction circuits and zero-curvature readings are not first-class ArchMap outputs.
- `concernHints` are review cues. They are not obstruction circuits, not law violations, and not theorem evidence.
- Lean / Python import-graph output is optional bounded adapter evidence, emitted explicitly by `archsig adapter-scan`; adapter artifacts retain `coverageBoundary`, `unsupportedConstructs`, `missingEvidence`, and `nonConclusions`.
- ArchSig validation does not prove extractor completeness, semantic correctness, architecture lawfulness, global safety, certified universal atom truth, zero curvature, SFT forecast correctness, or Lean theorem discharge.
- FieldSig / SFT forecast and governance surfaces are not owned by ArchSig. FieldSig consumes ArchMap atom / concern / observation gap refs as boundary-preserving observation refs, not as raw ground-truth guesses.

Atom handoff checklist:

- [Atom Handoff Checklist](atom_handoff.md)
- [LawPolicy](law_policy.md)
- [ArchSig Analysis Packet](archsig_analysis_packet.md)

Forward design PRDs:

- [LLM-native ArchMap / ArchSig PRD](llm_native_archmap_archsig_prd.md)

New implementation-facing specification documents should be added here only when they match the implementation and keep those boundaries explicit. Forward PRDs should keep future schema and migration work separate from the current source-of-truth boundaries above.
