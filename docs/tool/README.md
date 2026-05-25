# Tool Docs

`docs/tool/` is being rebuilt around the ArchMap-homomorphism-primary ArchSig workflow tracked by Issue #1206 and its child Issues.

The previous mixed ArchSig / ArchMap / AIR / theorem-precondition / FieldSig-transition documents are archived under:

- `docs/archive/2026-05-26-tool-docs-pre-archmap-primary/`

Current source-of-truth boundaries:

- ArchSig starts from supplied `archmap-v0` evidence read as a bounded AAT homomorphism. It diagnoses domain / codomain, object map, relation map, law map, obstruction map, signature-axis map, preservation claims, forgetful boundaries, unmeasured boundaries, unsupported boundaries, and non-conclusions.
- ArchSig projects that homomorphism through AIR, theorem precondition checks, Feature Extension Report, and AAT Observable Bundle review artifacts. Feature Report keeps the ArchMap homomorphism family surface, and AAT Observable Bundle derives concept / theorem-boundary review status from the validation checklist and workflow reports.
- Lean / Python import-graph output is optional bounded adapter evidence, emitted explicitly by `archsig adapter-scan`; adapter artifacts retain `coverageBoundary`, `unsupportedConstructs`, `missingEvidence`, and `nonConclusions`.
- ArchSig validation does not prove extractor completeness, semantic correctness, architecture lawfulness, global safety, or Lean theorem discharge.
- FieldSig / SFT forecast and governance surfaces are not owned by ArchSig.

New ArchMap-homomorphism-first specification documents should be added here only when they match the implementation and keep those boundaries explicit.
