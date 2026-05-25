# Tool Docs

`docs/tool/` is being rebuilt around the ArchMap-primary ArchSig workflow tracked by Issue #1203 and Issue #1204.

The previous mixed ArchSig / ArchMap / AIR / theorem-precondition / FieldSig-transition documents are archived under:

- `docs/archive/2026-05-26-tool-docs-pre-archmap-primary/`

Current source-of-truth boundaries:

- ArchSig starts from supplied `archmap-v0` evidence and projects it through AIR, theorem precondition checks, Feature Extension Report, and AAT Observable Bundle review artifacts.
- Lean / Python import-graph output is optional bounded adapter evidence, emitted explicitly by `archsig adapter-scan`; adapter artifacts retain `coverageBoundary`, `unsupportedConstructs`, `missingEvidence`, and `nonConclusions`.
- ArchSig validation does not prove extractor completeness, semantic correctness, architecture lawfulness, global safety, or Lean theorem discharge.
- FieldSig / SFT forecast and governance surfaces are not owned by ArchSig.

New ArchMap-first specification documents should be added here only when they match the implementation and keep those boundaries explicit.
