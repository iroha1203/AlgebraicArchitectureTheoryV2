# Tool Docs

`docs/tool/` is being rebuilt around the ArchMap-homomorphism-primary ArchSig workflow tracked by Issue #1206 and its child Issues.

The previous mixed ArchSig / ArchMap / AIR / theorem-precondition / FieldSig-transition documents are archived under:

- `docs/archive/2026-05-26-tool-docs-pre-archmap-primary/`

Current source-of-truth boundaries:

- ArchSig starts from supplied `archmap-v0` evidence read as a bounded AAT homomorphism and atomic observation surface. It diagnoses domain / codomain, object map, relation map, law map, obstruction map, signature-axis map, atom candidates, molecule candidates, obstruction circuit candidates, observation gaps, preservation claims, forgetful boundaries, unmeasured boundaries, unsupported boundaries, and non-conclusions.
- ArchSig projects that homomorphism through AIR, theorem precondition checks, Feature Extension Report, and AAT Observable Bundle review artifacts. Feature Report keeps the ArchMap homomorphism family surface, and AAT Observable Bundle derives concept / theorem-boundary review status from the validation checklist and workflow reports.
- The atomic observation surface is observational, not definitional. `atomCandidates` are source-grounded candidate facts, `moleculeCandidates` group atoms into roles such as responsibility, `obstructionCircuitCandidates` are composed failed-filling / failed-lifting witnesses, and `observationGaps` are explicit unknown/private/unavailable boundaries.
- ArchMap validation reports a Lean-facing AtomPresentation promotion boundary. This boundary identifies promotable observed candidates and presentation refs, but it does not certify universal `ArchitectureAtom` truth or discharge Lean theorem preconditions.
- Lean / Python import-graph output is optional bounded adapter evidence, emitted explicitly by `archsig adapter-scan`; adapter artifacts retain `coverageBoundary`, `unsupportedConstructs`, `missingEvidence`, and `nonConclusions`.
- ArchSig validation does not prove extractor completeness, semantic correctness, architecture lawfulness, global safety, certified universal atom truth, zero curvature, SFT forecast correctness, or Lean theorem discharge.
- FieldSig / SFT forecast and governance surfaces are not owned by ArchSig. FieldSig consumes ArchMap atom / circuit / observation gap refs as boundary-preserving observation refs, not as raw ground-truth guesses.

Atom handoff checklist:

- [Atom Handoff Checklist](atom_handoff.md)

New ArchMap-homomorphism-first specification documents should be added here only when they match the implementation and keep those boundaries explicit.
