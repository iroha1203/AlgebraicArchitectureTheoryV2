# ArchMap Schema Cheatsheet

Use this reference when filling an `archmap-v0` document. Prefer the field names listed here.
When the ArchSig source repository is available, fixtures and schema code may be used as additional
examples, but they are not required for this skill.

## Top-Level Fields

Required top-level shape:

```json
{
  "schemaVersion": "archmap-v0",
  "mapId": "...",
  "architectureId": "...",
  "generatedAt": "2026-05-24T00:00:00Z",
  "generator": {},
  "sourceInventoryRef": {},
  "generationBoundary": {},
  "sourceUniverse": {},
  "targetUniverse": {},
  "mapItems": [],
  "coverage": {},
  "conflicts": [],
  "nonConclusions": []
}
```

Use `promptRefs` when a prompt pack was used.

## Source Universe

`sourceUniverse` must describe what was selected:

- `root`: repository or source root
- `includedRefs`: files, doc sections, tests, runtime traces, policy files, PR artifacts
- `excludedRefs`: intentionally excluded artifacts
- `unavailableRefs`: relevant artifacts not available
- `privateRefs`: relevant private artifacts not inspected
- `hashes`: optional content hashes for reproducibility
- `knownBlindSpots`: dynamic loading, framework convention expansion, runtime traces, private registries
- `selectionBoundary`: one sentence describing the bounded scope

Use `artifactId` values consistently. `mapItems[].sourceRefs[]` should point back to `sourceUniverse.includedRefs[]` when possible.

## Map Item Fields

Each `mapItems[]` entry should include:

- `mapItemId`: stable snake/kebab id
- `mappingKind`: selector for the architecture/SFT interpretation
- `sourceRefs`: evidence refs
- `targetRef`: projected architecture target
- `preserves`: structures preserved by the mapping
- `forgets`: structures intentionally forgotten
- `claimClassification`: claim status
- `measurementBoundary`: measurement status
- `confidence`: review priority, not probability
- `requiredAssumptions`: optional assumptions needed to read the item
- `missingEvidence`: evidence gaps
- `nonConclusions`: claims this item does not make
- `conflictCategory`: optional review cue
- `evidenceRefs` or `theoremRefs`: optional supporting refs when available

## Common `mappingKind` Values

AAT/AIR-facing:

- `object`
- `relation`
- `semanticRole`
- `semanticDiagram`
- `semanticCommutationClaim`
- `nonfillabilityWitness`
- `policyBoundary`
- `reviewBoundary`

SFT-facing:

- `operationCandidate`
- `workflowCandidate`
- `eventCandidate`
- `stateCandidate`
- `stateTransitionCandidate`
- `testOracleCandidate`
- `runtimeObservationCandidate`
- `proposalForceCandidate`

## Common `targetRef.kind` Values

AAT/AIR-facing:

- `air-component`
- `air-relation`
- `air-claim`
- `semantic-diagram`
- `nonfillability-witness`

SFT-facing:

- `sft-operation-candidate`
- `sft-workflow-candidate`
- `sft-event-candidate`
- `sft-state-candidate`
- `sft-transition-candidate`
- `sft-test-oracle-candidate`
- `sft-runtime-observation-candidate`
- `sft-proposal-force-candidate`

Use `targetRef.layer` to separate `static`, `semantic`, `policy`, `runtime`, `framework`, `dynamic`, and `operation` surfaces.

## Classification Values

Prefer these values:

- `measured`: source evidence was inspected and cited.
- `assumed`: supplied doc/policy assumption is used.
- `unmeasured`: relevant evidence was not measured.
- `formal-candidate`: item may connect to Lean proof obligations, but is not discharged.

Prefer these measurement boundaries:

- `measuredNonzero`
- `measuredZero`
- `unmeasured`
- `unavailable`
- `private`
- `notComparable`
- `outOfScope`

Use confidence as qualitative review priority:

- `high`
- `medium`
- `low`

Do not read confidence as probability.

## Coverage

Use coverage to avoid overclaiming:

```json
{
  "measuredLayers": ["static", "semantic"],
  "unmeasuredLayers": ["runtime", "framework", "dynamic"],
  "assumedLayers": ["policy"],
  "unsupportedConstructs": ["dynamic plugin loading"]
}
```

If any `mapItem` is semantic, make sure semantic coverage is recorded as measured, assumed, or unmeasured.

## Validation Checklist

Before validation:

- every `mapItemId` is unique
- source refs resolve to included refs or are clearly boundary refs
- measured claims cite source refs
- missing evidence is not represented as measured zero
- semantic items have semantic coverage
- SFT-facing items are not presented as Lean theorem claims
- non-conclusions exist at both item and top level

Validate with:

```bash
${ARCHSIG_BIN:-archsig} archmap \
  --input <archmap.json> \
  --out .archsig/archmap/validation.json
```
