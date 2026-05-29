# ArchMap Observation Examples

Use these examples as authoring patterns. Keep examples small and evidence-bound.

## Atom Observation

Good:

```json
{
  "atomObservationId": "atom:component:service-user",
  "atomFamily": "existence",
  "predicate": "component service.user exists",
  "subjectRef": "service.user",
  "objectRefs": ["service.user"],
  "sourceRefs": [
    {"artifactId": "src-service-user", "kind": "file", "path": "src/services/user.ts", "symbol": "UserService", "line": 12}
  ],
  "observationStatus": "observed",
  "evidenceBoundary": "sourceObserved",
  "confidence": "high",
  "uncertainty": [],
  "projectionRefs": ["projection:aat:service-user"],
  "nonConclusions": ["atom observation is not a certified universal ArchitectureAtom"]
}
```

Bad:

```json
{
  "atomObservationId": "atom:obstruction:user-saga",
  "atomFamily": "obstruction",
  "predicate": "saga violates compensation law",
  "subjectRef": "user_saga",
  "objectRefs": [],
  "sourceRefs": [],
  "observationStatus": "certified",
  "evidenceBoundary": "sourceObserved",
  "confidence": "high",
  "uncertainty": [],
  "projectionRefs": [],
  "nonConclusions": []
}
```

Why bad: obstruction and law violation are law-relative ArchSig readings, not ArchMap atom observations. It also has no source refs and claims certification.

## Molecule Observation

Good:

```json
{
  "moleculeObservationId": "molecule:user-request-responsibility",
  "moleculeFamily": "responsibility",
  "roleName": "user request orchestration",
  "atomObservationRefs": [
    "atom:component:route-users",
    "atom:component:service-user",
    "atom:relation:route-service"
  ],
  "sourceRefs": [
    {"artifactId": "doc-architecture", "kind": "docSection", "path": "docs/architecture.md", "section": "Layer policy"}
  ],
  "observationStatus": "observed",
  "evidenceBoundary": "sourceObserved",
  "confidence": "medium",
  "nonConclusions": ["responsibility is a molecule over atom observations, not a primitive atom"]
}
```

Bad:

```json
{
  "atomObservationId": "atom:responsibility:user-request",
  "atomFamily": "responsibility",
  "predicate": "UserService owns all user request behavior",
  "subjectRef": "service.user",
  "objectRefs": [],
  "sourceRefs": [],
  "observationStatus": "observed",
  "evidenceBoundary": "sourceObserved",
  "confidence": "high",
  "uncertainty": [],
  "projectionRefs": [],
  "nonConclusions": []
}
```

Why bad: responsibility is composed from observed atoms and source context; it should be a molecule observation with boundaries.

## Semantic Observation

Good:

```json
{
  "semanticObservationId": "semantic:create-user-flow",
  "semanticFamily": "operationMeaning",
  "subjectRef": "operation.createUser",
  "predicate": "route, service, and contract jointly describe create-user behavior",
  "atomObservationRefs": [
    "atom:relation:route-service",
    "atom:contract:create-user"
  ],
  "moleculeObservationRefs": ["molecule:user-request-responsibility"],
  "sourceRefs": [
    {"artifactId": "doc-architecture", "kind": "docSection", "path": "docs/architecture.md", "section": "Layer policy"},
    {"artifactId": "test-user-contract", "kind": "test", "path": "tests/user_contract.test.ts", "symbol": "createsUser"}
  ],
  "observationStatus": "observed",
  "evidenceBoundary": "sourceObserved",
  "nonConclusions": ["semantic observation is not a proof of global semantic correctness"]
}
```

Bad:

```json
{
  "semanticObservationId": "semantic:create-user-global",
  "semanticFamily": "operationMeaning",
  "subjectRef": "operation.createUser",
  "predicate": "all create-user executions are correct",
  "atomObservationRefs": [],
  "moleculeObservationRefs": [],
  "sourceRefs": [{"artifactId": "test-user-contract", "kind": "test", "path": "tests/user_contract.test.ts"}],
  "observationStatus": "observed",
  "evidenceBoundary": "sourceObserved",
  "nonConclusions": []
}
```

Why bad: it turns a selected test or doc reading into global correctness.

## Observation Gap

Good:

```json
{
  "gapId": "gap-runtime-user-db-trace",
  "gapKind": "UnavailableRuntimeTrace",
  "subjectRef": "runtime.service.user->db.users",
  "evidenceStatus": "unavailable",
  "reason": "runtime trace was requested but not supplied",
  "expectedAtomFamilies": ["runtimeInteraction", "effect"],
  "sourceRefs": [
    {"kind": "runtimeTrace", "path": ".archsig/runtime-trace.json"}
  ],
  "nonConclusions": ["unavailable runtime trace is not measured zero"]
}
```

Bad:

```json
{
  "atomObservationId": "atom:runtime:user-db-none",
  "atomFamily": "runtimeInteraction",
  "predicate": "service.user has no runtime database interaction",
  "subjectRef": "service.user",
  "objectRefs": ["db.users"],
  "sourceRefs": [],
  "observationStatus": "observed",
  "evidenceBoundary": "sourceObserved",
  "confidence": "high",
  "uncertainty": [],
  "projectionRefs": [],
  "nonConclusions": []
}
```

Why bad: unavailable runtime evidence cannot be rewritten as observed absence.

## Projection Info

Good:

```json
{
  "projectionId": "projection:sft:create-user",
  "projectionFamily": "operationCandidate",
  "sourceObservationRef": "semantic:create-user-flow",
  "targetSurface": "sft:operation:create-user",
  "reading": "semantic observation can be handed off as bounded SFT evidence after ArchSig analysis",
  "projectionBoundary": "SFT consequence analysis is not owned by ArchMap",
  "nonConclusions": ["projection is not a forecast correctness claim"]
}
```

Bad:

```json
{
  "projectionId": "projection:sft:forecast-create-user",
  "projectionFamily": "forecastCone",
  "sourceObservationRef": "semantic:create-user-flow",
  "targetSurface": "sft:forecast:create-user",
  "reading": "this change will reduce risk",
  "projectionBoundary": "computed by ArchMap",
  "nonConclusions": []
}
```

Why bad: ForecastCone and consequence analysis belong to FieldSig, not ArchMap.

## Concern Hint

Good:

```json
{
  "concernHintId": "concern:missing-compensation",
  "concernFamily": "missingCompensation",
  "subjectRef": "operation.createUser",
  "atomObservationRefs": ["atom:contract:create-user"],
  "moleculeObservationRefs": ["molecule:user-request-responsibility"],
  "semanticObservationRefs": ["semantic:create-user-flow"],
  "sourceRefs": [
    {"artifactId": "test-user-contract", "kind": "test", "path": "tests/user_contract.test.ts", "symbol": "createsUser"}
  ],
  "evidenceBoundary": "review cue from observed contract atom and semantic observation",
  "analysisBoundary": "not an obstruction circuit; ArchSig must combine this ArchMap with LawPolicy before constructing obstruction witnesses",
  "nonConclusions": [
    "concern hint does not prove a law violation",
    "concern hint is not an obstruction circuit"
  ]
}
```

Bad:

```json
{
  "concernHintId": "concern:missing-compensation",
  "concernFamily": "obstructionCircuit",
  "subjectRef": "operation.createUser",
  "atomObservationRefs": ["atom:contract:create-user"],
  "moleculeObservationRefs": [],
  "semanticObservationRefs": [],
  "sourceRefs": [],
  "evidenceBoundary": "proved violation",
  "analysisBoundary": "ArchMap computed the obstruction",
  "nonConclusions": []
}
```

Why bad: `concernHints[]` are not obstruction circuits. They remain review cues until ArchSig combines ArchMap with LawPolicy.
