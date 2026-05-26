# ArchMap Examples

Use these examples as authoring patterns. Keep examples small and evidence-bound.

## Object Mapping

Good:

```json
{
  "mapItemId": "object-service-user",
  "mappingKind": "object",
  "sourceRefs": [
    {"artifactId": "src-service-user", "kind": "file", "path": "src/services/user.ts", "symbol": "UserService", "line": 12}
  ],
  "targetRef": {"kind": "air-component", "id": "service.user"},
  "preserves": ["component identity"],
  "forgets": ["constructor details"],
  "claimClassification": "measured",
  "measurementBoundary": "measuredNonzero",
  "confidence": "high",
  "missingEvidence": [],
  "nonConclusions": ["service mapping is not global service completeness"]
}
```

Bad:

```json
{
  "mapItemId": "object-service-user",
  "mappingKind": "object",
  "sourceRefs": [],
  "targetRef": {"kind": "air-component", "id": "service.user"},
  "preserves": ["all service semantics"],
  "forgets": [],
  "claimClassification": "measured",
  "measurementBoundary": "measuredNonzero",
  "confidence": "high",
  "missingEvidence": [],
  "nonConclusions": []
}
```

Why bad: it has no evidence refs, overclaims semantics, and lacks boundaries.

## Atomic Observation

Good:

```json
{
  "atomCandidateId": "atom-component-service-user",
  "atomFamily": "Existence.Component",
  "predicate": "component service.user exists",
  "subjectRef": "service.user",
  "objectRefs": ["service.user"],
  "sourceRefs": [
    {"artifactId": "src-service-user", "kind": "file", "path": "src/services/user.ts", "symbol": "UserService", "line": 12}
  ],
  "observationStatus": "observed",
  "measurementBoundary": "measuredNonzero",
  "confidence": "high",
  "uncertainty": [],
  "nonConclusions": ["atom candidate is not a certified ArchitectureAtom"]
}
```

Bad:

```json
{
  "atomCandidateId": "atom-obstruction-user-saga",
  "atomFamily": "Obstruction.MissingCompensation",
  "predicate": "saga is bad",
  "subjectRef": "user_saga",
  "objectRefs": [],
  "sourceRefs": [],
  "observationStatus": "certified",
  "measurementBoundary": "measuredNonzero",
  "confidence": "high",
  "uncertainty": [],
  "nonConclusions": []
}
```

Why bad: obstruction is a circuit over observed facts, not a primitive atom, and ArchMap does not certify atoms.

Good obstruction circuit:

```json
{
  "circuitCandidateId": "circuit-user-saga-missing-compensation",
  "circuitKind": "FailedFilling",
  "lawRef": "law:semantic-compensation",
  "atomCandidateRefs": ["atom-contract-create-user"],
  "moleculeCandidateRefs": ["molecule-user-request-responsibility"],
  "sourceRefs": [
    {"artifactId": "test-user-contract", "kind": "test", "path": "tests/user_contract.test.ts", "symbol": "createsUser"}
  ],
  "observationStatus": "observed",
  "measurementBoundary": "measuredNonzero",
  "claimBoundary": "selected witness; not incident causality",
  "nonConclusions": ["obstruction circuit candidate is not an ArchitectureAtom"]
}
```

## Semantic Relation

Good:

```json
{
  "mapItemId": "relation-route-service",
  "mappingKind": "relation",
  "sourceRefs": [
    {"artifactId": "src-route-users", "kind": "file", "path": "src/routes/users.ts", "symbol": "createUserRoute", "line": 42},
    {"artifactId": "src-service-user", "kind": "file", "path": "src/services/user.ts", "symbol": "UserService", "line": 12}
  ],
  "targetRef": {
    "kind": "air-relation",
    "layer": "semantic",
    "id": "relation-route-service",
    "from": "route.users",
    "to": "service.user",
    "subjectRef": "semantic.route.users->service.user",
    "predicate": "route delegates user creation to service"
  },
  "preserves": ["request-to-service semantic dependency"],
  "forgets": ["call count", "runtime frequency"],
  "claimClassification": "measured",
  "measurementBoundary": "measuredNonzero",
  "confidence": "medium",
  "missingEvidence": [],
  "nonConclusions": [
    "semantic relation is not complete over all routes",
    "LLM-authored relation does not prove runtime relation"
  ],
  "conflictCategory": "missing-static-edge"
}
```

Bad:

```json
{
  "mapItemId": "relation-route-service",
  "mappingKind": "relation",
  "sourceRefs": [{"artifactId": "src-route-users", "kind": "file", "path": "src/routes/users.ts"}],
  "targetRef": {"kind": "air-relation", "layer": "semantic", "from": "route.users", "to": "service.user"},
  "preserves": ["runtime dependency is proven"],
  "forgets": [],
  "claimClassification": "measured",
  "measurementBoundary": "measuredNonzero",
  "confidence": "high",
  "missingEvidence": [],
  "nonConclusions": []
}
```

Why bad: one source ref is insufficient for the relation, runtime is overclaimed, and the item has no non-conclusion.

## Semantic Diagram

Good:

```json
{
  "mapItemId": "contract_preservation",
  "mappingKind": "semanticDiagram",
  "sourceRefs": [
    {"artifactId": "src-user-contract", "kind": "test", "path": "tests/user_contract.test.ts", "symbol": "createsUser"}
  ],
  "targetRef": {
    "kind": "semantic-diagram",
    "layer": "semantic",
    "id": "diagram-contract-preservation",
    "from": "request.createUser",
    "to": "state.userCreated",
    "lhsPathRef": "path-route-service-contract",
    "rhsPathRef": "path-service-contract",
    "equivalence": "observational",
    "subjectRef": "semantic.contract.create_user",
    "predicate": "selected contract observation is preserved across the route-service path"
  },
  "preserves": ["contract preservation", "contract-test observation"],
  "forgets": ["all production traces"],
  "claimClassification": "measured",
  "measurementBoundary": "measuredNonzero",
  "confidence": "medium",
  "missingEvidence": [],
  "nonConclusions": ["contract preservation cue is selected-test relative"]
}
```

Bad:

```json
{
  "mapItemId": "contract_preservation",
  "mappingKind": "semanticDiagram",
  "sourceRefs": [{"artifactId": "src-user-contract", "kind": "test", "path": "tests/user_contract.test.ts"}],
  "targetRef": {"kind": "semantic-diagram", "layer": "semantic"},
  "preserves": ["all user creation semantics"],
  "forgets": [],
  "claimClassification": "measured",
  "measurementBoundary": "measuredNonzero",
  "confidence": "high",
  "missingEvidence": [],
  "nonConclusions": []
}
```

Why bad: it turns a selected contract observation into a global semantic claim.

## SFT Operation Candidate

Good:

```json
{
  "mapItemId": "operation-user-signup",
  "mappingKind": "operationCandidate",
  "sourceRefs": [
    {"artifactId": "src-saga", "kind": "file", "path": "src/workflows/user_signup_saga.ts", "symbol": "UserSignupSaga"}
  ],
  "targetRef": {
    "kind": "sft-operation-candidate",
    "layer": "operation",
    "id": "operation.user_signup",
    "subjectRef": "operation.user_signup",
    "predicate": "selected signup workflow is an operation-support candidate"
  },
  "preserves": ["operation support candidate", "workflow source ref"],
  "forgets": ["forecast correctness", "incident causality"],
  "claimClassification": "measured",
  "measurementBoundary": "measuredNonzero",
  "confidence": "medium",
  "missingEvidence": ["runtime success/failure distribution not supplied"],
  "nonConclusions": [
    "operation candidate is not a ForecastCone result",
    "operation candidate does not prove future trajectory"
  ]
}
```

Bad:

```json
{
  "mapItemId": "forecast-user-signup",
  "mappingKind": "operationCandidate",
  "sourceRefs": [{"artifactId": "src-saga", "kind": "file", "path": "src/workflows/user_signup_saga.ts"}],
  "targetRef": {"kind": "sft-operation-candidate", "id": "operation.user_signup"},
  "preserves": ["this workflow will reduce risk"],
  "forgets": [],
  "claimClassification": "measured",
  "measurementBoundary": "measuredNonzero",
  "confidence": "high",
  "missingEvidence": [],
  "nonConclusions": []
}
```

Why bad: ArchMap cannot author risk reduction, forecast correctness, or future trajectory claims.

## Runtime Missing Evidence

Good:

```json
{
  "mapItemId": "runtime_static_disagreement",
  "mappingKind": "reviewBoundary",
  "sourceRefs": [
    {"artifactId": "src-runtime-trace", "kind": "runtimeTrace", "path": ".archsig/runtime-trace.json"},
    {"artifactId": "src-static-edge", "kind": "file", "path": "src/db/user_db.ts", "symbol": "UserDb"}
  ],
  "targetRef": {
    "kind": "air-claim",
    "layer": "runtime",
    "id": "claim-runtime-static-disagreement",
    "subjectRef": "runtime.service_user.db_users",
    "predicate": "runtime edge is unavailable while static code suggests a database dependency"
  },
  "preserves": ["runtime/static disagreement"],
  "forgets": ["runtime frequency"],
  "claimClassification": "unmeasured",
  "measurementBoundary": "unmeasured",
  "confidence": "low",
  "missingEvidence": ["runtime trace not supplied"],
  "nonConclusions": ["unavailable runtime edge is not measured zero"],
  "conflictCategory": "semantic-runtime-disagreement"
}
```

Bad:

```json
{
  "mapItemId": "runtime_static_disagreement",
  "mappingKind": "reviewBoundary",
  "sourceRefs": [{"artifactId": "src-static-edge", "kind": "file", "path": "src/db/user_db.ts"}],
  "targetRef": {"kind": "air-claim", "layer": "runtime"},
  "preserves": ["no runtime dependency exists"],
  "forgets": [],
  "claimClassification": "measured",
  "measurementBoundary": "measuredZero",
  "confidence": "high",
  "missingEvidence": [],
  "nonConclusions": []
}
```

Why bad: unavailable runtime evidence is not measured zero.
