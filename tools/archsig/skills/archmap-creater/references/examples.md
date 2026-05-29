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

## From Code Fragment To Atoms

Source fragment:

```ts
import { CustomerRepository } from "../repositories/customer";
import { EventBus } from "../events/bus";

export class CustomerService {
  private cache: CustomerCache;

  constructor(
    private readonly customers: CustomerRepository,
    private readonly events: EventBus
  ) {}

  async updateEmail(actor: Actor, customerId: string, email: string): Promise<CustomerDto> {
    requireWorkspaceRole(actor, "workspace-admin");
    const customer = await this.customers.findById(customerId);
    customer.email = normalizeEmail(email);
    await this.customers.save(customer);
    await this.events.publish("customer.email.updated", { customerId });
    return toCustomerDto(customer);
  }
}
```

The source fragment can support several primitive atom observations. Do not compress them into
one atom such as "CustomerService handles customer email updates correctly".

Good atom set:

```json
[
  {
    "atomObservationId": "atom:existence:customer-service",
    "atomFamily": "existence",
    "predicate": "CustomerService is a service component",
    "subjectRef": "service.customer",
    "objectRefs": ["CustomerService"],
    "sourceRefs": [
      {"artifactId": "src-customer-service", "kind": "file", "path": "src/services/customer.ts", "symbol": "CustomerService"}
    ],
    "observationStatus": "observed",
    "evidenceBoundary": "sourceObserved",
    "confidence": "high",
    "uncertainty": [],
    "projectionRefs": [],
    "nonConclusions": ["component existence does not prove service responsibility boundaries"]
  },
  {
    "atomObservationId": "atom:relation:customer-service-repository-import",
    "atomFamily": "relation",
    "predicate": "CustomerService source imports CustomerRepository",
    "subjectRef": "service.customer",
    "objectRefs": ["repository.customer"],
    "sourceRefs": [
      {"artifactId": "src-customer-service", "kind": "file", "path": "src/services/customer.ts", "symbol": "CustomerRepository"}
    ],
    "observationStatus": "observed",
    "evidenceBoundary": "sourceObserved",
    "confidence": "high",
    "uncertainty": ["static import does not measure runtime call frequency"],
    "projectionRefs": [],
    "nonConclusions": ["relation atom is not a complete dependency graph"]
  },
  {
    "atomObservationId": "atom:state:customer-service-cache",
    "atomFamily": "state",
    "predicate": "CustomerService declares a CustomerCache state field",
    "subjectRef": "service.customer",
    "objectRefs": ["state.customerCache"],
    "sourceRefs": [
      {"artifactId": "src-customer-service", "kind": "file", "path": "src/services/customer.ts", "symbol": "cache"}
    ],
    "observationStatus": "observed",
    "evidenceBoundary": "sourceObserved",
    "confidence": "high",
    "uncertainty": ["cache lifecycle and invalidation policy are not shown in this fragment"],
    "projectionRefs": [],
    "nonConclusions": ["state atom does not prove cache consistency"]
  },
  {
    "atomObservationId": "atom:authority:update-email-admin-role",
    "atomFamily": "authority",
    "predicate": "updateEmail requires workspace-admin role before mutation",
    "subjectRef": "operation.customer.updateEmail",
    "objectRefs": ["role.workspace-admin", "resource.customer"],
    "sourceRefs": [
      {"artifactId": "src-customer-service", "kind": "file", "path": "src/services/customer.ts", "symbol": "requireWorkspaceRole"}
    ],
    "observationStatus": "observed",
    "evidenceBoundary": "sourceObserved",
    "confidence": "high",
    "uncertainty": ["the implementation of requireWorkspaceRole is not inspected by this fragment"],
    "projectionRefs": [],
    "nonConclusions": ["authority atom does not prove complete authorization coverage"]
  },
  {
    "atomObservationId": "atom:contract:update-email-return-shape",
    "atomFamily": "contractSpecification",
    "predicate": "updateEmail accepts actor, customer id, and email, and returns Promise<CustomerDto>",
    "subjectRef": "operation.customer.updateEmail",
    "objectRefs": ["Actor", "CustomerDto"],
    "sourceRefs": [
      {"artifactId": "src-customer-service", "kind": "file", "path": "src/services/customer.ts", "symbol": "updateEmail"}
    ],
    "observationStatus": "observed",
    "evidenceBoundary": "sourceObserved",
    "confidence": "high",
    "uncertainty": ["type annotation does not prove runtime validation of email"],
    "projectionRefs": [],
    "nonConclusions": ["contract atom does not prove all executions satisfy the return type"]
  },
  {
    "atomObservationId": "atom:effect:customer-save",
    "atomFamily": "effect",
    "predicate": "updateEmail persists the mutated customer through CustomerRepository.save",
    "subjectRef": "operation.customer.updateEmail",
    "objectRefs": ["repository.customer.save"],
    "sourceRefs": [
      {"artifactId": "src-customer-service", "kind": "file", "path": "src/services/customer.ts", "symbol": "customers.save"}
    ],
    "observationStatus": "observed",
    "evidenceBoundary": "sourceObserved",
    "confidence": "high",
    "uncertainty": ["repository transaction behavior is not shown in this fragment"],
    "projectionRefs": [],
    "nonConclusions": ["effect atom does not prove commit success"]
  },
  {
    "atomObservationId": "atom:effect:customer-email-event",
    "atomFamily": "effect",
    "predicate": "updateEmail publishes customer.email.updated after saving the customer",
    "subjectRef": "operation.customer.updateEmail",
    "objectRefs": ["event.customer.email.updated"],
    "sourceRefs": [
      {"artifactId": "src-customer-service", "kind": "file", "path": "src/services/customer.ts", "symbol": "events.publish"}
    ],
    "observationStatus": "observed",
    "evidenceBoundary": "sourceObserved",
    "confidence": "high",
    "uncertainty": ["event bus delivery and subscriber behavior are not shown in this fragment"],
    "projectionRefs": [],
    "nonConclusions": ["effect atom does not prove event delivery"]
  }
]
```

Bad coarse atom:

```json
{
  "atomObservationId": "atom:customer-service:update-email-workflow",
  "atomFamily": "semantic",
  "predicate": "CustomerService correctly updates customer email with authorization, persistence, and event publication",
  "subjectRef": "service.customer",
  "objectRefs": [],
  "sourceRefs": [
    {"artifactId": "src-customer-service", "kind": "file", "path": "src/services/customer.ts"}
  ],
  "observationStatus": "observed",
  "evidenceBoundary": "sourceObserved",
  "confidence": "high",
  "uncertainty": [],
  "projectionRefs": [],
  "nonConclusions": []
}
```

Why bad: it hides existence, relation, state, authority, contract, and effect facts inside one broad statement and adds correctness. The workflow reading can be a `semanticObservations[]` entry after primitive atoms exist, but it is not a primitive atom.

## Atom Family Choice

Good authority atom:

```json
{
  "atomObservationId": "atom:authority:workspace-role-gate",
  "atomFamily": "authority",
  "predicate": "workspace route checks member role before invoking workspace operation",
  "subjectRef": "route.workspace.membership",
  "objectRefs": ["role.workspaceMember", "operation.workspace"],
  "sourceRefs": [
    {"artifactId": "src-workspace-route", "kind": "file", "path": "src/routes/workspace.ts", "symbol": "requireWorkspaceMember"},
    {"artifactId": "src-permissions", "kind": "file", "path": "src/auth/permissions.ts", "symbol": "requireWorkspaceMember"}
  ],
  "observationStatus": "observed",
  "evidenceBoundary": "sourceObserved",
  "confidence": "high",
  "uncertainty": ["route-by-route coverage outside the cited route is not claimed"],
  "projectionRefs": [],
  "nonConclusions": ["authority atom does not prove complete permission coverage"]
}
```

Bad authority atom:

```json
{
  "atomObservationId": "atom:authority:all-workspace-access",
  "atomFamily": "authority",
  "predicate": "all workspace access is correctly permissioned",
  "subjectRef": "workspace",
  "objectRefs": [],
  "sourceRefs": [
    {"artifactId": "src-user-model", "kind": "file", "path": "src/models/user.ts"}
  ],
  "observationStatus": "observed",
  "evidenceBoundary": "sourceObserved",
  "confidence": "high",
  "uncertainty": [],
  "projectionRefs": [],
  "nonConclusions": []
}
```

Why bad: a user model or role field alone does not show full route permission coverage. This should become smaller authority atoms for observed guards plus an observation gap for unaudited routes.

Good effect atom:

```json
{
  "atomObservationId": "atom:effect:invoice-email-send",
  "atomFamily": "effect",
  "predicate": "invoice service delegates invoice email delivery to an email provider",
  "subjectRef": "service.invoice",
  "objectRefs": ["provider.email"],
  "sourceRefs": [
    {"artifactId": "src-invoice-service", "kind": "file", "path": "src/services/invoice.ts", "symbol": "sendInvoiceEmail"}
  ],
  "observationStatus": "observed",
  "evidenceBoundary": "sourceObserved",
  "confidence": "high",
  "uncertainty": ["provider runtime delivery outcome was not inspected"],
  "projectionRefs": [],
  "nonConclusions": ["effect atom does not prove email delivery success"]
}
```

Bad effect atom:

```json
{
  "atomObservationId": "atom:effect:email-success",
  "atomFamily": "effect",
  "predicate": "invoice emails are delivered successfully",
  "subjectRef": "provider.email",
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

Why bad: delivery success is runtime/provider evidence. Without supplied provider traces it belongs in an observation gap or non-conclusion, not an observed effect atom.

Good contract atom:

```json
{
  "atomObservationId": "atom:contract:refresh-token-rotation",
  "atomFamily": "contractSpecification",
  "predicate": "refresh token rotation accepts the previous token only within a bounded grace rule",
  "subjectRef": "auth.refreshTokenRotation",
  "objectRefs": ["state.refreshToken", "contract.rotationGrace"],
  "sourceRefs": [
    {"artifactId": "src-refresh-service", "kind": "file", "path": "src/auth/refresh-token.ts", "symbol": "rotateRefreshToken"}
  ],
  "observationStatus": "observed",
  "evidenceBoundary": "sourceObserved",
  "confidence": "high",
  "uncertainty": ["concurrent production behavior was not traced"],
  "projectionRefs": [],
  "nonConclusions": ["contract atom does not prove all concurrent executions are correct"]
}
```

Bad contract atom:

```json
{
  "atomObservationId": "atom:contract:auth-correct",
  "atomFamily": "contractSpecification",
  "predicate": "authentication is correct",
  "subjectRef": "auth",
  "objectRefs": [],
  "sourceRefs": [
    {"artifactId": "test-auth", "kind": "test", "path": "tests/auth.test.ts"}
  ],
  "observationStatus": "observed",
  "evidenceBoundary": "sourceObserved",
  "confidence": "high",
  "uncertainty": [],
  "projectionRefs": [],
  "nonConclusions": []
}
```

Why bad: a selected test may support a bounded contract observation, not global authentication correctness.

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
