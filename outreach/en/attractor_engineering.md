---
title: "Attractor Engineering: Seeing Software Development as Field Dynamics"
published: false
description: "A practical and formal view of software evolution as field-shaped dynamics in the age of AI-assisted development."
tags: softwareengineering, architecture, ai, programming
---

> **TL;DR**
>
> - A codebase can be read as a field that attracts future changes, and a pull request can be read as a force applied to that field.
> - A good field makes good changes easier to make. A bad field repeatedly makes bad shortcuts look natural. In an era where AI can produce PRs quickly, this attraction becomes stronger.
> - I call the practice of designing where future changes are pulled **Attractor Engineering**.
> - CI/CD, tests, reviews, and harnesses can be read as dissipative systems: they remove unwanted force and shape the trajectory.
> - ArchSig, or Architecture Signature, is a tool for observing that trajectory along multiple axes.

The first half of this article is written for practitioners: it explains the intuition in terms of codebases, PRs, review, CI, and AI-assisted development. The second half is more mathematical: it connects the same intuition to AAT, Architecture Signature, Lean formalization, and finite counterexamples.

## The First Discovery

The starting point was a simple thought experiment.

What if we look at software architecture not only as a set of directories, design rules, or conventions, but as an **algebraic structure**?

From that point of view, everyday changes such as feature additions, refactorings, splits, migrations, repairs, protections, deletions, and integrations become operations acting on the structure we call architecture.

```text
current codebase
  + feature addition
  + refactoring
  + review fix
  + migration
  + repair
  -> next codebase
```

If we take one more step, we can ask: if these operations are not applied once, but repeated dozens or hundreds of times, can the whole development process be read as a kind of dynamics?

Each individual PR is small.

But after enough PRs, the codebase gradually moves in some direction.

When a good structure already exists, the next change tends to fit into a good place.

When a bad structure exists, a locally natural change tends to take the same bad shortcut again.

Can we treat "where changes tend to go" as something we design?

I decided to call this way of thinking **Attractor Engineering**.

## A Codebase Is a Field, and a PR Is a Force

The central interpretation is this:

```text
codebase = a field that attracts changes
PR       = a force applied to that field
ArchSig  = an observer for the movement
```

A codebase is not a neutral space that passively receives future changes.

Existing names, types, responsibility boundaries, tests, directory structure, previous implementation examples, and review culture all shape which next change feels natural.

A PR is a force applied to that field. Each one may be small, but repeated PRs create a trajectory of change.

```text
current codebase
  -> a PR is applied
  -> an architectural change is observed
  -> a trajectory of change emerges
  -> this becomes the next codebase
```

The important point is that a PR changes the codebase, and the changed codebase then changes what the next PR is likely to look like.

## People and Systems Create the Field

This field is not created only by engineers.

Product managers, product owners, engineers, reviewers, AI agents, CI, tests, design documents, coding standards, and existing examples all participate in it.

Everyone and everything involved in development affects which changes become likely next.

| Participant / mechanism | Effect on the field |
| --- | --- |
| Product manager | Decides which values and demands are repeatedly injected into the system. |
| Product owner | Shapes PRs through requirement granularity, priorities, and acceptance criteria. |
| Engineer / architect | Creates paths for change through boundaries, abstractions, standard patterns, and reference implementations. |
| Reviewer | Pushes back bad force and redirects it toward better directions. |
| CI / tests / types | Rejects, weakens, and narrows inappropriate force. |
| AI agent | Reads the existing field and quickly proposes changes. |

The way requirements are sliced, prioritized, scheduled, and accepted changes how later PRs are produced. Even people who do not write code apply indirect force to the field of the codebase.

This becomes especially important in AI-assisted development. Vague requirements can quickly become vague PRs. If boundaries and non-goals are clear, an AI system is more likely to produce useful changes within those boundaries.

## What Changes in AI-Assisted Development

The essence of AI-assisted development is not simply that code can be written faster.

The more important change is that **the distribution of selected change operations** changes.

An AI system reads existing code, neighboring files, names, types, tests, previous implementation examples, READMEs, and design documents, and then generates the next proposed change.

In other words, the whole codebase becomes input context for the AI.

```text
the codebase becomes input context for AI
  -> AI proposes a change
  -> the proposal becomes a PR
  -> review / CI / merge process handles it
  -> the codebase is updated
  -> the next input context changes
```

If a good reference implementation is nearby, the AI is likely to imitate it.

If a bad shortcut already exists, the AI is also likely to treat it as a natural option.

In this sense, AI rapidly reproduces the local style already present in the field. That is why, in the AI era, what matters is not only the capability of an individual AI agent. The design of the field in which the AI participates matters just as much.

## What Is an Attractor?

When a codebase contains a huge `common` module, an overly convenient helper, or an ambiguous service, changes tend to be pulled there.

Conversely, when good responsibility boundaries and clear implementation examples exist, the next change tends to follow them.

This destination toward which changes are pulled is what I call an attractor. When something moves repeatedly, it often tends to approach certain places or states.

The surrounding region from which things are likely to fall into that attractor is what I call a basin.

Technical debt can be read as a bad basin.

Once a codebase falls into it, locally natural changes keep adding to the same place, and the cost of refactoring out of it grows higher and higher.

The important point is that attractors can be good or bad.

A good attractor pulls in good changes.

A bad attractor makes bad shortcuts get selected again and again.

## What Is Attractor Engineering?

Attractor Engineering is the idea that we should deliberately design these attractors.

Its target is not just the codebase.

It includes the whole development organization: product managers, product owners, engineers, reviewers, AI agents, CI/CD, tests, design documents, and coding standards.

The goal is not only to block bad changes from the outside. The goal is to create a field where good changes are naturally easier to select.

| Part of Attractor Engineering | What it shapes | Examples |
| --- | --- | --- |
| Create the field | Which changes feel natural to propose. | Requirements, priorities, design boundaries, types, APIs, examples, templates. |
| Dissipate bad force | Which proposed changes are rejected, weakened, or redirected. | Harnesses, CI, tests, reviews, PR granularity. |
| Observe the trajectory | How architectural movement becomes visible over time. | ArchSig, architecture features, drift reports. |

Attractor Engineering is an integrated design theory for the era of AI-assisted development. It treats the entire development organization as part of the system.

## Harness Engineering as a Dissipative System

We cannot simply take changes produced by AI and put them directly into the codebase.

Harnesses, CI, tests, type checking, static analysis, and review divide proposed changes into "accept", "fix and check again", and "do not merge".

In Attractor Engineering, this behavior can be read as dissipation.

Dissipation is the mechanism that removes unwanted components of the force entering the field.

If dissipation is too weak, the fast change force produced by AI enters the codebase directly. If it is too strong, nothing moves. A good harness weakens the force that increases debt while preserving the force that moves the product forward.

In this view, CI/CD is not merely a checklist. It is more like brakes, rails, signals, and safety equipment that convert fast PR generation into safe productivity.

What matters in AI-assisted development is not only making the engine stronger.

It is also preparing the field and the dissipative system that can receive a stronger engine.

## What ArchSig Observes

To design the field, we need to observe what is happening.

That is the role of ArchSig.

ArchSig is short for Architecture Signature.

In my [repository](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2), I use it to mean an observation framework for reading changes in a codebase or PR along multiple axes. Dependencies, boundaries, abstractions, runtime exposure, semantic drift, and test observability are not collapsed into a single score. They are treated as multiple features.

ArchSig is an observer for seeing which direction a PR moves the architecture.

For example, we may observe axes like these:

| Axis | What we want to observe |
| --- | --- |
| Static dependencies | Dependency direction and violations of forbidden dependencies. |
| Boundary rules | Connections that cross boundaries or bypass rules. |
| Abstraction leakage | Concrete dependencies that jump over abstractions. |
| Semantic drift | Whether responsibilities or meanings have shifted away from what was intended. |
| Test observability | Whether the change can be observed through tests. |
| Per-PR change | How each axis moves in a single PR. |

The important point is that we do not compress good and bad into one score.

What we want to know is which axes got worse, which axes improved, and what kind of force each change applies.

```text
PR
  -> observe change with ArchSig
  -> observe the trajectory of change
  -> see whether it is moving toward a good or bad region
```

ArchSig becomes an observer for the AI PR era.

Are AI-generated changes moving toward good attractors?

Are they falling into a pool of technical debt?

Is the harness dissipating enough bad force?

ArchSig gives us shared language for discussing those questions.

## PRs Become More Important, Not Less

When AI reduces the cost of generating code, it may look as if PRs become less important.

From a dynamical systems viewpoint, the opposite is true.

A PR is not just a work unit.

A PR has the following roles:

- It cuts continuous change into observable units.
- It lets us separate the directions in which a change acts.
- It embeds the dissipative process of review, CI, and approval.
- It creates a boundary for rollback and reversibility.
- It creates a unit for decision-making and discussion.

What AI lowers is mainly the cost of producing a PR.

But the value of PRs as units of observation, decomposition, dissipation, reversibility, and decision-making increases. In the AI era, PRs do not become unnecessary. They become more important as units for observing and controlling architectural movement.

## Future Development Organizations

In future development organizations, the central problem will not be only how fast we can write code. It will be how to design a field that can safely receive that speed.

A fast train cannot run safely just because it has a powerful motor.

It needs rails, brakes, signals, safety equipment, and operations control.

Software development is similar. AI is a powerful motor, but by itself it can create semantic drift, responsibility drift, degradation of design properties we wanted to preserve, merge confusion, and flow toward technical debt.

What we need is a field with properties like these:

- Small and observable PRs.
- Fast feedback.
- Reliable CI.
- A useful type system.
- Architecture tests.
- Carefully selected reference implementations.
- Isolation of legacy code.
- Clear demands, requirements, and design boundaries.
- Human-designed boundaries for value and acceptance criteria.

The safest AI coding environment is not the one with the strongest external harness. It is the one where good changes are natural, easy to imitate, observable, and less likely to fall into bad shortcuts.

## Summary So Far

The success or failure of AI-assisted development is not determined only by how fast AI can write code.

The direction of the next PR changes depending on the field created by the codebase, requirements, design boundaries, reference implementations, review, CI/CD, and ArchSig.

A good field attracts good changes. A bad field repeatedly makes bad changes look natural. That is why architecture design in the AI era becomes the design of where future changes are attracted.

So far, this has been Attractor Engineering in practical engineering language. In the second half, I translate the same intuition into the language of AAT, Algebraic Architecture Theory, and dynamical systems.

## From Here, in Mathematical Language

The rest of this article uses more mathematical formulation. If you only want the practical view first, it is fine to skip to the [conclusion](#conclusion).

Around AI development, there are many heuristics: "this prompt worked", "this workflow made us faster", and so on. These heuristics are valuable. But by themselves, they make it hard to separate why something worked, how far it generalizes, and under what conditions it breaks.

So I decompose the flow: a change is selected, becomes a PR, passes review / CI, is merged, and then the updated codebase changes the distribution of future changes. By separating state, operation, observation, invariant, obstruction witness, and proof obligation, we can turn heuristics into something easier to test.

## A Short Introduction to AAT

The background theory for this discussion is AAT, or Algebraic Architecture Theory. Here I introduce only the minimal vocabulary needed for the rest of the article.

The Lean snippets below are excerpts from implemented APIs, adjusted for readability. Namespaces, imports, and some proof bodies are omitted.

AAT treats software development not merely as a sequence of code changes, but as a theory of architectural extension, decomposition, repair, and composition.

Its central proposition does not appear in Lean as one large equation. It appears as packages that combine operations and proof obligations.

```lean
structure OperationProofObligation (State : Type u) (Witness : Type v) where
  kind : ArchitectureOperationKind
  obligation : ProofObligation State Witness
  precondition : Prop
  nonConclusion : Prop
```

Operations are first classified as an operation catalog on the Lean side.

```lean
inductive ArchitectureOperationKind where
  | compose
  | refine
  | abstract
  | replace
  | split
  | merge
  | isolate
  | protect
  | migrate
  | reverse
  | contract
  | repair
  | synthesize
  deriving DecidableEq, Repr
```

The important point is that names such as `split` or `repair` prove nothing by themselves. An operation kind is a classification for theorem packages. Claims about preservation, improvement, or repair must be stated separately as proof obligations.

From this viewpoint, a design review is not only the question "is this design good or bad?"

```text
- Is the existing structure embedded after extension?
- Can the new feature be split out from the existing structure?
- Do interactions pass through declared interfaces?
- Which invariants are preserved, and which invariants were broken?
- If a split is not possible, which obstruction witness blocks it?
```

The smallest object in AAT is `ArchitectureCore`.

```lean
structure ArchitectureCore (C : Type u) (A : Type v)
    (StaticObs : Type w) (SemanticExpr : Type q)
    (SemanticObs : Type r) where
  flatness :
    ArchitectureFlatnessModel C A StaticObs SemanticExpr SemanticObs
  staticUniverse : ComponentUniverse flatness.static
  componentDecidableEq : DecidableEq C
  staticEdgeDecidable : DecidableRel flatness.static.edge
  runtimeEdgeDecidable : DecidableRel flatness.runtime.edge
  boundaryPolicyDecidable : DecidableRel flatness.boundaryAllowed
  abstractionPolicyDecidable : DecidableRel flatness.abstractionAllowed
  runtimeRole : C -> C -> RuntimeDependencyRole
  semanticRequiredDecidable :
    ∀ d : RequiredDiagram SemanticExpr,
      Decidable (flatness.requiredSemantic d)
```

Here it is important that `ArchitectureCore` is not the whole real-world codebase itself. It is a finite or bounded object extracted from code, specifications, reviews, and operational observations so that the theory can handle it.

Feature addition is read as an operation that extends an existing architecture into a larger one while preserving the existing architecture.

```text
ExistingCore X
  -> ExtendedArchitecture X'
  -> FeatureView F
```

In a good feature extension, the existing core is preserved inside the extension, the feature view can be extracted in an explainable way, and interactions from the feature to the core pass through declared interfaces. Conversely, hidden dependencies, boundary policy violations, abstraction leakage, runtime exposure, and semantic mismatch are treated not as impressions, but as `ObstructionWitness` values.

To count, remove, preserve, or explicitly decline to conclude about these obstructions, AAT makes `ProofObligation` and `Certificate` explicit.

```lean
structure ProofObligation (State : Type u) (Witness : Type v) where
  formalUniverse : Prop
  requiredLaws : Prop
  invariantFamily : State -> Prop
  witnessUniverse : Witness -> Prop
  coverageAssumptions : Prop
  exactnessAssumptions : Prop
  operationPreconditions : Prop
  conclusion : Prop
  nonConclusions : Prop
```

An obligation is not discharged merely because it exists. It is discharged only when the visible assumptions imply the conclusion.

```lean
def AssumptionsHold (P : ProofObligation State Witness) : Prop :=
  P.formalUniverse ∧
  P.requiredLaws ∧
  P.coverageAssumptions ∧
  P.exactnessAssumptions ∧
  P.operationPreconditions

def Discharged (P : ProofObligation State Witness) : Prop :=
  AssumptionsHold P -> P.conclusion
```

The same is true for certificates. For example, in repair synthesis, if we say "there is no solution", solver failure alone is not enough. Only when a valid certificate exists do we use soundness to conclude that no satisfying architecture exists.

```lean
structure NoSolutionCertificate
    {State : Type u} {Constraint : Type c} (Certificate : Type v)
    (C : SynthesisConstraintSystem State Constraint)
    (cert : Certificate) where
  valid : Prop
  sound : valid -> NoArchitectureSatisfies C
  coverageAssumptions : Prop
  exactnessAssumptions : Prop
  nonConclusions : Prop

theorem sound_of_valid
    (pkg : NoSolutionCertificate Certificate C cert)
    (hValid : ValidNoSolutionCertificate pkg) :
    NoArchitectureSatisfies C
```

`nonConclusions` is not decoration. Even if a static split is proved, runtime flatness or semantic flatness does not automatically follow. Even if no obstruction is found in one observation universe, that does not imply there is no obstruction in every universe. Making this boundary explicit is necessary if we want to treat the theory as testable rather than as a collection of engineering anecdotes.

`ArchitectureSignature` is also not intended to collapse architecture quality into a single score. It is a multi-axis diagnosis for reading multiple invariant and obstruction families axis by axis.

```lean
structure ArchitectureSignatureV1 where
  core : ArchitectureSignatureV1Core
  weightedSccRisk : Option Nat
  projectionSoundnessViolation : Option Nat
  lspViolationCount : Option Nat
  nilpotencyIndex : Option Nat
  runtimePropagation : Option Nat
  relationComplexity : Option Nat
  empiricalChangeCost : Option Nat
  deriving DecidableEq, Repr
```

Some axes are `Option Nat` because an unmeasured value must not be treated as zero. `none` does not mean "no problem". It means "not measured in this universe / extractor / bridge".

```lean
theorem not_axisAvailableAndZero_of_axisValue_none
    {sig : ArchitectureSignatureV1} {axis : ArchitectureSignatureV1Axis}
    (hNone : axisValue sig axis = none) :
    ¬ axisAvailableAndZero sig axis
```

From this perspective, a signature is not a convenient bag of metrics. It is a multi-axis invariant relative to a law universe. For selected required law axes, there are also bridge theorems connecting lawfulness and zero signature axes.

```lean
theorem architectureLawful_iff_requiredSignatureAxesZero
    {C : Type u} {A : Type v} {Obs : Type w}
    (X : ArchitectureLawModel C A Obs)
    [DecidableEq C] [DecidableEq A] [DecidableEq Obs]
    [DecidableRel X.G.edge] [DecidableRel X.GA.edge]
    [DecidableRel X.boundaryAllowed]
    [DecidableRel X.abstractionAllowed] :
    ArchitectureLawful X ↔
      RequiredSignatureAxesZero (ArchitectureLawModel.signatureOf X)
```

AAT does not treat every claim at the same level. It separates definitions, proved theorem packages, bounded bridge theorems, tooling-side evidence, and empirical hypotheses. It also records which universe, observation, coverage, and exactness assumptions each claim is relative to.

The dynamics part below follows the same discipline. The important point is that AAT is not using mathematical vocabulary for atmosphere. It is trying to make the assumptions, conclusions, and non-conclusions part of the type-level structure.

So far, AAT gives us vocabulary for a single architectural state and operations acting on it.

But in AI-assisted development, the central issue is not only a single operation. Requirements, existing code, review, CI, and AI agents change which operation is likely to be selected next, and this selection is repeated many times.

So we need to view AAT operations not only as one-time proof targets, but also as transformations repeatedly selected over time. This is where a chaos-game-like reading enters.

## Formalizing Attractor Dynamics

From here, I use AAT vocabulary to rewrite "field", "force", "dissipation", and "observation" in a more mathematical form.

This is not merely a metaphor that says "AI development is kind of like a chaos game". It is an attempt to place PR force, operation support, trajectory, and basin candidates on top of the AAT vocabulary of state, operation, invariant, obstruction, proof obligation, certificate, and signature.

At this stage, I should be careful: this is not a finished theorem of real-world software development. It is a way to organize phenomena that practitioners can feel, in a structure that may eventually support measurement and verification.

The minimal loop of the dynamics can be read as follows:

```text
architecture field
  -> operation distribution
  -> accepted / rejected transitions
  -> signature trajectory
  -> updated architecture field
```

The position is that architecture quality is not only a property of a snapshot. It is also a property of the future operation distribution and the signature trajectory.

### 1. State, Operation, Observation

Let the architectural state be `X_t`.

Feature addition, repair, split, protection, migration, and refactoring are operations acting on that state.

```text
X_{t+1} = op_t(X_t)
```

The operation `op_t` is not selected uniformly at random.

The current codebase, requirements, prompt, review policy, CI, design boundaries, and organizational judgment all change which operations are likely to be selected.

```text
op_t ~ P(operation | X_t, control_t)
```

This probability expression is notation for the practical reading. The formal core of AAT is not a probability distribution. It is finite or bounded operation support, bounded scripts, accepted transition predicates, and explicit preservation assumptions.

In Lean, for example, operation support is represented not as a probability distribution, but as a finite list of candidate operations for each state.

```lean
structure FiniteOperationKernel
    (State : Type u) (OperationId : Type w) where
  support : State -> List OperationId
  coverageAssumptions : Prop
  weightSourceBoundary : Prop
  normalizationBoundary : Prop
  nonConclusions : Prop
```

Weights, normalization, and completeness of AI-generated proposals are not mixed into the theorem here. Boundaries such as `weightSourceBoundary` and `normalizationBoundary` record what is outside the formal claim, and the probabilistic reading remains outside that core.

Likewise, repeated operation sequences are first treated as bounded scripts.

```lean
structure BoundedOperationScript (OperationId : Type w) where
  operations : List OperationId
  operationFamily : OperationId -> Prop
  operationsInFamily :
    ∀ op, op ∈ operations -> operationFamily op
  coverageAssumptions : Prop
  nonConclusions : Prop
```

This boundary helps avoid confusing probabilistic interpretation with preservation claims over finite support.

Instead of observing the entire state directly, we map it into signature space through an observation function `Obs`.

```text
sigma_t = Obs(X_t)
```

This `sigma_t` is the Architecture Signature.

It contains multi-axis observations such as dependency direction, boundaries, abstraction, runtime exposure, and semantic mismatch.

In Lean, even the observation itself is packaged. The package contains not only the observation function, but also coverage and non-conclusion boundaries.

```lean
structure SignatureObservation (State : Type u) (Sig : Type v) where
  observe : State -> Sig
  coverageAssumptions : Prop
  nonConclusions : Prop
```

When architectural evolution is mapped into observation space, we get a signature trajectory.

```lean
def SignatureTrajectory (O : SignatureObservation State Sig) :
    {X Y : State} -> ArchitectureEvolution State X Y -> List Sig
  | X, _, ArchitecturePath.nil _ => [O.observe X]
  | X, _, ArchitecturePath.cons _step rest =>
      O.observe X :: SignatureTrajectory O rest
```

A change moves the signature.

```text
Delta_t = sigma_{t+1} - sigma_t
```

This `Delta_t` can be read as the force applied by the PR or operation.

However, not every axis admits simple subtraction. For numeric axes, we may read it as a signed delta. For other axes, we read it as a before / after comparison, the appearance of a witness, or a change in state classification.

### 2. PR Force Model

With this structure, a PR becomes more than a diff.

A PR can be read as a force applied to the codebase in the selected Architecture Signature space.

```text
PRForce(PR) = sigma(after(PR)) - sigma(before(PR))
```

The word force here does not mean physical force. It means an observed change in signature, relative to which axes are observed and which differences are defined.

Delta sequences, like trajectories, are relative to finite paths in Lean.

```lean
def SignatureDeltaSequence
    (O : SignatureObservation State Sig) (D : SignatureDelta Sig Delta) :
    {X Y : State} -> ArchitectureEvolution State X Y -> List Delta
  | _, _, ArchitecturePath.nil _ => []
  | X, _, ArchitecturePath.cons (Y := Y) _step rest =>
      D.between (O.observe X) (O.observe Y) ::
        SignatureDeltaSequence O D rest
```

For selected additive deltas, the sum of step deltas agrees with the endpoint delta. This is proved as a theorem.

```lean
theorem netSignatureDelta_telescopes [Zero Delta] [Add Delta]
    (O : SignatureObservation State Sig) (D : SignatureDelta Sig Delta)
    (law : AdditiveSignatureDeltaLaw D) :
    {X Y : State} -> (plan : ArchitectureEvolution State X Y) ->
      NetSignatureDelta (SignatureDeltaSequence O D plan) =
        EndpointSignatureDelta O D plan
```

But this theorem is finite path calculus under the assumption that the selected delta satisfies an additive law. It does not claim that unobserved axes, incident risk, review quality, or actual PR outcomes can all be added this way.

The force has multiple components.

| Force component | Meaning |
| --- | --- |
| Feature force | The force that moves product functionality forward. |
| Repair force | The force that repairs existing breakage. |
| Coupling force | The force that increases or decreases coupling. |
| Boundary force | The force that preserves or violates boundaries. |
| Type force | The force that adds type information or creates type holes. |
| Test force | The force that increases or decreases observability through tests. |
| Debt force | The force that pushes the system toward a bad basin. |
| Refactor force | The force that helps it escape a bad basin. |

A good PR has not only feature force, but also stabilizing force.

```text
v_PR = v_feature + v_stabilize
```

A risky PR moves the feature forward locally while quietly adding small debt force.

```text
v_PR = v_feature + v_debt
```

In AI-generated PRs, the especially important case is one where tests pass and the specification is satisfied, but small `v_debt`, `v_coupling`, `v_type_hole`, or `v_entropy` accumulates repeatedly. It may be hard to see in a single PR. But as a trajectory, the system is moving toward a bad basin. I call this the Local Correctness Trap.

### 3. Three Classes of Force

The earlier discussion about product managers, product owners, review, and CI/CD becomes clearer if we separate force by observability.

Force can be divided into three classes.

| Force class | Meaning | Main evidence |
| --- | --- | --- |
| ObservedForce | Before / after signature delta of PRs that were actually merged. | PRs, ArchSig reports, drift ledger. |
| LatentForce | Invisible force by which requirements, design, prompts, and local code style shape which PRs are proposed. | Requirements, prompts, proposal logs, case studies. |
| DissipatedForce | Raw force that was rejected, corrected, or weakened by review / CI / types / policy. | CI failures, requested changes in review, rejected proposals. |

This classification makes AI-assisted development more concrete.

If we look only at merged PRs, we see only ObservedForce.

But in an era where AI can generate many proposals, the force that was not merged also matters. Force removed by review, rejected by CI, or reshaped before merge matters.

To understand how well a dissipative system is working, we need DissipatedForce.

To understand what kind of PR distribution is created by upstream requirements or prompts, we need LatentForce.

In Lean, the separation between accepted and rejected changes appears as a damping / control schema.

```lean
structure DampingControlSchema (State : Type u) (Sig : Type v) where
  observation : SignatureObservation State Sig
  invariant : SafeRegion Sig
  accepted :
    {X Y : State} -> ArchitectureTransition State X Y -> Prop
  rejected :
    {X Y : State} -> ArchitectureTransition State X Y -> Prop
  acceptedPreservesInvariant :
    ∀ {X Y : State} (t : ArchitectureTransition State X Y),
      accepted t -> StepPreservesSafeRegion observation invariant t
  coverageAssumptions : Prop
  nonConclusions : Prop
```

What this proves is limited: transitions classified as `accepted` preserve the explicitly stated `invariant`. The existence of rejected changes does not prove that the whole future of the codebase is safe.

On top of this schema, it is proved that accepted finite evolutions create trajectories inside the selected invariant.

```lean
theorem acceptedEvolution_preserves_selectedInvariant
    (control : DampingControlSchema State Sig) :
    {X Y : State} -> (plan : ArchitectureEvolution State X Y) ->
      StateInSafeRegion control.observation control.invariant X ->
      control.AcceptedEvolution plan ->
        SignatureTrajectoryInSafeRegion
          control.invariant (SignatureTrajectory control.observation plan)
```

### 4. A Chaos-Game-Like Correspondence

This is where the chaos-game-like reading appears.

The similarity is that we have multiple transformations, one of them is selected at each step, and a state trajectory is produced.

The difference is that, in software development, neither the set of transformations nor their likelihood is fixed. Requirements, review, CI, design boundaries, existing examples, and AI agent behavior all affect which operation is likely to be selected next.

So the goal is not to claim that software development literally is the classical chaos game. The goal is to use AAT vocabulary to handle the structure where multiple operations are repeatedly selected and the resulting trajectory tends to move toward certain regions.

The correspondence is:

| Chaos-game side | AAT / development side |
| --- | --- |
| State `X_t` | Architecture state / codebase field. |
| Transformation `f_i` | Architecture operation / PR / patch. |
| Transformation selection | Operation selection by developer / AI / requirement / review. |
| Trajectory | Architecture Signature trajectory. |
| Attractor | Signature region where the system tends to stay. |
| Basin | Initial or surrounding states likely to fall into that attractor. |
| Control input | Prompt, review policy, CI, type checker, architecture rule. |

As a formula:

```text
X_{t+1} = f_{i_t}(X_t)
i_t ~ P(. | X_t, control_t)
Y_t = sigma(X_t)
```

The important point is not to assert probability or attractors as strong theorems too early.

What we should handle in practice is first an attractor candidate or basin candidate relative to a finite observation window, bounded horizon, selected signature axes, and selected operation support.

```text
finite observed trajectory
  + selected signature region
  + bounded operation support
  -> attractor / basin candidate
```

This is not an escape into weak claims. It is a boundary that makes measurement and falsification possible.

### 5. Support Shaping

The mathematical core of Attractor Engineering is support shaping.

This is not just about "blocking bad PRs". It is about changing the set of operations that can naturally be selected next, and changing how likely they are to be selected.

In short, Attractor Engineering is a theory of designing the geometry of the operation distribution.

```lean
def Supports
    (kernel : FiniteOperationKernel State OperationId)
    (X : State) (op : OperationId) : Prop :=
  op ∈ kernel.support X
```

For the current architecture state `X`, the set of operations that can naturally be selected is called operation support.

Good design changes this support.

```lean
def SupportOperationsPreserveSafeRegion
    (kernel : FiniteOperationKernel State OperationId)
    (sem : OperationTransitionSemantics State OperationId)
    (O : SignatureObservation State Sig) (R : SafeRegion Sig) : Prop :=
  ∀ {X : State} (op : OperationId),
    kernel.Supports X op -> sem.OperationPreservesSafeRegion O R op
```

The strong form of support shaping says: operations that remain in support preserve the selected safe region. In practical terms, we reduce bad operations, increase good operations, make correct paths easier to choose, and make dangerous shortcuts less convenient.

This idea is packaged on the Attractor Engineering side as follows:

```lean
structure AttractorEngineeringSupportPackage
    (State : Type u) (Sig : Type v) (OperationId : Type w) where
  observation : SignatureObservation State Sig
  kernel : FiniteOperationKernel State OperationId
  semantics : OperationTransitionSemantics State OperationId
  targetRegion : SafeRegion Sig
  supportPreserves :
    kernel.SupportOperationsPreserveSafeRegion semantics observation targetRegion
  coverageAssumptions : Prop
  measurementBoundary : Prop
  nonConclusions : Prop
```

With this package, if a bounded script uses only operations from finite support, and the starting point is in the target region, then the observed trajectory remains in the target region. This is stated as a theorem.

```lean
theorem supportPackage_preserves_targetTrajectory
    (package : AttractorEngineeringSupportPackage State Sig OperationId)
    (script : BoundedOperationScript OperationId)
    {X Y : State} (plan : ArchitectureEvolution State X Y)
    (hStart :
      StateInSafeRegion package.observation package.targetRegion X)
    (hRealizes : script.RealizesEvolution package.semantics plan)
    (hSupport :
      package.kernel.ScriptUsesSupport script.operations plan) :
    SignatureTrajectoryInSafeRegion package.targetRegion
      (package.TargetTrajectory plan)
```

For example, good APIs, good examples, clear ownership, narrow modules, and domain states represented in types increase the local discoverability of good operations.

Conversely, a huge common module, implicit global context, ambiguous services, and overly convenient helpers increase the local convenience of bad operations.

From this viewpoint, refactoring is not only cleaning up the current structure. It is also a basin-reshaping operation that changes the future operation distribution.

In the measurement layer, one tooling-side metric candidate to watch here is `SupportRiskMass`.

```text
SupportRiskMass(C) =
  sum over op in support(C) of weight(op) * risk(op, C)
```

Here again, it is important not to reduce `risk` to a simple 0 / 1.

In AAT terms, we should distinguish at least:

```text
safe-preserving proved
safe-preserving measured
safe-preserving estimated
unsafe witness measured
unmeasured
unavailable
private
notComparable
outOfScope
```

Unmeasured must not be read as zero. This is a central principle in both ArchSig and AAT.

### 6. The Same Signature Does Not Imply the Same Future

An important point is that two states can have the same current Architecture Signature but different future operation distributions.

For example, two modules might show the same number of dependency violations, the same test coverage, and the same complexity. But one may have a good canonical example nearby, while the other may contain many bad shortcuts.

Even if the current observation values are the same, future PRs may be attracted in different directions.

```text
Obs(X) = Obs(Y)
  does not imply
OperationSupport(X) = OperationSupport(Y)
```

This is why architecture quality should not be judged by snapshot metrics alone. The current value can be the same while the future force field is different. Attractor Engineering treats this future force field as a design object.

### 7. Accepted Preservation and Support Preservation Are Different

There is another important separation.

Suppose review and CI ensure that merged PRs preserve a safe region.

Even then, unsafe operations may still remain inside operation support.

This separation is not just a warning. It appears on the Lean side as a finite counterexample. Accepted-step invariant preservation can hold, and an accepted safe step can exist, while operations that do not preserve the safe region remain in support.

```lean
theorem acceptedPreservation_not_supportPreservation_counterexample :
    (∃ (t : ArchitectureTransition ExampleState safeState safeState),
      control.AcceptedStep t ∧
        StepPreservesSafeRegion control.observation control.invariant t) ∧
    (∀ {X Y : ExampleState} (t : ArchitectureTransition ExampleState X Y),
      control.AcceptedStep t ->
        StepPreservesSafeRegion control.observation control.invariant t) ∧
    (∃ X op,
      kernel.Supports X op ∧
        ¬ semantics.OperationPreservesSafeRegion control.observation
          control.invariant op)
```

This is the difference between guardrails and attractor engineering.

Strong guardrails may stop bad PRs.

But a field where bad PRs are produced in large numbers every time is still not a good field.

A good field is one where bad operations are less likely to appear in the first place, and good operations are natural, easy to imitate, observable, and low-friction.

### 8. PRs Are Non-Commutative

PRs are generally non-commutative.

```text
PR_2 o PR_1 != PR_1 o PR_2
```

Of course, this only makes sense when both orders can be applied. Even then, the same two PRs can produce different final signatures depending on merge order.

This matters in an era where AI agents can generate multiple PRs in parallel.

Even when individual PRs are locally correct, their order can change boundaries, types, tests, and semantic alignment.

I call this merge order sensitivity.

```text
MergeOrderSensitivity(a, b, X) =
  distance(
    sigma(b(a(X))),
    sigma(a(b(X)))
  )
```

This is not merely a merge conflict issue. It is the non-commutativity of operation algebra branching the signature trajectory. We will need this viewpoint when evaluating teams of AI agents as well.

### 9. Observe the Shape of the Trajectory

Architecture Signature should be read not only as a current value, but also as a trajectory.

Even if the endpoint is safe, the path may have passed through a bad region.

Even if net delta is zero, there may have been large churn inside the path.

```text
endpoint safe
  does not imply path safe

net force zero
  does not imply no excursion
```

This is also proved in Lean as a small finite counterexample. In a trajectory such as `0 -> 2 -> 0`, both endpoints are the same safe state. The endpoint delta and net delta can both appear to be zero, while the path passed through an unsafe region.

```lean
theorem netSignatureDelta_eq_zero :
    NetSignatureDelta (SignatureDeltaSequence observation signedNatDelta
      excursionPlan) = 0

theorem endpointSafe_and_zeroDelta_but_not_pathSafe :
    EndpointSignatureDelta observation signedNatDelta excursionPlan = 0 ∧
      StateInSafeRegion observation safeRegion 0 ∧
      StateInSafeRegion observation safeRegion 0 ∧
      ¬ SignatureTrajectoryInSafeRegion safeRegion
          (SignatureTrajectory observation excursionPlan)
```

Trajectories have shapes.

| Trajectory type | Meaning |
| --- | --- |
| Stable Orbit | The system returns to a safe region after small changes. |
| Drift | The system slowly shifts toward a bad region. |
| Spiral Debt | It appears to return, but over the long run moves closer to a bad basin. |
| Sudden Phase Shift | A signature changes sharply after a particular PR. |
| Oscillation | Feature additions and refactorings alternate between good and bad. |
| Basin Capture | After some point, the system gets captured by a bad structure. |

What ArchSig really wants to observe is this trajectory.

Not just the evaluation of one PR, but the resulting motion produced by a group of PRs.

### 10. Expanding Observation Can Suddenly Reveal Badness

With coarse observation, a codebase may look safe.

But if we add more observation axes, a hidden obstruction may suddenly appear as nonzero.

```text
coarse observation:
  safe

refined observation:
  hidden obstruction appears
```

We can call this an observability expansion shock.

The important point is that this does not necessarily mean the architecture got worse. It may simply mean that an axis that used to be invisible has become visible.

That is why ArchSig must distinguish `unmeasured` from `zero`. When something that was not measured becomes visible, we must separate "the architecture got worse" from "the observation became better".

### About the Lean Formalization

The structure above is not built only from metaphor. Some of the core vocabulary of AAT has been implemented as Lean definitions and theorems under `Formal/Arch`.

The repository is [AlgebraicArchitectureTheoryV2](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2). The proved API lives in the Lean source under `Formal/`.

The vocabulary used in the second half of this article mainly corresponds to `Formal/Arch/Evolution/SignatureDynamics.lean` and `Formal/Arch/Evolution/AttractorEngineering.lean`.

The role of Lean formalization is not to give this theory an aura of correctness. Its role is to record, with boundaries, what can be said under which universe, observation, coverage, and exactness assumptions.

It is important that counterexamples live in the same place as proved theorems.

```text
proved:
  accepted evolution preserves selected invariant
  bounded sampled support-preserving script stays in target region
  selected additive delta telescopes over finite path

proved counterexamples:
  endpoint safe + zero delta does not imply path safe
  accepted preservation does not imply support preservation
  unmeasured axis is not available-zero evidence
```

Conversely, the fact that something is proved in Lean does not mean that a real-world code extractor is complete, or that every runtime / semantic obstruction has already been observed. With this boundary, AAT can separate what is formally known, what depends on measurement, and what remains an empirical research question.

## Conclusion

The discovery of Attractor Engineering changes how I see software architecture: from a static blueprint to a field that guides future changes.

If software architecture is read as an algebraic structure, feature additions and refactorings become operations.

When those operations are repeated, the architecture state draws a trajectory.

We can then ask where that trajectory tends to go, and where it tends to stay. This is where attractors and basins enter the picture.

Architecture design in the era of AI-assisted development can be described as creating a field where future changes gather in good places and can escape bad places.

Harness engineering becomes the engineering of receiving AI's change force, dissipating unwanted components, and guiding the system toward good attractors.

ArchSig is the tool for observing that trajectory.

The essence of AI-assisted development is not only producing PRs faster.

It is deciding where fast force should converge.

A codebase is a field.

A PR is a force.

CI/CD is a dissipative system.

Product managers, product owners, engineers, reviewers, and AI agents are participants in the field.

ArchSig is an observer of the trajectory.

With this framing, development in the AI era is no longer just automation. It becomes field design.

As a design theory for that purpose, Attractor Engineering may be a useful direction for both practice and research.
