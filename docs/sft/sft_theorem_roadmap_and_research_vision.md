# SFT Theorem Roadmap and Research Vision

## 1. Core Thesis

Software engineering has long fought the limits of human understanding.

For decades, software architecture has been understood primarily as a discipline for organizing complexity so that humans can read, reason about, maintain, and safely modify software systems.

This view remains important, but AI changes the bottleneck.

When code can be generated faster than it can be socially absorbed, the central question shifts:

> from understanding the present system<br>
> to governing the evolution of future systems.

In this new setting, architecture is no longer only a static structure for human understanding. It becomes a field that shapes which software futures become reachable.

SFT — Software Field Theory — aims to formalize this shift.

> **SFT extends software architecture from the science of understanding systems to the science of shaping their evolution.**

Or more sharply:

> **Architecture is not only the shape of present code.<br>
> It is the shape of reachable futures.**

## 2. From Static Architecture to Software Evolution

Traditional architecture asks questions such as:

- How should responsibilities be separated?
- How should dependencies be controlled?
- How can humans understand the system?
- How can change be localized?
- How can review remain possible?

SFT does not reject these questions. Instead, it reinterprets them dynamically.

A good architecture is not merely one that is easy to understand today. A good architecture is one in which:

- desirable futures are reachable;
- undesirable futures are hard to reach;
- local changes remain locally understandable;
- local futures can be glued into global futures;
- AI-generated proposals are shaped toward safe paths;
- review, CI, governance, and runtime feedback modify the field of future possibilities.

In SFT terms:

> **A software architecture is modular exactly when its future evolution satisfies descent.**

This turns architecture from a static design artifact into a computational object of software evolution.

## 3. Existing SFT Computational Core

The current SFT computation layer already contains the essential vocabulary:

- `SoftwareFieldEstimate`
- selected evidence
- unavailable evidence
- unknown remainder
- architecture projection
- artifact actions
- operation support
- operation policy
- step semantics
- finite horizon
- `ForecastCone`
- `ConsequenceEnvelope`
- feedback and calibration hooks

The basic computational pipeline is:

```text
artifact pressure
  -> bounded field estimate
  -> operation support / policy
  -> step semantics
  -> bounded reachable paths
  -> ForecastCone
  -> ConsequenceEnvelope
  -> review / CI / governance
  -> observed outcome
  -> posterior field update
```

This is already a strong foundation. The next stage is to prove large theorems showing when this computation is compositional, observable, governable, and stable under feedback.

## 4. Primary Theorem: ForecastCone Descent Theorem

### Statement

Let a global software field `G` be covered by local regions `Uᵢ` with overlaps forming a finite architecture cover.

If field states, operations, support, policy, step semantics, idle/stutter steps, and observation boundaries satisfy descent conditions, then for every finite horizon `h`:

```text
ClockedForecastCone_h(G)
  ≃
lim_{σ ∈ Čech(Cover)} ClockedForecastCone_h(G|σ)
```

In the binary case:

```text
ClockedForecastCone_h(G)
  ≃
ClockedForecastCone_h(A)
  ×_{ClockedForecastCone_h(I)}
ClockedForecastCone_h(B)
```

where `G = A ∪_I B`.

### Intuition

The global future of a software system is exactly the gluing of compatible local futures.

```text
global reachable future
  ≃
compatible family of local reachable futures
```

### Why Clocked Cones Are Needed

Local regions may not change at every global step. A global step may modify `A` while `B` stutters, then later modify `B` while `A` stutters.

Therefore, ordinary path length is not sufficient. We introduce:

```text
ClockedForecastCone_h(F)
```

where every tick contains either a supported step or an idle/stutter step.

This aligns local paths on a shared clock and makes gluing possible.

### Philosophical Meaning

> **A boundary is architecturally real iff future evolution descends across it.**

In other words:

> A module boundary is not merely a static dependency cut.<br>
> It is a boundary across which future paths can be computed locally and glued globally.

### Value

This theorem would give SFT its first major local-to-global principle.

It would show that software evolution is not only computable, but compositional under the right architectural boundaries.

## 5. Theorem Family After ForecastCone Descent

ForecastCone Descent opens a much larger theorem landscape.

The following theorems are candidates for SFT’s long-term research program.

---

## 5.1 Modularity Representation Theorem

### Statement

For an architecture cover `C`, the following are equivalent:

```text
1. C is a genuine SFT module boundary.
2. ForecastCone satisfies descent over C for all admissible bounded fields and horizons.
3. Every global evolution path is uniquely representable as a compatible family of local evolution paths.
```

### Meaning

```text
Modularity
  ≃
ForecastCone sheaf condition
```

### Insight

This redefines modularity.

Traditional modularity is often described in terms of APIs, information hiding, coupling, cohesion, dependency direction, and responsibility separation.

SFT raises this to a dynamic principle:

> **Modularity is the local-to-global structure of future evolution.**

### Impact

This could become one of SFT’s central contributions to software engineering:

> Architecture is not merely the shape of present code.<br>
> Architecture is the descent structure of future evolution.

---

## 5.2 Descent Obstruction Theorem

### Statement

When ForecastCone descent fails, the failure can be represented by typed obstruction witnesses.

Possible obstruction classes:

```text
DescentFailure
  = hidden coupling
  + missing interface invariant
  + unsupported global operation
  + policy conflict
  + observation boundary leak
  + unknown remainder expansion
```

More structurally, the map:

```text
GlobalCone_h(G)
  -> CompatibleLocalConeFamily_h(C)
```

may fail by:

1. **surjectivity failure** — locally compatible futures do not lift to a global future;
2. **injectivity failure** — globally distinct futures look identical locally.

### Insight

Technical debt becomes a failure of descent.

Instead of saying:

```text
this architecture is bad
```

SFT can say:

```text
this compatible local future does not lift to a global future;
the obstruction witness is this missing invariant / hidden coupling / support mismatch.
```

### Impact

This would turn architectural debt into a mathematically classified obstruction.

It also gives Workbench a deeper role: obstruction candidates in `ConsequenceEnvelope` become typed mathematical witnesses.

---

## 5.3 Cone Cohomology Theorem

### Statement

Let `𝓕_h` be the ForecastCone presheaf over an architecture cover `C`.

Then local-to-global failures of software evolution are measured by Čech-style obstruction objects:

```text
H⁰(C, 𝓕_h) = global reachable futures
H¹(C, 𝓕_h) = failure of local futures to glue globally
H²(C, 𝓕_h) = higher compatibility obstruction among overlaps
```

In simple form:

```text
H¹(C, 𝓕_h) = 0
  iff
all compatible local futures glue globally
```

### Insight

Integration failure becomes cohomology.

```text
local tests pass
local reviews pass
local AI proposals look valid
but global integration fails
```

This is exactly the kind of phenomenon cohomology is designed to capture: local solvability without global compatibility.

### Impact

This would introduce a genuine geometry of software evolution.

It could provide a mathematical theory of hidden coupling, integration risk, and cross-boundary architectural debt.

---

## 5.4 Evolutionary Normal Form Theorem

### Statement

If an architecture cover satisfies ForecastCone descent and local operations satisfy appropriate commutation or confluence conditions, then every supported global evolution path can be rewritten into a normal form:

```text
interface synchronization
  ; local evolution block U₁
  ; local evolution block U₂
  ; ...
  ; interface synchronization
```

Equivalently, supported global paths are unique up to permutation of independent local steps.

### Insight

This gives a formal account of safe parallel development.

If independent local futures glue and commute, then different interleavings of local work produce equivalent global evolution.

### Impact

This is especially important for AI coding agents.

It would help answer:

- Which PRs can be safely developed in parallel?
- Which AI-generated patches commute?
- Which merge orders are equivalent?
- When can multi-agent development be safely distributed?

---

## 5.5 Cone-Conservative Observation Theorem

### Statement

An observation function `O` is cone-conservative for a class of fields `𝓒` if:

```text
O(F) = O(G)
  ->
ForecastCone_h(F) ≃ ForecastCone_h(G)
```

for all relevant horizons and support boundaries.

If `O` is not cone-conservative, then there exist fields `F` and `G` such that:

```text
O(F) = O(G)
but
ForecastCone_h(F) ≄ ForecastCone_h(G)
```

### Insight

This gives a precise theory of metric adequacy.

A metric is not good merely because it is measurable. It is good if it preserves distinctions that matter for future evolution.

### Impact

This could become the theoretical foundation for ArchSig and SFT observability.

It asks:

> Does this observation preserve the future cone?

If not, then the metric collapses fields that have different reachable futures.

---

## 5.6 Minimal ConsequenceEnvelope Theorem

### Statement

For a review decision class `Q`, define an equivalence relation on ForecastCone paths:

```text
p ≈_Q q
```

iff no valid `Q`-review can distinguish paths `p` and `q`.

Then the minimal sound review surface is:

```text
MinimalEnvelope_Q(ForecastCone)
  ≃
ForecastCone / ≈_Q
```

Any other sound envelope projection factors through this minimal envelope.

### Insight

This theorem answers:

> What is the minimum information a reviewer needs in order to make a sound decision?

Too much information overwhelms reviewers. Too little hides dangerous futures.

The minimal envelope is the smallest review-facing projection that preserves the distinctions required for a given class of decisions.

### Impact

This could provide a theoretical foundation for review tools, AI coding assistants, and architecture workbenches.

---

## 5.7 Modular Attractor Theorem

### Statement

Suppose ForecastCone descent holds over an architecture cover.

If each local region `Uᵢ` has a stable target region `Aᵢ`, and these target regions agree on overlaps, then the glued global target region `A` is stable.

```text
∀i, StableRegion(Uᵢ, Aᵢ)
compatibility on overlaps
  ->
StableRegion(G, glue(Aᵢ))
```

Similarly:

```text
Basin_G(A)
  ≃
lim Basin_Uᵢ(Aᵢ)
```

### Insight

Good futures can be engineered locally if the architecture lets futures glue.

### Impact

This makes Attractor Engineering modular.

It says teams do not need to reshape the whole system at once. Under the right boundaries, local attractor engineering composes into global evolution shaping.

---

## 5.8 Governance Synthesis Theorem

### Statement

Let `B` be a bad path family and `D` a desired path family inside a ForecastCone.

Given an intervention basis `Γ`, there exists a governance intervention that removes `B` while preserving `D` iff there exists a guard family that hits all bad witnesses and misses all desired witnesses.

```text
∃ τ : SupportTransformation.
  τ preserves D
  ∧ τ excludes B

iff

∃ GuardSet ⊆ Γ.
  hits(B)
  ∧ disjoint_from(D)
```

### Insight

Governance becomes synthesis.

Instead of merely adding rules, reviews, CI checks, or AI policies, SFT asks:

> Which intervention removes the bad futures while preserving the good ones?

### Impact

This could formalize the design of review policies, CI gates, coding rules, AI proposal constraints, and architectural guardrails.

It is a theory of minimum effective governance.

---

## 5.9 Closed-Loop Calibration Fixed Point Theorem

### Statement

Let `𝓔` be a space of bounded field estimates with a refinement order.

Let posterior update be:

```text
U : 𝓔 -> 𝓔
```

If `U` is monotone, evidence-preserving, boundary-explicit, non-conclusion-preserving, and forecast-error-refining, then the update sequence:

```text
E₀ -> U(E₀) -> U²(E₀) -> ...
```

eventually reaches either:

```text
1. a fixed point, or
2. a boundary expansion requirement.
```

### Insight

SFT becomes a learning theory of software evolution.

Forecast failures are not merely errors. They refine the field estimate or expose an insufficient observation boundary.

### Impact

This would give a formal backbone to closed-loop software evolution tooling.

A mature SFT workbench would continuously update its field model from observed PRs, incidents, reviews, and outcomes.

---

## 5.10 Artifact Yoneda Theorem

### Statement

Let `Art` be a category of artifacts/probes: PRDs, issues, review comments, AI proposals, incident reports, and governance interventions.

Each software field `F` defines a response functor:

```text
Φ_F : Artᵒᵖ -> ConeCat
```

mapping each artifact to the ForecastCone family it opens.

If the probe family is sufficiently separating, then:

```text
Φ_F ≃ Φ_G
  iff
F ≃_SFT G
```

### Insight

A software field is determined by how it responds to possible changes.

```text
field meaning
  =
artifact response behavior
```

### Impact

This gives SFT an operational semantics.

The meaning of a software field is not merely its present structure, but the family of future cones it produces under possible artifact pressures.

---

## 5.11 Agentic Confluence Theorem

### Statement

Suppose multiple AI agents generate local proposals over regions `Uᵢ`.

If:

- local proposal systems terminate;
- local proposal systems are confluent;
- ForecastCone descent holds;
- interface constraints are preserved;
- policies are commutation-invariant;

then all fair interleavings of accepted AI proposals land in the same global cone quotient.

```text
Interleaving₁ ≈ Interleaving₂
```

### Insight

This formalizes safe parallel AI development.

### Impact

It gives a theorem-shaped answer to one of the central problems of agentic software development:

> When can multiple AI coding agents work in parallel without producing unsafe architectural divergence?

---

## 5.12 Lifecycle Bifurcation Theorem

### Statement

Let `F` be a field and `A` a safe target region.

Define repair, migration, contraction, deletion, and end-of-life intervention classes.

There exists an obstruction measure `Ω(F)` such that:

```text
Ω(F) < threshold
  -> repair remains feasible

Ω(F) ≥ threshold
  -> repair-only intervention cannot preserve A
```

When repair fails, the system enters one of several lifecycle pressure regimes:

```text
migration pressure
contraction pressure
deletion pressure
end-of-life pressure
```

### Insight

Technical debt becomes a phase transition.

There is a point where repair is no longer the right operation; migration, contraction, deletion, or retirement becomes structurally necessary.

### Impact

This could formalize one of the hardest engineering judgments:

> Should we refactor, migrate, delete, or retire this subsystem?

---

## 5.13 Field-Shaping Fixed Point Theorem

### Statement

Let support transformations form a complete lattice.

Let a field-shaping operator be:

```text
S : 𝓣 -> 𝓣
```

If `S` is monotone, then by fixed-point principles it has least and greatest fixed points.

The least fixed point represents:

```text
the minimal field shaping that preserves desired paths
while excluding bad witness families
```

### Insight

Good development environments are fixed points of field-shaping operators.

### Impact

This theorem could unify review culture, CI, type boundaries, AI policies, ownership, and runtime feedback as transformations of future support.

---

## 5.14 Evolutionary Invariance Theorem

### Statement

If two fields `F` and `G` have naturally equivalent ForecastCones across relevant horizons, artifact actions, support relations, policies, and observation boundaries, then they are evolutionarily equivalent:

```text
ForecastCone_h(F) ≃ ForecastCone_h(G)
  ->
F ≃_evo G
```

### Insight

Refactoring can be understood as preservation of future evolution, not only preservation of present behavior.

Traditional refactoring preserves external behavior.

SFT-style refactoring preserves reachable futures.

### Impact

This would give a deeper semantics of refactoring, migration, and architecture-preserving transformation.

---

## 6. Grand Theorem: Fundamental Modularity Theorem of Software Evolution

日本語名: **ソフトウェア進化の基本定理**

The above theorems suggest a larger unifying theorem.

### Statement Sketch

A software architecture is modular iff its ForecastCone functor satisfies descent.

Its technical debt is measured by descent obstruction.

Its review surface is the minimal quotient preserving the decisions induced by those obstructions.

Its governance is complete iff every bad obstruction witness can be cut without cutting the desired cone.

Its evolution becomes computable iff the closed loop reaches a boundary-explicit fixed point.

In compressed form:

```text
Modularity
  = ForecastCone descent

Technical debt
  = descent obstruction

Review
  = minimal decision-preserving envelope

Governance
  = desired-cone-preserving obstruction cutting

Learning
  = closed-loop boundary-explicit fixed point
```

### One-Sentence Version

> **Every bounded software evolution is either computably governed, or fails with a typed witness explaining which boundary of computation broke.**

### Japanese Version

> **境界づけられたソフトウェア進化は、計算可能に統治できるか、さもなくば、どの計算境界が破れたかを示す型付き witness を持つ。**

This is the possible grand theorem of SFT.

It would position SFT as a unified theory of computability, observability, modularity, governance, and evolution in software systems.

Lean status: the current formalization provides a finite selected assembly,
`SFTFundamentalModularity.FiniteSelectedFundamentalModularityTheorem`, relative
to a `FiniteExactSFTModel`, a selected source, a selected horizon, and explicit
component hypotheses.  It proves the governed-or-typed-boundary-failure
conclusion for that selected finite package.  It does not prove the
assumption-free theorem for all software systems, all covers, empirical
calibration correctness, operational governance effectiveness, or global AI
safety.

## 7. Research Phases

### Phase 1: Local-to-Global Foundation

Goal: Establish SFT as a theory of compositional software evolution.

Target theorems:

1. ForecastCone Descent Theorem
2. Modularity Representation Theorem
3. Descent Obstruction Theorem

Outcome:

```text
Architecture boundary
  =
future-gluing boundary
```

### Phase 2: Engineering Surface

Goal: Connect the mathematical theory to review, CI, AI proposal governance, and tooling.

Target theorems:

1. Minimal ConsequenceEnvelope Theorem
2. Governance Synthesis Theorem
3. Agentic Confluence Theorem

Outcome:

```text
SFT Workbench
  =
reviewable computation of software futures
```

### Phase 3: Mathematical Deepening

Goal: Build the geometry and algebra of software evolution.

Target theorems:

1. Cone Cohomology Theorem
2. Artifact Yoneda Theorem
3. Evolutionary Normal Form Theorem

Outcome:

```text
Software evolution
  =
local-to-global geometry of future paths
```

### Phase 4: Closed-Loop Evolution Science

Goal: Turn SFT into a learning system for software evolution.

Target theorems:

1. Closed-Loop Calibration Fixed Point Theorem
2. Lifecycle Bifurcation Theorem
3. Field-Shaping Fixed Point Theorem
4. Evolutionary Invariance Theorem
5. Fundamental Modularity Theorem of Software Evolution

Outcome:

```text
Software engineering
  ->
computational science of software evolution
```

## 8. How SFT Could Change Computer Science and Software Engineering

### 8.1 From Understanding to Evolution

Software engineering has historically optimized for human understanding.

SFT reframes the field around software evolution.

```text
old center:
  Can humans understand this system?

new center:
  What futures does this system make reachable?
```

Understanding remains important, but it becomes a local condition for governing evolution.

### 8.2 From Static Modularity to Dynamic Modularity

Traditional modularity is structural.

SFT modularity is evolutionary.

```text
old modularity:
  dependencies are controlled
  APIs are clean
  responsibilities are separated

SFT modularity:
  local futures glue into global futures
```

This gives a new mathematical meaning to architecture boundaries.

### 8.3 From Metrics to Cone-Conservative Observation

Traditional metrics often measure what is easy to measure.

SFT asks whether an observation preserves future distinctions.

```text
metric adequacy
  =
ForecastCone preservation
```

This could reshape architecture metrics and software observability.

### 8.4 From Review Comments to Minimal Consequence Envelopes

Code review often struggles with information overload.

SFT can define the minimal information surface needed for a particular review decision.

```text
review surface
  =
minimal quotient of ForecastCone preserving decision-relevant distinctions
```

This could ground a new generation of review tools.

### 8.5 From Guardrails to Governance Synthesis

AI-era development often adds guardrails reactively.

SFT aims to synthesize interventions:

```text
remove bad futures
preserve desired futures
minimize governance burden
```

This reframes governance as support transformation.

### 8.6 From AI Coding to Agentic Confluence

Multiple AI agents can generate code faster than humans can coordinate manually.

SFT could provide conditions under which parallel AI proposals commute, converge, and preserve safe regions.

```text
safe multi-agent development
  =
local confluence + ForecastCone descent + interface preservation
```

### 8.7 From Technical Debt to Descent Obstruction

Technical debt is often discussed qualitatively.

SFT can model it as failure of future gluing.

```text
technical debt
  =
obstruction to descent of software evolution
```

This would make architectural debt observable, classifiable, and potentially repairable.

### 8.8 From Refactoring to Evolutionary Invariance

Traditional refactoring preserves behavior.

SFT refactoring preserves future possibilities.

```text
refactoring
  =
ForecastCone-preserving transformation
```

This could deepen the formal meaning of architecture-preserving change.

### 8.9 From Lifecycle Guesswork to Bifurcation Theory

Teams often struggle to decide whether to refactor, migrate, delete, or retire a system.

SFT could define lifecycle phase transitions using ForecastCone width, obstruction growth, unknown remainder, support cost, and safe-region failure.

```text
repair no longer works
  ->
phase transition to migration / deletion / retirement
```

### 8.10 From Software Engineering to Software Evolution Science

The largest vision is that software engineering becomes a computational science of software evolution.

SFT would provide:

- a field model of software systems;
- a path-space model of future evolution;
- a local-to-global theory of modularity;
- typed obstruction witnesses for architectural debt;
- minimal review surfaces;
- governance synthesis;
- closed-loop calibration;
- AI-agent confluence conditions;
- lifecycle phase transition theory.

This is the long-term research promise.

## 9. Suggested Website Integration

The SFT website could introduce this research program without overwhelming the reader.

Recommended placement:

```text
/sft/computation/forecast-cone-descent/
  Primary theorem page

/sft/references/research-program/
  Theorem roadmap section

/sft/computation/workbench/
  DescentGap detection as a workbench problem

/sft/software-evolution/attractor-engineering/
  Modular Attractor Theorem connection

/sft/software-evolution/ai-proposal-governance/
  Agentic Confluence Theorem connection

/sft/references/formal-anchors/
  Lean anchor list for each theorem family
```

## 10. Suggested Lean Anchor Names

Possible formal anchor names:

```text
ClockedFieldPath
IdleSupportedStep
FieldCover
BinaryFieldCover
CompatibleLocalFieldFamily
CompatibleLocalOperationFamily
CompatibleLocalConeFamily
ClockedForecastCone
ForecastConeDescent
forecastCone_descent_binary
forecastCone_descent_finiteCover
DescentGap
DescentObstruction
coneConservativeObservation
MinimalConsequenceEnvelope
GovernanceIntervention
governance_synthesis
AttractorGluing
agentic_confluence
closedLoopCalibration_fixedPoint
EvolutionaryEquivalence
```

## 11. Final Vision

SFT begins with a simple but powerful shift:

> Software architecture is not only about making the present understandable.<br>
> It is about shaping which futures become reachable.

ForecastCone Descent turns this shift into a theorem-shaped research program.

If successful, SFT could redefine several central concepts:

```text
architecture      -> shape of reachable futures
modularity        -> descent of future paths
technical debt    -> obstruction to future gluing
review            -> minimal consequence envelope
metrics           -> cone-conservative observations
governance        -> support transformation
refactoring       -> evolutionary invariance
AI coordination   -> agentic confluence
lifecycle         -> bifurcation of repair feasibility
```

The ultimate ambition is clear:

> **Make software evolution computable.**

Not by predicting a single future, but by computing bounded spaces of reachable futures, explaining their obstructions, shaping their attractors, and closing the loop through observation and calibration.

This is where SFT can become more than a theory of architecture.

It can become a theory of software evolution itself.
