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

## 12. LEAN 実装計画

この節は、上の theorem roadmap を Lean 実装へ落とすための計画である。
ここでいう実装は、未証明の `theorem` を `sorry` で置くことではない。
まず carrier、boundary、compatibility predicate、theorem package を定義し、
証明できる accessor / projection / preservation theorem から積み上げる。
大きな定理は、必要な前提を `structure ... : Prop` として明示し、各 proof obligation を
小さな Lean theorem に分解してから、最終 theorem package として束ねる。

### 12.1 実装方針

基本方針:

```text
definition first
  -> boundary predicate
  -> projection / restriction theorem
  -> binary theorem
  -> finite-cover theorem
  -> theorem-package entrypoint
  -> docs / theorem index sync
```

claim boundary:

- `ForecastCone` は bounded finite path membership であり、確率、予測精度、因果証明ではない。
- `ClockedForecastCone` は global/local clock alignment のための path model であり、全実時間や scheduler completeness を主張しない。
- descent theorem は明示された cover、restriction、step-gluing、policy compatibility、observation boundary に相対化する。
- obstruction theorem は typed witness を返すが、tool extractor がすべての witness を発見するとは主張しない。
- cohomology、Yoneda、fixed point、bifurcation は、必要な algebraic / order-theoretic 前提を明示した後にだけ theorem として読む。

実装上の制約:

- `axiom`, `admit`, `sorry`, `unsafe` は導入しない。
- 証明がまだ遠い主張は、Lean theorem stub ではなく theorem package の field として置く。
- 既存の `SFTForecastCone`, `SFTConeProjection`, `SFTReachability`, `SFTEnvelope`,
  `SFTPolicy`, `SFTFieldUpdate`, `SFTArtifactAction`, `SFTInterfaceBoundary` を再利用する。
- 汎用 category / limit が必要になるまでは、まず binary cover と finite cover の concrete API で進める。
- mathlib の category theory / order theory は、内部 API が固まった後に bridge として導入する。

### 12.2 追加予定 Lean module

第一波で追加する module:

```text
Formal/Arch/Evolution/SFTClockedCone.lean
Formal/Arch/Evolution/SFTFieldCover.lean
Formal/Arch/Evolution/SFTDescent.lean
```

現時点の Lean surface では、`SFTClockedCone.lean` が exact shared-clock cone core、
`SFTFieldCover.lean` が binary cover API、`SFTDescent.lean` が exact clocked cone 上の
binary descent surface を持つ。no-lift / local-identification から typed obstruction へ接続する
最小 bridge は `SFTTheoremRoadmap.lean` に置き、独立 module への分割は後続作業とする。

第二波で追加する module:

```text
Formal/Arch/Evolution/SFTMinimalEnvelope.lean
Formal/Arch/Evolution/SFTAttractorGluing.lean
Formal/Arch/Evolution/SFTGovernanceSynthesis.lean
Formal/Arch/Evolution/SFTAgenticConfluence.lean
Formal/Arch/Evolution/SFTEvolutionaryEquivalence.lean
```

第三波で追加する module:

```text
Formal/Arch/Evolution/SFTConeCohomology.lean
Formal/Arch/Evolution/SFTArtifactYoneda.lean
Formal/Arch/Evolution/SFTCalibrationFixedPoint.lean
Formal/Arch/Evolution/SFTLifecycleBifurcation.lean
Formal/Arch/Evolution/SFTFieldShapingFixedPoint.lean
Formal/Arch/Evolution/SFTFundamentalModularity.lean
```

各波の最後に更新する入口:

```text
Formal.lean
Formal/Arch/Evolution/SFTTheoremPackages.lean
docs/aat/lean_theorem_index.md
docs/aat/proof_obligations.md
```

### 12.3 ForecastCone Descent Theorem

Lean anchors:

```text
ClockedFieldStep
IdleSupportedStep
ClockedFieldPath
ClockedForecastCone
BinaryFieldCover
FieldCover
CompatibleLocalConeFamily
ForecastConeDescent
forecastCone_descent_binary
forecastCone_descent_finiteCover
```

実装ファイル:

```text
Formal/Arch/Evolution/SFTClockedCone.lean
Formal/Arch/Evolution/SFTFieldCover.lean
Formal/Arch/Evolution/SFTDescent.lean
```

第一段階では、clocked path を既存の `ArchitecturePath` 上に定義する。

```text
ClockedFieldStep support relation source target
  = active supported step
  | idle stutter step

ClockedFieldPath support relation source target
  = ArchitecturePath (ClockedFieldStep support relation) source target

ClockedForecastCone support relation source horizon target path
  = ArchitecturePath.length path = horizon
```

`ClockedForecastCone` は、通常の `ForecastCone` の `<= horizon` と異なり、
共有 clock 上の tick 数をそろえるために最初は exact horizon として扱う。
そのうえで次を証明する。

```text
ClockedForecastCone.length_eq_horizon
ClockedForecastCone.length_le_horizon
BoundedClockedForecastCone.of_clockedForecastCone
BoundedClockedForecastCone.monotone_horizon
boundedClockedForecastCone_of_forecastCone
clockedForecastCone_of_forecastCone
```

`ClockedForecastCone` 自体は exact horizon を保持し、horizon extension の monotonicity は
`BoundedClockedForecastCone` または explicit idle-padding bridge として読む。

第二段階では binary cover を concrete に定義する。

```text
BinaryFieldCover Global Left Right Interface where
  restrictLeft  : Global -> Left
  restrictRight : Global -> Right
  leftInterface : Left -> Interface
  rightInterface : Right -> Interface
  compatible    : Left -> Right -> Prop
  glue          : (l : Left) -> (r : Right) -> compatible l r -> Global
  glue_left     : ...
  glue_right    : ...
  global_ext    : ...
```

support、policy、step relation は cover と独立に持たせず、restriction compatibility
を theorem-bearing premise として分ける。

```text
RestrictsSupport
RestrictsStepRelation
PreservesPolicy
PreservesObservationBoundary
GlobalStepProjects
CompatibleLocalStepGlues
IdleStepProjects
IdleStepGlues
```

第三段階で、cone object を sigma type として固定する。

```text
ClockedConeObject support relation source horizon :=
  Sigma fun target =>
    Sigma fun path =>
      ClockedForecastCone support relation source horizon target path

CompatibleBinaryConeFamily cover leftModel rightModel interfaceModel horizon :=
  compatible pair of local ClockedConeObject values
```

binary descent の statement は、まず `Equiv` として実装する。

```text
forecastCone_descent_binary :
  BinaryDescentAssumptions cover globalModel localModels source horizon ->
    ClockedConeObject globalSupport globalRelation source horizon
      ≃
    CompatibleBinaryConeFamily cover localModels source horizon
```

証明戦略:

1. global clocked path を各 region へ射影する。
2. active step は local active または local idle へ写す。
3. local pair の interface projection が tick ごとに一致することを induction で示す。
4. 逆向きは compatible local tick pair を global tick に glue する。
5. `glue_unique` と step-gluing assumption で左右逆写像を証明する。

finite cover 版は binary 版の後に進める。
最初は full category-theoretic limit ではなく、finite index と Cech simplex を concrete に定義する。

```text
FiniteFieldCover
CechSimplex
LocalConeOnSimplex
CompatibleLocalConeFamily
forecastCone_descent_finiteCover
```

proof obligation:

- clocked path の exact horizon と unclocked cone の bounded horizon の bridge。
- stutter step が observation boundary と policy boundary を破らないこと。
- local operation family の tick alignment。
- interface overlap 上の endpoint compatibility。
- finite cover の Cech compatibility を binary overlap と一致させる補題。

最初の Issue 単位:

```text
Issue A: ClockedFieldStep / ClockedForecastCone core
Issue B: BinaryFieldCover and compatible local cone family
Issue C: forecastCone_descent_binary
Issue D: finite cover Cech compatibility skeleton
Issue E: forecastCone_descent_finiteCover theorem package
```

### 12.4 Modularity Representation Theorem

Lean anchors:

```text
SFTModuleBoundary
ForecastConeSheafCondition
GlobalEvolutionRepresentation
modularity_representation
```

実装ファイル:

```text
Formal/Arch/Evolution/SFTDescent.lean
```

`SFTModuleBoundary` は最初から直観的な言葉で定義しない。
まず theorem-bearing definition として、descent 条件を module boundary の意味にする。

```text
SFTModuleBoundary cover :=
  forall admissibleModel horizon source,
    ForecastConeDescent cover admissibleModel source horizon
```

次に、global path representation を別 predicate にする。

```text
GlobalEvolutionRepresentable cover model :=
  forall horizon source,
    ClockedConeObject global source horizon
      ≃ CompatibleLocalConeFamily cover model source horizon
```

定理は二段階に分ける。

```text
moduleBoundary_iff_forecastConeDescent
forecastConeDescent_iff_globalEvolutionRepresentable
modularity_representation
```

最初の定理は、定義の選び方により短い証明になる。
二番目の定理は、`ForecastConeDescent` の内部表現を `Equiv` にした場合は accessor theorem、
`map + inverse + laws` にした場合は `Equiv` への packaging theorem になる。

proof obligation:

- "all admissible bounded fields" の Lean 上の index を `AdmissibleSFTModel` として定義する。
- unique representability を `Equiv` の left/right inverse として読む。
- cover が module boundary であることを static API cleanliness ではなく future-gluing boundary として記録する。

### 12.5 Descent Obstruction Theorem

Lean anchors:

```text
DescentFailureKind
DescentFailure
DescentObstruction
DescentGap
LocalFamilyDoesNotLift
GlobalPathsLocallyIdentified
descent_obstruction_of_surjectivity_failure
descent_obstruction_of_injectivity_failure
```

実装ファイル:

```text
Formal/Arch/Evolution/SFTDescentObstruction.lean
```

failure kind は inductive type として置く。

```text
inductive DescentFailureKind where
  | hiddenCoupling
  | missingInterfaceInvariant
  | unsupportedGlobalOperation
  | policyConflict
  | observationBoundaryLeak
  | unknownRemainderExpansion
```

obstruction witness は、failure kind と evidence boundary を分けて持つ。

```text
structure DescentObstruction where
  kind : DescentFailureKind
  localWitness : Prop
  globalWitness : Prop
  interfaceWitness : Prop
  theoremBoundary : Prop
  observationBoundary : Prop
  nonConclusions : Prop
```

surjectivity failure と injectivity failure は、descent map を明示して定義する。

```text
GlobalToCompatibleLocal :
  ClockedConeObject global source h ->
  CompatibleLocalConeFamily cover model source h

LocalFamilyDoesNotLift family :=
  not exists globalCone, GlobalToCompatibleLocal globalCone = family

GlobalPathsLocallyIdentified p q :=
  p != q and GlobalToCompatibleLocal p = GlobalToCompatibleLocal q
```

主要 theorem は、obstruction classifier の completeness を前提にする。

```text
DescentObstructionClassifierComplete classifier :=
  forall failure, exists obstruction, classifier failure obstruction

descent_obstruction_of_surjectivity_failure :
  DescentObstructionClassifierComplete classifier ->
  LocalFamilyDoesNotLift family ->
    exists obstruction, classifier (.surjectivity family) obstruction

descent_obstruction_of_injectivity_failure :
  DescentObstructionClassifierComplete classifier ->
  GlobalPathsLocallyIdentified p q ->
    exists obstruction, classifier (.injectivity p q) obstruction
```

proof obligation:

- classifier completeness は theorem の前提であり、tooling が完全に分類できるとは読まない。
- `DescentGap` と `ConsequenceEnvelope.obstructionCandidates` の bridge を後続で追加する。
- finite counterexample を一つ作り、hidden coupling と unsupported global operation の witness が別物であることを示す。

### 12.6 Cone Cohomology Theorem

Lean anchors:

```text
ForecastConePresheaf
CechCone0
CechCone1
CechConeCocycle
CechConeCoboundary
ConeH1Vanishes
cone_h1_vanishes_iff_local_futures_glue
```

実装ファイル:

```text
Formal/Arch/Evolution/SFTConeCohomology.lean
```

この theorem は最初から一般の sheaf cohomology として実装しない。
ForecastCone は path family であり、自然に abelian group とは限らない。
第一段階では、local-to-global obstruction を Čech-style complex に似た concrete witness API として実装する。

```text
ForecastConePresheaf cover model horizon
Cech0 := compatible local 0-cochains
Cech1 := overlap disagreement witnesses
Cech1Cocycle := triple-overlap compatibility
Cech1Coboundary := disagreement explained by local reindexing
ConeH1Vanishes := forall cocycle, exists coboundary explanation
```

主要 theorem:

```text
cone_h1_vanishes_of_forecastConeDescent :
  ForecastConeDescent cover model source h ->
    ConeH1Vanishes cover model source h

forecastConeDescent_of_cone_h1_vanishes
  : ConeH1Vanishes cover model source h ->
    EffectiveLocalLift cover model source h ->
      ForecastConeDescent cover model source h
```

`H0` は global reachable futures と一致させる。

```text
cone_h0_equiv_globalCone :
  ForecastConeDescent cover model source h ->
    CechCone0 cover model source h ≃ ClockedConeObject global source h
```

第二段階で、必要なら mathlib の algebraic topology / category theory へ bridge する。
その場合も、`ConeH1Vanishes` を formal anchor として残し、一般 cohomology は追加 theorem にする。

proof obligation:

- path family を quotient / setoid にするか、raw dependent path のまま扱うかを決める。
- triple overlap を finite cover の Cech simplex と接続する。
- obstruction witness と `H1` nonzero の対応は、classifier completeness を前提にする。

### 12.7 Evolutionary Normal Form Theorem

Lean anchors:

```text
StepRegion
IndependentClockedStep
CommutingClockedSteps
EvolutionPathRewrite
EvolutionaryNormalForm
evolutionary_normal_form
```

実装ファイル:

```text
Formal/Arch/Evolution/SFTAgenticConfluence.lean
```

normal form は clocked path 上の rewrite として扱う。

```text
IndependentClockedStep s1 s2 :=
  disjoint affected regions
  + compatible interface effects
  + policy commutation

CommutingClockedSteps s1 s2 :=
  exists square filler, applying s1 then s2 equals applying s2 then s1

EvolutionPathRewrite :=
  adjacent independent steps may be swapped
```

normal form:

```text
interface synchronization
  ; local block for U_i
  ; local block for U_j
  ; ...
  ; interface synchronization
```

Lean では、最初に binary / finite ordered regions に対して block ordering を定義する。

```text
RegionOrderedPath
BlockNormalForm
PathEquivalentByIndependentSwaps
```

主要 theorem:

```text
independent_swap_preserves_clockedCone :
  CommutingClockedSteps s1 s2 ->
    PathEquivalentByIndependentSwaps p q ->
      ClockedForecastCone ... p ->
        ClockedForecastCone ... q

evolutionary_normal_form :
  ForecastConeDescent cover model source h ->
  LocalConfluenceOfIndependentSteps model ->
  TerminatingRewriteMeasure model ->
    exists nf, BlockNormalForm nf and PathEquivalentByIndependentSwaps path nf
```

proof obligation:

- adjacent swap が dependent endpoints を保つための square filler API。
- termination measure は path length ではなく inversion count で定義する。
- confluence は全 step ではなく independent local steps に限定する。

### 12.8 Cone-Conservative Observation Theorem

Lean anchors:

```text
ConeObservation
ConeEquivalentAt
ConeConservativeObservation
coneConservativeObservation
not_coneConservative_counterexample
```

実装ファイル:

```text
Formal/Arch/Evolution/SFTMinimalEnvelope.lean
```

定義:

```text
ConeObservation Field Obs :=
  Field -> Obs

ConeEquivalentAt F G :=
  forall horizon support relation source,
    ClockedConeObject F source horizon ≃ ClockedConeObject G source horizon

ConeConservativeObservation O :=
  forall F G, O F = O G -> ConeEquivalentAt F G
```

主要 theorem:

```text
coneConservativeObservation_preserves_cones :
  ConeConservativeObservation O ->
  O F = O G ->
    ConeEquivalentAt F G

not_coneConservative_counterexample :
  not ConeConservativeObservation O ->
    exists F G, O F = O G and not ConeEquivalentAt F G
```

二番目は classical logic を使えば定義展開から証明できる。
実務上重要なのは、`ObservationBoundary` と `ConsequenceEnvelope` への bridge である。

```text
EnvelopeProjectionConeConservative
coneConservative_envelope_projection_preserves_decision_surface
```

proof obligation:

- `ConeEquivalentAt` の horizon / support / relation の quantification を広くしすぎない。
- observation equality は selected observation universe に相対化する。
- "metric adequacy" は empirical claim ではなく cone distinction preservation として読む。

### 12.9 Minimal ConsequenceEnvelope Theorem

Lean anchors:

```text
ReviewDecisionClass
PathIndistinguishableFor
DecisionSoundEnvelope
MinimalConsequenceEnvelope
minimalConsequenceEnvelope
minimalEnvelope_factors
```

実装ファイル:

```text
Formal/Arch/Evolution/SFTMinimalEnvelope.lean
```

review decision class を predicate として置く。

```text
ReviewDecisionClass ConePath Decision :=
  ConePath -> Decision -> Prop
```

path indistinguishability は setoid にする。

```text
PathIndistinguishableFor Q p q :=
  forall decision, Q p decision <-> Q q decision
```

`Setoid` にするため、反射、対称、推移を証明する。

```text
pathIndistinguishableSetoid Q
MinimalEnvelope Q cone := Quot (pathIndistinguishableSetoid Q)
```

sound envelope projection:

```text
DecisionSoundEnvelope Q projection :=
  forall p q, projection p = projection q -> PathIndistinguishableFor Q p q
```

主要 theorem:

```text
minimalEnvelope_sound :
  DecisionSoundEnvelope Q (Quot.mk _)

minimalEnvelope_factors :
  DecisionSoundEnvelope Q projection ->
    exists factor,
      forall p, factor (Quot.mk _ p) = projection p
```

ここで向きに注意する。
`ForecastCone / approx_Q` は decision distinction を潰さない最小 quotient である。
任意の sound envelope が同じ indistinguishable path を同一視する場合、factorization が成立する。
Lean 上では、soundness だけでなく quotient-respecting 条件を分ける。

```text
EnvelopeRespectsDecisionEquivalence Q projection :=
  forall p q, PathIndistinguishableFor Q p q -> projection p = projection q
```

proof obligation:

- `ConsequenceEnvelope` 既存構造と quotient object の bridge。
- selected cone family が finite list の場合の executable quotient approximation。
- review decision が partial / unknown の場合の three-valued decision class。

### 12.10 Modular Attractor Theorem

Lean anchors:

```text
CompatibleRegionFamily
GluedStableRegion
AttractorGluing
BasinGluing
modular_attractor
```

実装ファイル:

```text
Formal/Arch/Evolution/SFTAttractorGluing.lean
```

既存の `StableRegion`, `ReachablePreimage`, `MayReach`, `MustReach` を使う。

```text
CompatibleRegionFamily cover localRegions :=
  forall overlap, local regions agree on overlap

GluedRegion global :=
  forall i, localRegion i (restrict i global)
```

主要 theorem:

```text
stableRegion_glued_of_local :
  ForecastConeDescent cover model source h ->
  CompatibleRegionFamily cover localRegions ->
  (forall i, StableRegion localSupport_i localRelation_i localRegion_i) ->
    StableRegion globalSupport globalRelation (GluedRegion cover localRegions)

basin_gluing :
  ForecastConeDescent cover model source h ->
    ReachablePreimage globalSupport globalRelation h gluedRegion
      ≃
    CompatibleLocalBasinFamily cover localRegions h
```

証明戦略:

1. global supported step を local step family に射影する。
2. local stable closure を各 region で適用する。
3. overlap compatibility から glued region に戻す。
4. basin は `ReachablePreimage = MayReach` と descent equivalence を使って示す。

proof obligation:

- target region の overlap compatibility。
- local stable region が idle step に閉じていること。
- basin equivalence では existential witness の transport が必要。

### 12.11 Governance Synthesis Theorem

Lean anchors:

```text
PathFamily
BadPathFamily
DesiredPathFamily
GuardBasis
GuardSet
HitsBadWitnesses
MissesDesiredWitnesses
GovernanceSynthesisComplete
governance_synthesis
```

実装ファイル:

```text
Formal/Arch/Evolution/SFTGovernanceSynthesis.lean
```

既存の `GovernanceIntervention`, `SupportTransformation`,
`PointwiseSupportInclusion`, `ForecastConeProjection` を再利用する。

定義:

```text
PathFamily support relation source h :=
  forall target path, ForecastCone support relation source h target path -> Prop

Guard guardBasis :=
  operation / path witness を許可または除外する predicate

GuardSetHits B guards :=
  forall badPath in B, exists guard in guards, guard excludes badPath

GuardSetMisses D guards :=
  forall desiredPath in D, forall guard in guards, not guard excludes desiredPath
```

governance intervention と guard set の対応は、complete basis を前提にする。

```text
GuardBasisComplete basis :=
  guard sets correspond to support transformations

governance_synthesis :
  GuardBasisComplete basis ->
    (exists intervention,
      PreservesDesiredPaths intervention D
        and ExcludesBadPaths intervention B)
    <->
    (exists guards,
      GuardSetHits B guards
        and GuardSetMisses D guards)
```

proof obligation:

- "preserves desired" は same path witness を保存するのか、projected path を保存するのかを分ける。
- restrictive intervention は support narrowing なので、bad path removal と desired path preservation の両方に exact support characterization が必要。
- governance effectiveness、incident reduction、human compliance は non-conclusion として残す。

### 12.12 Closed-Loop Calibration Fixed Point Theorem

Lean anchors:

```text
FieldEstimateRefinement
PosteriorUpdateOperator
ForecastErrorRefining
BoundaryExpansionRequired
ClosedLoopCalibrationRun
closedLoopCalibration_fixedPoint
```

実装ファイル:

```text
Formal/Arch/Evolution/SFTCalibrationFixedPoint.lean
```

既存の `FieldUpdate`, `ObservedOutcome`, `PosteriorFieldRecord`, `UpdateSound` を使う。

refinement order:

```text
FieldEstimateRefinement E1 E2 :=
  E2 preserves selected evidence of E1
  + E2 refines forecast error records
  + E2 preserves non-conclusions
```

update operator:

```text
PosteriorUpdateOperator Estimate :=
  Estimate -> Estimate

MonotoneUpdate U :=
  forall E1 E2, FieldEstimateRefinement E1 E2 ->
    FieldEstimateRefinement (U E1) (U E2)
```

fixed point theorem は、finite height か well-founded strict refinement を前提にする。

```text
FiniteRefinementHeight Estimate
BoundaryExpansionTrigger U

closedLoopCalibration_fixedPoint :
  FiniteRefinementHeight Estimate ->
  MonotoneUpdate U ->
  EvidencePreserving U ->
  BoundaryExplicit U ->
  NonConclusionPreserving U ->
  ForecastErrorRefining U ->
    exists n,
      FixedPoint U (iterate U n E0)
        or BoundaryExpansionRequired U (iterate U n E0)
```

proof obligation:

- monotone だけでは有限時間 fixed point は出ないため、finite height / no infinite strict refinement を明示する。
- boundary expansion requirement は failure ではなく、modeling boundary を広げる必要があるという typed outcome。
- calibration は accuracy improvement ではなく record refinement として読む。

### 12.13 Artifact Yoneda Theorem

Lean anchors:

```text
ArtifactProbe
ArtifactProbeCategory
ArtifactResponse
ArtifactResponseFunctor
SFTSeparatingProbeFamily
SFTFieldEquivalence
artifact_yoneda
```

実装ファイル:

```text
Formal/Arch/Evolution/SFTArtifactYoneda.lean
```

第一段階では、full Yoneda lemma を使わず、separating probes の theorem として実装する。

```text
ArtifactResponse F probe :=
  ForecastConeFamilyAfterAction probe F

ResponsesEquivalent F G :=
  forall probe, ArtifactResponse F probe ≃ ArtifactResponse G probe

SFTSeparatingProbeFamily probes :=
  forall F G, ResponsesEquivalentOn probes F G -> SFTFieldEquivalence F G
```

主要 theorem:

```text
artifact_yoneda :
  SFTSeparatingProbeFamily probes ->
  ResponsesEquivalentOn probes F G ->
    SFTFieldEquivalence F G
```

第二段階で、`ArtifactProbeCategory` と contravariant response functor を定義する。

```text
Phi F : Artᵒᵖ -> ConeCat
```

mathlib の category theory へ接続する場合は、次を別 theorem とする。

```text
artifact_response_functor_natural_equiv_of_field_equiv
field_equiv_of_artifact_response_natural_equiv
```

proof obligation:

- probe family が "sufficiently separating" であることは強い前提として明示する。
- artifact response は human intention や market outcome ではなく candidate update / cone family。
- `F ≃_SFT G` は field state equality ではなく selected SFT observable/evolutionary equivalence。

### 12.14 Agentic Confluence Theorem

Lean anchors:

```text
AgentProposalSystem
AcceptedProposalStep
LocalProposalTerminates
LocalProposalConfluent
PolicyCommutationInvariant
FairInterleaving
GlobalConeQuotient
agentic_confluence
```

実装ファイル:

```text
Formal/Arch/Evolution/SFTAgenticConfluence.lean
```

proposal system は rewriting system として扱う。

```text
AgentProposalSystem region :=
  proposal step relation
  + acceptance policy
  + interface preservation predicate
```

local confluence:

```text
LocalConfluent step :=
  forall a b c, step a b -> step a c ->
    exists d, Reaches step b d and Reaches step c d
```

termination:

```text
Terminates step :=
  WellFounded inverseStep
```

主要 theorem は Newman-style lemma を local proposal system に適用し、
descent で global quotient へ持ち上げる。

```text
local_confluence_unique_normal_form :
  Terminates step ->
  LocalConfluent step ->
    UniqueNormalForm step

agentic_confluence :
  (forall i, LocalProposalTerminates agent_i) ->
  (forall i, LocalProposalConfluent agent_i) ->
  ForecastConeDescent cover model source h ->
  InterfaceConstraintsPreserved agents ->
  PolicyCommutationInvariant policies ->
    forall fair1 fair2,
      EquivalentInGlobalConeQuotient fair1 fair2
```

proof obligation:

- fairness は scheduler completeness ではなく、accepted local proposal が無限に無視されない条件。
- local normal form と global cone quotient の bridge。
- policy commutation invariant は review/CI order の差が accepted quotient を変えないこととして定義する。

### 12.15 Lifecycle Bifurcation Theorem

Lean anchors:

```text
LifecycleInterventionKind
ObstructionMeasure
RepairFeasible
RepairOnlyPreserves
LifecyclePressureRegime
lifecycle_bifurcation
```

実装ファイル:

```text
Formal/Arch/Evolution/SFTLifecycleBifurcation.lean
```

measure は最初は `Nat` または `WithTop Nat` にする。

```text
ObstructionMeasure Field := Field -> Nat

LifecycleInterventionKind :=
  repair | migration | contraction | deletion | endOfLife
```

threshold theorem は、measure の soundness premise を明示する。

```text
RepairFeasibilitySound Omega threshold :=
  forall F, Omega F < threshold -> RepairFeasible F

RepairFailureSound Omega threshold :=
  forall F, threshold <= Omega F -> not RepairOnlyPreserves F targetRegion

lifecycle_bifurcation :
  RepairFeasibilitySound Omega threshold ->
  RepairFailureSound Omega threshold ->
    (Omega F < threshold -> RepairFeasible F)
      and
    (threshold <= Omega F -> exists regime,
      LifecyclePressureRegime regime F)
```

proof obligation:

- threshold は empirical calibration ではなく、選択された measure/premise に相対化した formal threshold。
- repair failure から migration/deletion/end-of-life のどれを選ぶかは、追加 classifier が必要。
- operational cost、組織判断、business lifecycle は non-conclusion。

### 12.16 Field-Shaping Fixed Point Theorem

Lean anchors:

```text
SupportTransformationOrder
FieldShapingOperator
DesiredPathPreserving
BadWitnessExcluding
MinimalFieldShaping
fieldShaping_fixedPoint
```

実装ファイル:

```text
Formal/Arch/Evolution/SFTFieldShapingFixedPoint.lean
```

support transformation に order を入れる。

```text
T1 <= T2 :=
  T1 excludes at least the bad paths excluded by T2
  + T1 preserves at least the desired paths preserved by T2
```

complete lattice はいきなり全 support transformation に主張しない。
選択された bounded transformation universe を定義する。

```text
BoundedSupportTransformationUniverse
CompleteLattice selectedTransformations
FieldShapingOperator S : T -> T
Monotone S
```

主要 theorem:

```text
fieldShaping_fixedPoint :
  CompleteLattice T ->
  Monotone S ->
    exists lfp, LeastFixedPoint S lfp

minimal_field_shaping_preserves_desired_excludes_bad :
  LeastFixedPoint S lfp ->
  DesiredPreservationEncoded S D ->
  BadExclusionEncoded S B ->
    DesiredPathPreserving lfp D and BadWitnessExcluding lfp B
```

mathlib の `OrderHom`, `lfp`, complete lattice theorem を使える場合は、それに bridge する。
使わない場合は finite lattice 版から始める。

proof obligation:

- support transformation order の向き。
- desired path preservation と bad witness exclusion が単調条件として表現できること。
- fixed point は governance が実効的に成功したという empirical claim ではない。

### 12.17 Evolutionary Invariance Theorem

Lean anchors:

```text
ConeFunctor
ForecastConeNaturallyEquivalent
EvolutionaryEquivalence
ForecastConePreservingTransformation
evolutionary_invariance
```

実装ファイル:

```text
Formal/Arch/Evolution/SFTEvolutionaryEquivalence.lean
```

第一段階では、natural equivalence を concrete family として定義する。

```text
ForecastConeEquivalentAcrossHorizons F G :=
  forall artifact support policy observation horizon,
    ClockedConeObject F artifact support policy observation horizon
      ≃
    ClockedConeObject G artifact support policy observation horizon

EvolutionaryEquivalence F G :=
  ForecastConeEquivalentAcrossHorizons F G
```

この定義を採用する場合、主 theorem は introduction theorem になる。

```text
evolutionary_invariance :
  ForecastConeEquivalentAcrossHorizons F G ->
    EvolutionaryEquivalence F G
```

第二段階で、field transformation を追加する。

```text
ForecastConePreservingTransformation T :=
  forall F, EvolutionaryEquivalence F (T F)

refactoring_preserves_evolutionary_equivalence :
  ForecastConePreservingTransformation T ->
    EvolutionaryEquivalence F (T F)
```

proof obligation:

- "relevant horizons, artifact actions, support relations, policies, observation boundaries" を `EvolutionaryContext` として束ねる。
- naturality は artifact action composition に対して後から追加する。
- external behavior preservation と future preservation を混同しない。

### 12.18 Fundamental Modularity Theorem of Software Evolution

Lean anchors:

```text
FundamentalModularityHypotheses
FundamentalModularityPackage
ComputablyGoverned
TypedComputationBoundaryFailure
fundamental_modularity
```

実装ファイル:

```text
Formal/Arch/Evolution/SFTFundamentalModularity.lean
```

この theorem は最後に証明する統合 theorem であり、初期段階では theorem package として置く。

```text
structure FundamentalModularityPackage where
  modularityDescent :
    ForecastConeDescent cover model source h
  obstructionCompleteness :
    DescentObstructionClassifierComplete classifier
  minimalEnvelope :
    MinimalConsequenceEnvelope Q cone
  governanceComplete :
    GovernanceSynthesisComplete basis
  closedLoopOutcome :
    ClosedLoopFixedPointOrBoundaryExpansion U E0
  nonConclusions : Prop
```

grand theorem の形:

```text
fundamental_modularity :
  FundamentalModularityHypotheses data ->
    ComputablyGoverned data
      or
    exists failure : TypedComputationBoundaryFailure data,
      failure.ExplainsBrokenBoundary
```

証明戦略:

1. descent がある場合は local-to-global computation を得る。
2. descent が壊れる場合は obstruction classifier で typed witness を得る。
3. review decision は minimal envelope へ落とす。
4. bad witness を切れる場合は governance synthesis を適用する。
5. feedback loop は fixed point または boundary expansion へ進む。
6. どこかの前提が欠ける場合は `TypedComputationBoundaryFailure` に分類する。

proof obligation:

- theorem family 間の data shape をそろえる。
- "computably governed" を過剰に強くしない。bounded, selected, boundary-explicit computation として定義する。
- failure witness は mathematical failure と tooling failure を分ける。

### 12.19 実装順序

Phase A: Clocked descent core

```text
1. SFTClockedCone.lean
2. SFTFieldCover.lean
3. SFTDescent.lean binary theorem
4. theorem index / proof obligations update
```

Current Lean status: Phase A の core は `Formal/Arch/Evolution/SFTClockedCone.lean`,
`Formal/Arch/Evolution/SFTFieldCover.lean`, `Formal/Arch/Evolution/SFTDescent.lean` に分割済み。
`forecastCone_descent_binary` は `BinaryDescentAssumptions` から selected `ConeEquivalence` を
構成する theorem-package surface である。`ConeEquivalence` の global/local relatedness は
reflexive / symmetric / transitive laws を持つ selected equivalence relation として要求される。
local-to-global path gluing は `BinaryClockedStepGluingData` から
`glueCompatibleLocalClockedPath` と `glueCompatibleBinaryClockedConeFamily` として構成される。
`BinaryDescentAssumptions.ofStepGluing` はこの concrete glue function を使って descent assumptions
を組み立てる。さらに `BinaryProjectionGluingLaws` による endpoint projection/glue laws から
`BinaryProjectionGluingEquivalenceLaws.ofEndpointLaws` と
`forecastCone_descent_binary_of_endpoint_laws` を構成できる。
加えて `BinaryProjectionGluingPathLaws` によって、explicit selected path-level equivalence data
に相対化した `forecastCone_descent_binary_of_path_laws` と path-law package accessor も構成できる。
これは dependent path の definitional equality ではなく selected path equivalence である。
`SFTFiniteCover.lean` では `UniformFiniteFieldCover`、Cech-style 0/1/2 simplex、`FiniteSFTModel`、
finite local projection、`FiniteLocalClockedConeFamily`、`FiniteClockedGluingData`、
`FiniteProjectionGluingLaws`、`forecastCone_descent_finite_of_laws` を追加した。finite-cover
ForecastCone descent は、explicit finite gluing と Cech-style compatibility laws に相対化された
selected skeleton として表現できる。`SFTDescentObstruction.lean` では selected finite descent
failure を typed obstruction witness へ分類する explicit classifier package と、selected bad
obstruction witness を governance package で cut する checked accessor surface を追加した。
definitional path equality / transport-normalized path equality、all finite covers satisfying descent、
all descent failures are completely classified、full Cech cohomology theorem、operational governance
effectiveness、concrete finite-height refinement order 上の closed-loop calibration、統合 SFT model
上の Fundamental Modularity theorem はまだ無条件には主張しない。

Phase B: Obstruction and review surface

```text
1. SFTDescentObstruction.lean
2. SFTMinimalEnvelope.lean
3. ConsequenceEnvelope bridge
4. DescentGap -> obstructionCandidates bridge
```

Phase C: Governance, attractor, confluence

```text
1. SFTAttractorGluing.lean
2. SFTGovernanceSynthesis.lean
3. SFTAgenticConfluence.lean
4. website / workbench-facing theorem package metadata
```

Phase D: Higher theory

```text
1. SFTConeCohomology.lean
2. SFTArtifactYoneda.lean
3. SFTEvolutionaryEquivalence.lean
```

Phase E: Closed-loop and lifecycle theory

```text
1. SFTCalibrationFixedPoint.lean
2. SFTFieldShapingFixedPoint.lean
3. SFTLifecycleBifurcation.lean
```

Phase F: Grand theorem package

```text
1. SFTFundamentalModularity.lean
2. SFTTheoremPackages metadata update
3. docs/aat/proof_obligations.md update
4. docs/aat/lean_theorem_index.md update
```

### 12.20 PR ごとの検証

Lean 変更を含む PR では、最低限次を実行する。

```text
lake build
git diff --check
hidden / bidirectional Unicode scan
axiom / admit / sorry / unsafe scan
```

docs-only の段階でも、claim boundary が変わる場合は次を確認する。

```text
docs/sft/software_field_theory.md
docs/sft/aat_interface.md
docs/aat/proof_obligations.md
docs/aat/lean_theorem_index.md
Formal/Arch/Evolution/SFTTheoremPackages.lean
```

この実装計画の最初の実作業は、`ClockedForecastCone`、`BinaryFieldCover`、exact cone projection、
binary descent assumptions の concrete API である。ここが通ると、SFT の中心命題である

```text
architecture boundary
  =
future-gluing boundary
```

を Lean 上の具体的な theorem package に変換する土台ができる。
