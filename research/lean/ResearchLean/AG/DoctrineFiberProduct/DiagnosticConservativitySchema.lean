import ResearchLean.AG.DoctrineFiberProduct.IndexedDiagnosticVanishing

/-!
# Diagnostic conservativity schema

This module fixes the G-113 F0 type surface.  It contains only the closed
structural condition language, its evaluator on G-111 diagram homs, the three
pre-registered class terms, the independent O20 and Full--Faithful candidate
heads, diagram-isomorphism witnesses, and the per-interpretation
`DiagnosticConservative` predicate.

## Implementation notes

The condition syntax is parameter-free so that one term applies uniformly to
every carrier, shape, and diagram hom.  Its evaluator reads only the underlying
`sourceMap` functions and the pullback property of G-111 generated edge squares.
The rejected alternatives were callbacks, diagnostic values, certificates,
and an aggregate vanishing antecedent; each would allow the desired conclusion
to enter the class definition or make conservativity vacuous.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation
open TransportCoherence

/-! ## Closed structural language and fixed heads -/

/-- The three constructors fixed by G-113; terms contain no semantic parameter. -/
inductive DiagnosticClassTerm
  | vertexwiseSourceMapInjective
  | edgewiseSquarePullback
  | conjunction (left right : DiagnosticClassTerm)
  deriving DecidableEq

namespace DiagnosticClassTerm

/-- Evaluate a structural term directly on a G-111 indexed diagram hom. -/
def eval {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (term : DiagnosticClassTerm)
    (hom : IndexedBaseDiagramHom D E) : Prop :=
  match term with
  | .vertexwiseSourceMapInjective =>
      ∀ vertex : G.Vertex,
        Function.Injective (hom.app vertex).doctrineHom.sourceMap
  | .edgewiseSquarePullback =>
      ∀ {i j : G.Vertex} (edge : G.Edge i j),
        IsPullback (hom.edgeSquare edge).left (hom.edgeSquare edge).top
          (hom.edgeSquare edge).bottom (hom.edgeSquare edge).right
  | .conjunction left right => left.eval hom ∧ right.eval hom

/-- The injectivity constructor exposes exactly its `sourceMap` dependency. -/
theorem eval_vertexwiseSourceMapInjective_iff
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E) :
    eval .vertexwiseSourceMapInjective hom ↔
      ∀ vertex : G.Vertex,
        Function.Injective (hom.app vertex).doctrineHom.sourceMap :=
  Iff.rfl

/-- The pullback constructor exposes exactly the generated edge-square dependency. -/
theorem eval_edgewiseSquarePullback_iff
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E) :
    eval .edgewiseSquarePullback hom ↔
      ∀ {i j : G.Vertex} (edge : G.Edge i j),
        IsPullback (hom.edgeSquare edge).left (hom.edgeSquare edge).top
          (hom.edgeSquare edge).bottom (hom.edgeSquare edge).right :=
  Iff.rfl

/-- Conjunction is the only language connective. -/
theorem eval_conjunction_iff (left right : DiagnosticClassTerm)
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E) :
    eval (.conjunction left right) hom ↔ eval left hom ∧ eval right hom :=
  Iff.rfl

end DiagnosticClassTerm

/-- The ordered three-term class sequence fixed before any G-113 proof. -/
def diagnosticClassTermCandidates : List DiagnosticClassTerm :=
  [ .vertexwiseSourceMapInjective,
    .conjunction .vertexwiseSourceMapInjective .edgewiseSquarePullback,
    .edgewiseSquarePullback ]

/-- The complete ordered class-term registry fixed by the G-113 card. -/
theorem diagnosticClassTermCandidates_eq_fixed_sequence :
    diagnosticClassTermCandidates =
      [ .vertexwiseSourceMapInjective,
        .conjunction .vertexwiseSourceMapInjective .edgewiseSquarePullback,
        .edgewiseSquarePullback ] :=
  rfl

/-- The mechanically selected initial class term is source-map injectivity. -/
theorem diagnosticClassTermCandidates_head :
    diagnosticClassTermCandidates.head? =
      some .vertexwiseSourceMapInjective :=
  rfl

/-- The second registered class term is the conjunction of both structural atoms. -/
theorem diagnosticClassTermCandidates_second :
    diagnosticClassTermCandidates.tail.head? =
      some (.conjunction .vertexwiseSourceMapInjective
        .edgewiseSquarePullback) :=
  rfl

/-- The third registered class term is edge-square pullback alone. -/
theorem diagnosticClassTermCandidates_third :
    diagnosticClassTermCandidates.tail.tail.head? =
      some .edgewiseSquarePullback :=
  rfl

/-- The fixed class-term registry is exhausted after its third entry. -/
theorem diagnosticClassTermCandidates_fourth :
    diagnosticClassTermCandidates.tail.tail.tail.head? = none :=
  rfl

/-- Every registered class term is one of the three card-fixed candidates. -/
theorem mem_diagnosticClassTermCandidates_iff (term : DiagnosticClassTerm) :
    term ∈ diagnosticClassTermCandidates ↔
      term = .vertexwiseSourceMapInjective ∨
      term = .conjunction .vertexwiseSourceMapInjective
        .edgewiseSquarePullback ∨
      term = .edgewiseSquarePullback := by
  rw [diagnosticClassTermCandidates_eq_fixed_sequence]
  simp only [List.mem_cons, List.not_mem_nil, or_false]

/-- The fixed O20 term, independent of every class-candidate transition. -/
def pointwiseReflectionTerm : DiagnosticClassTerm :=
  .vertexwiseSourceMapInjective

/-- O20 consumes the injectivity term by value, independently of the candidate list. -/
theorem pointwiseReflectionTerm_eq :
    pointwiseReflectionTerm = .vertexwiseSourceMapInjective :=
  rfl

/-- The sole G-113(i) candidate, stated without `Full` or `Faithful` in its definition. -/
def VertexwiseSourceMapBijective
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E) : Prop :=
  ∀ vertex : G.Vertex, Function.Bijective (hom.app vertex).doctrineHom.sourceMap

/-- The bijectivity candidate exposes exactly its vertexwise `sourceMap` meaning. -/
theorem vertexwiseSourceMapBijective_iff
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E) :
    VertexwiseSourceMapBijective hom ↔
      ∀ vertex : G.Vertex,
        Function.Bijective (hom.app vertex).doctrineHom.sourceMap :=
  Iff.rfl

/-- Closed tags for the independent G-113(i) candidate registry. -/
inductive FullFaithfulCandidate
  | vertexwiseSourceMapBijective
  deriving DecidableEq

/-- Interpret the fixed G-113(i) candidate without changing its predicate head. -/
def FullFaithfulCandidate.eval (candidate : FullFaithfulCandidate)
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E) : Prop :=
  match candidate with
  | .vertexwiseSourceMapBijective => VertexwiseSourceMapBijective hom

/-- The independent singleton registry fixed for G-113(i). -/
def fullFaithfulCandidateRegistry : List FullFaithfulCandidate :=
  [ .vertexwiseSourceMapBijective ]

/-- The G-113(i) registry is exactly the card-fixed singleton. -/
theorem fullFaithfulCandidateRegistry_eq_singleton :
    fullFaithfulCandidateRegistry = [ .vertexwiseSourceMapBijective ] :=
  rfl

/-- The sole mechanically selected G-113(i) candidate. -/
theorem fullFaithfulCandidateRegistry_head :
    fullFaithfulCandidateRegistry.head? =
      some .vertexwiseSourceMapBijective :=
  rfl

/-- The independent G-113(i) registry has no second candidate. -/
theorem fullFaithfulCandidateRegistry_second :
    fullFaithfulCandidateRegistry.tail.head? = none :=
  rfl

/-- Membership in the G-113(i) registry uniquely selects the fixed predicate. -/
theorem mem_fullFaithfulCandidateRegistry_iff
    (candidate : FullFaithfulCandidate) :
    candidate ∈ fullFaithfulCandidateRegistry ↔
      candidate = .vertexwiseSourceMapBijective := by
  rw [fullFaithfulCandidateRegistry_eq_singleton]
  exact List.mem_singleton

/-- The sole candidate evaluates to the card-fixed bijectivity predicate. -/
theorem fullFaithfulCandidate_eval_iff
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E) :
    FullFaithfulCandidate.eval .vertexwiseSourceMapBijective hom ↔
      VertexwiseSourceMapBijective hom :=
  Iff.rfl

/-- Membership in the generated class is evaluation of one pre-registered term. -/
def GeneratedDiagnosticClass
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (term : DiagnosticClassTerm)
    (hom : IndexedBaseDiagramHom D E) : Prop :=
  term.eval hom

/-- Generated class membership is exactly evaluation of the selected structural term. -/
theorem generatedDiagnosticClass_iff
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (term : DiagnosticClassTerm)
    (hom : IndexedBaseDiagramHom D E) :
    GeneratedDiagnosticClass term hom ↔ term.eval hom :=
  Iff.rfl

/-! ## Diagram-isomorphism witness head -/

/-- The existing category isomorphism between two G-111 indexed base diagrams. -/
abbrev IndexedBaseDiagramIso
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    (D E : IndexedBaseDiagram G U) := D ≅ E

/--
Isomorphisms of the source and target diagrams together with the forward and
backward natural squares relating two indexed diagram homs.
-/
structure IndexedBaseDiagramHomIsoWitness
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E D' E' : IndexedBaseDiagram G U}
    (first : IndexedBaseDiagramHom D E)
    (second : IndexedBaseDiagramHom D' E') where
  sourceIso : IndexedBaseDiagramIso D D'
  targetIso : IndexedBaseDiagramIso E E'
  forward_commutes : ∀ vertex : G.Vertex,
    first.app vertex ≫ targetIso.hom.app vertex =
      sourceIso.hom.app vertex ≫ second.app vertex
  backward_commutes : ∀ vertex : G.Vertex,
    second.app vertex ≫ targetIso.inv.app vertex =
      sourceIso.inv.app vertex ≫ first.app vertex

/-! ## Conservativity signature -/

/--
Per-interpretation diagnostic conservativity: every source interpretation whose
generated target obstruction vanishes already has vanishing source obstruction.
-/
def DiagnosticConservative
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E) : Prop :=
  ∀ source : IndexedDiagnosticInterpretation D,
    TransportObstructionVanishes
        (hom.transportedInterpretation source).toAdmissibleTransportData →
      TransportObstructionVanishes source.toAdmissibleTransportData

/-- The conservativity head exposes the required per-interpretation quantifier. -/
theorem diagnosticConservative_iff
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E) :
    DiagnosticConservative hom ↔
      ∀ source : IndexedDiagnosticInterpretation D,
        TransportObstructionVanishes
            (hom.transportedInterpretation source).toAdmissibleTransportData →
          TransportObstructionVanishes source.toAdmissibleTransportData :=
  Iff.rfl

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
