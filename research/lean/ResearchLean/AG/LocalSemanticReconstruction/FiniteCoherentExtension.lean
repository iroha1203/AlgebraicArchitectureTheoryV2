import ResearchLean.AG.LocalSemanticReconstruction.FiniteComponentEnumeration
import ResearchLean.AG.LocalSemanticReconstruction.FinitePrecompositionAlgorithm
import Formal.Util.AssertStandardAxioms

/-!
# Finite coherent vertex tables and component-family extension

G-124(D) reads a retained vertex table as coherent exactly when its values
agree across every named edge retained by the actual induced graph.  With
explicit finite graph tables and decidable value equality, this condition is
an executable finite decision.

A coherent table descends directly through the accepted induced-component
quotient.  No representative is selected.  When the induced component map
retains full connectivity, the Cycle 11 finite precomposition algorithm then
computes a full-component family whose value at every retained vertex is the
original table value.

Implementation notes: coherence is stated on the named-edge table rather than
on already-computed components, because this is the finite input presentation
fixed by G-124(D).  Quotient descent is used instead of enumerating component
representatives, preserving both the accepted component relation and the
computational finite-search route.
-/

namespace AAT.AG.LocalSemanticReconstruction

open RealizationReconstruction

namespace FiniteCoherentExtension

/-- G-124(D) input API: a retained-vertex table on the actual induced graph. -/
abbrev VertexTable (F : FixedFDirectedMultigraph) (S : F.Vertex → Prop)
    (Value : Type*) :=
  (InducedComponent.graph F S).Vertex → Value

/-- G-124(D) finite coherence predicate: the supplied table has equal values
at the two endpoints of every retained named edge. -/
def EdgeCoherent {F : FixedFDirectedMultigraph} {S : F.Vertex → Prop}
    {Value : Type*} (table : VertexTable F S Value) : Prop :=
  ∀ namedEdge : (InducedComponent.graph F S).Edge,
    table ((InducedComponent.graph F S).source namedEdge) =
      table ((InducedComponent.graph F S).target namedEdge)

/-- G-124(D) accepted input package: a retained-vertex table together with
its edge-coherence proof. -/
abbrev CoherentVertexTable (F : FixedFDirectedMultigraph)
    (S : F.Vertex → Prop) (Value : Type*) :=
  { table : VertexTable F S Value // EdgeCoherent table }

/-- G-124(D) executable coherence API.  Its finite edge table, retained-vertex
predicate decision, and value equality decision are supplied input data. -/
def coherenceTest
    (F : FixedFDirectedMultigraph)
    [Fintype F.Edge]
    (S : F.Vertex → Prop) [DecidablePred S]
    (Value : Type*) [DecidableEq Value]
    (table : VertexTable F S Value) : Bool := by
  letI : Fintype (InducedComponent.graph F S).Edge :=
    Subtype.fintype
      (fun namedEdge : F.Edge => S (F.source namedEdge) ∧ S (F.target namedEdge))
  letI : Decidable (EdgeCoherent table) := by
    unfold EdgeCoherent
    infer_instance
  exact decide (EdgeCoherent table)

/-- G-124(D) correctness theorem: the finite Bool coherence test is true
exactly when every actual retained named edge satisfies its table equation. -/
@[simp]
theorem coherenceTest_eq_true_iff
    (F : FixedFDirectedMultigraph)
    [Fintype F.Edge]
    (S : F.Vertex → Prop) [DecidablePred S]
    (Value : Type*) [DecidableEq Value]
    (table : VertexTable F S Value) :
    coherenceTest F S Value table = true ↔ EdgeCoherent table := by
  letI : Fintype (InducedComponent.graph F S).Edge :=
    Subtype.fintype
      (fun namedEdge : F.Edge => S (F.source namedEdge) ∧ S (F.target namedEdge))
  letI : Decidable (EdgeCoherent table) := by
    unfold EdgeCoherent
    infer_instance
  simp [coherenceTest]

/-- G-124(D) quotient-descent API: edge coherence extends along the accepted
generated reachability relation. -/
theorem value_eq_of_reachable
    {F : FixedFDirectedMultigraph} {S : F.Vertex → Prop}
    {Value : Type*} (table : VertexTable F S Value)
    (coherent : EdgeCoherent table)
    {first second : (InducedComponent.graph F S).Vertex}
    (reachable : InducedComponent.Reachable F S first second) :
    table first = table second := by
  induction reachable with
  | rel first second step =>
      obtain ⟨namedEdge, sourceEquality, targetEquality⟩ := step
      subst first
      subst second
      exact coherent namedEdge
  | refl vertex =>
      rfl
  | symm first second relation inductionHypothesis =>
      exact inductionHypothesis.symm
  | trans first second third firstRelation secondRelation
      firstInduction secondInduction =>
      exact firstInduction.trans secondInduction

/-- G-124(D) main descent construction: a coherent retained-vertex table
becomes a family on the actual induced-component quotient, without selecting
component representatives. -/
def descend
    {F : FixedFDirectedMultigraph} {S : F.Vertex → Prop} {Value : Type*}
    (table : CoherentVertexTable F S Value) :
    InducedComponent.Component F S → Value :=
  Quotient.lift table.1
    (fun _ _ reachable => value_eq_of_reachable table.1 table.2 reachable)

/-- G-124(D) descent computation rule: reading the descended family at a
retained vertex returns the original table entry. -/
@[simp]
theorem descend_mk
    {F : FixedFDirectedMultigraph} {S : F.Vertex → Prop} {Value : Type*}
    (table : CoherentVertexTable F S Value)
    (vertex : (InducedComponent.graph F S).Vertex) :
    descend table (fixedFComponentMk (InducedComponent.graph F S) vertex) =
      table.1 vertex :=
  rfl

/-- G-124(D) comparison API: component families are exactly coherent actual
retained-vertex tables. -/
def componentFamilyEquivCoherentVertexTable
    (F : FixedFDirectedMultigraph) (S : F.Vertex → Prop) (Value : Type*) :
    (InducedComponent.Component F S → Value) ≃
      CoherentVertexTable F S Value where
  toFun family :=
    ⟨fun vertex => family (fixedFComponentMk (InducedComponent.graph F S) vertex),
      fun namedEdge => congrArg family
        (fixedFComponent_source_eq_target
          (InducedComponent.graph F S) namedEdge)⟩
  invFun := descend
  left_inv family := by
    funext component
    refine Quotient.inductionOn component ?_
    intro vertex
    rfl
  right_inv table := by
    apply Subtype.ext
    funext vertex
    rfl

/-- G-124(D) computed extension: first descend the coherent vertex table to
induced components, then run the Cycle 11 finite precomposition algorithm
along the actual induced-to-full component map.  The finite graph tables,
vertex equality, predicate decision, and fallback value are supplied inputs. -/
def extendToFullComponents
    (F : FixedFDirectedMultigraph)
    [Fintype F.Vertex] [DecidableEq F.Vertex] [Fintype F.Edge]
    (S : F.Vertex → Prop) [DecidablePred S]
    {Value : Type*}
    (table : CoherentVertexTable F S Value) (fallback : Value) :
    FixedFComponent F → Value := by
  letI : Fintype (InducedComponent.Component F S) :=
    FiniteComponent.inducedComponentFintype F S
  letI : DecidableEq (FixedFComponent F) :=
    FiniteComponent.componentDecidableEq F
  exact FinitePrecomposition.extension
    (InducedComponent.toFull F S) (descend table) fallback

/-- G-124(D) extension correctness: if the retained graph preserves full
connectivity, the computed full-component family reads back to the original
table at every retained vertex. -/
@[simp]
theorem extendToFullComponents_mk
    (F : FixedFDirectedMultigraph)
    [Fintype F.Vertex] [DecidableEq F.Vertex] [Fintype F.Edge]
    (S : F.Vertex → Prop) [DecidablePred S]
    {Value : Type*}
    (table : CoherentVertexTable F S Value) (fallback : Value)
    (retains : InducedComponent.RetainsFullConnectivity F S)
    (vertex : (InducedComponent.graph F S).Vertex) :
    extendToFullComponents F S table fallback
        (fixedFComponentMk F vertex.1) = table.1 vertex := by
  letI : Fintype (InducedComponent.Component F S) :=
    FiniteComponent.inducedComponentFintype F S
  letI : DecidableEq (FixedFComponent F) :=
    FiniteComponent.componentDecidableEq F
  have injective : Function.Injective (InducedComponent.toFull F S) :=
    (InducedComponent.toFull_injective_iff_retainsFullConnectivity F S).2 retains
  have readback := congrFun
    (FinitePrecomposition.precompose_extension
      (InducedComponent.toFull F S) (descend table) fallback injective)
    (fixedFComponentMk (InducedComponent.graph F S) vertex)
  simpa only [InducedComponent.toFull_mk, descend_mk] using readback

/-! ### Non-vacuity examples for edge coherence -/

/-- The two vertices of the G-124(D) edge-coherence test example. -/
abbrev ExampleVertex := Bool

/-- The single named edge of the edge-coherence test example. -/
abbrev ExampleEdge := Unit

/-- A nondegenerate finite graph with one named edge from `source` to
`target`, used to test both truth values of the new coherence predicate. -/
def exampleGraph : FixedFDirectedMultigraph where
  Vertex := ExampleVertex
  Edge := ExampleEdge
  source _ := false
  target _ := true

instance : Fintype exampleGraph.Edge := inferInstanceAs (Fintype Unit)

/-- A concrete retained-vertex table satisfying `EdgeCoherent`: it is
constant on the endpoints of the actual named edge. -/
def coherentExampleTable :
    VertexTable exampleGraph (fun _ => True) Bool :=
  fun _ => false

/-- The concrete constant table is edge-coherent. -/
theorem coherentExampleTable_edgeCoherent :
    EdgeCoherent coherentExampleTable := by
  intro namedEdge
  rfl

/-- A concrete retained-vertex table that distinguishes the endpoints of the
actual named edge. -/
def incoherentExampleTable :
    VertexTable exampleGraph (fun _ => True) Bool :=
  fun vertex =>
    match vertex.1 with
    | false => false
    | true => true

/-- The endpoint-distinguishing table is not edge-coherent. -/
theorem incoherentExampleTable_not_edgeCoherent :
    ¬ EdgeCoherent incoherentExampleTable := by
  intro coherent
  have endpointEquality := coherent
    (⟨(), True.intro, True.intro⟩ :
      (InducedComponent.graph exampleGraph (fun _ => True)).Edge)
  exact Bool.noConfusion endpointEquality

/-- The executable coherence test accepts the concrete coherent table. -/
example :
    coherenceTest exampleGraph (fun _ => True) Bool coherentExampleTable = true := by
  exact (coherenceTest_eq_true_iff
    exampleGraph (fun _ => True) Bool coherentExampleTable).2
      coherentExampleTable_edgeCoherent

/-- The executable coherence test rejects the concrete incoherent table. -/
example :
    coherenceTest exampleGraph (fun _ => True) Bool incoherentExampleTable = false := by
  apply Bool.eq_false_iff.mpr
  intro testIsTrue
  exact incoherentExampleTable_not_edgeCoherent
    ((coherenceTest_eq_true_iff
      exampleGraph (fun _ => True) Bool incoherentExampleTable).1 testIsTrue)

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.FiniteCoherentExtension

end FiniteCoherentExtension

end AAT.AG.LocalSemanticReconstruction
