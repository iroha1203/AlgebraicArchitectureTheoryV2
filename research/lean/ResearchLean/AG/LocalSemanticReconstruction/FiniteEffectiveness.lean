import ResearchLean.AG.LocalSemanticReconstruction.FiniteDetermination
import ResearchLean.AG.LocalSemanticReconstruction.FinitePermutationExtension
import Formal.Util.AssertStandardAxioms

/-!
# The common finite-reading effectiveness property

G-124(D) requires effectiveness to remain separate from separation and
extension.  An effectiveness program decides the independently specified
coherence predicate on every finite table, attempts extension from the raw
table, rejects exactly incoherent input, and proves readback for every
successful result.  `FiniteReading.Effective` is the existence of this data;
the program itself remains available as computational content.

The graph specialization uses the actual retained named-edge predicate and
the actual operation-preserving following-change output from Cycles 13--14.

Implementation notes:

* The raw extension field returns `Option A`.  Accepting a coherence proof as
  an input was rejected because it would bypass the required coherence
  decision; returning an unconditionally supplied global element was rejected
  because incoherent tables must be detected.
* `Effective` is not conjoined with `Determining`: G-124(D) requires
  separation, extension, and effectiveness to be three independent
  properties.
* The graph adapter only changes the finite-table index presentation from
  Finset membership to the definitionally corresponding retained-vertex
  subtype.  It does not select component representatives or introduce a proxy
  family.
-/

namespace AAT.AG.LocalSemanticReconstruction

open RealizationReconstruction

namespace FiniteReading

/-- Computational data witnessing effectiveness of one finite reading. -/
structure EffectivenessProgram
    {A Index Value : Type*}
    (read : A → Index → Value)
    (S : Finset Index)
    (Coherent : ({index // index ∈ S} → Value) → Prop) where
  coherenceTest : ({index // index ∈ S} → Value) → Bool
  coherenceTest_eq_true_iff :
    ∀ table, coherenceTest table = true ↔ Coherent table
  extend? : ({index // index ∈ S} → Value) → Option A
  extend_eq_none_iff : ∀ table, extend? table = none ↔ ¬ Coherent table
  restrict_eq_of_extend_eq_some :
    ∀ table global, extend? table = some global →
      restrict read S global = table

/-- The third G-124(D) finite-reading property: an executable coherence
decision and raw-table extension program with exact rejection and readback. -/
def Effective
    {A Index Value : Type*}
    (read : A → Index → Value)
    (S : Finset Index)
    (Coherent : ({index // index ∈ S} → Value) → Prop) : Prop :=
  Nonempty (EffectivenessProgram read S Coherent)

/-- Effectiveness is not automatic: with no global element, even the unique
empty-index table cannot be extended when coherence accepts every table. -/
theorem emptyGlobal_not_effective :
    ¬ Effective
      (fun global : Empty => (nomatch global : Empty → Unit))
      (∅ : Finset Empty)
      (fun _ : ({index // index ∈ (∅ : Finset Empty)} → Unit) => True) := by
  rintro ⟨program⟩
  let table : {index // index ∈ (∅ : Finset Empty)} → Unit :=
    fun index => nomatch index.1
  have notNone : program.extend? table ≠ none := by
    intro extensionIsNone
    exact ((program.extend_eq_none_iff table).1 extensionIsNone) True.intro
  cases extensionResult : program.extend? table with
  | none => exact notNone extensionResult
  | some global => exact Empty.elim global

end FiniteReading

namespace FiniteEffectiveness

/-- The explicit finite set of retained vertices supplied by the graph table
and decidable predicate. -/
def retainedVertices
    (F : FixedFDirectedMultigraph) [Fintype F.Vertex]
    (S : F.Vertex → Prop) [DecidablePred S] : Finset F.Vertex :=
  Finset.univ.filter S

/-- Read an actual preserving following change at one visible vertex through
the accepted component-permutation classification. -/
def readPreservingChangeAt
    (F : FixedFDirectedMultigraph) (K : Type*)
    (u : FixedFGraphAutomorphism F)
    (change : PermutationRestriction.PreservingChange F K u)
    (vertex : F.Vertex) : Equiv.Perm K :=
  FixedFFollowingStateChange.preservingEquivComponentPermutationFamilies change
    (fixedFComponentMk F vertex)

/-- Convert the common Finset-indexed local table to the actual induced-graph
vertex table used by the executable retained-edge algorithm. -/
def toPermutationVertexTable
    (F : FixedFDirectedMultigraph) [Fintype F.Vertex]
    (S : F.Vertex → Prop) [DecidablePred S]
    (K : Type*)
    (table : {vertex // vertex ∈ retainedVertices F S} → Equiv.Perm K) :
    FiniteCoherentExtension.VertexTable F S (Equiv.Perm K) :=
  fun vertex => table ⟨vertex.1, by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ vertex.1, vertex.2⟩⟩

/-- The common-surface coherence predicate is exactly equality across every
actual named edge retained by the induced graph. -/
def PermutationTableCoherent
    (F : FixedFDirectedMultigraph) [Fintype F.Vertex]
    (S : F.Vertex → Prop) [DecidablePred S]
    (K : Type*)
    (table : {vertex // vertex ∈ retainedVertices F S} → Equiv.Perm K) : Prop :=
  FiniteCoherentExtension.EdgeCoherent
    (toPermutationVertexTable F S K table)

/-- Cycles 11--15 realize the common effectiveness program for actual
permutation readings and actual preserving following changes. -/
def permutationEffectivenessProgram
    (F : FixedFDirectedMultigraph)
    [Fintype F.Vertex] [DecidableEq F.Vertex] [Fintype F.Edge]
    (S : F.Vertex → Prop) [DecidablePred S]
    (K : Type*) [Fintype K] [DecidableEq K]
    (u : FixedFGraphAutomorphism F)
    (retains : InducedComponent.RetainsFullConnectivity F S) :
    FiniteReading.EffectivenessProgram
      (readPreservingChangeAt F K u)
      (retainedVertices F S)
      (PermutationTableCoherent F S K) where
  coherenceTest table :=
    FinitePermutationExtension.permutationCoherenceTest
      F S K (toPermutationVertexTable F S K table)
  coherenceTest_eq_true_iff table := by
    exact FinitePermutationExtension.permutationCoherenceTest_eq_true_iff
      F S K (toPermutationVertexTable F S K table)
  extend? table :=
    FinitePermutationExtension.decideAndExtendPreservingChange
      F S K u (toPermutationVertexTable F S K table)
  extend_eq_none_iff table := by
    exact FinitePermutationExtension.decideAndExtendPreservingChange_eq_none_iff
      F S K u (toPermutationVertexTable F S K table)
  restrict_eq_of_extend_eq_some table change success := by
    funext vertex
    have retained : S vertex.1 := by
      have membership := vertex.2
      change vertex.1 ∈ Finset.univ.filter S at membership
      exact (Finset.mem_filter.mp membership).2
    exact FinitePermutationExtension.decideAndExtendPreservingChange_readback
      F S K u (toPermutationVertexTable F S K table) retains change success
        ⟨vertex.1, retained⟩

/-- The executable decision/extension route proves the third common property
without deriving it from separation or extension. -/
theorem permutation_effective
    (F : FixedFDirectedMultigraph)
    [Fintype F.Vertex] [DecidableEq F.Vertex] [Fintype F.Edge]
    (S : F.Vertex → Prop) [DecidablePred S]
    (K : Type*) [Fintype K] [DecidableEq K]
    (u : FixedFGraphAutomorphism F)
    (retains : InducedComponent.RetainsFullConnectivity F S) :
    FiniteReading.Effective
      (readPreservingChangeAt F K u)
      (retainedVertices F S)
      (PermutationTableCoherent F S K) :=
  ⟨permutationEffectivenessProgram F S K u retains⟩

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.FiniteReading
#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.FiniteEffectiveness

end FiniteEffectiveness

end AAT.AG.LocalSemanticReconstruction
