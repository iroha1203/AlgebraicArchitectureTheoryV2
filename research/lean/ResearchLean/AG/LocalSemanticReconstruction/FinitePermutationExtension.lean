import ResearchLean.AG.LocalSemanticReconstruction.FiniteCoherentExtension
import ResearchLean.AG.LocalSemanticReconstruction.PermutationRestrictionCriteria
import Mathlib.Data.Fintype.Perm
import Formal.Util.AssertStandardAxioms

/-!
# Finite permutation-valued coherence and preserving-change extension

G-124(D) fixes a finite hidden carrier `K`.  Its actual local value type is
`Equiv.Perm K`, whose finite table and decidable equality are inherited from
the supplied finite enumeration and equality decision on `K`.

This file specializes the Cycle 13 coherent-table algorithm to those
permutation values, uses the identity permutation as the explicit totalization
fallback, and transports the computed full component family through the
accepted classification of operation-preserving following changes.  The final
raw-table API returns `none` exactly on the incoherent branch and an actual
preserving change on the coherent branch.

Implementation notes:

* `Finset.univ` is used for the actual `Equiv.Perm K` value table; a supplied
  list or a separate permutation-code type was rejected because either could
  omit actual permutations and weaken the fixed finite-input claim.
* The identity permutation is the explicit off-image fallback.  Requiring an
  additional arbitrary fallback would add input not needed by the actual
  permutation specialization.
* The construction does not stop at a full component family: it applies the
  inverse of the accepted preserving-change classification so that the output
  is an actual operation-preserving following change.
* The raw API decides edge coherence internally.  Accepting a coherence
  certificate as raw input was rejected because it would bypass the required
  executable decision on the supplied finite table.
-/

namespace AAT.AG.LocalSemanticReconstruction

open RealizationReconstruction

namespace FinitePermutationExtension

/-- G-124(D) finite value table: all permutations of the supplied finite
hidden carrier. -/
def permutationValues (K : Type*) [Fintype K] [DecidableEq K] :
    Finset (Equiv.Perm K) :=
  Finset.univ

/-- The finite permutation table contains every actual hidden permutation. -/
@[simp]
theorem mem_permutationValues
    (K : Type*) [Fintype K] [DecidableEq K]
    (permutation : Equiv.Perm K) :
    permutation ∈ permutationValues K := by
  simp [permutationValues]

/-- The supplied finite carrier yields exactly `|K|!` permutation values. -/
theorem card_permutationValues
    (K : Type*) [Fintype K] [DecidableEq K] :
    (permutationValues K).card = (Fintype.card K).factorial := by
  simpa [permutationValues] using (Fintype.card_perm (α := K))

/-- G-124(D) executable coherence decision specialized to the actual hidden
permutation value table. -/
def permutationCoherenceTest
    (F : FixedFDirectedMultigraph)
    [Fintype F.Edge]
    (S : F.Vertex → Prop) [DecidablePred S]
    (K : Type*) [Fintype K] [DecidableEq K]
    (table : FiniteCoherentExtension.VertexTable F S (Equiv.Perm K)) : Bool :=
  FiniteCoherentExtension.coherenceTest F S (Equiv.Perm K) table

/-- The specialized Bool test accepts exactly the tables coherent on every
actual retained named edge. -/
@[simp]
theorem permutationCoherenceTest_eq_true_iff
    (F : FixedFDirectedMultigraph)
    [Fintype F.Edge]
    (S : F.Vertex → Prop) [DecidablePred S]
    (K : Type*) [Fintype K] [DecidableEq K]
    (table : FiniteCoherentExtension.VertexTable F S (Equiv.Perm K)) :
    permutationCoherenceTest F S K table = true ↔
      FiniteCoherentExtension.EdgeCoherent table :=
  FiniteCoherentExtension.coherenceTest_eq_true_iff
    F S (Equiv.Perm K) table

/-- G-124(D) accepted coherent local permutation table. -/
abbrev CoherentPermutationTable
    (F : FixedFDirectedMultigraph) (S : F.Vertex → Prop)
    (K : Type*) :=
  FiniteCoherentExtension.CoherentVertexTable F S (Equiv.Perm K)

/-- Extend a coherent local permutation table to the actual full-component
family.  The identity permutation supplies the value away from the retained
image. -/
def extendPermutationFamily
    (F : FixedFDirectedMultigraph)
    [Fintype F.Vertex] [DecidableEq F.Vertex] [Fintype F.Edge]
    (S : F.Vertex → Prop) [DecidablePred S]
    (K : Type*) [Fintype K] [DecidableEq K]
    (table : CoherentPermutationTable F S K) :
    PermutationRestriction.FullFamily F K :=
  FiniteCoherentExtension.extendToFullComponents F S table 1

/-- Under the accepted connectivity criterion, the computed full family
reads back to the original local permutation at every retained vertex. -/
@[simp]
theorem extendPermutationFamily_mk
    (F : FixedFDirectedMultigraph)
    [Fintype F.Vertex] [DecidableEq F.Vertex] [Fintype F.Edge]
    (S : F.Vertex → Prop) [DecidablePred S]
    (K : Type*) [Fintype K] [DecidableEq K]
    (table : CoherentPermutationTable F S K)
    (retains : InducedComponent.RetainsFullConnectivity F S)
    (vertex : (InducedComponent.graph F S).Vertex) :
    extendPermutationFamily F S K table (fixedFComponentMk F vertex.1) =
      table.1 vertex :=
  FiniteCoherentExtension.extendToFullComponents_mk
    F S table 1 retains vertex

/-- Transport the computed component-permutation family through the accepted
classification to an actual operation-preserving following change. -/
def extendPreservingChange
    (F : FixedFDirectedMultigraph)
    [Fintype F.Vertex] [DecidableEq F.Vertex] [Fintype F.Edge]
    (S : F.Vertex → Prop) [DecidablePred S]
    (K : Type*) [Fintype K] [DecidableEq K]
    (u : FixedFGraphAutomorphism F)
    (table : CoherentPermutationTable F S K) :
    PermutationRestriction.PreservingChange F K u :=
  (FixedFFollowingStateChange.preservingEquivComponentPermutationFamilies
    (F := F) (K := K) (u := u)).symm
      (extendPermutationFamily F S K table)

/-- Classifying the computed preserving change and reading it at a retained
vertex returns the original local permutation. -/
@[simp]
theorem extendPreservingChange_classification_mk
    (F : FixedFDirectedMultigraph)
    [Fintype F.Vertex] [DecidableEq F.Vertex] [Fintype F.Edge]
    (S : F.Vertex → Prop) [DecidablePred S]
    (K : Type*) [Fintype K] [DecidableEq K]
    (u : FixedFGraphAutomorphism F)
    (table : CoherentPermutationTable F S K)
    (retains : InducedComponent.RetainsFullConnectivity F S)
    (vertex : (InducedComponent.graph F S).Vertex) :
    FixedFFollowingStateChange.preservingEquivComponentPermutationFamilies
        (extendPreservingChange F S K u table)
        (fixedFComponentMk F vertex.1) = table.1 vertex := by
  rw [extendPreservingChange]
  simp only [Equiv.apply_symm_apply]
  exact extendPermutationFamily_mk F S K table retains vertex

/-- Complete executable route from a raw finite local permutation table:
reject incoherent input and otherwise compute an actual preserving change. -/
def decideAndExtendPreservingChange
    (F : FixedFDirectedMultigraph)
    [Fintype F.Vertex] [DecidableEq F.Vertex] [Fintype F.Edge]
    (S : F.Vertex → Prop) [DecidablePred S]
    (K : Type*) [Fintype K] [DecidableEq K]
    (u : FixedFGraphAutomorphism F)
    (table : FiniteCoherentExtension.VertexTable F S (Equiv.Perm K)) :
    Option (PermutationRestriction.PreservingChange F K u) := by
  letI : Fintype (InducedComponent.graph F S).Edge :=
    Subtype.fintype
      (fun namedEdge : F.Edge => S (F.source namedEdge) ∧ S (F.target namedEdge))
  letI : Decidable (FiniteCoherentExtension.EdgeCoherent table) := by
    unfold FiniteCoherentExtension.EdgeCoherent
    infer_instance
  exact if coherent : FiniteCoherentExtension.EdgeCoherent table then
    some (extendPreservingChange F S K u ⟨table, coherent⟩)
  else
    none

/-- The raw-table algorithm rejects exactly the incoherent permutation
tables; coherence is decided internally from the actual retained edges. -/
@[simp]
theorem decideAndExtendPreservingChange_eq_none_iff
    (F : FixedFDirectedMultigraph)
    [Fintype F.Vertex] [DecidableEq F.Vertex] [Fintype F.Edge]
    (S : F.Vertex → Prop) [DecidablePred S]
    (K : Type*) [Fintype K] [DecidableEq K]
    (u : FixedFGraphAutomorphism F)
    (table : FiniteCoherentExtension.VertexTable F S (Equiv.Perm K)) :
    decideAndExtendPreservingChange F S K u table = none ↔
      ¬ FiniteCoherentExtension.EdgeCoherent table := by
  unfold decideAndExtendPreservingChange
  split <;> simp_all

/-- Every successful raw-table computation has the required retained-vertex
readback through the accepted preserving-change classification. -/
theorem decideAndExtendPreservingChange_readback
    (F : FixedFDirectedMultigraph)
    [Fintype F.Vertex] [DecidableEq F.Vertex] [Fintype F.Edge]
    (S : F.Vertex → Prop) [DecidablePred S]
    (K : Type*) [Fintype K] [DecidableEq K]
    (u : FixedFGraphAutomorphism F)
    (table : FiniteCoherentExtension.VertexTable F S (Equiv.Perm K))
    (retains : InducedComponent.RetainsFullConnectivity F S)
    (change : PermutationRestriction.PreservingChange F K u)
    (success : decideAndExtendPreservingChange F S K u table = some change)
    (vertex : (InducedComponent.graph F S).Vertex) :
    FixedFFollowingStateChange.preservingEquivComponentPermutationFamilies change
        (fixedFComponentMk F vertex.1) = table vertex := by
  unfold decideAndExtendPreservingChange at success
  split at success
  next coherent =>
    simp only [Option.some.injEq] at success
    subst change
    exact extendPreservingChange_classification_mk
      F S K u ⟨table, coherent⟩ retains vertex
  next notCoherent =>
    simp at success

/-! ### Executable permutation-coherence examples -/

/-- A constant permutation table on the Cycle 13 one-edge graph. -/
def coherentPermutationExampleTable :
    FiniteCoherentExtension.VertexTable
      FiniteCoherentExtension.exampleGraph (fun _ => True) (Equiv.Perm Bool) :=
  fun _ => 1

/-- The constant permutation table is coherent on the actual named edge. -/
theorem coherentPermutationExampleTable_edgeCoherent :
    FiniteCoherentExtension.EdgeCoherent coherentPermutationExampleTable := by
  intro namedEdge
  rfl

/-- A permutation table assigning identity at the source and the Bool swap at
the target of the Cycle 13 actual named edge. -/
def incoherentPermutationExampleTable :
    FiniteCoherentExtension.VertexTable
      FiniteCoherentExtension.exampleGraph (fun _ => True) (Equiv.Perm Bool) :=
  fun vertex =>
    match vertex.1 with
    | false => 1
    | true => Equiv.swap false true

/-- The identity/swap table is not coherent on the actual named edge. -/
theorem incoherentPermutationExampleTable_not_edgeCoherent :
    ¬ FiniteCoherentExtension.EdgeCoherent incoherentPermutationExampleTable := by
  intro coherent
  have endpointEquality := coherent
    (⟨(), True.intro, True.intro⟩ :
      (InducedComponent.graph
        FiniteCoherentExtension.exampleGraph (fun _ => True)).Edge)
  change (1 : Equiv.Perm Bool) = Equiv.swap false true at endpointEquality
  have valueEquality := congrArg
    (fun permutation : Equiv.Perm Bool => permutation false) endpointEquality
  simp at valueEquality

/-- The specialized executable test accepts the coherent permutation table. -/
example :
    permutationCoherenceTest FiniteCoherentExtension.exampleGraph
        (fun _ => True) Bool coherentPermutationExampleTable = true := by
  exact (permutationCoherenceTest_eq_true_iff
    FiniteCoherentExtension.exampleGraph (fun _ => True) Bool
      coherentPermutationExampleTable).2
        coherentPermutationExampleTable_edgeCoherent

/-- The specialized executable test rejects the incoherent permutation table. -/
example :
    permutationCoherenceTest FiniteCoherentExtension.exampleGraph
        (fun _ => True) Bool incoherentPermutationExampleTable = false := by
  apply Bool.eq_false_iff.mpr
  intro testIsTrue
  exact incoherentPermutationExampleTable_not_edgeCoherent
    ((permutationCoherenceTest_eq_true_iff
      FiniteCoherentExtension.exampleGraph (fun _ => True) Bool
        incoherentPermutationExampleTable).1 testIsTrue)

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.FinitePermutationExtension

end FinitePermutationExtension

end AAT.AG.LocalSemanticReconstruction
