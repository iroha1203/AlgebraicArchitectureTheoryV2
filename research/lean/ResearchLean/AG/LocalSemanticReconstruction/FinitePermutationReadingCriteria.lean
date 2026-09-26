import ResearchLean.AG.LocalSemanticReconstruction.FiniteReadingCore
import ResearchLean.AG.LocalSemanticReconstruction.FiniteCoherentExtension
import ResearchLean.AG.LocalSemanticReconstruction.PermutationRestrictionCriteria
import Formal.Util.AssertStandardAxioms

/-!
# Finite vertex readings for arbitrary fixed operation graphs

The accepted component restriction criteria are expressed here on the same
finite raw vertex tables used by `FiniteReading`.  Neither the full graph nor
the hidden carrier is assumed finite for the separation and extension results.
-/

namespace AAT.AG.LocalSemanticReconstruction

open RealizationReconstruction

namespace FinitePermutationReadingCriteria

universe u v

variable (F : FixedFDirectedMultigraph.{u, v}) (K : Type*)
  (u : FixedFGraphAutomorphism F)

/-- Read the hidden permutation of an actual following change at a vertex. -/
def readAt (change : PermutationRestriction.PreservingChange F K u)
    (vertex : F.Vertex) : Equiv.Perm K :=
  FixedFFollowingStateChange.preservingEquivComponentPermutationFamilies change
    (fixedFComponentMk F vertex)

/-- The retained named-edge equations on a raw finite vertex table. -/
def EdgeCoherent (S : Finset F.Vertex)
    (table : {vertex // vertex ∈ S} → Equiv.Perm K) : Prop :=
  FiniteCoherentExtension.EdgeCoherent
    (F := F) (S := fun vertex => vertex ∈ S) table

/-- Finite point readings separate actual changes exactly when the selected
vertices meet every full component. -/
theorem separates_iff [Nontrivial K] (S : Finset F.Vertex) :
    FiniteReading.Separates (readAt F K u) S ↔
      InducedComponent.MeetsEveryFullComponent F
        (fun vertex => vertex ∈ S) := by
  rw [← PermutationRestriction.restrictPreservingChange_injective_iff_meetsEveryFullComponent
    (K := K) F (fun vertex => vertex ∈ S) u]
  constructor
  · intro h first second heq
    apply h
    funext selected
    have atComponent := congrFun heq
      (fixedFComponentMk
        (InducedComponent.graph F (fun vertex => vertex ∈ S))
        ⟨selected.1, selected.2⟩)
    simpa [PermutationRestriction.restrictPreservingChange,
      PermutationRestriction.restrict, ComponentRestriction.precompose,
      FiniteReading.restrict, readAt] using atComponent
  · intro h first second heq
    apply h
    funext component
    refine Quotient.inductionOn component ?_
    intro vertex
    have atVertex := congrFun heq ⟨vertex.1, vertex.2⟩
    simpa [PermutationRestriction.restrictPreservingChange,
      PermutationRestriction.restrict, ComponentRestriction.precompose,
      FiniteReading.restrict, readAt] using atVertex

/-- Every retained-edge-coherent raw table extends exactly when the induced
graph retains the full connectivity between its selected vertices. -/
theorem extends_iff [Nontrivial K] (S : Finset F.Vertex) :
    FiniteReading.Extends (readAt F K u) S (EdgeCoherent F K S) ↔
      InducedComponent.RetainsFullConnectivity F
        (fun vertex => vertex ∈ S) := by
  rw [← PermutationRestriction.restrictPreservingChange_surjective_iff_retainsFullConnectivity
    (K := K) F (fun vertex => vertex ∈ S) u]
  constructor
  · intro hextends family
    let table : {vertex // vertex ∈ S} → Equiv.Perm K :=
      fun vertex => family
        (fixedFComponentMk
          (InducedComponent.graph F (fun vertex => vertex ∈ S)) vertex)
    have coherent : EdgeCoherent F K S table := by
      intro edge
      exact congrArg family
        (fixedFComponent_source_eq_target
          (InducedComponent.graph F (fun vertex => vertex ∈ S)) edge)
    obtain ⟨change, hread⟩ := hextends table coherent
    refine ⟨change, ?_⟩
    funext component
    refine Quotient.inductionOn component ?_
    intro vertex
    have atVertex := congrFun hread ⟨vertex.1, vertex.2⟩
    simpa [PermutationRestriction.restrictPreservingChange,
      PermutationRestriction.restrict, ComponentRestriction.precompose,
      FiniteReading.restrict, readAt, table] using atVertex
  · intro hsurjective table coherent
    let family : InducedComponent.Component F
        (fun vertex => vertex ∈ S) → Equiv.Perm K :=
      (FiniteCoherentExtension.componentFamilyEquivCoherentVertexTable
        F (fun vertex => vertex ∈ S) (Equiv.Perm K)).symm
        ⟨table, coherent⟩
    obtain ⟨change, hread⟩ := hsurjective family
    refine ⟨change, ?_⟩
    funext vertex
    have atComponent := congrFun hread
      (fixedFComponentMk
        (InducedComponent.graph F (fun vertex => vertex ∈ S))
        ⟨vertex.1, vertex.2⟩)
    simpa [PermutationRestriction.restrictPreservingChange,
      PermutationRestriction.restrict, ComponentRestriction.precompose,
      FiniteReading.restrict, readAt, family,
      FiniteCoherentExtension.componentFamilyEquivCoherentVertexTable] using
      atComponent

/-- The common determining predicate is the conjunction of the two separate
graph criteria for any finite selection. -/
theorem determining_iff [Nontrivial K] (S : Finset F.Vertex) :
    FiniteReading.Determining (readAt F K u) S (EdgeCoherent F K S) ↔
      InducedComponent.MeetsEveryFullComponent F
        (fun vertex => vertex ∈ S) ∧
      InducedComponent.RetainsFullConnectivity F
        (fun vertex => vertex ∈ S) := by
  exact and_congr (separates_iff F K u S) (extends_iff F K u S)

/-- A finite raw vertex reading determines each change over the fixed visible
automorphism exactly when the full component type is finite. -/
theorem exists_finite_determining_iff [Nontrivial K] :
    (∃ S : Finset F.Vertex,
      FiniteReading.Determining (readAt F K u) S (EdgeCoherent F K S)) ↔
      Finite (FixedFComponent F) := by
  rw [← PermutationRestriction.hasFiniteDeterminingPreservingRestriction_iff
    (K := K) F u]
  constructor
  · rintro ⟨S, hdetermining⟩
    refine ⟨fun vertex => vertex ∈ S, ?_, ?_, ?_⟩
    · simpa only using S.finite_toSet
    · exact (PermutationRestriction.restrictPreservingChange_injective_iff_meetsEveryFullComponent
        (K := K) F (fun vertex => vertex ∈ S) u).2
          ((determining_iff F K u S).1 hdetermining).1
    · exact (PermutationRestriction.restrictPreservingChange_surjective_iff_retainsFullConnectivity
        (K := K) F (fun vertex => vertex ∈ S) u).2
          ((determining_iff F K u S).1 hdetermining).2
  · rintro ⟨selected, finite, separates, hextends⟩
    classical
    let S : Finset F.Vertex := finite.toFinset
    have hS : (fun vertex => vertex ∈ S) = selected := by
      funext vertex
      simp [S]
    refine ⟨S, (determining_iff F K u S).2 ?_⟩
    rw [hS]
    constructor
    · exact (PermutationRestriction.restrictPreservingChange_injective_iff_meetsEveryFullComponent
        (K := K) F selected u).1 separates
    · exact (PermutationRestriction.restrictPreservingChange_surjective_iff_retainsFullConnectivity
        (K := K) F selected u).1 hextends

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.FinitePermutationReadingCriteria

end FinitePermutationReadingCriteria

end AAT.AG.LocalSemanticReconstruction
