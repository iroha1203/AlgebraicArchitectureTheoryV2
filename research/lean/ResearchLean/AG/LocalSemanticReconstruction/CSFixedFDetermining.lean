import ResearchLean.AG.LocalSemanticReconstruction.FinitePermutationReadingCriteria
import ResearchLean.AG.LocalSemanticReconstruction.FiniteDeterminingComponents
import ResearchLean.AG.RealizationReconstruction.FixedFFiniteExamples
import Formal.Util.AssertStandardAxioms

/-! Design IV-3: the common fixed-F D determining criterion specializes to
the singleton reference view of a complete-update lens graph and to one
chosen vertex from each component of a finite protocol graph. -/
namespace AAT.AG.LocalSemanticReconstruction
open RealizationReconstruction
namespace CSFixedFDetermining
universe u
variable {V K : Type u}
/-- The reference view alone determines the hidden permutation of each
fixed-visible following change of a complete-update product lens. -/
theorem lens_reference_determining [Nontrivial K]
    (reference : V)
    (visible : FixedFGraphAutomorphism (FixedFFiniteExamples.completeUpdateGraph V)) :
    FiniteReading.Determining
      (FinitePermutationReadingCriteria.readAt
        (FixedFFiniteExamples.completeUpdateGraph V) K visible)
      ({reference} : Finset V)
      (FinitePermutationReadingCriteria.EdgeCoherent
        (FixedFFiniteExamples.completeUpdateGraph V) K {reference}) := by
  apply (FinitePermutationReadingCriteria.determining_iff
    (FixedFFiniteExamples.completeUpdateGraph V) K visible {reference}).2
  constructor
  · intro vertex
    refine ⟨⟨reference, by simp⟩, ?_⟩
    apply Relation.EqvGen.rel
    exact ⟨(reference, vertex), rfl, rfl⟩
  · intro first second _
    have hfirst : first.1 = reference := Finset.mem_singleton.mp first.2
    have hsecond : second.1 = reference := Finset.mem_singleton.mp second.2
    have h : first = second := by
      apply Subtype.ext
      exact hfirst.trans hsecond.symm
    subst second
    exact Relation.EqvGen.refl _

/-- One chosen vertex from each full component of a finite protocol graph. -/
noncomputable def protocolRepresentativeSet
    (F : FixedFDirectedMultigraph) [Finite F.Vertex] : Finset F.Vertex := by
  classical
  letI : Fintype (FixedFComponent F) := Fintype.ofFinite _
  exact Finset.univ.image (InducedComponent.representative F)

/-- The chosen protocol vertices satisfy the same common D determining
predicate for every fixed visible automorphism. -/
theorem protocol_representatives_determining
    (F : FixedFDirectedMultigraph) [Finite F.Vertex] [Nontrivial K]
    (visible : FixedFGraphAutomorphism F) :
    FiniteReading.Determining
      (FinitePermutationReadingCriteria.readAt F K visible)
      (protocolRepresentativeSet F)
      (FinitePermutationReadingCriteria.EdgeCoherent F K
        (protocolRepresentativeSet F)) := by
  apply (FinitePermutationReadingCriteria.determining_iff F K visible
    (protocolRepresentativeSet F)).2
  have hset : (fun vertex => vertex ∈ protocolRepresentativeSet F) =
      InducedComponent.RepresentativeVertex F := by
    funext vertex
    apply propext
    change (vertex ∈ protocolRepresentativeSet F) ↔
      vertex ∈ Set.range (InducedComponent.representative F)
    simp [protocolRepresentativeSet]
  rw [hset]
  exact ⟨InducedComponent.representativeVertex_meetsEveryFullComponent F,
    InducedComponent.representativeVertex_retainsFullConnectivity F⟩


#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.CSFixedFDetermining

end CSFixedFDetermining
end AAT.AG.LocalSemanticReconstruction
