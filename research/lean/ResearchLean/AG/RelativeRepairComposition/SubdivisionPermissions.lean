import ResearchLean.AG.RelativeRepairComposition.SubdivisionEquivalence

/-!
# The same categorical construction for every original permission range

The selected internal edge belongs to neither the fixed part nor the candidate
set. Retention preserves all set operations defining forbidden names. Both new
factors remain always available in every range, and the same actual repair and
label formulas commute with all range inclusions.

## Implementation notes

Retention is applied to the original fixed and candidate name sets before defining each permission range. The same functors and labels are then used for every range. Choosing a new presentation or inverse separately for each range would obscure inclusion compatibility.
-/
namespace AAT.AG.RelativeRepairComposition.Subdivision
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
universe uG uE uB uD vE vB vD
variable {K : FiniteTransportPresentation.{uG}}
variable (chosen : EdgeName (K := K))

/-- Retaining complete nonselected names preserves every difference of original name sets. -/
theorem old_set_diff (S U : Set (EdgeName (K := K))) :
    oldEdgeSet K chosen (S \ U) = oldEdgeSet K chosen S \ oldEdgeSet K chosen U := by
  ext n
  constructor
  · rintro ⟨e,⟨hs,hu⟩,rfl⟩
    refine ⟨⟨e,hs,rfl⟩,?_⟩
    rintro ⟨f,hf,hfe⟩
    exact hu ((retained_injective K chosen hfe) ▸ hf)
  · rintro ⟨⟨e,hs,rfl⟩,hu⟩
    refine ⟨e,⟨hs,?_⟩,rfl⟩
    intro h
    exact hu ⟨e,h,rfl⟩

/-- The retained fixed names are precisely the new fixed part and the same forbidden original candidate names. -/
theorem fixed_range_retained (part candidates allowed : Set (EdgeName (K := K))) :
    oldEdgeSet K chosen (fixedEdgesForRange part candidates allowed) =
      fixedEdgesForRange (oldEdgeSet K chosen part) (oldEdgeSet K chosen candidates)
        (oldEdgeSet K chosen allowed) := by
  rw [fixedEdgesForRange,old_set_union,old_set_diff]
  rfl

/-- The actual first factor is never a retained original name in any fixed or candidate set. -/
theorem first_not_old_set (S : Set (EdgeName (K := K))) :
    firstEdgeName K chosen ∉ oldEdgeSet K chosen S := by
  rintro ⟨e,_,h⟩
  have hn := congrArg (edgeNameEquiv K chosen) h
  change Sum.inl e = Sum.inr false at hn
  cases hn

/-- The actual second factor is never a retained original name in any fixed or candidate set. -/
theorem second_not_old_set (S : Set (EdgeName (K := K))) :
    secondEdgeName K chosen ∉ oldEdgeSet K chosen S := by
  rintro ⟨e,_,h⟩
  have hn := congrArg (edgeNameEquiv K chosen) h
  change Sum.inl e = Sum.inr true at hn
  cases hn

variable {E : Type uE} {B : Type uB} {D : Type uD}
variable [Category.{vE} E] [Category.{vB} B] [Category.{vD} D]
variable {p : E ⥤ B} {q : B ⥤ D}
variable (T : OriginalTowerPresentation K p q) (F : Factorization T chosen)
variable (vertices : Set K.Vertex)

/-- The same actual full-label subdivision equivalence applies to every original permission range. -/
noncomputable def rangeEquivalence (part candidates : Set (EdgeName (K := K)))
    (hpart : chosen ∉ part) (hcandidates : chosen ∉ candidates)
    (allowed : Set (EdgeName (K := K))) :
    RepairGroupoid T vertices (fixedEdgesForRange part candidates allowed) ≌
      RepairGroupoid (originalTower T chosen F) (Sum.inl '' vertices)
        (fixedEdgesForRange (oldEdgeSet K chosen part) (oldEdgeSet K chosen candidates)
          (oldEdgeSet K chosen allowed)) := by
  rw [← fixed_range_retained]
  exact equivalence T chosen F vertices _ (by
    rintro (h | ⟨h,_⟩)
    · exact hpart h
    · exact hcandidates h)

/-- Actual repair collapse commutes with inclusion of every fixed-name set. -/
theorem collapse_supported_inclusion {small large : Set (EdgeName (K := K))}
    (h : small ⊆ large) (hsmall : chosen ∉ small) (hlarge : chosen ∉ large)
    (R : SupportedRepair (originalTower T chosen F) (oldEdgeSet K chosen large)) :
    collapseSupported T chosen F small hsmall
      (repairInclusion (originalTower T chosen F) (old_set_mono K chosen h) R) =
      repairInclusion T h (collapseSupported T chosen F large hlarge R) := Subtype.ext rfl

/-- Every arbitrary-first-value actual restoration commutes with every fixed-name inclusion. -/
theorem expand_supported_inclusion {small large : Set (EdgeName (K := K))}
    (h : small ⊆ large) (R : SupportedRepair T large) (r : Additive (Kernel p q F.middle)) :
    expandSupported T chosen F small (repairInclusion T h R) r =
      repairInclusion (originalTower T chosen F) (old_set_mono K chosen h)
        (expandSupported T chosen F large R r) := Subtype.ext rfl

/-- Full old label restriction commutes with every allowed-label fixed-name inclusion. -/
theorem collapse_label_inclusion {small large : Set (EdgeName (K := K))}
    (h : small ⊆ large) (hsmall : chosen ∉ small) (hlarge : chosen ∉ large)
    (b : supportedC0 (originalTower T chosen F) (Sum.inl '' vertices) (oldEdgeSet K chosen large)) :
    collapseAllowedLabel T chosen F vertices small hsmall
      (gaugeInclusion (originalTower T chosen F) (Sum.inl '' vertices) (old_set_mono K chosen h) b) =
      gaugeInclusion T vertices h (collapseAllowedLabel T chosen F vertices large hlarge b) := Subtype.ext rfl

/-- The complete zero-first-value inverse label section commutes with every fixed-name inclusion. -/
theorem zero_section_inclusion {small large : Set (EdgeName (K := K))}
    (h : small ⊆ large) (b : supportedC0 T vertices large) :
    zeroSectionLabel T chosen F vertices small (gaugeInclusion T vertices h b) =
      gaugeInclusion (originalTower T chosen F) (Sum.inl '' vertices) (old_set_mono K chosen h)
        (zeroSectionLabel T chosen F vertices large b) := Subtype.ext rfl

end AAT.AG.RelativeRepairComposition.Subdivision
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.Subdivision
