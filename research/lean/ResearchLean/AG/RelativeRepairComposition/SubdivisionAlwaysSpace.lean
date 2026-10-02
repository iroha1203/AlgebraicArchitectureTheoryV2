import ResearchLean.AG.RelativeRepairComposition.SubdivisionLinearCochains
import ResearchLean.AG.RelativeRepairComposition.SubdivisionSupportedCochains
import ResearchLean.AG.RelativeRepairComposition.OriginalCandidateColumns

/-!
# The independent always source before and after the same actual subdivision

All candidate values remain zero in this source. The old always correction and
the unrestricted full first-factor value give coordinates on every new source
element, with the same actual inverse restoration.

## Implementation notes

The original range construction uses families indexed by the universal closed
region. Reindexing those families into the actual supported cochains connects
the existing source to the earlier full subdivision equivalence. It does not
define the new always source as an image of old corrections.
-/
namespace AAT.AG.RelativeRepairComposition.Subdivision.AlwaysSpace
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
universe uk uG uE uB uD vE vB vD
variable {k : Type uk} [Field k]
variable {K : FiniteTransportPresentation.{uG}}
variable {E : Type uE} {B : Type uB} {D : Type uD}
variable [Category.{vE} E] [Category.{vB} B] [Category.{vD} D]
variable {p : E ⥤ B} {q : B ⥤ D}
variable (T : OriginalTowerPresentation K p q)
variable [∀ v, Module k (T.toTower.localCoefficients.A v)]
variable (P : ClosedRegion K) (candidates : Set (EdgeName (K := K)))

/-- Reindex the independently defined whole always source as the same actual supported cochain. -/
def nativeEquiv : OriginalColumns.alwaysSpace (k := k) T.toTower.localCoefficients P candidates ≃+
    supportedC1 T (fixedEdgesForRange P.edges candidates ∅) where
  toFun h := ⟨fun e => h.1.1 ⟨e,Set.mem_univ e⟩,by
    intro e he
    rcases he with he | ⟨he,_⟩
    · exact h.1.2 ⟨e,Set.mem_univ e⟩ he
    · exact h.2 ⟨e,he⟩⟩
  invFun h := ⟨⟨fun e => h.1 e.1,by
    intro e he
    exact h.2 e.1 (Or.inl he)⟩,by
      intro e
      exact h.2 e.1 (Or.inr ⟨e.2,by simp⟩)⟩
  left_inv h := by
    apply Subtype.ext
    apply Subtype.ext
    funext e
    rfl
  right_inv h := by
    apply Subtype.ext
    funext e
    rfl
  map_add' h j := by
    apply Subtype.ext
    funext e
    rfl

/-- Native reindexing reads every same original complete named always value. -/
theorem nativeEquiv_value
    (h : OriginalColumns.alwaysSpace (k := k) T.toTower.localCoefficients P candidates)
    (e : EdgeName (K := K)) :
    (nativeEquiv T P candidates h).1 e = h.1.1 ⟨e,Set.mem_univ e⟩ := rfl

/-- Inverse reindexing retains each original value in the universal closed region. -/
theorem nativeEquiv_inverse_value
    (h : supportedC1 T (fixedEdgesForRange P.edges candidates ∅))
    (e : EdgeName (K := K)) :
    ((nativeEquiv (k := k) T P candidates).symm h).1.1 ⟨e,Set.mem_univ e⟩ = h.1 e := rfl

variable (chosen : EdgeName (K := K)) (F : Factorization T chosen)
variable (hp : chosen ∉ P.edges) (hc : chosen ∉ candidates)
attribute [local instance] LinearCoefficients.coefficientModules

/-- The independently fixed new always zero conditions are precisely the retained original names. -/
theorem fixed_always_retained :
    fixedEdgesForRange (oldRegion K chosen P hp).edges (oldEdgeSet K chosen candidates) ∅ =
      oldEdgeSet K chosen (fixedEdgesForRange P.edges candidates ∅) := by
  have h := fixed_range_retained chosen P.edges candidates (∅ : Set (EdgeName (K := K)))
  simpa only [old_set_empty] using h.symm

/-- All new always corrections are exactly all old always corrections and every full fresh value. -/
noncomputable def additiveEquiv :
    OriginalColumns.alwaysSpace (k := k) (originalTower T chosen F).toTower.localCoefficients
      (oldRegion K chosen P hp) (oldEdgeSet K chosen candidates) ≃+
    (OriginalColumns.alwaysSpace (k := k) T.toTower.localCoefficients P candidates ×
      (originalTower T chosen F).toTower.localCoefficients.A (.inr ())) :=
  (nativeEquiv (originalTower T chosen F) (oldRegion K chosen P hp)
    (oldEdgeSet K chosen candidates)).trans
    ((AddEquiv.addSubgroupCongr (congrArg (supportedC1 (originalTower T chosen F))
      (fixed_always_retained P candidates chosen hp))).trans
      ((supported1Equiv T chosen F (fixedEdgesForRange P.edges candidates ∅)
        (chosen_not_fixed_range chosen P candidates ∅ hp hc)).trans
        (AddEquiv.prodCongr (nativeEquiv (k := k) T P candidates).symm (AddEquiv.refl _))))

/-- The first always coordinate keeps the actual collapse at every original complete name. -/
theorem additiveEquiv_collapse
    (h : OriginalColumns.alwaysSpace (k := k) (originalTower T chosen F).toTower.localCoefficients
      (oldRegion K chosen P hp) (oldEdgeSet K chosen candidates)) (e : EdgeName (K := K)) :
    (additiveEquiv T P candidates chosen F hp hc h).1.1.1 ⟨e,Set.mem_univ e⟩ =
      collapseCorrection T chosen F (fun f => h.1.1 ⟨f,Set.mem_univ f⟩) e := rfl

/-- The second always coordinate retains the entire actual first-factor value. -/
theorem additiveEquiv_first
    (h : OriginalColumns.alwaysSpace (k := k) (originalTower T chosen F).toTower.localCoefficients
      (oldRegion K chosen P hp) (oldEdgeSet K chosen candidates)) :
    (additiveEquiv T P candidates chosen F hp hc h).2 =
      h.1.1 ⟨firstEdgeName K chosen,Set.mem_univ _⟩ := rfl

variable (hlinear : ∀ {i j : K.Vertex} (e : K.Edge i j) (t : k)
  (x : T.toTower.localCoefficients.A i),
  T.toTower.localCoefficients.edge e (t • x) = t • T.toTower.localCoefficients.edge e x)

/-- The same complete always decomposition is linear for the generated full actual modules. -/
noncomputable def linearEquiv :
    OriginalColumns.alwaysSpace (k := k) (originalTower T chosen F).toTower.localCoefficients
      (oldRegion K chosen P hp) (oldEdgeSet K chosen candidates) ≃ₗ[k]
    (OriginalColumns.alwaysSpace (k := k) T.toTower.localCoefficients P candidates ×
      (originalTower T chosen F).toTower.localCoefficients.A (.inr ())) where
  toAddEquiv := additiveEquiv T P candidates chosen F hp hc
  map_smul' t h := by
    apply Prod.ext
    · apply Subtype.ext
      apply Subtype.ext
      funext e
      change collapseCorrection T chosen F (t • (fun f => h.1.1 ⟨f,Set.mem_univ f⟩)) e.1 =
        t • collapseCorrection T chosen F (fun f => h.1.1 ⟨f,Set.mem_univ f⟩) e.1
      exact congrFun (LinearCochains.collapse_smul T chosen F hlinear t _) e.1
    · rfl

/-- The linear always comparison reads precisely the same actual collapsed correction. -/
theorem linearEquiv_collapse
    (h : OriginalColumns.alwaysSpace (k := k) (originalTower T chosen F).toTower.localCoefficients
      (oldRegion K chosen P hp) (oldEdgeSet K chosen candidates)) (e : EdgeName (K := K)) :
    (linearEquiv T P candidates chosen F hp hc hlinear h).1.1.1 ⟨e,Set.mem_univ e⟩ =
      collapseCorrection T chosen F (fun f => h.1.1 ⟨f,Set.mem_univ f⟩) e := rfl

/-- The inverse restores every named actual correction for every independent full fresh value. -/
theorem linearEquiv_inverse_value
    (h : OriginalColumns.alwaysSpace (k := k) T.toTower.localCoefficients P candidates)
    (r : (originalTower T chosen F).toTower.localCoefficients.A (.inr ()))
    (e : EdgeName (K := presentation K chosen)) :
    ((linearEquiv T P candidates chosen F hp hc hlinear).symm (h,r)).1.1 ⟨e,Set.mem_univ e⟩ =
      expandCorrection T chosen F (fun f => h.1.1 ⟨f,Set.mem_univ f⟩) r e := rfl

end AAT.AG.RelativeRepairComposition.Subdivision.AlwaysSpace
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.Subdivision.AlwaysSpace
