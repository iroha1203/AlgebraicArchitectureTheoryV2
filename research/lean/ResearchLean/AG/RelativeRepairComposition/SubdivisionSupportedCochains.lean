import ResearchLean.AG.RelativeRepairComposition.SubdivisionCochainDecomposition
import ResearchLean.AG.RelativeRepairComposition.SubdivisionSupportedLabels
import ResearchLean.AG.RelativeRepairComposition.SubdivisionPermissions
import ResearchLean.AG.RelativeRepairComposition.RelativeComplex

/-!
# Full supported additive subdivision coordinates

Every old permission range is retained before taking the supported subgroups.
The fresh coordinate is the entire kernel at the new object in both degrees.

## Implementation notes

The subgroup comparisons use the fixed-name and vertex-label APIs of the same
actual subdivision. Degree zero uses the fresh displacement, so its differential
is identity on the supplemental kernel. Neither factor is fixed by a range.
-/
namespace AAT.AG.RelativeRepairComposition.Subdivision
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
universe uG uE uB uD vE vB vD
variable {K : FiniteTransportPresentation.{uG}}
variable {E : Type uE} {B : Type uB} {D : Type uD}
variable [Category.{vE} E] [Category.{vB} B] [Category.{vD} D]
variable {p : E ⥤ B} {q : B ⥤ D}
variable (T : OriginalTowerPresentation K p q) (chosen : EdgeName (K := K))
variable (F : Factorization T chosen)
variable (vertices : Set K.Vertex) (fixed : Set (EdgeName (K := K)))
variable (hchosen : chosen ∉ fixed)

/-- Supported degree one retains the actual old collapse and every first-factor value. -/
noncomputable def supported1Equiv :
    supportedC1 (originalTower T chosen F) (oldEdgeSet K chosen fixed) ≃+
      (supportedC1 T fixed × (originalTower T chosen F).toTower.localCoefficients.A (.inr ())) where
  toFun h := ⟨⟨collapseCorrection T chosen F h.1, by
    intro e he
    have hn : e ≠ chosen := fun h => hchosen (h ▸ he)
    rw [collapseCorrection_old T chosen F _ e hn]
    exact h.2 _ ⟨⟨e,hn⟩,he,rfl⟩⟩,h.1 (firstEdgeName K chosen)⟩
  invFun h := ⟨expandCorrection T chosen F h.1.1 h.2, by
    rintro _ ⟨⟨e,hn⟩,he,rfl⟩
    change expandCorrection T chosen F h.1.1 h.2 (oldEdgeName K chosen e hn) = 0
    rw [expandCorrection_old]
    exact h.1.2 e he⟩
  left_inv h := Subtype.ext (expand_collapse T chosen F h.1)
  right_inv h := Prod.ext (Subtype.ext (collapse_expand T chosen F h.1.1 h.2))
    (expandCorrection_first T chosen F h.1.1 h.2)
  map_add' h k := Prod.ext (Subtype.ext (collapseCorrection_add T chosen F h.1 k.1)) rfl

/-- Supported degree zero retains the old allowed label and its unrestricted fresh displacement. -/
noncomputable def supported0Equiv :
    supportedC0 (originalTower T chosen F) (Sum.inl '' vertices) (oldEdgeSet K chosen fixed) ≃+
      (supportedC0 T vertices fixed × (originalTower T chosen F).toTower.localCoefficients.A (.inr ())) where
  toFun b := ⟨collapseAllowedLabel T chosen F vertices fixed hchosen b,
    (cochain0Equiv T chosen F b.1).2⟩
  invFun b := expandAllowedLabel T chosen F vertices fixed b.1
    (b.2 + rho1AddEquiv T chosen F (b.1.1 chosen.1))
  left_inv b := Subtype.ext ((cochain0Equiv T chosen F).left_inv b.1)
  right_inv b := Prod.ext (collapse_expand_allowed T chosen F vertices fixed hchosen _ _) (by
    change (b.2 + rho1AddEquiv T chosen F (b.1.1 chosen.1)) -
      rho1AddEquiv T chosen F (b.1.1 chosen.1) = b.2
    exact add_sub_cancel_right _ _)
  map_add' b c := by
    apply Prod.ext
    · exact map_add _ _ _
    · change (cochain0Equiv T chosen F (b.1+c.1)).2 =
        (cochain0Equiv T chosen F b.1).2 + (cochain0Equiv T chosen F c.1).2
      exact congrArg (fun z : C0 T.toTower.localCoefficients ×
        (originalTower T chosen F).toTower.localCoefficients.A (.inr ()) => z.2)
        ((cochain0Equiv T chosen F).map_add b.1 c.1)

variable (P : ClosedRegion K) (candidates allowed : Set (EdgeName (K := K)))
variable (hp : chosen ∉ P.edges) (hc : chosen ∉ candidates)

include hp hc in
/-- The selected edge belongs to no fixed-name set of an original permission range. -/
theorem chosen_not_fixed_range : chosen ∉ fixedEdgesForRange P.edges candidates allowed := by
  rintro (h | ⟨h,_⟩)
  · exact hp h
  · exact hc h

omit hp hc in
/-- Retention identifies the actual supported new edge group with the new relative range group. -/
theorem retained_supported1_eq (hp : chosen ∉ P.edges) :
    supportedC1 (originalTower T chosen F)
      (oldEdgeSet K chosen (fixedEdgesForRange P.edges candidates allowed)) =
    RelativeComplex.C1Group (originalTower T chosen F).toTower.localCoefficients
      (oldRegion K chosen P hp) (oldEdgeSet K chosen candidates) (oldEdgeSet K chosen allowed) := by
  rw [fixed_range_retained]
  rfl

omit hp hc in
/-- Retention identifies all actual allowed new labels with the new relative range group. -/
theorem retained_supported0_eq (hp : chosen ∉ P.edges) :
    supportedC0 (originalTower T chosen F) (Sum.inl '' P.vertices)
      (oldEdgeSet K chosen (fixedEdgesForRange P.edges candidates allowed)) =
    RelativeComplex.C0Group (originalTower T chosen F).toTower.localCoefficients
      (oldRegion K chosen P hp) (oldEdgeSet K chosen candidates) (oldEdgeSet K chosen allowed) := by
  rw [fixed_range_retained]
  exact ActualRelative.supportedC0_eq (originalTower T chosen F) (oldRegion K chosen P hp)
    (oldEdgeSet K chosen candidates) (oldEdgeSet K chosen allowed)

/-- The same full additive decomposition in supported relative degree one, for every range. -/
noncomputable def relative1Equiv :
    RelativeComplex.C1Group (originalTower T chosen F).toTower.localCoefficients
      (oldRegion K chosen P hp) (oldEdgeSet K chosen candidates) (oldEdgeSet K chosen allowed) ≃+
    (RelativeComplex.C1Group T.toTower.localCoefficients P candidates allowed ×
      (originalTower T chosen F).toTower.localCoefficients.A (.inr ())) :=
  (AddEquiv.addSubgroupCongr (retained_supported1_eq T chosen F P candidates allowed hp).symm).trans
    ((supported1Equiv T chosen F _ (chosen_not_fixed_range chosen P candidates allowed hp hc)).trans
      (AddEquiv.prodCongr (AddEquiv.addSubgroupCongr (ActualRelative.supportedC1_eq T P candidates allowed))
        (AddEquiv.refl _)))

/-- The same full additive decomposition in allowed relative degree zero, for every range. -/
noncomputable def relative0Equiv :
    RelativeComplex.C0Group (originalTower T chosen F).toTower.localCoefficients
      (oldRegion K chosen P hp) (oldEdgeSet K chosen candidates) (oldEdgeSet K chosen allowed) ≃+
    (RelativeComplex.C0Group T.toTower.localCoefficients P candidates allowed ×
      (originalTower T chosen F).toTower.localCoefficients.A (.inr ())) :=
  (AddEquiv.addSubgroupCongr (retained_supported0_eq T chosen F P candidates allowed hp).symm).trans
    ((supported0Equiv T chosen F P.vertices _ (chosen_not_fixed_range chosen P candidates allowed hp hc)).trans
      (AddEquiv.prodCongr (AddEquiv.addSubgroupCongr (ActualRelative.supportedC0_eq T P candidates allowed))
        (AddEquiv.refl _)))

/-- Relative degree-zero coordinates retain exactly the old vertex label and full fresh displacement. -/
theorem relative0Equiv_values (b : RelativeComplex.C0Group (originalTower T chosen F).toTower.localCoefficients
    (oldRegion K chosen P hp) (oldEdgeSet K chosen candidates) (oldEdgeSet K chosen allowed)) :
    ((relative0Equiv T chosen F P candidates allowed hp hc b).1.1,
      (relative0Equiv T chosen F P candidates allowed hp hc b).2) =
    cochain0Equiv T chosen F b.1 := rfl

/-- Relative degree-one coordinates retain the same actual collapse and full first-factor value. -/
theorem relative1Equiv_values (h : RelativeComplex.C1Group (originalTower T chosen F).toTower.localCoefficients
    (oldRegion K chosen P hp) (oldEdgeSet K chosen candidates) (oldEdgeSet K chosen allowed)) :
    ((relative1Equiv T chosen F P candidates allowed hp hc h).1.1,
      (relative1Equiv T chosen F P candidates allowed hp hc h).2) =
    cochain1Equiv T chosen F h.1 := rfl

/-- The original supported d0 is old supported d0 paired with identity on the complete fresh kernel. -/
theorem relative_d0 (b : RelativeComplex.C0Group (originalTower T chosen F).toTower.localCoefficients
    (oldRegion K chosen P hp) (oldEdgeSet K chosen candidates) (oldEdgeSet K chosen allowed)) :
    relative1Equiv T chosen F P candidates allowed hp hc
      (RelativeComplex.d0Supported (originalTower T chosen F).toTower.localCoefficients
        (oldRegion K chosen P hp) (oldEdgeSet K chosen candidates) (oldEdgeSet K chosen allowed) b) =
    (RelativeComplex.d0Supported T.toTower.localCoefficients P candidates allowed
      (relative0Equiv T chosen F P candidates allowed hp hc b).1,
      (relative0Equiv T chosen F P candidates allowed hp hc b).2) :=
  Prod.ext (Subtype.ext (collapse_d0 T chosen F b.1)) (d0_first T chosen F b.1)

/-- The original supported face differential keeps the old relative value and forgets only the free factor. -/
theorem relative_d1 (h : RelativeComplex.C1Group (originalTower T chosen F).toTower.localCoefficients
    (oldRegion K chosen P hp) (oldEdgeSet K chosen candidates) (oldEdgeSet K chosen allowed)) :
    RelativeComplex.d1Supported (originalTower T chosen F).toTower.localCoefficients
      (oldRegion K chosen P hp) (oldEdgeSet K chosen candidates) (oldEdgeSet K chosen allowed) h =
    RelativeComplex.d1Supported T.toTower.localCoefficients P candidates allowed
      (relative1Equiv T chosen F P candidates allowed hp hc h).1 :=
  Subtype.ext (d1_collapse T chosen F h.1)

omit hc candidates allowed in
/-- The original relative third differential keeps both complete authored routes under the same identity on cells. -/
theorem relative_d2 (c : RelativeComplex.relativeC2 (originalTower T chosen F).toTower.localCoefficients
    (oldRegion K chosen P hp)) :
    RelativeComplex.d2Relative (originalTower T chosen F).toTower.localCoefficients
      (oldRegion K chosen P hp) c = RelativeComplex.d2Relative T.toTower.localCoefficients P c :=
  Subtype.ext (d2_substitute T chosen F c.1)

end AAT.AG.RelativeRepairComposition.Subdivision
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.Subdivision
