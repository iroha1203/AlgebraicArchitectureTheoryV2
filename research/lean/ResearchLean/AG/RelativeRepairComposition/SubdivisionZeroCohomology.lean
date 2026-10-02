import ResearchLean.AG.RelativeRepairComposition.SubdivisionHomotopy

/-!
# Full original zero-cocycles under actual subdivision

The same collapse retains every old vertex label. Its inverse has fresh label
rho1 of the old source label, forced by vanishing of the actual first d0 value.

## Implementation notes

The kernel is taken in the full permitted label group. All zero-cocycles and
both inverse laws use the supported additive decomposition already constructed;
there is no assumption that a repair object exists.
-/
namespace AAT.AG.RelativeRepairComposition.Subdivision
open CategoryTheory Limits TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
universe uG uE uB uD vE vB vD
variable {K : FiniteTransportPresentation.{uG}}
variable {E : Type uE} {B : Type uB} {D : Type uD}
variable [Category.{vE} E] [Category.{vB} B] [Category.{vD} D]
variable {p : E ⥤ B} {q : B ⥤ D}
variable (T : OriginalTowerPresentation K p q) (chosen : EdgeName (K := K))
variable (F : Factorization T chosen)
variable (P : ClosedRegion K) (candidates allowed : Set (EdgeName (K := K)))
variable (hp : chosen ∉ P.edges) (hc : chosen ∉ candidates)

/-- Every original new zero-cocycle has zero entire supplemental displacement. -/
theorem h0_fresh_zero (z : RelativeComplex.H0 (originalTower T chosen F).toTower.localCoefficients
    (oldRegion K chosen P hp) (oldEdgeSet K chosen candidates) (oldEdgeSet K chosen allowed)) :
    (relative0Equiv T chosen F P candidates allowed hp hc z.1).2 = 0 := by
  change (cochain0Equiv T chosen F z.1.1).2 = 0
  rw [← d0_first]
  exact congrFun (congrArg Subtype.val z.2) (firstEdgeName K chosen)

/-- Full actual relative H0 is preserved with every original label and the forced fresh label. -/
noncomputable def relativeH0Equiv :
    RelativeComplex.H0 (originalTower T chosen F).toTower.localCoefficients
      (oldRegion K chosen P hp) (oldEdgeSet K chosen candidates) (oldEdgeSet K chosen allowed) ≃+
    RelativeComplex.H0 T.toTower.localCoefficients P candidates allowed where
  toFun z := ⟨(relative0Equiv T chosen F P candidates allowed hp hc z.1).1,by
    have hz := relative_d0 T chosen F P candidates allowed hp hc z.1
    rw [z.2,map_zero] at hz
    exact (congrArg Prod.fst hz).symm⟩
  invFun z := ⟨(relative0Equiv T chosen F P candidates allowed hp hc).symm (z.1,0),by
    apply (relative1Equiv T chosen F P candidates allowed hp hc).injective
    rw [map_zero,relative_d0,AddEquiv.apply_symm_apply]
    change (RelativeComplex.d0Supported T.toTower.localCoefficients P candidates allowed z.1,0) = 0
    rw [z.2]
    rfl⟩
  left_inv z := by
    apply Subtype.ext
    apply (relative0Equiv T chosen F P candidates allowed hp hc).injective
    rw [AddEquiv.apply_symm_apply]
    exact Prod.ext rfl (h0_fresh_zero T chosen F P candidates allowed hp hc z).symm
  right_inv z := Subtype.ext (congrArg Prod.fst
    ((relative0Equiv T chosen F P candidates allowed hp hc).apply_symm_apply (z.1,0)))
  map_add' z w := Subtype.ext (congrArg Prod.fst
    ((relative0Equiv T chosen F P candidates allowed hp hc).map_add z.1 w.1))

/-- The H0 comparison uses precisely the same actual native degree-zero collapse. -/
theorem relativeH0Equiv_label (z : RelativeComplex.H0 (originalTower T chosen F).toTower.localCoefficients
    (oldRegion K chosen P hp) (oldEdgeSet K chosen candidates) (oldEdgeSet K chosen allowed)) :
    (relativeH0Equiv T chosen F P candidates allowed hp hc z).1 =
      (relativeCollapse T chosen F P candidates allowed hp hc).f 0 z.1 := rfl

/-- Every old zero-cocycle restores all old values and the uniquely forced actual fresh value. -/
theorem relativeH0Equiv_inverse_label (z : RelativeComplex.H0 T.toTower.localCoefficients P candidates allowed) :
    ((relativeH0Equiv T chosen F P candidates allowed hp hc).symm z).1.1 =
      expandVertex T chosen F z.1.1 (rho1AddEquiv T chosen F (z.1.1 chosen.1)) := by
  change expandVertex T chosen F z.1.1 (0+rho1AddEquiv T chosen F (z.1.1 chosen.1)) = _
  rw [zero_add]

end AAT.AG.RelativeRepairComposition.Subdivision
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.Subdivision
