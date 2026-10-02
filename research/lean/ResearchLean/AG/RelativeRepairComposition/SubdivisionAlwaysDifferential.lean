import ResearchLean.AG.RelativeRepairComposition.SubdivisionAlwaysSpace
import ResearchLean.AG.RelativeRepairComposition.SubdivisionCoefficientPaths

/-!
# The actual always differential under full subdivision coordinates

Both sources and their face values are independently defined by their original
presentations. The same actual correction collapse identifies their complete
always differential images, with restoration for every full fresh value.
-/
namespace AAT.AG.RelativeRepairComposition.Subdivision.AlwaysDifferential
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

variable (chosen : EdgeName (K := K)) (F : Factorization T chosen)
variable (hp : chosen ∉ P.edges) (hc : chosen ∉ candidates)
attribute [local instance] LinearCoefficients.coefficientModules
variable (hlinear : ∀ {i j : K.Vertex} (e : K.Edge i j) (t : k)
  (x : T.toTower.localCoefficients.A i),
  T.toTower.localCoefficients.edge e (t • x) = t • T.toTower.localCoefficients.edge e x)
local notation "M" => T.toTower.localCoefficients
local notation "newP" => oldRegion K chosen P hp
local notation "newCandidates" => oldEdgeSet K chosen candidates
local notation "newLinear" => LinearCoefficients.edge_linear T chosen F hlinear

/-- The original complete face family and all fixed face conditions are literally retained. -/
noncomputable def faceLinearEquiv :
    RelativeCover.C2 (originalTower T chosen F).toTower.localCoefficients ClosedRegion.all newP ≃ₗ[k]
      RelativeCover.C2 M ClosedRegion.all P := LinearEquiv.refl k _

/-- Every full original face coordinate is the same value under the comparison. -/
theorem faceLinearEquiv_value (c : RelativeCover.C2 (originalTower T chosen F).toTower.localCoefficients ClosedRegion.all newP)
    (f : K.TwoCell) :
    (faceLinearEquiv (k := k) T P chosen F hp c).1 ⟨f,Set.mem_univ f⟩ =
      c.1 ⟨f,Set.mem_univ f⟩ := rfl

/-- The independently generated full always differential commutes with actual collapse. -/
theorem D_collapse (h : OriginalColumns.alwaysSpace (k := k) (originalTower T chosen F).toTower.localCoefficients newP newCandidates) :
    faceLinearEquiv (k := k) T P chosen F hp
      (OriginalColumns.D (originalTower T chosen F).toTower.localCoefficients newP newCandidates newLinear h) =
      OriginalColumns.D M P candidates hlinear
        (AlwaysSpace.linearEquiv T P candidates chosen F hp hc hlinear h).1 := by
  classical
  apply Subtype.ext
  funext f
  rw [faceLinearEquiv_value,OriginalColumns.D_value,OriginalColumns.D_value]
  have hd := congrFun (d1_collapse T chosen F (fun e => h.1.1 ⟨e,Set.mem_univ e⟩)) f.1
  have he : (fun e => (AlwaysSpace.linearEquiv T P candidates chosen F hp hc hlinear h).1.1.1
      ⟨e,Set.mem_univ e⟩) = collapseCorrection T chosen F (fun e => h.1.1 ⟨e,Set.mem_univ e⟩) := by
    funext e
    exact AlwaysSpace.linearEquiv_collapse T P candidates chosen F hp hc hlinear h e
  rw [he]
  exact hd

/-- Every old always value restores the same differential for every independent full fresh value. -/
theorem D_restore (h : OriginalColumns.alwaysSpace (k := k) M P candidates)
    (r : (originalTower T chosen F).toTower.localCoefficients.A (.inr ())) :
    faceLinearEquiv (k := k) T P chosen F hp
      (OriginalColumns.D (originalTower T chosen F).toTower.localCoefficients newP newCandidates newLinear
        ((AlwaysSpace.linearEquiv T P candidates chosen F hp hc hlinear).symm (h,r))) =
      OriginalColumns.D M P candidates hlinear h := by
  classical
  rw [D_collapse T P candidates chosen F hp hc hlinear,LinearEquiv.apply_symm_apply]

include hc in
/-- The two independent full always images are equal in their unchanged complete face space. -/
theorem range_D :
    LinearMap.range (OriginalColumns.D (originalTower T chosen F).toTower.localCoefficients newP newCandidates newLinear) =
      LinearMap.range (OriginalColumns.D M P candidates hlinear) := by
  classical
  apply le_antisymm
  · rintro _ ⟨h,rfl⟩
    exact ⟨(AlwaysSpace.linearEquiv T P candidates chosen F hp hc hlinear h).1,
      (D_collapse T P candidates chosen F hp hc hlinear h).symm⟩
  · rintro _ ⟨h,rfl⟩
    exact ⟨(AlwaysSpace.linearEquiv T P candidates chosen F hp hc hlinear).symm (h,0),
      D_restore T P candidates chosen F hp hc hlinear h 0⟩

end AAT.AG.RelativeRepairComposition.Subdivision.AlwaysDifferential
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.Subdivision.AlwaysDifferential
