import ResearchLean.AG.RelativeRepairComposition.SubdivisionFiniteBases
import ResearchLean.AG.RelativeRepairComposition.SubdivisionFixedPublicValues
import ResearchLean.AG.RelativeRepairComposition.FiniteNativeCoordinates

/-!
# Complete original public coordinate names through actual subdivision

## Implementation notes

The finite public index is first read as its original nonfixed public edge and
its full target-kernel basis index. The independently generated public names
then compare by the retained-edge bijection. Fixed physical names remain in
the separately defined complete public family, with their prescribed zero
correction; they are never introduced as free finite variables.
-/
namespace AAT.AG.RelativeRepairComposition.FiniteNative
open TransportCoherence AbelianLiftingObstruction
universe uk uG uA uI
variable {k : Type uk} [Field k]
variable {K : FiniteTransportPresentation.{uG}} (M : LocalCoefficients.{uG,uA} K)
variable [∀ v, Module k (M.A v)]
variable (bases : FiniteFamily.Bases (k := k) M.A)
variable {I : Type uI} (U : I → ClosedRegion K) (P : ClosedRegion K)
variable (candidates : Set (EdgeName (K := K))) (j : I)

/-- Every public matrix index retains its complete original edge and complete basis index. -/
def publicIndexEquiv :
    ZIndex M bases (U j) P (ClosedRegion.privateAlwaysEdges U P candidates j) ≃
      Σ e : Subdivision.publicEdges K U P candidates j, Fin (bases.dimension e.1.2.1) where
  toFun z := ⟨⟨z.1.1.1,z.1.1.2.1,z.1.1.2.2,z.2⟩,z.1.2⟩
  invFun z := ⟨⟨⟨z.1.1,z.1.2.1,z.1.2.2.1⟩,z.2⟩,z.1.2.2.2⟩
  left_inv z := by cases z; rfl
  right_inv z := by cases z; rfl

/-- The public matrix index reads exactly its original edge name. -/
theorem publicIndexEquiv_name
    (z : ZIndex M bases (U j) P (ClosedRegion.privateAlwaysEdges U P candidates j)) :
    (publicIndexEquiv M bases U P candidates j z).1.1 = z.1.1.1 := rfl

/-- The public matrix index retains every target-kernel basis component. -/
theorem publicIndexEquiv_basis
    (z : ZIndex M bases (U j) P (ClosedRegion.privateAlwaysEdges U P candidates j)) :
    (publicIndexEquiv M bases U P candidates j z).2 = z.1.2 := rfl

/-- Inverse public indexing restores the exact original name and basis component. -/
theorem publicIndexEquiv_inverse
    (z : Σ e : Subdivision.publicEdges K U P candidates j, Fin (bases.dimension e.1.2.1)) :
    ((publicIndexEquiv M bases U P candidates j).symm z).1.1.1 = z.1.1 := rfl

end AAT.AG.RelativeRepairComposition.FiniteNative

namespace AAT.AG.RelativeRepairComposition.Subdivision.GeneratedPublic
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
universe uk uG uI uE uB uD vE vB vD
variable {k : Type uk} [Field k]
variable {K : FiniteTransportPresentation.{uG}}
variable {E : Type uE} {B : Type uB} {D : Type uD}
variable [Category.{vE} E] [Category.{vB} B] [Category.{vD} D]
variable {p : E ⥤ B} {q : B ⥤ D}
variable (T : OriginalTowerPresentation K p q) (chosen : EdgeName (K := K))
variable (F : Factorization T chosen)
variable [∀ v, Module k (T.toTower.localCoefficients.A v)]
attribute [local instance] LinearCoefficients.coefficientModules
variable (bases : FiniteFamily.Bases (k := k) T.toTower.localCoefficients.A)
variable {I : Type uI} (U : I → ClosedRegion K) (P : ClosedRegion K)
variable (candidates : Set (EdgeName (K := K))) (i : I)
variable (hi : chosen ∈ ClosedRegion.privateAlwaysEdges U P candidates i) (j : I)

/-- Independently generated public indices retain every old name and every full basis component. -/
noncomputable def publicIndexEquiv :
    FiniteNative.ZIndex (originalTower T chosen F).toTower.localCoefficients
      (FiniteBases.expandedBases T chosen F bases) (expandedRegion K chosen (U j))
      (expandedRegion K chosen P)
      (ClosedRegion.privateAlwaysEdges (fun l => expandedRegion K chosen (U l))
        (expandedRegion K chosen P) (oldEdgeSet K chosen candidates) j) ≃
    FiniteNative.ZIndex T.toTower.localCoefficients bases (U j) P
      (ClosedRegion.privateAlwaysEdges U P candidates j) :=
  (FiniteNative.publicIndexEquiv (originalTower T chosen F).toTower.localCoefficients
    (FiniteBases.expandedBases T chosen F bases) (fun l => expandedRegion K chosen (U l))
    (expandedRegion K chosen P) (oldEdgeSet K chosen candidates) j).trans
    ((Equiv.sigmaCongrLeft' (Subdivision.publicNameEquiv K chosen U P candidates i hi j)).trans
      ((Equiv.sigmaCongrRight (fun _ => Equiv.refl _)).trans
        (FiniteNative.publicIndexEquiv T.toTower.localCoefficients bases U P candidates j).symm))

/-- The forward finite index reads the same complete original public edge. -/
theorem publicIndexEquiv_name
    (z : FiniteNative.ZIndex (originalTower T chosen F).toTower.localCoefficients
      (FiniteBases.expandedBases T chosen F bases) (expandedRegion K chosen (U j))
      (expandedRegion K chosen P)
      (ClosedRegion.privateAlwaysEdges (fun l => expandedRegion K chosen (U l))
        (expandedRegion K chosen P) (oldEdgeSet K chosen candidates) j)) :
    (publicIndexEquiv T chosen F bases U P candidates i hi j z).1.1.1 =
      edgeOrigin K chosen z.1.1.1 := rfl

/-- Every original full public basis component is retained by inverse indexing. -/
theorem publicIndexEquiv_inverse_basis
    (z : FiniteNative.ZIndex T.toTower.localCoefficients bases (U j) P
      (ClosedRegion.privateAlwaysEdges U P candidates j)) :
    ((publicIndexEquiv T chosen F bases U P candidates i hi j).symm z).1.2 = z.1.2 := rfl

/-- Every independently generated public coordinate family has full linear inverse restoration. -/
noncomputable def publicCoordinateEquiv :
    (FiniteNative.ZIndex (originalTower T chosen F).toTower.localCoefficients
      (FiniteBases.expandedBases T chosen F bases) (expandedRegion K chosen (U j))
      (expandedRegion K chosen P)
      (ClosedRegion.privateAlwaysEdges (fun l => expandedRegion K chosen (U l))
        (expandedRegion K chosen P) (oldEdgeSet K chosen candidates) j) → k) ≃ₗ[k]
    (FiniteNative.ZIndex T.toTower.localCoefficients bases (U j) P
      (ClosedRegion.privateAlwaysEdges U P candidates j) → k) :=
  LinearEquiv.piCongrLeft' k (fun _ => k) (publicIndexEquiv T chosen F bases U P candidates i hi j)

/-- Public coordinate comparison reads the complete retained index without altering its scalar. -/
theorem publicCoordinateEquiv_value
    (z : FiniteNative.ZIndex (originalTower T chosen F).toTower.localCoefficients
      (FiniteBases.expandedBases T chosen F bases) (expandedRegion K chosen (U j))
      (expandedRegion K chosen P)
      (ClosedRegion.privateAlwaysEdges (fun l => expandedRegion K chosen (U l))
        (expandedRegion K chosen P) (oldEdgeSet K chosen candidates) j) → k)
    (e : FiniteNative.ZIndex T.toTower.localCoefficients bases (U j) P
      (ClosedRegion.privateAlwaysEdges U P candidates j)) :
    publicCoordinateEquiv T chosen F bases U P candidates i hi j z e =
      z ((publicIndexEquiv T chosen F bases U P candidates i hi j).symm e) := rfl

/-- Restoring every arbitrary public family recovers each full original basis value. -/
theorem publicCoordinateEquiv_inverse_value
    (z : FiniteNative.ZIndex T.toTower.localCoefficients bases (U j) P
      (ClosedRegion.privateAlwaysEdges U P candidates j) → k)
    (e : FiniteNative.ZIndex T.toTower.localCoefficients bases (U j) P
      (ClosedRegion.privateAlwaysEdges U P candidates j)) :
    (publicCoordinateEquiv T chosen F bases U P candidates i hi j).symm z
      ((publicIndexEquiv T chosen F bases U P candidates i hi j).symm e) = z e := by
  exact congrFun ((publicCoordinateEquiv T chosen F bases U P candidates i hi j).apply_symm_apply z) e

end AAT.AG.RelativeRepairComposition.Subdivision.GeneratedPublic
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.FiniteNative
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.Subdivision.GeneratedPublic
