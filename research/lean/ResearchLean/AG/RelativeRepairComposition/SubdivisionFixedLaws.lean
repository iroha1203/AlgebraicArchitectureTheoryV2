import ResearchLean.AG.RelativeRepairComposition.SubdivisionThreeLaws
import ResearchLean.AG.RelativeRepairComposition.SubdivisionIncidence

/-! # The same fixed full original reference laws on the retained closed part -/
namespace AAT.AG.RelativeRepairComposition.Subdivision
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
universe uG uE uB uD vE vB vD
variable {K : FiniteTransportPresentation.{uG}}
variable {E : Type uE} {B : Type uB} {D : Type uD}
variable [Category.{vE} E] [Category.{vB} B] [Category.{vD} D]
variable {p : E ⥤ B} {q : B ⥤ D}
variable (T : OriginalTowerPresentation K p q) (chosen : EdgeName (K := K))
variable (F : Factorization T chosen) (P : ClosedRegion K) (hp : chosen ∉ P.edges)

/-- Every fixed original actual reference face Law transfers to its same named full rewritten face. -/
theorem fixed_face_laws
    (h : ∀ f ∈ P.faces, T.toTower.upper.pathLift (K.twoLeft f) ≫ FiberAut.hom (T.comparator f) =
      T.toTower.upper.pathLift (K.twoRight f)) :
    ∀ f ∈ (oldRegion K chosen P hp).faces,
      (originalTower T chosen F).toTower.upper.pathLift ((presentation K chosen).twoLeft f) ≫
        FiberAut.hom ((originalTower T chosen F).comparator f) =
      (originalTower T chosen F).toTower.upper.pathLift ((presentation K chosen).twoRight f) := by
  intro f hf
  change (originalTower T chosen F).toTower.upper.pathLift (substitutePath K chosen (K.twoLeft f)) ≫
    FiberAut.hom (T.comparator f) =
    (originalTower T chosen F).toTower.upper.pathLift (substitutePath K chosen (K.twoRight f))
  rw [originalTower_selected_path,originalTower_selected_path]
  exact h f hf

end AAT.AG.RelativeRepairComposition.Subdivision
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.Subdivision
