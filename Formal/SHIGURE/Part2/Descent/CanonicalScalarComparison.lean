import Formal.SHIGURE.Part2.Descent.ScalarChangeProjection

/-! # The canonical scalar comparison for a commutative ring square -/

namespace SHIGURE.CoefficientDescent

open CategoryTheory ModuleCat

noncomputable section

universe u

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
  (f : R →+* S) (p q : S →+* T) (h : p.comp f = q.comp f)
  (M : ModuleCat.{u} R)

/-- The two successive scalar extensions agree over the same composite
coefficient homomorphism. -/
def canonicalScalarComparison :
    (extendScalars p).obj ((extendScalars f).obj M) ≅ (extendScalars q).obj ((extendScalars f).obj M) :=
  ((extendScalarsComp f p).app M).symm ≪≫ (extensionAlongCongruence h).app M ≪≫
    (extendScalarsComp f q).app M

/-- On the two successive unit tensors the canonical overlap comparison
keeps the original element in the module slot. -/
theorem canonicalScalarComparison_unit (x : M) :
    (canonicalScalarComparison f p q h M).hom
      ((extendRestrictScalarsAdj p).unit.app ((extendScalars f).obj M)
        ((extendRestrictScalarsAdj f).unit.app M x)) =
    (extendRestrictScalarsAdj q).unit.app ((extendScalars f).obj M)
      ((extendRestrictScalarsAdj f).unit.app M x) := by
  let N := (extendScalars f).obj M
  let y := (extendRestrictScalarsAdj f).unit.app M x
  let a := (extendScalarsComp f p).app M
  let b := (extendScalarsComp f q).app M
  let c := (extensionAlongCongruence h).app M
  let l := (extendRestrictScalarsAdj (p.comp f)).unit.app M x
  let r := (extendRestrictScalarsAdj (q.comp f)).unit.app M x
  have l_eq : a.hom l = (extendRestrictScalarsAdj p).unit.app N y :=
    extendScalarsComp_hom_app_one_tmul f p M x
  have r_eq : b.hom r = (extendRestrictScalarsAdj q).unit.app N y :=
    extendScalarsComp_hom_app_one_tmul f q M x
  have c_eq : c.hom l = r := extensionAlongCongruence_unit h M x
  let L := (extendScalars (p.comp f)).obj M
  have inv_eq : a.inv (a.hom l) = l := congrArg (fun m : L ⟶ L => m l) a.hom_inv_id
  change b.hom (c.hom (a.inv ((extendRestrictScalarsAdj p).unit.app N y))) = _
  rw [← l_eq, inv_eq, c_eq, r_eq]

end

end SHIGURE.CoefficientDescent
