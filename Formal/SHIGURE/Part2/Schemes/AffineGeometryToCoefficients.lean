import Formal.SHIGURE.Part2.Schemes.AffineTensorCoefficientCocycle
import Formal.SHIGURE.Part2.Schemes.AffineDescentMapRecovery
import Formal.SHIGURE.Part2.Descent.ModuleEquivalence

/-! # Geometric descent data as ordered tensor descent data -/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory TensorProduct SHIGURE.CoefficientDescent

noncomputable section

universe u

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- The actual affine charts and overlap define a coefficient descent datum. -/
def affineCoefficientDatum (D : AffineSingletonDescentData A B) : DescentModule A B := by
  let N := affineDescentCoefficientModule D
  letI : Module A N := Module.compHom _ (algebraMap A B)
  letI : IsScalarTower A B N := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  exact DescentModule.ofDatum (N := N)
    ⟨affineDescentCoefficientOverlap D, affineDescentCoefficientTensorCocycle D⟩

/-- Read the full ordered tensor descent datum from an affine geometric datum,
including the compatible linear map of every geometric descent morphism. -/
def affineGeometryToCoefficients : AffineSingletonDescentData A B ⥤ DescentModule A B where
  obj := affineCoefficientDatum
  map m := ⟨(affineDescentCoefficientMap m).hom, affineDescentCoefficientOverlap_preserves m⟩
  map_id D := by
    apply DescentModule.Hom.ext
    let E := (affineTildeEquivalence (CommRingCat.of B)).inverse
    exact congrArg ModuleCat.Hom.hom (E.map_id (D.obj ()))
  map_comp m n := by
    apply DescentModule.Hom.ext
    let E := (affineTildeEquivalence (CommRingCat.of B)).inverse
    exact congrArg ModuleCat.Hom.hom (E.map_comp (m.hom ()) (n.hom ()))

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1000000 in
/-- Every compatible coefficient map is induced by a unique geometric map. -/
def affineGeometryToCoefficientsFullyFaithful :
    (affineGeometryToCoefficients (A := A) (B := B)).FullyFaithful where
  preimage {D E} f := by
    let h : affineDescentCoefficientModule D ⟶ affineDescentCoefficientModule E :=
      ModuleCat.ofHom f.hom
    let M := affineDescentCoefficientModule D
    let N := affineDescentCoefficientModule E
    letI : Module A M := Module.compHom _ (algebraMap A B)
    letI : Module A N := Module.compHom _ (algebraMap A B)
    letI : IsScalarTower A B M := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
    letI : IsScalarTower A B N := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
    refine affineDescentMapOfScalar h (scalarOverlapIso_reflect_comm (A := A)
      (affineDescentScalarExtensionIso D) (affineDescentScalarExtensionIso E) h ?_)
    intro x
    simpa only [LinearMap.rTensor_tmul, LinearMap.restrictScalars_apply] using
      f.compatible (x ⊗ₜ[A] (1 : B))
  map_preimage f := by
    apply DescentModule.Hom.ext
    exact congrArg ModuleCat.Hom.hom (affineDescentCoefficientMap_ofScalar _ _)
  preimage_map f := by
    apply affineDescentCoefficientMap_injective
    exact affineDescentCoefficientMap_ofScalar _ _

end

end SHIGURE.SchemeDescent
