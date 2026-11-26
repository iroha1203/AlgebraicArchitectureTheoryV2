import Formal.SHIGURE.Part2.Schemes.AffineTensorCoefficientCocycle
import Formal.SHIGURE.Part2.Schemes.AffineDescentMapRecovery
import Formal.SHIGURE.Part2.Descent.ModuleEquivalence

/-! # Geometric descent data as ordered tensor descent data

## Implementation notes

For the singleton affine site in Appendix B.3, the inverse of the affine
tilde equivalence gives the coefficient module of the original chart.
This choice gives a functor on all module maps; choosing a coefficient
presentation object by object would require a separate comparison for
identities and composites. The actual double and triple pullbacks give
the transition and cocycle of equation (B.1) in Lemma B.4.
-/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory TensorProduct SHIGURE.CoefficientDescent

noncomputable section

universe u

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- The actual singleton chart and descent transition of Appendix B.3
define the coefficient module and ordered tensor datum of Lemma B.4.
An arbitrary algebra map supplies the two scalar embeddings. -/
def affineCoefficientDatum (D : AffineSingletonDescentData A B) : DescentModule A B := by
  let N := affineDescentCoefficientModule D
  letI : Module A N := Module.compHom _ (algebraMap A B)
  letI : IsScalarTower A B N := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  exact DescentModule.ofDatum (N := N)
    ⟨affineDescentCoefficientOverlap D, affineDescentCoefficientTensorCocycle D⟩

/-- Send the singleton affine descent data of Appendix B.3 to the data
of Lemma B.4, using the actual transitions and all compatible geometric
module maps. The source is the singleton family of the given algebra map. -/
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

/-- The object of the Appendix B.3 comparison reads the chart and its
overlap as the coefficient datum of Lemma B.4. -/
theorem affineGeometryToCoefficients_obj (D : AffineSingletonDescentData A B) :
    affineGeometryToCoefficients.obj D = affineCoefficientDatum D := rfl

/-- The underlying linear map of the coefficient comparison is the map
obtained from the original affine chart in Appendix B.3. -/
theorem affineGeometryToCoefficients_map_hom {D E : AffineSingletonDescentData A B} (f : D ⟶ E) :
    (affineGeometryToCoefficients.map f).hom = (affineDescentCoefficientMap f).hom := rfl

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1000000 in
/-- Every compatible linear map between the coefficient data of two
geometric descent data lifts uniquely to a geometric descent morphism.
The compatibility from Lemma B.4 gives the square on the double overlap
of Appendix B.3, and the pullback property extends it to every test overlap. -/
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
