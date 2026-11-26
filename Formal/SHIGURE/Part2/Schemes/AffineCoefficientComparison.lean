import Formal.SHIGURE.Part2.Schemes.AffineDescentOverlaps
import Formal.SHIGURE.Part2.Schemes.AffineQuasiCoherentFiber
import Formal.SHIGURE.Part2.Descent.ScalarOverlapMaps

/-! # The coefficient comparison of an affine descent datum -/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory Opposite TensorProduct
open SHIGURE.CoefficientDescent

noncomputable section

universe u

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

local notation "B₂" => B ⊗[A] B

private abbrev overlapMap (i : Fin 2) : CommRingCat.of B ⟶ CommRingCat.of B₂ :=
  CommRingCat.ofHom (affineDoubleEmbedding A B i).toRingHom

/-- The representing coefficient module of the quasi-coherent chart. -/
def affineDescentCoefficientModule (data : AffineSingletonDescentData A B) : ModuleCat.{u} B :=
  (affineTildeEquivalence (CommRingCat.of B)).inverse.obj (data.obj ())

/-- The actual associated sheaf of the coefficient module is the original chart. -/
def affineDescentCoefficientChart (data : AffineSingletonDescentData A B) :=
  (affineTildeEquivalence (CommRingCat.of B)).counitIso.app (data.obj ())

set_option maxHeartbeats 700000 in
/-- On the double tensor spectrum the geometric overlap isomorphism is the
associated sheaf of an isomorphism between the two scalar extensions. -/
def affineDescentScalarExtensionIso (data : AffineSingletonDescentData A B) :
    (ModuleCat.extendScalars (overlapMap (A := A) (B := B) 0).hom).obj (affineDescentCoefficientModule data) ≅
      (ModuleCat.extendScalars (overlapMap (A := A) (B := B) 1).hom).obj (affineDescentCoefficientModule data) := by
  let M := affineDescentCoefficientModule data
  let e := affineDescentCoefficientChart data
  let p := affinePullbackFunctor (overlapMap (A := A) (B := B) 0)
  let q := affinePullbackFunctor (overlapMap (A := A) (B := B) 1)
  let c := (affineTildePullbackIso (overlapMap (A := A) (B := B) 0)).app M
  let d := (affineTildePullbackIso (overlapMap (A := A) (B := B) 1)).app M
  exact (affineTildeEquivalence (CommRingCat.of B₂)).fullyFaithfulFunctor.preimageIso
    (c.symm ≪≫ p.mapIso e ≪≫ affineDoubleTransition A B data ≪≫ (q.mapIso e).symm ≪≫ d)

set_option maxHeartbeats 700000 in
/-- The same scalar extension comparison in the ordered overlap modules of
the coefficient descent theorem. -/
def affineDescentCoefficientOverlap (data : AffineSingletonDescentData A B) :
    let M := affineDescentCoefficientModule data
    letI : Module A M := Module.compHom _ (algebraMap A B)
    letI : IsScalarTower A B M := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
    OverlapIso A B M := by
  let M := affineDescentCoefficientModule data
  letI : Module A M := Module.compHom _ (algebraMap A B)
  letI : IsScalarTower A B M := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  exact scalarOverlapIso (A := A) (B := B) (affineDescentScalarExtensionIso data)

end

end SHIGURE.SchemeDescent
