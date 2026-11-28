import Formal.SHIGURE.Part2.Schemes.AffineDescentAssociated
import Formal.SHIGURE.Part2.Descent.ExtensionAlgebraTensor

/-! # The coefficient chart of the canonical affine descent datum -/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory Opposite TensorProduct SHIGURE.CoefficientDescent

noncomputable section

universe u

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- The actual affine restriction of the associated module over the base. -/
def affineCanonicalDatum (M : ModuleCat.{u} A) : AffineSingletonDescentData A B :=
  (quasiCoherentModulesPseudofunctor.toDescentData (fun _ : Unit => affineScalarMap A B)).obj
    ((affineTildeFunctor (CommRingCat.of A)).obj M)

set_option maxHeartbeats 650000 in
/-- The coefficient module of a canonical geometric datum is the actual
extension of scalars, through the associated-module comparison. -/
def affineCanonicalCoefficientIso (M : ModuleCat.{u} A) :
    affineDescentCoefficientModule (affineCanonicalDatum (B := B) M) ≅
      (ModuleCat.extendScalars (algebraMap A B)).obj M :=
  (affineTildeEquivalence (CommRingCat.of B)).fullyFaithfulFunctor.preimageIso
    (affineDescentCoefficientChart (affineCanonicalDatum (B := B) M) ≪≫
      (affineTildePullbackIso (CommRingCat.ofHom (algebraMap A B))).app M)

set_option maxHeartbeats 600000 in
/-- The chart from the canonical coefficient presentation is compatible with
the fixed equivalence between affine modules and their associated sheaves. -/
theorem affineCanonicalCoefficientIso_tilde_hom (M : ModuleCat.{u} A) :
    (affineTildeFunctor (CommRingCat.of B)).map (affineCanonicalCoefficientIso (B := B) M).hom =
    (affineDescentCoefficientChart (affineCanonicalDatum (B := B) M)).hom ≫
      (affineTildePullbackIso (CommRingCat.ofHom (algebraMap A B))).hom.app M :=
  (affineTildeEquivalence (CommRingCat.of B)).fullyFaithfulFunctor.map_preimage _

/-- The associated coefficient chart in the ordinary tensor presentation used
by the faithful-flat descent equivalence. -/
def affineCanonicalTensorIso (M : ModuleCat.{u} A) :
    affineDescentCoefficientModule (affineCanonicalDatum (B := B) M) ≅ ModuleCat.of B (B ⊗[A] M) :=
  affineCanonicalCoefficientIso (B := B) M ≪≫ extendScalarsTensorIso (B := B) M

end

end SHIGURE.SchemeDescent
