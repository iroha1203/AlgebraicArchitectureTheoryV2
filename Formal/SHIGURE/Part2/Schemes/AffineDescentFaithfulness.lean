import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Formal.SHIGURE.Part2.Schemes.AffineDescentAssociated

/-! # Faithfulness of descent on an affine faithfully flat singleton -/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory TensorProduct ModuleCat

noncomputable section

universe u

section Scalar

variable {A B : Type u} [CommRing A] [CommRing B]

/-- Faithfully flat scalar extension detects all maps by evaluation on unit tensors. -/
theorem affineScalarExtension_faithful (a : A →+* B) (ha : a.FaithfullyFlat) :
    (extendScalars.{u,u,u} a).Faithful where
  map_injective {M N} {f g} e := by
    letI : Algebra A B := a.toAlgebra
    letI : Module.FaithfullyFlat A B := ha
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Module.FaithfullyFlat.tensorProduct_mk_injective (A := A) (B := B) N
    let S : ModuleCat.{u} A ⥤ ModuleCat.{u} B := extendScalars a
    let X := S.obj M
    let Y := S.obj N
    let z : X := (extendRestrictScalarsAdj a).unit.app M x
    have eq : S.map f z = S.map g z := congrArg (fun m : X ⟶ Y => m z) e
    exact eq

end Scalar

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [Module.FaithfullyFlat A B]

private abbrev scalarMap : CommRingCat.of A ⟶ CommRingCat.of B := CommRingCat.ofHom (algebraMap A B)

/-- Pullback along the original faithfully flat affine morphism detects equality of
quasi-coherent module maps. -/
theorem affineFaithfullyFlatPullback_faithful : (affinePullbackFunctor (scalarMap (A := A) (B := B))).Faithful := by
  let E := affineTildeEquivalence (CommRingCat.of A)
  let T := affineTildeFunctor (CommRingCat.of B)
  let a := scalarMap (A := A) (B := B)
  let P := affinePullbackFunctor a
  let S : ModuleCat.{u} A ⥤ ModuleCat.{u} B := extendScalars a.hom
  letI : S.Faithful := affineScalarExtension_faithful a.hom
    (RingHom.faithfullyFlat_algebraMap_iff.mpr (inferInstance : Module.FaithfullyFlat A B))
  letI : T.Faithful := (affineTildeEquivalence (CommRingCat.of B)).fullyFaithfulFunctor.faithful
  letI : (E.functor ⋙ P).Faithful := Functor.Faithful.of_iso (affineTildePullbackIso a).symm
  letI : (E.inverse ⋙ (E.functor ⋙ P)).Faithful := inferInstance
  exact Functor.Faithful.of_iso ((Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight E.counitIso P ≪≫ P.leftUnitor)

/-- The comparison to the affine singleton's original descent category is faithful. -/
theorem affineSingletonComparison_faithful :
    (quasiCoherentModulesPseudofunctor.toDescentData (fun _ : Unit => affineScalarMap A B)).Faithful where
  map_injective {M N} {f g} e := by
    let P := affinePullbackFunctor (scalarMap (A := A) (B := B))
    letI : P.Faithful := affineFaithfullyFlatPullback_faithful
    apply P.map_injective
    exact congrArg (fun h :
      (quasiCoherentModulesPseudofunctor.toDescentData (fun _ : Unit => affineScalarMap A B)).obj M ⟶
      (quasiCoherentModulesPseudofunctor.toDescentData (fun _ : Unit => affineScalarMap A B)).obj N => h.hom ()) e

end

end SHIGURE.SchemeDescent
