import Formal.SHIGURE.Part2.Schemes.QuasiCoherentPullback

/-! # The quasi-coherent fiber on a spectrum -/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Bicategory Opposite TopologicalSpace
open Scheme.Modules

noncomputable section

universe u

variable (R : CommRingCat.{u})

/-- A quasi-coherent module on a spectrum has an actual global tilde presentation. -/
theorem affineQuasiCoherent_iff_essImage (M : (Spec R).Modules) :
    IsQuasiCoherentModule M ↔ (tilde.functor R).essImage M := by
  refine ⟨?_, isQuasiCoherentModule_of_tilde M⟩
  intro coherent
  let h := isAffineOpen_top (Spec R)
  let a := (Scheme.ΓSpecIso R).hom
  have inverse : Spec.map a ≫ h.fromSpec = 𝟙 _ := by
    rw [IsAffineOpen.fromSpec_top, ← Scheme.isoSpec_Spec_hom]
    exact (Scheme.isoSpec (Spec R)).hom_inv_id
  obtain ⟨N, ⟨e⟩⟩ := coherent ⟨⊤, h⟩
  refine ⟨(ModuleCat.extendScalars a.hom).obj N, ⟨?_⟩⟩
  exact ((tildeRestrictIso a).app N).symm ≪≫ (restrictFunctor (Spec.map a)).mapIso e ≪≫
    ((restrictFunctorComp (Spec.map a) h.fromSpec).app M).symm ≪≫
    (restrictFunctorCongr inverse).app M ≪≫ (restrictFunctorId (X := Spec R)).app M

private def affineProperty : ObjectProperty (Spec R).Modules :=
  IsQuasiCoherentModule

private abbrev affineFiber := (affineProperty R).FullSubcategory

/-- The original associated sheaf functor, with its values in the quasi-coherent fiber. -/
def affineTildeFunctor : ModuleCat.{u} R ⥤ affineFiber R :=
  (affineProperty R).lift (tilde.functor R)
    (fun N => isQuasiCoherentModule_of_tilde _ ⟨N, ⟨Iso.refl _⟩⟩)

/-- The associated sheaf functor is fully faithful and reaches every affine quasi-coherent module. -/
instance : (affineTildeFunctor R).IsEquivalence := by
  letI : (tilde.functor R).Full := (tilde.fullyFaithfulFunctor (R := R)).full
  letI : (tilde.functor R).Faithful := (tilde.fullyFaithfulFunctor (R := R)).faithful
  letI : (affineTildeFunctor R).Full := by
    unfold affineTildeFunctor
    infer_instance
  letI : (affineTildeFunctor R).Faithful := by
    unfold affineTildeFunctor
    infer_instance
  letI : (affineTildeFunctor R).EssSurj := ⟨fun M => by
    obtain ⟨N, ⟨e⟩⟩ := (affineQuasiCoherent_iff_essImage R M.obj).1 M.property
    exact ⟨N, ⟨(affineProperty R).fullyFaithfulι.preimageIso
      (X := (affineTildeFunctor R).obj N) (Y := M) e⟩⟩⟩
  exact { }

/-- Modules over the affine coordinate ring are equivalent to the geometric quasi-coherent fiber. -/
def affineTildeEquivalence : ModuleCat.{u} R ≌ affineFiber R :=
  (affineTildeFunctor R).asEquivalence

/-- On spectra, the quasi-coherent pullback in the geometric pseudofunctor
is expressed by the same scalar extension that is used in coefficient descent. -/
def affinePullbackFunctor {R S : CommRingCat.{u}} (f : R ⟶ S) : affineFiber R ⥤ affineFiber S :=
  (quasiCoherentModulesPseudofunctor.map (Spec.map f).op.toLoc).toFunctor

/-- The associated sheaf equivalences compare the actual fiber functors, naturally in module maps. -/
def affineTildePullbackIso {R S : CommRingCat.{u}} (f : R ⟶ S) :
    affineTildeFunctor R ⋙ affinePullbackFunctor f ≅
      ModuleCat.extendScalars f.hom ⋙ affineTildeFunctor S := by
  apply ((affineProperty S).fullyFaithfulι.whiskeringRight _).preimageIso
  exact tildePullbackIso f

end

end SHIGURE.SchemeDescent
