import Mathlib.AlgebraicGeometry.Modules.Tilde

/-! # Affine pullback of associated module sheaves

On a morphism of affine schemes, pushforward on the global sections of
modules is restriction of scalars. The associated module sheaf commutes
with extension of scalars by uniqueness of the left adjoint.
-/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory
open Scheme.Modules

noncomputable section

universe u

variable {R S : CommRingCat.{u}}

/-- On each open of the target spectrum, the pushforward section is the
original section on its inverse image, with scalars restricted along the ring map. -/
def moduleSpecPushforwardPresheafIso (f : R ⟶ S) (N : (Spec S).Modules) :
    ((modulesSpecToSheaf (R := R)).obj ((pushforward (Spec.map f)).obj N)).val ≅
      (TopologicalSpace.Opens.map (Spec.map f).base).op ⋙
        ((modulesSpecToSheaf (R := S)).obj N).val ⋙ ModuleCat.restrictScalars f.hom := by
  let g := Spec.map f
  let q := TopologicalSpace.Opens.map g.base
  let F := ((modulesSpecToSheaf (R := R)).obj ((pushforward g).obj N)).val
  let G := q.op ⋙ ((modulesSpecToSheaf (R := S)).obj N).val ⋙ ModuleCat.restrictScalars f.hom
  change F ≅ G
  refine NatIso.ofComponents (fun U => ?_) (fun a => ?_)
  · let A := F.obj U
    let B := G.obj U
    let V := U.unop
    let incl : (Opposite.op (⊤ : (Spec R).Opens)) ⟶ U := (homOfLE (show V ≤ ⊤ from le_top)).op
    change A ≅ B
    refine LinearEquiv.toModuleIso (X₁ := A) (X₂ := B)
      { AddEquiv.refl _ with map_smul' := fun r x => ?_ }
    let x' : Γ(N, g ⁻¹ᵁ V) := x
    let pulledIncl : Opposite.op (⊤ : (Spec S).Opens) ⟶ Opposite.op (g ⁻¹ᵁ V) := q.op.map incl
    change g.app V ((Spec R).presheaf.map incl ((Scheme.ΓSpecIso R).inv r)) • x' =
      (Spec S).presheaf.map pulledIncl ((Scheme.ΓSpecIso S).inv (f r)) • x'
    have natural := congrArg (fun m : Γ(Spec R, ⊤) ⟶ Γ(Spec S, g ⁻¹ᵁ V) =>
      m ((Scheme.ΓSpecIso R).inv r)) (g.naturality incl)
    have scalar := congrArg (fun m : R ⟶ Γ(Spec S, ⊤) => m r) (Scheme.ΓSpecIso_inv_naturality f)
    exact congrArg (fun t : Γ(Spec S, g ⁻¹ᵁ V) => t • x')
      (natural.trans (congrArg ((Spec S).presheaf.map pulledIncl) scalar.symm))
  · ext a
    rfl

/-- The global sections of a pushforward along an affine morphism use the same
sections, with the scalar action restricted along its original ring map. -/
def moduleSpecΓPushforwardIso (f : R ⟶ S) :
    pushforward (Spec.map f) ⋙ moduleSpecΓFunctor (R := R) ≅
      moduleSpecΓFunctor (R := S) ⋙ ModuleCat.restrictScalars f.hom :=
  NatIso.ofComponents (fun N => (moduleSpecPushforwardPresheafIso f N).app (Opposite.op ⊤))
    (fun _ => by ext x; rfl)

/-- Pullback of an associated module sheaf on spectra is the sheaf associated
to scalar extension along the ring map. -/
def tildePullbackIso (f : R ⟶ S) :
    tilde.functor R ⋙ pullback (Spec.map f) ≅
      ModuleCat.extendScalars f.hom ⋙ tilde.functor S :=
  (((tilde.adjunction (R := R)).comp (pullbackPushforwardAdjunction (Spec.map f))).ofNatIsoRight
    (moduleSpecΓPushforwardIso f)).leftAdjointUniq
    ((ModuleCat.extendRestrictScalarsAdj f.hom).comp (tilde.adjunction (R := S)))

/-- For an affine open immersion the same comparison uses the actual sheaf restriction. -/
def tildeRestrictIso (f : R ⟶ S) [IsOpenImmersion (Spec.map f)] :
    tilde.functor R ⋙ restrictFunctor (Spec.map f) ≅
      ModuleCat.extendScalars f.hom ⋙ tilde.functor S :=
  (tilde.functor R).isoWhiskerLeft (restrictFunctorIsoPullback (Spec.map f)) ≪≫ tildePullbackIso f

end

end SHIGURE.SchemeDescent
