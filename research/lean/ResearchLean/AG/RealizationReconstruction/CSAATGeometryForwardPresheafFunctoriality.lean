import ResearchLean.AG.RealizationReconstruction.CSAATGeometryForwardFunctoriality
import Formal.Util.AssertStandardAxioms

/-!
# Component functoriality for forward polynomial and raw presheaf maps

The forward maps live over object-dependent context categories.  Consequently
their identity law includes the explicit transport induced by identity rebase,
while their composition law compares the direct component with the two
successive components.  This file proves those full component-morphism laws at
every context, first for the complete coordinate-polynomial presheaf and then
for the raw quotient presheaf.

The raw proofs unfold the endpoint conjugation.  Identity cancels the source
endpoint isomorphism with its inverse; composition cancels the intermediate
endpoint inverse with its isomorphism.  No inverse CS morphism, aggregate
functoriality certificate, or selected coordinate subset is an input.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory

universe u

namespace LensAATForwardMorphism

/-- At every lens context, the complete polynomial component of identity is
the identity after the explicit identity-rebase transport. -/
@[simp] theorem equationPolynomialForwardHom_id_app {input : LensFamilyInput.{u}}
    (X : LensRealization input.View input.reference)
    (W : (lensAATGeometryReadingSite input X).category) :
    (lensAATEquationPolynomialForwardHom input (id X)).app (Opposite.op W) ≫
        eqToHom (congrArg
          (fun Q => (equationCoordinatePolynomialPresheaf
            (lensAATGeometryReadingSite input X)).obj (Opposite.op Q))
          (lawContextFunctor_id_obj X W)) =
      𝟙 ((equationCoordinatePolynomialPresheaf
        (lensAATGeometryReadingSite input X)).obj (Opposite.op W)) := by
  apply CategoryTheory.Under.UnderMorphism.ext
  apply CommRingCat.hom_ext
  ext polynomial
  simp [lensAATEquationPolynomialForwardHom, lawCoordinateMap_id]
  rfl

/-- Direct and successive lens polynomial components agree at every context. -/
@[simp] theorem equationPolynomialForwardHom_comp_app
    {input : LensFamilyInput.{u}}
    {X Y Z : LensRealization input.View input.reference}
    (f : LensAATForwardMorphism X Y) (g : LensAATForwardMorphism Y Z)
    (W : (lensAATGeometryReadingSite input X).category) :
    (lensAATEquationPolynomialForwardHom input (comp f g)).app
        (Opposite.op W) =
      (lensAATEquationPolynomialForwardHom input f).app (Opposite.op W) ≫
        (lensAATEquationPolynomialForwardHom input g).app
          (Opposite.op (f.lawContextFunctor.obj W)) := by
  apply CategoryTheory.Under.UnderMorphism.ext
  apply CommRingCat.hom_ext
  ext polynomial
  simp [lensAATEquationPolynomialForwardHom, lawCoordinateMap_comp]
  rfl

/-- At every lens context, raw identity conjugation cancels after the explicit
identity-rebase transport. -/
@[simp] theorem rawForwardHom_id_app {input : LensFamilyInput.{u}}
    (X : LensRealization input.View input.reference)
    (W : (lensAATGeometryReadingSite input X).category) :
    (lensAATGeometryReadingRawForwardHom input (id X)).app (Opposite.op W) ≫
        eqToHom (congrArg
          (fun Q => (lensAATGeometryReadingRawSystem input X).toPresheaf.obj
            (Opposite.op Q))
          (lawContextFunctor_id_obj X W)) =
      𝟙 ((lensAATGeometryReadingRawSystem input X).toPresheaf.obj
        (Opposite.op W)) := by
  apply CategoryTheory.Under.UnderMorphism.ext
  apply CommRingCat.hom_ext
  ext raw
  dsimp [lensAATGeometryReadingRawForwardHom]
  rw [lawContextFunctor_id_obj X W]
  have h := congrArg (fun k => k.right raw)
    ((lensAATGeometryReadingRawPresheafIso input X).hom_inv_id_app
      (Opposite.op W))
  simpa only [CategoryTheory.comp_apply, CategoryTheory.id_apply,
    lensAATEquationPolynomialForwardHom, lawCoordinateMap_id,
    RingHom.id_apply] using h

/-- Direct and successive lens raw components agree at every context; the
intermediate endpoint isomorphism is cancelled explicitly. -/
@[simp] theorem rawForwardHom_comp_app {input : LensFamilyInput.{u}}
    {X Y Z : LensRealization input.View input.reference}
    (f : LensAATForwardMorphism X Y) (g : LensAATForwardMorphism Y Z)
    (W : (lensAATGeometryReadingSite input X).category) :
    (lensAATGeometryReadingRawForwardHom input (comp f g)).app
        (Opposite.op W) =
      (lensAATGeometryReadingRawForwardHom input f).app (Opposite.op W) ≫
        (lensAATGeometryReadingRawForwardHom input g).app
          (Opposite.op (f.lawContextFunctor.obj W)) := by
  apply CategoryTheory.Under.UnderMorphism.ext
  apply CommRingCat.hom_ext
  ext raw
  dsimp [lensAATGeometryReadingRawForwardHom]
  let value :=
    ((lensAATEquationPolynomialForwardHom input f).app
      (Opposite.op W)).right
        (((lensAATGeometryReadingRawPresheafIso input X).hom.app
          (Opposite.op W)).right raw)
  have h := congrArg (fun k => k.right value)
    ((lensAATGeometryReadingRawPresheafIso input Y).inv_hom_id_app
      (Opposite.op (f.lawContextFunctor.obj W)))
  have hc :
      ((lensAATGeometryReadingRawPresheafIso input Y).hom.app
        (Opposite.op (f.lawContextFunctor.obj W))).right
          (((lensAATGeometryReadingRawPresheafIso input Y).inv.app
            (Opposite.op (f.lawContextFunctor.obj W))).right value) = value := by
    simpa only [CategoryTheory.comp_apply, CategoryTheory.id_apply] using h
  dsimp [value] at hc
  rw [hc]
  simp [lensAATEquationPolynomialForwardHom, lawCoordinateMap_comp]
  rfl

end LensAATForwardMorphism

namespace ProtocolAATForwardMorphism

/-- At every protocol context, the complete polynomial component of identity
is the identity after the explicit identity-rebase transport. -/
@[simp] theorem equationPolynomialForwardHom_id_app
    {input : ProtocolFamilyInput.{u}}
    (X : ProtocolRealization input.schema input.observation)
    (W : (protocolAATGeometryReadingSite input X).category) :
    (protocolAATEquationPolynomialForwardHom input (id X)).app (Opposite.op W) ≫
        eqToHom (congrArg
          (fun Q => (equationCoordinatePolynomialPresheaf
            (protocolAATGeometryReadingSite input X)).obj (Opposite.op Q))
          (lawContextFunctor_id_obj X W)) =
      𝟙 ((equationCoordinatePolynomialPresheaf
        (protocolAATGeometryReadingSite input X)).obj (Opposite.op W)) := by
  apply CategoryTheory.Under.UnderMorphism.ext
  apply CommRingCat.hom_ext
  ext polynomial
  simp [protocolAATEquationPolynomialForwardHom, lawCoordinateMap_id]
  rfl

/-- Direct and successive protocol polynomial components agree at every
context. -/
@[simp] theorem equationPolynomialForwardHom_comp_app
    {input : ProtocolFamilyInput.{u}}
    {X Y Z : ProtocolRealization input.schema input.observation}
    (f : ProtocolAATForwardMorphism X Y) (g : ProtocolAATForwardMorphism Y Z)
    (W : (protocolAATGeometryReadingSite input X).category) :
    (protocolAATEquationPolynomialForwardHom input (comp f g)).app
        (Opposite.op W) =
      (protocolAATEquationPolynomialForwardHom input f).app (Opposite.op W) ≫
        (protocolAATEquationPolynomialForwardHom input g).app
          (Opposite.op (f.lawContextFunctor.obj W)) := by
  apply CategoryTheory.Under.UnderMorphism.ext
  apply CommRingCat.hom_ext
  ext polynomial
  simp [protocolAATEquationPolynomialForwardHom, lawCoordinateMap_comp]
  rfl

/-- At every protocol context, raw identity conjugation cancels after the
explicit identity-rebase transport. -/
@[simp] theorem rawForwardHom_id_app {input : ProtocolFamilyInput.{u}}
    (X : ProtocolRealization input.schema input.observation)
    (W : (protocolAATGeometryReadingSite input X).category) :
    (protocolAATGeometryReadingRawForwardHom input (id X)).app (Opposite.op W) ≫
        eqToHom (congrArg
          (fun Q => (protocolAATGeometryReadingRawSystem input X).toPresheaf.obj
            (Opposite.op Q))
          (lawContextFunctor_id_obj X W)) =
      𝟙 ((protocolAATGeometryReadingRawSystem input X).toPresheaf.obj
        (Opposite.op W)) := by
  apply CategoryTheory.Under.UnderMorphism.ext
  apply CommRingCat.hom_ext
  ext raw
  dsimp [protocolAATGeometryReadingRawForwardHom]
  rw [lawContextFunctor_id_obj X W]
  have h := congrArg (fun k => k.right raw)
    ((protocolAATGeometryReadingRawPresheafIso input X).hom_inv_id_app
      (Opposite.op W))
  simpa only [CategoryTheory.comp_apply, CategoryTheory.id_apply,
    protocolAATEquationPolynomialForwardHom, lawCoordinateMap_id,
    RingHom.id_apply] using h

/-- Direct and successive protocol raw components agree at every context; the
intermediate endpoint isomorphism is cancelled explicitly. -/
@[simp] theorem rawForwardHom_comp_app {input : ProtocolFamilyInput.{u}}
    {X Y Z : ProtocolRealization input.schema input.observation}
    (f : ProtocolAATForwardMorphism X Y) (g : ProtocolAATForwardMorphism Y Z)
    (W : (protocolAATGeometryReadingSite input X).category) :
    (protocolAATGeometryReadingRawForwardHom input (comp f g)).app
        (Opposite.op W) =
      (protocolAATGeometryReadingRawForwardHom input f).app (Opposite.op W) ≫
        (protocolAATGeometryReadingRawForwardHom input g).app
          (Opposite.op (f.lawContextFunctor.obj W)) := by
  apply CategoryTheory.Under.UnderMorphism.ext
  apply CommRingCat.hom_ext
  ext raw
  dsimp [protocolAATGeometryReadingRawForwardHom]
  let value :=
    ((protocolAATEquationPolynomialForwardHom input f).app
      (Opposite.op W)).right
        (((protocolAATGeometryReadingRawPresheafIso input X).hom.app
          (Opposite.op W)).right raw)
  have h := congrArg (fun k => k.right value)
    ((protocolAATGeometryReadingRawPresheafIso input Y).inv_hom_id_app
      (Opposite.op (f.lawContextFunctor.obj W)))
  have hc :
      ((protocolAATGeometryReadingRawPresheafIso input Y).hom.app
        (Opposite.op (f.lawContextFunctor.obj W))).right
          (((protocolAATGeometryReadingRawPresheafIso input Y).inv.app
            (Opposite.op (f.lawContextFunctor.obj W))).right value) = value := by
    simpa only [CategoryTheory.comp_apply, CategoryTheory.id_apply] using h
  dsimp [value] at hc
  rw [hc]
  simp [protocolAATEquationPolynomialForwardHom, lawCoordinateMap_comp]
  rfl

end ProtocolAATForwardMorphism

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end AAT.AG.RealizationReconstruction
