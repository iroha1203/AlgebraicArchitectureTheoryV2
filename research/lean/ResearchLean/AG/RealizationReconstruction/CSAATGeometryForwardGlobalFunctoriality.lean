import ResearchLean.AG.RealizationReconstruction.CSAATGeometryForwardPresheafFunctoriality
import Formal.Util.AssertStandardAxioms

/-!
# Transported global functoriality for forward CS presheaf maps

Each realization has its own context category, so the forward presheaf maps do
not form an ordinary strict functor over one fixed category.  This file states
the honest global unit and compositor laws: the target functors are identified
by explicit reindexing equalities, and the forward natural transformations are
then compared after `eqToHom` transport.

The proofs are generated from the objectwise context equalities and the full
component-morphism laws.  No global-law record is accepted as input.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory

universe u

namespace LensAATForwardMorphism

/-- Identity on the context data between the definitionally matching Law
endpoints of the generated lens identity. -/
noncomputable def lawContextDataIdentityFunctor {input : LensFamilyInput.{u}}
    (X : LensRealization input.View input.reference) :
    CategoryTheory.Functor
      (Site.ContextCategoryObject
        (Site.contextMorphismPreorderCategory
          (lensLawSourceObject (id X).lawHom)))
      (Site.ContextCategoryObject
        (Site.contextMorphismPreorderCategory
          (lensLawTargetObject (id X).lawHom))) where
  obj W := W
  map h := h
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The generated lens identity context functor is globally identity on all
context data and induced thin arrows. -/
@[simp] theorem lawContextFunctor_id {input : LensFamilyInput.{u}}
    (X : LensRealization input.View input.reference) :
    (id X).lawContextFunctor = lawContextDataIdentityFunctor X := by
  refine CategoryTheory.Functor.ext (fun W => lawContextFunctor_id_obj X W) ?_
  intro W V h
  exact lawContextFunctor_id_map X h

/-- The generated lens context functor respects composition globally. -/
@[simp] theorem lawContextFunctor_comp {input : LensFamilyInput.{u}}
    {X Y Z : LensRealization input.View input.reference}
    (f : LensAATForwardMorphism X Y) (g : LensAATForwardMorphism Y Z) :
    (comp f g).lawContextFunctor =
      f.lawContextFunctor ⋙ g.lawContextFunctor := by
  refine CategoryTheory.Functor.ext
    (fun W => lawContextFunctor_comp_obj f g W) ?_
  intro W V h
  exact lawContextFunctor_comp_map f g h

/-- Identity reindexing fixes the complete lens polynomial presheaf. -/
theorem equationPolynomialTarget_id {input : LensFamilyInput.{u}}
    (X : LensRealization input.View input.reference) :
    ((id X).lawContextFunctor).op ⋙
        equationCoordinatePolynomialPresheaf
          (lensAATGeometryReadingSite input X) =
      equationCoordinatePolynomialPresheaf
        (lensAATGeometryReadingSite input X) := by
  refine CategoryTheory.Functor.ext (fun W => ?_) ?_
  · exact congrArg
      (fun Q => (equationCoordinatePolynomialPresheaf
        (lensAATGeometryReadingSite input X)).obj (Opposite.op Q))
      (lawContextFunctor_id_obj X (Opposite.unop W))
  · intros
    rfl

/-- Direct and successive lens reindexing give the same polynomial target
functor. -/
theorem equationPolynomialTarget_comp {input : LensFamilyInput.{u}}
    {X Y Z : LensRealization input.View input.reference}
    (f : LensAATForwardMorphism X Y) (g : LensAATForwardMorphism Y Z) :
    ((comp f g).lawContextFunctor).op ⋙
        equationCoordinatePolynomialPresheaf
          (lensAATGeometryReadingSite input Z) =
      f.lawContextFunctor.op ⋙ g.lawContextFunctor.op ⋙
        equationCoordinatePolynomialPresheaf
          (lensAATGeometryReadingSite input Z) := by
  refine CategoryTheory.Functor.ext (fun W => ?_) ?_
  · exact congrArg
      (fun Q => (equationCoordinatePolynomialPresheaf
        (lensAATGeometryReadingSite input Z)).obj (Opposite.op Q))
      (lawContextFunctor_comp_obj f g (Opposite.unop W))
  · intros
    rfl

/-- The lens polynomial forward transformation satisfies the transported
global identity law. -/
@[simp] theorem equationPolynomialForwardHom_id {input : LensFamilyInput.{u}}
    (X : LensRealization input.View input.reference) :
    lensAATEquationPolynomialForwardHom input (id X) ≫
        eqToHom (equationPolynomialTarget_id X) =
      𝟙 (equationCoordinatePolynomialPresheaf
        (lensAATGeometryReadingSite input X)) := by
  apply NatTrans.ext
  funext W
  simpa using equationPolynomialForwardHom_id_app X (Opposite.unop W)

/-- The lens polynomial forward transformation satisfies the transported
global composition law. -/
@[simp] theorem equationPolynomialForwardHom_comp
    {input : LensFamilyInput.{u}}
    {X Y Z : LensRealization input.View input.reference}
    (f : LensAATForwardMorphism X Y) (g : LensAATForwardMorphism Y Z) :
    lensAATEquationPolynomialForwardHom input (comp f g) ≫
        eqToHom (equationPolynomialTarget_comp f g) =
      lensAATEquationPolynomialForwardHom input f ≫
        Functor.whiskerLeft f.lawContextFunctor.op
          (lensAATEquationPolynomialForwardHom input g) := by
  apply NatTrans.ext
  funext W
  simpa using equationPolynomialForwardHom_comp_app f g (Opposite.unop W)

/-- Identity reindexing fixes the complete lens raw presheaf. -/
theorem rawTarget_id {input : LensFamilyInput.{u}}
    (X : LensRealization input.View input.reference) :
    ((id X).lawContextFunctor).op ⋙
        (lensAATGeometryReadingRawSystem input X).toPresheaf =
      (lensAATGeometryReadingRawSystem input X).toPresheaf := by
  refine CategoryTheory.Functor.ext (fun W => ?_) ?_
  · exact congrArg
      (fun Q => (lensAATGeometryReadingRawSystem input X).toPresheaf.obj
        (Opposite.op Q))
      (lawContextFunctor_id_obj X (Opposite.unop W))
  · intros
    rfl

/-- Direct and successive lens reindexing give the same raw target functor. -/
theorem rawTarget_comp {input : LensFamilyInput.{u}}
    {X Y Z : LensRealization input.View input.reference}
    (f : LensAATForwardMorphism X Y) (g : LensAATForwardMorphism Y Z) :
    ((comp f g).lawContextFunctor).op ⋙
        (lensAATGeometryReadingRawSystem input Z).toPresheaf =
      f.lawContextFunctor.op ⋙ g.lawContextFunctor.op ⋙
        (lensAATGeometryReadingRawSystem input Z).toPresheaf := by
  refine CategoryTheory.Functor.ext (fun W => ?_) ?_
  · exact congrArg
      (fun Q => (lensAATGeometryReadingRawSystem input Z).toPresheaf.obj
        (Opposite.op Q))
      (lawContextFunctor_comp_obj f g (Opposite.unop W))
  · intros
    rfl

/-- The lens raw forward transformation satisfies the transported global
identity law. -/
@[simp] theorem rawForwardHom_id {input : LensFamilyInput.{u}}
    (X : LensRealization input.View input.reference) :
    lensAATGeometryReadingRawForwardHom input (id X) ≫
        eqToHom (rawTarget_id X) =
      𝟙 (lensAATGeometryReadingRawSystem input X).toPresheaf := by
  apply NatTrans.ext
  funext W
  simpa using rawForwardHom_id_app X (Opposite.unop W)

/-- The lens raw forward transformation satisfies the transported global
composition law. -/
@[simp] theorem rawForwardHom_comp {input : LensFamilyInput.{u}}
    {X Y Z : LensRealization input.View input.reference}
    (f : LensAATForwardMorphism X Y) (g : LensAATForwardMorphism Y Z) :
    lensAATGeometryReadingRawForwardHom input (comp f g) ≫
        eqToHom (rawTarget_comp f g) =
      lensAATGeometryReadingRawForwardHom input f ≫
        Functor.whiskerLeft f.lawContextFunctor.op
          (lensAATGeometryReadingRawForwardHom input g) := by
  apply NatTrans.ext
  funext W
  simpa using rawForwardHom_comp_app f g (Opposite.unop W)

end LensAATForwardMorphism

namespace ProtocolAATForwardMorphism

/-- Identity on the context data between the definitionally matching Law
endpoints of the generated protocol identity. -/
noncomputable def lawContextDataIdentityFunctor
    {input : ProtocolFamilyInput.{u}}
    (X : ProtocolRealization input.schema input.observation) :
    CategoryTheory.Functor
      (Site.ContextCategoryObject
        (Site.contextMorphismPreorderCategory
          (protocolLawSourceObject (id X).lawHom)))
      (Site.ContextCategoryObject
        (Site.contextMorphismPreorderCategory
          (protocolLawTargetObject (id X).lawHom))) where
  obj W := W
  map h := h
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The generated protocol identity context functor is globally identity on
all context data and induced thin arrows. -/
@[simp] theorem lawContextFunctor_id {input : ProtocolFamilyInput.{u}}
    (X : ProtocolRealization input.schema input.observation) :
    (id X).lawContextFunctor = lawContextDataIdentityFunctor X := by
  refine CategoryTheory.Functor.ext (fun W => lawContextFunctor_id_obj X W) ?_
  intro W V h
  exact lawContextFunctor_id_map X h

/-- The generated protocol context functor respects composition globally. -/
@[simp] theorem lawContextFunctor_comp {input : ProtocolFamilyInput.{u}}
    {X Y Z : ProtocolRealization input.schema input.observation}
    (f : ProtocolAATForwardMorphism X Y)
    (g : ProtocolAATForwardMorphism Y Z) :
    (comp f g).lawContextFunctor =
      f.lawContextFunctor ⋙ g.lawContextFunctor := by
  refine CategoryTheory.Functor.ext
    (fun W => lawContextFunctor_comp_obj f g W) ?_
  intro W V h
  exact lawContextFunctor_comp_map f g h

/-- Identity reindexing fixes the complete protocol polynomial presheaf. -/
theorem equationPolynomialTarget_id {input : ProtocolFamilyInput.{u}}
    (X : ProtocolRealization input.schema input.observation) :
    ((id X).lawContextFunctor).op ⋙
        equationCoordinatePolynomialPresheaf
          (protocolAATGeometryReadingSite input X) =
      equationCoordinatePolynomialPresheaf
        (protocolAATGeometryReadingSite input X) := by
  refine CategoryTheory.Functor.ext (fun W => ?_) ?_
  · exact congrArg
      (fun Q => (equationCoordinatePolynomialPresheaf
        (protocolAATGeometryReadingSite input X)).obj (Opposite.op Q))
      (lawContextFunctor_id_obj X (Opposite.unop W))
  · intros
    rfl

/-- Direct and successive protocol reindexing give the same polynomial target
functor. -/
theorem equationPolynomialTarget_comp {input : ProtocolFamilyInput.{u}}
    {X Y Z : ProtocolRealization input.schema input.observation}
    (f : ProtocolAATForwardMorphism X Y) (g : ProtocolAATForwardMorphism Y Z) :
    ((comp f g).lawContextFunctor).op ⋙
        equationCoordinatePolynomialPresheaf
          (protocolAATGeometryReadingSite input Z) =
      f.lawContextFunctor.op ⋙ g.lawContextFunctor.op ⋙
        equationCoordinatePolynomialPresheaf
          (protocolAATGeometryReadingSite input Z) := by
  refine CategoryTheory.Functor.ext (fun W => ?_) ?_
  · exact congrArg
      (fun Q => (equationCoordinatePolynomialPresheaf
        (protocolAATGeometryReadingSite input Z)).obj (Opposite.op Q))
      (lawContextFunctor_comp_obj f g (Opposite.unop W))
  · intros
    rfl

/-- The protocol polynomial forward transformation satisfies the transported
global identity law. -/
@[simp] theorem equationPolynomialForwardHom_id
    {input : ProtocolFamilyInput.{u}}
    (X : ProtocolRealization input.schema input.observation) :
    protocolAATEquationPolynomialForwardHom input (id X) ≫
        eqToHom (equationPolynomialTarget_id X) =
      𝟙 (equationCoordinatePolynomialPresheaf
        (protocolAATGeometryReadingSite input X)) := by
  apply NatTrans.ext
  funext W
  simpa using equationPolynomialForwardHom_id_app X (Opposite.unop W)

/-- The protocol polynomial forward transformation satisfies the transported
global composition law. -/
@[simp] theorem equationPolynomialForwardHom_comp
    {input : ProtocolFamilyInput.{u}}
    {X Y Z : ProtocolRealization input.schema input.observation}
    (f : ProtocolAATForwardMorphism X Y) (g : ProtocolAATForwardMorphism Y Z) :
    protocolAATEquationPolynomialForwardHom input (comp f g) ≫
        eqToHom (equationPolynomialTarget_comp f g) =
      protocolAATEquationPolynomialForwardHom input f ≫
        Functor.whiskerLeft f.lawContextFunctor.op
          (protocolAATEquationPolynomialForwardHom input g) := by
  apply NatTrans.ext
  funext W
  simpa using equationPolynomialForwardHom_comp_app f g (Opposite.unop W)

/-- Identity reindexing fixes the complete protocol raw presheaf. -/
theorem rawTarget_id {input : ProtocolFamilyInput.{u}}
    (X : ProtocolRealization input.schema input.observation) :
    ((id X).lawContextFunctor).op ⋙
        (protocolAATGeometryReadingRawSystem input X).toPresheaf =
      (protocolAATGeometryReadingRawSystem input X).toPresheaf := by
  refine CategoryTheory.Functor.ext (fun W => ?_) ?_
  · exact congrArg
      (fun Q => (protocolAATGeometryReadingRawSystem input X).toPresheaf.obj
        (Opposite.op Q))
      (lawContextFunctor_id_obj X (Opposite.unop W))
  · intros
    rfl

/-- Direct and successive protocol reindexing give the same raw target
functor. -/
theorem rawTarget_comp {input : ProtocolFamilyInput.{u}}
    {X Y Z : ProtocolRealization input.schema input.observation}
    (f : ProtocolAATForwardMorphism X Y) (g : ProtocolAATForwardMorphism Y Z) :
    ((comp f g).lawContextFunctor).op ⋙
        (protocolAATGeometryReadingRawSystem input Z).toPresheaf =
      f.lawContextFunctor.op ⋙ g.lawContextFunctor.op ⋙
        (protocolAATGeometryReadingRawSystem input Z).toPresheaf := by
  refine CategoryTheory.Functor.ext (fun W => ?_) ?_
  · exact congrArg
      (fun Q => (protocolAATGeometryReadingRawSystem input Z).toPresheaf.obj
        (Opposite.op Q))
      (lawContextFunctor_comp_obj f g (Opposite.unop W))
  · intros
    rfl

/-- The protocol raw forward transformation satisfies the transported global
identity law. -/
@[simp] theorem rawForwardHom_id {input : ProtocolFamilyInput.{u}}
    (X : ProtocolRealization input.schema input.observation) :
    protocolAATGeometryReadingRawForwardHom input (id X) ≫
        eqToHom (rawTarget_id X) =
      𝟙 (protocolAATGeometryReadingRawSystem input X).toPresheaf := by
  apply NatTrans.ext
  funext W
  simpa using rawForwardHom_id_app X (Opposite.unop W)

/-- The protocol raw forward transformation satisfies the transported global
composition law. -/
@[simp] theorem rawForwardHom_comp {input : ProtocolFamilyInput.{u}}
    {X Y Z : ProtocolRealization input.schema input.observation}
    (f : ProtocolAATForwardMorphism X Y) (g : ProtocolAATForwardMorphism Y Z) :
    protocolAATGeometryReadingRawForwardHom input (comp f g) ≫
        eqToHom (rawTarget_comp f g) =
      protocolAATGeometryReadingRawForwardHom input f ≫
        Functor.whiskerLeft f.lawContextFunctor.op
          (protocolAATGeometryReadingRawForwardHom input g) := by
  apply NatTrans.ext
  funext W
  simpa using rawForwardHom_comp_app f g (Opposite.unop W)

end ProtocolAATForwardMorphism

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end AAT.AG.RealizationReconstruction
