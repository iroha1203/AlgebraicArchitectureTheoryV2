import ResearchLean.AG.RealizationReconstruction.CSAATGeometryForwardEquations
import Formal.Util.AssertStandardAxioms

/-!
# Forward raw-presheaf maps for the concrete CS readings

The Cycle 134 one-way equation action supplies a coordinate-ring homomorphism
on every context.  This file lifts that homomorphism to the lifted-integer
under-category, proves naturality on every selected restriction, and conjugates
it by the Cycle 133 raw/polynomial presheaf isomorphisms.  The result is an
actual natural transformation between the raw quotient presheaves.

No inverse coordinate map, equation-index equivalence, context equivalence,
coverage certificate, or completed geometry morphism is used.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory

universe u

/-! ## Polynomial presheaf maps -/

/-- The lens Law coordinate homomorphism as a natural transformation of the
full coordinate-polynomial presheaves. -/
noncomputable def lensAATEquationPolynomialForwardHom
    (input : LensFamilyInput.{u})
    {X Y : LensRealization input.View input.reference}
    (f : LensAATForwardMorphism X Y) :
    equationCoordinatePolynomialPresheaf
        (lensAATGeometryReadingSite input X) ⟶
      (f.lawContextFunctor).op ⋙
        equationCoordinatePolynomialPresheaf
          (lensAATGeometryReadingSite input Y) where
  app W := CategoryTheory.Under.homMk
    (CommRingCat.ofHom f.lawCoordinateMap) (by
      ext value
      change f.lawCoordinateMap (MvPolynomial.C value.down) =
        MvPolynomial.C value.down
      simp [LensAATForwardMorphism.lawCoordinateMap, lensLawCoordinateMap])
  naturality := by
    intro W V contextMap
    apply CategoryTheory.Under.UnderMorphism.ext
    apply CommRingCat.hom_ext
    ext polynomial
    rfl

/-- The protocol Law coordinate homomorphism as a natural transformation of
the full coordinate-polynomial presheaves. -/
noncomputable def protocolAATEquationPolynomialForwardHom
    (input : ProtocolFamilyInput.{u})
    {X Y : ProtocolRealization input.schema input.observation}
    (f : ProtocolAATForwardMorphism X Y) :
    equationCoordinatePolynomialPresheaf
        (protocolAATGeometryReadingSite input X) ⟶
      (f.lawContextFunctor).op ⋙
        equationCoordinatePolynomialPresheaf
          (protocolAATGeometryReadingSite input Y) where
  app W := CategoryTheory.Under.homMk
    (CommRingCat.ofHom f.lawCoordinateMap) (by
      ext value
      change f.lawCoordinateMap (MvPolynomial.C value.down) =
        MvPolynomial.C value.down
      simp [ProtocolAATForwardMorphism.lawCoordinateMap, protocolLawCoordinateMap])
  naturality := by
    intro W V contextMap
    apply CategoryTheory.Under.UnderMorphism.ext
    apply CommRingCat.hom_ext
    ext polynomial
    rfl

/-- At every context, the polynomial transformation sends a lens violation
variable to the variable with the complete mapped Law index. -/
@[simp] theorem lensAATEquationPolynomialForwardHom_app_X
    (input : LensFamilyInput.{u})
    {X Y : LensRealization input.View input.reference}
    (f : LensAATForwardMorphism X Y)
    (W : (lensAATGeometryReadingSite input X).category)
    (index : LensLawIndex input.View X.Carrier) (atom : LensAATAtom input) :
    ((lensAATEquationPolynomialForwardHom input f).app (Opposite.op W)).right
        (MvPolynomial.X (ULift.up index, atom)) =
      MvPolynomial.X (ULift.up (f.lawIndexMap index), atom) := by
  exact lensLawCoordinateMap_violation input f.lawHom index atom

/-- At every context, the protocol polynomial transformation sends a relation
or observation variable to the variable with its mapped Law index. -/
@[simp] theorem protocolAATEquationPolynomialForwardHom_app_X
    (input : ProtocolFamilyInput.{u})
    {X Y : ProtocolRealization input.schema input.observation}
    (f : ProtocolAATForwardMorphism X Y)
    (W : (protocolAATGeometryReadingSite input X).category)
    (index : ProtocolLawIndex X.State) (atom : ProtocolAATAtom input) :
    ((protocolAATEquationPolynomialForwardHom input f).app (Opposite.op W)).right
        (MvPolynomial.X (ULift.up index, atom)) =
      MvPolynomial.X (ULift.up (f.lawIndexMap index), atom) := by
  exact protocolLawCoordinateMap_violation input f.lawHom index atom

/-! ## Raw quotient presheaf maps -/

/-- Conjugating the polynomial map by the independently proved Cycle 133
presheaf isomorphisms gives the actual forward map on lens raw quotients. -/
noncomputable def lensAATGeometryReadingRawForwardHom
    (input : LensFamilyInput.{u})
    {X Y : LensRealization input.View input.reference}
    (f : LensAATForwardMorphism X Y) :
    (lensAATGeometryReadingRawSystem input X).toPresheaf ⟶
      (f.lawContextFunctor).op ⋙
        (lensAATGeometryReadingRawSystem input Y).toPresheaf :=
  (lensAATGeometryReadingRawPresheafIso input X).hom ≫
    lensAATEquationPolynomialForwardHom input f ≫
      Functor.whiskerLeft (f.lawContextFunctor).op
        (lensAATGeometryReadingRawPresheafIso input Y).inv

/-- The same conjugation constructs the actual forward map on protocol raw
quotients for every primitive protocol morphism. -/
noncomputable def protocolAATGeometryReadingRawForwardHom
    (input : ProtocolFamilyInput.{u})
    {X Y : ProtocolRealization input.schema input.observation}
    (f : ProtocolAATForwardMorphism X Y) :
    (protocolAATGeometryReadingRawSystem input X).toPresheaf ⟶
      (f.lawContextFunctor).op ⋙
        (protocolAATGeometryReadingRawSystem input Y).toPresheaf :=
  (protocolAATGeometryReadingRawPresheafIso input X).hom ≫
    protocolAATEquationPolynomialForwardHom input f ≫
      Functor.whiskerLeft (f.lawContextFunctor).op
        (protocolAATGeometryReadingRawPresheafIso input Y).inv

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end AAT.AG.RealizationReconstruction
