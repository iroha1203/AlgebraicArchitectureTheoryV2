import ResearchLean.AG.RealizationReconstruction.CSAATCoefficientRawExactMap
import Formal.Util.AssertStandardAxioms

/-!
# Target-indexed exact raw maps from genuine CS isomorphisms

The exact geometry layer indexes its raw action by target contexts and the
inverse context functor of the eventual core morphism.  The concrete lens and
protocol raw systems have constant complete Law-coordinate families and
identity restrictions at every context.  Consequently the actual coordinate
action of a genuine CS isomorphism defines an exact raw map against any such
inverse functor, without replacing either independently constructed endpoint.

This module constructs only that raw component.  It does not accept or claim
the eventual core-package morphism, realization comparison, or total geometry
morphism.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory

universe u

/-- Complete equation-coordinate raw systems support the target-indexed exact
map induced by any complete coordinate equivalence.  The inverse context
functor is arbitrary because both endpoint restrictions are identities, but
the coordinate action itself is the supplied equivalence on every context. -/
noncomputable def equationCoordinateRawExactMapAgainst
    {U : AtomCarrier.{u}} {A B : ArchitectureObject U}
    (S : Site.AATSite A) (T : Site.AATSite B)
    (inverse : T.category ⥤ S.category)
    (coordinateEquiv : S.equationSystem.Coordinate ≃
      T.equationSystem.Coordinate) :
    RawAmbientRestrictionSystemExactMapAgainst S T inverse
      (RingHom.id Int)
      (equationCoordinateRawSystemOn S)
      (equationCoordinateRawSystemOn T) where
  coordinate _ := {
    coordinateEquiv := coordinateEquiv
    label_eq := fun _ => rfl
    localDataEquiv := fun _ => Equiv.refl PUnit
  }
  relation _ := {
    relationEquiv := Equiv.refl PEmpty
    polynomial_eq := fun relation => PEmpty.elim relation
  }
  restriction_polynomial map polynomial := by
    change ((MvPolynomial.renameEquiv Int coordinateEquiv).toRingHom.comp
        (MvPolynomial.map (RingHom.id Int)))
          ((equationCoordinateRawRestriction S
            (inverse.map map)).polynomialMap polynomial) =
      (equationCoordinateRawRestriction T map).polynomialMap
        (((MvPolynomial.renameEquiv Int coordinateEquiv).toRingHom.comp
          (MvPolynomial.map (RingHom.id Int))) polynomial)
    change (MvPolynomial.renameEquiv Int coordinateEquiv)
        ((MvPolynomial.map (RingHom.id Int))
          ((equationCoordinateRawRestriction S
            (inverse.map map)).polynomialMap polynomial)) =
      (equationCoordinateRawRestriction T map).polynomialMap
        ((MvPolynomial.renameEquiv Int coordinateEquiv)
          ((MvPolynomial.map (RingHom.id Int)) polynomial))
    simp only [MvPolynomial.map_id]
    change (MvPolynomial.rename coordinateEquiv)
        ((equationCoordinateRawRestriction S (inverse.map map)).polynomialMap
          polynomial) =
      (equationCoordinateRawRestriction T map).polynomialMap
        ((MvPolynomial.rename coordinateEquiv) polynomial)
    rw [equationCoordinateRawRestriction_polynomialMap S (inverse.map map),
      equationCoordinateRawRestriction_polynomialMap T map]
    rfl

/-! ## Lens -/

/-- A genuine lens isomorphism supplies the target-indexed exact raw action
for any inverse-context functor selected by the later core bridge. -/
noncomputable def lensIsoRawExactMapAgainst
    {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference} (e : X ≅ Y)
    (inverse : (lensAATGeometryReadingSite input Y).category ⥤
      (lensAATGeometryReadingSite input X).category) :
    RawAmbientRestrictionSystemExactMapAgainst
      (lensAATGeometryReadingSite input X)
      (lensAATGeometryReadingSite input Y) inverse
      (RingHom.id Int)
      (lensAATGeometryReadingRawSystem input X)
      (lensAATGeometryReadingRawSystem input Y) :=
  equationCoordinateRawExactMapAgainst _ _ inverse
    (lensIsoLawCoordinateIndexEquiv e)

/-- The lens map acts by the genuine Law-index action on every target context
and every Law-index/Atom coordinate. -/
@[simp] theorem lensIsoRawExactMapAgainst_coordinate_apply
    {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference} (e : X ≅ Y)
    (inverse : (lensAATGeometryReadingSite input Y).category ⥤
      (lensAATGeometryReadingSite input X).category)
    (W : (lensAATGeometryReadingSite input Y).category)
    (index : LensLawIndex input.View X.Carrier) (atom : LensAATAtom input) :
    ((lensIsoRawExactMapAgainst e inverse).coordinate W).coordinateEquiv
        (ULift.up index, atom) =
      (ULift.up (lensIsoLawIndexEquiv e index), atom) :=
  rfl

/-! ## Protocol -/

/-- A genuine protocol isomorphism supplies the target-indexed exact raw
action for any inverse-context functor selected by the later core bridge. -/
noncomputable def protocolIsoRawExactMapAgainst
    {input : ProtocolFamilyInput.{u}}
    {X Y : ProtocolRealization input.schema input.observation} (e : X ≅ Y)
    (inverse : (protocolAATGeometryReadingSite input Y).category ⥤
      (protocolAATGeometryReadingSite input X).category) :
    RawAmbientRestrictionSystemExactMapAgainst
      (protocolAATGeometryReadingSite input X)
      (protocolAATGeometryReadingSite input Y) inverse
      (RingHom.id Int)
      (protocolAATGeometryReadingRawSystem input X)
      (protocolAATGeometryReadingRawSystem input Y) :=
  equationCoordinateRawExactMapAgainst _ _ inverse
    (protocolIsoLawCoordinateIndexEquiv e)

/-- The protocol map acts by the genuine relation/observation-index action on
every target context and every Law-index/Atom coordinate. -/
@[simp] theorem protocolIsoRawExactMapAgainst_coordinate_apply
    {input : ProtocolFamilyInput.{u}}
    {X Y : ProtocolRealization input.schema input.observation} (e : X ≅ Y)
    (inverse : (protocolAATGeometryReadingSite input Y).category ⥤
      (protocolAATGeometryReadingSite input X).category)
    (W : (protocolAATGeometryReadingSite input Y).category)
    (index : ProtocolLawIndex X.State) (atom : ProtocolAATAtom input) :
    ((protocolIsoRawExactMapAgainst e inverse).coordinate W).coordinateEquiv
        (ULift.up index, atom) =
      (ULift.up (protocolIsoLawIndexEquiv e index), atom) :=
  rfl

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end AAT.AG.RealizationReconstruction
