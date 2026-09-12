import ResearchLean.AG.FullGeometryNormalization.ExactBarBetaClassification
import ResearchLean.AG.DoctrineFiberProduct.IdempotentExchangeWitnessPacket

/-!
# A fixed finite witness for the exact complete-geometry comparison

This module supplies geometry and raw restriction data on every cell of the
finite axis-fold datum fixed by G-122(C).  At the second cell, the firing and
admissibility fields of the existing G-116 witness packet select the same
actual `authoredExactBarBetaAt` classified in the preceding module, so that
comparison is not an ambient isomorphism.
-/

namespace AAT.AG.FullGeometryNormalization

open CategoryTheory AtomFoundation CrossStageCoherence TransportCoherence
open DoctrineFiberProduct

set_option maxHeartbeats 3000000

local instance finiteAxisFoldAtomDecidableEq :
    DecidableEq FiniteModel.carrier.Atom := by
  change DecidableEq FiniteModel.FiniteAtom
  infer_instance

/-- Vacuous coverage requirements on the untransported finite witness core. -/
def finiteAxisFoldSourceGeometryRequirements :
    Site.CoverageRequirements
      finiteWitnessSourcePackage.object
      finiteWitnessSourcePackage.equationSystem
      finiteWitnessSourcePackage.algebra.signatureReading where
  requiredSupport := fun _ => False
  requiredEquationCoordinate := fun _ => False
  selectedViolationWitness := fun _ => False
  requiredAxis := fun _ => False
  supportVisibleOn := fun _ _ => False
  equationCoordinateVisibleOn := fun _ _ => False
  violationWitnessVisibleOn := fun _ _ => False
  axisReadableOn := fun _ _ => False
  boundaryVisibleOn := fun _ _ => False

/-- Selected finite-meet geometry on the untransported finite witness core. -/
noncomputable def finiteAxisFoldSourceSelectedGeometry :
    Site.SelectedGeometryReading finiteWitnessSourcePackage where
  requirements := finiteAxisFoldSourceGeometryRequirements
  overlap := Site.meetOverlapPullback _ Site.productContextFiniteMeet

/-- One raw coordinate at every context of the fixed selected geometry. -/
def finiteAxisFoldSourceCoordinateFamily
    (W : finiteAxisFoldSourceSelectedGeometry.toAATSite.category) :
    LawAlgebra.CoordinateFamily W.ctx where
  Coord := Unit
  label := fun _ => LawAlgebra.CoordinateLabel.semantic
  LocalData := fun _ => Unit

/-- A fixed integral idempotence relation at every context. -/
noncomputable def finiteAxisFoldSourceRelationFamily
    (W : finiteAxisFoldSourceSelectedGeometry.toAATSite.category) :
    LawAlgebra.StructuralRelationFamily
      (finiteAxisFoldSourceCoordinateFamily W) Int where
  Relation := Unit
  polynomial := fun _ => MvPolynomial.X () ^ 2 - MvPolynomial.X ()

/-- Identity restriction of the unique raw coordinate. -/
noncomputable def finiteAxisFoldSourceCoordinateRestriction
    {X Y : finiteAxisFoldSourceSelectedGeometry.toAATSite.category}
    (w : X ⟶ Y) :
    LawAlgebra.TypedCoordinateRestriction
      (finiteAxisFoldSourceCoordinateFamily X)
      (finiteAxisFoldSourceCoordinateFamily Y) Int
      (finiteAxisFoldSourceSelectedGeometry.toAATSite.contextPreorder.morphism
        (leOfHom w)) where
  variableImage := fun _ => MvPolynomial.X ()

/-- The coordinate restriction induces the identity polynomial map. -/
theorem finiteAxisFoldSourceCoordinateRestriction_polynomialMap
    {X Y : finiteAxisFoldSourceSelectedGeometry.toAATSite.category}
    (w : X ⟶ Y) :
    (finiteAxisFoldSourceCoordinateRestriction w).polynomialMap =
      RingHom.id
        (LawAlgebra.FreeTypedCommAlg (finiteAxisFoldSourceCoordinateFamily X) Int) := by
  apply MvPolynomial.ringHom_ext
  · intro value
    change (finiteAxisFoldSourceCoordinateRestriction w).polynomialMap
        (MvPolynomial.C value) = MvPolynomial.C value
    exact LawAlgebra.TypedCoordinateRestriction.polynomialMap_C _ _
  · intro coordinate
    cases coordinate
    rw [LawAlgebra.TypedCoordinateRestriction.polynomialMap_X]
    rfl

/-- The fixed raw relation is stable under all context restrictions. -/
noncomputable def finiteAxisFoldSourceRestrictionStable
    {X Y : finiteAxisFoldSourceSelectedGeometry.toAATSite.category}
    (w : X ⟶ Y) :
    LawAlgebra.RestrictionStableStructuralRelations
      (finiteAxisFoldSourceRelationFamily X)
      (finiteAxisFoldSourceRelationFamily Y)
      (finiteAxisFoldSourceSelectedGeometry.toAATSite.contextPreorder.morphism
        (leOfHom w)) where
  restriction := finiteAxisFoldSourceCoordinateRestriction w
  maps_JStruct := by
    intro polynomial hpolynomial
    have identity :
        (finiteAxisFoldSourceCoordinateRestriction w).polynomialMap polynomial =
          polynomial := by
      rw [finiteAxisFoldSourceCoordinateRestriction_polynomialMap]
      rfl
    rw [identity]
    exact hpolynomial

/-- Raw integral restriction data on the untransported finite witness core. -/
noncomputable def finiteAxisFoldSourceRaw :
    LawAlgebra.RawAmbientRestrictionSystem
      finiteAxisFoldSourceSelectedGeometry.toAATSite Int where
  coordFamily := finiteAxisFoldSourceCoordinateFamily
  relationFamily := finiteAxisFoldSourceRelationFamily
  restrictionStable := finiteAxisFoldSourceRestrictionStable
  identity_polynomialMap W :=
    finiteAxisFoldSourceCoordinateRestriction_polynomialMap (𝟙 W)
  composition_polynomialMap f g := by
    change (finiteAxisFoldSourceCoordinateRestriction (f ≫ g)).polynomialMap =
      ((finiteAxisFoldSourceCoordinateRestriction f).polynomialMap).comp
        ((finiteAxisFoldSourceCoordinateRestriction g).polynomialMap)
    rw [finiteAxisFoldSourceCoordinateRestriction_polynomialMap,
      finiteAxisFoldSourceCoordinateRestriction_polynomialMap,
      finiteAxisFoldSourceCoordinateRestriction_polynomialMap]
    exact (RingHom.id_comp _).symm

/-- Complete source package before applying the fixed exact doctrine transport. -/
noncomputable def finiteAxisFoldSourceGeometryPackage :
    GeometryTransport.GeometryPackage.{0, 0} FiniteModel.carrier where
  core := finiteWitnessSourcePackage
  geometry := finiteAxisFoldSourceSelectedGeometry
  Coefficient := Int
  coefficientCommRing := inferInstance
  raw := finiteAxisFoldSourceRaw

/-- The complete package transported to the support core used at every cell. -/
noncomputable def finiteAxisFoldGeometryPackage :
    GeometryTransport.GeometryPackage.{0, 0} FiniteModel.carrier :=
  GeometryTransport.geomTransportAlong finiteAxisFoldSourceGeometryPackage
    finiteModelDoctrineFromFixture

/-- Fixed-coefficient complete geometry on one cell of the finite datum. -/
noncomputable def finiteAxisFoldFixedCoefficientGeometryAt
    (cell : finiteAxisFoldBCDatumSquare.context.Category) :
  FixedCoefficientGeometryAt
      (finiteAxisFoldBCDatumSquare.context.supportPackage cell.as) Int where
  geometry := finiteAxisFoldGeometryPackage.geometry
  raw := finiteAxisFoldGeometryPackage.raw

/-- A geometry/raw-data input at every cell of the fixed finite datum. -/
noncomputable def finiteAxisFoldFixedCoefficientGeometryFamily :
    ∀ cell : finiteAxisFoldBCDatumSquare.context.Category,
      FixedCoefficientGeometryAt
        (finiteAxisFoldBCDatumSquare.context.supportPackage cell.as) Int :=
  fun cell => finiteAxisFoldFixedCoefficientGeometryAt cell

/-- The fixed finite example has a nonempty family of complete-geometry
inputs on its original support cores. -/
theorem finiteAxisFold_fixedCoefficientGeometryFamily_nonempty :
    Nonempty
      (∀ cell : finiteAxisFoldBCDatumSquare.context.Category,
        FixedCoefficientGeometryAt
          (finiteAxisFoldBCDatumSquare.context.supportPackage cell.as) Int) :=
  ⟨finiteAxisFoldFixedCoefficientGeometryFamily⟩

/-- At the required second cell and integral coefficient ring, the same actual
`barBeta` constructed by the exact route is not an ambient isomorphism. -/
theorem finiteAxisFold_authoredExactBarBetaAt_not_isIso :
    let input := finiteAxisFoldBCDatumSquare
    let omega := initialRawDefectCochain input.toTransportData
    let z : input.context.Category := Discrete.mk DoubleDiamondTwoCell.second
    ¬ IsIso (authoredExactBarBetaAt input z omega Int
      (finiteAxisFoldFixedCoefficientGeometryFamily z)) := by
  dsimp only
  intro isIso
  have notSelected :=
    (authoredExactBarBetaAt_isIso_iff_not_selected
      finiteAxisFoldBCDatumSquare
      (Discrete.mk DoubleDiamondTwoCell.second)
      (initialRawDefectCochain finiteAxisFoldBCDatumSquare.toTransportData)
      Int
      (finiteAxisFoldFixedCoefficientGeometryFamily
        (Discrete.mk DoubleDiamondTwoCell.second))).1 isIso
  have packet := finiteAxisFold_idempotentExchange_witnessPacket
  dsimp only at packet
  exact notSelected ⟨packet.1, packet.2.1⟩

/-- G-122(C)'s fixed finite witness packet: inputs exist at every cell and the
generated comparison at the specified second cell is noninvertible. -/
theorem finiteAxisFold_exactBarBeta_witnessPacket :
    let input := finiteAxisFoldBCDatumSquare
    let omega := initialRawDefectCochain input.toTransportData
    let z : input.context.Category := Discrete.mk DoubleDiamondTwoCell.second
    let family := finiteAxisFoldFixedCoefficientGeometryFamily
    Nonempty
      (∀ cell : input.context.Category,
        FixedCoefficientGeometryAt (input.context.supportPackage cell.as) Int) ∧
      ¬ IsIso (authoredExactBarBetaAt input z omega Int (family z)) := by
  dsimp only
  exact ⟨finiteAxisFold_fixedCoefficientGeometryFamily_nonempty,
    finiteAxisFold_authoredExactBarBetaAt_not_isIso⟩

#assert_standard_axioms_only AAT.AG.FullGeometryNormalization

end AAT.AG.FullGeometryNormalization
