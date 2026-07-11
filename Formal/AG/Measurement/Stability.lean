import Mathlib.Data.Finset.Basic
import Formal.AG.Measurement.SquareFreeRepair

noncomputable section

namespace AAT.AG
namespace Measurement

universe u v

/-!
Part VIII R4 / AC10 witness perturbation, persistence / zigzag reading, and
stability theorem-candidate surfaces.

The structures below record finite update and stability interfaces. They do
not prove persistence, zigzag, Morse, or monotone witness stability.
-/

/-- VIII.Definition 6.1: cardinality of the symmetric difference of two finite sets. -/
def witnessSymmetricDifferenceCardinality {α : Type u} [DecidableEq α]
    (F G : Finset α) : Nat :=
  ((F \ G) ∪ (G \ F)).card

/--
VIII.Definition 6.1: witness perturbation profile.

`d_wit` is the selected distance on finite forbidden-support families. The
profile records that it is read as the cardinality of symmetric difference of
the underlying finite forbidden-support sets.
-/
structure WitnessPerturbationProfile {M : MeasurementProfile.{u, v}}
    (R : SquareFreeRepairRegime M) where
  forbiddenSupportDecidableEq : DecidableEq R.ForbiddenSupport
  ForbiddenFamily : Type u
  familyFinset : ForbiddenFamily -> Finset R.ForbiddenSupport
  d_wit : ForbiddenFamily -> ForbiddenFamily -> Nat
  d_wit_eq_symmetricDifferenceCardinality :
    (F G : ForbiddenFamily) ->
      d_wit F G =
        @witnessSymmetricDifferenceCardinality R.ForbiddenSupport
          forbiddenSupportDecidableEq (familyFinset F) (familyFinset G)
  finiteForbiddenFamilies : Prop
  finiteForbiddenFamilies_cert : finiteForbiddenFamilies
  singleUpdateDistanceOne : Prop
  singleUpdateDistanceOne_cert : singleUpdateDistanceOne

namespace WitnessPerturbationProfile

/-- VIII.Definition 6.1: the selected symmetric-difference cardinality. -/
def symmetricDifferenceCardinality {M : MeasurementProfile.{u, v}}
    {R : SquareFreeRepairRegime M} (P : WitnessPerturbationProfile R)
    (F G : P.ForbiddenFamily) : Nat :=
  @witnessSymmetricDifferenceCardinality R.ForbiddenSupport
    P.forbiddenSupportDecidableEq (P.familyFinset F) (P.familyFinset G)

/-- VIII.Definition 6.1: expose that `d_wit` is symmetric-difference cardinality. -/
theorem d_wit_eq_symmetricDifferenceCardinality_holds {M : MeasurementProfile.{u, v}}
    {R : SquareFreeRepairRegime M} (P : WitnessPerturbationProfile R)
    (F G : P.ForbiddenFamily) :
    P.d_wit F G = P.symmetricDifferenceCardinality F G :=
  P.d_wit_eq_symmetricDifferenceCardinality F G

end WitnessPerturbationProfile

/-- VIII.Definition 6.1: finite complex updates used to read witness perturbations. -/
inductive WitnessUpdateKind where
  | singleUpdate
  | faceInsertion
  | faceDeletion
  | collapse
  | anticollapse
  deriving DecidableEq

/--
VIII.Definition 6.1: a selected finite complex update reading.

The update object records the finite data used to read single updates, face
insertions / deletions, collapses, and anticollapses. It does not assert that
the update is an architecture operation.
-/
structure FiniteComplexUpdateReading {M : MeasurementProfile.{u, v}}
    {R : SquareFreeRepairRegime M} (P : WitnessPerturbationProfile R) where
  sourceFamily : P.ForbiddenFamily
  targetFamily : P.ForbiddenFamily
  updateKind : WitnessUpdateKind
  SourceComplex : Type u
  TargetComplex : Type u
  updateData : Type u
  finiteComplexUpdate : Prop
  finiteComplexUpdate_cert : finiteComplexUpdate
  realizesWitnessPerturbation : Prop
  realizesWitnessPerturbation_cert : realizesWitnessPerturbation
  notOperationSemantics : Prop
  notOperationSemantics_cert : notOperationSemantics

/-- VIII.Definition 6.2: monotone persistence module interface for witness filtrations. -/
structure PersistenceProfile {M : MeasurementProfile.{u, v}}
    {R : SquareFreeRepairRegime M} (P : WitnessPerturbationProfile R) where
  Index : Type u
  le : Index -> Index -> Prop
  familyAt : Index -> P.ForbiddenFamily
  ComplexAt : Index -> Type u
  CohomologyAt : Index -> Type u
  coefficientComparisonMap : (i j : Index) -> le i j -> Type v
  persistenceMap : (i j : Index) -> le i j -> Type v
  finiteIndex : Prop
  finiteIndex_cert : finiteIndex
  monotoneFamilies : Prop
  monotoneFamilies_cert : monotoneFamilies
  finiteTypeCondition : Prop
  finiteTypeCondition_cert : finiteTypeCondition
  d_stab : Index -> Index -> Nat

/-- VIII.Definition 6.2: orientation of a finite zigzag arrow. -/
inductive ZigzagArrowDirection where
  | forward
  | backward
  deriving DecidableEq

/-- VIII.Definition 6.2: one selected arrow in a finite zigzag module. -/
structure ZigzagArrow {M : MeasurementProfile.{u, v}}
    {R : SquareFreeRepairRegime M} (P : WitnessPerturbationProfile R) where
  sourceFamily : P.ForbiddenFamily
  targetFamily : P.ForbiddenFamily
  direction : ZigzagArrowDirection
  correspondenceMap : Type v
  coefficientComparisonMap : Type v
  finiteCorrespondence : Prop
  finiteCorrespondence_cert : finiteCorrespondence

/-- VIII.Definition 6.2: finite zigzag module interface for witness perturbations. -/
structure ZigzagProfile {M : MeasurementProfile.{u, v}}
    {R : SquareFreeRepairRegime M} (P : WitnessPerturbationProfile R) where
  Node : Type u
  familyAt : Node -> P.ForbiddenFamily
  ComplexAt : Node -> Type u
  Arrow : Type u
  sourceNode : Arrow -> Node
  targetNode : Arrow -> Node
  arrowData : Arrow -> ZigzagArrow P
  arrow_sourceFamily_eq : (a : Arrow) ->
    (arrowData a).sourceFamily = familyAt (sourceNode a)
  arrow_targetFamily_eq : (a : Arrow) ->
    (arrowData a).targetFamily = familyAt (targetNode a)
  finiteNodes : Prop
  finiteNodes_cert : finiteNodes
  finiteArrows : Prop
  finiteArrows_cert : finiteArrows
  finiteTypeCondition : Prop
  finiteTypeCondition_cert : finiteTypeCondition

/--
VIII.Theorem candidate 6.3: finite Cech stability statement-only interface.

The candidate records the Lipschitz statement
`d_stab(H^*(F), H^*(F')) <= C_M * d_wit(F,F')` as a proposition shape. It does
not provide a proof of that proposition.
-/
structure FiniteCechStabilityCandidate {M : MeasurementProfile.{u, v}}
    {R : SquareFreeRepairRegime M} (P : WitnessPerturbationProfile R) where
  persistenceProfile : PersistenceProfile P
  zigzagProfile : ZigzagProfile P
  C_M : Nat
  indexOfFamily : P.ForbiddenFamily -> persistenceProfile.Index
  indexOfFamily_readsFamily :
    (F : P.ForbiddenFamily) -> persistenceProfile.familyAt (indexOfFamily F) = F
  finiteCechStabilityStatement : Prop
  finiteCechStabilityStatement_shape :
    finiteCechStabilityStatement =
      ∀ F G : P.ForbiddenFamily,
        persistenceProfile.d_stab (indexOfFamily F) (indexOfFamily G) <=
          C_M * P.d_wit F G

/--
VIII.Theorem candidate 6.5: monotone witness stability statement-only interface.

The candidate records the bottleneck bound
`d_bottleneck(Barcode(F), Barcode(F')) <= d_wit(F,F')` as a proposition shape.
It does not provide a proof of that proposition.
-/
structure MonotoneWitnessStabilityCandidate {M : MeasurementProfile.{u, v}}
    {R : SquareFreeRepairRegime M} (P : WitnessPerturbationProfile R) where
  persistenceProfile : PersistenceProfile P
  Barcode : P.ForbiddenFamily -> Type u
  bottleneckDistance : P.ForbiddenFamily -> P.ForbiddenFamily -> Nat
  monotoneWitnessStabilityStatement : Prop
  monotoneWitnessStabilityStatement_shape :
    monotoneWitnessStabilityStatement =
      ∀ F G : P.ForbiddenFamily, bottleneckDistance F G <= P.d_wit F G

/--
VIII.Principle 6.4 boundary: stability is a measurement assumption.

This records that a theorem-candidate interface is not a certified stable
measurement verdict unless the relevant stability theorem is supplied.
-/
structure StabilityMeasurementBoundary {M : MeasurementProfile.{u, v}}
    {R : SquareFreeRepairRegime M} (P : WitnessPerturbationProfile R) where
  candidateOnly : Prop
  candidateOnly_cert : candidateOnly
  noCertifiedStableMeasurementWithoutTheorem : Prop
  noCertifiedStableMeasurementWithoutTheorem_cert :
    noCertifiedStableMeasurementWithoutTheorem
  analyticBarcodeNotStructuralVerdict : Prop
  analyticBarcodeNotStructuralVerdict_cert : analyticBarcodeNotStructuralVerdict

namespace StabilityMeasurementBoundary

/-- VIII.R4: expose the boundary that candidate stability is not certified stability. -/
theorem noCertifiedStableMeasurementWithoutTheorem_holds {M : MeasurementProfile.{u, v}}
    {R : SquareFreeRepairRegime M} {P : WitnessPerturbationProfile R}
    (B : StabilityMeasurementBoundary P) :
    B.noCertifiedStableMeasurementWithoutTheorem :=
  B.noCertifiedStableMeasurementWithoutTheorem_cert

end StabilityMeasurementBoundary

end Measurement
end AAT.AG
