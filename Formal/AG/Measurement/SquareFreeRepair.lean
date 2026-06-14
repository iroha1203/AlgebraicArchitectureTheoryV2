import Formal.AG.Measurement.Computability
import Formal.AG.LawAlgebra.StanleyReisner

noncomputable section

namespace AAT.AG
namespace Measurement

universe u v

/-!
PRD-8 R3 / AC7-AC9 square-free repair and Alexander dual surface.

The repair objects here are combinatorial measurement targets. A minimal repair
hitting set is not an architecture operation semantics or a legality theorem.
-/

/-- VIII.R3: Part VIII can reuse the PRD-3 square-free witness regime surface. -/
abbrev UsesSquareFreeWitnessRegime (E : Type u) :=
  LawAlgebra.StanleyReisner.SquareFreeWitnessRegime E

/-- VIII.Definition 5.1: square-free repair regime over a measurement profile. -/
structure SquareFreeRepairRegime (M : MeasurementProfile.{u, v}) where
  finiteRegime : FiniteMeasurementRegime M
  sourceWitnessRegime : UsesSquareFreeWitnessRegime M.WitnessVariables
  Witness : Type u
  witnessOfProfileWitness : M.WitnessVariables -> Witness
  ForbiddenSupport : Type u
  MinimalForbiddenSupport : Type u
  ObstructionIdeal : Type u
  StanleyReisnerIdeal : Type u
  Delta : Type u
  profileWitnessesLifted : Prop
  profileWitnessesLifted_cert : profileWitnessesLifted
  forbiddenSupportReadsSourceRegime : Prop
  forbiddenSupportReadsSourceRegime_cert : forbiddenSupportReadsSourceRegime
  finiteWitness : Prop
  finiteWitness_cert : finiteWitness
  forbiddenSupportsFinite : Prop
  forbiddenSupportsFinite_cert : forbiddenSupportsFinite
  minimalForbiddenSupportsFinite : Prop
  minimalForbiddenSupportsFinite_cert : minimalForbiddenSupportsFinite
  obstructionIdealGeneratedByMinimalForbidden : Prop
  obstructionIdealGeneratedByMinimalForbidden_cert : obstructionIdealGeneratedByMinimalForbidden
  deltaAvoidsForbiddenSupports : Prop
  deltaAvoidsForbiddenSupports_cert : deltaAvoidsForbiddenSupports

/-- VIII.Theorem 5.2 supporting data: Alexander dual complex of a square-free regime. -/
structure AlexanderDualComplex {M : MeasurementProfile.{u, v}}
    (R : SquareFreeRepairRegime M) where
  Dual : Type u
  dualOfDelta : Prop
  dualOfDelta_cert : dualOfDelta

/-- VIII.Theorem 5.2 supporting data: minimal vertex covers for forbidden supports. -/
structure MinimalVertexCover {M : MeasurementProfile.{u, v}}
    (R : SquareFreeRepairRegime M) where
  Cover : Type u
  minimalVertexCover : Cover -> Prop

/-- VIII.Theorem 5.2 supporting data: minimal witness hitting sets. -/
structure MinimalWitnessHittingSet {M : MeasurementProfile.{u, v}}
    (R : SquareFreeRepairRegime M) where
  HittingSet : Type u
  minimalWitnessHittingSet : HittingSet -> Prop

/--
VIII.Theorem 5.2 supporting data: minimal repair hitting sets.

This is a combinatorial target, not an operation semantics.
-/
structure MinimalRepairHittingSet {M : MeasurementProfile.{u, v}}
    (R : SquareFreeRepairRegime M) where
  RepairTarget : Type u
  minimalRepairHittingSet : RepairTarget -> Prop
  notOperationSemantics : Prop
  notOperationSemantics_cert : notOperationSemantics

/-- VIII.Theorem 5.2: Stanley-Reisner / Alexander dual repair theorem package. -/
structure StanleyReisnerAlexanderDualRepair {M : MeasurementProfile.{u, v}}
    (R : SquareFreeRepairRegime M) where
  alexanderDual : AlexanderDualComplex R
  minimalVertexCovers : MinimalVertexCover R
  minimalWitnessHittingSets : MinimalWitnessHittingSet R
  minimalRepairHittingSets : MinimalRepairHittingSet R
  obstructionIdeal_eq_stanleyReisnerIdeal : Prop
  obstructionIdeal_eq_stanleyReisnerIdeal_cert : obstructionIdeal_eq_stanleyReisnerIdeal
  minimalGenerators_iff_minimalForbiddenSupports : Prop
  minimalGenerators_iff_minimalForbiddenSupports_cert :
    minimalGenerators_iff_minimalForbiddenSupports
  minimalVertexCovers_iff_minimalWitnessHittingSets : Prop
  minimalVertexCovers_iff_minimalWitnessHittingSets_cert :
    minimalVertexCovers_iff_minimalWitnessHittingSets
  alexanderDualGenerators_iff_minimalRepairHittingSets : Prop
  alexanderDualGenerators_iff_minimalRepairHittingSets_cert :
    alexanderDualGenerators_iff_minimalRepairHittingSets

namespace StanleyReisnerAlexanderDualRepair

/-- VIII.Theorem 5.2: expose the obstruction-ideal / SR-ideal equality certificate. -/
theorem obstructionIdeal_eq_holds {M : MeasurementProfile.{u, v}}
    {R : SquareFreeRepairRegime M} (T : StanleyReisnerAlexanderDualRepair R) :
    T.obstructionIdeal_eq_stanleyReisnerIdeal :=
  T.obstructionIdeal_eq_stanleyReisnerIdeal_cert

/-- VIII.Theorem 5.2: expose the minimal generator / forbidden support certificate. -/
theorem minimalGenerators_iff_holds {M : MeasurementProfile.{u, v}}
    {R : SquareFreeRepairRegime M} (T : StanleyReisnerAlexanderDualRepair R) :
    T.minimalGenerators_iff_minimalForbiddenSupports :=
  T.minimalGenerators_iff_minimalForbiddenSupports_cert

/-- VIII.Theorem 5.2: expose the vertex-cover / witness-hitting-set certificate. -/
theorem vertexCovers_iff_hittingSets_holds {M : MeasurementProfile.{u, v}}
    {R : SquareFreeRepairRegime M} (T : StanleyReisnerAlexanderDualRepair R) :
    T.minimalVertexCovers_iff_minimalWitnessHittingSets :=
  T.minimalVertexCovers_iff_minimalWitnessHittingSets_cert

/-- VIII.Theorem 5.2: expose the Alexander-dual generator / repair target certificate. -/
theorem alexanderDualGenerators_iff_holds {M : MeasurementProfile.{u, v}}
    {R : SquareFreeRepairRegime M} (T : StanleyReisnerAlexanderDualRepair R) :
    T.alexanderDualGenerators_iff_minimalRepairHittingSets :=
  T.alexanderDualGenerators_iff_minimalRepairHittingSets_cert

end StanleyReisnerAlexanderDualRepair

/-- VIII.Theorem 5.2: construct the selected repair theorem package. -/
def stanleyReisnerAlexanderDualRepairPackage {M : MeasurementProfile.{u, v}}
    {R : SquareFreeRepairRegime M}
    (alexanderDual : AlexanderDualComplex R)
    (minimalVertexCovers : MinimalVertexCover R)
    (minimalWitnessHittingSets : MinimalWitnessHittingSet R)
    (minimalRepairHittingSets : MinimalRepairHittingSet R)
    (obstructionIdeal_eq_stanleyReisnerIdeal : Prop)
    (obstructionIdeal_eq_stanleyReisnerIdeal_cert :
      obstructionIdeal_eq_stanleyReisnerIdeal)
    (minimalGenerators_iff_minimalForbiddenSupports : Prop)
    (minimalGenerators_iff_minimalForbiddenSupports_cert :
      minimalGenerators_iff_minimalForbiddenSupports)
    (minimalVertexCovers_iff_minimalWitnessHittingSets : Prop)
    (minimalVertexCovers_iff_minimalWitnessHittingSets_cert :
      minimalVertexCovers_iff_minimalWitnessHittingSets)
    (alexanderDualGenerators_iff_minimalRepairHittingSets : Prop)
    (alexanderDualGenerators_iff_minimalRepairHittingSets_cert :
      alexanderDualGenerators_iff_minimalRepairHittingSets) :
    StanleyReisnerAlexanderDualRepair R where
  alexanderDual := alexanderDual
  minimalVertexCovers := minimalVertexCovers
  minimalWitnessHittingSets := minimalWitnessHittingSets
  minimalRepairHittingSets := minimalRepairHittingSets
  obstructionIdeal_eq_stanleyReisnerIdeal := obstructionIdeal_eq_stanleyReisnerIdeal
  obstructionIdeal_eq_stanleyReisnerIdeal_cert :=
    obstructionIdeal_eq_stanleyReisnerIdeal_cert
  minimalGenerators_iff_minimalForbiddenSupports :=
    minimalGenerators_iff_minimalForbiddenSupports
  minimalGenerators_iff_minimalForbiddenSupports_cert :=
    minimalGenerators_iff_minimalForbiddenSupports_cert
  minimalVertexCovers_iff_minimalWitnessHittingSets :=
    minimalVertexCovers_iff_minimalWitnessHittingSets
  minimalVertexCovers_iff_minimalWitnessHittingSets_cert :=
    minimalVertexCovers_iff_minimalWitnessHittingSets_cert
  alexanderDualGenerators_iff_minimalRepairHittingSets :=
    alexanderDualGenerators_iff_minimalRepairHittingSets
  alexanderDualGenerators_iff_minimalRepairHittingSets_cert :=
    alexanderDualGenerators_iff_minimalRepairHittingSets_cert

/-- VIII.Theorem 5.2: the selected SR / Alexander dual repair package exists. -/
theorem stanleyReisner_alexanderDual_repair {M : MeasurementProfile.{u, v}}
    {R : SquareFreeRepairRegime M}
    (alexanderDual : AlexanderDualComplex R)
    (minimalVertexCovers : MinimalVertexCover R)
    (minimalWitnessHittingSets : MinimalWitnessHittingSet R)
    (minimalRepairHittingSets : MinimalRepairHittingSet R)
    (obstructionIdeal_eq_stanleyReisnerIdeal : Prop)
    (obstructionIdeal_eq_stanleyReisnerIdeal_cert :
      obstructionIdeal_eq_stanleyReisnerIdeal)
    (minimalGenerators_iff_minimalForbiddenSupports : Prop)
    (minimalGenerators_iff_minimalForbiddenSupports_cert :
      minimalGenerators_iff_minimalForbiddenSupports)
    (minimalVertexCovers_iff_minimalWitnessHittingSets : Prop)
    (minimalVertexCovers_iff_minimalWitnessHittingSets_cert :
      minimalVertexCovers_iff_minimalWitnessHittingSets)
    (alexanderDualGenerators_iff_minimalRepairHittingSets : Prop)
    (alexanderDualGenerators_iff_minimalRepairHittingSets_cert :
      alexanderDualGenerators_iff_minimalRepairHittingSets) :
    Nonempty (StanleyReisnerAlexanderDualRepair R) :=
  ⟨stanleyReisnerAlexanderDualRepairPackage alexanderDual minimalVertexCovers
    minimalWitnessHittingSets minimalRepairHittingSets
    obstructionIdeal_eq_stanleyReisnerIdeal
    obstructionIdeal_eq_stanleyReisnerIdeal_cert
    minimalGenerators_iff_minimalForbiddenSupports
    minimalGenerators_iff_minimalForbiddenSupports_cert
    minimalVertexCovers_iff_minimalWitnessHittingSets
    minimalVertexCovers_iff_minimalWitnessHittingSets_cert
    alexanderDualGenerators_iff_minimalRepairHittingSets
    alexanderDualGenerators_iff_minimalRepairHittingSets_cert⟩

/-- VIII.Definition 5.4: selected discrete Morse repair reading. -/
structure DiscreteMorseRepairReading {M : MeasurementProfile.{u, v}}
    (R : SquareFreeRepairRegime M) where
  AcyclicMatching : Type u
  DiscreteMorseFunction : Type u
  CriticalCell : Type u
  selectedRepairRoute : Type u
  acyclicMatching_cert : Prop
  acyclicMatching_holds : acyclicMatching_cert
  selectedCombinatorialReading : Prop
  selectedCombinatorialReading_holds : selectedCombinatorialReading

/--
VIII.Theorem candidate 5.5: Morse lower bound statement-only interface.

The candidate requires operation-semantics compatibility, legality, and
side-effect assumptions; this file only records the statement surface.
-/
structure MorseLowerBoundForStructuralRepairCandidate {M : MeasurementProfile.{u, v}}
    {R : SquareFreeRepairRegime M} (D : DiscreteMorseRepairReading R) where
  operationSemanticsCompatible : Prop
  legalityAssumption : Prop
  sideEffectProfileControlled : Prop
  criticalCellLowerBound : Prop
  candidateStatement :
    operationSemanticsCompatible ->
      legalityAssumption ->
        sideEffectProfileControlled ->
          criticalCellLowerBound

end Measurement
end AAT.AG
