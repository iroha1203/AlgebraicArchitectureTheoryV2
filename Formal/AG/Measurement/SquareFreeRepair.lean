import Formal.AG.Measurement.Computability
import Formal.AG.LawAlgebra.StanleyReisner
import Mathlib.Data.Finset.Lattice.Basic

noncomputable section

namespace AAT.AG
namespace Measurement

universe u v

/-!
Part VIII R3 / AC7-AC9 square-free repair and Alexander dual surface.

The repair objects here are combinatorial measurement targets. A minimal repair
hitting set is not an architecture operation semantics or a legality theorem.
-/

/-- VIII.R3: Part VIII can reuse the Part III square-free witness regime surface. -/
abbrev UsesSquareFreeWitnessRegime (E : Type u) :=
  LawAlgebra.StanleyReisner.SquareFreeWitnessRegime E

/-- VIII.Definition 5.1: square-free repair regime over a measurement profile. -/
structure SquareFreeRepairRegime (M : MeasurementProfile.{u, v}) where
  /-- Finite selected witness carrier used by the repair computation. -/
  witnessFintype : Fintype M.WitnessVariables
  /-- Decidable equality used by finite support computations. -/
  witnessDecidableEq : DecidableEq M.WitnessVariables
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

namespace SquareFreeRepairRegime

variable {M : MeasurementProfile.{u, v}}

/--
VIII.Theorem 5.2 hardening: reuse the Part III Stanley-Reisner ideal theorem for
the selected source square-free witness regime.
-/
theorem source_obstructionIdeal_eq_stanleyReisnerIdeal
    (R : SquareFreeRepairRegime M) [DecidableEq M.WitnessVariables]
    (k : Type v) [CommRing k] :
    LawAlgebra.StanleyReisner.SquareFreeWitnessRegime.obstructionIdeal M.WitnessVariables k
        R.sourceWitnessRegime =
      LawAlgebra.StanleyReisner.SquareFreeWitnessRegime.stanleyReisnerIdeal M.WitnessVariables k
        (LawAlgebra.StanleyReisner.SquareFreeWitnessRegime.delta M.WitnessVariables R.sourceWitnessRegime) :=
  LawAlgebra.StanleyReisner.SquareFreeWitnessRegime.obstructionIdeal_eq_stanleyReisnerIdeal
    M.WitnessVariables k R.sourceWitnessRegime

/--
VIII.Theorem 5.2 hardening: reuse the Part III minimal generator / minimal forbidden
support theorem for the selected source square-free witness regime.
-/
theorem source_minimalGeneratorSupport_iff_minimalForbidden
    (R : SquareFreeRepairRegime M) [DecidableEq M.WitnessVariables]
    (S : Finset M.WitnessVariables) :
    LawAlgebra.StanleyReisner.SquareFreeWitnessRegime.MinimalStanleyReisnerGeneratorSupport
        M.WitnessVariables
        (LawAlgebra.StanleyReisner.SquareFreeWitnessRegime.delta M.WitnessVariables R.sourceWitnessRegime) S ↔
      LawAlgebra.StanleyReisner.SquareFreeWitnessRegime.MinimalForbidden
        M.WitnessVariables R.sourceWitnessRegime S :=
  LawAlgebra.StanleyReisner.SquareFreeWitnessRegime.minimalGeneratorSupport_iff_minimalForbidden
    M.WitnessVariables R.sourceWitnessRegime S

end SquareFreeRepairRegime

/-! ### Finset Alexander dual bridge -/

/--
VIII.Theorem 5.2 hardening: the Alexander dual face predicate
`S ∈ Δ*` iff `Sᶜ ∉ Δ.faces`, relative to a finite selected witness universe.
-/
def finiteAlexanderDualFaces (E : Type u) [Fintype E] [DecidableEq E]
    (Delta : LawAlgebra.StanleyReisner.SquareFreeWitnessRegime.AbstractSimplicialComplex E) :
    Set (Finset E) :=
  {S | (Finset.univ \ S) ∉ Delta.faces}

/-- VIII.Theorem 5.2 hardening: membership in the finite Alexander dual. -/
theorem mem_finiteAlexanderDualFaces_iff
    (E : Type u) [Fintype E] [DecidableEq E]
    (Delta : LawAlgebra.StanleyReisner.SquareFreeWitnessRegime.AbstractSimplicialComplex E)
    (S : Finset E) :
    S ∈ finiteAlexanderDualFaces E Delta ↔ (Finset.univ \ S) ∉ Delta.faces :=
  Iff.rfl

/-- VIII.Theorem 5.2 hardening: finite Alexander dual complex. -/
def finiteAlexanderDual (E : Type u) [Fintype E] [DecidableEq E]
    (Delta : LawAlgebra.StanleyReisner.SquareFreeWitnessRegime.AbstractSimplicialComplex E) :
    LawAlgebra.StanleyReisner.SquareFreeWitnessRegime.AbstractSimplicialComplex E where
  faces := finiteAlexanderDualFaces E Delta
  downward_closed := by
    intro S T hT hST hScomp
    exact hT (Delta.downward_closed hScomp (by
      intro x hx
      simp at hx ⊢
      intro hxS
      exact hx (hST hxS)))

/-- VIII.Theorem 5.2 hardening: finite support `H` hits every forbidden support. -/
def FinsetHitsForbidden (E : Type u) [DecidableEq E]
    (R : LawAlgebra.StanleyReisner.SquareFreeWitnessRegime E) (H : Finset E) : Prop :=
  ∀ F : Finset E, R.Forb F -> (H.filter fun x => x ∈ F).Nonempty

/--
VIII.Theorem 5.2 hardening: inclusion-minimal finite hitting set for the selected
forbidden support family.
-/
def MinimalHittingSetForForbidden (E : Type u) [DecidableEq E]
    (R : LawAlgebra.StanleyReisner.SquareFreeWitnessRegime E) (H : Finset E) : Prop :=
  FinsetHitsForbidden E R H ∧
    ∀ K : Finset E, FinsetHitsForbidden E R K -> K ⊆ H -> H ⊆ K

theorem not_subset_compl_iff_inter_nonempty
    (E : Type u) [Fintype E] [DecidableEq E]
    (F H : Finset E) :
    ¬ F ⊆ Finset.univ \ H ↔ (H.filter fun x => x ∈ F).Nonempty := by
  constructor
  · intro h
    by_contra hEmpty
    apply h
    intro x hxF
    simp
    intro hxH
    exact hEmpty ⟨x, by simp [hxH, hxF]⟩
  · intro h hsubset
    rcases h with ⟨x, hx⟩
    simp at hx
    have hxComp := hsubset hx.2
    simp at hxComp
    exact hxComp hx.1

/--
VIII.Theorem 5.2 hardening: nonfaces of the Alexander dual of `Δ_R` are exactly
hitting sets for the forbidden supports of `R`.
-/
theorem not_mem_finiteAlexanderDual_iff_hitsForbidden
    (E : Type u) [Fintype E] [DecidableEq E]
    (R : LawAlgebra.StanleyReisner.SquareFreeWitnessRegime E) (H : Finset E) :
    H ∉ (finiteAlexanderDual E
        (LawAlgebra.StanleyReisner.SquareFreeWitnessRegime.delta E R)).faces ↔
      FinsetHitsForbidden E R H := by
  classical
  unfold finiteAlexanderDual finiteAlexanderDualFaces FinsetHitsForbidden
  change ¬ ((Finset.univ \ H) ∉
        (LawAlgebra.StanleyReisner.SquareFreeWitnessRegime.delta E R).faces) ↔
      ∀ F : Finset E, R.Forb F -> (H.filter fun x => x ∈ F).Nonempty
  rw [not_not]
  constructor
  · intro h F hF
    exact (not_subset_compl_iff_inter_nonempty E F H).mp (h F hF)
  · intro h F hF
    exact (not_subset_compl_iff_inter_nonempty E F H).mpr (h F hF)

/--
VIII.Theorem 5.2 hardening: concrete bridge from repair targets to minimal finite
hitting sets.  This keeps repair as a combinatorial target, not operation
semantics.
-/
structure FiniteAlexanderDualRepairBridge {M : MeasurementProfile.{u, v}}
    (R : SquareFreeRepairRegime M) [Fintype M.WitnessVariables]
    [DecidableEq M.WitnessVariables] where
  RepairTarget : Type u
  repairSupport : RepairTarget -> Finset M.WitnessVariables
  minimalRepairTarget : RepairTarget -> Prop
  minimalRepairTarget_iff :
    ∀ target,
      minimalRepairTarget target ↔
        MinimalHittingSetForForbidden M.WitnessVariables R.sourceWitnessRegime
          (repairSupport target)

namespace FiniteAlexanderDualRepairBridge

variable {M : MeasurementProfile.{u, v}} {R : SquareFreeRepairRegime M}
variable [Fintype M.WitnessVariables] [DecidableEq M.WitnessVariables]

/-- VIII.Theorem 5.2 hardening: expose the minimal hitting-set bridge. -/
theorem minimalRepairTarget_iff_minimalHitting
    (B : FiniteAlexanderDualRepairBridge R) (target : B.RepairTarget) :
    B.minimalRepairTarget target ↔
      MinimalHittingSetForForbidden M.WitnessVariables R.sourceWitnessRegime
        (B.repairSupport target) :=
  B.minimalRepairTarget_iff target

end FiniteAlexanderDualRepairBridge

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
