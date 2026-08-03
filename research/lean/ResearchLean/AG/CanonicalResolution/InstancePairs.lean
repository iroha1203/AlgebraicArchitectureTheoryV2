import ResearchLean.AG.CanonicalResolution.NegativeWitness

/-!
# Instance-pair audit for canonical resolution predicates

This module closes the positive/negative instance-pair obligation for every
`Prop` predicate introduced by `G-103-aat-canonical-resolution`.  All fixtures
use the same six-element source and nonconstant law family as the target
witnesses.  The two-index negative class deliberately repeats one doctrine,
so its failure of kernel distinctness is not caused by an undersized index.
-/

namespace AAT.AG.CanonicalResolution

namespace InstancePairs

open PositiveWitness NegativeWitness

/-- The identity reading on the six-element witness source. -/
def identityReading : Reading Source where
  Target := Source
  read := id
  surjective := fun source => ⟨source, rfl⟩

/-- The total reading that identifies every witness source. -/
def totalReading : Reading Source where
  Target := PUnit
  read := fun _ => PUnit.unit
  surjective := by
    intro target
    rcases target with ⟨⟩
    exact ⟨Source.a0, rfl⟩

/-- A two-index doctrine family whose two members induce the same kernel. -/
def duplicateDoctrine (_ : Bool) : DoctrineOn FiniteModel.carrier Source :=
  codedOn canonicalCode

/-- A genuine two-index class that fails kernel distinctness. -/
def duplicateKernelAdmissible :
    AdmissibleClass FiniteModel.carrier Source where
  Index := Bool
  indexFintype := inferInstance
  doctrine := duplicateDoctrine

/-! ## `Reading.Kernel` -/

/-- The identity reading relates a source to itself. -/
theorem kernel_positive : identityReading.Kernel Source.a0 Source.a0 :=
  rfl

/-- The identity reading does not relate two distinct sources. -/
theorem kernel_negative : ¬ identityReading.Kernel Source.a0 Source.a1 := by
  intro hkernel
  change Source.a0 = Source.a1 at hkernel
  cases hkernel

/-! ## `Reading.Factors` -/

/-- The nonconstant law signal factors through the identity reading. -/
theorem factors_positive : identityReading.Factors lawValue := by
  refine ⟨lawValue, ?_⟩
  intro source
  rfl

/-- The nonconstant law signal does not factor through the total reading. -/
theorem factors_negative : ¬ totalReading.Factors lawValue := by
  rintro ⟨descend, hdescend⟩
  have hfalseTrue : false = true := by
    calc
      false = descend PUnit.unit := (hdescend Source.a0).symm
      _ = true := hdescend Source.b0
  cases hfalseTrue

/-! ## `Reading.FactorsThrough` -/

/-- The total reading factors through the identity reading. -/
theorem factorsThrough_positive :
    totalReading.FactorsThrough identityReading := by
  refine ⟨fun _ => PUnit.unit, ?_⟩
  intro source
  rfl

/-- The identity reading cannot factor through the total reading. -/
theorem factorsThrough_negative :
    ¬ identityReading.FactorsThrough totalReading := by
  rintro ⟨descend, hdescend⟩
  have hdistinct : Source.a0 = Source.a1 := by
    calc
      Source.a0 = descend PUnit.unit := (hdescend Source.a0).symm
      _ = Source.a1 := hdescend Source.a1
  cases hdistinct

/-! ## `Reading.CoarserThan` -/

/-- The total reading is coarser than the identity reading. -/
theorem coarserThan_positive :
    totalReading.CoarserThan identityReading := by
  intro x y _hxy
  rfl

/-- The identity reading is not coarser than the total reading. -/
theorem coarserThan_negative :
    ¬ identityReading.CoarserThan totalReading := by
  intro hcoarser
  apply kernel_negative
  exact hcoarser (x := Source.a0) (y := Source.a1) rfl

/-! ## `Reading.KernelEquivalent` -/

/-- Kernel equivalence holds for the identity reading with itself. -/
theorem kernelEquivalent_positive :
    identityReading.KernelEquivalent identityReading :=
  identityReading.kernelEquivalent_refl

/-- The identity and total readings do not have the same kernel. -/
theorem kernelEquivalent_negative :
    ¬ identityReading.KernelEquivalent totalReading := by
  intro hkernel
  apply kernel_negative
  exact (hkernel Source.a0 Source.a1).2 rfl

/-! ## `FiniteLawFamily.Equivalent` -/

/-- Two sources in the first law fiber are law-equivalent. -/
theorem equivalent_positive : laws.Equivalent Source.a0 Source.a1 :=
  (laws_equivalent_iff_canonicalCode_eq _ _).2 rfl

/-- Sources in different law fibers are not law-equivalent. -/
theorem equivalent_negative : ¬ laws.Equivalent Source.a0 Source.b0 := by
  intro hequivalent
  have hvalue := (laws_equivalent_iff_lawValue_eq _ _).1 hequivalent
  change false = true at hvalue
  cases hvalue

/-! ## `FiniteLawFamily.Adequate` -/

/-- The canonical doctrine reading is adequate for the witness laws. -/
theorem adequate_positive : laws.Adequate (codedOn canonicalCode).reading :=
  canonicalCode_adequate

/-- The total reading is not adequate for the nonconstant witness law. -/
theorem adequate_negative : ¬ laws.Adequate totalReading := by
  intro hadequate
  apply equivalent_negative
  exact (laws.adequate_iff_kernel totalReading).1 hadequate
    (x := Source.a0) (y := Source.b0) rfl

/-! ## `DoctrineOn.Equivalent` -/

/-- The canonical doctrine extracts the same Atom set on one law fiber. -/
theorem doctrineEquivalent_positive :
    (codedOn canonicalCode).Equivalent Source.a0 Source.a1 := by
  change (codedOn canonicalCode).extractedAtoms Source.a0 =
    (codedOn canonicalCode).extractedAtoms Source.a1
  apply Set.ext
  intro atom
  rw [codedOn_extractedAtoms_mem_iff, codedOn_extractedAtoms_mem_iff]
  rfl

/-- The canonical doctrine extracts different Atom sets on different fibers. -/
theorem doctrineEquivalent_negative :
    ¬ (codedOn canonicalCode).Equivalent Source.a0 Source.b0 := by
  intro hequivalent
  have hkernel : (codedOn canonicalCode).reading.Kernel
      Source.a0 Source.b0 :=
    ((codedOn canonicalCode).reading_kernel_iff _ _).2 hequivalent
  have hcode := (codedOn_reading_kernel_iff canonicalCode _ _).1 hkernel
  change FiniteModel.FiniteAtom.componentA =
    FiniteModel.FiniteAtom.componentB at hcode
  cases hcode

/-! ## `AdmissibleClass.Representable` -/

/-- The positive doctrine class represents the canonical law kernel. -/
theorem representable_positive :
    PositiveWitness.admissible.Representable laws :=
  PositiveWitness.representable

/-- The negative doctrine class does not represent the canonical law kernel. -/
theorem representable_negative :
    ¬ NegativeWitness.admissible.Representable laws :=
  NegativeWitness.not_representable

/-! ## `Reading.NonDiscrete` -/

/-- The canonical joint-kernel reading is non-discrete. -/
theorem nonDiscrete_positive : laws.jointKernelReading.NonDiscrete :=
  jointKernel_nonDiscrete

/-- The identity reading is not non-discrete. -/
theorem nonDiscrete_negative : ¬ identityReading.NonDiscrete := by
  rintro ⟨x, y, hxy, hkernel⟩
  change x = y at hkernel
  exact hxy hkernel

/-! ## `Reading.NonTotal` -/

/-- The canonical joint-kernel reading is nontotal. -/
theorem nonTotal_positive : laws.jointKernelReading.NonTotal :=
  jointKernel_nonTotal

/-- The total reading is not nontotal. -/
theorem nonTotal_negative : ¬ totalReading.NonTotal := by
  rintro ⟨x, y, hkernel⟩
  exact hkernel rfl

/-! ## `AdmissibleClass.HasTwoKernelDistinct` -/

/-- The positive class has two kernel-distinct members. -/
theorem hasTwoKernelDistinct_positive :
    PositiveWitness.admissible.HasTwoKernelDistinct :=
  positive_hasTwoKernelDistinct

/-- The duplicate-kernel fixture really has two distinct indices. -/
theorem duplicateKernelAdmissible_has_distinct_indices :
    ∃ i j : duplicateKernelAdmissible.Index, i ≠ j := by
  change ∃ i j : Bool, i ≠ j
  refine ⟨false, true, ?_⟩
  intro hfalseTrue
  cases hfalseTrue

/-- Two indices are insufficient when every induced doctrine kernel is equal. -/
theorem hasTwoKernelDistinct_negative :
    ¬ duplicateKernelAdmissible.HasTwoKernelDistinct := by
  rintro ⟨i, j, _hij, hnotKernelEquivalent⟩
  apply hnotKernelEquivalent
  change (codedOn canonicalCode).reading.KernelEquivalent
    (codedOn canonicalCode).reading
  exact (codedOn canonicalCode).reading.kernelEquivalent_refl

/-!
The conjunction below is a fail-closed inventory.  It stores no certificate;
each component resolves to the independently proved finite declarations above.
-/

/-- Every new canonical-resolution `Prop` has explicit satisfying and refuting instances. -/
theorem all_new_prop_instance_pairs :
    (identityReading.Kernel Source.a0 Source.a0 ∧
      ¬ identityReading.Kernel Source.a0 Source.a1) ∧
    (identityReading.Factors lawValue ∧
      ¬ totalReading.Factors lawValue) ∧
    (totalReading.FactorsThrough identityReading ∧
      ¬ identityReading.FactorsThrough totalReading) ∧
    (totalReading.CoarserThan identityReading ∧
      ¬ identityReading.CoarserThan totalReading) ∧
    (identityReading.KernelEquivalent identityReading ∧
      ¬ identityReading.KernelEquivalent totalReading) ∧
    (laws.Equivalent Source.a0 Source.a1 ∧
      ¬ laws.Equivalent Source.a0 Source.b0) ∧
    (laws.Adequate (codedOn canonicalCode).reading ∧
      ¬ laws.Adequate totalReading) ∧
    ((codedOn canonicalCode).Equivalent Source.a0 Source.a1 ∧
      ¬ (codedOn canonicalCode).Equivalent Source.a0 Source.b0) ∧
    (PositiveWitness.admissible.Representable laws ∧
      ¬ NegativeWitness.admissible.Representable laws) ∧
    (laws.jointKernelReading.NonDiscrete ∧
      ¬ identityReading.NonDiscrete) ∧
    (laws.jointKernelReading.NonTotal ∧
      ¬ totalReading.NonTotal) ∧
    (PositiveWitness.admissible.HasTwoKernelDistinct ∧
      ¬ duplicateKernelAdmissible.HasTwoKernelDistinct) := by
  exact ⟨⟨kernel_positive, kernel_negative⟩,
    ⟨factors_positive, factors_negative⟩,
    ⟨factorsThrough_positive, factorsThrough_negative⟩,
    ⟨coarserThan_positive, coarserThan_negative⟩,
    ⟨kernelEquivalent_positive, kernelEquivalent_negative⟩,
    ⟨equivalent_positive, equivalent_negative⟩,
    ⟨adequate_positive, adequate_negative⟩,
    ⟨doctrineEquivalent_positive, doctrineEquivalent_negative⟩,
    ⟨representable_positive, representable_negative⟩,
    ⟨nonDiscrete_positive, nonDiscrete_negative⟩,
    ⟨nonTotal_positive, nonTotal_negative⟩,
    ⟨hasTwoKernelDistinct_positive, hasTwoKernelDistinct_negative⟩⟩

end InstancePairs

end AAT.AG.CanonicalResolution

#assert_standard_axioms_only AAT.AG.CanonicalResolution.InstancePairs
