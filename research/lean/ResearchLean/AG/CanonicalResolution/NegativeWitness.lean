import ResearchLean.AG.CanonicalResolution.PositiveWitness

/-!
# Nonrepresentability and firing witnesses

This module discharges F4 of `G-103-aat-canonical-resolution`.  It constructs
two explicit proper refinements of the same six-source law kernel.  Both are
adequate and non-discrete, but neither has the canonical kernel.  Separate
theorems prove nonempty and nonconstant laws, a nonidentity and nontotal
canonical quotient, and two kernel-distinct members in both the positive and
negative admissible classes.
-/

namespace AAT.AG.CanonicalResolution

universe u

namespace Reading

variable {Source : Type u}

/-- A reading is non-discrete when it identifies two distinct sources. -/
def NonDiscrete (q : Reading Source) : Prop :=
  ∃ x y, x ≠ y ∧ q.Kernel x y

/-- A reading is nontotal when some pair of sources remains separated. -/
def NonTotal (q : Reading Source) : Prop :=
  ∃ x y, ¬ q.Kernel x y

end Reading

namespace AdmissibleClass

variable {U : AtomCarrier.{u}} {Source : Type u}

/-- A class has two meaningful members when their induced kernels differ. -/
def HasTwoKernelDistinct (admissible : AdmissibleClass U Source) : Prop :=
  ∃ i j : admissible.Index, i ≠ j ∧
    ¬ (admissible.doctrine i).reading.KernelEquivalent
      (admissible.doctrine j).reading

end AdmissibleClass

namespace NegativeWitness

open PositiveWitness

/-- A proper refinement of the second law fiber. -/
def fineCodeB : Source → FiniteModel.FiniteAtom
  | .a0 | .a1 | .a2 => .componentA
  | .b0 => .componentB
  | .b1 | .b2 => .componentC

/-- The two proper-refinement doctrines of the negative class. -/
def doctrine : Bool → DoctrineOn FiniteModel.carrier Source
  | false => codedOn fineCodeA
  | true => codedOn fineCodeB

/-- A two-element class of adequate proper refinements with no canonical member. -/
def admissible : AdmissibleClass FiniteModel.carrier Source where
  Index := Bool
  indexFintype := inferInstance
  doctrine := doctrine

/-- Equality of the first refined signal implies equality of all law values. -/
theorem fineCodeA_eq_implies_laws_equivalent {x y : Source}
    (hxy : fineCodeA x = fineCodeA y) : laws.Equivalent x y := by
  apply (laws_equivalent_iff_canonicalCode_eq x y).2
  cases x <;> cases y <;>
    simp [fineCodeA, canonicalCode] at hxy ⊢

/-- Equality of the second refined signal implies equality of all law values. -/
theorem fineCodeB_eq_implies_laws_equivalent {x y : Source}
    (hxy : fineCodeB x = fineCodeB y) : laws.Equivalent x y := by
  apply (laws_equivalent_iff_canonicalCode_eq x y).2
  cases x <;> cases y <;>
    simp [fineCodeB, canonicalCode] at hxy ⊢

/-- A coded doctrine is adequate whenever its signal refines the law kernel. -/
theorem codedOn_adequate_of_refines (code : Source → FiniteModel.FiniteAtom)
    (hrefines : ∀ ⦃x y⦄, code x = code y → laws.Equivalent x y) :
    laws.Adequate (codedOn code).reading := by
  apply (laws.adequate_iff_kernel (codedOn code).reading).2
  intro x y hxy
  exact hrefines ((codedOn_reading_kernel_iff code x y).1 hxy)

/-- The canonical-code doctrine is adequate. -/
theorem canonicalCode_adequate : laws.Adequate (codedOn canonicalCode).reading :=
  codedOn_adequate_of_refines canonicalCode
    (fun {_x _y} hxy =>
      (laws_equivalent_iff_canonicalCode_eq _ _).2 hxy)

/-- The first proper refinement is adequate. -/
theorem fineCodeA_adequate : laws.Adequate (codedOn fineCodeA).reading :=
  codedOn_adequate_of_refines fineCodeA
    (fun {_x _y} hxy => fineCodeA_eq_implies_laws_equivalent hxy)

/-- The second proper refinement is adequate. -/
theorem fineCodeB_adequate : laws.Adequate (codedOn fineCodeB).reading :=
  codedOn_adequate_of_refines fineCodeB
    (fun {_x _y} hxy => fineCodeB_eq_implies_laws_equivalent hxy)

/-- Every positive class member is adequate. -/
theorem positive_every_member_adequate
    (index : PositiveWitness.admissible.Index) :
    laws.Adequate (PositiveWitness.admissible.doctrine index).reading := by
  cases index with
  | false => exact canonicalCode_adequate
  | true => exact fineCodeA_adequate

/-- Every negative class member is adequate. -/
theorem every_member_adequate (index : admissible.Index) :
    laws.Adequate (admissible.doctrine index).reading := by
  cases index with
  | false => exact fineCodeA_adequate
  | true => exact fineCodeB_adequate

/-- The first proper refinement identifies two distinct sources. -/
theorem fineCodeA_nonDiscrete : (codedOn fineCodeA).reading.NonDiscrete := by
  refine ⟨Source.a1, Source.a2, by decide, ?_⟩
  exact (codedOn_reading_kernel_iff fineCodeA _ _).2 rfl

/-- The second proper refinement identifies two distinct sources. -/
theorem fineCodeB_nonDiscrete : (codedOn fineCodeB).reading.NonDiscrete := by
  refine ⟨Source.a0, Source.a1, by decide, ?_⟩
  exact (codedOn_reading_kernel_iff fineCodeB _ _).2 rfl

/-- Every negative class member is non-discrete. -/
theorem every_member_nonDiscrete (index : admissible.Index) :
    (admissible.doctrine index).reading.NonDiscrete := by
  cases index with
  | false => exact fineCodeA_nonDiscrete
  | true => exact fineCodeB_nonDiscrete

/-- The negative class contains a non-discrete adequate reading. -/
theorem contains_nonDiscrete_adequate :
    ∃ index : admissible.Index,
      laws.Adequate (admissible.doctrine index).reading ∧
        (admissible.doctrine index).reading.NonDiscrete :=
  ⟨false, fineCodeA_adequate, fineCodeA_nonDiscrete⟩

/-- No member of the negative class has the canonical law kernel. -/
theorem every_member_not_kernelEquivalent (index : admissible.Index) :
    ¬ laws.jointKernelReading.KernelEquivalent
      (admissible.doctrine index).reading := by
  cases index with
  | false =>
      change ¬ laws.jointKernelReading.KernelEquivalent
        (codedOn fineCodeA).reading
      intro hkernel
      have hcanonical : laws.jointKernelReading.Kernel Source.a0 Source.a1 :=
        (laws.jointKernel_kernel_iff _ _).2
          ((laws_equivalent_iff_canonicalCode_eq _ _).2 rfl)
      have hrefined := (hkernel Source.a0 Source.a1).1 hcanonical
      exact (by
        rw [codedOn_reading_kernel_iff] at hrefined
        contradiction)
  | true =>
      change ¬ laws.jointKernelReading.KernelEquivalent
        (codedOn fineCodeB).reading
      intro hkernel
      have hcanonical : laws.jointKernelReading.Kernel Source.b0 Source.b1 :=
        (laws.jointKernel_kernel_iff _ _).2
          ((laws_equivalent_iff_canonicalCode_eq _ _).2 rfl)
      have hrefined := (hkernel Source.b0 Source.b1).1 hcanonical
      exact (by
        rw [codedOn_reading_kernel_iff] at hrefined
        contradiction)

/-- The negative admissible class does not represent the canonical resolution. -/
theorem not_representable : ¬ admissible.Representable laws := by
  rintro ⟨index, hkernel⟩
  exact every_member_not_kernelEquivalent index hkernel

/-- The positive class contains two kernel-distinct doctrine readings. -/
theorem positive_hasTwoKernelDistinct :
    PositiveWitness.admissible.HasTwoKernelDistinct := by
  refine ⟨false, true, ?_, ?_⟩
  · change (false : Bool) ≠ true
    decide
  change ¬ (codedOn canonicalCode).reading.KernelEquivalent
    (codedOn fineCodeA).reading
  intro hkernel
  have hcanonical : (codedOn canonicalCode).reading.Kernel
      Source.a0 Source.a1 :=
    (codedOn_reading_kernel_iff canonicalCode _ _).2 rfl
  have hrefined := (hkernel Source.a0 Source.a1).1 hcanonical
  rw [codedOn_reading_kernel_iff] at hrefined
  contradiction

/-- The negative class contains two kernel-distinct doctrine readings. -/
theorem negative_hasTwoKernelDistinct : admissible.HasTwoKernelDistinct := by
  refine ⟨false, true, ?_, ?_⟩
  · change (false : Bool) ≠ true
    decide
  change ¬ (codedOn fineCodeA).reading.KernelEquivalent
    (codedOn fineCodeB).reading
  intro hkernel
  have hsecond : (codedOn fineCodeB).reading.Kernel Source.a0 Source.a1 :=
    (codedOn_reading_kernel_iff fineCodeB _ _).2 rfl
  have hfirst := (hkernel Source.a0 Source.a1).2 hsecond
  rw [codedOn_reading_kernel_iff] at hfirst
  contradiction

/-- The concrete law family has an actual law. -/
theorem laws_nonempty : Nonempty laws.Law :=
  ⟨Law.observedBlock⟩

/-- The actual law evaluation is nonconstant. -/
theorem laws_nonconstant :
    ∃ law x y, laws.eval law x ≠ laws.eval law y :=
  ⟨Law.observedBlock, Source.a0, Source.b0, by decide⟩

/-- The canonical reading is not the identity reading. -/
theorem jointKernel_nonDiscrete : laws.jointKernelReading.NonDiscrete := by
  refine ⟨Source.a0, Source.a1, by decide, ?_⟩
  apply (laws.jointKernel_kernel_iff _ _).2
  exact (laws_equivalent_iff_canonicalCode_eq _ _).2 rfl

/-- The canonical reading does not collapse every source. -/
theorem jointKernel_nonTotal : laws.jointKernelReading.NonTotal := by
  refine ⟨Source.a0, Source.b0, ?_⟩
  rw [laws.jointKernel_kernel_iff,
    laws_equivalent_iff_canonicalCode_eq]
  decide

/-- All required firing conditions hold for the positive instance. -/
theorem positive_firing :
    Nonempty laws.Law ∧
      (∃ law x y, laws.eval law x ≠ laws.eval law y) ∧
      laws.jointKernelReading.NonDiscrete ∧
      laws.jointKernelReading.NonTotal ∧
      PositiveWitness.admissible.HasTwoKernelDistinct :=
  ⟨laws_nonempty, laws_nonconstant, jointKernel_nonDiscrete,
    jointKernel_nonTotal, positive_hasTwoKernelDistinct⟩

/-- All required firing conditions hold for the negative instance. -/
theorem negative_firing :
    Nonempty laws.Law ∧
      (∃ law x y, laws.eval law x ≠ laws.eval law y) ∧
      laws.jointKernelReading.NonDiscrete ∧
      laws.jointKernelReading.NonTotal ∧
      admissible.HasTwoKernelDistinct :=
  ⟨laws_nonempty, laws_nonconstant, jointKernel_nonDiscrete,
    jointKernel_nonTotal, negative_hasTwoKernelDistinct⟩

end NegativeWitness

open PositiveWitness NegativeWitness

/-!
The completion theorem below is an index over the independently proved
construction, universal property, computation theorem, and finite witnesses.
Its proof does not replace any of those material declarations.
-/

/-- The complete five-part theorem package fixed by G-103. -/
theorem finiteCanonicalResolutionRepresentability
    {Source : Type u} [Fintype Source] [DecidableEq Source]
    (laws : FiniteLawFamily Source) :
    laws.Adequate laws.jointKernelReading ∧
      (∀ (q : Reading Source), laws.Adequate q →
        ∃! factor : q.Target → laws.JointKernelQuotient,
          ∀ source, factor (q.read source) =
            laws.jointKernelReading.read source) ∧
      laws.computedReading.KernelEquivalent laws.jointKernelReading ∧
      PositiveWitness.admissible.Representable PositiveWitness.laws ∧
      ¬ NegativeWitness.admissible.Representable PositiveWitness.laws ∧
      (∃ index : NegativeWitness.admissible.Index,
        PositiveWitness.laws.Adequate
            (NegativeWitness.admissible.doctrine index).reading ∧
          (NegativeWitness.admissible.doctrine index).reading.NonDiscrete) ∧
      (Nonempty PositiveWitness.laws.Law ∧
        (∃ law x y, PositiveWitness.laws.eval law x ≠
          PositiveWitness.laws.eval law y) ∧
        PositiveWitness.laws.jointKernelReading.NonDiscrete ∧
        PositiveWitness.laws.jointKernelReading.NonTotal ∧
        PositiveWitness.admissible.HasTwoKernelDistinct) ∧
      (Nonempty PositiveWitness.laws.Law ∧
        (∃ law x y, PositiveWitness.laws.eval law x ≠
          PositiveWitness.laws.eval law y) ∧
        PositiveWitness.laws.jointKernelReading.NonDiscrete ∧
        PositiveWitness.laws.jointKernelReading.NonTotal ∧
        NegativeWitness.admissible.HasTwoKernelDistinct) := by
  refine ⟨laws.jointKernel_adequate, ?_,
    laws.computed_kernelEquivalent_jointKernel,
    PositiveWitness.representable, NegativeWitness.not_representable,
    NegativeWitness.contains_nonDiscrete_adequate,
    NegativeWitness.positive_firing, NegativeWitness.negative_firing⟩
  intro q hq
  exact laws.jointKernel_universal q hq

end AAT.AG.CanonicalResolution

#assert_standard_axioms_only AAT.AG.CanonicalResolution
