import Formal.AG.Examples.FiniteModel
import ResearchLean.AG.CanonicalResolution.Admissible

/-!
# A finite positive representability witness

This module completes the concrete part of F3 for
`G-103-aat-canonical-resolution`.  The source, law, and doctrine signals are
explicit finite data over `FiniteModel.carrier`.  One doctrine reading has the
same kernel as the joint-law quotient; a second, strictly finer signal is kept
for the nondegeneracy audit in F4.
-/

namespace AAT.AG.CanonicalResolution

namespace PositiveWitness

open FiniteModel

/-- Six sources supporting nontrivial coarse and refined readings. -/
inductive Source where
  | a0 | a1 | a2
  | b0 | b1 | b2
  deriving DecidableEq

namespace Source

/-- Explicit enumeration of the six witness sources. -/
def all : List Source := [.a0, .a1, .a2, .b0, .b1, .b2]

/-- The source enumeration is exhaustive. -/
theorem mem_all (source : Source) : source ∈ all := by
  cases source <;> simp [all]

instance : Fintype Source := Fintype.ofList all mem_all

end Source

/-- The nonempty finite law index of the witness. -/
inductive Law where
  | observedBlock
  deriving DecidableEq

namespace Law

/-- Explicit enumeration of the witness law index. -/
def all : List Law := [.observedBlock]

/-- The law enumeration is exhaustive. -/
theorem mem_all (law : Law) : law ∈ all := by
  cases law
  simp [all]

instance : Fintype Law := Fintype.ofList all mem_all

end Law

/-- The source signal observed by the witness law. -/
def lawValue : Source → Bool
  | .a0 | .a1 | .a2 => false
  | .b0 | .b1 | .b2 => true

/-- The one-law finite family whose two fibers are both non-singleton. -/
def laws : FiniteLawFamily Source where
  Law := Law
  lawFintype := inferInstance
  Value := fun _ => Bool
  valueDecidableEq := fun _ => inferInstance
  eval := fun _ source => lawValue source

/-- The two-Atom signal matching the law fibers. -/
def canonicalCode : Source → FiniteAtom
  | .a0 | .a1 | .a2 => .componentA
  | .b0 | .b1 | .b2 => .componentB

/-- A proper refinement of the first law fiber. -/
def fineCodeA : Source → FiniteAtom
  | .a0 => .componentA
  | .a1 | .a2 => .componentC
  | .b0 | .b1 | .b2 => .componentB

/-- An extraction doctrine generated from a source-to-Atom signal. -/
def codedDoctrine (code : Source → FiniteAtom) :
    ExtractionDoctrine FiniteModel.carrier where
  Source := Source
  Vocabulary := PUnit
  SemanticReading := PUnit
  Resolution := PUnit
  vocabulary := PUnit.unit
  semanticReading := PUnit.unit
  resolution := PUnit.unit
  vocabularyAllows := fun _ _ => True
  semanticAllows := fun _ _ _ => True
  resolutionAllows := fun _ _ _ => True
  sourceSemantics := fun source atom => atom = code source
  normalize := id

/-- A coded doctrine as an actual doctrine on the fixed witness source. -/
def codedOn (code : Source → FiniteAtom) :
    DoctrineOn FiniteModel.carrier Source where
  doctrine := codedDoctrine code
  source_eq := rfl

/-- Coded extraction is exactly membership in the selected singleton signal. -/
theorem codedOn_extractedAtoms_mem_iff (code : Source → FiniteAtom)
    (source : Source) (atom : FiniteAtom) :
    atom ∈ (codedOn code).extractedAtoms source ↔ atom = code source := by
  simp [DoctrineOn.extractedAtoms, DoctrineOn.castSource, codedOn,
    codedDoctrine, ExtractionDoctrine.extracts]

/-- The coded doctrine reading kernel is equality of source signals. -/
theorem codedOn_reading_kernel_iff (code : Source → FiniteAtom)
    (x y : Source) :
    (codedOn code).reading.Kernel x y ↔ code x = code y := by
  rw [DoctrineOn.reading_kernel_iff]
  constructor
  · intro hsets
    have hx : code x ∈ (codedOn code).extractedAtoms x :=
      (codedOn_extractedAtoms_mem_iff code x (code x)).2 rfl
    have hy : code x ∈ (codedOn code).extractedAtoms y := by
      rw [← hsets]
      exact hx
    exact (codedOn_extractedAtoms_mem_iff code y (code x)).1 hy
  · intro hcode
    apply Set.ext
    intro atom
    rw [codedOn_extractedAtoms_mem_iff, codedOn_extractedAtoms_mem_iff,
      hcode]

/-- The law kernel is equality of the explicit Boolean signal. -/
theorem laws_equivalent_iff_lawValue_eq (x y : Source) :
    laws.Equivalent x y ↔ lawValue x = lawValue y := by
  constructor
  · intro h
    exact h Law.observedBlock
  · intro h law
    cases law
    exact h

/-- Equality of the law signal is exactly equality of the canonical Atom signal. -/
theorem lawValue_eq_iff_canonicalCode_eq (x y : Source) :
    lawValue x = lawValue y ↔ canonicalCode x = canonicalCode y := by
  cases x <;> cases y <;> decide

/-- The law kernel and canonical doctrine signal coincide. -/
theorem laws_equivalent_iff_canonicalCode_eq (x y : Source) :
    laws.Equivalent x y ↔ canonicalCode x = canonicalCode y :=
  (laws_equivalent_iff_lawValue_eq x y).trans
    (lawValue_eq_iff_canonicalCode_eq x y)

/-- The two-element positive doctrine family. -/
def doctrine : Bool → DoctrineOn FiniteModel.carrier Source
  | false => codedOn canonicalCode
  | true => codedOn fineCodeA

/-- A finite admissible class containing the canonical and refined readings. -/
def admissible : AdmissibleClass FiniteModel.carrier Source where
  Index := Bool
  indexFintype := inferInstance
  doctrine := doctrine

/-- The canonical doctrine member has exactly the joint-law kernel. -/
theorem canonical_member_kernelEquivalent :
    laws.jointKernelReading.KernelEquivalent
      (admissible.doctrine false).reading := by
  intro x y
  change laws.jointKernelReading.Kernel x y ↔
    (codedOn canonicalCode).reading.Kernel x y
  exact (laws.jointKernel_kernel_iff x y).trans
    ((laws_equivalent_iff_canonicalCode_eq x y).trans
      (codedOn_reading_kernel_iff canonicalCode x y).symm)

/-- The finite doctrine class positively represents the canonical resolution. -/
theorem representable : admissible.Representable laws :=
  ⟨false, canonical_member_kernelEquivalent⟩

end PositiveWitness

end AAT.AG.CanonicalResolution

#assert_standard_axioms_only AAT.AG.CanonicalResolution
