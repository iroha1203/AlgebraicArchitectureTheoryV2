import ResearchLean.AG.FullGeometryNormalization.CanonicalNormalizationObjectSection

/-!
# A nontrivial object swap in the ambient normalization kernel

This module constructs the object-level permutation required by G-122(D)'s
ambient-kernel witness.  Three explicit auxiliary decorations allow two of
them to be chosen away from the package-selected decoration at every
configuration.  Swapping those two decorations fixes the selected object,
fixes configurations, is involutive, and is nontrivial.
-/

namespace AAT.AG.FullGeometryNormalization

universe u

open AtomFoundation DoctrineFiberProduct

noncomputable local instance ambientKernelAuxiliaryDecidableEq :
    DecidableEq ArchitectureAuxiliaryData.{u} := Classical.decEq _

/-- First of three explicit auxiliary decorations. -/
def architectureAuxiliaryZero : ArchitectureAuxiliaryData.{u} :=
  ⟨ULift.{u} (Fin 3), ULift.{u} Unit, ULift.up 0, ULift.up ()⟩

/-- Second of three explicit auxiliary decorations. -/
def architectureAuxiliaryOne : ArchitectureAuxiliaryData.{u} :=
  ⟨ULift.{u} (Fin 3), ULift.{u} Unit, ULift.up 1, ULift.up ()⟩

/-- Third of three explicit auxiliary decorations. -/
def architectureAuxiliaryTwo : ArchitectureAuxiliaryData.{u} :=
  ⟨ULift.{u} (Fin 3), ULift.{u} Unit, ULift.up 2, ULift.up ()⟩

/-- The first two explicit auxiliary decorations are distinct. -/
theorem architectureAuxiliaryZero_ne_one :
    architectureAuxiliaryZero.{u} ≠ architectureAuxiliaryOne.{u} := by
  simp [architectureAuxiliaryZero, architectureAuxiliaryOne]

/-- The first and third explicit auxiliary decorations are distinct. -/
theorem architectureAuxiliaryZero_ne_two :
    architectureAuxiliaryZero.{u} ≠ architectureAuxiliaryTwo.{u} := by
  simp [architectureAuxiliaryZero, architectureAuxiliaryTwo]

/-- The second and third explicit auxiliary decorations are distinct. -/
theorem architectureAuxiliaryOne_ne_two :
    architectureAuxiliaryOne.{u} ≠ architectureAuxiliaryTwo.{u} := by
  simp [architectureAuxiliaryOne, architectureAuxiliaryTwo]

/-- First auxiliary decoration selected away from `d`. -/
noncomputable def ambientKernelFirst
    (d : ArchitectureAuxiliaryData.{u}) : ArchitectureAuxiliaryData.{u} :=
  if d = architectureAuxiliaryZero then architectureAuxiliaryOne
  else architectureAuxiliaryZero

/-- Second auxiliary decoration selected away from `d` and from the first. -/
noncomputable def ambientKernelSecond
    (d : ArchitectureAuxiliaryData.{u}) : ArchitectureAuxiliaryData.{u} :=
  if d = architectureAuxiliaryTwo then architectureAuxiliaryOne
  else architectureAuxiliaryTwo

/-- The first chosen decoration avoids `d`. -/
theorem ambientKernelFirst_ne
    (d : ArchitectureAuxiliaryData.{u}) : ambientKernelFirst d ≠ d := by
  classical
  by_cases hzero : d = architectureAuxiliaryZero
  · simp [ambientKernelFirst, hzero, architectureAuxiliaryZero_ne_one.symm]
  · rw [ambientKernelFirst, if_neg hzero]
    exact fun h => hzero h.symm

/-- The second chosen decoration avoids `d`. -/
theorem ambientKernelSecond_ne
    (d : ArchitectureAuxiliaryData.{u}) : ambientKernelSecond d ≠ d := by
  classical
  by_cases htwo : d = architectureAuxiliaryTwo
  · simp [ambientKernelSecond, htwo, architectureAuxiliaryOne_ne_two]
  · rw [ambientKernelSecond, if_neg htwo]
    exact fun h => htwo h.symm

/-- The two chosen decorations are distinct. -/
theorem ambientKernelFirst_ne_second
    (d : ArchitectureAuxiliaryData.{u}) :
    ambientKernelFirst d ≠ ambientKernelSecond d := by
  classical
  by_cases hzero : d = architectureAuxiliaryZero
  · rw [ambientKernelFirst, if_pos hzero]
    rw [ambientKernelSecond, if_neg (fun h =>
      architectureAuxiliaryZero_ne_two (hzero.symm.trans h))]
    exact architectureAuxiliaryOne_ne_two
  · by_cases htwo : d = architectureAuxiliaryTwo
    · rw [ambientKernelFirst, if_neg hzero]
      rw [ambientKernelSecond, if_pos htwo]
      exact architectureAuxiliaryZero_ne_one
    · rw [ambientKernelFirst, if_neg hzero]
      rw [ambientKernelSecond, if_neg htwo]
      exact architectureAuxiliaryZero_ne_two

/-- Configurationwise auxiliary permutation swapping two decorations away
from the package-selected decoration. -/
noncomputable def ambientKernelAuxiliaryEquiv
    {U : AtomCarrier.{u}} (P : AATCorePackage U)
    (C : AtomConfiguration U) :
    ArchitectureAuxiliaryData.{u} ≃ ArchitectureAuxiliaryData.{u} :=
  Equiv.swap
    (ambientKernelFirst (selectedArchitectureAuxiliaryData P C))
    (ambientKernelSecond (selectedArchitectureAuxiliaryData P C))

/-- The auxiliary kernel permutation fixes the package-selected decoration. -/
theorem ambientKernelAuxiliaryEquiv_selected
    {U : AtomCarrier.{u}} (P : AATCorePackage U)
    (C : AtomConfiguration U) :
    ambientKernelAuxiliaryEquiv P C
        (selectedArchitectureAuxiliaryData P C) =
      selectedArchitectureAuxiliaryData P C := by
  unfold ambientKernelAuxiliaryEquiv
  exact Equiv.swap_apply_of_ne_of_ne
    (ambientKernelFirst_ne _).symm (ambientKernelSecond_ne _).symm

/-- Presentation-level ambient-kernel object permutation. -/
noncomputable def ambientKernelPresentationMap
    {U : AtomCarrier.{u}} (P : AATCorePackage U)
    (A : Σ _configuration : AtomConfiguration U,
      ArchitectureAuxiliaryData.{u}) :
    Σ _configuration : AtomConfiguration U, ArchitectureAuxiliaryData.{u} :=
  ⟨A.1, ambientKernelAuxiliaryEquiv P A.1 A.2⟩

/-- Raw architecture-object permutation underlying the ambient-kernel
witness. -/
noncomputable def ambientKernelObjectMap
    {U : AtomCarrier.{u}} (P : AATCorePackage U) :
    ArchitectureObject U → ArchitectureObject U :=
  (architectureObjectPresentation U).symm ∘
    ambientKernelPresentationMap P ∘ architectureObjectPresentation U

/-- The ambient-kernel object permutation fixes configurations. -/
@[simp]
theorem ambientKernelObjectMap_configuration
    {U : AtomCarrier.{u}} (P : AATCorePackage U)
    (A : ArchitectureObject U) :
    (ambientKernelObjectMap P A).configuration = A.configuration := by
  rfl

/-- The ambient-kernel object permutation fixes every package-selected
object. -/
theorem ambientKernelObjectMap_selected
    {U : AtomCarrier.{u}} (P : AATCorePackage U)
    (C : AtomConfiguration U) :
    ambientKernelObjectMap P (P.reading.objectReading.object C) =
      P.reading.objectReading.object C := by
  apply (architectureObjectPresentation U).injective
  simp only [ambientKernelObjectMap, Function.comp_apply, Equiv.apply_symm_apply]
  rw [architectureObjectPresentation_selected]
  simp only [ambientKernelPresentationMap]
  rw [ambientKernelAuxiliaryEquiv_selected]

/-- The ambient-kernel object permutation is involutive. -/
theorem ambientKernelObjectMap_involutive
    {U : AtomCarrier.{u}} (P : AATCorePackage U) :
    ambientKernelObjectMap P ∘ ambientKernelObjectMap P = _root_.id := by
  funext A
  apply (architectureObjectPresentation U).injective
  simp only [ambientKernelObjectMap, Function.comp_apply, Equiv.apply_symm_apply,
    ambientKernelPresentationMap]
  change
    ⟨(architectureObjectPresentation U A).1,
      ambientKernelAuxiliaryEquiv P (architectureObjectPresentation U A).1
        (ambientKernelAuxiliaryEquiv P (architectureObjectPresentation U A).1
          (architectureObjectPresentation U A).2)⟩ =
      architectureObjectPresentation U A
  generalize hX : architectureObjectPresentation U A = X
  rcases X with ⟨C, d⟩
  simp only
  unfold ambientKernelAuxiliaryEquiv
  rw [Equiv.swap_apply_self]

/-- A concrete object moved by the ambient-kernel permutation. -/
noncomputable def ambientKernelMovedObject
    {U : AtomCarrier.{u}} (P : AATCorePackage U) : ArchitectureObject U :=
  (architectureObjectPresentation U).symm
    ⟨P.configuration,
      ambientKernelFirst (selectedArchitectureAuxiliaryData P P.configuration)⟩

/-- The ambient-kernel object permutation is genuinely nonidentity. -/
theorem ambientKernelObjectMap_ne_id
    {U : AtomCarrier.{u}} (P : AATCorePackage U) :
    ambientKernelObjectMap P ≠ _root_.id := by
  intro h
  have moved := congrFun h (ambientKernelMovedObject P)
  have presented := congrArg (architectureObjectPresentation U) moved
  have auxiliary :
      ambientKernelSecond
          (selectedArchitectureAuxiliaryData P P.configuration) =
        ambientKernelFirst
          (selectedArchitectureAuxiliaryData P P.configuration) := by
    simpa [ambientKernelMovedObject, ambientKernelObjectMap,
      ambientKernelPresentationMap, ambientKernelAuxiliaryEquiv] using
        congrArg Sigma.snd presented
  exact (ambientKernelFirst_ne_second _).symm auxiliary

/-- Canonical object normalization kills the ambient-kernel object
permutation pointwise. -/
theorem canonicalObjectNormalization_ambientKernelObjectMap
    {U : AtomCarrier.{u}} (P : AATCorePackage U)
    (A : ArchitectureObject U) :
    canonicalObjectNormalization P (ambientKernelObjectMap P A) =
      canonicalObjectNormalization P A := by
  unfold canonicalObjectNormalization
  rw [ambientKernelObjectMap_configuration]

#assert_standard_axioms_only AAT.AG.FullGeometryNormalization

end AAT.AG.FullGeometryNormalization
