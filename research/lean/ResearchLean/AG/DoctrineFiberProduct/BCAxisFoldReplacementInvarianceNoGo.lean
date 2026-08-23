import ResearchLean.AG.DoctrineFiberProduct.BCDiagnosticAxisFoldComparisonWitnesses

/-!
# Replacement-invariant axis-fold no-go on the fixed lax witness

The authored comparator on the lax second face is the adjacent transposition of
the first two axes. A comparator-only axis operation that is invariant under
that relabelling must commute with the transposition. If it also stays inside
the supplied comparator orbit, then it is injective: on the two-element orbit
it can only be the identity or the transposition, and it fixes the remaining
singleton orbit.

The noninvertible one-axis fold from the earlier diagnostic checkpoint fails
this equivariance condition. Its collapse therefore depends exactly on an
orientation of the symmetric two-cycle; hiding the orientation behind
`Classical.choice` does not turn it into a replacement-invariant construction.

This is a scoped no-go for repairing that fold route. Injectivity of the axis
map is not promoted to categorical invertibility, and the theorem does not
classify unrelated K2 producers.
-/

namespace AAT.AG.DoctrineFiberProduct

open CategoryTheory
open AtomFoundation TransportCoherence

/-- The axis action of the authored adjacent transposition. -/
def finiteAxisFoldAuthoredSwapAxis : Fin 3 → Fin 3 :=
  Equiv.swap (0 : Fin 3) 1

/-- Invariance under replacement by the supplied authored transposition. -/
def FiniteAxisFoldSwapEquivariant (axisMap : Fin 3 → Fin 3) : Prop :=
  ∀ axis,
    axisMap (finiteAxisFoldAuthoredSwapAxis axis) =
      finiteAxisFoldAuthoredSwapAxis (axisMap axis)

/-- The operation introduces no axis outside the orbit supplied by the comparator. -/
def FiniteAxisFoldSwapOrbitLocal (axisMap : Fin 3 → Fin 3) : Prop :=
  ∀ axis,
    axisMap axis = axis ∨
      axisMap axis = finiteAxisFoldAuthoredSwapAxis axis

/--
Every replacement-equivariant, comparator-orbit-local operation on the fixed
three-axis witness is injective.
-/
theorem finiteAxisFold_swapEquivariant_orbitLocal_injective
    (axisMap : Fin 3 → Fin 3)
    (equivariant : FiniteAxisFoldSwapEquivariant axisMap)
    (orbitLocal : FiniteAxisFoldSwapOrbitLocal axisMap) :
    Function.Injective axisMap := by
  have imageZero := orbitLocal (0 : Fin 3)
  have imageTwo := orbitLocal (2 : Fin 3)
  have commuteZero := equivariant (0 : Fin 3)
  simp only [finiteAxisFoldAuthoredSwapAxis, Equiv.swap_apply_def] at imageZero imageTwo commuteZero
  rcases imageZero with imageZero | imageZero
  · have imageOne : axisMap 1 = 1 := by
      simpa [imageZero] using commuteZero
    have imageTwo' : axisMap 2 = 2 := by
      rcases imageTwo with imageTwo | imageTwo <;> simpa using imageTwo
    intro first second equality
    fin_cases first <;> fin_cases second <;> simp_all
  · have imageOne : axisMap 1 = 0 := by
      simpa [imageZero] using commuteZero
    have imageTwo' : axisMap 2 = 2 := by
      rcases imageTwo with imageTwo | imageTwo <;> simpa using imageTwo
    intro first second equality
    fin_cases first <;> fin_cases second <;> simp_all

/-- No noninjective axis operation can satisfy both invariance and orbit locality. -/
theorem finiteAxisFold_not_swapEquivariant_and_orbitLocal_of_not_injective
    (axisMap : Fin 3 → Fin 3)
    (notInjective : ¬ Function.Injective axisMap) :
    ¬ (FiniteAxisFoldSwapEquivariant axisMap ∧
      FiniteAxisFoldSwapOrbitLocal axisMap) := by
  rintro ⟨equivariant, orbitLocal⟩
  exact notInjective
    (finiteAxisFold_swapEquivariant_orbitLocal_injective axisMap
      equivariant orbitLocal)

/-- The concrete witness axis action, exposed at its `Fin 3` presentation. -/
noncomputable def finiteAxisFoldSwapWitnessAxisMap : Fin 3 → Fin 3 :=
  finiteAxisFoldSwapWitness.axisMap

/-- The oriented fold sends axis zero to axis one. -/
theorem finiteAxisFoldSwapWitness_axisMap_zero :
    finiteAxisFoldSwapWitnessAxisMap 0 = 1 := by
  unfold finiteAxisFoldSwapWitnessAxisMap
    PackageFiberAut.AxisFoldWitness.axisMap
  split
  · rfl
  · contradiction

/-- The oriented fold fixes axis one. -/
theorem finiteAxisFoldSwapWitness_axisMap_one :
    finiteAxisFoldSwapWitnessAxisMap 1 = 1 := by
  unfold finiteAxisFoldSwapWitnessAxisMap
    PackageFiberAut.AxisFoldWitness.axisMap
  split
  · rename_i equality _
    rw [show finiteAxisFoldSwapWitness.source = (0 : Fin 3) by rfl] at equality
    exact ((by decide : (1 : Fin 3) ≠ 0) equality).elim
  · rfl

/-- The oriented fold fixes axis two. -/
theorem finiteAxisFoldSwapWitness_axisMap_two :
    finiteAxisFoldSwapWitnessAxisMap 2 = 2 := by
  unfold finiteAxisFoldSwapWitnessAxisMap
    PackageFiberAut.AxisFoldWitness.axisMap
  split
  · rename_i equality _
    rw [show finiteAxisFoldSwapWitness.source = (0 : Fin 3) by rfl] at equality
    exact ((by decide : (2 : Fin 3) ≠ 0) equality).elim
  · rfl

/-- The concrete one-axis fold stays inside the authored swap orbit. -/
theorem finiteAxisFoldSwapWitness_orbitLocal :
    FiniteAxisFoldSwapOrbitLocal finiteAxisFoldSwapWitnessAxisMap := by
  intro axis
  fin_cases axis <;>
    simp [finiteAxisFoldAuthoredSwapAxis,
      finiteAxisFoldSwapWitness_axisMap_zero,
      finiteAxisFoldSwapWitness_axisMap_one,
      finiteAxisFoldSwapWitness_axisMap_two]

/--
The concrete one-axis fold is not replacement-equivariant: selecting axis zero
as the source distinguishes the two symmetric orientations of the swap orbit.
-/
theorem finiteAxisFoldSwapWitness_not_equivariant :
    ¬ FiniteAxisFoldSwapEquivariant finiteAxisFoldSwapWitnessAxisMap := by
  intro equivariant
  have atZero := equivariant (0 : Fin 3)
  simp [finiteAxisFoldAuthoredSwapAxis,
    finiteAxisFoldSwapWitness_axisMap_zero,
    finiteAxisFoldSwapWitness_axisMap_one] at atZero

/-- The previous noninjective fold fires the abstract no-go concretely. -/
theorem finiteAxisFoldSwapWitness_invariance_noGo :
    ¬ (FiniteAxisFoldSwapEquivariant finiteAxisFoldSwapWitnessAxisMap ∧
      FiniteAxisFoldSwapOrbitLocal finiteAxisFoldSwapWitnessAxisMap) :=
  finiteAxisFold_not_swapEquivariant_and_orbitLocal_of_not_injective
    finiteAxisFoldSwapWitnessAxisMap
    finiteAxisFoldSwapWitness.not_injective_axisMap

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
