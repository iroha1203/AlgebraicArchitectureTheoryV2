import ResearchLean.AG.DoctrineFiberProduct.BCDiagnosticAxisFoldComparisonWitnesses

/-!
# Swap-symmetric orbit-local axis-fold no-go on the fixed lax witness

The authored comparator on the lax second face is the adjacent transposition of
the first two axes. If an axis operation commutes with that transposition and
stays inside its orbits, then it is injective: on the two-element orbit
it can only be the identity or the transposition, and it fixes the remaining
singleton orbit.

The noninvertible one-axis fold from the earlier diagnostic checkpoint fails
this equivariance condition. Its collapse therefore depends on an orientation
of the symmetric two-cycle.

This is a scoped conditional no-go for a swap-symmetric, orbit-local repair of
that fold route. Neither equivariance nor orbit locality is derived here from
the GOAL's presentation-replacement requirement or from comparator-only
provenance. Injectivity of the axis map is not promoted to categorical
invertibility, and the theorem does not classify unrelated K2 producers.
-/

namespace AAT.AG.DoctrineFiberProduct

open CategoryTheory
open AtomFoundation TransportCoherence

/-- The axis action of the authored adjacent transposition. -/
def finiteAxisFoldAuthoredSwapAxis : Fin 3 → Fin 3 :=
  Equiv.swap (0 : Fin 3) 1

/-- Equivariance under the supplied authored transposition. -/
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
Every swap-equivariant, swap-orbit-local operation on the fixed
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

/-- The axis action of an arbitrary fold witness for the fixed authored swap. -/
noncomputable def finiteAxisFoldWitnessAxisMap
    (witness : PackageFiberAut.AxisFoldWitness finiteAxisFoldSwap) :
    Fin 3 → Fin 3 :=
  witness.axisMap

/-- Every oriented fold witness for the fixed swap is orbit-local. -/
theorem finiteAxisFoldWitness_orbitLocal
    (witness : PackageFiberAut.AxisFoldWitness finiteAxisFoldSwap) :
    FiniteAxisFoldSwapOrbitLocal (finiteAxisFoldWitnessAxisMap witness) := by
  intro axis
  by_cases equality : axis = witness.source
  · subst axis
    right
    unfold finiteAxisFoldWitnessAxisMap
    rw [PackageFiberAut.AxisFoldWitness.axisMap_source]
    rfl
  · left
    exact PackageFiberAut.AxisFoldWitness.axisMap_of_ne
      witness axis equality

/-- Every oriented fold witness for the fixed swap breaks swap equivariance. -/
theorem finiteAxisFoldWitness_not_equivariant
    (witness : PackageFiberAut.AxisFoldWitness finiteAxisFoldSwap) :
    ¬ FiniteAxisFoldSwapEquivariant (finiteAxisFoldWitnessAxisMap witness) := by
  intro equivariant
  have moved :
      finiteAxisFoldAuthoredSwapAxis witness.source ≠ witness.source := by
    simpa [finiteAxisFoldAuthoredSwapAxis, finiteAxisFoldSwap,
      finiteAxisFoldSwapTotal, finiteAxisFoldPermutationTotal,
      finiteAxisFoldPermutationUpper] using witness.moved
  have sourceImage :
      finiteAxisFoldWitnessAxisMap witness witness.source =
        finiteAxisFoldAuthoredSwapAxis witness.source := by
    unfold finiteAxisFoldWitnessAxisMap
    rw [PackageFiberAut.AxisFoldWitness.axisMap_source]
    rfl
  have imageImage :
      finiteAxisFoldWitnessAxisMap witness
          (finiteAxisFoldAuthoredSwapAxis witness.source) =
        finiteAxisFoldAuthoredSwapAxis witness.source := by
    unfold finiteAxisFoldWitnessAxisMap
    exact PackageFiberAut.AxisFoldWitness.axisMap_of_ne witness _ moved
  have atSource := equivariant witness.source
  rw [imageImage, sourceImage] at atSource
  apply moved
  simpa [finiteAxisFoldAuthoredSwapAxis] using atSource

/-- The actual choice-based generator's axis action on the fixed swap. -/
noncomputable def finiteAxisFoldGeneratedAxisMap : Fin 3 → Fin 3 :=
  (PackageFiberAut.generatedAxisFoldTotal finiteAxisFoldSwap).upper.axisMap

/-- The generator uses one of the oriented witnesses whose existence is fixed. -/
theorem finiteAxisFoldGeneratedAxisMap_eq_chosen :
    finiteAxisFoldGeneratedAxisMap =
      finiteAxisFoldWitnessAxisMap
        (Classical.choice finiteAxisFoldSwap_available) := by
  funext axis
  unfold finiteAxisFoldGeneratedAxisMap finiteAxisFoldWitnessAxisMap
  rw [PackageFiberAut.generatedAxisFoldTotal,
    dif_pos finiteAxisFoldSwap_available]
  rfl

/-- The actual choice-based generator is orbit-local. -/
theorem finiteAxisFoldGeneratedAxisMap_orbitLocal :
    FiniteAxisFoldSwapOrbitLocal finiteAxisFoldGeneratedAxisMap := by
  rw [finiteAxisFoldGeneratedAxisMap_eq_chosen]
  exact finiteAxisFoldWitness_orbitLocal _

/-- The actual choice-based generator cannot be swap-equivariant. -/
theorem finiteAxisFoldGeneratedAxisMap_not_equivariant :
    ¬ FiniteAxisFoldSwapEquivariant finiteAxisFoldGeneratedAxisMap := by
  rw [finiteAxisFoldGeneratedAxisMap_eq_chosen]
  exact finiteAxisFoldWitness_not_equivariant _

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
The concrete one-axis fold is not swap-equivariant: selecting axis zero
as the source distinguishes the two symmetric orientations of the swap orbit.
-/
theorem finiteAxisFoldSwapWitness_not_equivariant :
    ¬ FiniteAxisFoldSwapEquivariant finiteAxisFoldSwapWitnessAxisMap := by
  intro equivariant
  have atZero := equivariant (0 : Fin 3)
  simp [finiteAxisFoldAuthoredSwapAxis,
    finiteAxisFoldSwapWitness_axisMap_zero,
    finiteAxisFoldSwapWitness_axisMap_one] at atZero

/-- Identity is a positive control for swap equivariance. -/
theorem finiteAxisFoldSwapEquivariant_id :
    FiniteAxisFoldSwapEquivariant id := by
  intro axis
  rfl

/-- The constant-zero map is a negative control for swap-orbit locality. -/
theorem finiteAxisFoldSwapOrbitLocal_not_constZero :
    ¬ FiniteAxisFoldSwapOrbitLocal (fun _ : Fin 3 => 0) := by
  intro orbitLocal
  have atTwo := orbitLocal (2 : Fin 3)
  simp [finiteAxisFoldAuthoredSwapAxis] at atTwo
  exact ((by decide : (0 : Fin 3) ≠ 2) atTwo).elim

/-- The previous noninjective fold fires the abstract no-go concretely. -/
theorem finiteAxisFoldSwapWitness_invariance_noGo :
    ¬ (FiniteAxisFoldSwapEquivariant finiteAxisFoldSwapWitnessAxisMap ∧
      FiniteAxisFoldSwapOrbitLocal finiteAxisFoldSwapWitnessAxisMap) :=
  finiteAxisFold_not_swapEquivariant_and_orbitLocal_of_not_injective
    finiteAxisFoldSwapWitnessAxisMap
    finiteAxisFoldSwapWitness.not_injective_axisMap

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
