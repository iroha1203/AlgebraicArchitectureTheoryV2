import ResearchLean.AG.LocalSemanticReconstruction.G122DisplayedKernelGroupTorsor
import Formal.Util.AssertStandardAxioms

/-!
# Dependent reconstruction of the displayed G-122 lift bundle

The four-component comparison code and the source-owned kernel group code are
assembled together into the dependent total space of all represented
comparisons and their displayed lifts.  The construction supplies both
inverse laws rather than merely pairing two pointwise uniqueness statements.

On every represented comparison, the actual generated kernel subgroup acts
on the displayed lift image.  This action agrees on underlying actual lifts
with the ambient restriction-kernel action, is free and transitive, and is
equivariantly identified with left multiplication on the source group code.

The result concerns the displayed two-point subbundle.  It does not classify
the full restriction kernel, arbitrary comparison fibers, or arbitrary G-122
Homs.
-/

namespace AAT.AG.LocalSemanticReconstruction.G122DisplayedFiberBundleReconstruction

open CategoryTheory AtomFoundation DoctrineFiberProduct GeometryTransport
open TransportCoherence FullGeometryNormalization
open AAT.AG.RealizationReconstruction MulAction Set Subgroup

noncomputable section

open G122FourComponentComparisonLocalModel
open G122DisplayedKernelLiftLocalModel
open G122DisplayedKernelGroupTorsor

/-- One displayed fiber over a represented four-component comparison. -/
abbrev DisplayedFiber (comparison : LocalComparisonImage) :=
  DisplayedLiftImage comparison

/-- Package the orbit lift of one source group code in the accepted displayed
fiber. -/
noncomputable def orbitPoint (comparison : LocalComparisonImage)
    (code : GroupCode) : DisplayedFiber comparison :=
  ⟨orbitLift comparison code, by
    change orbitLift comparison code ∈ DisplayedLiftImage comparison
    rw [← orbitLift_range_eq_displayedLiftImage]
    exact ⟨code, rfl⟩⟩

/-- Packaging an orbit point does not change its underlying actual lift. -/
@[simp] theorem orbitPoint_val (comparison : LocalComparisonImage)
    (code : GroupCode) :
    (orbitPoint comparison code).1 = orbitLift comparison code :=
  rfl

/-- Source group codes remain separated after packaging in the displayed
fiber. -/
theorem orbitPoint_injective (comparison : LocalComparisonImage) :
    Function.Injective (orbitPoint comparison) := by
  intro first second equality
  apply orbitLift_injective comparison
  exact congrArg Subtype.val equality

/-- Every accepted displayed lift is reached by one source group code. -/
theorem orbitPoint_surjective (comparison : LocalComparisonImage) :
    Function.Surjective (orbitPoint comparison) := by
  intro point
  have membership : point.1 ∈ Set.range (orbitLift comparison) := by
    rw [orbitLift_range_eq_displayedLiftImage]
    exact point.2
  rcases membership with ⟨code, equality⟩
  exact ⟨code, Subtype.ext equality⟩

/-- Every displayed fiber is equivalent to the independent source group
code, with actual orbit evaluation as the forward map. -/
noncomputable def orbitPointEquiv (comparison : LocalComparisonImage) :
    GroupCode ≃ DisplayedFiber comparison :=
  Equiv.ofBijective (orbitPoint comparison)
    ⟨orbitPoint_injective comparison, orbitPoint_surjective comparison⟩

/-- Reading an assembled orbit point recovers its source group code. -/
@[simp] theorem orbitPointEquiv_symm_orbitPoint
    (comparison : LocalComparisonImage) (code : GroupCode) :
    (orbitPointEquiv comparison).symm (orbitPoint comparison code) = code :=
  (orbitPointEquiv comparison).symm_apply_apply code

/-- Assembling a read orbit code recovers the displayed point. -/
@[simp] theorem orbitPoint_orbitPointEquiv_symm
    (comparison : LocalComparisonImage) (point : DisplayedFiber comparison) :
    orbitPoint comparison ((orbitPointEquiv comparison).symm point) = point :=
  (orbitPointEquiv comparison).apply_symm_apply point

/-- Multiplicative subgroup readback preserves the identity. -/
@[simp] theorem subgroupRead_one :
    read (1 : ActualSubgroup) = 1 :=
  sourceActualMulEquiv.symm.map_one

/-- Multiplicative subgroup readback preserves products. -/
@[simp] theorem subgroupRead_mul (first second : ActualSubgroup) :
    read (first * second) = read first * read second :=
  sourceActualMulEquiv.symm.map_mul first second

/-- Transport left multiplication by the actual generated subgroup to one
displayed fiber through source-code readback. -/
noncomputable def fiberAction (comparison : LocalComparisonImage)
    (value : ActualSubgroup) (point : DisplayedFiber comparison) :
    DisplayedFiber comparison :=
  orbitPoint comparison
    (read value * (orbitPointEquiv comparison).symm point)

noncomputable instance displayedFiberSMul
    (comparison : LocalComparisonImage) :
    SMul ActualSubgroup (DisplayedFiber comparison) :=
  ⟨fiberAction comparison⟩

/-- The transported operation is a genuine group action on every displayed
fiber. -/
noncomputable instance displayedFiberMulAction
    (comparison : LocalComparisonImage) :
    MulAction ActualSubgroup (DisplayedFiber comparison) where
  one_smul point := by
    change orbitPoint comparison
      (read (1 : ActualSubgroup) *
        (orbitPointEquiv comparison).symm point) = point
    rw [subgroupRead_one, one_mul,
      orbitPoint_orbitPointEquiv_symm]
  mul_smul first second point := by
    change fiberAction comparison (first * second) point =
      fiberAction comparison first (fiberAction comparison second point)
    simp only [fiberAction]
    rw [orbitPointEquiv_symm_orbitPoint, subgroupRead_mul, mul_assoc]

/-- The displayed-fiber action is exactly the ambient actual kernel action on
underlying lifts. -/
theorem fiberAction_val (comparison : LocalComparisonImage)
    (value : ActualSubgroup) (point : DisplayedFiber comparison) :
    (value • point).1 = value.1 • point.1 := by
  let code := (orbitPointEquiv comparison).symm point
  have valueEquality : evaluate (read value) = value.1 := by
    exact congrArg Subtype.val (assemble_read value)
  have pointEquality : orbitLift comparison code = point.1 := by
    exact congrArg Subtype.val
      (orbitPoint_orbitPointEquiv_symm comparison point)
  change orbitLift comparison (read value * code) = value.1 • point.1
  calc
    orbitLift comparison (read value * code) =
        evaluate (read value) • orbitLift comparison code := by
      simp only [orbitLift, evaluate_mul, mul_smul]
    _ = value.1 • orbitLift comparison code := by rw [valueEquality]
    _ = value.1 • point.1 := congrArg (fun lift => value.1 • lift) pointEquality

/-- Actual subgroup multiplication on displayed points is equivariant with
left multiplication on source group codes. -/
theorem fiberAction_orbitPoint (comparison : LocalComparisonImage)
    (value : ActualSubgroup) (code : GroupCode) :
    value • orbitPoint comparison code =
      orbitPoint comparison (read value * code) := by
  change orbitPoint comparison
      (read value *
        (orbitPointEquiv comparison).symm (orbitPoint comparison code)) = _
  rw [orbitPointEquiv_symm_orbitPoint]

/-- The actual generated subgroup action is free and transitive: between any
two displayed points there is exactly one acting subgroup element. -/
theorem displayedFiber_existsUnique_smul_eq
    (comparison : LocalComparisonImage)
    (first second : DisplayedFiber comparison) :
    ∃! value : ActualSubgroup, value • first = second := by
  rcases displayedOrbit_existsUnique_subgroup_displacement
      comparison first second with ⟨value, equality, unique⟩
  refine ⟨value, ?_, ?_⟩
  · apply Subtype.ext
    exact (fiberAction_val comparison value first).trans equality
  · intro candidate candidateEquality
    apply unique candidate
    calc
      candidate.1 • first.1 = (candidate • first).1 :=
        (fiberAction_val comparison candidate first).symm
      _ = second.1 := congrArg Subtype.val candidateEquality

/-- The source-code equivalence intertwines the regular source action with
the actual generated-subgroup action on each displayed fiber. -/
theorem orbitPointEquiv_equivariant
    (comparison : LocalComparisonImage)
    (value : ActualSubgroup) (code : GroupCode) :
    orbitPointEquiv comparison (read value * code) =
      value • orbitPointEquiv comparison code := by
  exact (fiberAction_orbitPoint comparison value code).symm

/-- Independent local data for a represented comparison and one displayed
lift over it. -/
abbrev TotalLocalCode := LocalCode × GroupCode

/-- Dependent total space of all represented comparisons and their displayed
lift fibers. -/
abbrev TotalDisplayedSpace :=
  Σ comparison : LocalComparisonImage, DisplayedFiber comparison

/-- Assemble both comparison and kernel codes into the dependent displayed
lift total space. -/
noncomputable def totalAssemble (code : TotalLocalCode) :
    TotalDisplayedSpace :=
  ⟨assemble code.1, orbitPoint (assemble code.1) code.2⟩

/-- Read both independent codes from an actual point of the dependent total
space. -/
noncomputable def totalRead (point : TotalDisplayedSpace) : TotalLocalCode :=
  (read point.1, (orbitPointEquiv point.1).symm point.2)

/-- Reading after dependent assembly recovers both independent source codes. -/
@[simp] theorem totalRead_assemble (code : TotalLocalCode) :
    totalRead (totalAssemble code) = code := by
  rcases code with ⟨comparisonCode, kernelCode⟩
  apply Prod.ext
  · exact read_assemble comparisonCode
  · exact orbitPointEquiv_symm_orbitPoint
      (assemble comparisonCode) kernelCode

/-- Dependent assembly after reading recovers both the actual comparison and
its displayed lift. -/
@[simp] theorem totalAssemble_read (point : TotalDisplayedSpace) :
    totalAssemble (totalRead point) = point := by
  rcases point with ⟨comparison, point⟩
  rcases comparison with ⟨comparisonValue, comparisonCode, rfl⟩
  change totalAssemble
      (read (assemble comparisonCode),
        (orbitPointEquiv (assemble comparisonCode)).symm point) =
    ⟨assemble comparisonCode, point⟩
  rw [G122FourComponentComparisonLocalModel.read_assemble]
  simp only [totalAssemble]
  exact Sigma.ext rfl
    (heq_of_eq (orbitPoint_orbitPointEquiv_symm _ point))

/-- Two-sided reconstruction of the complete displayed comparison/lift
bundle from the product of independent comparison and kernel codes. -/
noncomputable def totalReconstructionEquiv :
    TotalLocalCode ≃ TotalDisplayedSpace where
  toFun := totalAssemble
  invFun := totalRead
  left_inv := totalRead_assemble
  right_inv := totalAssemble_read

/-- Every actual point of the dependent displayed bundle has exactly one pair
of independent source codes. -/
theorem totalCode_existsUnique (point : TotalDisplayedSpace) :
    ∃! code : TotalLocalCode, totalAssemble code = point := by
  refine ⟨totalRead point, totalAssemble_read point, ?_⟩
  intro candidate equality
  exact totalReconstructionEquiv.injective
    (equality.trans (totalAssemble_read point).symm)

/-- Total-code reconstruction and the principal generated-subgroup action
hold together for the same represented comparison fiber. -/
theorem totalReconstruction_and_principalFiber
    (point : TotalDisplayedSpace)
    (target : DisplayedFiber point.1) :
    (∃! code : TotalLocalCode, totalAssemble code = point) ∧
    (∃! value : ActualSubgroup, value • point.2 = target) :=
  ⟨totalCode_existsUnique point,
    displayedFiber_existsUnique_smul_eq point.1 point.2 target⟩

end
end AAT.AG.LocalSemanticReconstruction.G122DisplayedFiberBundleReconstruction

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.G122DisplayedFiberBundleReconstruction
