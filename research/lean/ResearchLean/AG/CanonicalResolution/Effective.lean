import ResearchLean.AG.CanonicalResolution.JointKernel

/-!
# Effective finite canonical resolution

This module discharges F2 of `G-103-aat-canonical-resolution`.  For a finite
decidable source it computes every joint-law equivalence class as a `Finset`,
collects the resulting finite partition, and uses the partition classes as a
concrete reading target.  Correctness is proved by comparing kernels; it is not
stored in the computed data.
-/

namespace AAT.AG.CanonicalResolution

universe u

namespace FiniteLawFamily

variable {Source : Type u}

/-- Equality of all law evaluations is decidable from the declared finite inputs. -/
instance instDecidableEquivalent (laws : FiniteLawFamily Source)
    (x y : Source) : Decidable (laws.Equivalent x y) := by
  unfold Equivalent
  infer_instance

/-- The computed joint-law class of one source. -/
def computedClass (laws : FiniteLawFamily Source)
    [Fintype Source] [DecidableEq Source] (source : Source) : Finset Source :=
  Finset.univ.filter (laws.Equivalent source)

/-- The finite partition obtained by enumerating all computed joint-law classes. -/
def computedPartition (laws : FiniteLawFamily Source)
    [Fintype Source] [DecidableEq Source] : Finset (Finset Source) :=
  Finset.univ.image laws.computedClass

/-- Every computed class occurs in the computed partition. -/
theorem computedClass_mem_partition (laws : FiniteLawFamily Source)
    [Fintype Source] [DecidableEq Source] (source : Source) :
    laws.computedClass source ∈ laws.computedPartition := by
  exact Finset.mem_image.mpr ⟨source, Finset.mem_univ source, rfl⟩

/-- The concrete finite target consisting of the partition classes. -/
abbrev ComputedTarget (laws : FiniteLawFamily Source)
    [Fintype Source] [DecidableEq Source] :=
  { sourceClass : Finset Source // sourceClass ∈ laws.computedPartition }

/-- The computed target is itself a finite type. -/
instance instFintypeComputedTarget (laws : FiniteLawFamily Source)
    [Fintype Source] [DecidableEq Source] :
    Fintype laws.ComputedTarget :=
  inferInstance

/-- The executable reading whose values are the computed joint-law classes. -/
def computedReading (laws : FiniteLawFamily Source)
    [Fintype Source] [DecidableEq Source] : Reading Source where
  Target := laws.ComputedTarget
  read source := ⟨laws.computedClass source,
    laws.computedClass_mem_partition source⟩
  surjective := by
    intro sourceClass
    rcases Finset.mem_image.mp sourceClass.property with
      ⟨source, _hsource, hclass⟩
    refine ⟨source, ?_⟩
    apply Subtype.ext
    exact hclass

/-- Two computed classes coincide exactly when all law evaluations coincide. -/
theorem computedClass_eq_iff (laws : FiniteLawFamily Source)
    [Fintype Source] [DecidableEq Source] (x y : Source) :
    laws.computedClass x = laws.computedClass y ↔
      laws.Equivalent x y := by
  constructor
  · intro hclasses
    have hself : x ∈ laws.computedClass x := by
      simp [computedClass, Equivalent]
    have hmem : x ∈ laws.computedClass y := by
      rw [← hclasses]
      exact hself
    have hyx : laws.Equivalent y x := by
      simpa [computedClass] using hmem
    exact fun law => (hyx law).symm
  · intro hxy
    apply Finset.ext
    intro source
    simp only [computedClass, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hx law
      exact (hxy law).symm.trans (hx law)
    · intro hy law
      exact (hxy law).trans (hy law)

/-- The computed reading kernel is the declared joint-law equivalence. -/
theorem computed_kernel_iff (laws : FiniteLawFamily Source)
    [Fintype Source] [DecidableEq Source] (x y : Source) :
    laws.computedReading.Kernel x y ↔ laws.Equivalent x y := by
  constructor
  · intro hxy
    apply (laws.computedClass_eq_iff x y).1
    exact congrArg Subtype.val hxy
  · intro hxy
    apply Subtype.ext
    exact (laws.computedClass_eq_iff x y).2 hxy

/-- The computed reading is adequate for every law. -/
theorem computed_adequate (laws : FiniteLawFamily Source)
    [Fintype Source] [DecidableEq Source] :
    laws.Adequate laws.computedReading := by
  apply (laws.adequate_iff_kernel laws.computedReading).2
  intro x y hxy
  exact (laws.computed_kernel_iff x y).1 hxy

/-- The finite computation returns exactly the canonical joint-kernel quotient relation. -/
theorem computed_kernelEquivalent_jointKernel
    (laws : FiniteLawFamily Source)
    [Fintype Source] [DecidableEq Source] :
    laws.computedReading.KernelEquivalent laws.jointKernelReading := by
  intro x y
  exact (laws.computed_kernel_iff x y).trans
    (laws.jointKernel_kernel_iff x y).symm

end FiniteLawFamily

end AAT.AG.CanonicalResolution

#assert_standard_axioms_only AAT.AG.CanonicalResolution
