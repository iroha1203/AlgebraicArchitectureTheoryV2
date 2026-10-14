import ResearchLean.AG.SafeCoarseningOrder.TriangleCounterexamples

/-!
# 証拠付き出力の正負instance

W0と同じ原始三角形で最大元・join・不安全証拠を正負に発火させる。
一般cochain証拠の正負は、非零実H¹を持つ同じ三角形複体の零Homと恒等Homで検査する。
この零HomはT0粗化の反例の代替ではなく、一般certificate APIだけの発火例である。
-/
noncomputable section
namespace AAT.AG.SafeCoarseningOrder
open CanonicalResolution ResolutionInvariance TwoPhase AtlasDefectComposition FailureCertificate
/-- 指定W0の正の最大元producer。 -/
def w0_greatestWitness : w0.GreatestWitness := w0.greatestWitness w0_greatestDecision
/-- 同じ原始三角形で正の最大元証拠は存在しない。 -/
theorem triangle_greatestWitness_empty : ¬ Nonempty Triangle.input.GreatestWitness := by
  rintro ⟨w⟩
  exact Triangle.no_greatest ⟨w.coarsening,w.greatest⟩
/-- W0では最大元負の証拠が存在しない。 -/
theorem w0_noGreatestWitness_empty : ¬ Nonempty w0.NoGreatestWitness := by
  rintro ⟨w⟩
  exact w.exclude ⊤ le_top le_top (w0_safe ⊤)
/-- W0ではjoin負の証拠が存在しない。 -/
theorem w0_joinFailure_empty : ¬ Nonempty w0.JoinFailure := by
  rintro ⟨w⟩
  exact PrimitiveInput.UnsafeWitness.not_safe w0 w.failure (w0_safe _)
/-- W0全粗化で不安全証拠は存在しない。 -/
theorem w0_unsafeWitness_empty (R : Coarsening Unit Bool) : ¬ Nonempty (w0.UnsafeWitness R) := by
  rintro ⟨w⟩
  exact PrimitiveInput.UnsafeWitness.not_safe w0 w (w0_safe R)
/-- 非零三角形の同じ実複体間の零Hom。 -/
def triangleZeroHom : ThreeCochainComplex.Hom Triangle.fullComplex Triangle.fullComplex where
  f0 := 0
  f1 := 0
  f2 := 0
  comm0 _ := (map_zero _).symm
  comm1 _ := (map_zero _).symm
/-- 零Homの元次数1評価API。 -/
theorem triangleZeroHom_f1 (z : Triangle.fullComplex.C1) : triangleZeroHom.f1 z = 0 := rfl
/-- 同じ原非零cycleとperiodから核証拠の全fieldを生成。 -/
def triangleZeroKernel : KernelFailure triangleZeroHom where
  x := Triangle.spike
  x_cycle := (Triangle.cycle Triangle.spike).2
  y := 0
  comparison_exact := by rw [triangleZeroHom_f1,map_zero]
  functional := Triangle.period
  annihilate_d0 := Triangle.period_boundary
  normalized := Triangle.period_spike
/-- 同じ原非零cycleとperiodから余核証拠の全fieldを生成。 -/
def triangleZeroCoker : CokerFailure triangleZeroHom where
  z := Triangle.spike
  z_cycle := (Triangle.cycle Triangle.spike).2
  functional := Triangle.period
  annihilate_d0 := Triangle.period_boundary
  annihilate_comparison _ := by rw [triangleZeroHom_f1,map_zero]
  normalized := Triangle.period_spike
/-- 同じ非零複体の恒等比較には核失敗証拠がない。 -/
theorem triangle_id_kernel_empty : ¬ Nonempty (KernelFailure (cochainId Triangle.fullComplex)) := by
  rintro ⟨w⟩
  have hi : Function.Injective (cochainId Triangle.fullComplex).h1Map := by
    rw [cochainId_h1Map]
    exact Function.injective_id
  exact KernelFailure.not_injective _ w hi
/-- 同じ非零複体の恒等比較には余核失敗証拠がない。 -/
theorem triangle_id_coker_empty : ¬ Nonempty (CokerFailure (cochainId Triangle.fullComplex)) := by
  rintro ⟨w⟩
  have hs : Function.Surjective (cochainId Triangle.fullComplex).h1Map := by
    rw [cochainId_h1Map]
    exact Function.surjective_id
  exact CokerFailure.not_surjective _ w hs
end AAT.AG.SafeCoarseningOrder
#assert_standard_axioms_only AAT.AG.SafeCoarseningOrder
