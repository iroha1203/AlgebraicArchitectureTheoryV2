import ResearchLean.AG.SafeCoarseningOrder.UniformSafety
import ResearchLean.AG.AtlasDefectComposition.GeneratedDefect
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# 実比較の失敗を元cochainと有理汎関数へ戻す

面なしの実複体では全1-cochainがcycleである。同じ既存H¹商の核・余核の
非零性から代表元とpotentialまたは分離汎関数を生成する。
## Implementation notes

既存H¹商とliteral余核の有理分離双対を用いる。出力は元cochainとpotentialと
正規化汎関数を保持する。次元差だけを失敗証拠にせず、その商から実代表元へ戻す。
非計算的双対選択は有限次元の通常の数学的構成であり、期待rankを入力しない。
-/
noncomputable section
namespace AAT.AG.SafeCoarseningOrder
open CanonicalResolution ResolutionInvariance TwoPhase AtlasDefectComposition
namespace FailureCertificate
variable (C : ThreeCochainComplex ℚ) (hz : ∀ z, C.d1 z = 0)
/-- 面なし条件から全cochainを同じ実cycle型に入れる線形写像。 -/
def allCycles : C.C1 →ₗ[ℚ] LinearMap.ker C.d1 where
  toFun z := ⟨z,hz z⟩
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl
/-- 全cochainから既存のd0像による実H¹商への写像。 -/
def cochainClass : C.C1 →ₗ[ℚ] C.H1 :=
  (LinearMap.range C.boundaryToCycles).mkQ.comp (allCycles C hz)
/-- cochainの実商への評価式。 -/
theorem cochainClass_apply (z : C.C1) : cochainClass C hz z =
    (LinearMap.range C.boundaryToCycles).mkQ ⟨z,hz z⟩ := rfl
/-- 同じ実H¹類のすべてが元cochainに代表される。 -/
theorem cochainClass_surjective : Function.Surjective (cochainClass C hz) := by
  intro x
  obtain ⟨z,rfl⟩ := (LinearMap.range C.boundaryToCycles).mkQ_surjective x
  exact ⟨z.1,rfl⟩
/-- d0像は同じ商で零。 -/
theorem cochainClass_d0 (x : C.C0) : cochainClass C hz (C.d0 x) = 0 := by
  rw [cochainClass_apply]
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  exact ⟨x,Subtype.ext (C.boundaryToCycles_apply x)⟩
variable {C D : ThreeCochainComplex ℚ} (f : ThreeCochainComplex.Hom C D)
/-- 生成した全cochain商射と同じ実H¹比較の可換性。 -/
theorem cochainClass_naturality (hc : ∀ z, C.d1 z = 0) (hd : ∀ z, D.d1 z = 0)
    (z : C.C1) : cochainClass D hd (f.f1 z) = f.h1Map (cochainClass C hc z) := by
  rw [cochainClass_apply,cochainClass_apply,ThreeCochainComplex.Hom.h1Map_mk]
  apply congrArg (LinearMap.range D.boundaryToCycles).mkQ
  apply Subtype.ext
  exact (f.cyclesMap_apply ⟨z,hc z⟩).symm
/-- 粗非零商類が実比較でexactになる核失敗証拠。 -/
structure KernelFailure where
  x : C.C1
  x_cycle : C.d1 x = 0
  y : D.C0
  comparison_exact : f.f1 x = D.d0 y
  functional : C.C1 →ₗ[ℚ] ℚ
  annihilate_d0 : ∀ b, functional (C.d0 b) = 0
  normalized : functional x = 1
/-- 細非零余核類を検証する実cochainと有理分離汎関数。 -/
structure CokerFailure where
  z : D.C1
  z_cycle : D.d1 z = 0
  functional : D.C1 →ₗ[ℚ] ℚ
  annihilate_d0 : ∀ b, functional (D.d0 b) = 0
  annihilate_comparison : ∀ x : LinearMap.ker C.d1, functional (f.f1 x.1) = 0
  normalized : functional z = 1
/-- 非単射性を粗非零類と細potentialと粗分離汎関数へ戻す。 -/
theorem kernelFailure_exists (hc : ∀ z, C.d1 z = 0) (hn : ¬ Function.Injective f.h1Map) :
    Nonempty (KernelFailure f) := by
  classical
  change ¬ ∀ a b, f.h1Map a = f.h1Map b → a = b at hn
  push_neg at hn
  obtain ⟨a,b,hab,hne⟩ := hn
  have hx : a-b ≠ 0 := sub_ne_zero.mpr hne
  have hf : f.h1Map (a-b) = 0 := by rw [map_sub,hab,sub_self]
  obtain ⟨x,hxrep⟩ := cochainClass_surjective C hc (a-b)
  obtain ⟨y,hy⟩ := (h1Map_mk_eq_zero_iff f ⟨x,hc x⟩).mp (hxrep.symm ▸ hf)
  obtain ⟨psi,hpsi⟩ := Module.Projective.exists_dual_eq_one ℚ hx
  refine ⟨⟨x,hc x,y,hy.symm,psi.comp (cochainClass C hc),?_,?_⟩⟩
  · intro b
    rw [LinearMap.comp_apply,cochainClass_d0,map_zero]
  · rw [LinearMap.comp_apply,hxrep]
    exact hpsi
/-- 非全射性を同じ実余核の分離汎関数へ戻す。 -/
theorem cokerFailure_exists (hc : ∀ z, C.d1 z = 0) (hd : ∀ z, D.d1 z = 0)
    (hn : ¬ Function.Surjective f.h1Map) : Nonempty (CokerFailure f) := by
  classical
  change ¬ ∀ b, ∃ a, f.h1Map a = b at hn
  push_neg at hn
  obtain ⟨b,hb⟩ := hn
  have hbn : b ∉ LinearMap.range f.h1Map := by
    rintro ⟨a,ha⟩
    exact hb a ha
  have hqn : (LinearMap.range f.h1Map).mkQ b ≠ 0 := by
    intro hq
    exact hbn ((Submodule.Quotient.mk_eq_zero _).mp hq)
  obtain ⟨psi,hpsi⟩ := Module.Projective.exists_dual_eq_one ℚ hqn
  obtain ⟨z,hzrep⟩ := cochainClass_surjective D hd b
  let phi := psi.comp ((LinearMap.range f.h1Map).mkQ.comp (cochainClass D hd))
  refine ⟨⟨z,hd z,phi,?_,?_,?_⟩⟩
  · intro y
    simp only [phi,LinearMap.comp_apply,cochainClass_d0,map_zero]
  · intro x
    have hx := cochainClass_naturality f hc hd x.1
    rw [show phi (f.f1 x.1) = psi ((LinearMap.range f.h1Map).mkQ
      (cochainClass D hd (f.f1 x.1))) by rfl,hx]
    have hz : (LinearMap.range f.h1Map).mkQ (f.h1Map (cochainClass C hc x.1)) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr ⟨_,rfl⟩
    rw [hz,map_zero]
  · change psi ((LinearMap.range f.h1Map).mkQ (cochainClass D hd z)) = 1
    rw [hzrep]
    exact hpsi
/-- 同じ実H¹比較の非全単射からどちらかのcochain失敗証拠を生成。 -/
theorem failure_exists (hc : ∀ z, C.d1 z = 0) (hd : ∀ z, D.d1 z = 0)
    (hn : ¬ Function.Bijective f.h1Map) :
    Nonempty (KernelFailure f) ∨ Nonempty (CokerFailure f) := by
  classical
  by_cases hi : Function.Injective f.h1Map
  · exact Or.inr (cokerFailure_exists f hc hd (fun hs => hn ⟨hi,hs⟩))
  · exact Or.inl (kernelFailure_exists f hc hi)

/-- 核証拠の汎関数は粗H¹非零性を保証し、同じ実比較の単射性を排除。 -/
theorem KernelFailure.not_injective (w : KernelFailure f) : ¬ Function.Injective f.h1Map := by
  intro hi
  let z : LinearMap.ker C.d1 := ⟨w.x,w.x_cycle⟩
  have hz : f.h1Map ((LinearMap.range C.boundaryToCycles).mkQ z) = 0 :=
    (h1Map_mk_eq_zero_iff f z).mpr ⟨w.y,w.comparison_exact.symm⟩
  have hq : (LinearMap.range C.boundaryToCycles).mkQ z = 0 := hi (hz.trans (map_zero _).symm)
  obtain ⟨b,hb⟩ := (Submodule.Quotient.mk_eq_zero _).mp hq
  have hbval : C.d0 b = w.x := by
    have h := congrArg Subtype.val hb
    simpa only [ThreeCochainComplex.boundaryToCycles_apply] using h
  have hzero : w.functional w.x = 0 := hbval ▸ w.annihilate_d0 b
  exact one_ne_zero (w.normalized.symm.trans hzero)
/-- 核証拠の指定粗cochainは既存の同じ実H¹商で非零。 -/
theorem KernelFailure.class_nonzero (w : KernelFailure f) :
    (LinearMap.range C.boundaryToCycles).mkQ ⟨w.x,w.x_cycle⟩ ≠ 0 := by
  intro hz
  obtain ⟨b,hb⟩ := (Submodule.Quotient.mk_eq_zero _).mp hz
  have hbval : C.d0 b = w.x := by
    have h := congrArg Subtype.val hb
    simpa only [ThreeCochainComplex.boundaryToCycles_apply] using h
  have hzero : w.functional w.x = 0 := hbval ▸ w.annihilate_d0 b
  exact one_ne_zero (w.normalized.symm.trans hzero)
/-- 余核汎関数は指定された細d0像と粗cycle比較像の和で零。 -/
theorem CokerFailure.annihilate_sum (w : CokerFailure f) (b : D.C0)
    (x : LinearMap.ker C.d1) : w.functional (D.d0 b + f.f1 x.1) = 0 := by
  rw [map_add,w.annihilate_d0,w.annihilate_comparison,add_zero]

/-- 余核証拠は細d0像と実比較像の和で零なので実全射性を排除。 -/
theorem CokerFailure.not_surjective (w : CokerFailure f) : ¬ Function.Surjective f.h1Map := by
  intro hs
  let z : LinearMap.ker D.d1 := ⟨w.z,w.z_cycle⟩
  have hr : (LinearMap.range D.boundaryToCycles).mkQ z ∈ LinearMap.range f.h1Map :=
    hs _
  obtain ⟨a,b,hb⟩ := (h1_mk_mem_range_iff f z).mp hr
  have hf := congrArg w.functional hb
  rw [map_sub,w.annihilate_comparison a,w.annihilate_d0 b,sub_zero] at hf
  exact one_ne_zero (w.normalized.symm.trans hf)


/-- 元cycleとd0像の正逆lift条件は、同じ実H¹比較の全単射性を与える。 -/
theorem bijective_of_representatives
    (hi : ∀ z : LinearMap.ker C.d1, (∃ y, D.d0 y = f.f1 z.1) →
      ∃ b, C.d0 b = z.1)
    (hs : ∀ z : LinearMap.ker D.d1, ∃ x : LinearMap.ker C.d1, ∃ y,
      z.1 - f.f1 x.1 = D.d0 y) : Function.Bijective f.h1Map := by
  constructor
  · apply LinearMap.ker_eq_bot.mp
    apply (Submodule.eq_bot_iff _).mpr
    intro x hx
    obtain ⟨z,hz⟩ := (LinearMap.range C.boundaryToCycles).mkQ_surjective x
    have hzero : f.h1Map ((LinearMap.range C.boundaryToCycles).mkQ z) = 0 := by
      rw [hz]
      exact hx
    obtain ⟨b,hb⟩ := hi z ((h1Map_mk_eq_zero_iff f z).mp hzero)
    have hq : (LinearMap.range C.boundaryToCycles).mkQ z = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr ⟨b,Subtype.ext hb⟩
    exact hz.symm.trans hq
  · intro x
    obtain ⟨z,rfl⟩ := (LinearMap.range D.boundaryToCycles).mkQ_surjective x
    exact (h1_mk_mem_range_iff f z).mpr (hs z)

end FailureCertificate
end AAT.AG.SafeCoarseningOrder
#assert_standard_axioms_only AAT.AG.SafeCoarseningOrder
