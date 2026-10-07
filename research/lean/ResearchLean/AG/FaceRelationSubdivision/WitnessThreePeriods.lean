import ResearchLean.AG.FaceRelationSubdivision.WitnessThreeInput
import Mathlib.LinearAlgebra.Isomorphisms
import Formal.Util.AssertStandardAxioms

/-!
# W3の同じ連結loopのH¹

## Implementation notes

loop kの値をcocycle商上で読む。period零の全cocycleを原始頂点potentialで回復し、
旧面と複製面の両方で同じ実d0像を得る。rankによる代替はしない。
-/
noncomputable section
namespace AAT.AG.FaceRelationSubdivision.WitnessThree
open CanonicalResolution ResolutionInvariance TwoPhase AtlasDefectComposition
open ConnectedFaceWitness (q laws adequate)

/-- 旧実名付きcocycleのloop k上のperiod。 -/
def loopPeriod : LinearMap.ker (namedComplex N).d1 →ₗ[ℚ] ℚ where
  toFun z := z.val (3 : Fin 4)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
/-- 複製後の実名付きcocycleの同じloop k上のperiod。 -/
def fineLoopPeriod : LinearMap.ker (namedComplex fine).d1 →ₗ[ℚ] ℚ where
  toFun z := z.val (3 : Fin 4)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
/-- 旧periodのcochain評価。 -/
@[simp] theorem loopPeriod_apply (z : LinearMap.ker (namedComplex N).d1) : loopPeriod z = z.val (3 : Fin 4) := rfl
/-- 細periodのcochain評価。 -/
@[simp] theorem fineLoopPeriod_apply (z : LinearMap.ker (namedComplex fine).d1) : fineLoopPeriod z = z.val (3 : Fin 4) := rfl
/-- 元の面による旧cocycle条件。 -/
theorem cycle_relation (z : LinearMap.ker (namedComplex N).d1) : z.val (0 : Fin 4) - z.val (1 : Fin 4) + z.val (2 : Fin 4) = 0 := by
  have hz : (namedComplex N).d1 z.val = 0 := z.property
  have he := congrFun hz ()
  rw [d1_apply] at he
  exact he
/-- 複製後でも同じ元面によるcocycle条件。 -/
theorem fine_cycle_relation (z : LinearMap.ker (namedComplex fine).d1) : z.val (0 : Fin 4) - z.val (1 : Fin 4) + z.val (2 : Fin 4) = 0 := by
  have hz : (namedComplex fine).d1 z.val = 0 := z.property
  have he := congrFun hz (.inl ())
  rw [fine_d1_apply] at he
  exact he
/-- 旧loop period零の全cocycleは原始頂点差分から生まれる。 -/
theorem loopPeriod_kernel : LinearMap.ker loopPeriod = LinearMap.range (namedComplex N).boundaryToCycles := by
  ext z
  constructor
  · intro hz
    have hk : z.val (3 : Fin 4) = 0 := hz
    have hf := cycle_relation z
    refine ⟨![0,z.val (0 : Fin 4),z.val (1 : Fin 4)], ?_⟩
    apply Subtype.ext
    funext e
    rw [ThreeCochainComplex.boundaryToCycles_apply, d0_apply]
    fin_cases e <;> simp <;> linarith
  · rintro ⟨c,rfl⟩
    rw [LinearMap.mem_ker, loopPeriod_apply, ThreeCochainComplex.boundaryToCycles_apply, d0_apply]
    simp
/-- 細loop period零の全cocycleも同じ頂点potentialから生まれる。 -/
theorem fineLoopPeriod_kernel : LinearMap.ker fineLoopPeriod = LinearMap.range (namedComplex fine).boundaryToCycles := by
  ext z
  constructor
  · intro hz
    have hk : z.val (3 : Fin 4) = 0 := hz
    have hf := fine_cycle_relation z
    refine ⟨![0,z.val (0 : Fin 4),z.val (1 : Fin 4)], ?_⟩
    apply Subtype.ext
    funext e
    rw [ThreeCochainComplex.boundaryToCycles_apply, fine_d0_apply]
    fin_cases e <;> simp <;> linarith
  · rintro ⟨c,rfl⟩
    rw [LinearMap.mem_ker, fineLoopPeriod_apply, ThreeCochainComplex.boundaryToCycles_apply, fine_d0_apply]
    simp
/-- 旧loop単独cochainは任意periodを与えるcocycle。 -/
def loopOnly (a : ℚ) : LinearMap.ker (namedComplex N).d1 :=
  ⟨![0,0,0,a], by funext f; rw [d1_apply]; simp; rfl⟩
/-- 複製後もloop単独cochainは任意periodを与えるcocycle。 -/
def fineLoopOnly (a : ℚ) : LinearMap.ker (namedComplex fine).d1 :=
  ⟨![0,0,0,a], by funext f; rw [fine_d1_apply]; simp; rfl⟩
/-- 同じ旧loop単独cochainのperiod。 -/
@[simp] theorem loopPeriod_loopOnly (a : ℚ) : loopPeriod (loopOnly a) = a := rfl
/-- 同じ細loop単独cochainのperiod。 -/
@[simp] theorem fineLoopPeriod_loopOnly (a : ℚ) : fineLoopPeriod (fineLoopOnly a) = a := rfl
/-- 原始loopから旧periodの全射性を得る。 -/
theorem loopPeriod_surjective : Function.Surjective loopPeriod := fun a => ⟨loopOnly a,rfl⟩
/-- 原始loopから細periodの全射性を得る。 -/
theorem fineLoopPeriod_surjective : Function.Surjective fineLoopPeriod := fun a => ⟨fineLoopOnly a,rfl⟩
/-- 同じ旧H¹商をloop periodでℚに同定する。 -/
def namedH1Equiv : (namedComplex N).H1 ≃ₗ[ℚ] ℚ :=
  (Submodule.quotEquivOfEq _ _ loopPeriod_kernel.symm).trans (loopPeriod.quotKerEquivOfSurjective loopPeriod_surjective)
/-- 同じ細H¹商をloop periodでℚに同定する。 -/
def fineNamedH1Equiv : (namedComplex fine).H1 ≃ₗ[ℚ] ℚ :=
  (Submodule.quotEquivOfEq _ _ fineLoopPeriod_kernel.symm).trans
    (fineLoopPeriod.quotKerEquivOfSurjective fineLoopPeriod_surjective)
/-- 旧H¹同定は実cocycleのloop値を読む。 -/
@[simp] theorem namedH1Equiv_mk (z : LinearMap.ker (namedComplex N).d1) :
    namedH1Equiv ((LinearMap.range (namedComplex N).boundaryToCycles).mkQ z) = z.val (3 : Fin 4) := rfl
/-- 細H¹同定も実cocycleの同じloop値を読む。 -/
@[simp] theorem fineNamedH1Equiv_mk (z : LinearMap.ker (namedComplex fine).d1) :
    fineNamedH1Equiv ((LinearMap.range (namedComplex fine).boundaryToCycles).mkQ z) = z.val (3 : Fin 4) := rfl
/-- 同じ実生成比較はperiod座標で恒等になる。 -/
theorem named_h1_identity (l : LawValueLabel laws) (x : (namedComplex N).H1) :
    fineNamedH1Equiv ((namedHom l).h1Map x) = namedH1Equiv x := by
  obtain ⟨z,rfl⟩ := (LinearMap.range (namedComplex N).boundaryToCycles).mkQ_surjective x
  rw [ThreeCochainComplex.Hom.h1Map_mk, fineNamedH1Equiv_mk, namedH1Equiv_mk,
    ThreeCochainComplex.Hom.cyclesMap_apply, named_f1]
/-- loop単独1は旧H¹の非零類。 -/
theorem loop_class_nonzero : (LinearMap.range (namedComplex N).boundaryToCycles).mkQ (loopOnly 1) ≠ 0 := by
  intro hz
  have he := congrArg namedH1Equiv hz
  rw [namedH1Equiv_mk, map_zero] at he
  exact one_ne_zero he
/-- 同じloop単独1は細H¹でも非零。 -/
theorem fine_loop_class_nonzero :
    (LinearMap.range (namedComplex fine).boundaryToCycles).mkQ (fineLoopOnly 1) ≠ 0 := by
  intro hz
  have he := congrArg fineNamedH1Equiv hz
  rw [fineNamedH1Equiv_mk, map_zero] at he
  exact one_ne_zero he

end AAT.AG.FaceRelationSubdivision.WitnessThree
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision.WitnessThree
