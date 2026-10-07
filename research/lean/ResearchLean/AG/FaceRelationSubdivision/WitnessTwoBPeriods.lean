import ResearchLean.AG.FaceRelationSubdivision.WitnessTwoBInput
import ResearchLean.AG.FaceRelationSubdivision.IncidenceNamedComparison
import Mathlib.LinearAlgebra.Isomorphisms
import Formal.Util.AssertStandardAxioms

/-!
# W2b の同じ loop period

## Implementation notes

原始三重面の cocycle 条件が e 値を零にし、k の値だけが商に残ることを証明する。
微分の rank を入力する方式は採らず、零 potential と k 単独 cochain を使う。
-/
noncomputable section
namespace AAT.AG.FaceRelationSubdivision.WitnessTwoB
open CanonicalResolution ResolutionInvariance TwoPhase AtlasDefectComposition
open ConnectedFaceWitness (q laws adequate label)

/-- 実名付き cocycle の同じ k 値。 -/
def loopPeriod : LinearMap.ker (namedComplex N).d1 →ₗ[ℚ] ℚ where
  toFun z := z.val true
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
/-- loop period の代表評価。 -/
@[simp] theorem loopPeriod_apply (z : LinearMap.ker (namedComplex N).d1) : loopPeriod z=z.val true := rfl
/-- 三重面の原始条件は e 値を零にする。 -/
theorem cycle_relation (z : LinearMap.ker (namedComplex N).d1) : z.val false=0 := by
  have h := congrFun z.property ()
  rw [d1_apply] at h
  exact h
/-- period 零の cocycle は同じ実次数0像で尽くされる。 -/
theorem loopPeriod_kernel : LinearMap.ker loopPeriod=LinearMap.range (namedComplex N).boundaryToCycles := by
  ext z
  constructor
  · intro hz
    have hk : z.val true=0 := hz
    have he := cycle_relation z
    refine ⟨0,?_⟩
    apply Subtype.ext
    funext e
    rw [ThreeCochainComplex.boundaryToCycles_apply,d0_apply]
    cases e
    · exact he.symm
    · exact hk.symm
  · rintro ⟨c,rfl⟩
    rw [LinearMap.mem_ker,loopPeriod_apply,ThreeCochainComplex.boundaryToCycles_apply,d0_apply]
/-- k 単独値は同じ原始 cocycle。 -/
def loopOnly (a : ℚ) : LinearMap.ker (namedComplex N).d1 :=
  ⟨fun e => if e then a else 0,by funext f; rw [d1_apply]; rfl⟩
/-- k 単独値の period。 -/
@[simp] theorem loopPeriod_loopOnly (a : ℚ) : loopPeriod (loopOnly a)=a := rfl
/-- 同じ単独 cochain による全射。 -/
theorem loopPeriod_surjective : Function.Surjective loopPeriod := fun a => ⟨loopOnly a,rfl⟩
/-- 原始 period による同じ H¹商の ℚ 同定。 -/
def namedH1Period : (namedComplex N).H1 ≃ₗ[ℚ] ℚ :=
  (Submodule.quotEquivOfEq _ _ loopPeriod_kernel.symm).trans
    (loopPeriod.quotKerEquivOfSurjective loopPeriod_surjective)
/-- 商同定は実代表の k 値を読む。 -/
@[simp] theorem namedH1Period_mk (z : LinearMap.ker (namedComplex N).d1) :
    namedH1Period ((LinearMap.range (namedComplex N).boundaryToCycles).mkQ z)=z.val true := rfl
/-- 同じ k 単独1の実 H¹類は非零。 -/
theorem loop_class_nonzero : (LinearMap.range (namedComplex N).boundaryToCycles).mkQ (loopOnly 1)≠0 := by
  intro h
  have he := congrArg namedH1Period h
  rw [namedH1Period_mk,map_zero] at he
  exact one_ne_zero he
/-- 各元ラベルの独立実 block と名付き表の全三成分同型。 -/
def blockEquiv (l : LawValueLabel laws) :=
  fullBlockNamedEquivalence N laws adequate chart_full
    (fullSupport_edge N chart_full) (fullSupport_face N chart_full) l
/-- 同じ独立実旧 H¹の k period。 -/
def oldBlockPeriod (l : LawValueLabel laws) := (blockEquiv l).h1Equiv.trans namedH1Period
/-- 元ラベルの実旧 k 座標。 -/
def oldK (l : LawValueLabel laws) :=
  (fullBlockCoordinateEquiv laws q adequate N.edgeSupport (fullSupport_edge N chart_full) l).symm true
/-- 同じ旧 k 座標の原始辺名。 -/
@[simp] theorem oldK_cell (l) : (oldK l).val.cell=true := fullBlockCoordinateEquiv_symm_cell _ _ _ _ _ _ _
/-- k は分割される e と別名である。 -/
theorem oldK_retained (l) : (oldK l).val.cell≠false := by rw [oldK_cell]; exact Ne.symm Bool.false_ne_true
/-- 同じ実旧 period は代表の k 座標を読む。 -/
@[simp] theorem oldBlockPeriod_mk (l) (z : LinearMap.ker (N.lawValueBlockComplex laws adequate l).d1) :
    oldBlockPeriod l ((LinearMap.range (N.lawValueBlockComplex laws adequate l).boundaryToCycles).mkQ z)=z.val (oldK l) := by
  rw [oldBlockPeriod,LinearEquiv.trans_apply,ThreeCochainComplex.CochainEquiv.h1Equiv_apply,
    ThreeCochainComplex.Hom.h1Map_mk,namedH1Period_mk,ThreeCochainComplex.Hom.cyclesMap_apply]
  exact fullBlockNamedEquivalence_e1 N laws adequate chart_full
    (fullSupport_edge N chart_full) (fullSupport_face N chart_full) l z.val true
/-- 同じ独立実比較とその逆から得る細側 k period 同定。 -/
def fineBlockPeriod (l : LawValueLabel laws) :=
  (EdgeSubdivision.blockOldH1Iso N false laws adequate l).toLinearEquiv.symm.trans (oldBlockPeriod l)
/-- 同じ実 H¹比較は period 座標で恒等。 -/
theorem block_period_identity (l : LawValueLabel laws) (x : (N.lawValueBlockComplex laws adequate l).H1) :
    fineBlockPeriod l ((EdgeSubdivision.blockR N false laws adequate l).h1Map x)=oldBlockPeriod l x := by
  have h : (EdgeSubdivision.blockOldH1Iso N false laws adequate l).toLinearEquiv x=
      (EdgeSubdivision.blockR N false laws adequate l).h1Map x := by
    rw [CategoryTheory.Iso.toLinearEquiv_apply,EdgeSubdivision.blockOldH1Iso_hom]
    rfl
  rw [← h]
  exact congrArg (oldBlockPeriod l) ((EdgeSubdivision.blockOldH1Iso N false laws adequate l).toLinearEquiv.symm_apply_apply x)

end AAT.AG.FaceRelationSubdivision.WitnessTwoB
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision.WitnessTwoB
