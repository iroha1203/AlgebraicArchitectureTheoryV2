import ResearchLean.AG.FaceRelationSubdivision.WitnessThreeInput
import Formal.Util.AssertStandardAxioms

/-!
# W3の実H²と複製単独類

## Implementation notes

原始e単独cochainで旧d1の全射を証明する。
細側の差の核は同じe単独cochainの像であり、fresh単独1を非零類として評価する。
標準Law同定には独立生成後の全三成分同型だけを用いる。
-/
noncomputable section
open CategoryTheory HomologicalComplex
namespace AAT.AG.FaceRelationSubdivision.WitnessThree
open CanonicalResolution ResolutionInvariance TwoPhase AtlasDefectComposition
open ConnectedFaceWitness (q laws adequate)

/-- 原始辺e単独のcochainで旧面微分の任意値を実現する。 -/
theorem d1_surjective : Function.Surjective (namedComplex N).d1 := by
  intro z
  refine ⟨![z (),0,0,0],?_⟩
  funext f
  cases f
  rw [d1_apply]
  simp
/-- 実旧H²商は零。 -/
theorem named_oldH2_subsingleton : Subsingleton ((namedComplex N).C2 ⧸ LinearMap.range (namedComplex N).d1) :=
  Submodule.Quotient.subsingleton_iff.mpr (LinearMap.range_eq_top.mpr d1_surjective)
/-- 細面cochainの原始fresh−F差。 -/
def namedDifference : (namedComplex fine).C2 →ₗ[ℚ] ℚ where
  toFun z := z (.inr PUnit.unit) - z (.inl ())
  map_add' z w := by change (z _ + w _) - (z _ + w _) = (z _ - z _) + (w _ - w _); ring
  map_smul' a z := by change a * z _ - a * z _ = a * (z _ - z _); ring
/-- 原始差の実評価。 -/
@[simp] theorem namedDifference_apply (z : (namedComplex fine).C2) :
    namedDifference z = z (.inr PUnit.unit) - z (.inl ()) := rfl
/-- 実fresh面単独cochain。 -/
def namedFreshOnly (a : ℚ) : (namedComplex fine).C2 := fun f => match f with | .inl _ => 0 | .inr _ => a
/-- fresh単独cochainは指定差aを持つ。 -/
@[simp] theorem namedDifference_freshOnly (a : ℚ) : namedDifference (namedFreshOnly a) = a := by
  rw [namedDifference_apply]
  exact sub_zero a
/-- 原始差は全射。 -/
theorem namedDifference_surjective : Function.Surjective namedDifference := fun a => ⟨namedFreshOnly a,namedDifference_freshOnly a⟩
/-- 原始差の核は同じ細実微分の像。 -/
theorem namedDifference_kernel : LinearMap.ker namedDifference = LinearMap.range (namedComplex fine).d1 := by
  ext z
  constructor
  · intro hz
    have he : z (.inr PUnit.unit) = z (.inl ()) := sub_eq_zero.mp hz
    refine ⟨![z (.inl ()),0,0,0],?_⟩
    funext f
    rw [fine_d1_apply]
    rcases f with f | f <;> cases f <;> simp
    exact he.symm
  · rintro ⟨z,rfl⟩
    rw [LinearMap.mem_ker, namedDifference_apply, fine_d1_apply, fine_d1_apply, sub_self]
/-- 実細H²商は原始差でℚに同定される。 -/
def fineNamedH2Equiv : ((namedComplex fine).C2 ⧸ LinearMap.range (namedComplex fine).d1) ≃ₗ[ℚ] ℚ :=
  (Submodule.quotEquivOfEq _ _ namedDifference_kernel.symm).trans
    (namedDifference.quotKerEquivOfSurjective namedDifference_surjective)
/-- 同じ実H²商の代表元は原始差で評価される。 -/
@[simp] theorem fineNamedH2Equiv_mk (z : (namedComplex fine).C2) :
    fineNamedH2Equiv ((LinearMap.range (namedComplex fine).d1).mkQ z) = namedDifference z := rfl
/-- fresh単独1は同じ実H²の非零類を与える。 -/
theorem named_fresh_class_nonzero : (LinearMap.range (namedComplex fine).d1).mkQ (namedFreshOnly 1) ≠ 0 := by
  intro hz
  have he := congrArg fineNamedH2Equiv hz
  rw [fineNamedH2Equiv_mk, namedDifference_freshOnly, map_zero] at he
  exact one_ne_zero he
/-- 同じ実生成旧Law blockの標準H²は零。 -/
theorem block_standardH2_subsingleton (l : LawValueLabel laws) :
    Subsingleton ((zeroExtension (N.lawValueBlockComplex laws adequate l)).homology 2) := by
  letI := named_oldH2_subsingleton
  exact ((fullBlockNamedHomologyEquiv N laws adequate chart_full edge_full face_full l 2).trans
    (oldH2Equiv (namedComplex N)).symm).toEquiv.subsingleton
/-- 同じ実生成細Law blockの標準H²はℚ。 -/
def fineBlockStandardH2Equiv (l : LawValueLabel laws) :
    (zeroExtension (fine.lawValueBlockComplex laws adequate l)).homology 2 ≃ₗ[ℚ] ℚ :=
  (fullBlockNamedHomologyEquiv fine laws adequate fine_chart_full fine_edge_full fine_face_full l 2).trans
    ((oldH2Equiv (namedComplex fine)).symm.trans fineNamedH2Equiv)
/-- 同じ実細blockの任意次数2代表元を原始差で読む。 -/
theorem fineBlockStandardH2Equiv_mk (l : LawValueLabel laws)
    (z : (fine.lawValueBlockComplex laws adequate l).C2) :
    fineBlockStandardH2Equiv l (oldH2Equiv (fine.lawValueBlockComplex laws adequate l)
      ((LinearMap.range (fine.lawValueBlockComplex laws adequate l).d1).mkQ z)) =
      namedDifference ((fineBlockEquiv l).e2 z) := by
  exact (congrArg (fun x => fineNamedH2Equiv ((oldH2Equiv (namedComplex fine)).symm x))
    (fullBlockNamedHomologyEquiv_oldH2_mk fine laws adequate fine_chart_full fine_edge_full fine_face_full l z)).trans (by
      rw [LinearEquiv.symm_apply_apply, fineNamedH2Equiv_mk]
      rfl)
/-- 独立実Law座標での複製面単独1cochain。 -/
def blockFreshOnly (l : LawValueLabel laws) : (fine.lawValueBlockComplex laws adequate l).C2 :=
  (fineBlockEquiv l).e2.symm (namedFreshOnly 1)
/-- 独立実Law座標での複製面単独1標準H²類。 -/
def blockFreshClass (l : LawValueLabel laws) : (zeroExtension (fine.lawValueBlockComplex laws adequate l)).homology 2 :=
  oldH2Equiv (fine.lawValueBlockComplex laws adequate l)
    ((LinearMap.range (fine.lawValueBlockComplex laws adequate l).d1).mkQ (blockFreshOnly l))
/-- 同じ実Law複製単独類の差は1。 -/
@[simp] theorem blockFreshClass_difference (l : LawValueLabel laws) :
    fineBlockStandardH2Equiv l (blockFreshClass l) = 1 := by
  rw [blockFreshClass, fineBlockStandardH2Equiv_mk, blockFreshOnly,
    LinearEquiv.apply_symm_apply, namedDifference_freshOnly]
/-- 同じ実Law複製単独類は非零。 -/
theorem blockFreshClass_nonzero (l : LawValueLabel laws) : blockFreshClass l ≠ 0 := by
  intro hz
  have he := congrArg (fineBlockStandardH2Equiv l) hz
  rw [blockFreshClass_difference, map_zero] at he
  exact one_ne_zero he
/-- 同じ独立block比較の標準H²射は零空間からの零射。 -/
theorem block_h2Map_zero (l : LawValueLabel laws) :
    (homologyMap (zeroExtensionMap (FaceDuplication.blockHom N () laws adequate l)) 2).hom = 0 := by
  letI := block_standardH2_subsingleton l
  apply LinearMap.ext
  intro x
  rw [Subsingleton.elim x 0, map_zero]
  rfl
/-- 同じ実比較のH²余核で複製面単独1が非零となる。 -/
theorem blockFresh_cokernel_nonzero (l : LawValueLabel laws) :
    (LinearMap.range (homologyMap (zeroExtensionMap (FaceDuplication.blockHom N () laws adequate l)) 2).hom).mkQ
      (blockFreshClass l) ≠ 0 := by
  intro hz
  have hm := (Submodule.Quotient.mk_eq_zero _).mp hz
  rw [block_h2Map_zero, LinearMap.range_zero] at hm
  exact blockFreshClass_nonzero l hm

end AAT.AG.FaceRelationSubdivision.WitnessThree
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision.WitnessThree
