import ResearchLean.AG.AtlasDefectComposition.SubsetRestriction
import ResearchLean.AG.AtlasDefectComposition.CochainEquivalence
import Formal.Util.AssertStandardAxioms
/-! # 同じ実セル選択の指定同値

Implementation notes: 両方向の実選択包含は同じセル名を固定する。
順逆座標制限を線形同値にまとめ、G-107 の CochainEquiv と標準零延長に接続する。
-/
noncomputable section
namespace AAT.AG.AtlasDefectComposition.SubsetRestriction
open CanonicalResolution ResolutionInvariance TwoPhase CategoryTheory
universe u
variable {Source : Type u} {q : Reading Source} (N : TargetSupportedNerve q)
variable {A B : Set q.Target} (h : SelectedLE N A B) (k : SelectedLE N B A)
/-- 同選択の chart セル同値。順逆とも元のセルを固定する。 -/
def chartEquiv : N.ChartInTargetSubset A ≃ N.ChartInTargetSubset B where
  toFun := chartInclusion N h
  invFun := chartInclusion N k
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
/-- 同選択の次数 0 の順逆座標制限は線形同値を生成する。 -/
def equiv0 : (N.targetSubsetComplex B).C0 ≃ₗ[ℚ] (N.targetSubsetComplex A).C0 :=
  LinearEquiv.ofLinear (restrict0 N h) (restrict0 N k)
    (by ext x; rfl) (by ext x; rfl)
/-- 次数 0 の指定線形同値は順方向制限そのものである。 -/
@[simp] theorem equiv0_toLinearMap : (equiv0 N h k).toLinearMap = restrict0 N h := rfl
/-- 次数 0 の指定同値の逆射は逆方向制限そのものである。 -/
@[simp] theorem equiv0_symm_toLinearMap : (equiv0 N h k).symm.toLinearMap = restrict0 N k := rfl
/-- 同選択の edge セル同値。順逆とも元のセルを固定する。 -/
def edgeEquiv : N.EdgeInTargetSubset A ≃ N.EdgeInTargetSubset B where
  toFun := edgeInclusion N h
  invFun := edgeInclusion N k
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
/-- 同選択の次数 1 の順逆座標制限は線形同値を生成する。 -/
def equiv1 : (N.targetSubsetComplex B).C1 ≃ₗ[ℚ] (N.targetSubsetComplex A).C1 :=
  LinearEquiv.ofLinear (restrict1 N h) (restrict1 N k)
    (by ext x; rfl) (by ext x; rfl)
/-- 次数 1 の指定線形同値は順方向制限そのものである。 -/
@[simp] theorem equiv1_toLinearMap : (equiv1 N h k).toLinearMap = restrict1 N h := rfl
/-- 次数 1 の指定同値の逆射は逆方向制限そのものである。 -/
@[simp] theorem equiv1_symm_toLinearMap : (equiv1 N h k).symm.toLinearMap = restrict1 N k := rfl
/-- 同選択の face セル同値。順逆とも元のセルを固定する。 -/
def faceEquiv : N.FaceInTargetSubset A ≃ N.FaceInTargetSubset B where
  toFun := faceInclusion N h
  invFun := faceInclusion N k
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
/-- 同選択の次数 2 の順逆座標制限は線形同値を生成する。 -/
def equiv2 : (N.targetSubsetComplex B).C2 ≃ₗ[ℚ] (N.targetSubsetComplex A).C2 :=
  LinearEquiv.ofLinear (restrict2 N h) (restrict2 N k)
    (by ext x; rfl) (by ext x; rfl)
/-- 次数 2 の指定線形同値は順方向制限そのものである。 -/
@[simp] theorem equiv2_toLinearMap : (equiv2 N h k).toLinearMap = restrict2 N h := rfl
/-- 次数 2 の指定同値の逆射は逆方向制限そのものである。 -/
@[simp] theorem equiv2_symm_toLinearMap : (equiv2 N h k).symm.toLinearMap = restrict2 N k := rfl
/-- 同じ全選択セルから生成した三項複体の同値。 -/
def cochainEquiv : ThreeCochainComplex.CochainEquiv (N.targetSubsetComplex B) (N.targetSubsetComplex A) where
  e0 := equiv0 N h k
  e1 := equiv1 N h k
  e2 := equiv2 N h k
  comm0 := restrict_d0 N h
  comm1 := restrict_d1 N h
/-- 指定同値の実 Hom は台制限と一致する。 -/
@[simp] theorem cochainEquiv_toHom : (cochainEquiv N h k).toHom = hom N h := rfl
/-- 指定同値の逆 Hom も台制限と一致する。 -/
@[simp] theorem cochainEquiv_symm_toHom : (cochainEquiv N h k).symm.toHom = hom N k := rfl
/-- 同じ全セル選択の標準零延長同型。 -/
def complexIso : zeroExtension (N.targetSubsetComplex B) ≅ zeroExtension (N.targetSubsetComplex A) :=
  cochainEquivZeroExtensionIso (cochainEquiv N h k)
/-- 同じセル選択の H¹ 同型は既存の商同値を用いる。 -/
def h1Equiv : (N.targetSubsetComplex B).H1 ≃ₗ[ℚ] (N.targetSubsetComplex A).H1 :=
  (cochainEquiv N h k).h1Equiv
end AAT.AG.AtlasDefectComposition.SubsetRestriction
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition.SubsetRestriction
