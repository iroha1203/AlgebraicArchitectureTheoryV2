import ResearchLean.AG.AtlasCoefficientFiber.PrimitiveRankCriterion
import ResearchLean.AG.UniformInvariance.ExecutableRationalRank
import Mathlib.LinearAlgebra.Basis.Prod

/-!
# G-135 B：原始セル自由基底での同じ制約とblock行列

基底は名前付きセルのsingle基底とその積だけ。homology基底や期待rankは使わない。

## Implementation notes

原セル名を保持するsingle基底と積基底を使い、toMatrixで元射を全元に表示する。
行・列のSumの括弧は元射の積構造を反映し、二制約と重複するセル名を保持する。
homologyや核の基底を供給する方法は、原始入力からの表示に追加の選択を要するため採らない。
一部の列だけの評価では全元表示とrankの接続を保証しないため、標準toMatrixの両APIを使う。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CanonicalResolution ResolutionInvariance FaceRelationSubdivision Module
universe u

/-- 任意の指定基底で、既存toMatrixは全元で同じ射を表示する。 -/
theorem matrix_represents_map {I J X Y : Type u} [Fintype I] [Finite J] [DecidableEq I]
    [AddCommGroup X] [Module ℚ X] [AddCommGroup Y] [Module ℚ Y]
    (b : Basis I ℚ X) (c : Basis J ℚ Y) (f : X →ₗ[ℚ] Y) (x : X) :
    (LinearMap.toMatrix b c f).mulVec (b.repr x) = c.repr (f x) := by
  classical
  exact LinearMap.toMatrix_mulVec_repr b c f x

/-- 既存toMatrixのrankは同じ元射のrange次元。 -/
theorem matrix_rank_eq_range {I J X Y : Type u} [Fintype I] [Finite J] [DecidableEq I]
    [AddCommGroup X] [Module ℚ X] [AddCommGroup Y] [Module ℚ Y]
    (b : Basis I ℚ X) (c : Basis J ℚ Y) (f : X →ₗ[ℚ] Y) :
    (LinearMap.toMatrix b c f).rank = finrank ℚ (LinearMap.range f) := by
  classical
  rw [Matrix.rank_eq_finrank_range_toLin _ c b, Matrix.toLin_toMatrix]

variable {Source : Type u} {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve.{u,u} qc} {Nf : TargetSupportedNerve.{u,u} qf}
variable (M : IncidenceSupportedComparison qc qf h Nc Nf) (A : Set qc.Target)

/-- 元Bの各原セル列を返す行列。 -/
def primitiveBMatrix [Fintype (MixedFace M A)] : Matrix (HorizontalEdge M A) (MixedFace M A) ℚ := by
  classical
  exact LinearMap.toMatrix Finsupp.basisSingleOne Finsupp.basisSingleOne
    (mixedHorizontalBoundary M A)

/-- B表示の所有API。有限な元混在面の各列を原Bのsingle評価へ正規化する。 -/
@[simp] theorem primitiveBMatrix_entry [Fintype (MixedFace M A)] (e : HorizontalEdge M A) (f : MixedFace M A) :
    primitiveBMatrix M A e f = mixedHorizontalBoundary M A (Finsupp.single f 1) e := by
  classical
  rw [primitiveBMatrix, LinearMap.toMatrix_apply]
  rfl

/-- 元Dの各原セル列を返す行列。 -/
def primitiveDMatrix [Fintype (MixedFace M A)] : Matrix (VerticalEdge M A) (MixedFace M A) ℚ := by
  classical
  exact LinearMap.toMatrix Finsupp.basisSingleOne Finsupp.basisSingleOne
    (mixedVerticalBoundary M A)

/-- D表示の所有API。有限な元混在面の各列を原Dのsingle評価へ正規化する。 -/
@[simp] theorem primitiveDMatrix_entry [Fintype (MixedFace M A)] (e : VerticalEdge M A) (f : MixedFace M A) :
    primitiveDMatrix M A e f = mixedVerticalBoundary M A (Finsupp.single f 1) e := by
  classical
  rw [primitiveDMatrix, LinearMap.toMatrix_apply]
  rfl

/-- 元Hの各原セル列を返す行列。 -/
def primitiveHMatrix [Fintype (HorizontalFace M A)] : Matrix (HorizontalEdge M A) (HorizontalFace M A) ℚ := by
  classical
  exact LinearMap.toMatrix Finsupp.basisSingleOne Finsupp.basisSingleOne
    (horizontalFaceBoundary M A)

/-- H表示の所有API。有限な元水平面の各列を原Hのsingle評価へ正規化する。 -/
@[simp] theorem primitiveHMatrix_entry [Fintype (HorizontalFace M A)] (e : HorizontalEdge M A) (f : HorizontalFace M A) :
    primitiveHMatrix M A e f = horizontalFaceBoundary M A (Finsupp.single f 1) e := by
  classical
  rw [primitiveHMatrix, LinearMap.toMatrix_apply]
  rfl

/-- 元Vの各原セル列を返す行列。 -/
def primitiveVMatrix [Fintype (VerticalFace M A)] : Matrix (VerticalEdge M A) (VerticalFace M A) ℚ := by
  classical
  exact LinearMap.toMatrix Finsupp.basisSingleOne Finsupp.basisSingleOne
    (verticalBoundary M A)

/-- V表示の所有API。有限な元垂直面の各列を原Vのsingle評価へ正規化する。 -/
@[simp] theorem primitiveVMatrix_entry [Fintype (VerticalFace M A)] (e : VerticalEdge M A) (f : VerticalFace M A) :
    primitiveVMatrix M A e f = verticalBoundary M A (Finsupp.single f 1) e := by
  classical
  rw [primitiveVMatrix, LinearMap.toMatrix_apply]
  rfl

/-- 元By-Hxの原セル積基底での表示。 -/
def primitiveConstraintMatrix [Fintype (MixedFace M A)] [Fintype (HorizontalFace M A)] :
    Matrix (HorizontalEdge M A) (MixedFace M A ⊕ HorizontalFace M A) ℚ := by
  classical
  exact LinearMap.toMatrix (Finsupp.basisSingleOne.prod Finsupp.basisSingleOne)
    Finsupp.basisSingleOne (primitiveConstraint M A)

/-- 元(Vv+Dt,Bt)の原セル積基底での表示。 -/
def primitiveBaseMatrix [Fintype (VerticalFace M A)] [Fintype (MixedFace M A)] : Matrix (VerticalEdge M A ⊕ HorizontalEdge M A)
    (VerticalFace M A ⊕ MixedFace M A) ℚ := by
  classical
  exact LinearMap.toMatrix (Finsupp.basisSingleOne.prod Finsupp.basisSingleOne)
    (Finsupp.basisSingleOne.prod Finsupp.basisSingleOne) (primitiveBaseBlock M A)

/-- 原Giantの各制約を別行blockに保った原セル表示。 -/
def primitiveGiantMatrix [Fintype (VerticalFace M A)] [Fintype (MixedFace M A)] [Fintype (HorizontalFace M A)] :
    Matrix (VerticalEdge M A ⊕ (HorizontalEdge M A ⊕ HorizontalEdge M A))
      ((VerticalFace M A ⊕ MixedFace M A) ⊕ (MixedFace M A ⊕ HorizontalFace M A)) ℚ := by
  classical
  exact LinearMap.toMatrix
    ((Finsupp.basisSingleOne.prod Finsupp.basisSingleOne).prod
      (Finsupp.basisSingleOne.prod Finsupp.basisSingleOne))
    (Finsupp.basisSingleOne.prod (Finsupp.basisSingleOne.prod Finsupp.basisSingleOne))
    (primitiveGiantBlock M A)

/-- 制約行列の所有API：元の名前付き積基底の各列を返す。 -/
theorem primitiveConstraintMatrix_entry [Fintype (MixedFace M A)]
    [Fintype (HorizontalFace M A)] (e : HorizontalEdge M A)
    (f : MixedFace M A ⊕ HorizontalFace M A) :
    primitiveConstraintMatrix M A e f =
      primitiveConstraint M A ((Finsupp.basisSingleOne.prod Finsupp.basisSingleOne) f) e := by
  classical
  rw [primitiveConstraintMatrix, LinearMap.toMatrix_apply]
  rfl

/-- WB行列の所有API：各元セル列は同じ元WBを評価する。 -/
theorem primitiveBaseMatrix_entry [Fintype (VerticalFace M A)] [Fintype (MixedFace M A)]
    (e : VerticalEdge M A ⊕ HorizontalEdge M A) (f : VerticalFace M A ⊕ MixedFace M A) :
    primitiveBaseMatrix M A e f =
      (Finsupp.basisSingleOne.prod Finsupp.basisSingleOne).repr
        (primitiveBaseBlock M A ((Finsupp.basisSingleOne.prod Finsupp.basisSingleOne) f)) e := by
  classical
  rw [primitiveBaseMatrix, LinearMap.toMatrix_apply]

/-- Giant行列の所有API：二制約を保つ元射の各セル列を返す。 -/
theorem primitiveGiantMatrix_entry [Fintype (VerticalFace M A)] [Fintype (MixedFace M A)]
    [Fintype (HorizontalFace M A)]
    (e : VerticalEdge M A ⊕ (HorizontalEdge M A ⊕ HorizontalEdge M A))
    (f : (VerticalFace M A ⊕ MixedFace M A) ⊕ (MixedFace M A ⊕ HorizontalFace M A)) :
    primitiveGiantMatrix M A e f =
      (Finsupp.basisSingleOne.prod (Finsupp.basisSingleOne.prod Finsupp.basisSingleOne)).repr
        (primitiveGiantBlock M A
          (((Finsupp.basisSingleOne.prod Finsupp.basisSingleOne).prod
            (Finsupp.basisSingleOne.prod Finsupp.basisSingleOne)) f)) e := by
  classical
  rw [primitiveGiantMatrix, LinearMap.toMatrix_apply]

/-- 元有限セルの積基底により、任意の鎖に対する制約行列の作用が同じ元制約射を表示する。 -/
theorem primitiveConstraintMatrix_represents [Fintype (MixedFace M A)] [Fintype (HorizontalFace M A)] (x : (MixedFace M A →₀ ℚ) ×
    (HorizontalFace M A →₀ ℚ)) :
    (primitiveConstraintMatrix M A).mulVec
      ((Finsupp.basisSingleOne.prod Finsupp.basisSingleOne).repr x) =
        primitiveConstraint M A x := by
  classical
  exact matrix_represents_map (Finsupp.basisSingleOne.prod Finsupp.basisSingleOne) Finsupp.basisSingleOne (primitiveConstraint M A) x

/-- 元有限セルの積基底により、任意の鎖に対するWB行列の作用が同じ元WBを表示する。 -/
theorem primitiveBaseMatrix_represents [Fintype (VerticalFace M A)] [Fintype (MixedFace M A)] (x : (VerticalFace M A →₀ ℚ) ×
    (MixedFace M A →₀ ℚ)) :
    (primitiveBaseMatrix M A).mulVec
      ((Finsupp.basisSingleOne.prod Finsupp.basisSingleOne).repr x) =
        (Finsupp.basisSingleOne.prod Finsupp.basisSingleOne).repr
          (primitiveBaseBlock M A x) := by
  classical
  exact matrix_represents_map (Finsupp.basisSingleOne.prod Finsupp.basisSingleOne) (Finsupp.basisSingleOne.prod Finsupp.basisSingleOne) (primitiveBaseBlock M A) x

/-- 元有限セルの積基底により、任意の鎖に対するGiant行列の作用が同じ二制約付き元射を表示する。 -/
theorem primitiveGiantMatrix_represents [Fintype (VerticalFace M A)] [Fintype (MixedFace M A)] [Fintype (HorizontalFace M A)] (x : ((VerticalFace M A →₀ ℚ) ×
    (MixedFace M A →₀ ℚ)) × ((MixedFace M A →₀ ℚ) × (HorizontalFace M A →₀ ℚ))) :
    (primitiveGiantMatrix M A).mulVec
      (((Finsupp.basisSingleOne.prod Finsupp.basisSingleOne).prod
        (Finsupp.basisSingleOne.prod Finsupp.basisSingleOne)).repr x) =
          (Finsupp.basisSingleOne.prod (Finsupp.basisSingleOne.prod Finsupp.basisSingleOne)).repr
            (primitiveGiantBlock M A x) := by
  classical
  exact matrix_represents_map ((Finsupp.basisSingleOne.prod Finsupp.basisSingleOne).prod (Finsupp.basisSingleOne.prod Finsupp.basisSingleOne)) (Finsupp.basisSingleOne.prod (Finsupp.basisSingleOne.prod Finsupp.basisSingleOne)) (primitiveGiantBlock M A) x

/-- 元有限セルの積基底での制約行列rankは、同じ元制約射の像の次元と一致する。 -/
theorem primitiveConstraintMatrix_rank [Fintype (MixedFace M A)] [Fintype (HorizontalFace M A)] : (primitiveConstraintMatrix M A).rank =
    finrank ℚ (LinearMap.range (primitiveConstraint M A)) := by
  classical
  exact matrix_rank_eq_range (Finsupp.basisSingleOne.prod Finsupp.basisSingleOne) Finsupp.basisSingleOne (primitiveConstraint M A)

/-- 元有限セルの積基底でのWB行列rankは、同じ元WBの像の次元と一致する。 -/
theorem primitiveBaseMatrix_rank [Fintype (VerticalFace M A)] [Fintype (MixedFace M A)] : (primitiveBaseMatrix M A).rank =
    finrank ℚ (LinearMap.range (primitiveBaseBlock M A)) := by
  classical
  exact matrix_rank_eq_range (Finsupp.basisSingleOne.prod Finsupp.basisSingleOne) (Finsupp.basisSingleOne.prod Finsupp.basisSingleOne) (primitiveBaseBlock M A)

/-- 元有限セルの積基底でのGiant行列rankは、同じ元Giantの像の次元と一致する。 -/
theorem primitiveGiantMatrix_rank [Fintype (VerticalFace M A)] [Fintype (MixedFace M A)] [Fintype (HorizontalFace M A)] : (primitiveGiantMatrix M A).rank =
    finrank ℚ (LinearMap.range (primitiveGiantBlock M A)) := by
  classical
  exact matrix_rank_eq_range ((Finsupp.basisSingleOne.prod Finsupp.basisSingleOne).prod (Finsupp.basisSingleOne.prod Finsupp.basisSingleOne)) (Finsupp.basisSingleOne.prod (Finsupp.basisSingleOne.prod Finsupp.basisSingleOne)) (primitiveGiantBlock M A)


/-- E whole-vector API for original B. Raw finite cell coordinates retain
all names and incidence occurrences, without a supplied homology basis. -/
theorem primitiveBMatrix_mulVec [Fintype (MixedFace M A)]
    (x : MixedFace M A →₀ ℚ) :
    (primitiveBMatrix M A).mulVec (x : MixedFace M A → ℚ) =
      (mixedHorizontalBoundary M A x : HorizontalEdge M A → ℚ) := by
  classical
  exact matrix_represents_map Finsupp.basisSingleOne Finsupp.basisSingleOne
    (mixedHorizontalBoundary M A) x

/-- E whole-vector API for original D. Raw finite cell coordinates retain
all names and incidence occurrences, without a supplied homology basis. -/
theorem primitiveDMatrix_mulVec [Fintype (MixedFace M A)]
    (x : MixedFace M A →₀ ℚ) :
    (primitiveDMatrix M A).mulVec (x : MixedFace M A → ℚ) =
      (mixedVerticalBoundary M A x : VerticalEdge M A → ℚ) := by
  classical
  exact matrix_represents_map Finsupp.basisSingleOne Finsupp.basisSingleOne
    (mixedVerticalBoundary M A) x

/-- E whole-vector API for original V. Raw finite cell coordinates retain
all names and incidence occurrences, without a supplied homology basis. -/
theorem primitiveVMatrix_mulVec [Fintype (VerticalFace M A)]
    (x : VerticalFace M A →₀ ℚ) :
    (primitiveVMatrix M A).mulVec (x : VerticalFace M A → ℚ) =
      (verticalBoundary M A x : VerticalEdge M A → ℚ) := by
  classical
  exact matrix_represents_map Finsupp.basisSingleOne Finsupp.basisSingleOne
    (verticalBoundary M A) x

end AAT.AG.AtlasCoefficientFiber

#print axioms AAT.AG.AtlasCoefficientFiber.matrix_represents_map
#print axioms AAT.AG.AtlasCoefficientFiber.matrix_rank_eq_range
#print axioms AAT.AG.AtlasCoefficientFiber.primitiveBMatrix
#print axioms AAT.AG.AtlasCoefficientFiber.primitiveBMatrix_entry
#print axioms AAT.AG.AtlasCoefficientFiber.primitiveDMatrix
#print axioms AAT.AG.AtlasCoefficientFiber.primitiveDMatrix_entry
#print axioms AAT.AG.AtlasCoefficientFiber.primitiveHMatrix
#print axioms AAT.AG.AtlasCoefficientFiber.primitiveHMatrix_entry
#print axioms AAT.AG.AtlasCoefficientFiber.primitiveVMatrix
#print axioms AAT.AG.AtlasCoefficientFiber.primitiveVMatrix_entry
#print axioms AAT.AG.AtlasCoefficientFiber.primitiveConstraintMatrix
#print axioms AAT.AG.AtlasCoefficientFiber.primitiveBaseMatrix
#print axioms AAT.AG.AtlasCoefficientFiber.primitiveGiantMatrix
#print axioms AAT.AG.AtlasCoefficientFiber.primitiveConstraintMatrix_entry
#print axioms AAT.AG.AtlasCoefficientFiber.primitiveBaseMatrix_entry
#print axioms AAT.AG.AtlasCoefficientFiber.primitiveGiantMatrix_entry
#print axioms AAT.AG.AtlasCoefficientFiber.primitiveConstraintMatrix_represents
#print axioms AAT.AG.AtlasCoefficientFiber.primitiveBaseMatrix_represents
#print axioms AAT.AG.AtlasCoefficientFiber.primitiveGiantMatrix_represents
#print axioms AAT.AG.AtlasCoefficientFiber.primitiveConstraintMatrix_rank
#print axioms AAT.AG.AtlasCoefficientFiber.primitiveBaseMatrix_rank
#print axioms AAT.AG.AtlasCoefficientFiber.primitiveGiantMatrix_rank
#print axioms AAT.AG.AtlasCoefficientFiber.primitiveBMatrix_mulVec
#print axioms AAT.AG.AtlasCoefficientFiber.primitiveDMatrix_mulVec
#print axioms AAT.AG.AtlasCoefficientFiber.primitiveVMatrix_mulVec
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
