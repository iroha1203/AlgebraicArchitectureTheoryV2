import ResearchLean.AG.AtlasCoefficientFiber.PrimitiveRankCriterion
import ResearchLean.AG.UniformInvariance.ExecutableRationalRank
import Mathlib.LinearAlgebra.Basis.Prod

/-!
# G-135 B：原始セル自由基底での同じ制約とblock行列

基底は名前付きセルのsingle基底とその積だけ。homology基底や期待rankは使わない。
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

theorem primitiveConstraintMatrix_represents [Fintype (MixedFace M A)] [Fintype (HorizontalFace M A)] (x : (MixedFace M A →₀ ℚ) ×
    (HorizontalFace M A →₀ ℚ)) :
    (primitiveConstraintMatrix M A).mulVec
      ((Finsupp.basisSingleOne.prod Finsupp.basisSingleOne).repr x) =
        primitiveConstraint M A x := by
  classical
  exact matrix_represents_map (Finsupp.basisSingleOne.prod Finsupp.basisSingleOne) Finsupp.basisSingleOne (primitiveConstraint M A) x

theorem primitiveBaseMatrix_represents [Fintype (VerticalFace M A)] [Fintype (MixedFace M A)] (x : (VerticalFace M A →₀ ℚ) ×
    (MixedFace M A →₀ ℚ)) :
    (primitiveBaseMatrix M A).mulVec
      ((Finsupp.basisSingleOne.prod Finsupp.basisSingleOne).repr x) =
        (Finsupp.basisSingleOne.prod Finsupp.basisSingleOne).repr
          (primitiveBaseBlock M A x) := by
  classical
  exact matrix_represents_map (Finsupp.basisSingleOne.prod Finsupp.basisSingleOne) (Finsupp.basisSingleOne.prod Finsupp.basisSingleOne) (primitiveBaseBlock M A) x

theorem primitiveGiantMatrix_represents [Fintype (VerticalFace M A)] [Fintype (MixedFace M A)] [Fintype (HorizontalFace M A)] (x : ((VerticalFace M A →₀ ℚ) ×
    (MixedFace M A →₀ ℚ)) × ((MixedFace M A →₀ ℚ) × (HorizontalFace M A →₀ ℚ))) :
    (primitiveGiantMatrix M A).mulVec
      (((Finsupp.basisSingleOne.prod Finsupp.basisSingleOne).prod
        (Finsupp.basisSingleOne.prod Finsupp.basisSingleOne)).repr x) =
          (Finsupp.basisSingleOne.prod (Finsupp.basisSingleOne.prod Finsupp.basisSingleOne)).repr
            (primitiveGiantBlock M A x) := by
  classical
  exact matrix_represents_map ((Finsupp.basisSingleOne.prod Finsupp.basisSingleOne).prod (Finsupp.basisSingleOne.prod Finsupp.basisSingleOne)) (Finsupp.basisSingleOne.prod (Finsupp.basisSingleOne.prod Finsupp.basisSingleOne)) (primitiveGiantBlock M A) x

theorem primitiveConstraintMatrix_rank [Fintype (MixedFace M A)] [Fintype (HorizontalFace M A)] : (primitiveConstraintMatrix M A).rank =
    finrank ℚ (LinearMap.range (primitiveConstraint M A)) := by
  classical
  exact matrix_rank_eq_range (Finsupp.basisSingleOne.prod Finsupp.basisSingleOne) Finsupp.basisSingleOne (primitiveConstraint M A)

theorem primitiveBaseMatrix_rank [Fintype (VerticalFace M A)] [Fintype (MixedFace M A)] : (primitiveBaseMatrix M A).rank =
    finrank ℚ (LinearMap.range (primitiveBaseBlock M A)) := by
  classical
  exact matrix_rank_eq_range (Finsupp.basisSingleOne.prod Finsupp.basisSingleOne) (Finsupp.basisSingleOne.prod Finsupp.basisSingleOne) (primitiveBaseBlock M A)

theorem primitiveGiantMatrix_rank [Fintype (VerticalFace M A)] [Fintype (MixedFace M A)] [Fintype (HorizontalFace M A)] : (primitiveGiantMatrix M A).rank =
    finrank ℚ (LinearMap.range (primitiveGiantBlock M A)) := by
  classical
  exact matrix_rank_eq_range ((Finsupp.basisSingleOne.prod Finsupp.basisSingleOne).prod (Finsupp.basisSingleOne.prod Finsupp.basisSingleOne)) (Finsupp.basisSingleOne.prod (Finsupp.basisSingleOne.prod Finsupp.basisSingleOne)) (primitiveGiantBlock M A)

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
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
