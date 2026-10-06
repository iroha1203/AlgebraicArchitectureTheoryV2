import ResearchLean.AG.FaceRelationSubdivision.PrimitiveOperationPath
import ResearchLean.AG.FaceRelationSubdivision.MixedSubsetHomotopy
import ResearchLean.AG.FaceRelationSubdivision.RawLawHomotopy

/-!
# 原始有限操作列の同じ実subset・Law比較

## Implementation notes

列の幾何を先に固定し、全Aと任意の最初のadequate Lawを後から量化する。
終点adequacyと支持適合は原始reading因子から導く。実Homや保存certificateを
操作列の入力にする案は採らない。
-/
noncomputable section
open CategoryTheory
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution ResolutionInvariance TwoPhase AtlasDefectComposition
universe u
variable {Source : Type u} {qc qf : Reading Source}
variable {Nc : TargetSupportedNerve qc} {Nf : TargetSupportedNerve qf}
namespace PrimitiveOperationPath
variable (path : PrimitiveOperationPath qc Nc qf Nf)

/-- 任意Aの原始直接有限和から独立生成する実subset比較。 -/
def subsetR (A : Set qc.Target) :=
  path.rawEquivalence.targetRHom A (path.targetSubset A) (path.source_subset_eq A)
/-- 任意Aの同じ原始sから独立生成する実subset逆比較。 -/
def subsetS (A : Set qc.Target) :=
  path.rawEquivalence.targetSHom A (path.targetSubset A) (path.source_subset_eq A)
/-- 全Aの同じ原始r/sと二補正から標準subset同値を生成する。 -/
def subsetHomotopyEquiv (A : Set qc.Target) :=
  path.rawEquivalence.targetHomotopyEquiv A (path.targetSubset A) (path.source_subset_eq A)
/-- 実subset標準同値の順射は同じ独立比較。 -/
@[simp] theorem subsetHomotopyEquiv_hom (A) :
    (path.subsetHomotopyEquiv A).hom = zeroExtensionMap (path.subsetR A) := rfl
/-- 実subset標準同値の逆射は同じ独立逆比較。 -/
@[simp] theorem subsetHomotopyEquiv_inv (A) :
    (path.subsetHomotopyEquiv A).inv = zeroExtensionMap (path.subsetS A) := rfl

/-- 列の独立subset順射の生成経路。 -/
@[simp] theorem subsetR_eq_raw (A) : path.subsetR A =
    path.rawEquivalence.targetRHom A (path.targetSubset A) (path.source_subset_eq A) := rfl
/-- 列の独立subset逆射の生成経路。 -/
@[simp] theorem subsetS_eq_raw (A) : path.subsetS A =
    path.rawEquivalence.targetSHom A (path.targetSubset A) (path.source_subset_eq A) := rfl

variable [Fintype Source] (laws : FiniteLawFamily Source) (ha : laws.Adequate qc)

/-- 任意Lawの原始直接有限和から独立生成する同じ実Law比較。 -/
def lawR := path.rawEquivalence.lawR laws ha (path.adequate laws ha)
/-- 同じ原始s有限和から独立生成する同じ実Law逆比較。 -/
def lawS := path.rawEquivalence.lawS laws ha (path.adequate laws ha)
/-- 同じ原始r/s/h/kから任意Lawの標準同値を生成する。 -/
def lawHomotopyEquiv := path.rawEquivalence.lawHomotopyEquiv laws ha (path.adequate laws ha)
/-- 実Law標準同値の順射は同じ独立比較。 -/
@[simp] theorem lawHomotopyEquiv_hom :
    (path.lawHomotopyEquiv laws ha).hom = zeroExtensionMap (path.lawR laws ha) := rfl
/-- 実Law標準同値の逆射は同じ独立逆比較。 -/
@[simp] theorem lawHomotopyEquiv_inv :
    (path.lawHomotopyEquiv laws ha).inv = zeroExtensionMap (path.lawS laws ha) := rfl

/-- 列の独立Law順射の生成経路を公開する。 -/
@[simp] theorem lawR_eq_raw : path.lawR laws ha = path.rawEquivalence.lawR laws ha (path.adequate laws ha) := rfl
/-- 列の独立Law逆射の生成経路を公開する。 -/
@[simp] theorem lawS_eq_raw : path.lawS laws ha = path.rawEquivalence.lawS laws ha (path.adequate laws ha) := rfl

end PrimitiveOperationPath
end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
