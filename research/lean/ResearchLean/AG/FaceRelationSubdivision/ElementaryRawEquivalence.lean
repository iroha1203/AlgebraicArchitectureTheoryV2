import ResearchLean.AG.FaceRelationSubdivision.RawChainEquivalence
import ResearchLean.AG.FaceRelationSubdivision.TriangleContraction
import ResearchLean.AG.FaceRelationSubdivision.EdgeContraction

/-!
# 正基本操作の同じ原始二方向出力

## Implementation notes

既存の正操作セル表のr/s/hをSource台へ運び、旧側補正を零有限和として生成する。
原始chain式を既存の受理済み式で放電する。診断同型を受け取る案は用いない。
-/
noncomputable section
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution ResolutionInvariance
universe u
variable {Source : Type u} {q : Reading Source}
namespace TriangleAddition
variable (N : TargetSupportedNerve q) (e : N.nerve.EdgeComponent)

/-- 原始正操作から生成した同じr/s/hと零の旧側補正。 -/
def rawEquivalence : RawChainEquivalence N (supported N e) where
  r0 := (r0 N e).toSource
  r1 := (r1 N e).toSource
  r2 := (r2 N e).toSource
  s0 := (s0 N e).toSource
  s1 := (s1 N e).toSource
  s2 := (s2 N e).toSource
  h0 := (h0 N e).toSource
  h1 := (h1 N e).toSource
  k0 := SupportedBasisMap.zero _ _
  k1 := SupportedBasisMap.zero _ _
  r_comm01 := r_comm01 N e
  r_comm12 := r_comm12 N e
  s_comm01 := s_comm01 N e
  s_comm12 := s_comm12 N e
  sr_h0 := sr_h0 N e
  sr_h1 := sr_h1 N e
  sr_h2 := sr_h2 N e
  rs_k0 := by simp only [SupportedBasisMap.toSource_raw, SupportedBasisMap.raw_zero, LinearMap.comp_zero, add_zero, rs0]
  rs_k1 := by simp only [SupportedBasisMap.toSource_raw, SupportedBasisMap.raw_zero, LinearMap.comp_zero, LinearMap.zero_comp, add_zero, rs1]
  rs_k2 := by simp only [SupportedBasisMap.toSource_raw, SupportedBasisMap.raw_zero, LinearMap.zero_comp, add_zero, rs2]

/-- 有限列出力の原始r0は受理済み同じ基本操作のSource台有限和。 -/
@[simp] theorem rawEquivalence_r0 : (rawEquivalence N e).r0 = (r0 N e).toSource := rfl
/-- 有限列出力の原始r1は受理済み同じ基本操作のSource台有限和。 -/
@[simp] theorem rawEquivalence_r1 : (rawEquivalence N e).r1 = (r1 N e).toSource := rfl
/-- 有限列出力の原始r2は受理済み同じ基本操作のSource台有限和。 -/
@[simp] theorem rawEquivalence_r2 : (rawEquivalence N e).r2 = (r2 N e).toSource := rfl
/-- 有限列出力の原始s0は受理済み同じ基本操作のSource台有限和。 -/
@[simp] theorem rawEquivalence_s0 : (rawEquivalence N e).s0 = (s0 N e).toSource := rfl
/-- 有限列出力の原始s1は受理済み同じ基本操作のSource台有限和。 -/
@[simp] theorem rawEquivalence_s1 : (rawEquivalence N e).s1 = (s1 N e).toSource := rfl
/-- 有限列出力の原始s2は受理済み同じ基本操作のSource台有限和。 -/
@[simp] theorem rawEquivalence_s2 : (rawEquivalence N e).s2 = (s2 N e).toSource := rfl
/-- 有限列出力の原始h0は受理済み同じ基本操作のSource台有限和。 -/
@[simp] theorem rawEquivalence_h0 : (rawEquivalence N e).h0 = (h0 N e).toSource := rfl
/-- 有限列出力の原始h1は受理済み同じ基本操作のSource台有限和。 -/
@[simp] theorem rawEquivalence_h1 : (rawEquivalence N e).h1 = (h1 N e).toSource := rfl

end TriangleAddition
namespace EdgeSubdivision
variable (N : TargetSupportedNerve q) (e : N.nerve.EdgeComponent)

/-- 原始正操作から生成した同じr/s/hと零の旧側補正。 -/
def rawEquivalence : RawChainEquivalence N (supported N e) where
  r0 := (r0 N e).toSource
  r1 := (r1 N e).toSource
  r2 := (r2 N e).toSource
  s0 := (s0 N e).toSource
  s1 := (s1 N e).toSource
  s2 := (s2 N e).toSource
  h0 := (h0 N e).toSource
  h1 := (h1 N e).toSource
  k0 := SupportedBasisMap.zero _ _
  k1 := SupportedBasisMap.zero _ _
  r_comm01 := r_comm01 N e
  r_comm12 := r_comm12 N e
  s_comm01 := s_comm01 N e
  s_comm12 := s_comm12 N e
  sr_h0 := sr_h0 N e
  sr_h1 := sr_h1 N e
  sr_h2 := sr_h2 N e
  rs_k0 := by simp only [SupportedBasisMap.toSource_raw, SupportedBasisMap.raw_zero, LinearMap.comp_zero, add_zero, rs0]
  rs_k1 := by simp only [SupportedBasisMap.toSource_raw, SupportedBasisMap.raw_zero, LinearMap.comp_zero, LinearMap.zero_comp, add_zero, rs1]
  rs_k2 := by simp only [SupportedBasisMap.toSource_raw, SupportedBasisMap.raw_zero, LinearMap.zero_comp, add_zero, rs2]

/-- 有限列出力の原始r0は受理済み同じ基本操作のSource台有限和。 -/
@[simp] theorem rawEquivalence_r0 : (rawEquivalence N e).r0 = (r0 N e).toSource := rfl
/-- 有限列出力の原始r1は受理済み同じ基本操作のSource台有限和。 -/
@[simp] theorem rawEquivalence_r1 : (rawEquivalence N e).r1 = (r1 N e).toSource := rfl
/-- 有限列出力の原始r2は受理済み同じ基本操作のSource台有限和。 -/
@[simp] theorem rawEquivalence_r2 : (rawEquivalence N e).r2 = (r2 N e).toSource := rfl
/-- 有限列出力の原始s0は受理済み同じ基本操作のSource台有限和。 -/
@[simp] theorem rawEquivalence_s0 : (rawEquivalence N e).s0 = (s0 N e).toSource := rfl
/-- 有限列出力の原始s1は受理済み同じ基本操作のSource台有限和。 -/
@[simp] theorem rawEquivalence_s1 : (rawEquivalence N e).s1 = (s1 N e).toSource := rfl
/-- 有限列出力の原始s2は受理済み同じ基本操作のSource台有限和。 -/
@[simp] theorem rawEquivalence_s2 : (rawEquivalence N e).s2 = (s2 N e).toSource := rfl
/-- 有限列出力の原始h0は受理済み同じ基本操作のSource台有限和。 -/
@[simp] theorem rawEquivalence_h0 : (rawEquivalence N e).h0 = (h0 N e).toSource := rfl
/-- 有限列出力の原始h1は受理済み同じ基本操作のSource台有限和。 -/
@[simp] theorem rawEquivalence_h1 : (rawEquivalence N e).h1 = (h1 N e).toSource := rfl

end EdgeSubdivision
end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
