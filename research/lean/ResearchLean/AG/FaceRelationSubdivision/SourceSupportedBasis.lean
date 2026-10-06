import ResearchLean.AG.FaceRelationSubdivision.RawSupportedChain
import ResearchLean.AG.FaceRelationSubdivision.ReadingPullback

/-!
# 原始セル台のSource逆像

## Implementation notes

readingの異なる操作を同じSourceの台で合成する。基底像は変更せず、
台包含だけをreadingの逆像へ運ぶ。Law座標の共役を原始射として使う案は
独立生成を隠すため採らない。これは台の表示であり新しい操作ではない。
-/
noncomputable section
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution ResolutionInvariance
universe u
variable {Source I J : Type u} {q : Reading Source}

/-- 原始target台をSourceで読む。 -/
def sourceSupport (q : Reading Source) (s : I → Set q.Target) : I → Set Source :=
  fun i => q.read ⁻¹' s i

/-- Source台のmembershipは同じreading値でのmembership。 -/
@[simp] theorem mem_sourceSupport (s : I → Set q.Target) (i : I) (x : Source) :
    x ∈ sourceSupport q s i ↔ q.read x ∈ s i := Iff.rfl

namespace SupportedBasisMap
variable {si : I → Set q.Target} {sj : J → Set q.Target}

/-- 同じ原始有限和をSource台で表す。 -/
def toSource (M : SupportedBasisMap si sj) :
    SupportedBasisMap (sourceSupport q si) (sourceSupport q sj) where
  basisImage := M.basisImage
  support_compatible := fun i j hj _ ht => M.support_compatible i j hj ht

/-- Source表示でも原始基底係数は同じ。 -/
@[simp] theorem toSource_basis (M : SupportedBasisMap si sj) (i) :
    M.toSource.basisImage i = M.basisImage i := rfl

/-- Source表示でも全セルの原始線形射は同じ。 -/
@[simp] theorem toSource_raw (M : SupportedBasisMap si sj) : M.toSource.raw = M.raw := rfl

/-- 同じ原始有限和のSource台化は直接合成と可換。 -/
theorem toSource_comp {K : Type u} {sk : K → Set q.Target}
    (M : SupportedBasisMap si sj) (N : SupportedBasisMap sj sk) :
    (M.comp N).toSource = M.toSource.comp N.toSource := by
  apply SupportedBasisMap.ext_raw
  rw [toSource_raw, raw_comp, raw_comp, toSource_raw, toSource_raw]

end SupportedBasisMap

namespace TargetSupportedNerve
variable (N : ResolutionInvariance.TargetSupportedNerve q)

/-- Source台を保つ同じ端点差分。 -/
def sourceD1 := (rawD1 N).toSource
/-- Source台を保つ同じ三辺符号和。 -/
def sourceD2 := (rawD2 N).toSource
/-- Source端点差分は原始支持差分の同じ台表示。 -/
@[simp] theorem sourceD1_eq_toSource : sourceD1 N = (rawD1 N).toSource := rfl
/-- Source三辺差分は原始支持差分の同じ台表示。 -/
@[simp] theorem sourceD2_eq_toSource : sourceD2 N = (rawD2 N).toSource := rfl
/-- Source台でも端点差分の実線形射は同じ。 -/
@[simp] theorem sourceD1_raw : (sourceD1 N).raw = (rawD1 N).raw := rfl
/-- Source台でも三辺符号和の実線形射は同じ。 -/
@[simp] theorem sourceD2_raw : (sourceD2 N).raw = (rawD2 N).raw := rfl

end TargetSupportedNerve

/-- reading変更ではSource上のchart台は変わらない。 -/
theorem readingPullback_source_chart {qf : Reading Source} (N : TargetSupportedNerve q)
    (h : q.CoarserThan qf) (v) :
    sourceSupport qf (readingPullback N h).chartSupport v =
      sourceSupport q N.chartSupport v := by
  ext x
  simp only [mem_sourceSupport, readingPullback_chartSupport, Set.mem_preimage,
    comparisonFactor_commutes]

end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
