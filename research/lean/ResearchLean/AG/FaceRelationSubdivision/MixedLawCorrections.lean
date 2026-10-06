import ResearchLean.AG.FaceRelationSubdivision.MixedLawFiniteFunctor

/-!
# 原始二補正式の独立Law有限和への移送

## Implementation notes

原始三項式を支持基底射の和と合成で表し、同じ有限和の等号として検査する。
一般補題の補正式は方向仮定であり、原始操作列では生成済みr/s/h/k式で放電する。
標準ホモトピーを仮定にする案は用いない。
-/
noncomputable section
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution ResolutionInvariance
universe u
variable {Source I I0 I2 : Type u} {q : Reading Source}
variable {si : I → Set q.Target} {si0 : I0 → Set q.Target} {si2 : I2 → Set q.Target}
namespace SupportedBasisMap
variable (laws : FiniteLawFamily Source) (ha : laws.Adequate q)

/-- 頂点または面の原始二項補正式を同じLaw射の式へ運ぶ。 -/
theorem mixedLaw_correction_two
    (P : SupportedBasisMap (sourceSupport q si) (sourceSupport q si))
    (h : SupportedBasisMap (sourceSupport q si) (sourceSupport q si2))
    (d : SupportedBasisMap (sourceSupport q si2) (sourceSupport q si))
    (he : P.raw + d.raw.comp h.raw = LinearMap.id) :
    P.mixedLawDual laws ha ha + (h.mixedLawDual laws ha ha).comp (d.mixedLawDual laws ha ha) = LinearMap.id := by
  have hr : (P.add (h.comp d)).raw = (identity (sourceSupport q si)).raw := by
    rw [raw_add, raw_comp, raw_identity]
    exact he
  have hh := (P.add (h.comp d)).mixedLawDual_eq_of_raw_eq laws ha ha
    (identity (sourceSupport q si)) hr
  rw [mixedLawDual_add, mixedLawDual_comp, mixedLawDual_identity] at hh
  exact hh

/-- 辺の原始三項補正式を同じ二Law補正の式へ運ぶ。 -/
theorem mixedLaw_correction_three
    (P : SupportedBasisMap (sourceSupport q si) (sourceSupport q si))
    (h : SupportedBasisMap (sourceSupport q si) (sourceSupport q si2))
    (d2 : SupportedBasisMap (sourceSupport q si2) (sourceSupport q si))
    (d1 : SupportedBasisMap (sourceSupport q si) (sourceSupport q si0))
    (k : SupportedBasisMap (sourceSupport q si0) (sourceSupport q si))
    (he : P.raw + d2.raw.comp h.raw + k.raw.comp d1.raw = LinearMap.id) :
    P.mixedLawDual laws ha ha + (h.mixedLawDual laws ha ha).comp (d2.mixedLawDual laws ha ha) +
      (d1.mixedLawDual laws ha ha).comp (k.mixedLawDual laws ha ha) = LinearMap.id := by
  have hr : ((P.add (h.comp d2)).add (d1.comp k)).raw = (identity (sourceSupport q si)).raw := by
    rw [raw_add, raw_add, raw_comp, raw_comp, raw_identity]
    exact he
  have hh := ((P.add (h.comp d2)).add (d1.comp k)).mixedLawDual_eq_of_raw_eq laws ha ha
    (identity (sourceSupport q si)) hr
  rw [mixedLawDual_add, mixedLawDual_add, mixedLawDual_comp, mixedLawDual_comp,
    mixedLawDual_identity] at hh
  exact hh

end SupportedBasisMap
end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
