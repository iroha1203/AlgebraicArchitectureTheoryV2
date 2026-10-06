import ResearchLean.AG.FaceRelationSubdivision.MixedLawFiniteFunctor
import ResearchLean.AG.FaceRelationSubdivision.LawFiniteDifferential

/-!
# 混在有限和と既存の実Law微分

## Implementation notes

同じreadingの原始支持射について非零項ごとの座標等号を証明する。
既存微分とC6の同定に接続し、readingの異なるchain式を同じ実Law微分へ渡す。
抽象同型だけで微分一致を推測する案は採らない。
-/
noncomputable section
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution ResolutionInvariance
universe u
variable {Source I J : Type u} {q : Reading Source}
namespace SupportedBasisMap
variable {si : I → Set q.Target} {sj : J → Set q.Target}
variable (M : SupportedBasisMap si sj) (laws : FiniteLawFamily Source) (ha : laws.Adequate q)

/-- 同じreadingのSource表示輸送は原始Law輸送と同じ座標。 -/
theorem toSource_mixedLawCoordinate (x) (j) (hne) :
    M.toSource.mixedLawCoordinate laws ha ha x j hne = M.lawCoordinate laws ha x j hne := by
  apply CellCoordinate.ext <;> rfl

/-- Source表示の独立有限和は同じreadingの独立Law有限和に一致。 -/
theorem toSource_mixedLawDual : M.toSource.mixedLawDual laws ha ha = M.lawDual laws ha := by
  apply LinearMap.ext
  intro z
  funext x
  rw [mixedLawDual_apply, lawDual_apply]
  simp only [toSource_basis]
  apply Finset.sum_congr rfl
  intro j hj
  rw [toSource_mixedLawCoordinate]

end SupportedBasisMap
variable (N : TargetSupportedNerve q) (laws : FiniteLawFamily Source) (ha : laws.Adequate q)

/-- Source台の端点差分の混在Law双対は実lawGeneratedD0。 -/
theorem mixedLaw_sourceD1 :
    (TargetSupportedNerve.sourceD1 N).mixedLawDual laws ha ha = N.lawGeneratedD0 laws ha := by
  rw [TargetSupportedNerve.sourceD1_eq_toSource, SupportedBasisMap.toSource_mixedLawDual, lawDual_rawD1]

/-- Source台の三辺符号和の混在Law双対は実lawGeneratedD1。 -/
theorem mixedLaw_sourceD2 :
    (TargetSupportedNerve.sourceD2 N).mixedLawDual laws ha ha = N.lawGeneratedD1 laws ha := by
  rw [TargetSupportedNerve.sourceD2_eq_toSource, SupportedBasisMap.toSource_mixedLawDual, lawDual_rawD2]

end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
