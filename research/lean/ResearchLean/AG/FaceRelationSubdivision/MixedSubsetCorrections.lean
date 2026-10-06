import ResearchLean.AG.FaceRelationSubdivision.MixedSubsetHom

/-!
# 原始二補正式の同じ実target subset双対

## Implementation notes

原始支持有限和の等号を、独立生成した同じ実選択有限和の等号へ運ぶ。
全Aを同じ非零項で扱い、補正を外部入力の診断証明で代替しない。
-/
noncomputable section
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution ResolutionInvariance
universe u
variable {Source I I0 I2 : Type u} {q : Reading Source}
variable {si : I → Set q.Target} {si0 : I0 → Set q.Target} {si2 : I2 → Set q.Target}
namespace SupportedBasisMap

/-- 原始二項補正式を同じ実選択双対の二項式へ運ぶ。 -/
theorem mixedSelectedDual_correction_two
    (P : SupportedBasisMap (sourceSupport q si) (sourceSupport q si))
    (h : SupportedBasisMap (sourceSupport q si) (sourceSupport q si2))
    (d : SupportedBasisMap (sourceSupport q si2) (sourceSupport q si))
    (he : P.raw + d.raw.comp h.raw = LinearMap.id) (A : Set q.Target) :
    dualCellMap (P.mixedSelected A A rfl) +
      (dualCellMap (h.mixedSelected A A rfl)).comp (dualCellMap (d.mixedSelected A A rfl)) = LinearMap.id := by
  have hr : (P.add (h.comp d)).raw = (identity (sourceSupport q si)).raw := by
    rw [raw_add, raw_comp, raw_identity]
    exact he
  have hh := (P.add (h.comp d)).mixedSelected_eq_of_raw_eq A A rfl
    (identity (sourceSupport q si)) hr
  rw [mixedSelected_add, mixedSelected_comp, mixedSelected_identity] at hh
  have hd := congrArg dualCellMap hh
  rw [dualCellMap_add, dualCellMap_comp, dualCellMap_identity] at hd
  exact hd

/-- 原始三項補正式を同じ実選択双対の三項式へ運ぶ。 -/
theorem mixedSelectedDual_correction_three
    (P : SupportedBasisMap (sourceSupport q si) (sourceSupport q si))
    (h : SupportedBasisMap (sourceSupport q si) (sourceSupport q si2))
    (d2 : SupportedBasisMap (sourceSupport q si2) (sourceSupport q si))
    (d1 : SupportedBasisMap (sourceSupport q si) (sourceSupport q si0))
    (k : SupportedBasisMap (sourceSupport q si0) (sourceSupport q si))
    (he : P.raw + d2.raw.comp h.raw + k.raw.comp d1.raw = LinearMap.id) (A : Set q.Target) :
    dualCellMap (P.mixedSelected A A rfl) +
      (dualCellMap (h.mixedSelected A A rfl)).comp (dualCellMap (d2.mixedSelected A A rfl)) +
      (dualCellMap (d1.mixedSelected A A rfl)).comp (dualCellMap (k.mixedSelected A A rfl)) = LinearMap.id := by
  have hr : ((P.add (h.comp d2)).add (d1.comp k)).raw = (identity (sourceSupport q si)).raw := by
    rw [raw_add, raw_add, raw_comp, raw_comp, raw_identity]
    exact he
  have hh := ((P.add (h.comp d2)).add (d1.comp k)).mixedSelected_eq_of_raw_eq A A rfl
    (identity (sourceSupport q si)) hr
  rw [mixedSelected_add, mixedSelected_add, mixedSelected_comp, mixedSelected_comp, mixedSelected_identity] at hh
  have hd := congrArg dualCellMap hh
  rw [dualCellMap_add, dualCellMap_add, dualCellMap_comp, dualCellMap_comp, dualCellMap_identity] at hd
  exact hd

end SupportedBasisMap
end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
