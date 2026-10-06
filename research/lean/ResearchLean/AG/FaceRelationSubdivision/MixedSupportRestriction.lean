import ResearchLean.AG.FaceRelationSubdivision.MixedSelectedFunctor
import ResearchLean.AG.FaceRelationSubdivision.SupportRestriction

/-!
# 混在reading原始有限和の全支持包含自然性

## Implementation notes

全セルの同じ原始像と零延長から支持包含のchain正方形を証明する。
双対化は同じ基底包含の双対を使い、r/s/h/kの任意有限和を一つの式で扱う。
-/
noncomputable section
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution ResolutionInvariance
universe u
variable {Source I J : Type u} {qi qj : Reading Source}
variable {si : I → Set qi.Target} {sj : J → Set qj.Target}
namespace SupportedBasisMap
variable (M : SupportedBasisMap (sourceSupport qi si) (sourceSupport qj sj))
variable (Ai Bi : Set qi.Target) (Aj Bj : Set qj.Target)
variable (hAi : Ai ⊆ Bi) (hAj : Aj ⊆ Bj)
variable (hA : qi.read ⁻¹' Ai = qj.read ⁻¹' Aj) (hB : qi.read ⁻¹' Bi = qj.read ⁻¹' Bj)

/-- 原始有限和の同じ実選択chain射は支持セル包含と可換。 -/
theorem mixedSelected_include_natural :
    (selectedInclude sj hAj).comp (M.mixedSelected Ai Aj hA) =
      (M.mixedSelected Bi Bj hB).comp (selectedInclude si hAi) := by
  apply LinearMap.ext
  intro x
  apply selectedEmbed_injective sj Bj
  rw [LinearMap.comp_apply, LinearMap.comp_apply, selectedInclude_embed_apply,
    mixedSelectedEmbed_apply, mixedSelectedEmbed_apply, selectedInclude_embed_apply]

/-- 独立実双対有限和も同じ支持制限と可換。 -/
theorem mixedSelected_dual_restrict_natural :
    (selectedRestrict si hAi).comp (dualCellMap (M.mixedSelected Bi Bj hB)) =
      (dualCellMap (M.mixedSelected Ai Aj hA)).comp (selectedRestrict sj hAj) := by
  have h := congrArg dualCellMap (M.mixedSelected_include_natural Ai Bi Aj Bj hAi hAj hA hB)
  rw [dualCellMap_comp, dualCellMap_comp, ← selectedRestrict_eq_dual,
    ← selectedRestrict_eq_dual] at h
  exact h.symm

end SupportedBasisMap
end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
