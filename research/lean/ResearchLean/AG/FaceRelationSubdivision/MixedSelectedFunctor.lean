import ResearchLean.AG.FaceRelationSubdivision.MixedSelectedBasis

/-!
# 同じ実支持セル有限和の合成とchain正方形

## Implementation notes

原始全セル射との零延長可換式で同じ実選択射の等号を検査する。
Source逆像の適合は方向仮定であり、有限列の各段ではreading因子式から導く。
-/
noncomputable section
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution ResolutionInvariance
universe u
variable {Source I J L : Type u} {qi qj ql : Reading Source}
variable {si : I → Set qi.Target} {sj : J → Set qj.Target} {sl : L → Set ql.Target}
namespace SupportedBasisMap
variable (M : SupportedBasisMap (sourceSupport qi si) (sourceSupport qj sj))
variable (Ai : Set qi.Target) (Aj : Set qj.Target) (hA : qi.read ⁻¹' Ai = qj.read ⁻¹' Aj)

/-- 原始全セル射が一致すれば同じ実選択射も一致。 -/
theorem mixedSelected_eq_of_raw_eq
    (N : SupportedBasisMap (sourceSupport qi si) (sourceSupport qj sj)) (h : M.raw = N.raw) :
    M.mixedSelected Ai Aj hA = N.mixedSelected Ai Aj hA := by
  apply LinearMap.ext
  intro x
  apply selectedEmbed_injective sj Aj
  rw [mixedSelectedEmbed_apply, mixedSelectedEmbed_apply, h]

/-- 原始直接合成と各段の同じ実選択射の合成は一致。 -/
theorem mixedSelected_comp
    (N : SupportedBasisMap (sourceSupport qj sj) (sourceSupport ql sl))
    (Al : Set ql.Target) (hB : qj.read ⁻¹' Aj = ql.read ⁻¹' Al) :
    (M.comp N).mixedSelected Ai Al (hA.trans hB) =
      (N.mixedSelected Aj Al hB).comp (M.mixedSelected Ai Aj hA) := by
  apply LinearMap.ext
  intro x
  apply selectedEmbed_injective sl Al
  rw [LinearMap.comp_apply, mixedSelectedEmbed_apply, mixedSelectedEmbed_apply,
    mixedSelectedEmbed_apply, raw_comp]
  rfl

/-- 原始和から生成した同じ実選択射は二射の和。 -/
theorem mixedSelected_add
    (N : SupportedBasisMap (sourceSupport qi si) (sourceSupport qj sj)) :
    (M.add N).mixedSelected Ai Aj hA = M.mixedSelected Ai Aj hA + N.mixedSelected Ai Aj hA := by
  apply LinearMap.ext
  intro x
  apply selectedEmbed_injective sj Aj
  rw [LinearMap.add_apply, map_add, mixedSelectedEmbed_apply, mixedSelectedEmbed_apply,
    mixedSelectedEmbed_apply, raw_add]
  rfl

/-- 同じreadingの原始恒等は同じ実選択恒等。 -/
theorem mixedSelected_identity :
    (identity (sourceSupport qi si)).mixedSelected Ai Ai rfl = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply selectedEmbed_injective si Ai
  rw [mixedSelectedEmbed_apply, raw_identity, LinearMap.id_apply, LinearMap.id_apply]

/-- 同じreadingのSource表示から実選択した射は既存selected射そのもの。 -/
theorem toSource_mixedSelected {sj0 : J → Set qi.Target} (M0 : SupportedBasisMap si sj0) :
    M0.toSource.mixedSelected Ai Ai rfl = M0.selected Ai := by
  apply LinearMap.ext
  intro x
  apply selectedEmbed_injective sj0 Ai
  rw [mixedSelectedEmbed_apply, selectedEmbed_apply, toSource_raw]

/-- 原始chain正方形は同じ実支持セルのchain正方形へ降りる。 -/
theorem mixedSelected_square {I0 J0 : Type u}
    {si0 : I0 → Set qi.Target} {sj0 : J0 → Set qj.Target}
    (M0 : SupportedBasisMap (sourceSupport qi si0) (sourceSupport qj sj0))
    (di : SupportedBasisMap si si0) (dj : SupportedBasisMap sj sj0)
    (h : dj.raw.comp M.raw = M0.raw.comp di.raw) :
    (dj.selected Aj).comp (M.mixedSelected Ai Aj hA) =
      (M0.mixedSelected Ai Aj hA).comp (di.selected Ai) := by
  apply LinearMap.ext
  intro x
  apply selectedEmbed_injective sj0 Aj
  rw [LinearMap.comp_apply, LinearMap.comp_apply, dj.selectedEmbed_apply,
    mixedSelectedEmbed_apply, mixedSelectedEmbed_apply, di.selectedEmbed_apply]
  exact LinearMap.congr_fun h (selectedEmbed si Ai x)

end SupportedBasisMap
end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
