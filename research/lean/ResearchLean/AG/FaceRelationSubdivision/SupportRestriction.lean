import ResearchLean.AG.FaceRelationSubdivision.ChainDualMap

/-!
# 同じ原始有限和と支持セル包含・双対制限

## Implementation notes

包含はセル名を変えない基底像から生成する。台を保つ有限和との可換性は、
両辺を全セルへ零延長し同じ原始射に一致させて証明する。
支持包含ごとに新しい有限和を入力する案は、同じ原始射との一致を保証しないため採らない。
-/
noncomputable section
namespace AAT.AG.FaceRelationSubdivision
universe u
variable {T I J : Type u}

/-- 支持部分集合の包含から同じセル名の包含を生成する。 -/
def selectedInclude (si : I → Set T) {A B : Set T} (h : A ⊆ B) :
    (Selected si A →₀ ℚ) →ₗ[ℚ] (Selected si B →₀ ℚ) :=
  freeMap fun i => Finsupp.single ⟨i.1, by
    obtain ⟨t, ht, ha⟩ := i.2
    exact ⟨t, ht, h ha⟩⟩ 1

/-- 同じ原始包含の基底評価。 -/
@[simp] theorem selectedInclude_single (si : I → Set T) {A B : Set T}
    (h : A ⊆ B) (i : Selected si A) (a : ℚ) :
    selectedInclude si h (Finsupp.single i a) = a • Finsupp.single
      ⟨i.1, by obtain ⟨t, ht, ha⟩ := i.2; exact ⟨t, ht, h ha⟩⟩ 1 :=
  freeMap_single _ _ _

/-- 支持包含は全セルへの同じ零延長と可換。 -/
theorem selectedInclude_embed (si : I → Set T) {A B : Set T} (h : A ⊆ B) :
    (selectedEmbed si B).comp (selectedInclude si h) = selectedEmbed si A := by
  apply Finsupp.lhom_ext
  intro i a
  simp only [LinearMap.comp_apply, selectedInclude_single,
    selectedEmbed_single, Finsupp.smul_single, smul_eq_mul, mul_one]

/-- 支持包含と零延長の点ごとの式。 -/
theorem selectedInclude_embed_apply (si : I → Set T) {A B : Set T}
    (h : A ⊆ B) (x) : selectedEmbed si B (selectedInclude si h x) =
      selectedEmbed si A x := LinearMap.congr_fun (selectedInclude_embed si h) x

/-- 空列の支持包含は同じセルchainの恒等。 -/
theorem selectedInclude_refl (si : I → Set T) (A : Set T) :
    selectedInclude si (Set.Subset.refl A) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply selectedEmbed_injective si A
  rw [selectedInclude_embed_apply, LinearMap.id_apply]

/-- 支持包含の直接生成は二つの同じセル包含の合成。 -/
theorem selectedInclude_comp (si : I → Set T) {A B C : Set T}
    (hab : A ⊆ B) (hbc : B ⊆ C) :
    selectedInclude si (hab.trans hbc) =
      (selectedInclude si hbc).comp (selectedInclude si hab) := by
  apply LinearMap.ext
  intro x
  apply selectedEmbed_injective si C
  simp only [LinearMap.comp_apply, selectedInclude_embed_apply]

namespace SupportedBasisMap
variable {si : I → Set T} {sj : J → Set T}
/-- 原始支持有限和は全A包含Bの同じセル包含と可換。r/s/hすべてに適用する。 -/
theorem selected_include_natural (M : SupportedBasisMap si sj) {A B : Set T}
    (h : A ⊆ B) :
    (selectedInclude sj h).comp (M.selected A) =
      (M.selected B).comp (selectedInclude si h) := by
  apply LinearMap.ext
  intro x
  apply selectedEmbed_injective sj B
  simp only [LinearMap.comp_apply, selectedInclude_embed_apply, M.selectedEmbed_apply]

end SupportedBasisMap

/-- 支持包含の同じ原始chain射を双対化した実cochain制限。 -/
def selectedRestrict (si : I → Set T) {A B : Set T} (h : A ⊆ B) :=
  dualCellMap (selectedInclude si h)

/-- 支持制限の同じ原始双対生成式。 -/
@[simp] theorem selectedRestrict_eq_dual (si : I → Set T) {A B : Set T} (h : A ⊆ B) :
    selectedRestrict si h = dualCellMap (selectedInclude si h) := rfl

/-- 双対制限は同じセル名の関数評価。 -/
theorem selectedRestrict_apply (si : I → Set T) {A B : Set T}
    (h : A ⊆ B) (z : Selected si B → ℚ) (i : Selected si A) :
    selectedRestrict si h z i = z ⟨i.1, by
      obtain ⟨t, ht, ha⟩ := i.2; exact ⟨t, ht, h ha⟩⟩ := by
  rw [selectedRestrict, dualCellMap_apply, selectedInclude_single, one_smul,
    freeDualEquiv_single, one_mul]

/-- 支持制限の恒等則。 -/
theorem selectedRestrict_refl (si : I → Set T) (A : Set T) :
    selectedRestrict si (Set.Subset.refl A) = LinearMap.id := by
  rw [selectedRestrict_eq_dual, selectedInclude_refl, dualCellMap_identity]

/-- 支持制限は包含の逆順で同じ実射を合成する。 -/
theorem selectedRestrict_comp (si : I → Set T) {A B C : Set T}
    (hab : A ⊆ B) (hbc : B ⊆ C) :
    selectedRestrict si (hab.trans hbc) =
      (selectedRestrict si hab).comp (selectedRestrict si hbc) := by
  rw [selectedRestrict_eq_dual, selectedInclude_comp, dualCellMap_comp,
    selectedRestrict_eq_dual, selectedRestrict_eq_dual]

namespace SupportedBasisMap
variable {si : I → Set T} {sj : J → Set T}
/-- 同じ支持有限和の実双対は全A包含Bの制限と可換。 -/
theorem dual_selected_restrict_natural (M : SupportedBasisMap si sj) {A B : Set T}
    (h : A ⊆ B) :
    (selectedRestrict si h).comp (dualCellMap (M.selected B)) =
      (dualCellMap (M.selected A)).comp (selectedRestrict sj h) := by
  have hn := congrArg dualCellMap (M.selected_include_natural h)
  simpa only [dualCellMap_comp, selectedRestrict_eq_dual] using hn.symm

end SupportedBasisMap
end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
