import ResearchLean.AG.AtlasDefectComposition.SelectedFamilyOperations
import Formal.Util.AssertStandardAxioms
/-! # selected block 族の対称モノイド圏

Implementation notes: 元の添字の非交和・空添字・標準入れ替えを指定する。
可換図式は非零添字での元評価を全場合で照合して証明する。
-/
noncomputable section
open CategoryTheory
namespace AAT.AG.AtlasDefectComposition.SelectedFamilies
universe u v
variable {T : Type u} {Ω : Type v} (S : T → Set Ω)
/-- 指定射の対称モノイド構造。積は元の有限添字の非交和である。 -/
instance familyMonoidal : MonoidalCategory (Family S) where
  tensorObj := sum S
  whiskerLeft F _ _ g := tensorHom S (homId S F) g
  whiskerRight f G := tensorHom S f (homId S G)
  tensorHom := tensorHom S
  tensorUnit := empty S
  associator F G H := isoOfHom S (associatorHom S F G H)
  leftUnitor F := isoOfHom S (leftUnitorHom S F)
  rightUnitor F := isoOfHom S (rightUnitorHom S F)
  tensorHom_def := by
    intro F G F' G' f g
    apply hom_ext S
    rintro ⟨a | b,h⟩ <;> apply Subtype.ext <;> rfl
  id_tensorHom_id := by
    intro F G
    apply hom_ext S
    rintro ⟨a | b,h⟩ <;> apply Subtype.ext <;> rfl
  tensorHom_comp_tensorHom := by
    intro F F' F'' G G' G'' f g f' g'
    apply hom_ext S
    rintro ⟨a | b,h⟩ <;> apply Subtype.ext <;> rfl
  whiskerLeft_id := by
    intro F G
    apply hom_ext S
    rintro ⟨a | b,h⟩ <;> apply Subtype.ext <;> rfl
  id_whiskerRight := by
    intro F G
    apply hom_ext S
    rintro ⟨a | b,h⟩ <;> apply Subtype.ext <;> rfl
  associator_naturality := by
    intro F G H F' G' H' f g k
    apply hom_ext S
    rintro ⟨(a | b) | c,h⟩ <;> apply Subtype.ext <;> rfl
  leftUnitor_naturality := by
    intro F G f
    apply hom_ext S
    rintro ⟨a | b,h⟩
    · exact a.elim
    · apply Subtype.ext
      rfl
  rightUnitor_naturality := by
    intro F G f
    apply hom_ext S
    rintro ⟨a | b,h⟩
    · apply Subtype.ext
      rfl
    · exact b.elim
  pentagon := by
    intro F G H K
    apply hom_ext S
    rintro ⟨((a | b) | c) | d,h⟩ <;> apply Subtype.ext <;> rfl
  triangle := by
    intro F G
    apply hom_ext S
    rintro ⟨(a | b) | c,h⟩
    · apply Subtype.ext
      rfl
    · exact b.elim
    · apply Subtype.ext
      rfl
/-- 非交和の標準入れ替えを braiding にする。両 hexagon を元の添字で証明する。 -/
instance familyBraided : BraidedCategory (Family S) where
  braiding F G := isoOfHom S (braidingHom S F G)
  braiding_naturality_right := by
    intro F G H f
    apply hom_ext S
    rintro ⟨a | b,h⟩ <;> apply Subtype.ext <;> rfl
  braiding_naturality_left := by
    intro F G f H
    apply hom_ext S
    rintro ⟨a | b,h⟩ <;> apply Subtype.ext <;> rfl
  hexagon_forward := by
    intro F G H
    apply hom_ext S
    rintro ⟨(a | b) | c,h⟩ <;> apply Subtype.ext <;> rfl
  hexagon_reverse := by
    intro F G H
    apply hom_ext S
    rintro ⟨a | (b | c),h⟩ <;> apply Subtype.ext <;> rfl
/-- 標準入れ替えを二回施すと元の全非零添字へ戻る。 -/
instance familySymmetric : SymmetricCategory (Family S) where
  symmetry := by
    intro F G
    apply hom_ext S
    rintro ⟨a | b,h⟩ <;> apply Subtype.ext <;> rfl
end AAT.AG.AtlasDefectComposition.SelectedFamilies
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition.SelectedFamilies
