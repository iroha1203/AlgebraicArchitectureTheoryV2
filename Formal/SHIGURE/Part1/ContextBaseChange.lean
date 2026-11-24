import Formal.SHIGURE.Part1.Contexts

/-! # Compatibility of assembly with restriction

Over a smaller context each original piece is replaced by its intersection.
The pulled back map at that piece is computed from the original local map
and the two strictly equal composites of restrictions.
-/

universe u

namespace SHIGURE
namespace DeclarationCover

open CategoryTheory DeclarationContext

variable {P : PrimitivePresentation.{u}} {U V : DeclarationContext P} (cover : DeclarationCover U)

/-- Assembling local identity arrows gives the global identity. -/
theorem assemble_id (A : Models U) : cover.assemble (𝟙 (cover.read A)) = 𝟙 A := by
  apply cover.maps_eq_of_restrict_eq
  intro i
  rw [cover.assemble_restrict, Functor.map_id, Match.id_pieceMap]
  rfl

/-- Assembly preserves the composition of compatible local families between fixed global endpoints. -/
theorem assemble_comp {A B C : Models U}
    (f : Match.Hom (cover.read A) (cover.read B)) (g : Match.Hom (cover.read B) (cover.read C)) :
    cover.assemble (Match.Hom.comp f g) = cover.assemble f ≫ cover.assemble g := by
  apply cover.maps_eq_of_restrict_eq
  intro i
  rw [cover.assemble_restrict, Functor.map_comp, cover.assemble_restrict, cover.assemble_restrict]
  rfl

/-- The two routes to a pulled-back piece give the same model. -/
theorem pullback_restrict_eq (A : Models U) (inside : V ≤ U) (i : cover.Index) :
    (A.restrict inside).restrict ((cover.pullback inside).subset i) =
      (A.restrict (cover.subset i)).restrict (inter_le_left (cover.piece i) V) :=
  (A.restrict_comp inside ((cover.pullback inside).subset i)).trans
    (A.restrict_comp (cover.subset i) (inter_le_left (cover.piece i) V)).symm

/-- Restrict a local arrow to an intersection, using the strict equalities of the endpoint restrictions. -/
noncomputable def pullbackComponent {A B : Models U} (f : Match.Hom (cover.read A) (cover.read B))
    (inside : V ≤ U) (i : cover.Index) :
    ((cover.pullback inside).read (A.restrict inside)).pieceModel i ⟶
      ((cover.pullback inside).read (B.restrict inside)).pieceModel i :=
  eqToHom (cover.pullback_restrict_eq A inside i) ≫
    (res (inter_le_left (cover.piece i) V)).map (f.pieceMap i) ≫
    eqToHom (cover.pullback_restrict_eq B inside i).symm

/-- Restricting the assembled arrow and reading any intersection agrees with the local restriction. -/
theorem restrict_assemble_piece {A B : Models U} (f : Match.Hom (cover.read A) (cover.read B))
    (inside : V ≤ U) (i : cover.Index) :
    (res ((cover.pullback inside).subset i)).map ((res inside).map (cover.assemble f)) =
      cover.pullbackComponent f inside i := by
  unfold pullbackComponent
  rw [← cover.assemble_restrict f i]
  apply Models.hom_ext
  intro s kept x
  simp only [Models.comp_onSort, Models.eqToHom_onSort, res_onSort, selectedMap, cast_cast]

/-- The restricted local arrows form a matching family on the pulled-back cover. -/
noncomputable def pullbackMatchingMap {A B : Models U} (f : Match.Hom (cover.read A) (cover.read B))
    (inside : V ≤ U) :
    Match.Hom ((cover.pullback inside).read (A.restrict inside)) ((cover.pullback inside).read (B.restrict inside)) where
  pieceMap := cover.pullbackComponent f inside
  overlap_comm i j := by
    rw [← cover.restrict_assemble_piece f inside i, ← cover.restrict_assemble_piece f inside j]
    exact (show Match.Hom _ _ from
      (cover.pullback inside).readFunctor.map ((res inside).map (cover.assemble f))).overlap_comm i j

/-- Restriction of an assembly is precisely assembly over the pulled-back declaration cover. -/
theorem assemble_pullback {A B : Models U} (f : Match.Hom (cover.read A) (cover.read B)) (inside : V ≤ U) :
    (res inside).map (cover.assemble f) = (cover.pullback inside).assemble (cover.pullbackMatchingMap f inside) := by
  apply (cover.pullback inside).maps_eq_of_restrict_eq
  intro i
  rw [(cover.pullback inside).assemble_restrict, cover.restrict_assemble_piece]
  rfl

end DeclarationCover
end SHIGURE
