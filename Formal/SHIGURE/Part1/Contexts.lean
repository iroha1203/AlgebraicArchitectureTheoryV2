import Formal.SHIGURE.Part1.ContextGluingMaps

/-! # Model descent for declaration covers

Theorems 3.4–3.5 assemble both objects and arrows. The two functors are
strict inverses in Cat, with no additional choice of overlap isomorphisms.
-/

universe u

namespace SHIGURE
namespace DeclarationCover

open CategoryTheory DeclarationContext

variable {P : PrimitivePresentation.{u}} {U : DeclarationContext P} (cover : DeclarationCover U)

/-- The restrictions to all pieces define the functor from global models to strict matching families. -/
noncomputable def readFunctor : Models U ⥤ Match cover.piece where
  obj := cover.read
  map f := show Match.Hom _ _ from {
    pieceMap i := (res (cover.subset i)).map f
    overlap_comm i j := by
      apply Models.hom_ext
      intro s keep x
      simp only [Models.comp_onSort, Models.eqToHom_onSort, res_onSort, selectedMap_apply, cast_cast] }
  map_id A := Match.Hom.ext fun i => (res (cover.subset i)).map_id A
  map_comp f g := Match.Hom.ext fun i => (res (cover.subset i)).map_comp f g

/-- At a piece the reading functor's arrow is the restriction to that piece. -/
theorem readFunctor_pieceMap {A B : Models U} (f : A ⟶ B) (i : cover.Index) :
    (show Match.Hom (cover.read A) (cover.read B) from cover.readFunctor.map f).pieceMap i =
      (res (cover.subset i)).map f :=
  rfl

/-- Assembling arrows commutes with identity and composition on the matching side. -/
noncomputable def glueFunctor : Match cover.piece ⥤ Models U where
  obj A := A.glue cover
  map f := Match.glueMap cover f
  map_id A := by
    apply Models.hom_ext
    intro s keep x
    let i := cover.index keep
    have localKept := cover.mem_index keep
    simp only [Match.glueMap_onSort, Match.glueOnSort_eq_piece cover _ i s localKept, Match.arrowView_apply,
      Match.id_pieceMap, Models.id_onSort, Match.toPieceCarrier_apply, cast_cast]
    rfl
  map_comp f g := by
    apply Models.hom_ext
    intro s keep x
    let i := cover.index keep
    have localKept := cover.mem_index keep
    simp only [Models.comp_onSort, Match.glueMap_onSort, Match.glueOnSort_eq_piece cover _ i s localKept,
      Match.arrowView_apply, Match.comp_pieceMap, Match.toPieceCarrier_apply, cast_cast]
    rfl

/-- The assembly functor maps a matching arrow by gluing its components. -/
theorem glueFunctor_map {A B : Match cover.piece} (f : A ⟶ B) :
    cover.glueFunctor.map f = Match.glueMap cover f :=
  rfl

/-- Reading before assembly is strictly the identity on the entire model category. -/
theorem read_comp_glue : cover.readFunctor ⋙ cover.glueFunctor = 𝟭 (Models U) := by
  refine Functor.ext (fun A => cover.glue_read A) ?_
  intro A B f
  apply Models.hom_ext
  intro s keep x
  let i := cover.index keep
  have localKept := cover.mem_index keep
  simp only [Functor.comp_map, glueFunctor_map, Match.glueMap_onSort,
    Match.glueOnSort_eq_piece cover _ i s localKept, Match.arrowView_apply, readFunctor_pieceMap, res_onSort,
    Match.toPieceCarrier_apply, Models.comp_onSort, Models.eqToHom_onSort, Functor.id_map, selectedMap_apply, cast_cast]

/-- Assembly before reading is strictly the identity on all objects and arrows of the matching category. -/
theorem glue_comp_read : cover.glueFunctor ⋙ cover.readFunctor = 𝟭 (Match cover.piece) := by
  refine Functor.ext (fun A => cover.read_glue A) ?_
  intro A B f
  apply Match.Hom.ext
  intro i
  apply Models.hom_ext
  intro s keep x
  simp only [Functor.comp_map, glueFunctor_map, readFunctor_pieceMap, Match.comp_pieceMap,
    Match.eqToHom_pieceMap, res_onSort, Match.glueMap_onSort, Match.glueOnSort_eq_piece cover f i s keep,
    Match.arrowView_apply, Match.toPieceCarrier_apply, Models.comp_onSort, Models.eqToHom_onSort, Functor.id_map,
    selectedMap_apply, cast_cast]

/-- Equation (3.3): restriction and assembly give an isomorphism in the category of categories. -/
noncomputable def modelIso : Cat.of (Models U) ≅ Cat.of (Match cover.piece) where
  hom := cover.readFunctor.toCatHom
  inv := cover.glueFunctor.toCatHom
  hom_inv_id := congrArg Functor.toCatHom cover.read_comp_glue
  inv_hom_id := congrArg Functor.toCatHom cover.glue_comp_read

/-- A global map is determined by its restrictions to all pieces. -/
theorem maps_eq_of_restrict_eq {A B : Models U} {f g : A ⟶ B}
    (same : ∀ i, (res (cover.subset i)).map f = (res (cover.subset i)).map g) : f = g := by
  apply Models.hom_ext
  intro s keep x
  let i := cover.index keep
  have localKept := cover.mem_index keep
  let localX := cast (A.obj.restrict_carrier (cover.subset i) (s := s) localKept).symm x
  have component := congrArg (fun h => Models.onSort h s localKept localX) (same i)
  apply (Equiv.cast (B.obj.restrict_carrier (cover.subset i) (s := s) localKept).symm).injective
  simpa only [res_onSort, selectedMap_apply, localX, cast_cast, Equiv.cast_apply] using component

/-- A matching family of maps between restrictions of two fixed models determines a global map. -/
noncomputable def assemble {A B : Models U} (f : Match.Hom (cover.read A) (cover.read B)) : A ⟶ B :=
  eqToHom (cover.glue_read A).symm ≫ Match.glueMap cover f ≫ eqToHom (cover.glue_read B)

/-- Restricting the assembled map between two global models gives the specified local map. -/
@[simp] theorem assemble_restrict {A B : Models U} (f : Match.Hom (cover.read A) (cover.read B))
    (i : cover.Index) : (res (cover.subset i)).map (cover.assemble f) = f.pieceMap i := by
  apply Models.hom_ext
  intro s keep x
  simp only [assemble, res_onSort, Models.comp_onSort, Models.eqToHom_onSort, Match.glueMap_onSort,
    Match.glueOnSort_eq_piece cover f i s keep, Match.arrowView_apply, Match.toPieceCarrier_apply, selectedMap_apply, cast_cast]
  rfl

/-- Theorem 3.5: strictly compatible local arrows extend to exactly one global arrow. -/
theorem existsUnique_assemble {A B : Models U} (f : Match.Hom (cover.read A) (cover.read B)) :
    ∃! h : A ⟶ B, ∀ i, (res (cover.subset i)).map h = f.pieceMap i :=
  ⟨cover.assemble f, cover.assemble_restrict f, fun _ same => cover.maps_eq_of_restrict_eq fun i =>
    (same i).trans (cover.assemble_restrict f i).symm⟩

/-- Assembly of the restrictions of a global morphism recovers it exactly. -/
@[simp] theorem assemble_read {A B : Models U} (f : A ⟶ B) :
    cover.assemble (show Match.Hom (cover.read A) (cover.read B) from cover.readFunctor.map f) = f :=
  cover.maps_eq_of_restrict_eq fun i => cover.assemble_restrict _ i

end DeclarationCover
end SHIGURE
