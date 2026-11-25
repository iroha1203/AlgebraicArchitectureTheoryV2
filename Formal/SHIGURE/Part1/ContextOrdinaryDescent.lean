import Formal.SHIGURE.Part1.ContextOrdinaryMatching

/-! # Declaration descent in the ordinary model categories

Cover restriction projects to the ordinary reduct functor in each piece.
Assembly is its strict inverse on both the closed models and their maps.
-/

universe u

namespace SHIGURE.DeclarationCover

open CategoryTheory DeclarationContext

variable {P : PrimitivePresentation.{u}} {U : DeclarationContext P} (cover : DeclarationCover U)

/-- Read an ordinary global model as the strictly matching family of ordinary local models. -/
noncomputable def ordinaryRead : Model (Selected.theory U) ⥤ OrdinaryMatch cover.piece :=
  Selected.writeFunctor U ⋙ cover.readFunctor ⋙ OrdinaryMatch.readFunctor

/-- Assemble an ordinary family by gluing its primitive evaluations and converting back to a model. -/
noncomputable def ordinaryGlue : OrdinaryMatch cover.piece ⥤ Model (Selected.theory U) :=
  OrdinaryMatch.writeFunctor ⋙ cover.glueFunctor ⋙ Selected.readFunctor U

/-- Projection to each piece is exactly the ordinary model restriction functor. -/
theorem ordinaryRead_project (i : cover.Index) :
    cover.ordinaryRead ⋙ OrdinaryMatch.project i = Selected.modelRestriction (cover.subset i) := by
  rw [ordinaryRead, Selected.modelRestriction_eq, Functor.assoc, Functor.assoc,
    OrdinaryMatch.readFunctor_project, ← Functor.assoc cover.readFunctor (Match.project i),
    cover.readFunctor_project]

/-- The components of the restriction to a cover are the ordinary reducts. -/
theorem ordinaryRead_obj (X : Model (Selected.theory U)) (i : cover.Index) :
    (cover.ordinaryRead.obj X).pieceModel i = (Selected.modelRestriction (cover.subset i)).obj X :=
  (OrdinaryMatch.project_obj i (cover.ordinaryRead.obj X)).symm.trans
    (Functor.congr_obj (cover.ordinaryRead_project i) X)

/-- The arrow read at each piece is its usual ordinary reduct. -/
theorem ordinaryRead_map_heq {A B : Model (Selected.theory U)} (f : A ⟶ B) (i : cover.Index) :
    (show OrdinaryMatch.Hom _ _ from cover.ordinaryRead.map f).pieceMap i ≍
      (Selected.modelRestriction (cover.subset i)).map f := by
  have projected := Functor.hcongr_hom (cover.ordinaryRead_project i) f
  simp only [Functor.comp_map] at projected
  exact (OrdinaryMatch.project_map i (cover.ordinaryRead.map f)).symm.trans projected

/-- The component of an ordinary restriction agrees at its definitionally matching endpoints. -/
theorem ordinaryRead_map {A B : Model (Selected.theory U)} (f : A ⟶ B) (i : cover.Index) :
    (show OrdinaryMatch.Hom _ _ from cover.ordinaryRead.map f).pieceMap i =
      (Selected.modelRestriction (cover.subset i)).map f :=
  eq_of_heq (cover.ordinaryRead_map_heq f i)

/-- Restricting then gluing is the identity on the ordinary global model category. -/
theorem ordinaryRead_comp_glue :
    cover.ordinaryRead ⋙ cover.ordinaryGlue = 𝟭 (Model (Selected.theory U)) := by
  simp only [ordinaryRead, ordinaryGlue, Functor.assoc]
  rw [← Functor.assoc OrdinaryMatch.readFunctor OrdinaryMatch.writeFunctor,
    OrdinaryMatch.read_comp_write, Functor.id_comp,
    ← Functor.assoc cover.readFunctor cover.glueFunctor, cover.read_comp_glue,
    Functor.id_comp, Selected.write_comp_read]

/-- Gluing then restricting is the identity on the ordinary matching category. -/
theorem ordinaryGlue_comp_read :
    cover.ordinaryGlue ⋙ cover.ordinaryRead = 𝟭 (OrdinaryMatch cover.piece) := by
  simp only [ordinaryRead, ordinaryGlue, Functor.assoc]
  rw [← Functor.assoc (Selected.readFunctor U) (Selected.writeFunctor U),
    Selected.read_comp_write, Functor.id_comp,
    ← Functor.assoc cover.glueFunctor cover.readFunctor, cover.glue_comp_read,
    Functor.id_comp, OrdinaryMatch.write_comp_read]

/-- Equation (3.3) between the ordinary global model category and the ordinary matching category. -/
noncomputable def ordinaryModelIso : Cat.of (Model (Selected.presentation U).theory) ≅
    Cat.of (OrdinaryMatch cover.piece) where
  hom := cover.ordinaryRead.toCatHom
  inv := cover.ordinaryGlue.toCatHom
  hom_inv_id := congrArg Functor.toCatHom cover.ordinaryRead_comp_glue
  inv_hom_id := congrArg Functor.toCatHom cover.ordinaryGlue_comp_read

/-- The equality that identifies an assembled ordinary model's read with its input. -/
theorem ordinaryGlue_read (A : OrdinaryMatch cover.piece) :
    cover.ordinaryRead.obj (cover.ordinaryGlue.obj A) = A :=
  Functor.congr_obj cover.ordinaryGlue_comp_read A

/-- Theorem 3.4 for an arbitrary family of ordinary local models. -/
theorem existsUnique_ordinary_glue (A : OrdinaryMatch cover.piece) :
    ∃! X : Model (Selected.presentation U).theory, ∀ i,
      (Selected.modelRestriction (cover.subset i)).obj X = A.pieceModel i := by
  refine ⟨cover.ordinaryGlue.obj A, ?_, ?_⟩
  · intro i
    exact (cover.ordinaryRead_obj (cover.ordinaryGlue.obj A) i).symm.trans
      (congrArg (fun B : OrdinaryMatch cover.piece => B.pieceModel i) (cover.ordinaryGlue_read A))
  · intro X h
    have matching : cover.ordinaryRead.obj X = A :=
      OrdinaryMatch.ext fun i => (cover.ordinaryRead_obj X i).trans (h i)
    exact (Functor.congr_obj cover.ordinaryRead_comp_glue X).symm.trans
      (congrArg cover.ordinaryGlue.obj matching)

/-- An assembled map has the originally specified ordinary endpoints. -/
noncomputable def ordinaryAssemble {A B : Model (Selected.theory U)}
    (f : OrdinaryMatch.Hom (cover.ordinaryRead.obj A) (cover.ordinaryRead.obj B)) : A ⟶ B :=
  eqToHom (Functor.congr_obj cover.ordinaryRead_comp_glue A).symm ≫
    cover.ordinaryGlue.map f ≫ eqToHom (Functor.congr_obj cover.ordinaryRead_comp_glue B)

/-- An assembled map is the glued arrow transported along its two endpoint identifications. -/
theorem ordinaryAssemble_eq {A B : Model (Selected.theory U)}
    (f : OrdinaryMatch.Hom (cover.ordinaryRead.obj A) (cover.ordinaryRead.obj B)) :
    cover.ordinaryAssemble f = eqToHom (Functor.congr_obj cover.ordinaryRead_comp_glue A).symm ≫
      cover.ordinaryGlue.map f ≫ eqToHom (Functor.congr_obj cover.ordinaryRead_comp_glue B) :=
  rfl

/-- Reading the assembled ordinary arrow gives exactly the supplied matching arrow. -/
theorem ordinaryAssemble_read {A B : Model (Selected.theory U)}
    (f : OrdinaryMatch.Hom (cover.ordinaryRead.obj A) (cover.ordinaryRead.obj B)) :
    cover.ordinaryRead.map (cover.ordinaryAssemble f) = f := by
  let R := cover.ordinaryRead
  let G := cover.ordinaryGlue
  have h := Functor.congr_hom cover.ordinaryGlue_comp_read (show R.obj A ⟶ R.obj B from f)
  simp only [ordinaryAssemble_eq, Functor.map_comp, eqToHom_map]
  change _ ≫ (G ⋙ R).map f ≫ _ = _
  rw [h]
  simp only [Functor.id_map, Category.assoc, eqToHom_trans_assoc, eqToHom_trans, eqToHom_refl, Category.id_comp, Category.comp_id]

/-- The restriction of the assembled arrow recovers each local component across the identified endpoints. -/
theorem ordinaryAssemble_piece_heq {A B : Model (Selected.theory U)}
    (f : OrdinaryMatch.Hom (cover.ordinaryRead.obj A) (cover.ordinaryRead.obj B)) (i : cover.Index) :
    (Selected.modelRestriction (cover.subset i)).map (cover.ordinaryAssemble f) ≍ f.pieceMap i :=
  (cover.ordinaryRead_map_heq (cover.ordinaryAssemble f) i).symm.trans
    (heq_of_eq (congrArg (fun g : OrdinaryMatch.Hom _ _ => g.pieceMap i) (cover.ordinaryAssemble_read f)))

/-- A piece of the assembled ordinary arrow is exactly its original local component. -/
theorem ordinaryAssemble_piece {A B : Model (Selected.theory U)}
    (f : OrdinaryMatch.Hom (cover.ordinaryRead.obj A) (cover.ordinaryRead.obj B)) (i : cover.Index) :
    (Selected.modelRestriction (cover.subset i)).map (cover.ordinaryAssemble f) = f.pieceMap i :=
  eq_of_heq (cover.ordinaryAssemble_piece_heq f i)

/-- Theorem 3.5 with the equalities of the local endpoint types left explicit. -/
theorem existsUnique_ordinary_assemble_heq {A B : Model (Selected.theory U)}
    (f : OrdinaryMatch.Hom (cover.ordinaryRead.obj A) (cover.ordinaryRead.obj B)) :
    ∃! h : A ⟶ B, ∀ i, (Selected.modelRestriction (cover.subset i)).map h ≍ f.pieceMap i := by
  refine ⟨cover.ordinaryAssemble f, cover.ordinaryAssemble_piece_heq f, fun h components => ?_⟩
  have matching : cover.ordinaryRead.map h = f :=
    OrdinaryMatch.Hom.ext fun i => eq_of_heq ((cover.ordinaryRead_map_heq h i).trans (components i))
  rw [cover.ordinaryAssemble_eq]
  rw [← matching]
  change h = _ ≫ (cover.ordinaryRead ⋙ cover.ordinaryGlue).map h ≫ _
  rw [Functor.congr_hom cover.ordinaryRead_comp_glue h]
  simp only [Functor.id_map, Category.assoc, eqToHom_trans_assoc, eqToHom_trans, eqToHom_refl, Category.id_comp, Category.comp_id]

/-- Theorem 3.5 for arbitrary compatible arrows of the ordinary local models. -/
theorem existsUnique_ordinary_assemble {A B : Model (Selected.theory U)}
    (f : OrdinaryMatch.Hom (cover.ordinaryRead.obj A) (cover.ordinaryRead.obj B)) :
    ∃! h : A ⟶ B, ∀ i, (Selected.modelRestriction (cover.subset i)).map h = f.pieceMap i := by
  obtain ⟨h, components, unique⟩ := cover.existsUnique_ordinary_assemble_heq f
  exact ⟨h, fun i => eq_of_heq (components i), fun g same => unique g (fun i => heq_of_eq (same i))⟩

section

attribute [local irreducible] ordinaryRead

/-- Ordinary assembly takes the tuple of local identities to the global identity. -/
theorem ordinaryAssemble_id (A : Model (Selected.theory U)) :
    cover.ordinaryAssemble (show OrdinaryMatch.Hom _ _ from 𝟙 (cover.ordinaryRead.obj A)) = 𝟙 A := by
  let f := (show OrdinaryMatch.Hom _ _ from 𝟙 (cover.ordinaryRead.obj A))
  obtain ⟨g, _, unique⟩ := cover.existsUnique_ordinary_assemble_heq f
  refine (unique _ (cover.ordinaryAssemble_piece_heq f)).trans (unique _ ?_).symm
  intro i
  have readIdentity := congrArg (fun g : OrdinaryMatch.Hom _ _ => g.pieceMap i) (cover.ordinaryRead.map_id A)
  exact (cover.ordinaryRead_map_heq (𝟙 A) i).symm.trans (heq_of_eq readIdentity)

/-- Ordinary assembly commutes with composition of ordinary matching arrows. -/
theorem ordinaryAssemble_comp {A B C : Model (Selected.theory U)}
    (f : OrdinaryMatch.Hom (cover.ordinaryRead.obj A) (cover.ordinaryRead.obj B))
    (g : OrdinaryMatch.Hom (cover.ordinaryRead.obj B) (cover.ordinaryRead.obj C)) :
    cover.ordinaryAssemble (f.comp g) = cover.ordinaryAssemble f ≫ cover.ordinaryAssemble g := by
  obtain ⟨h, _, unique⟩ := cover.existsUnique_ordinary_assemble_heq (f.comp g)
  refine (unique _ (cover.ordinaryAssemble_piece_heq (f.comp g))).trans (unique _ ?_).symm
  have readComposite : cover.ordinaryRead.map (cover.ordinaryAssemble f ≫ cover.ordinaryAssemble g) = f.comp g := by
    rw [Functor.map_comp, ordinaryAssemble_read, ordinaryAssemble_read]
    rfl
  intro i
  exact (cover.ordinaryRead_map_heq (cover.ordinaryAssemble f ≫ cover.ordinaryAssemble g) i).symm.trans
    (heq_of_eq (congrArg (fun g : OrdinaryMatch.Hom _ _ => g.pieceMap i) readComposite))

/-- The ordinary restriction to an intersection is independent of the route to it. -/
theorem ordinaryPullback_restrictions {V : DeclarationContext P} (inside : V ≤ U) (i : cover.Index) :
    Selected.modelRestriction inside ⋙ Selected.modelRestriction ((cover.pullback inside).subset i) =
      Selected.modelRestriction (cover.subset i) ⋙ Selected.modelRestriction (inter_le_left (cover.piece i) V) :=
  (Selected.modelRestriction_comp inside ((cover.pullback inside).subset i)).trans
    (Selected.modelRestriction_comp (cover.subset i) (inter_le_left (cover.piece i) V)).symm

/-- Comparing the two restriction routes also identifies their actual matching endpoints. -/
private theorem ordinaryPullback_endpoint {V : DeclarationContext P} (inside : V ≤ U) (i : cover.Index)
    (A : Model (Selected.theory U)) :
    ((cover.pullback inside).ordinaryRead.obj ((Selected.modelRestriction inside).obj A)).pieceModel i =
      (Selected.modelRestriction (inter_le_left (cover.piece i) V)).obj ((cover.ordinaryRead.obj A).pieceModel i) :=
  ((cover.pullback inside).ordinaryRead_obj ((Selected.modelRestriction inside).obj A) i).trans
    ((Functor.congr_obj (cover.ordinaryPullback_restrictions inside i) A).trans
      (congrArg (Selected.modelRestriction (inter_le_left (cover.piece i) V)).obj (cover.ordinaryRead_obj A i).symm))

/-- At a pullback piece, the assembled arrow and the restricted local map agree after transporting their endpoints. -/
theorem ordinaryPullback_component_heq {V : DeclarationContext P} {A B : Model (Selected.theory U)}
    (f : OrdinaryMatch.Hom (cover.ordinaryRead.obj A) (cover.ordinaryRead.obj B))
    (inside : V ≤ U) (i : cover.Index) :
    HEq ((Selected.modelRestriction ((cover.pullback inside).subset i)).map
      ((Selected.modelRestriction inside).map (cover.ordinaryAssemble f)))
      ((Selected.modelRestriction (inter_le_left (cover.piece i) V)).map (f.pieceMap i)) := by
  have paths := Functor.hcongr_hom (cover.ordinaryPullback_restrictions inside i) (cover.ordinaryAssemble f)
  simp only [Functor.comp_map] at paths
  exact paths.trans (OrdinaryMatch.map_heq_of_endpoints _ (cover.ordinaryRead_obj A i).symm
    (cover.ordinaryRead_obj B i).symm (cover.ordinaryAssemble_piece_heq f i))

end

/-- At a pullback piece the assembled ordinary arrow restricts to the given local map's restriction. -/
theorem ordinaryPullback_component {V : DeclarationContext P} {A B : Model (Selected.theory U)}
    (f : OrdinaryMatch.Hom (cover.ordinaryRead.obj A) (cover.ordinaryRead.obj B))
    (inside : V ≤ U) (i : cover.Index) :
    (Selected.modelRestriction ((cover.pullback inside).subset i)).map
      ((Selected.modelRestriction inside).map (cover.ordinaryAssemble f)) =
    eqToHom (Functor.congr_obj (cover.ordinaryPullback_restrictions inside i) A) ≫
      (Selected.modelRestriction (inter_le_left (cover.piece i) V)).map (f.pieceMap i) ≫
      eqToHom (Functor.congr_obj (cover.ordinaryPullback_restrictions inside i) B).symm := by
  apply eq_of_heq
  simpa only [heq_eqToHom_comp_iff, heq_comp_eqToHom_iff] using cover.ordinaryPullback_component_heq f inside i

section

attribute [local irreducible] ordinaryRead

/-- Ordinary matching arrows restrict along the pullback cover of a smaller context. -/
noncomputable def ordinaryPullback_matchingMap {V : DeclarationContext P} {A B : Model (Selected.theory U)}
    (f : OrdinaryMatch.Hom (cover.ordinaryRead.obj A) (cover.ordinaryRead.obj B))
    (inside : V ≤ U) : OrdinaryMatch.Hom
      ((cover.pullback inside).ordinaryRead.obj ((Selected.modelRestriction inside).obj A))
      ((cover.pullback inside).ordinaryRead.obj ((Selected.modelRestriction inside).obj B)) := by
  let restrict := Selected.modelRestriction inside
  let pulled := cover.pullback inside
  let part i := eqToHom (cover.ordinaryPullback_endpoint inside i A) ≫
    (Selected.modelRestriction (inter_le_left (cover.piece i) V)).map (f.pieceMap i) ≫
    eqToHom (cover.ordinaryPullback_endpoint inside i B).symm
  let readArrow := (show OrdinaryMatch.Hom (pulled.ordinaryRead.obj (restrict.obj A))
    (pulled.ordinaryRead.obj (restrict.obj B)) from pulled.ordinaryRead.map (restrict.map (cover.ordinaryAssemble f)))
  have pointwise i : part i = readArrow.pieceMap i := by
    apply eq_of_heq
    simp only [part, eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
    exact (cover.ordinaryPullback_component_heq f inside i).symm.trans
      (pulled.ordinaryRead_map_heq (restrict.map (cover.ordinaryAssemble f)) i).symm
  exact ⟨part, fun i j => by rw [pointwise i, pointwise j]; exact readArrow.overlap_comm i j⟩

/-- The pullback arrow's components recover the restrictions of the assembled arrow. -/
theorem ordinaryPullback_matchingMap_piece_heq {V : DeclarationContext P} {A B : Model (Selected.theory U)}
    (f : OrdinaryMatch.Hom (cover.ordinaryRead.obj A) (cover.ordinaryRead.obj B))
    (inside : V ≤ U) (i : cover.Index) :
    HEq ((Selected.modelRestriction ((cover.pullback inside).subset i)).map
      ((Selected.modelRestriction inside).map (cover.ordinaryAssemble f)))
      ((cover.ordinaryPullback_matchingMap f inside).pieceMap i) := by
  simp only [ordinaryPullback_matchingMap, heq_eqToHom_comp_iff, heq_comp_eqToHom_iff]
  exact cover.ordinaryPullback_component_heq f inside i

/-- Ordinary assembly commutes strictly with restriction to any smaller context. -/
theorem ordinaryAssemble_pullback {V : DeclarationContext P} {A B : Model (Selected.theory U)}
    (f : OrdinaryMatch.Hom (cover.ordinaryRead.obj A) (cover.ordinaryRead.obj B))
    (inside : V ≤ U) :
    (Selected.modelRestriction inside).map (cover.ordinaryAssemble f) =
      (cover.pullback inside).ordinaryAssemble (cover.ordinaryPullback_matchingMap f inside) := by
  let localMap := cover.ordinaryPullback_matchingMap f inside
  obtain ⟨g, _, unique⟩ := (cover.pullback inside).existsUnique_ordinary_assemble_heq localMap
  exact (unique _ (cover.ordinaryPullback_matchingMap_piece_heq f inside)).trans
    (unique _ ((cover.pullback inside).ordinaryAssemble_piece_heq localMap)).symm

end

end SHIGURE.DeclarationCover
