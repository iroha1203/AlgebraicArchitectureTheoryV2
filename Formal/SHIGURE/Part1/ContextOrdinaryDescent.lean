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
    cover.ordinaryRead ⋙ OrdinaryMatch.project i = Selected.modelRestriction (cover.subset i) :=
  rfl

/-- The components of the restriction to a cover are the ordinary reducts. -/
theorem ordinaryRead_obj (X : Model (Selected.theory U)) (i : cover.Index) :
    (cover.ordinaryRead.obj X).pieceModel i = (Selected.modelRestriction (cover.subset i)).obj X :=
  rfl

/-- The arrow read at each piece is its usual ordinary reduct. -/
theorem ordinaryRead_map {A B : Model (Selected.theory U)} (f : A ⟶ B) (i : cover.Index) :
    (show OrdinaryMatch.Hom _ _ from cover.ordinaryRead.map f).pieceMap i =
      (Selected.modelRestriction (cover.subset i)).map f :=
  rfl

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
    exact congrArg (fun B : OrdinaryMatch cover.piece => B.pieceModel i) (cover.ordinaryGlue_read A)
  · intro X h
    have matching : cover.ordinaryRead.obj X = A := OrdinaryMatch.ext h
    exact (Functor.congr_obj cover.ordinaryRead_comp_glue X).symm.trans
      (congrArg cover.ordinaryGlue.obj matching)

/-- An assembled map has the originally specified ordinary endpoints. -/
noncomputable def ordinaryAssemble {A B : Model (Selected.theory U)}
    (f : OrdinaryMatch.Hom (cover.ordinaryRead.obj A) (cover.ordinaryRead.obj B)) : A ⟶ B :=
  eqToHom (Functor.congr_obj cover.ordinaryRead_comp_glue A).symm ≫
    cover.ordinaryGlue.map f ≫ eqToHom (Functor.congr_obj cover.ordinaryRead_comp_glue B)

/-- Reading the assembled ordinary arrow gives exactly the supplied matching arrow. -/
theorem ordinaryAssemble_read {A B : Model (Selected.theory U)}
    (f : OrdinaryMatch.Hom (cover.ordinaryRead.obj A) (cover.ordinaryRead.obj B)) :
    cover.ordinaryRead.map (cover.ordinaryAssemble f) = f := by
  let R := cover.ordinaryRead
  let G := cover.ordinaryGlue
  have h := Functor.congr_hom cover.ordinaryGlue_comp_read (show R.obj A ⟶ R.obj B from f)
  change R.map (eqToHom (Functor.congr_obj cover.ordinaryRead_comp_glue A).symm ≫ G.map f ≫
    eqToHom (Functor.congr_obj cover.ordinaryRead_comp_glue B)) = f
  simp only [Functor.map_comp, eqToHom_map]
  change _ ≫ (G ⋙ R).map f ≫ _ = _
  rw [h]
  simp only [Functor.id_map, Category.assoc, eqToHom_trans_assoc, eqToHom_trans, eqToHom_refl, Category.id_comp, Category.comp_id]

/-- Theorem 3.5 for arbitrary compatible arrows of the ordinary local models. -/
theorem existsUnique_ordinary_assemble {A B : Model (Selected.theory U)}
    (f : OrdinaryMatch.Hom (cover.ordinaryRead.obj A) (cover.ordinaryRead.obj B)) :
    ∃! h : A ⟶ B, ∀ i, (Selected.modelRestriction (cover.subset i)).map h = f.pieceMap i := by
  refine ⟨cover.ordinaryAssemble f, ?_, ?_⟩
  · intro i
    exact congrArg (fun g : OrdinaryMatch.Hom _ _ => g.pieceMap i) (cover.ordinaryAssemble_read f)
  · intro h components
    have matching : cover.ordinaryRead.map h = f :=
      OrdinaryMatch.Hom.ext components
    unfold ordinaryAssemble
    rw [← matching]
    change h = _ ≫ (cover.ordinaryRead ⋙ cover.ordinaryGlue).map h ≫ _
    rw [Functor.congr_hom cover.ordinaryRead_comp_glue h]
    simp only [Functor.id_map, Category.assoc, eqToHom_trans_assoc, eqToHom_trans, eqToHom_refl, Category.id_comp, Category.comp_id]

end SHIGURE.DeclarationCover
