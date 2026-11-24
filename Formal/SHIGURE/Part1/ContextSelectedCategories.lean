import Formal.SHIGURE.Part1.ContextSelectedRoundtrip
import Formal.SHIGURE.Part1.ContextSelectedMorphisms
import Formal.SHIGURE.Part1.ContextSelectedPresentation
import Formal.SHIGURE.Part1.Contexts

/-! # Ordinary selected model categories and exact declaration descent

The graph presentation used for gluing and the ordinary selected signature
are related by strictly inverse functors. This transfers the existing
strict assembly theorems to the original semantic category of a theory.
-/

universe u

namespace SHIGURE
namespace DeclarationContext.Selected

open CategoryTheory

variable {P : PrimitivePresentation.{u}}

/-- Read all objects and arrows as ordinary models of the selected theory. -/
noncomputable def readFunctor (U : DeclarationContext P) : Models U ⥤ Model (theory U) where
  obj := readModel
  map f := ObjectProperty.homMk (readStructureMap f.hom)
  map_id _ := Model.hom_ext (fun _ _ => rfl)
  map_comp _ _ := Model.hom_ext (fun _ _ => rfl)

/-- The ordinary component of a read map is the original retained component. -/
theorem readFunctor_onSort {U : DeclarationContext P} {A B : Models U} (f : A ⟶ B)
    (s : SortName U) (x : A.obj.carrier s.val) :
    ((readFunctor U).map f).hom.onSort s x = Models.onSort f s.val s.property x :=
  rfl

/-- Write ordinary models and arrows as the original-name model data. -/
noncomputable def writeFunctor (U : DeclarationContext P) : Model (theory U) ⥤ Models U where
  obj := writeModel
  map f := ObjectProperty.homMk (writeStructureMap f.hom)
  map_id A := by
    apply Models.hom_ext
    intro s keep x
    change writeOnSort (InducedCategory.Hom.hom (𝟙 A)) s keep x = x
    simp only [writeOnSort, Model.id_apply, Equiv.symm_apply_apply]
  map_comp f g := by
    apply Models.hom_ext
    intro s keep x
    change writeOnSort (f ≫ g).hom s keep x = writeOnSort g.hom s keep (writeOnSort f.hom s keep x)
    simp only [writeOnSort, Model.comp_apply, Equiv.apply_symm_apply]

/-- The written point map is the ordinary point map under the retained carrier identification. -/
theorem writeFunctor_onSort {U : DeclarationContext P} {A B : Model (theory U)} (f : A ⟶ B)
    (s : P.signature.SortType) (keep : Declaration.sort s ∈ U.declarations) (x : extendedCarrier A.obj s) :
    Models.onSort ((writeFunctor U).map f) s keep x = writeOnSort f.hom s keep x :=
  rfl

/-- Equality transport of ordinary model arrows only transports the corresponding point value. -/
theorem ordinary_eqToHom_onSort {U : DeclarationContext P} {A B : Model (theory U)} (h : A = B)
    (s : SortName U) (x : A.obj.carrier s) :
    (eqToHom h).hom.onSort s x = cast (congrArg (fun M => M.obj.carrier s) h) x := by
  subst B
  rfl

/-- Reading then writing is strictly the identity, including on every context arrow. -/
theorem read_comp_write (U : DeclarationContext P) : readFunctor U ⋙ writeFunctor U = 𝟭 (Models U) := by
  have objects (A : Models U) : (readFunctor U ⋙ writeFunctor U).obj A = (𝟭 _).obj A :=
    write_read_model A
  refine CategoryTheory.Functor.ext objects ?_
  intro A B f
  apply Models.hom_ext
  intro s keep x
  simp only [Functor.comp_map, Functor.id_map, writeFunctor_onSort, writeOnSort, readFunctor_onSort,
    Models.comp_onSort, Models.eqToHom_onSort, extendedEquiv, ← Equiv.cast_symm, Equiv.cast_apply]

/-- Writing then reading is strictly the identity, including on all ordinary model arrows. -/
theorem write_comp_read (U : DeclarationContext P) : writeFunctor U ⋙ readFunctor U = 𝟭 (Model (theory U)) := by
  have objects (A : Model (theory U)) : (writeFunctor U ⋙ readFunctor U).obj A = (𝟭 _).obj A :=
    read_write_model A
  refine CategoryTheory.Functor.ext objects ?_
  intro A B f
  apply Model.hom_ext
  intro s x
  change SortName U at s
  rcases s with ⟨s, keep⟩
  simp only [Functor.comp_map, Functor.id_map, readFunctor_onSort, writeFunctor_onSort, writeOnSort,
    Model.comp_apply, ordinary_eqToHom_onSort, extendedEquiv, ← Equiv.cast_symm, Equiv.cast_apply]

/-- The graph and ordinary model categories are strictly isomorphic. -/
noncomputable def modelIso (U : DeclarationContext P) : Cat.of (Models U) ≅ Cat.of (Model (theory U)) where
  hom := (readFunctor U).toCatHom
  inv := (writeFunctor U).toCatHom
  hom_inv_id := congrArg Functor.toCatHom (read_comp_write U)
  inv_hom_id := congrArg Functor.toCatHom (write_comp_read U)

/-- Restrict an ordinary model by translating the same readout of retained declaration data. -/
noncomputable def modelRestriction {U V : DeclarationContext P} (inside : V ≤ U) :
    Model (theory U) ⥤ Model (theory V) :=
  writeFunctor U ⋙ res inside ⋙ readFunctor V

/-- Restricting ordinary models commutes strictly with the comparison on objects and arrows. -/
theorem read_res {U V : DeclarationContext P} (inside : V ≤ U) :
    res inside ⋙ readFunctor V = readFunctor U ⋙ modelRestriction inside := by
  rw [modelRestriction, ← Functor.assoc, read_comp_write, Functor.id_comp]

/-- The ordinary restriction is strictly the identity on an identity inclusion. -/
theorem modelRestriction_id (U : DeclarationContext P) : modelRestriction (le_refl U) = 𝟭 (Model (theory U)) := by
  rw [modelRestriction, res_id, Functor.id_comp, write_comp_read]

/-- Ordinary restriction composes strictly along inclusions. -/
theorem modelRestriction_comp {U V W : DeclarationContext P} (inside : V ≤ U) (smaller : W ≤ V) :
    modelRestriction inside ⋙ modelRestriction smaller = modelRestriction (smaller.trans inside) := by
  rw [modelRestriction, modelRestriction, modelRestriction]
  simp only [Functor.assoc]
  rw [← Functor.assoc (readFunctor V) (writeFunctor V), read_comp_write, Functor.id_comp,
    ← Functor.assoc (res inside) (res smaller), res_comp]

/-- The object reduct reads the genuinely selected theory of the smaller context. -/
theorem modelRestriction_obj {U V : DeclarationContext P} (inside : V ≤ U) (A : Model (theory U)) :
    (modelRestriction inside).obj A = readModel ((writeModel A).restrict inside) :=
  rfl

end DeclarationContext.Selected

namespace ChapterContext

open CategoryTheory DeclarationContext

/-- The ordinary model category of the actual restricted primitive presentation. -/
abbrev Models {P : PrimitivePresentation.{u}} (U : ChapterContext P) := Model U.restrict.theory

/-- The ordinary model reduct along a logical declaration inclusion. -/
noncomputable def res {P : PrimitivePresentation.{u}} {U V : ChapterContext P} (inside : V ≤ U) :
    Models U ⥤ Models V :=
  Selected.modelRestriction inside

end ChapterContext

namespace DeclarationCover

open CategoryTheory DeclarationContext

/-- The ordinary semantic category of the actual restricted presentation satisfies (3.3). -/
noncomputable def ordinaryModelIso {P : PrimitivePresentation.{u}} {U : DeclarationContext P}
    (cover : DeclarationCover U) : Cat.of (Model (Selected.presentation U).theory) ≅ Cat.of (Match cover.piece) :=
  (Selected.modelIso U).symm ≪≫ cover.modelIso

/-- Theorem 3.4 in the ordinary semantic category of the genuinely restricted theory. -/
theorem existsUnique_ordinary_glue {P : PrimitivePresentation.{u}} {U : DeclarationContext P}
    (cover : DeclarationCover U) (A : Match cover.piece) :
    ∃! X : Model (Selected.theory U), ∀ i,
      (Selected.modelRestriction (cover.subset i)).obj X = Selected.readModel (A.pieceModel i) := by
  refine ⟨Selected.readModel (A.glue cover), ?_, ?_⟩
  · intro i
    rw [Selected.modelRestriction_obj, Selected.write_read_model, A.glue_restrict cover i]
  · intro X restrictions
    have same : Selected.writeModel X = A.glue cover :=
      cover.models_eq_of_restrict_eq fun i => by
        have localEq := congrArg Selected.writeModel (restrictions i)
        rw [Selected.modelRestriction_obj, Selected.write_read_model, Selected.write_read_model] at localEq
        exact localEq.trans (A.glue_restrict cover i).symm
    rw [← Selected.read_write_model X, same]

end DeclarationCover
end SHIGURE
