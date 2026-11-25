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
  map_id A := by
    apply Model.hom_ext
    intro s x
    rw [Model.id_apply]
    change (readStructureMap (InducedCategory.Hom.hom (𝟙 A))).onSort s x = x
    simp only [readStructureMap_onSort, readOnSort_apply, Models.id_onSort, Equiv.apply_symm_apply]
  map_comp f g := by
    apply Model.hom_ext
    intro s x
    rw [Model.comp_apply]
    change (readStructureMap (f ≫ g).hom).onSort s x =
      (readStructureMap g.hom).onSort s ((readStructureMap f.hom).onSort s x)
    simp only [readStructureMap_onSort, readOnSort_apply, Models.comp_onSort, Equiv.symm_apply_apply]

/-- The object part of reading is the ordinary model on the selected signature. -/
theorem readFunctor_obj {U : DeclarationContext P} (A : Models U) :
    (readFunctor U).obj A = readModel A :=
  rfl

/-- The read model has the carrier family of its read structure. -/
theorem readFunctor_carrier_eq {U : DeclarationContext P} (A : Models U) :
    ((readFunctor U).obj A).obj.carrier = (readStructure A.obj).carrier :=
  congrArg (fun M => M.obj.carrier) (readFunctor_obj A)

/-- The ordinary component of a read map uses the original retained component. -/
theorem readFunctor_onSort {U : DeclarationContext P} {A B : Models U} (f : A ⟶ B)
    (s : SortName U) (x : ((readFunctor U).obj A).obj.carrier s) :
    ((readFunctor U).map f).hom.onSort s x = cast (congrFun (readFunctor_carrier_eq B).symm s)
      (readOnSort f.hom s (cast (congrFun (readFunctor_carrier_eq A) s) x)) :=
  readStructureMap_onSort f.hom s x

/-- Write ordinary models and arrows as the original-name model data. -/
noncomputable def writeFunctor (U : DeclarationContext P) : Model (theory U) ⥤ Models U where
  obj := writeModel
  map f := ObjectProperty.homMk (writeStructureMap f.hom)
  map_id A := by
    apply Models.hom_ext
    intro s keep x
    change (writeStructureMap (InducedCategory.Hom.hom (𝟙 A))).onSort s keep x = x
    simp only [writeStructureMap_onSort, writeOnSort_apply, Model.id_apply, Equiv.symm_apply_apply]
  map_comp f g := by
    apply Models.hom_ext
    intro s keep x
    change (writeStructureMap (f ≫ g).hom).onSort s keep x =
      (writeStructureMap g.hom).onSort s keep ((writeStructureMap f.hom).onSort s keep x)
    simp only [writeStructureMap_onSort, writeOnSort_apply, Model.comp_apply, Equiv.apply_symm_apply]

/-- The object part of writing is the context model of the selected structure. -/
theorem writeFunctor_obj {U : DeclarationContext P} (A : Model (theory U)) :
    (writeFunctor U).obj A = writeModel A :=
  rfl

/-- The written model has the carrier family of its written structure. -/
theorem writeFunctor_carrier_eq {U : DeclarationContext P} (A : Model (theory U)) :
    ((writeFunctor U).obj A).obj.carrier = (writeStructure A.obj).carrier :=
  congrArg (fun M => M.obj.carrier) (writeFunctor_obj A)

/-- The written point map is the ordinary point map under the retained carrier identification. -/
theorem writeFunctor_onSort {U : DeclarationContext P} {A B : Model (theory U)} (f : A ⟶ B)
    (s : P.signature.SortType) (keep : Declaration.sort s ∈ U.declarations)
    (x : ((writeFunctor U).obj A).obj.carrier s) :
    Models.onSort ((writeFunctor U).map f) s keep x = cast (congrFun (writeFunctor_carrier_eq B).symm s)
      (writeOnSort f.hom s keep (cast (congrFun (writeFunctor_carrier_eq A) s) x)) :=
  writeStructureMap_onSort f.hom s keep x

/-- Equality transport of ordinary model arrows only transports the corresponding point value. -/
theorem ordinary_eqToHom_onSort {U : DeclarationContext P} {A B : Model (theory U)} (h : A = B)
    (s : SortName U) (x : A.obj.carrier s) :
    (eqToHom h).hom.onSort s x = cast (congrArg (fun M => M.obj.carrier s) h) x := by
  subst B
  rfl

/-- Reading then writing is strictly the identity, including on every context arrow. -/
theorem read_comp_write (U : DeclarationContext P) : readFunctor U ⋙ writeFunctor U = 𝟭 (Models U) := by
  have objects (A : Models U) : (readFunctor U ⋙ writeFunctor U).obj A = (𝟭 _).obj A :=
    by simpa only [Functor.comp_obj, Functor.id_obj, readFunctor_obj, writeFunctor_obj] using write_read_model A
  refine CategoryTheory.Functor.ext objects ?_
  intro A B f
  apply Models.hom_ext
  intro s keep x
  simp only [Functor.comp_map, Functor.id_map, writeFunctor_onSort, writeOnSort_apply, readFunctor_onSort,
    readOnSort_apply, Models.comp_onSort, Models.eqToHom_onSort, writeCarrierEquiv_eq_cast, readCarrierEquiv_eq_cast,
    ← Equiv.cast_symm, Equiv.cast_apply, cast_cast]

/-- Writing then reading is strictly the identity, including on all ordinary model arrows. -/
theorem write_comp_read (U : DeclarationContext P) : writeFunctor U ⋙ readFunctor U = 𝟭 (Model (theory U)) := by
  have objects (A : Model (theory U)) : (writeFunctor U ⋙ readFunctor U).obj A = (𝟭 _).obj A :=
    by simpa only [Functor.comp_obj, Functor.id_obj, readFunctor_obj, writeFunctor_obj] using read_write_model A
  refine CategoryTheory.Functor.ext objects ?_
  intro A B f
  apply Model.hom_ext
  intro s x
  change SortName U at s
  rcases s with ⟨s, keep⟩
  simp only [Functor.comp_map, Functor.id_map, readFunctor_onSort, writeFunctor_onSort, writeOnSort_apply,
    readOnSort_apply, Model.comp_apply, ordinary_eqToHom_onSort, writeCarrierEquiv_eq_cast, readCarrierEquiv_eq_cast,
    ← Equiv.cast_symm, Equiv.cast_apply, cast_cast]

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

/-- Ordinary restriction is the comparison of the context restriction through the two model functors. -/
theorem modelRestriction_eq {U V : DeclarationContext P} (inside : V ≤ U) :
    modelRestriction inside = writeFunctor U ⋙ res inside ⋙ readFunctor V :=
  rfl

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
    (modelRestriction inside).obj A = readModel ((writeModel A).restrict inside) := by
  rw [modelRestriction_eq, Functor.comp_obj, Functor.comp_obj, writeFunctor_obj, res_obj, readFunctor_obj]

/-- Restriction also commutes strictly with writing the retained graph data. -/
theorem write_res {U V : DeclarationContext P} (inside : V ≤ U) :
    writeFunctor U ⋙ res inside = modelRestriction inside ⋙ writeFunctor V := by
  rw [modelRestriction, Functor.assoc, Functor.assoc, read_comp_write, Functor.comp_id]

/-- The ordinary model categories and their literal reducts form a contravariant functor. -/
noncomputable def modelPresheaf (P : PrimitivePresentation.{u}) :
    (DeclarationContext P)ᵒᵖ ⥤ Cat.{u, u + 1} where
  obj U := Cat.of (Model (theory (Opposite.unop U)))
  map f := (modelRestriction (leOfHom f.unop)).toCatHom
  map_id U := congrArg Functor.toCatHom (modelRestriction_id (Opposite.unop U))
  map_comp f g := congrArg Functor.toCatHom
    (modelRestriction_comp (leOfHom f.unop) (leOfHom g.unop)).symm

end DeclarationContext.Selected
end SHIGURE
