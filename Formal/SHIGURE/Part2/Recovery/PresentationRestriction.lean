import Formal.SHIGURE.Part2.Recovery.DeclarationRestriction
import Formal.SHIGURE.Part2.Recovery.Models
import Formal.SHIGURE.Part2.Recovery.SelectedNative
import Mathlib.CategoryTheory.Whiskering

/-!
# Restriction of copied models along a selected presentation

An inclusion of Part I contexts induces a restriction of copying models.
The coefficient and declaration restriction functors act on the same
structures and preserving arrows. Restricting the native models on each
open preserves local splitting.
-/

open AlgebraicGeometry CategoryTheory

universe u

noncomputable section

namespace SHIGURE.Copying

open DeclarationContext.Selected

variable {P : PrimitivePresentation.{u}} {U V : DeclarationContext P}

/-- The named reduct of all native models and their preserving arrows along a context inclusion. -/
def restrictNativePresentation (inside : V ≤ U) : Model (theory U) ⥤ Model (theory V) where
  obj M := ⟨(namesOfLE inside).restrict M.obj, fun l => by
    apply ((namesOfLE inside).restrict_law_iff M.obj ((theory V).law l)).mpr
    rw [namesOfLE_requiredLaw]
    exact M.property (requiredNameOfLE inside l)⟩
  map h := ObjectProperty.homMk (restrictNativeMap (namesOfLE inside) h.hom)
  map_id _ := ObjectProperty.hom_ext _ (StructureMap.ext fun _ _ => rfl)
  map_comp _ _ := ObjectProperty.hom_ext _ (StructureMap.ext fun _ _ => rfl)

/-- The typed reduct agrees with Part I on the native models and every model arrow. -/
theorem restrictNativePresentation_eq (inside : V ≤ U) :
    restrictNativePresentation inside = modelRestriction inside := by
  have objects (M : Model (theory U)) :
      (restrictNativePresentation inside).obj M = (modelRestriction inside).obj M := by
    apply ObjectProperty.FullSubcategory.ext
    rw [modelRestriction_obj, readModel_obj, DeclarationContext.Models.restrict_obj, writeModel_obj,
      writeStructure_namesOfLE_restrict inside, read_write_structure]
    rfl
  refine CategoryTheory.Functor.ext objects ?_
  intro A D h
  apply Model.hom_ext
  intro s x
  simp only [modelRestriction_eq, Functor.comp_map, Model.comp_apply, ordinary_eqToHom_onSort, readFunctor_onSort_cast,
    readOnSort_apply, DeclarationContext.res_onSort, writeFunctor_onSort_cast, writeOnSort_apply,
    DeclarationContext.selectedMap_apply, writeCarrierEquiv_eq_cast, readCarrierEquiv_eq_cast, ← Equiv.cast_symm,
    Equiv.cast_apply, cast_cast]
  rfl

variable {B B' : Scheme.{u}}

/-- The local splittings themselves restrict to the native models on the retained declarations. -/
theorem isZariskiSplit_restrictPresentation (inside : V ≤ U)
    {A : SheafStructure (signature U) (Scheme.zariskiTopology.over B)}
    (hA : IsZariskiSplit (theory U) A) :
    IsZariskiSplit (theory V) (restrictDeclarations (namesOfLE inside) A) := by
  obtain ⟨C, hC⟩ := hA
  refine ⟨C, fun i => ?_⟩
  obtain ⟨M, ⟨e⟩⟩ := hC i
  refine ⟨(restrictNativePresentation inside).obj M, ⟨?_⟩⟩
  exact eqToIso (restrictStructure_restrictDeclarations (C.f i) (namesOfLE inside) A) ≪≫
    (restrictDeclarationsFunctor (C.X i) (namesOfLE inside)).mapIso e ≪≫
    restrictDeclarationsConstantIso (namesOfLE inside) M.obj (C.X i)

/-- Forget the unselected declarations in the copying semantic category. -/
def restrictCopyingPresentation (inside : V ≤ U) (B : Scheme.{u}) :
    (zariskiCopyingProperty (theory U) B).FullSubcategory ⥤
      (zariskiCopyingProperty (theory V) B).FullSubcategory where
  obj A := ⟨restrictDeclarations (namesOfLE inside) A.obj, isZariskiSplit_restrictPresentation inside A.property.1,
    fun l => (restrictDeclarations_holdsLaw_iff (namesOfLE inside) A.obj ((theory V).law l)).mpr (by
      rw [namesOfLE_requiredLaw]
      exact A.property.2 (requiredNameOfLE inside l))⟩
  map h := ObjectProperty.homMk (restrictDeclarationsMap (namesOfLE inside) h.hom)
  map_id _ := ObjectProperty.hom_ext _ (SheafStructure.Hom.ext rfl)
  map_comp _ _ := ObjectProperty.hom_ext _ (SheafStructure.Hom.ext rfl)

/-- Pulling back the open cover preserves the actual native splittings. -/
theorem isZariskiSplit_restrictCoefficients (T : Theory.{u}) (f : B' ⟶ B)
    {A : SheafStructure T.signature (Scheme.zariskiTopology.over B)}
    (hA : IsZariskiSplit T A) : IsZariskiSplit T (restrictStructure f A) := by
  obtain ⟨C, split⟩ := hA
  refine ⟨C.pullback₁ f, fun i => ?_⟩
  obtain ⟨M, ⟨e⟩⟩ := split i
  let g := (C.pullback₁ f).f i
  let p := C.pullbackHom f i
  have he : g ≫ f = p ≫ C.f i := (C.pullbackHom_map f i).symm
  refine ⟨M, ⟨?_⟩⟩
  exact eqToIso (restrictStructure_comp g f A) ≪≫
    eqToIso (congrArg (fun g => restrictStructure g A) he) ≪≫
    (eqToIso (restrictStructure_comp p (C.f i) A)).symm ≪≫
    (restrictStructureFunctor T.signature p).mapIso e ≪≫
    eqToIso (restrictConstantStructure p M.obj)

/-- Coefficient restriction is a functor on the existing copying semantic categories. -/
def restrictCopyingCoefficients (T : Theory.{u}) (f : B' ⟶ B) :
    (zariskiCopyingProperty T B).FullSubcategory ⥤
      (zariskiCopyingProperty T B').FullSubcategory :=
  (zariskiCopyingProperty T B').lift ((zariskiCopyingProperty T B).ι ⋙ restrictStructureFunctor T.signature f)
    (fun A => ⟨isZariskiSplit_restrictCoefficients T f A.property.1,
      fun l => restrictStructure_holdsLaw f A.obj (T.law l) (A.property.2 l)⟩)

/-- The square for declaration and coefficient restriction commutes within the copying model categories. -/
def restrictCopyingPresentation_changeIso (inside : V ≤ U) (f : B' ⟶ B) :
    restrictCopyingPresentation inside B ⋙ restrictCopyingCoefficients (theory V) f ≅
      restrictCopyingCoefficients (theory U) f ⋙ restrictCopyingPresentation inside B' :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro A D h
    simp only [Functor.comp_map, Iso.refl_hom, Category.comp_id, Category.id_comp]
    exact ObjectProperty.hom_ext _ (restrictStructureMap_restrictDeclarationsMap f (namesOfLE inside) h.hom).symm)

/-- Restrict the vocabulary on the public copying model category of Definition 4.1. -/
def selectedCopyingRestriction {base : CoefficientRing.{u}} (inside : V ≤ U) (R : CoefficientAlgebra base) :
    SelectedCopyingModels U R ⥤ SelectedCopyingModels V R := by
  letI := R.scalars.ring
  exact copyingModeModelComparison (theory U) R ⋙ restrictCopyingPresentation inside R.scalars.spec ⋙
    copyingModeModelReadback (theory V) R

/-- Coefficient changes on the public copying category pull back structures and all preserving arrows. -/
def selectedCopyingCoefficientChange {base : CoefficientRing.{u}} (U : DeclarationContext P)
    {R S : CoefficientAlgebra base} (f : R.scalars.Hom S.scalars) :
    SelectedCopyingModels U R ⥤ SelectedCopyingModels U S := by
  letI := R.scalars.ring
  letI := S.scalars.ring
  exact copyingModeModelComparison (theory U) R ⋙
    restrictCopyingCoefficients (theory U) (CoefficientRing.specMap f) ⋙
    copyingModeModelReadback (theory U) S

/-- The two restriction directions commute on the copying models of the selected contexts. -/
def selectedCopyingRestriction_changeIso {base : CoefficientRing.{u}} (inside : V ≤ U)
    {R S : CoefficientAlgebra base} (f : R.scalars.Hom S.scalars) :
    selectedCopyingRestriction inside R ⋙ selectedCopyingCoefficientChange V f ≅
      selectedCopyingCoefficientChange U f ⋙ selectedCopyingRestriction inside S := by
  letI := R.scalars.ring
  letI := S.scalars.ring
  unfold selectedCopyingRestriction selectedCopyingCoefficientChange
  simp only [Functor.assoc, ← Functor.assoc (copyingModeModelReadback _ _) (copyingModeModelComparison _ _),
    copyingModeModelReadback_comp, Functor.id_comp]
  simpa only [Functor.assoc] using CategoryTheory.Functor.isoWhiskerLeft (copyingModeModelComparison (theory U) R)
    (CategoryTheory.Functor.isoWhiskerRight (restrictCopyingPresentation_changeIso inside (CoefficientRing.specMap f))
      (copyingModeModelReadback (theory V) S))

/-- Restriction of the copied structure agrees naturally with the copied Part I native reduct. -/
def restrictCopyingNativeIso (inside : V ≤ U) (R : Type u) [CommRing R] :
    constantCopyingModelFunctor (theory U) R ⋙ restrictCopyingPresentation inside (Spec (CommRingCat.of R)) ≅
      modelRestriction inside ⋙ constantCopyingModelFunctor (theory V) R := by
  rw [← restrictNativePresentation_eq inside]
  exact NatIso.ofComponents
    (fun M => (zariskiCopyingProperty (theory V) (Spec (CommRingCat.of R))).isoMk
      (restrictDeclarationsConstantIso (namesOfLE inside) M.obj (Spec (CommRingCat.of R))))
    (by
      intro A D h
      apply ObjectProperty.hom_ext
      apply SheafStructure.Hom.ext
      funext s
      ext T a
      rfl)

/-- Realize the original Part I model in the public copying category at a coefficient algebra. -/
def selectedConstantCopyingModelFunctor {base : CoefficientRing.{u}} (U : DeclarationContext P)
    (R : CoefficientAlgebra base) : Model (theory U) ⥤ SelectedCopyingModels U R := by
  letI := R.scalars.ring
  exact constantCopyingModelFunctor (theory U) R.scalars.Carrier ⋙ copyingModeModelReadback (theory U) R

/-- The public copying reduct recovers the Part I reduct on every native model and arrow. -/
def selectedCopyingNativeIso {base : CoefficientRing.{u}} (inside : V ≤ U) (R : CoefficientAlgebra base) :
    selectedConstantCopyingModelFunctor U R ⋙ selectedCopyingRestriction inside R ≅
      modelRestriction inside ⋙ selectedConstantCopyingModelFunctor V R := by
  letI := R.scalars.ring
  unfold selectedConstantCopyingModelFunctor selectedCopyingRestriction
  simp only [Functor.assoc, ← Functor.assoc (copyingModeModelReadback _ _) (copyingModeModelComparison _ _),
    copyingModeModelReadback_comp, Functor.id_comp]
  simpa only [Functor.assoc] using CategoryTheory.Functor.isoWhiskerRight
    (restrictCopyingNativeIso inside R.scalars.Carrier)
    (copyingModeModelReadback (theory V) R)

end SHIGURE.Copying
