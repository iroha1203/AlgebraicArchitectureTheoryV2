import Formal.SHIGURE.Part2.Recovery.DeclarationRestriction
import Formal.SHIGURE.Part2.Recovery.Models

/-!
# Restriction of copied models along a selected presentation

The Part I selection records exactly which required Laws and primitive
names are retained. The coefficient and declaration restriction functors
act on the same structures and preserving arrows. The named reduct
retains local splitting by restricting each original native model.
-/

open AlgebraicGeometry CategoryTheory

universe u

noncomputable section

namespace SHIGURE.Copying

variable {P Q : PrimitivePresentation.{u}} {U : DeclarationContext Q}

/-- Retaining a required Law preserves its role as well as its ambient name. -/
def retainedRequiredName (origin : ReadingOrigin P Q U) (l : P.theory.LawName) :
    Q.theory.LawName :=
  ⟨origin.lawName l.val, (origin.law_role l.val).symm.trans l.property⟩

/-- The Part I selection keeps the literal antecedent and conclusion of each retained required Law. -/
theorem retainedRequiredLaw_eq (origin : ReadingOrigin P Q U) (l : P.theory.LawName) :
    origin.signature.law (P.theory.law l) = Q.theory.law (retainedRequiredName origin l) :=
  origin.law_eq l.val

/-- The corresponding Part I restriction of models and their preserving arrows. -/
def restrictNativePresentation (origin : ReadingOrigin P Q U) : Model Q.theory ⥤ Model P.theory where
  obj M := ⟨origin.signature.restrict M.obj, fun l => by
    apply (origin.signature.restrict_law_iff M.obj (P.theory.law l)).mpr
    rw [retainedRequiredLaw_eq]
    exact M.property (retainedRequiredName origin l)⟩
  map h := ObjectProperty.homMk (restrictNativeMap origin.signature h.hom)
  map_id _ := ObjectProperty.hom_ext _ (StructureMap.ext fun _ _ => rfl)
  map_comp _ _ := ObjectProperty.hom_ext _ (StructureMap.ext fun _ _ => rfl)

variable {B B' : Scheme.{u}}

/-- The local splittings themselves restrict to the native models on the retained declarations. -/
theorem isZariskiSplit_restrictPresentation (origin : ReadingOrigin P Q U)
    {A : SheafStructure Q.signature (Scheme.zariskiTopology.over B)}
    (hA : IsZariskiSplit Q.theory A) :
    IsZariskiSplit P.theory (restrictDeclarations origin.signature A) := by
  obtain ⟨C, hC⟩ := hA
  refine ⟨C, fun i => ?_⟩
  obtain ⟨M, ⟨e⟩⟩ := hC i
  refine ⟨(restrictNativePresentation origin).obj M, ⟨?_⟩⟩
  exact eqToIso (restrictStructure_restrictDeclarations (C.f i) origin.signature A) ≪≫
    (restrictDeclarationsFunctor (C.X i) origin.signature).mapIso e ≪≫
    restrictDeclarationsConstantIso origin.signature M.obj (C.X i)

/-- Forget the unselected declarations in the copying semantic category. -/
def restrictCopyingPresentation (origin : ReadingOrigin P Q U) (B : Scheme.{u}) :
    (zariskiCopyingProperty Q.theory B).FullSubcategory ⥤
      (zariskiCopyingProperty P.theory B).FullSubcategory where
  obj A := ⟨restrictDeclarations origin.signature A.obj, isZariskiSplit_restrictPresentation origin A.property.1,
    fun l => (restrictDeclarations_holdsLaw_iff origin.signature A.obj (P.theory.law l)).mpr (by
      rw [retainedRequiredLaw_eq]
      exact A.property.2 (retainedRequiredName origin l))⟩
  map h := ObjectProperty.homMk (restrictDeclarationsMap origin.signature h.hom)
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
      (zariskiCopyingProperty T B').FullSubcategory where
  obj A := ⟨restrictStructure f A.obj, isZariskiSplit_restrictCoefficients T f A.property.1,
    fun l => restrictStructure_holdsLaw f A.obj (T.law l) (A.property.2 l)⟩
  map h := ObjectProperty.homMk (restrictStructureMap f h.hom)
  map_id _ := ObjectProperty.hom_ext _ (SheafStructure.Hom.ext rfl)
  map_comp _ _ := ObjectProperty.hom_ext _ (SheafStructure.Hom.ext rfl)

/-- The square for declaration and coefficient restriction commutes within the copying model categories. -/
def restrictCopyingPresentation_changeIso (origin : ReadingOrigin P Q U) (f : B' ⟶ B) :
    restrictCopyingPresentation origin B ⋙ restrictCopyingCoefficients P.theory f ≅
      restrictCopyingCoefficients Q.theory f ⋙ restrictCopyingPresentation origin B' :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro A D h
    simp only [Functor.comp_map, Iso.refl_hom, Category.comp_id, Category.id_comp]
    exact ObjectProperty.hom_ext _ (restrictStructureMap_restrictDeclarationsMap f origin.signature h.hom).symm)

/-- Restriction of the copied structure agrees naturally with the copied Part I native reduct. -/
def restrictCopyingNativeIso (origin : ReadingOrigin P Q U) (R : Type u) [CommRing R] :
    constantCopyingModelFunctor Q.theory R ⋙ restrictCopyingPresentation origin (Spec (CommRingCat.of R)) ≅
      restrictNativePresentation origin ⋙ constantCopyingModelFunctor P.theory R :=
  NatIso.ofComponents
    (fun M => (zariskiCopyingProperty P.theory (Spec (CommRingCat.of R))).isoMk
      (restrictDeclarationsConstantIso origin.signature M.obj (Spec (CommRingCat.of R))))
    (by
      intro A D h
      apply ObjectProperty.hom_ext
      apply SheafStructure.Hom.ext
      funext s
      ext T a
      rfl)

end SHIGURE.Copying
