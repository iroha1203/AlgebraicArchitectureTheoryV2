import Formal.SHIGURE.Part1.FixedModels
import Formal.SHIGURE.Part2.Recovery.StructureMaps
import Formal.SHIGURE.Part2.Realizations.CopyingMode
import Formal.SHIGURE.Part2.Recovery.SheafLawMaps
import Mathlib.CategoryTheory.Equivalence

/-!
# The globally split part of the copying semantic category

The constant realization of a model satisfies each written Law. Its
essential image in the copying semantic category is the full subcategory
of globally split copying models.
-/

open AlgebraicGeometry CategoryTheory Opposite

universe u

noncomputable section

namespace SHIGURE.Copying

/-- Apply the constant realization to each native model and its preserving arrows. -/
def constantCopyingModelFunctor (T : Theory.{u}) (R : Type u) [CommRing R] :
    Model T ⥤ ZariskiCopyingModels T R where
  obj M :=
    ⟨constantStructure (Spec (CommRingCat.of R)) M.obj, isZariskiSplit_constant T M,
      fun name => constantStructure_holdsLaw M.obj (T.law name) (M.property name)⟩
  map f := ObjectProperty.homMk (constantStructureMap (Spec (CommRingCat.of R)) f.hom)
  map_id M := ObjectProperty.hom_ext _ ((constantStructureFunctor T.signature (Spec (CommRingCat.of R))).map_id M.obj)
  map_comp f g := ObjectProperty.hom_ext _
    ((constantStructureFunctor T.signature (Spec (CommRingCat.of R))).map_comp f.hom g.hom)

/-- Connected nonzero coefficients recover all native arrows between the copied models. -/
def constantCopyingModelFullyFaithful (T : Theory.{u}) (R : Type u) [CommRing R] [Nontrivial R]
    [PreconnectedSpace (PrimeSpectrum R)] : (constantCopyingModelFunctor T R).FullyFaithful := by
  let S := Spec (CommRingCat.of R)
  letI : PreconnectedSpace S := inferInstanceAs (PreconnectedSpace (PrimeSpectrum R))
  letI : Nonempty S := inferInstanceAs (Nonempty (PrimeSpectrum R))
  refine ⟨fun {M N} f => ObjectProperty.homMk ((constantStructureMapsEquiv (S := S)).symm f.hom), ?_, ?_⟩
  · intro M N f
    exact ObjectProperty.hom_ext _ ((constantStructureMapsEquiv (S := S)).apply_symm_apply f.hom)
  · intro M N f
    exact ObjectProperty.hom_ext _ ((constantStructureMapsEquiv (S := S)).symm_apply_apply f.hom)

/-- A structure is globally split when its entire primitive structure has a native presentation. -/
def IsGloballySplit {sig : Signature.{u}} {S : Scheme.{u}}
    (A : SheafStructure sig (Scheme.zariskiTopology.over S)) : Prop :=
  ∃ N : Structure sig, Nonempty (constantStructure S N ≅ A)

/-- The full subcategory of globally split copying models of the original coefficient semantics. -/
def globallySplitCopyingProperty (T : Theory.{u}) (R : Type u) [CommRing R] :
    ObjectProperty (ZariskiCopyingModels T R) :=
  fun A => IsGloballySplit A.obj

/-- The original pattern of objects, before identifying it with the image of native models. -/
abbrev GloballySplitCopyingModels (T : Theory.{u}) (R : Type u) [CommRing R] :=
  (globallySplitCopyingProperty T R).FullSubcategory

/-- The Laws of a copied model transfer across a structure isomorphism and reflect to the native structure. -/
theorem nativeLaws_of_globallySplit {T : Theory.{u}} {R : Type u} [CommRing R] [Nontrivial R]
    (A : ZariskiCopyingModels T R) (N : Structure T.signature)
    (e : constantStructure (Spec (CommRingCat.of R)) N ≅ A.obj) : T.Holds N := by
  letI : Nonempty (Spec (CommRingCat.of R)) := inferInstanceAs (Nonempty (PrimeSpectrum R))
  intro l
  exact (constantStructure_holdsLaw_iff N (T.law l)).mp
    (SheafStructure.holdsLaw_of_iso e.symm (T.law l) (A.property.2 l))

/-- Over nonzero coefficients the independently defined globally split objects are exactly the native image. -/
theorem globallySplitCopying_iff_mem_essImage {T : Theory.{u}} {R : Type u} [CommRing R] [Nontrivial R]
    (A : ZariskiCopyingModels T R) :
    globallySplitCopyingProperty T R A ↔ (constantCopyingModelFunctor T R).essImage A := by
  constructor
  · rintro ⟨N, ⟨e⟩⟩
    let M : Model T := ⟨N, nativeLaws_of_globallySplit A N e⟩
    exact ⟨M, ⟨(zariskiCopyingProperty T (Spec (CommRingCat.of R))).isoMk e⟩⟩
  · rintro ⟨M, ⟨e⟩⟩
    exact ⟨M.obj, ⟨(zariskiCopyingProperty T (Spec (CommRingCat.of R))).ι.mapIso e⟩⟩

/-- The constant model functor takes values in the independently defined globally split subcategory. -/
def globallySplitCopyingFunctor (T : Theory.{u}) (R : Type u) [CommRing R] :
    Model T ⥤ GloballySplitCopyingModels T R :=
  (globallySplitCopyingProperty T R).lift (constantCopyingModelFunctor T R)
    (fun M => ⟨M.obj, ⟨Iso.refl _⟩⟩)

/-- The original semantic category is equivalent to the full subcategory selected by global splitting. -/
def globallySplitCopyingEquivalence (T : Theory.{u}) (R : Type u) [CommRing R] [Nontrivial R]
    [PreconnectedSpace (PrimeSpectrum R)] : Model T ≌ GloballySplitCopyingModels T R := by
  let F := constantCopyingModelFunctor T R
  let G := globallySplitCopyingFunctor T R
  let h := constantCopyingModelFullyFaithful T R
  letI : F.Full := h.full
  letI : F.Faithful := h.faithful
  letI : G.Full := inferInstanceAs (((globallySplitCopyingProperty T R).lift F _).Full)
  letI : G.Faithful := inferInstanceAs (((globallySplitCopyingProperty T R).lift F _).Faithful)
  letI : G.EssSurj := ⟨fun A => by
    obtain ⟨M, ⟨e⟩⟩ := (globallySplitCopying_iff_mem_essImage A.obj).mp A.property
    exact ⟨M, ⟨(globallySplitCopyingProperty T R).isoMk e⟩⟩⟩
  letI : G.IsEquivalence := {}
  exact G.asEquivalence

/-- Compare the actual Definition 4.1 carrier-diagram category with the sheaf-structure presentation. -/
def copyingModeModelComparison {base : CoefficientRing.{u}} (T : Theory.{u}) (R : CoefficientAlgebra base) :
    letI := R.scalars.ring
    (copyingMode base T).Models R ⥤ ZariskiCopyingModels T R.scalars.Carrier := by
  letI := R.scalars.ring
  exact
    { obj := fun M => ⟨M.obj, M.property⟩
      map := fun {M N} f => ObjectProperty.homMk
        (copyingStructureHomEquiv T.signature R.scalars.spec M.obj N.obj f.hom)
      map_id := fun _ => ObjectProperty.hom_ext _ (SheafStructure.Hom.ext rfl)
      map_comp := fun _ _ => ObjectProperty.hom_ext _ (SheafStructure.Hom.ext rfl) }

/-- The models at the public copying-mode entry and the sheaf-model category are equivalent. -/
def copyingModeModelEquivalence {base : CoefficientRing.{u}} (T : Theory.{u}) (R : CoefficientAlgebra base) :
    letI := R.scalars.ring
    (copyingMode base T).Models R ≌ ZariskiCopyingModels T R.scalars.Carrier := by
  letI := R.scalars.ring
  let F := copyingModeModelComparison T R
  let H : F.FullyFaithful :=
    { preimage := fun {M N} f => ObjectProperty.homMk
        ((copyingStructureHomEquiv T.signature R.scalars.spec M.obj N.obj).symm f.hom)
      map_preimage := fun f => ObjectProperty.hom_ext _ ((copyingStructureHomEquiv _ _ _ _).apply_symm_apply f.hom)
      preimage_map := fun f => ObjectProperty.hom_ext _ ((copyingStructureHomEquiv _ _ _ _).symm_apply_apply f.hom) }
  letI : F.Full := H.full
  letI : F.Faithful := H.faithful
  letI : F.EssSurj := ⟨fun M => ⟨⟨M.obj, M.property⟩, ⟨Iso.refl M⟩⟩⟩
  letI : F.IsEquivalence := {}
  exact F.asEquivalence

/-- The independent global splitting condition on the public copying-mode meaning category. -/
def globallySplitModeProperty {base : CoefficientRing.{u}} (T : Theory.{u}) (R : CoefficientAlgebra base) :
    ObjectProperty ((copyingMode base T).Models R) :=
  fun A => IsGloballySplit A.obj

/-- The comparison with the sheaf-structure presentation respects exactly the globally split objects. -/
def globallySplitModeComparison {base : CoefficientRing.{u}} (T : Theory.{u}) (R : CoefficientAlgebra base) :
    letI := R.scalars.ring
    (globallySplitModeProperty T R).FullSubcategory ≌ GloballySplitCopyingModels T R.scalars.Carrier := by
  letI := R.scalars.ring
  let F := (copyingModeModelEquivalence T R).functor
  let G := (globallySplitCopyingProperty T R.scalars.Carrier).lift
    ((globallySplitModeProperty T R).ι ⋙ F) (fun A => A.property)
  letI : F.IsEquivalence := inferInstanceAs ((copyingModeModelEquivalence T R).functor.IsEquivalence)
  letI : G.Full := inferInstanceAs
    (((globallySplitCopyingProperty T R.scalars.Carrier).lift
      ((globallySplitModeProperty T R).ι ⋙ F) _).Full)
  letI : G.Faithful := inferInstanceAs
    (((globallySplitCopyingProperty T R.scalars.Carrier).lift
      ((globallySplitModeProperty T R).ι ⋙ F) _).Faithful)
  letI : G.EssSurj := ⟨fun A => ⟨⟨⟨A.obj.obj, A.obj.property⟩, A.property⟩, ⟨Iso.refl A⟩⟩⟩
  letI : G.IsEquivalence := {}
  exact G.asEquivalence

/-- The globally split full subcategory of Definition 4.1 is equivalent to the native meaning category. -/
def globallySplitCopyingModeEquivalence {base : CoefficientRing.{u}} (T : Theory.{u})
    (R : CoefficientAlgebra base) :
    letI := R.scalars.ring
    [Nontrivial R.scalars.Carrier] → [PreconnectedSpace (PrimeSpectrum R.scalars.Carrier)] →
      Model T ≌ (globallySplitModeProperty T R).FullSubcategory := by
  letI := R.scalars.ring
  intro _ _
  exact (globallySplitCopyingEquivalence T R.scalars.Carrier).trans (globallySplitModeComparison T R).symm

variable {S : Scheme.{u}} {sig : Signature.{u}} {A B : Structure sig}

/-- A designated native value is preserved exactly when the corresponding native section is preserved. -/
theorem constantStructureMap_preservesValue_iff (T : Over S) [Nonempty T.left]
    (f : StructureMap A B) (s : sig.SortType) (x : A.carrier s) (y : B.carrier s) :
    ((constantStructureMap S f).onSort s).val.app (op T) (nativeState S T x) = nativeState S T y ↔
      f.onSort s x = y := by
  change LocallyConstant.const T.left (f.onSort s x) = LocallyConstant.const T.left y ↔ _
  constructor
  · intro h
    obtain ⟨p⟩ := (inferInstance : Nonempty T.left)
    exact DFunLike.congr_fun h p
  · exact congrArg (LocallyConstant.const T.left)

/-- Fixed carrier identities on native states are exactly the corresponding fixed carrier identities of sheaf maps. -/
theorem constantStructureMap_fixesSort_iff [Nonempty S]
    (f : StructureMap A B) (s : sig.SortType) (h : A.carrier s = B.carrier s) :
    (constantStructureMap S f).onSort s = constantCarrierMap S (cast h) ↔
      ∀ x : A.carrier s, f.onSort s x = cast h x := by
  constructor
  · intro he
    exact congrFun (congrArg readConstantCarrierMap he)
  · intro he
    exact congrArg (constantCarrierMap S) (funext he)

/-- The fixed-data condition from Part I is the identity condition on exactly the prescribed carrier sheaves. -/
theorem constantCopyingModelMap_fixesCarriers_iff {D : Signature.{u}} {theory : Theory.{u}}
    {names : Subsignature D theory.signature} {data : Structure D} [Nonempty S]
    (M N : FixedModel theory names data) (f : M.model ⟶ N.model) :
    (∀ s : D.SortType, (constantStructureMap S f.hom).onSort (names.val.onSort s) =
      constantCarrierMap S (cast ((M.carrier_eq s).trans (N.carrier_eq s).symm))) ↔
      FixedModel.FixesCarriers M N f := by
  constructor
  · intro h s
    exact (constantStructureMap_fixesSort_iff f.hom (names.val.onSort s) _).mp (h s)
  · intro h s
    exact (constantStructureMap_fixesSort_iff f.hom (names.val.onSort s) _).mpr (h s)

end SHIGURE.Copying
