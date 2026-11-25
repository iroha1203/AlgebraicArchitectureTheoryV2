import Formal.SHIGURE.Part1.FixedModels
import Formal.SHIGURE.Part2.Recovery.StructureMaps
import Formal.SHIGURE.Part2.Realizations.ZariskiModels
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

/-- The full subcategory on copying models isomorphic to constant realizations of native models. -/
abbrev GloballySplitCopyingModels (T : Theory.{u}) (R : Type u) [CommRing R] :=
  (constantCopyingModelFunctor T R).EssImageSubcategory

/-- The original semantic category is equivalent to the globally split full subcategory. -/
def globallySplitCopyingEquivalence (T : Theory.{u}) (R : Type u) [CommRing R] [Nontrivial R]
    [PreconnectedSpace (PrimeSpectrum R)] : Model T ≌ GloballySplitCopyingModels T R := by
  let F := constantCopyingModelFunctor T R
  let h := constantCopyingModelFullyFaithful T R
  letI : F.Full := h.full
  letI : F.Faithful := h.faithful
  letI : F.toEssImage.IsEquivalence := {}
  exact F.toEssImage.asEquivalence

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
