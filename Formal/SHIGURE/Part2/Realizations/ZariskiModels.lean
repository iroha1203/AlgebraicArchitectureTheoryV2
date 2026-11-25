import Formal.SHIGURE.Part1.ContextSelectedPresentation
import Formal.SHIGURE.Part1.Models
import Formal.SHIGURE.Part2.Realizations.ConstantStructures
import Formal.SHIGURE.Part2.Realizations.SheafStructureMaps

/-!
# Zariski locally split copying models

The whole structure of a copying realization is locally isomorphic to a
native model's constant realization. The native model may vary across the
cover. The global morphisms are the structure-preserving sheaf maps.

## Implementation notes

Restriction acts on the relative test category by composing the test
scheme's structural map with the base morphism. The sectionwise assignment
sheaf supplies the same tuples before and after restriction. Restricting
only the carrier sheaves would leave the primitive domains and their
operations unspecified.
-/

open AlgebraicGeometry CategoryTheory Opposite

universe u

noncomputable section

namespace SHIGURE.Copying

variable {S S' : Scheme.{u}}

/-- Coefficient restriction of a predicate pulls back all its satisfying sections. -/
def restrictPredicate (f : S' ⟶ S) {F : ZariskiSheaf S} (P : SheafPredicate F) :
    SheafPredicate ((Scheme.zariskiTopology.overMapPullback (Type u) f).obj F) where
  carrier :=
    { obj := fun U => P.carrier.obj (op ((Over.map f).obj U.unop))
      map := by
        intro U V g x hx
        exact P.carrier.map ((Over.map f).map g.unop).op hx }
  isSheaf := by
    apply (isSheaf_iff_isSheaf_of_type (Scheme.zariskiTopology.over S') _).mp
    exact ((Scheme.zariskiTopology.overMapPullback (Type u) f).obj P.toSheaf).cond

/-- Restrict the carriers and all primitive interpretations along a map of base schemes. -/
def restrictStructure {sig : Signature.{u}} (f : S' ⟶ S)
    (A : SheafStructure sig (Scheme.zariskiTopology.over S)) :
    SheafStructure sig (Scheme.zariskiTopology.over S') where
  carrier s := (Scheme.zariskiTopology.overMapPullback (Type u) f).obj (A.carrier s)
  total op := (Scheme.zariskiTopology.overMapPullback (Type u) f).map (A.total op)
  relation r := restrictPredicate f (A.relation r)
  partialDomain p := restrictPredicate f (A.partialDomain p)
  partialValue p := (Scheme.zariskiTopology.overMapPullback (Type u) f).map (A.partialValue p)
  quantity q := (Scheme.zariskiTopology.overMapPullback (Type u) f).map (A.quantity q)

/-- A structure-preserving sheaf map restricts to a structure-preserving map on the new test site. -/
def restrictStructureMap {sig : Signature.{u}} (f : S' ⟶ S)
    {A B : SheafStructure sig (Scheme.zariskiTopology.over S)} (h : SheafStructure.Hom A B) :
    SheafStructure.Hom (restrictStructure f A) (restrictStructure f B) where
  onSort s := (Scheme.zariskiTopology.overMapPullback (Type u) f).map (h.onSort s)
  preservesTotal op := congrArg ((Scheme.zariskiTopology.overMapPullback (Type u) f).map)
    (h.preservesTotal op)
  preservesRelation r := fun U _ hx => h.preservesRelation r (op ((Over.map f).obj U.unop)) hx
  preservesDomain p := fun U _ hx => h.preservesDomain p (op ((Over.map f).obj U.unop)) hx
  preservesPartial p := congrArg ((Scheme.zariskiTopology.overMapPullback (Type u) f).map)
    (h.preservesPartial p)
  preservesQuantity q := congrArg ((Scheme.zariskiTopology.overMapPullback (Type u) f).map)
    (h.preservesQuantity q)

/-- Restriction on base schemes is functorial on the full primitive structures. -/
def restrictStructureFunctor (sig : Signature.{u}) (f : S' ⟶ S) :
    SheafStructure sig (Scheme.zariskiTopology.over S) ⥤
      SheafStructure sig (Scheme.zariskiTopology.over S') where
  obj := restrictStructure f
  map := restrictStructureMap f
  map_id _ := SheafStructure.Hom.ext rfl
  map_comp _ _ := SheafStructure.Hom.ext rfl

/-- Changing the base of a constant structure changes only its relative test category. -/
theorem restrictConstantStructure {sig : Signature.{u}} (f : S' ⟶ S) (A : Structure sig) :
    restrictStructure f (constantStructure S A) = constantStructure S' A :=
  rfl

/-- The copying rule for changing coefficients along a homomorphism of rings. -/
def changeCopyingCoefficients {sig : Signature.{u}} {R R' : Type u} [CommRing R] [CommRing R']
    (f : R →+* R')
    (A : SheafStructure sig (Scheme.zariskiTopology.over (Spec (CommRingCat.of R)))) :
    SheafStructure sig (Scheme.zariskiTopology.over (Spec (CommRingCat.of R'))) :=
  restrictStructure (Spec.map (CommRingCat.ofHom f)) A

/-- Zariski local splitting compares the full primitive structure on every cover piece
with the constant realization of a native model on that piece. -/
def IsZariskiSplit (T : Theory.{u}) (A : SheafStructure T.signature (Scheme.zariskiTopology.over S)) : Prop :=
  ∃ cover : Scheme.OpenCover.{u, u} S, ∀ i : cover.I₀, ∃ native : Model T,
    Nonempty (restrictStructure (cover.f i) A ≅ constantStructure (cover.X i) native.obj)

/-- The constant realization of a single native model satisfies the local splitting condition. -/
theorem isZariskiSplit_constant (T : Theory.{u}) (M : Model T) :
    IsZariskiSplit T (constantStructure S M.obj) :=
  ⟨S.affineCover, fun i => ⟨M, ⟨eqToIso (restrictConstantStructure (S.affineCover.f i) M.obj)⟩⟩⟩

/-- Copying models are locally split and satisfy each required Law in the sheaf semantics. -/
def zariskiCopyingProperty (T : Theory.{u}) (S : Scheme.{u}) :
    ObjectProperty (SheafStructure T.signature (Scheme.zariskiTopology.over S)) :=
  fun A => IsZariskiSplit T A ∧ ∀ name : T.LawName, A.holdsLaw (T.law name)

/-- The copying-mode semantic category at the chosen coefficients. -/
abbrev ZariskiCopyingModels (T : Theory.{u}) (R : Type u) [CommRing R] :=
  (zariskiCopyingProperty T (Spec (CommRingCat.of R))).FullSubcategory

end SHIGURE.Copying
