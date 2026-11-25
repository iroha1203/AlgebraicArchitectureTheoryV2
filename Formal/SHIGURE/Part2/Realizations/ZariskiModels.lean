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

/-- Restrict a predicate along the continuous functor on relative test objects. -/
private def restrictPredicateAlong (F : Over S' ⥤ Over S)
    [F.IsContinuous (Scheme.zariskiTopology.over S') (Scheme.zariskiTopology.over S)]
    {G : ZariskiSheaf S} (P : SheafPredicate G) :
    SheafPredicate ((F.sheafPushforwardContinuous (Type u) (Scheme.zariskiTopology.over S') (Scheme.zariskiTopology.over S)).obj G) where
  carrier :=
    { obj := fun U => P.carrier.obj (op (F.obj U.unop))
      map := by
        intro U V g x hx
        exact P.carrier.map (F.map g.unop).op hx }
  isSheaf := by
    apply (isSheaf_iff_isSheaf_of_type (Scheme.zariskiTopology.over S') _).mp
    exact ((F.sheafPushforwardContinuous (Type u) (Scheme.zariskiTopology.over S') (Scheme.zariskiTopology.over S)).obj P.toSheaf).cond

/-- Coefficient restriction of a predicate pulls back all its satisfying sections. -/
def restrictPredicate (f : S' ⟶ S) {F : ZariskiSheaf S} (P : SheafPredicate F) :
    SheafPredicate ((Scheme.zariskiTopology.overMapPullback (Type u) f).obj F) :=
  restrictPredicateAlong (Over.map f) P

/-- Restrict an entire structure along a continuous functor on its relative test category. -/
private def restrictStructureAlong {sig : Signature.{u}} (F : Over S' ⥤ Over S)
    [F.IsContinuous (Scheme.zariskiTopology.over S') (Scheme.zariskiTopology.over S)]
    (A : SheafStructure sig (Scheme.zariskiTopology.over S)) :
    SheafStructure sig (Scheme.zariskiTopology.over S') :=
  let pullback := F.sheafPushforwardContinuous (Type u)
    (Scheme.zariskiTopology.over S') (Scheme.zariskiTopology.over S)
  { carrier := fun s => pullback.obj (A.carrier s)
    total := fun op => pullback.map (A.total op)
    relation := fun r => restrictPredicateAlong F (A.relation r)
    partialDomain := fun p => restrictPredicateAlong F (A.partialDomain p)
    partialValue := fun p => pullback.map (A.partialValue p)
    quantity := fun q => pullback.map (A.quantity q) }

/-- Restrict the carriers and all primitive interpretations along a map of base schemes. -/
def restrictStructure {sig : Signature.{u}} (f : S' ⟶ S)
    (A : SheafStructure sig (Scheme.zariskiTopology.over S)) :
    SheafStructure sig (Scheme.zariskiTopology.over S') :=
  restrictStructureAlong (Over.map f) A

/-- Equal functors on tests induce the same restriction of the whole structure. -/
private theorem restrictStructureAlong_congr {sig : Signature.{u}} {F G : Over S' ⥤ Over S}
    [F.IsContinuous (Scheme.zariskiTopology.over S') (Scheme.zariskiTopology.over S)]
    [G.IsContinuous (Scheme.zariskiTopology.over S') (Scheme.zariskiTopology.over S)]
    (h : F = G) (A : SheafStructure sig (Scheme.zariskiTopology.over S)) :
    restrictStructureAlong F A = restrictStructureAlong G A := by
  subst G
  rfl

/-- Comparing two stages of coefficient change agrees with restricting along their composite. -/
theorem restrictStructure_comp {S'' : Scheme.{u}} {sig : Signature.{u}} (g : S'' ⟶ S') (f : S' ⟶ S)
    (A : SheafStructure sig (Scheme.zariskiTopology.over S)) :
    restrictStructure g (restrictStructure f A) = restrictStructure (g ≫ f) A := by
  letI := Functor.isContinuous_comp (Over.map g) (Over.map f)
    (Scheme.zariskiTopology.over S'') (Scheme.zariskiTopology.over S') (Scheme.zariskiTopology.over S)
  have h := restrictStructureAlong_congr (Over.mapComp_eq g f).symm A
  exact h

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
