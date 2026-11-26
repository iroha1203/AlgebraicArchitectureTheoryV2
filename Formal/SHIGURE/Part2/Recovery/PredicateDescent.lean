import Formal.SHIGURE.Part2.Recovery.TupleDescent
import Mathlib.CategoryTheory.Subfunctor.Image

/-!
# Descent of subsheaves of tuples

The local inclusions commute with the tuple transitions. Their glued
map is injective on sections, so its range retains the domain sheaf
and gives an actual subsheaf of the global tuples.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

noncomputable section

namespace SHIGURE.SheafPredicate

variable {S : Scheme.{u}} {F G : Copying.ZariskiSheaf S}

private def rangePresheafIso (f : F ⟶ G) (h : ∀ T, Function.Injective (f.val.app T)) :
    F.val ≅ (Subfunctor.range f.val).toFunctor := by
  haveI : Mono f.val := (NatTrans.mono_iff_mono_app _).mpr fun T => (mono_iff_injective _).mpr (h T)
  exact asIso (Subfunctor.toRange f.val)

/-- The range of an injective sheaf morphism is a subsheaf of the target. -/
def ofInjection (f : F ⟶ G) (h : ∀ T, Function.Injective (f.val.app T)) : SheafPredicate G where
  carrier := Subfunctor.range f.val
  isSheaf := (isSheaf_iff_isSheaf_of_type _ _).mp
    ((Presheaf.isSheaf_of_iso_iff (rangePresheafIso f h)).mp F.cond)

/-- An injective morphism identifies its source sheaf with the range subsheaf. -/
def ofInjectionIso (f : F ⟶ G) (h : ∀ T, Function.Injective (f.val.app T)) : F ≅ (ofInjection f h).toSheaf :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso (rangePresheafIso f h)

@[simp]
theorem ofInjectionIso_inclusion (f : F ⟶ G) (h : ∀ T, Function.Injective (f.val.app T)) :
    (ofInjectionIso f h).hom ≫ (ofInjection f h).inclusion = f := rfl

end SHIGURE.SheafPredicate

namespace SHIGURE.Copying.SheafCharts

variable {S : Scheme.{u}} {C : Scheme.OpenCover.{u} S} {K : Type u}
variable (D : K → SheafCharts C) (Γ : List K)
variable (P : ∀ i, SheafPredicate ((tuples D Γ).chart i))

/-- The two maps of the overlap isomorphism preserve the prescribed subsheaves. -/
structure PreservesPredicates : Prop where
  /-- The forward map takes sections of the first subsheaf into the second. -/
  hom (i j : C.I₀) :
    (restrictPredicate (pullback.fst (C.f i) (C.f j)) (P i)).carrier ≤
      ((restrictPredicate (pullback.snd (C.f i) (C.f j)) (P j)).preimage ((tuples D Γ).transition i j).hom).carrier
  /-- The inverse does the same in the opposite direction. -/
  inv (i j : C.I₀) :
    (restrictPredicate (pullback.snd (C.f i) (C.f j)) (P j)).carrier ≤
      ((restrictPredicate (pullback.fst (C.f i) (C.f j)) (P i)).preimage ((tuples D Γ).transition i j).inv).carrier

variable {D Γ P}

/-- The local subobjects glue with the restrictions of the tuple isomorphisms. -/
def predicateCharts (h : PreservesPredicates D Γ P) : SheafCharts C where
  chart i := (P i).toSheaf
  transition i j :=
    ⟨SheafPredicate.mapAlong ((tuples D Γ).transition i j).hom (h.hom i j),
      SheafPredicate.mapAlong ((tuples D Γ).transition i j).inv (h.inv i j),
      by
        ext U x
        apply Subtype.ext
        exact congrArg (fun f => f.val.app U x.val) ((tuples D Γ).transition i j).hom_inv_id,
      by
        ext U x
        apply Subtype.ext
        exact congrArg (fun f => f.val.app U x.val) ((tuples D Γ).transition i j).inv_hom_id⟩

/-- The local inclusions commute with the transition on every common relative test. -/
def predicateInclusion (h : PreservesPredicates D Γ P) : (predicateCharts h).Arrow (tuples D Γ) where
  onChart i := (P i).inclusion
  commute _ _ _ := rfl

/-- The unit and the cocycle descend to the chosen subsheaves. -/
theorem predicateCharts_coherent (h : PreservesPredicates D Γ P) (hD : ∀ s, (D s).Coherent) :
    (predicateCharts h).Coherent where
  unit a x := Subtype.ext ((tuples_coherent D Γ hD).unit a x.val)
  cocycle a b c x := Subtype.ext ((tuples_coherent D Γ hD).cocycle a b c x.val)

/-- The sectionwise inclusion of the glued predicate into the global tuple sheaf. -/
def gluedPredicateMap (h : PreservesPredicates D Γ P) :
    (predicateCharts h).matchingSheaf ⟶ sheafTuple (fun s => (D s).matchingSheaf) Γ :=
  (predicateInclusion h).glue ≫ tupleComparison D Γ

private theorem gluedPredicateMap_injective (h : PreservesPredicates D Γ P) (hD : ∀ s, (D s).Coherent)
    (T : (Over S)ᵒᵖ) : Function.Injective ((gluedPredicateMap h).val.app T) := by
  have hinj := (predicateInclusion h).glue_injective (fun _ _ => Subtype.val_injective) T.unop
  have htuple : Function.Injective ((tupleComparison D Γ).val.app T) :=
    ((sheafToPresheaf _ _).mapIso (tupleComparisonIso D Γ hD)).app T |>.toEquiv.injective
  exact htuple.comp hinj

/-- The glued subsheaf of the global tuple sheaf. -/
def gluedPredicate (h : PreservesPredicates D Γ P) (hD : ∀ s, (D s).Coherent) :
    SheafPredicate (sheafTuple (fun s => (D s).matchingSheaf) Γ) :=
  SheafPredicate.ofInjection (gluedPredicateMap h) (gluedPredicateMap_injective h hD)

/-- The glued predicate sheaf is identified with the sheaf of matching sections of the local predicates. -/
def gluedPredicateIso (h : PreservesPredicates D Γ P) (hD : ∀ s, (D s).Coherent) :
    (predicateCharts h).matchingSheaf ≅ (gluedPredicate h hD).toSheaf :=
  SheafPredicate.ofInjectionIso (gluedPredicateMap h) (gluedPredicateMap_injective h hD)

/-- On a common relative test, the global inclusion reads as the original chart inclusion. -/
theorem gluedPredicateMap_readChart (h : PreservesPredicates D Γ P) {i : C.I₀} {T : Over S}
    (a : CoverLift C i T) (x : (predicateCharts h).matchingSheaf.val.obj (op T)) {s : K} (v : Var Γ s) :
    (D s).readChart a (((gluedPredicateMap h).val.app (op T) x).get v) =
      (((predicateCharts h).readChart a x).val.get v) := by
  change (D s).readChart a (((tupleComparison D Γ).val.app (op T)
    ((predicateInclusion h).glue.val.app (op T) x)).get v) = _
  rw [tupleComparison_readChart, Arrow.glue_readChart]
  rfl

/-- A glued tuple belongs to the global predicate on a chart exactly when its chart readings belong locally. -/
theorem gluedPredicate_mem_iff (h : PreservesPredicates D Γ P) (hD : ∀ s, (D s).Coherent)
    {i : C.I₀} {T : Over S} (a : CoverLift C i T)
    (x : (sheafTuple (fun s => (D s).matchingSheaf) Γ).val.obj (op T)) :
    x ∈ (gluedPredicate h hD).carrier.obj (op T) ↔
      (show ((tuples D Γ).chart i).val.obj (op a.test) from ⟨fun {s} v => (D s).readChart a (x.get v)⟩) ∈
        (P i).carrier.obj (op a.test) := by
  constructor
  · rintro ⟨y, rfl⟩
    have e : (show ((tuples D Γ).chart i).val.obj (op a.test) from
        ⟨fun {s} v => (D s).readChart a (((gluedPredicateMap h).val.app (op T) y).get v)⟩) =
        ((predicateCharts h).readChart a y).val :=
      Assignment.ext (fun {_} v => gluedPredicateMap_readChart h a y v)
    exact e.symm ▸ ((predicateCharts h).readChart a y).property
  · intro hx
    let y : ((predicateCharts h).chart i).val.obj (op a.test) :=
      ⟨⟨fun {s} v => (D s).readChart a (x.get v)⟩, hx⟩
    obtain ⟨z, hz⟩ := ((predicateCharts h).readChart_bijective (predicateCharts_coherent h hD) a).2 y
    refine ⟨z, ?_⟩
    apply Assignment.ext
    intro s v
    apply ((D s).readChart_bijective (hD s) a).1
    rw [gluedPredicateMap_readChart, hz]

end SHIGURE.Copying.SheafCharts
