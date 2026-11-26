import Formal.SHIGURE.Part2.Recovery.SheafObjectDescent

/-!
# Descent of typed tuples

Restriction and the overlap maps of tuples are coordinatewise. Gluing
commutes with these products because the chart comparisons determine
each coordinate on an open cover.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

noncomputable section

namespace SHIGURE.Copying.SheafCharts

variable {S : Scheme.{u}} {C : Scheme.OpenCover.{u} S} {K : Type u}
variable (D : K → SheafCharts C) (Γ : List K)

/-- The chart data of a tuple of carriers, with its coordinatewise transitions. -/
def tuples : SheafCharts C where
  chart i := sheafTuple (fun s => (D s).chart i) Γ
  transition i j :=
    ⟨sheafTupleMap (fun s => ((D s).transition i j).hom) Γ,
      sheafTupleMap (fun s => ((D s).transition i j).inv) Γ,
      by
        rw [← sheafTupleMap_comp]
        simp only [Iso.hom_inv_id, sheafTupleMap_id]
        rfl,
      by
        rw [← sheafTupleMap_comp]
        simp only [Iso.inv_hom_id, sheafTupleMap_id]
        rfl⟩

/-- A transition on a common test applies to each coordinate of a tuple. -/
theorem tuples_transition_get {i j : C.I₀} {T : Over S} (a : CoverLift C i T) (b : CoverLift C j T)
    (x : ((tuples D Γ).chart i).val.obj (op a.test)) {s : K} (v : Var Γ s) :
    (((tuples D Γ).transitionAt a b x).get v) = (D s).transitionAt a b (x.get v) :=
  rfl

/-- The unit and cocycle conditions for the carrier transitions give those for all tuples. -/
theorem tuples_coherent (hD : ∀ s, (D s).Coherent) : (tuples D Γ).Coherent where
  unit a x := by
    apply Assignment.ext
    intro s v
    exact (hD s).unit a (x.get v)
  cocycle a b c x := by
    apply Assignment.ext
    intro s v
    exact (hD s).cocycle a b c (x.get v)

/-- Projection to a typed variable is a compatible family of maps on the charts. -/
def tupleProjection {s : K} (v : Var Γ s) : (tuples D Γ).Arrow (D s) where
  onChart i := sheafTupleProj (fun t => (D t).chart i) v
  commute _ _ _ := rfl

/-- A matching tuple gives its matching sections in each coordinate. -/
def tupleComparison : (tuples D Γ).matchingSheaf ⟶ sheafTuple (fun s => (D s).matchingSheaf) Γ :=
  ⟨{ app := fun T => ↾fun x => ⟨fun {s} v => (tupleProjection D Γ v).glue.val.app T x⟩
     naturality := by
       intro T U f
       ext x
       apply Assignment.ext
       intro s v
       exact FunctorToTypes.naturality _ _ (tupleProjection D Γ v).glue.val f x }⟩

/-- On each chart the tuple comparison reads exactly the componentwise chart maps. -/
theorem tupleComparison_readChart {i : C.I₀} {T : Over S} (a : CoverLift C i T)
    (x : (tuples D Γ).matchingSheaf.val.obj (op T)) {s : K} (v : Var Γ s) :
    (D s).readChart a (((tupleComparison D Γ).val.app (op T) x).get v) = ((tuples D Γ).readChart a x).get v :=
  (tupleProjection D Γ v).glue_readChart a x

set_option maxHeartbeats 800000 in
/-- The tuple comparison is a canonical isomorphism with the tuple of the glued carriers. -/
def tupleComparisonIso (hD : ∀ s, (D s).Coherent) :
    (tuples D Γ).matchingSheaf ≅ sheafTuple (fun s => (D s).matchingSheaf) Γ := by
  let f := tupleComparison D Γ
  have hf : IsIso f := coefficientCover_isIso C f (by
    intro i V
    let T := (Over.map (C.f i)).obj V
    let a := CoverLift.ofTest V
    change Function.Bijective (fun x : (tuples D Γ).matchingSheaf.val.obj (op T) => (tupleComparison D Γ).val.app (op T) x)
    have ht := (tuples D Γ).readChart_bijective (tuples_coherent D Γ hD) a
    constructor
    · intro x y eq
      apply ht.1
      apply Assignment.ext
      intro s v
      have h := congrArg (fun ts : Assignment (fun t => (D t).matchingSheaf.val.obj (op T)) Γ => ts.get v) eq
      exact (tupleComparison_readChart D Γ a x v).symm.trans
        ((congrArg ((D s).readChart a) h).trans (tupleComparison_readChart D Γ a y v))
    · intro y
      let z : ((tuples D Γ).chart i).val.obj (op a.test) :=
        ⟨fun {s} v => (D s).readChart a (y.get v)⟩
      obtain ⟨x, hx⟩ := ht.2 z
      refine ⟨x, ?_⟩
      apply Assignment.ext
      intro s v
      apply ((D s).readChart_bijective (hD s) a).1
      exact (tupleComparison_readChart D Γ a x v).trans
        (congrArg (fun ts : ((tuples D Γ).chart i).val.obj (op a.test) => ts.get v) hx))
  exact asIso f

end SHIGURE.Copying.SheafCharts
