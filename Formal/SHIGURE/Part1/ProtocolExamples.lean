import Formal.SHIGURE.Part1.ProtocolGenerated
import Mathlib.Algebra.Order.Ring.Int

/-! # Path equations and Example 2.13

A loop equation identifies a generating edge with an empty path and excludes
the Boolean flip. The three-stage example constructs the actual integer
protocols and their noninjective map on the free path category.
-/

namespace SHIGURE.Protocol

open CategoryTheory

namespace LoopEquation

/-- The vertex of a single-loop presentation. -/
inductive Vertex
  | only

/-- Its one generating loop. -/
inductive Link : Vertex → Vertex → Type
  | tick : Link .only .only

/-- The generator quiver of the loop equation. -/
instance quiver : Quiver Vertex := ⟨Link⟩

/-- Identify the one-edge loop with the empty path. -/
def relations : HomRel (Paths Vertex) := fun {_ _} p q => Quiver.Path.length p = 1 ∧ Quiver.Path.length q = 0

/-- The observation functor of the loop quotient has a single value. -/
def observable : Generated.Execution relations ⥤ Type := (Functor.const _).obj Unit

/-- An action of the generator with Boolean states and constant readout. -/
def action (step : Bool → Bool) : Action (Generated.observations observable) where
  state _ := Bool
  step _ := step
  observe _ _ := ()

/-- Identity generators act by the identity on every path. -/
theorem path_identity {i j : Vertex} (p : Quiver.Path i j) (x : Bool) :
    Generated.pathValue (action id) p x = x := by
  induction p with
  | nil => rfl
  | cons p e ih => simpa only [Generated.pathValue_cons] using ih

/-- The identity generator satisfies the path Law and the observation Law. -/
def lawful : Generated.Actions observable :=
  ⟨action id, fun name => match name with
  | .relation p q _ => (Generated.relationLaw_holds_iff (action id) p q).2
      fun x => (path_identity p x).trans (path_identity q x).symm
  | .naturality e => (observationLaw_holds_iff (action id) e).2 fun _ => rfl⟩

/-- The designated pair consists of a genuine one-edge path and the empty path. -/
theorem tick_related : relations (Quiver.Hom.toPath Link.tick) (Quiver.Path.nil : Quiver.Path Vertex.only Vertex.only) :=
  ⟨rfl, rfl⟩

/-- The two representatives are distinct paths with equal execution in the quotient. -/
theorem quotient_tick :
    (Quiver.Hom.toPath Link.tick) ≠ (Quiver.Path.nil : Quiver.Path Vertex.only Vertex.only) ∧
    (CategoryTheory.Quotient.functor relations).map (Quiver.Hom.toPath Link.tick) =
      (CategoryTheory.Quotient.functor relations).map (Quiver.Path.nil : Quiver.Path Vertex.only Vertex.only) := by
  refine ⟨?_, CategoryTheory.Quotient.sound relations tick_related⟩
  intro same
  have lengths : 1 = 0 := congrArg Quiver.Path.length same
  cases lengths

/-- The Boolean flip has the same constant observation square. -/
theorem flip_observes : (observationLaw (V := Vertex) Link.tick).Holds (action Bool.not).toStructure :=
  (observationLaw_holds_iff (action Bool.not) Link.tick).2 fun _ => rfl

/-- The Boolean flip fails the stated path Law at `false`. -/
theorem flip_fails_relation :
    ¬ (Generated.relationLaw (Quiver.Hom.toPath Link.tick) Quiver.Path.nil).Holds (action Bool.not).toStructure := by
  intro holds
  have unequal : true = false :=
    (Generated.relationLaw_holds_iff (action Bool.not) (Quiver.Hom.toPath Link.tick) Quiver.Path.nil).1 holds false
  cases unequal

/-- The lawful action really recovers a protocol on the path quotient. -/
def protocol : Protocol observable := Generated.toProtocol lawful

/-- Its state action on the collapsed generator is the identity. -/
theorem recovered_tick (x : Bool) : protocol.left.map ((Generated.edges relations).map Link.tick) x = x :=
  Generated.stateFunctor_map_edge lawful Link.tick x

end LoopEquation

namespace IntegerPaths

/-- The three stages of Example 2.13. -/
inductive Stage
  | zero
  | one
  | two

/-- The two edges of the example. -/
inductive Link : Stage → Stage → Type
  | e : Link .zero .one
  | f : Link .one .two

/-- The example uses the free category on these generators. -/
instance quiver : Quiver Stage := ⟨Link⟩

/-- The pair-valued state functions on the two edges. -/
def pairEdges : Stage ⥤q Type where
  obj _ := ℤ × ℤ
  map edge := match edge with
    | .e => fun a => (a.1 + 1, a.2)
    | .f => fun a => (2 * a.1, a.2 + 1)

/-- The observation and scalar state functions on the two edges. -/
def integerEdges : Stage ⥤q Type where
  obj _ := ℤ
  map edge := match edge with
    | .e => fun a => a + 1
    | .f => fun a => 2 * a

/-- The state functor `X` on the actual free execution category. -/
def pairs : Paths Stage ⥤ Type := Paths.lift pairEdges

/-- Both the state functor `Y` and observation `O` use the scalar actions. -/
def integers : Paths Stage ⥤ Type := Paths.lift integerEdges

/-- Forgetting the second coordinate commutes with every path. -/
theorem project_path {i j : Stage} (p : Quiver.Path i j) (x : ℤ × ℤ) :
    (pairs.map p x).1 = integers.map p x.1 := by
  induction p with
  | nil => rfl
  | cons p edge ih =>
    cases edge with
    | e => exact congrArg (fun a : ℤ => a + 1) ih
    | f => exact congrArg (fun a : ℤ => 2 * a) ih

/-- The projection gives the natural readout of `X` and the state component of its arrow to `Y`. -/
def projection : pairs ⟶ integers where
  app _ x := x.1
  naturality := fun {_ _} p => funext (project_path p)

/-- The pair-valued protocol observes the first coordinate. -/
def X : Protocol integers := Over.mk projection

/-- The scalar protocol observes the scalar itself. -/
def Y : Protocol integers := Over.mk (𝟙 integers)

/-- The protocol arrow forgets the second state coordinate. -/
def forgetSecond : X ⟶ Y := Over.homMk projection (Category.comp_id _)

/-- At every stage the protocol map identifies two distinct points. -/
theorem not_injective (i : Stage) : ¬ Function.Injective (forgetSecond.left.app ((Paths.of Stage).obj i)) := by
  intro injective
  have same : ((0, 0) : ℤ × ℤ) = (0, 1) := injective rfl
  have values : (0 : ℤ) = 1 := congrArg Prod.snd same
  exact zero_ne_one values

/-- The empty path leaves both kinds of states unchanged. -/
theorem empty_path (i : Stage) (a b : ℤ) :
    pairs.map (Quiver.Path.nil : Quiver.Path i i) (a, b) = (a, b) ∧
    integers.map (Quiver.Path.nil : Quiver.Path i i) a = a := ⟨rfl, rfl⟩

/-- At `e` the state and observation first coordinates advance by one. -/
theorem e_path (a b : ℤ) :
    pairs.map (Quiver.Hom.toPath Link.e) (a, b) = (a + 1, b) ∧
    integers.map (Quiver.Hom.toPath Link.e) a = a + 1 := ⟨rfl, rfl⟩

/-- At `f` both first coordinates double and the second state coordinate advances by one. -/
theorem f_path (a b : ℤ) :
    pairs.map (Quiver.Hom.toPath Link.f) (a, b) = (2 * a, b + 1) ∧
    integers.map (Quiver.Hom.toPath Link.f) a = 2 * a := ⟨rfl, rfl⟩

/-- The actual path `e` followed by `f`. -/
def ef : Quiver.Path Stage.zero Stage.two := (Quiver.Hom.toPath Link.e).cons Link.f

/-- The two-edge path is the composite of the two generating arrows. -/
theorem ef_eq_comp : ef = ((Paths.of Stage).map Link.e ≫ (Paths.of Stage).map Link.f) :=
  rfl

/-- The length-two path acts by both updates in order. -/
theorem ef_path (a b : ℤ) :
    pairs.map ef (a, b) = (2 * a + 2, b + 1) ∧ integers.map ef a = 2 * a + 2 := by
  constructor
  · simp only [ef_eq_comp, FunctorToTypes.map_comp_apply, Paths.of_map, (e_path a b).1,
      (f_path (a + 1) b).1, mul_add, mul_one]
  · simp only [ef_eq_comp, FunctorToTypes.map_comp_apply, Paths.of_map, (e_path a b).2,
      (f_path (a + 1) b).2, mul_add, mul_one]

/-- Evaluation followed by readout agrees after applying the protocol arrow, for every path. -/
theorem observe_all_paths {i j : Stage} (p : Quiver.Path i j) (a b : ℤ) :
    Y.hom.app ((Paths.of Stage).obj j)
        (Y.left.map p (forgetSecond.left.app ((Paths.of Stage).obj i) (a, b))) =
      X.hom.app ((Paths.of Stage).obj j) (X.left.map p (a, b)) :=
  (project_path p (a, b)).symm

/-- Both observed values on `ef` are exactly `2*a+2`. -/
theorem observe_ef (a b : ℤ) :
    Y.hom.app ((Paths.of Stage).obj .two)
        (Y.left.map ef (forgetSecond.left.app ((Paths.of Stage).obj .zero) (a, b))) = 2 * a + 2 ∧
    X.hom.app ((Paths.of Stage).obj .two) (X.left.map ef (a, b)) = 2 * a + 2 :=
  ⟨(ef_path a b).2, congrArg Prod.fst (ef_path a b).1⟩

end IntegerPaths
end SHIGURE.Protocol
