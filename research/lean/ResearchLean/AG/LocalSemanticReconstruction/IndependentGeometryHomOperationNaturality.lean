import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomOperationPoints
import Formal.Util.AssertStandardAxioms

/-!
# Operation naturality from common primitive action points

The local square compares the two endpoint graph pairs, the directed
operation graph, an input Atom pair, and two primitive operation-action
responses. Its output is one Atom graph point. These rules recover exactly
the native action square, hence the original configuration-hom equality.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.OperationNatural

noncomputable section

universe u v

open IndependentCorePrimitive

variable {U : AtomCarrier.{u}} {mode : Mode}

/-- Operation naturality compares only endpoint, operation, and Atom points with primitive action responses. -/
def PointLaws (s t : Operations.Table U) (h : Table.{u, v} U mode) : Prop :=
  ∀ (A B A' B' : ArchitectureObject U) (K L : Type u) (op : K) (op' : L) (a b ax bx : U.Atom),
    h (.object A A') = true → h (.object B B') = true →
    h (.operation A B A' B' (.edge K L op op')) = true → h (.atom .forward a b) = true →
    (s (.action A B K op a)).down = some ax → (t (.action A' B' L op' b)).down = some bx →
    h (.atom .forward ax bx) = true

variable (s t : Operations.Table U) (hs : Operations.IsTyped s) (ht : Operations.IsTyped t)
variable (h : Table.{u, v} U mode) (hm : CoreLaws.ObjectRows h)
variable (ha : Atom.IsLawful (Atom.upper h))
variable (ho : Operation.IsLawful h (Operations.carrier s) (Operations.carrier t))

/-- The native operation action square for the maps independently reconstructed from common rows. -/
def NativeSquare : Prop :=
  ∀ (A B : ArchitectureObject U) (op : Operations.carrier s A B) (a : U.Atom),
    Operations.action t ht (Operation.assemble h hm (Operations.carrier s) (Operations.carrier t) ho A B op)
      (Atom.assemble (Atom.upper h) ha a) =
      Atom.assemble (Atom.upper h) ha (Operations.action s hs op a)

/-- Primitive action squares imply native operation naturality at every operation and Atom. -/
theorem nativeSquare_of_points (hp : PointLaws s t h) : NativeSquare s t hs ht h hm ha ho := by
  intro A B op a
  symm
  apply Atom.assemble_eq_of_edge (Atom.upper h) ha
  exact hp A B (CoreLaws.objectMap h hm A) (CoreLaws.objectMap h hm B) _ _ op
    (Operation.assemble h hm (Operations.carrier s) (Operations.carrier t) ho A B op)
    a (Atom.assemble (Atom.upper h) ha a) _ _
    ((CoreLaws.objectGraph h hm).edge_target A) ((CoreLaws.objectGraph h hm).edge_target B)
    (Operation.Point.assemble_point h (Operations.carrier s) (Operations.carrier t) ho hm A B op)
    (Atom.edge_assemble (Atom.upper h) ha a) (Option.some_get _).symm (Option.some_get _).symm

/-- Native operation naturality recovers all candidate endpoint/carrier action-square instances. -/
theorem points_of_nativeSquare (hp : NativeSquare s t hs ht h hm ha ho) : PointLaws s t h := by
  intro A B A' B' K L op op' a b ax bx hAA hBB hopp hab hx hy
  have hK := (hs A B K op a).1 (by simp [hx])
  have hL := (ht A' B' L op' b).1 (by simp [hy])
  subst K L
  have hA := (CoreLaws.objectGraph h hm).target_eq_of_edge hAA
  have hB := (CoreLaws.objectGraph h hm).target_eq_of_edge hBB
  subst A' B'
  have hop : Operation.assemble h hm (Operations.carrier s) (Operations.carrier t) ho A B op = op' :=
    (Operation.Point.assemble_eq_atPair h (Operations.carrier s) (Operations.carrier t) ho hm A B op).trans
      ((Operation.Point.forward_iff h (Operations.carrier s) (Operations.carrier t) ho (A, B) _
        (Operation.Point.endpoints_point h hm A B) op op').1 hopp)
  have hb := Atom.assemble_eq_of_edge (Atom.upper h) ha hab
  subst op' b
  have hx' : Operations.action s hs op a = ax := Option.some.inj ((Option.some_get _).trans hx)
  have hy' : Operations.action t ht _ _ = bx := Option.some.inj ((Option.some_get _).trans hy)
  have he : Atom.assemble (Atom.upper h) ha ax = bx :=
    (congrArg (Atom.assemble (Atom.upper h) ha) hx').symm.trans ((hp A B op a).symm.trans hy')
  exact ((Atom.graph (Atom.upper h) ha .forward).edge_eq_true_iff_target_eq ax bx).2 he

/-- Primitive operation point laws and native action naturality are exactly equivalent. -/
theorem points_iff_nativeSquare : PointLaws s t h ↔ NativeSquare s t hs ht h hm ha ho :=
  ⟨nativeSquare_of_points s t hs ht h hm ha ho, points_of_nativeSquare s t hs ht h hm ha ho⟩

variable (hls : Operations.IsLawful s hs) (hlt : Operations.IsLawful t ht)
variable (configurationMap : ∀ A : ArchitectureObject U,
  ConfigurationHom A.configuration (CoreLaws.objectMap h hm A).configuration)
variable (hconfig : ∀ A, (configurationMap A).atomMap = Atom.assemble (Atom.upper h) ha)

include hconfig in
/-- Equality of the complete configuration-hom square is derived from the primitive Atom-action square. -/
theorem native_configuration_square_iff :
    (∀ (A B : ArchitectureObject U) (op : Operations.carrier s A B),
      ConfigurationHom.comp
          ((Operations.assemble t ht hlt).configurationMap
            (Operation.assemble h hm (Operations.carrier s) (Operations.carrier t) ho A B op))
          (configurationMap A) =
        ConfigurationHom.comp (configurationMap B) ((Operations.assemble s hs hls).configurationMap op)) ↔
      NativeSquare s t hs ht h hm ha ho := by
  constructor
  · intro hp A B op a
    have he := congrArg (fun f => f.atomMap a) (hp A B op)
    change Operations.action t ht _ ((configurationMap A).atomMap a) =
      (configurationMap B).atomMap (Operations.action s hs op a) at he
    rw [hconfig A, hconfig B] at he
    exact he
  · intro hp A B op
    apply ConfigurationHom.ext
    funext a
    change Operations.action t ht _ ((configurationMap A).atomMap a) =
      (configurationMap B).atomMap (Operations.action s hs op a)
    rw [hconfig A, hconfig B]
    exact hp A B op a

end

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.OperationNatural

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.OperationNatural
