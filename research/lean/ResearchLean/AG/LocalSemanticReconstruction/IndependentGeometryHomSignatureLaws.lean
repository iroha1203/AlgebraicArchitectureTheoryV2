import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomSignatureReadings
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomCoreLaws
import Formal.Util.AssertStandardAxioms

/-!
# Signature preservation from common primitive Hom points

Selected-axis status is compared at each true directed axis pair. Object
coordinates are compared at true object and axis pairs using their primitive
source and target responses. The resulting rules are equivalent to the
native selected-axis and coordinate equations for the reconstructed maps.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.SignatureLaws

noncomputable section

universe u v

variable {U : AtomCarrier.{u}} {mode : Mode}

/-- Selected status is preserved and reflected at each primitive directed axis pair. -/
def SelectedPoints (s t : IndependentInvariantSignaturePrimitive.Signature.Table U) (h : Table.{u, v} U mode) : Prop :=
  ∀ (I J : Type u) (i : I) (j : J),
    h (.signatureAxis (.edge I J i j)) = true →
      ((s (.selected I i)).down ↔ (t (.selected J j)).down)

/-- Coordinate preservation compares primitive point responses over the actual object and axis graphs. -/
def CoordinatePoints (s t : IndependentInvariantSignaturePrimitive.Signature.Table U) (h : Table.{u, v} U mode) : Prop :=
  ∀ (M N : ArchitectureObject U) (I J K L : Type u) (i : I) (j : J) (x : K) (y : L),
    h (.object M N) = true → h (.signatureAxis (.edge I J i j)) = true →
    (s (.coordinate I i K M)).down = some x → (t (.coordinate J j L N)).down = some y →
    h (.signatureCoordinate .forward I J i j (.edge K L x y)) = true

variable (s t : IndependentInvariantSignaturePrimitive.Signature.Table U)
variable (hs : IndependentInvariantSignaturePrimitive.Signature.IsTyped s)
variable (ht : IndependentInvariantSignaturePrimitive.Signature.IsTyped t)
variable (h : Table.{u, v} U mode)
variable (ha : IndependentCarrierGraph.IsLawful
  (IndependentInvariantSignaturePrimitive.Signature.axis s) (IndependentInvariantSignaturePrimitive.Signature.axis t)
  (signatureAxis h))

include ha in
/-- A true axis pair activates exactly the two selected native axis carriers. -/
theorem axis_carriers (I J : Type u) (i : I) (j : J)
    (hp : h (.signatureAxis (.edge I J i j)) = true) :
    I = IndependentInvariantSignaturePrimitive.Signature.axis s ∧
      J = IndependentInvariantSignaturePrimitive.Signature.axis t := by
  classical
  by_contra hn
  exact Bool.noConfusion ((ha.1 I J i j (not_and_or.mp hn)).symm.trans hp)

/-- Primitive selected-status rules give the native selected-axis equivalence. -/
theorem selected_of_points (hp : SelectedPoints s t h)
    (i : IndependentInvariantSignaturePrimitive.Signature.axis s) :
    (s (.selected _ i)).down ↔ (t (.selected _ (Signature.axisMap h _ _ ha i))).down :=
  hp _ _ i _ ((Signature.axis_forward_iff h _ _ ha i _).2 rfl)

/-- Native selected-status preservation gives every primitive candidate-axis instance. -/
theorem selected_points_of_native
    (hp : ∀ i, (s (.selected _ i)).down ↔ (t (.selected _ (Signature.axisMap h _ _ ha i))).down) :
    SelectedPoints s t h := by
  intro I J i j hij
  obtain ⟨rfl, rfl⟩ := axis_carriers s t h ha I J i j hij
  have he := (Signature.axis_forward_iff h _ _ ha i j).1 hij
  subst j
  exact hp i

/-- Primitive selected-axis conditions are equivalent to the complete native selected-status field. -/
theorem selected_points_iff : SelectedPoints s t h ↔
    ∀ i, (s (.selected _ i)).down ↔ (t (.selected _ (Signature.axisMap h _ _ ha i))).down :=
  ⟨selected_of_points s t h ha, selected_points_of_native s t h ha⟩

variable (hm : CoreLaws.ObjectRows h)
variable (hc : Signature.IsLawful h
  (IndependentInvariantSignaturePrimitive.Signature.axis s) (IndependentInvariantSignaturePrimitive.Signature.axis t)
  (IndependentInvariantSignaturePrimitive.Signature.coordinateType s hs)
  (IndependentInvariantSignaturePrimitive.Signature.coordinateType t ht))

/-- The native coordinate field evaluated on the reconstructed object, axis, and coordinate maps. -/
def NativeCoordinates : Prop :=
  ∀ (M : ArchitectureObject U) (i : IndependentInvariantSignaturePrimitive.Signature.axis s),
    Signature.assemble h _ _ ha _ _ hc i (IndependentInvariantSignaturePrimitive.Signature.coordinate s hs M i) =
      IndependentInvariantSignaturePrimitive.Signature.coordinate t ht (CoreLaws.objectMap h hm M)
        (Signature.axisMap h _ _ ha i)

/-- Primitive coordinate points construct the native coordinate-preservation equation at every object and axis. -/
theorem nativeCoordinates_of_points (hp : CoordinatePoints s t h) :
    NativeCoordinates s t hs ht h ha hm hc := by
  intro M i
  rw [Signature.assemble_eq_atPair]
  apply (Signature.atPair_forward_iff h _ _ _ _ hc i _
    ((Signature.axis_forward_iff h _ _ ha i _).2 rfl) _ _).1
  exact hp M (CoreLaws.objectMap h hm M) _ _ _ _ i (Signature.axisMap h _ _ ha i) _ _
    ((CoreLaws.objectGraph h hm).edge_target M) ((Signature.axis_forward_iff h _ _ ha i _).2 rfl)
    (Option.some_get _).symm (Option.some_get _).symm

/-- Native coordinate preservation recovers every primitive candidate-carrier coordinate condition. -/
theorem coordinate_points_of_native (hp : NativeCoordinates s t hs ht h ha hm hc) :
    CoordinatePoints s t h := by
  intro M N I J K L i j x y hMN hij hx hy
  obtain ⟨rfl, rfl⟩ := axis_carriers s t h ha I J i j hij
  have hk := (hs.coordinate _ i K M).1 (by simp [hx])
  have hl := (ht.coordinate _ j L N).1 (by simp [hy])
  have hk' := Option.some.inj
    ((IndependentInvariantSignaturePrimitive.Signature.coordinateType_some s hs i).symm.trans hk)
  have hl' := Option.some.inj
    ((IndependentInvariantSignaturePrimitive.Signature.coordinateType_some t ht j).symm.trans hl)
  subst K L
  have hn := (CoreLaws.objectGraph h hm).target_eq_of_edge hMN
  have hj := (Signature.axis_forward_iff h _ _ ha i j).1 hij
  subst N j
  have hx' : IndependentInvariantSignaturePrimitive.Signature.coordinate s hs M i = x :=
    Option.some.inj ((Option.some_get _).trans hx)
  have hy' : IndependentInvariantSignaturePrimitive.Signature.coordinate t ht _ _ = y :=
    Option.some.inj ((Option.some_get _).trans hy)
  have hh := hp M i
  rw [Signature.assemble_eq_atPair] at hh
  apply (Signature.atPair_forward_iff h _ _ _ _ hc i _ hij x y).2
  exact (congrArg (Signature.atPair h _ _ _ _ hc i _ hij) hx').symm.trans (hh.trans hy')

/-- Primitive coordinate point preservation is exactly the complete native coordinate equation. -/
theorem coordinate_points_iff : CoordinatePoints s t h ↔ NativeCoordinates s t hs ht h ha hm hc :=
  ⟨nativeCoordinates_of_points s t hs ht h ha hm hc,
    coordinate_points_of_native s t hs ht h ha hm hc⟩

end

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.SignatureLaws

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.SignatureLaws
