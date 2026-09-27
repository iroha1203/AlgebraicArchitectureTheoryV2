import ResearchLean.AG.OperationRepair.Composition

/-!
# Maps between operation repair inputs

The lower and upper congruences are preserved by maps respecting named
operations, observations, and the request relation. Their quotient maps form
the comparison square of GOAL C.
-/

namespace AAT.AG.OperationRepair

universe u u' u'' v w

variable {S : Type u} {S' : Type u'} {S'' : Type u''}
variable {E : Type v} {O : Type w}

/-- A map of two operation/observation/request inputs with the same operation
names and observation type. -/
structure InputHom (T : OperationSystem S E) (observe : S → O)
    (R : S → S → Prop) (T' : OperationSystem S' E)
    (observe' : S' → O) (R' : S' → S' → Prop) where
  map : S → S'
  step_comm : ∀ e x, map (T.step e x) = T'.step e (map x)
  observe_comm : ∀ x, observe' (map x) = observe x
  request_preserve : ∀ x y, R x y → R' (map x) (map y)

namespace InputHom

variable {T : OperationSystem S E} {observe : S → O} {R : S → S → Prop}
variable {T' : OperationSystem S' E} {observe' : S' → O}
variable {R' : S' → S' → Prop}
variable {T'' : OperationSystem S'' E} {observe'' : S'' → O}
variable {R'' : S'' → S'' → Prop}

/-- Identity map of an operation repair input. -/
def id (T : OperationSystem S E) (observe : S → O) (R : S → S → Prop) :
    InputHom T observe R T observe R where
  map := _root_.id
  step_comm := by intro e x; rfl
  observe_comm := by intro x; rfl
  request_preserve := by intro x y h; exact h

/-- Composition of operation repair input maps. -/
def comp (h : InputHom T observe R T' observe' R')
    (k : InputHom T' observe' R' T'' observe'' R'') :
    InputHom T observe R T'' observe'' R'' where
  map := k.map ∘ h.map
  step_comm := by intro e x; simp [Function.comp, h.step_comm, k.step_comm]
  observe_comm := by intro x; simp [Function.comp, h.observe_comm, k.observe_comm]
  request_preserve := by
    intro x y hxy
    exact k.request_preserve _ _ (h.request_preserve x y hxy)

variable (h : InputHom T observe R T' observe' R')

/-- Input maps commute with the action of every word. -/
theorem eval_comm (x : S) (word : List E) :
    h.map (T.eval x word) = T'.eval (h.map x) word := by
  induction word generalizing x with
  | nil => rfl
  | cons e word ih =>
      rw [OperationSystem.eval_cons, OperationSystem.eval_cons,
        ih, h.step_comm]

/-- GOAL C: an input map sends the generated lower congruence to the lower
congruence of the target input. -/
theorem generated_preserve {x y : S}
    (hxy : (generated T R).setoid.r x y) :
    (generated T' R').setoid.r (h.map x) (h.map y) := by
  let pullback : OperationCongruence T :=
    { setoid := Setoid.comap h.map (generated T' R').setoid
      stable := by
        intro e a b hab
        change (generated T' R').setoid.r
          (h.map (T.step e a)) (h.map (T.step e b))
        rw [h.step_comm, h.step_comm]
        exact (generated T' R').stable e (h.map a) (h.map b) hab }
  have hle : generated T R ≤ pullback := by
    apply (generated_le_iff T pullback).mpr
    intro a b hab
    exact generated_contains T' (h.request_preserve a b hab)
  exact hle hxy

/-- GOAL C: an input map preserves future-observation equivalence. -/
theorem behavior_preserve {x y : S}
    (hxy : (behavior T observe).setoid.r x y) :
    (behavior T' observe').setoid.r (h.map x) (h.map y) := by
  apply (behavior_iff T' observe' (h.map x) (h.map y)).mpr
  intro word
  rw [← h.eval_comm x word, ← h.eval_comm y word,
    h.observe_comm, h.observe_comm]
  exact (behavior_iff T observe x y).mp hxy word

/-- The induced map between lower standard quotients. -/
def lowerMap : Quotient (generated T R).setoid →
    Quotient (generated T' R').setoid :=
  fun q => Quotient.liftOn q
    (fun x => Quotient.mk (generated T' R').setoid (h.map x))
    (fun _ _ hxy => Quotient.sound (h.generated_preserve hxy))

/-- The induced map between upper standard quotients. -/
def upperMap : Quotient (behavior T observe).setoid →
    Quotient (behavior T' observe').setoid :=
  fun q => Quotient.liftOn q
    (fun x => Quotient.mk (behavior T' observe').setoid (h.map x))
    (fun _ _ hxy => Quotient.sound (h.behavior_preserve hxy))

@[simp] theorem lowerMap_mk (x : S) :
    h.lowerMap (Quotient.mk (generated T R).setoid x) =
      Quotient.mk (generated T' R').setoid (h.map x) := rfl

@[simp] theorem upperMap_mk (x : S) :
    h.upperMap (Quotient.mk (behavior T observe).setoid x) =
      Quotient.mk (behavior T' observe').setoid (h.map x) := rfl

/-- GOAL C: the induced maps commute with the canonical lower-to-upper
factorization whenever both inputs are repairable. -/
theorem endpoint_square
    (hsource : generated T R ≤ behavior T observe)
    (htarget : generated T' R' ≤ behavior T' observe') :
    h.upperMap ∘ Setoid.map_of_le hsource =
      Setoid.map_of_le htarget ∘ h.lowerMap := by
  funext q
  refine Quotient.inductionOn q ?_
  intro x
  rfl

/-- The induced lower map preserves the descended named operations. -/
theorem lowerMap_step
    (hsource : generated T R ≤ behavior T observe)
    (htarget : generated T' R' ≤ behavior T' observe')
    (e : E) (q : Quotient (generated T R).setoid) :
    h.lowerMap ((lowerRepair T observe R hsource).step e q) =
      (lowerRepair T' observe' R' htarget).step e (h.lowerMap q) := by
  refine Quotient.inductionOn q ?_
  intro x
  change Quotient.mk (generated T' R').setoid (h.map (T.step e x)) =
    Quotient.mk (generated T' R').setoid (T'.step e (h.map x))
  rw [h.step_comm]

/-- The induced lower map preserves the descended observation. -/
theorem lowerMap_observation
    (hsource : generated T R ≤ behavior T observe)
    (htarget : generated T' R' ≤ behavior T' observe')
    (q : Quotient (generated T R).setoid) :
    (lowerRepair T' observe' R' htarget).observation (h.lowerMap q) =
      (lowerRepair T observe R hsource).observation q := by
  refine Quotient.inductionOn q ?_
  intro x
  exact h.observe_comm x

/-- The induced upper map preserves the descended named operations. -/
theorem upperMap_step
    (hsource : generated T R ≤ behavior T observe)
    (htarget : generated T' R' ≤ behavior T' observe')
    (e : E) (q : Quotient (behavior T observe).setoid) :
    h.upperMap ((upperRepair T observe R hsource).step e q) =
      (upperRepair T' observe' R' htarget).step e (h.upperMap q) := by
  refine Quotient.inductionOn q ?_
  intro x
  change Quotient.mk (behavior T' observe').setoid (h.map (T.step e x)) =
    Quotient.mk (behavior T' observe').setoid (T'.step e (h.map x))
  rw [h.step_comm]

/-- The induced upper map preserves the descended observation. -/
theorem upperMap_observation
    (hsource : generated T R ≤ behavior T observe)
    (htarget : generated T' R' ≤ behavior T' observe')
    (q : Quotient (behavior T observe).setoid) :
    (upperRepair T' observe' R' htarget).observation (h.upperMap q) =
      (upperRepair T observe R hsource).observation q := by
  refine Quotient.inductionOn q ?_
  intro x
  exact h.observe_comm x

/-- The lower quotient construction respects identity input maps. -/
theorem lowerMap_id :
    (id T observe R).lowerMap = _root_.id := by
  funext q
  refine Quotient.inductionOn q ?_
  intro x
  rfl

/-- The upper quotient construction respects identity input maps. -/
theorem upperMap_id :
    (id T observe R).upperMap = _root_.id := by
  funext q
  refine Quotient.inductionOn q ?_
  intro x
  rfl

/-- The lower quotient construction respects composition of input maps. -/
theorem lowerMap_comp
    (k : InputHom T' observe' R' T'' observe'' R'') :
    (comp h k).lowerMap = k.lowerMap ∘ h.lowerMap := by
  funext q
  refine Quotient.inductionOn q ?_
  intro x
  rfl

/-- The upper quotient construction respects composition of input maps. -/
theorem upperMap_comp
    (k : InputHom T' observe' R' T'' observe'' R'') :
    (comp h k).upperMap = k.upperMap ∘ h.upperMap := by
  funext q
  refine Quotient.inductionOn q ?_
  intro x
  rfl

end InputHom

/-- An isomorphism of operation repair inputs. -/
structure InputIso (T : OperationSystem S E) (observe : S → O)
    (R : S → S → Prop) (T' : OperationSystem S' E)
    (observe' : S' → O) (R' : S' → S' → Prop) where
  hom : InputHom T observe R T' observe' R'
  inv : InputHom T' observe' R' T observe R
  left_inv : ∀ x, inv.map (hom.map x) = x
  right_inv : ∀ y, hom.map (inv.map y) = y

namespace InputIso

variable {T : OperationSystem S E} {observe : S → O} {R : S → S → Prop}
variable {T' : OperationSystem S' E} {observe' : S' → O}
variable {R' : S' → S' → Prop}

/-- GOAL C: an input isomorphism induces an isomorphism of generated lower
quotients, commuting with the original state maps. -/
def lowerEquiv (iso : InputIso T observe R T' observe' R') :
    Quotient (generated T R).setoid ≃ Quotient (generated T' R').setoid where
  toFun := iso.hom.lowerMap
  invFun := iso.inv.lowerMap
  left_inv := by
    intro q
    refine Quotient.inductionOn q ?_
    intro x
    simp [iso.left_inv]
  right_inv := by
    intro q
    refine Quotient.inductionOn q ?_
    intro x
    simp [iso.right_inv]

/-- GOAL C: an input isomorphism induces an isomorphism of behavioral upper
quotients. -/
def upperEquiv (iso : InputIso T observe R T' observe' R') :
    Quotient (behavior T observe).setoid ≃
      Quotient (behavior T' observe').setoid where
  toFun := iso.hom.upperMap
  invFun := iso.inv.upperMap
  left_inv := by
    intro q
    refine Quotient.inductionOn q ?_
    intro x
    simp [iso.left_inv]
  right_inv := by
    intro q
    refine Quotient.inductionOn q ?_
    intro x
    simp [iso.right_inv]

end InputIso

#assert_standard_axioms_only AAT.AG.OperationRepair

end AAT.AG.OperationRepair
