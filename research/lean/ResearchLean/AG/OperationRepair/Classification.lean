import ResearchLean.AG.OperationRepair.Endpoints
import Mathlib.Data.Fintype.EquivFin

/-!
# Repair quotients and their kernels

This module constructs the two directions underlying GOAL B's classification:
every repair quotient gives a congruence between the endpoints, and every
congruence in that interval gives an actual repair quotient.
-/

namespace AAT.AG.OperationRepair

universe u v w z z' z''

variable {S : Type u} {E : Type v} {O : Type w}
variable (T : OperationSystem S E) (observe : S → O) (R : S → S → Prop)

/-- A surjective repair quotient with descended operations and observation.
The equations are the object condition in GOAL B, not an assumption in the
construction from a congruence below. -/
structure RepairQuotient where
  Target : Type z
  read : S → Target
  surjective : Function.Surjective read
  step : E → Target → Target
  observation : Target → O
  step_comm : ∀ e x, read (T.step e x) = step e (read x)
  observation_comm : ∀ x, observation (read x) = observe x
  identifies : ∀ x y, R x y → read x = read y

namespace RepairQuotient

variable {T : OperationSystem S E} {observe : S → O} {R : S → S → Prop}

/-- The kernel of a repair quotient is stable under every operation. -/
def kernel (q : RepairQuotient T observe R) : OperationCongruence T where
  setoid := Setoid.ker q.read
  stable := by
    intro e x y h
    change q.read (T.step e x) = q.read (T.step e y)
    rw [q.step_comm, q.step_comm, h]

/-- Every repair quotient kernel contains the generated lower endpoint. -/
theorem generated_le_kernel (q : RepairQuotient T observe R) :
    generated T R ≤ q.kernel := by
  apply (generated_le_iff T q.kernel).mpr
  intro x y h
  exact q.identifies x y h

/-- Every repair quotient kernel refines the behavioral upper endpoint. -/
theorem kernel_le_behavior (q : RepairQuotient T observe R) :
    q.kernel ≤ behavior T observe := by
  apply (le_behavior_iff T observe q.kernel).mpr
  intro x y h
  change observe x = observe y
  rw [← q.observation_comm, ← q.observation_comm, h]

/-- A repair quotient determines an element of the interval in GOAL B. -/
def intervalPoint (q : RepairQuotient T observe R) :
    {c : OperationCongruence T // generated T R ≤ c ∧ c ≤ behavior T observe} :=
  ⟨q.kernel, q.generated_le_kernel, q.kernel_le_behavior⟩

/-- A surjective repair quotient is canonically equivalent to the standard
quotient by its kernel. This works for a target in any universe. -/
noncomputable def standardEquiv (q : RepairQuotient T observe R) :
    Quotient q.kernel.setoid ≃ q.Target :=
  Setoid.quotientKerEquivOfSurjective q.read q.surjective

/-- The canonical equivalence commutes with the original source map. -/
@[simp] theorem standardEquiv_mk (q : RepairQuotient T observe R) (x : S) :
    q.standardEquiv (Quotient.mk q.kernel.setoid x) = q.read x := rfl

/-- The target of every repair quotient of a finite state type is finite. -/
theorem finite_target [Finite S] (q : RepairQuotient T observe R) :
    Finite q.Target := Finite.of_surjective q.read q.surjective

end RepairQuotient

/-- A morphism of repair quotients preserves the named operations and observation
and commutes with the original state map, as required by GOAL B. -/
structure RepairHom (q : RepairQuotient.{u, v, w, z} T observe R)
    (q' : RepairQuotient.{u, v, w, z'} T observe R) where
  toFun : q.Target → q'.Target
  source_comm : ∀ x, toFun (q.read x) = q'.read x
  step_comm : ∀ e z, toFun (q.step e z) = q'.step e (toFun z)
  observation_comm : ∀ z, q'.observation (toFun z) = q.observation z

namespace RepairHom

variable {T : OperationSystem S E} {observe : S → O} {R : S → S → Prop}
variable {q : RepairQuotient.{u, v, w, z} T observe R}
variable {q' : RepairQuotient.{u, v, w, z'} T observe R}
variable {q'' : RepairQuotient.{u, v, w, z''} T observe R}

/-- The identity morphism of a repair quotient. -/
def id (q : RepairQuotient T observe R) : RepairHom T observe R q q where
  toFun := _root_.id
  source_comm := by intro x; rfl
  step_comm := by intro e z; rfl
  observation_comm := by intro z; rfl

/-- Composition of repair quotient morphisms. -/
def comp (f : RepairHom T observe R q q') (g : RepairHom T observe R q' q'') :
    RepairHom T observe R q q'' where
  toFun := g.toFun ∘ f.toFun
  source_comm := by intro x; simp [Function.comp, f.source_comm, g.source_comm]
  step_comm := by intro e z; simp [Function.comp, f.step_comm, g.step_comm]
  observation_comm := by intro z; simp [Function.comp, f.observation_comm, g.observation_comm]

/-- A morphism is uniquely determined by commuting with the surjective source map. -/
theorem unique (f g : RepairHom T observe R q q') : f.toFun = g.toFun := by
  funext z
  obtain ⟨x, rfl⟩ := q.surjective z
  exact (f.source_comm x).trans (g.source_comm x).symm

/-- GOAL B uniqueness as equality of all morphism data. -/
theorem subsingleton (f g : RepairHom T observe R q q') : f = g := by
  cases f with
  | mk f hf hs ho =>
    cases g with
    | mk g hg ht hp =>
      have hfg : f = g := unique
        { toFun := f, source_comm := hf, step_comm := hs, observation_comm := ho }
        { toFun := g, source_comm := hg, step_comm := ht, observation_comm := hp }
      cases hfg
      rfl

/-- Every morphism of repair quotients is surjective. -/
theorem surjective (f : RepairHom T observe R q q') : Function.Surjective f.toFun := by
  intro z
  obtain ⟨x, hx⟩ := q'.surjective z
  exact ⟨q.read x, (f.source_comm x).trans hx⟩

/-- Existence of a morphism is equivalent to inclusion of quotient kernels.
The reverse implication constructs the map using source representatives;
operation and observation preservation then follow from source surjectivity. -/
theorem nonempty_iff_kernel_le :
    Nonempty (RepairHom T observe R q q') ↔ q.kernel ≤ q'.kernel := by
  constructor
  · rintro ⟨f⟩ x y h
    change q'.read x = q'.read y
    rw [← f.source_comm, ← f.source_comm, h]
  · intro h
    classical
    let rep : q.Target → S := fun z => Classical.choose (q.surjective z)
    have hrep (z : q.Target) : q.read (rep z) = z :=
      Classical.choose_spec (q.surjective z)
    let f : q.Target → q'.Target := fun z => q'.read (rep z)
    have hsource (x : S) : f (q.read x) = q'.read x := by
      apply h
      change q.read (rep (q.read x)) = q.read x
      exact hrep (q.read x)
    refine ⟨{
      toFun := f
      source_comm := hsource
      step_comm := ?_
      observation_comm := ?_ }⟩
    · intro e z
      obtain ⟨x, rfl⟩ := q.surjective z
      rw [← q.step_comm e x, hsource, hsource, q'.step_comm]
    · intro z
      obtain ⟨x, rfl⟩ := q.surjective z
      rw [hsource, q.observation_comm, q'.observation_comm]

end RepairHom

/-- Construct the quotient's operation and observation tables from an interval
congruence. The requested pairs are identified by the lower-endpoint proof. -/
def quotientRepair (c : OperationCongruence T)
    (hR : generated T R ≤ c) (hobs : c ≤ behavior T observe) :
    RepairQuotient T observe R where
  Target := Quotient c.setoid
  read := Quotient.mk c.setoid
  surjective := by
    intro q
    refine Quotient.inductionOn q ?_
    intro x
    exact ⟨x, rfl⟩
  step := fun e q => Quotient.liftOn q
    (fun x => Quotient.mk c.setoid (T.step e x))
    (fun x y h => Quotient.sound (c.stable e x y h))
  observation := fun q => Quotient.liftOn q observe (by
    intro x y h
    exact (behavior_le_kernel T observe) (hobs h))
  step_comm := by intro e x; rfl
  observation_comm := by intro x; rfl
  identifies := by
    intro x y h
    exact Quotient.sound (hR (generated_contains T h))

/-- The quotient constructed from a congruence has exactly that kernel. -/
theorem quotientRepair_kernel (c : OperationCongruence T)
    (hR : generated T R ≤ c) (hobs : c ≤ behavior T observe) :
    (quotientRepair T observe R c hR hobs).kernel.setoid = c.setoid := by
  apply Setoid.ext
  intro x y
  change (Quotient.mk c.setoid x = Quotient.mk c.setoid y) ↔ c.setoid.r x y
  exact Quotient.eq

/-- GOAL B: repair quotients exist precisely when the generated lower endpoint
lies below the behavioral upper endpoint. -/
theorem repair_exists_iff :
    Nonempty (RepairQuotient.{u, v, w, u} T observe R) ↔
      generated T R ≤ behavior T observe := by
  constructor
  · rintro ⟨q⟩
    exact le_trans q.generated_le_kernel q.kernel_le_behavior
  · intro h
    exact ⟨quotientRepair T observe R (generated T R) (le_refl _) h⟩

/-- GOAL B: the present observation kernel suffices because the lower
endpoint is itself stable under every operation. -/
theorem generated_le_kernel_observe_iff :
    generated T R ≤ behavior T observe ↔
      (generated T R).setoid ≤ Setoid.ker observe :=
  le_behavior_iff T observe (generated T R)

/-- GOAL B: a repair exists precisely when every requested pair has equal
observations after every future operation word. -/
theorem repair_exists_iff_request_behavior :
    Nonempty (RepairQuotient.{u, v, w, u} T observe R) ↔
      ∀ x y, R x y → (behavior T observe).setoid.r x y := by
  rw [repair_exists_iff]
  exact generated_le_behavior_iff T observe R

/-- The lower endpoint is the finest repair quotient when repair is possible. -/
def lowerRepair (h : generated T R ≤ behavior T observe) :
    RepairQuotient T observe R :=
  quotientRepair T observe R (generated T R) (le_refl _) h

/-- The upper endpoint is the coarsest repair quotient when repair is possible. -/
def upperRepair (h : generated T R ≤ behavior T observe) :
    RepairQuotient T observe R :=
  quotientRepair T observe R (behavior T observe) h (le_refl _)

/-- Every repair quotient receives a unique map from the lower endpoint. -/
theorem lower_hom (h : generated T R ≤ behavior T observe)
    (q : RepairQuotient T observe R) :
    Nonempty (RepairHom T observe R (lowerRepair T observe R h) q) := by
  apply RepairHom.nonempty_iff_kernel_le.mpr
  change (lowerRepair T observe R h).kernel.setoid ≤ q.kernel.setoid
  rw [lowerRepair, quotientRepair_kernel]
  exact q.generated_le_kernel

/-- Every repair quotient has a unique map into the upper endpoint. -/
theorem upper_hom (h : generated T R ≤ behavior T observe)
    (q : RepairQuotient T observe R) :
    Nonempty (RepairHom T observe R q (upperRepair T observe R h)) := by
  apply RepairHom.nonempty_iff_kernel_le.mpr
  change q.kernel.setoid ≤ (upperRepair T observe R h).kernel.setoid
  rw [upperRepair, quotientRepair_kernel]
  exact q.kernel_le_behavior

#assert_standard_axioms_only AAT.AG.OperationRepair

end AAT.AG.OperationRepair
