import ResearchLean.AG.OperationRepair.InputMaps

/-! Sequential repair quotients and operation congruences. -/
namespace AAT.AG.OperationRepair
universe u v
variable {S : Type u} {E : Type v} (T : OperationSystem S E)

/-- Operations induced on a quotient by an operation congruence. -/
def quotientSystem (c : OperationCongruence T) :
    OperationSystem (Quotient c.setoid) E where
  step e := fun q => Quotient.liftOn q
    (fun x => Quotient.mk c.setoid (T.step e x))
    (fun x y h => Quotient.sound (c.stable e x y h))

@[simp] theorem quotientSystem_step_mk (c : OperationCongruence T) (e : E) (x : S) :
    (quotientSystem T c).step e (Quotient.mk c.setoid x) =
      Quotient.mk c.setoid (T.step e x) := rfl

/-- Image of a request under a quotient map. -/
def imageRequest (c : OperationCongruence T) (R : S → S → Prop)
    (a b : Quotient c.setoid) : Prop :=
  ∃ x y, R x y ∧ Quotient.mk c.setoid x = a ∧ Quotient.mk c.setoid y = b

/-- Map from one quotient to a quotient by a larger congruence. -/
def quotientMap (c d : OperationCongruence T) (h : c ≤ d) :
    Quotient c.setoid → Quotient d.setoid :=
  fun q => Quotient.liftOn q (Quotient.mk d.setoid)
    (fun _ _ hxy => Quotient.sound (h hxy))

@[simp] theorem quotientMap_mk (c d : OperationCongruence T) (h : c ≤ d) (x : S) :
    quotientMap T c d h (Quotient.mk c.setoid x) = Quotient.mk d.setoid x := rfl

@[simp] theorem quotientMap_step (c d : OperationCongruence T) (h : c ≤ d)
    (e : E) (q : Quotient c.setoid) :
    quotientMap T c d h ((quotientSystem T c).step e q) =
      (quotientSystem T d).step e (quotientMap T c d h q) := by
  induction q using Quotient.inductionOn with
  | _ x => rfl

/-- The kernel of the quotient map is an operation congruence. -/
def quotientMapKernel (c d : OperationCongruence T) (h : c ≤ d) :
    OperationCongruence (quotientSystem T c) where
  setoid := Setoid.ker (quotientMap T c d h)
  stable := by
    intro e a b hab
    change quotientMap T c d h ((quotientSystem T c).step e a) =
      quotientMap T c d h ((quotientSystem T c).step e b)
    rw [quotientMap_step, quotientMap_step, hab]

/-- Image-generated congruence equals the kernel of the map to the join. -/
theorem generated_imageRequest_eq_kernel (c : OperationCongruence T)
    (R : S → S → Prop) :
    generated (quotientSystem T c) (imageRequest T c R) =
      quotientMapKernel T c (c ⊔ generated T R) le_sup_left := by
  let d : OperationCongruence T := c ⊔ generated T R
  let k := generated (quotientSystem T c) (imageRequest T c R)
  apply le_antisymm
  · apply (generated_le_iff (quotientSystem T c) _).mpr
    intro a b hab
    obtain ⟨x, y, hr, rfl, rfl⟩ := hab
    change (quotientMap T c d le_sup_left) (Quotient.mk c.setoid x) =
      (quotientMap T c d le_sup_left) (Quotient.mk c.setoid y)
    simp only [quotientMap_mk]
    exact Quotient.sound ((show generated T R ≤ d from le_sup_right)
      (generated_contains T hr))
  · intro a b hab
    induction a using Quotient.inductionOn with
    | _ x =>
      induction b using Quotient.inductionOn with
      | _ y =>
        let pull : OperationCongruence T := {
          setoid := Setoid.comap (Quotient.mk c.setoid) k.setoid
          stable := by
            intro e s t hst
            exact k.stable e (Quotient.mk c.setoid s)
              (Quotient.mk c.setoid t) hst }
        have hc : c ≤ pull := by
          intro s t hst
          change k.setoid.r (Quotient.mk c.setoid s) (Quotient.mk c.setoid t)
          have heq : Quotient.mk c.setoid s = Quotient.mk c.setoid t := Quotient.sound hst
          rw [heq]
        have hr : generated T R ≤ pull := by
          apply (generated_le_iff T pull).mpr
          intro s t hst
          change k.setoid.r (Quotient.mk c.setoid s) (Quotient.mk c.setoid t)
          exact generated_contains (quotientSystem T c)
            (show imageRequest T c R (Quotient.mk c.setoid s)
              (Quotient.mk c.setoid t) from ⟨s, t, hst, rfl, rfl⟩)
        have hd : d ≤ pull := sup_le hc hr
        change quotientMap T c d le_sup_left (Quotient.mk c.setoid x) =
          quotientMap T c d le_sup_left (Quotient.mk c.setoid y) at hab
        simp only [quotientMap_mk] at hab
        exact hd (Quotient.eq.mp hab)

/-- The third isomorphism theorem after identifying the second generated
congruence with the kernel of the map to the join. -/
def sequentialEquiv (c : OperationCongruence T) (R : S → S → Prop) :
    Quotient (generated (quotientSystem T c) (imageRequest T c R)).setoid ≃
      Quotient (c ⊔ generated T R).setoid := by
  exact (Quotient.congr (Equiv.refl _) (fun a b => by
    rw [generated_imageRequest_eq_kernel]
    induction a using Quotient.inductionOn with
    | _ x =>
      induction b using Quotient.inductionOn with
      | _ y => rfl)).trans
    (Setoid.quotientQuotientEquivQuotient c.setoid
      (c ⊔ generated T R).setoid
      (by change c ≤ c ⊔ generated T R; exact le_sup_left))

@[simp] theorem sequentialEquiv_mk (c : OperationCongruence T)
    (R : S → S → Prop) (x : S) :
    sequentialEquiv T c R
      (Quotient.mk (generated (quotientSystem T c) (imageRequest T c R)).setoid
        (Quotient.mk c.setoid x)) =
      Quotient.mk (c ⊔ generated T R).setoid x := by
  simp [sequentialEquiv, Setoid.quotientQuotientEquivQuotient]

/-- The sequential equivalence preserves each descended named operation. -/
theorem sequentialEquiv_step (c : OperationCongruence T) (R : S → S → Prop)
    (e : E)
    (q : Quotient (generated (quotientSystem T c) (imageRequest T c R)).setoid) :
    sequentialEquiv T c R
      ((quotientSystem (quotientSystem T c)
        (generated (quotientSystem T c) (imageRequest T c R))).step e q) =
      (quotientSystem T (c ⊔ generated T R)).step e (sequentialEquiv T c R q) := by
  induction q using Quotient.inductionOn with
  | _ a =>
    induction a using Quotient.inductionOn with
    | _ x => simp only [quotientSystem_step_mk, sequentialEquiv_mk]

/-- Observation descended along an operation congruence below behavior. -/
def quotientObservation {O : Type w} (observe : S → O)
    (c : OperationCongruence T) (h : c ≤ behavior T observe) :
    Quotient c.setoid → O :=
  fun q => Quotient.liftOn q observe (by
    intro x y hxy
    exact (behavior_le_kernel T observe) (h hxy))

@[simp] theorem quotientObservation_mk {O : Type w} (observe : S → O)
    (c : OperationCongruence T) (h : c ≤ behavior T observe) (x : S) :
    quotientObservation T observe c h (Quotient.mk c.setoid x) = observe x := rfl

/-- When both stages are repairable, the second image request is repairable
on the first quotient using its descended observation. -/
theorem imageRequest_repairable {O : Type w} (observe : S → O)
    (c : OperationCongruence T) (R : S → S → Prop)
    (hc : c ≤ behavior T observe) (hR : generated T R ≤ behavior T observe) :
    generated (quotientSystem T c) (imageRequest T c R) ≤
      behavior (quotientSystem T c) (quotientObservation T observe c hc) := by
  rw [generated_imageRequest_eq_kernel]
  apply (le_behavior_iff (quotientSystem T c)
    (quotientObservation T observe c hc) _).mpr
  intro a b hab
  induction a using Quotient.inductionOn with
  | _ x =>
    induction b using Quotient.inductionOn with
    | _ y =>
      change quotientObservation T observe c hc (Quotient.mk c.setoid x) =
        quotientObservation T observe c hc (Quotient.mk c.setoid y)
      simp only [quotientObservation_mk]
      have hd : (c ⊔ generated T R).setoid.r x y := by
        apply Quotient.eq.mp
        exact hab
      exact (behavior_le_kernel T observe) ((sup_le hc hR) hd)

/-- Sequential quotient and direct quotient have the same observation. -/
theorem sequentialEquiv_observation {O : Type w} (observe : S → O)
    (c : OperationCongruence T) (R : S → S → Prop)
    (hc : c ≤ behavior T observe) (hR : generated T R ≤ behavior T observe)
    (q : Quotient (generated (quotientSystem T c) (imageRequest T c R)).setoid) :
    quotientObservation T observe (c ⊔ generated T R) (sup_le hc hR)
      (sequentialEquiv T c R q) =
    quotientObservation (quotientSystem T c) (quotientObservation T observe c hc)
      (generated (quotientSystem T c) (imageRequest T c R))
      (imageRequest_repairable T observe c R hc hR) q := by
  induction q using Quotient.inductionOn with
  | _ a =>
    induction a using Quotient.inductionOn with
    | _ x => simp only [sequentialEquiv_mk, quotientObservation_mk]

/-- Any comparison commuting with the map from the original source is
uniquely the sequential equivalence. -/
theorem sequentialEquiv_unique (c : OperationCongruence T)
    (R : S → S → Prop)
    (f : Quotient (generated (quotientSystem T c) (imageRequest T c R)).setoid →
      Quotient (c ⊔ generated T R).setoid)
    (h : ∀ x : S,
      f (Quotient.mk (generated (quotientSystem T c) (imageRequest T c R)).setoid
        (Quotient.mk c.setoid x)) = Quotient.mk (c ⊔ generated T R).setoid x) :
    f = sequentialEquiv T c R := by
  funext q
  induction q using Quotient.inductionOn with
  | _ a =>
    induction a using Quotient.inductionOn with
    | _ x => simpa only [sequentialEquiv_mk] using h x

#assert_standard_axioms_only AAT.AG.OperationRepair
end AAT.AG.OperationRepair
