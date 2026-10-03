import Mathlib.LinearAlgebra.Quotient.Basic
import Formal.Util.AssertStandardAxioms

/-!
# G-131 C: information fibers of the same correction equation

## Implementation notes

The fiber is a set of possible inputs, and the observation is an arbitrary
function on inputs. A numerical answer contains the entire correction value,
or `none` with the independent assertion that there is no solution. This form
keeps the output value distinct from a program referring to unknown operations.
The general factorization theorem uses choice only to prove existence of a
function. Executable finite planning and actual-operation restoration are
separate subsequent obligations.
-/

namespace AAT.AG.RepairObservationDuality

section General
variable {V H W T : Type*} (D : H → W) (rhs : V → W)

/-- C's independent solvability predicate for the specified correction equation. -/
def Solvable (v : V) : Prop := ∃ h, D h = rhs v

/-- C's output fixes all coordinates of a correction or certifies impossibility. -/
def ValidOutput (v : V) : Option H → Prop
  | none => ¬ Solvable D rhs v
  | some h => D h = rhs v

/-- C's complete successful output has exactly the specified correction equation. -/
theorem validOutput_some_iff (v : V) (h : H) :
    ValidOutput D rhs v (some h) ↔ D h = rhs v := Iff.rfl

/-- C's definite failure output asserts precisely independent equation impossibility. -/
theorem validOutput_none_iff (v : V) :
    ValidOutput D rhs v none ↔ ¬ Solvable D rhs v := Iff.rfl

/-- C's decision output factors the solvability predicate on the known input fiber. -/
def DecisionSufficient (F : Set V) (obs : V → T) : Prop :=
  ∃ p : T → Prop, ∀ v ∈ F, p (obs v) ↔ Solvable D rhs v

/-- C's numerical output factors a correct complete correction value on the fiber. -/
def NumericalSufficient (F : Set V) (obs : V → T) : Prop :=
  ∃ out : T → Option H, ∀ v ∈ F, ValidOutput D rhs v (out (obs v))

/-- Basic transport API for C: equal equation RHSs have equal solvability. -/
theorem solvable_congr_rhs {v w : V} (he : rhs v = rhs w) :
    Solvable D rhs v ↔ Solvable D rhs w := by
  simp only [Solvable, he]

/-- General information fibers support a decision precisely when observationally
equal inputs have equal solvability. No linearity of the information is assumed. -/
theorem decision_sufficient_iff (F : Set V) (obs : V → T) :
    DecisionSufficient D rhs F obs ↔
      ∀ v ∈ F, ∀ w ∈ F, obs v = obs w →
        (Solvable D rhs v ↔ Solvable D rhs w) := by
  constructor
  · rintro ⟨p, hp⟩ v hv w hw he
    rw [← hp v hv, ← hp w hw, he]
  · intro hf
    refine ⟨fun t => ∃ v ∈ F, obs v = t ∧ Solvable D rhs v, ?_⟩
    intro v hv
    constructor
    · rintro ⟨w, hw, he, hs⟩
      exact (hf w hw v hv he).mp hs
    · intro hs
      exact ⟨v, hv, rfl, hs⟩

/-- General information fibers support numerical output precisely when every
observation fiber is impossible throughout, or solvable with a constant RHS. -/
theorem numerical_sufficient_iff (F : Set V) (obs : V → T) :
    NumericalSufficient D rhs F obs ↔
      ∀ v ∈ F, ∀ w ∈ F, obs v = obs w →
        (Solvable D rhs v ↔ Solvable D rhs w) ∧
        (Solvable D rhs v → rhs v = rhs w) := by
  classical
  constructor
  · rintro ⟨out, ho⟩ v hv w hw he
    have hvo := ho v hv
    have hwo := ho w hw
    rw [← he] at hwo
    cases hval : out (obs v) with
    | none =>
        simp only [hval, ValidOutput] at hvo hwo
        exact ⟨iff_of_false hvo hwo, fun hs => (hvo hs).elim⟩
    | some h =>
        simp only [hval, ValidOutput] at hvo hwo
        exact ⟨iff_of_true ⟨h, hvo⟩ ⟨h, hwo⟩, fun _ => hvo.symm.trans hwo⟩
  · intro hf
    let has : T → Prop := fun t => ∃ v ∈ F, obs v = t ∧ Solvable D rhs v
    let chosen : ∀ t, has t → H := fun _ ht =>
      Classical.choose (Classical.choose_spec ht).2.2
    refine ⟨fun t => if ht : has t then some (chosen t ht) else none, ?_⟩
    intro v hv
    by_cases ht : has (obs v)
    · simp only [dif_pos ht, ValidOutput]
      let w := Classical.choose ht
      have hw := Classical.choose_spec ht
      have hs := Classical.choose_spec hw.2.2
      have he := (hf w hw.1 v hv hw.2.1).2 hw.2.2
      exact hs.trans he
    · simp only [dif_neg ht, ValidOutput]
      intro hs
      exact ht ⟨v, hv, rfl, hs⟩

end General

section Linear
variable {k V H W T I : Type*} [Field k]
variable [AddCommGroup V] [Module k V] [AddCommGroup H] [Module k H]
variable [AddCommGroup W] [Module k W] [AddCommGroup T] [Module k T]
variable [AddCommGroup I] [Module k I]
variable (D : H →ₗ[k] W) (B : V →ₗ[k] W) (b₀ : W)

/-- A's affine RHS retains the sign already generated from the actual defect. -/
def affineRhs (v : V) : W := b₀ + B v

/-- A's affine RHS evaluates its known constant and linear contribution. -/
theorem affineRhs_apply (v : V) : affineRhs B b₀ v = b₀ + B v := rfl

/-- A's obstruction is the native full cokernel of the permitted correction map. -/
def obstruction : V → W ⧸ LinearMap.range D :=
  fun v => (LinearMap.range D).mkQ (affineRhs B b₀ v)

/-- A's affine constant cancels in an input difference; downstream uses this API. -/
theorem affineRhs_sub (v w : V) :
    affineRhs B b₀ v - affineRhs B b₀ w = B (v - w) := by
  simp [affineRhs, map_sub]

/-- Equality of complete RHSs is equality of the linear parameter contributions. -/
theorem affineRhs_eq_iff (v w : V) :
    affineRhs B b₀ v = affineRhs B b₀ w ↔ B v = B w := by
  simp only [affineRhs, add_left_cancel_iff]

/-- The native obstruction difference is the image of the same input difference. -/
theorem obstruction_sub (v w : V) :
    obstruction D B b₀ v - obstruction D B b₀ w =
      (LinearMap.range D).mkQ (B (v - w)) := by
  rw [obstruction, obstruction, ← map_sub, affineRhs_sub]

/-- A's equation is solvable exactly at zero of this same cokernel class. -/
theorem solvable_iff_obstruction_zero (v : V) :
    Solvable D (affineRhs B b₀) v ↔ obstruction D B b₀ v = 0 := by
  exact (Submodule.Quotient.mk_eq_zero (LinearMap.range D)).symm

/-- C's known linear information fiber contains every input satisfying L v = s. -/
def informationFiber (L : V →ₗ[k] I) (s : I) : Set V := {v | L v = s}

/-- C's information fiber reads the specified linear information and value. -/
theorem mem_informationFiber (L : V →ₗ[k] I) (s : I) (v : V) :
    v ∈ informationFiber L s ↔ L v = s := Iff.rfl

/-- Every input in a nonempty linear fiber differs from its base by a kernel vector. -/
theorem mem_fiber_sub (L : V →ₗ[k] I) (s : I) {v w : V}
    (hv : v ∈ informationFiber L s) (hw : w ∈ informationFiber L s) :
    v - w ∈ LinearMap.ker L := by
  change L (v - w) = 0
  rw [map_sub, hv, hw, sub_self]

/-- Adding any unknown kernel direction retains precisely the known information. -/
theorem add_mem_fiber (L : V →ₗ[k] I) (s : I) {w : V}
    (hw : w ∈ informationFiber L s) {n : V} (hn : n ∈ LinearMap.ker L) :
    w + n ∈ informationFiber L s := by
  change L (w + n) = s
  rw [map_add, hw, hn, add_zero]

/-- Success at a base input translates the same repair predicate to ker(q B). -/
theorem solvable_add_iff {w : V} (hw : Solvable D (affineRhs B b₀) w) (n : V) :
    Solvable D (affineRhs B b₀) (w + n) ↔
      n ∈ LinearMap.ker ((LinearMap.range D).mkQ.comp B) := by
  rw [solvable_iff_obstruction_zero]
  have hz := (solvable_iff_obstruction_zero D B b₀ w).mp hw
  change (LinearMap.range D).mkQ (b₀ + B w) = 0 at hz
  change (LinearMap.range D).mkQ (b₀ + B (w + n)) = 0 ↔
    (LinearMap.range D).mkQ (B n) = 0
  rw [map_add B, ← add_assoc, map_add, hz, zero_add]

/-- C's decision sufficient sets on a successful known fiber are exactly the
stated intersection-kernel inclusions. The success premise is a direction hypothesis. -/
theorem decision_sufficient_linear_iff (L : V →ₗ[k] I) (s : I) (O : V →ₗ[k] T)
    {w : V} (hw : w ∈ informationFiber L s)
    (hs : Solvable D (affineRhs B b₀) w) :
    DecisionSufficient D (affineRhs B b₀) (informationFiber L s) O ↔
      LinearMap.ker L ⊓ LinearMap.ker O ≤
        LinearMap.ker ((LinearMap.range D).mkQ.comp B) := by
  rw [decision_sufficient_iff]
  constructor
  · intro hf n hn
    have hfn := add_mem_fiber L s hw hn.1
    have he : O (w + n) = O w := by rw [map_add, hn.2, add_zero]
    exact (solvable_add_iff D B b₀ hs n).mp ((hf (w + n) hfn w hw he).mpr hs)
  · intro hk v hv z hz he
    have hn : v - z ∈ LinearMap.ker L ⊓ LinearMap.ker O :=
      ⟨mem_fiber_sub L s hv hz, by change O (v - z) = 0; rw [map_sub, he, sub_self]⟩
    have heq : obstruction D B b₀ v = obstruction D B b₀ z := by
      have hnq := hk hn
      change (LinearMap.range D).mkQ (B (v - z)) = 0 at hnq
      apply sub_eq_zero.mp
      rw [obstruction_sub]
      exact hnq
    rw [solvable_iff_obstruction_zero, solvable_iff_obstruction_zero, heq]

/-- C's full numerical correction needs ker B, even when the obstruction vanishes
for all possible inputs. The same returned correction forces equality of both RHSs. -/
theorem numerical_sufficient_linear_iff (L : V →ₗ[k] I) (s : I) (O : V →ₗ[k] T)
    {w : V} (hw : w ∈ informationFiber L s)
    (hs : Solvable D (affineRhs B b₀) w) :
    NumericalSufficient D (affineRhs B b₀) (informationFiber L s) O ↔
      LinearMap.ker L ⊓ LinearMap.ker O ≤ LinearMap.ker B := by
  rw [numerical_sufficient_iff]
  constructor
  · intro hf n hn
    have hfn := add_mem_fiber L s hw hn.1
    have he : O w = O (w + n) := by rw [map_add, hn.2, add_zero]
    have hr := (hf w hw (w + n) hfn he).2 hs
    change B n = 0
    have heq : B w = B w + B n := by
      simpa only [map_add] using (affineRhs_eq_iff B b₀ w (w + n)).mp hr
    exact (add_left_cancel (heq.symm.trans (add_zero (B w)).symm))
  · intro hk v hv z hz he
    have hn : v - z ∈ LinearMap.ker L ⊓ LinearMap.ker O :=
      ⟨mem_fiber_sub L s hv hz, by change O (v - z) = 0; rw [map_sub, he, sub_self]⟩
    have hb : B v = B z := sub_eq_zero.mp (by simpa [map_sub] using hk hn)
    have hr : affineRhs B b₀ v = affineRhs B b₀ z :=
      (affineRhs_eq_iff B b₀ v z).mpr hb
    exact ⟨solvable_congr_rhs D (affineRhs B b₀) hr, fun _ => hr⟩

end Linear

section Nonvacuity
variable (k : Type*) [Field k]

/-- The independently defined equation has both solvable and impossible inputs
on every nonzero field, using the zero correction map and RHS equal to the input. -/
theorem solvable_zero_not_one :
    Solvable (fun _ : k => (0 : k)) id 0 ∧
      ¬ Solvable (fun _ : k => (0 : k)) id 1 := by
  exact ⟨⟨0, rfl⟩, fun ⟨_, he⟩ => zero_ne_one he⟩

/-- Each numerical answer constructor has an explicit valid and invalid instance
for the same correction equation, without an observational assumption. -/
theorem valid_output_examples :
    ValidOutput (fun _ : k => (0 : k)) id 0 (some 0) ∧
    ¬ ValidOutput (fun _ : k => (0 : k)) id 1 (some 0) ∧
    ValidOutput (fun _ : k => (0 : k)) id 1 none ∧
    ¬ ValidOutput (fun _ : k => (0 : k)) id 0 none := by
  exact ⟨rfl, zero_ne_one, (solvable_zero_not_one k).2,
    fun hn => hn (solvable_zero_not_one k).1⟩

/-- Constant observation fails decision sufficiency when zero and one inputs have
different solvability, providing the negative instance of C's decision predicate. -/
theorem decision_sufficient_fails :
    ¬ DecisionSufficient (fun _ : k => (0 : k)) id Set.univ (fun _ : k => ()) := by
  intro hs
  have hf := (decision_sufficient_iff (fun _ : k => (0 : k)) id Set.univ
    (fun _ : k => ())).mp hs
  exact (solvable_zero_not_one k).2
    ((hf 0 (Set.mem_univ _) 1 (Set.mem_univ _) rfl).mp (solvable_zero_not_one k).1)

omit [Field k] in
/-- Observing the whole input numerically gives the positive instance of C's
numerical predicate, with every complete correction value returned directly. -/
theorem numerical_sufficient_identity :
    NumericalSufficient (id : k → k) id Set.univ id :=
  ⟨some, fun _ _ => rfl⟩

/-- A nonzero field supplies a same-equation example: all inputs are solvable
without observation, while a constant observation cannot determine numerical output. -/
theorem decision_numerical_differ :
    DecisionSufficient (id : k → k) id Set.univ (fun _ : k => ()) ∧
      ¬ NumericalSufficient (id : k → k) id Set.univ (fun _ : k => ()) := by
  constructor
  · exact ⟨fun _ => True, fun v _ => ⟨fun _ => ⟨v, rfl⟩, fun _ => trivial⟩⟩
  · intro hn
    have hf := (numerical_sufficient_iff (id : k → k) id Set.univ
      (fun _ : k => ())).mp hn
    have he := (hf 0 (Set.mem_univ _) 1 (Set.mem_univ _) rfl).2 ⟨0, rfl⟩
    exact zero_ne_one he

end Nonvacuity
end AAT.AG.RepairObservationDuality
#assert_standard_axioms_only AAT.AG.RepairObservationDuality
