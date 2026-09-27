import ResearchLean.AG.OperationRepair.ClassOrder

/-!
# Universal factorization through the generated repair quotient

The target can have any universe and any cardinality. The source map need not
be surjective.
-/

namespace AAT.AG.OperationRepair

universe u v w z

variable {S : Type u} {E : Type v} {O : Type w} {X : Type z}
variable (T : OperationSystem S E) (observe : S → O) (R : S → S → Prop)
variable (stepX : E → X → X) (observeX : X → O) (h : S → X)

/-- The kernel of an operation-preserving map is an operation congruence. -/
def mapKernel (hstep : ∀ e x, h (T.step e x) = stepX e (h x)) :
    OperationCongruence T where
  setoid := Setoid.ker h
  stable := by
    intro e x y hxy
    change h (T.step e x) = h (T.step e y)
    rw [hstep, hstep, hxy]

/-- The request is contained in the kernel of every operation-preserving map
that identifies the requested pairs. -/
theorem generated_le_mapKernel
    (hstep : ∀ e x, h (T.step e x) = stepX e (h x))
    (hR : ∀ x y, R x y → h x = h y) :
    generated T R ≤ mapKernel T stepX h hstep := by
  apply (generated_le_iff T (mapKernel T stepX h hstep)).mpr
  exact hR

/-- The map to any operation/observation-preserving target implies the repair
existence condition for its identified request. -/
theorem repairable_of_map
    (hstep : ∀ e x, h (T.step e x) = stepX e (h x))
    (hobserve : ∀ x, observeX (h x) = observe x)
    (hR : ∀ x y, R x y → h x = h y) :
    generated T R ≤ behavior T observe := by
  apply (le_behavior_iff T observe (generated T R)).mpr
  intro x y hxy
  have hh : h x = h y := (generated_le_mapKernel T R stepX h hstep hR) hxy
  change observe x = observe y
  calc
    observe x = observeX (h x) := (hobserve x).symm
    _ = observeX (h y) := congrArg observeX hh
    _ = observe y := hobserve y

/-- The map through the generated quotient, constructed from the kernel
inclusion rather than supplied as a factorization certificate. -/
def generatedLift
    (hstep : ∀ e x, h (T.step e x) = stepX e (h x))
    (hR : ∀ x y, R x y → h x = h y) :
    Quotient (generated T R).setoid → X :=
  Quotient.lift h (fun _ _ hab =>
    (generated_le_mapKernel T R stepX h hstep hR) hab)

@[simp] theorem generatedLift_mk
    (hstep : ∀ e x, h (T.step e x) = stepX e (h x))
    (hR : ∀ x y, R x y → h x = h y) (x : S) :
    generatedLift T R stepX h hstep hR
      (Quotient.mk (generated T R).setoid x) = h x := rfl

/-- GOAL B: the generated lift preserves every descended operation. -/
theorem generatedLift_step
    (hstep : ∀ e x, h (T.step e x) = stepX e (h x))
    (hobserve : ∀ x, observeX (h x) = observe x)
    (hR : ∀ x y, R x y → h x = h y) (e : E)
    (q : Quotient (generated T R).setoid) :
    generatedLift T R stepX h hstep hR
      ((lowerRepair T observe R
        (repairable_of_map T observe R stepX observeX h hstep hobserve hR)).step e q) =
      stepX e (generatedLift T R stepX h hstep hR q) := by
  refine Quotient.inductionOn q ?_
  intro x
  exact hstep e x

/-- GOAL B: the generated lift preserves the descended observation. -/
theorem generatedLift_observation
    (hstep : ∀ e x, h (T.step e x) = stepX e (h x))
    (hobserve : ∀ x, observeX (h x) = observe x)
    (hR : ∀ x y, R x y → h x = h y)
    (q : Quotient (generated T R).setoid) :
    observeX (generatedLift T R stepX h hstep hR q) =
      (lowerRepair T observe R
        (repairable_of_map T observe R stepX observeX h hstep hobserve hR)).observation q := by
  refine Quotient.inductionOn q ?_
  intro x
  exact hobserve x

/-- GOAL B: any factorization agreeing with the source map equals the
constructed lift; no surjectivity or finiteness of the target is assumed. -/
theorem generatedLift_unique
    (hstep : ∀ e x, h (T.step e x) = stepX e (h x))
    (hR : ∀ x y, R x y → h x = h y)
    (f : Quotient (generated T R).setoid → X)
    (hf : ∀ x, f (Quotient.mk (generated T R).setoid x) = h x) :
    f = generatedLift T R stepX h hstep hR := by
  funext q
  refine Quotient.inductionOn q ?_
  intro x
  exact (hf x).trans (generatedLift_mk T R stepX h hstep hR x).symm

/-- GOAL B's full universal property for an arbitrary operation/observation
target. The factor is constructed, preserves both structures, and is unique. -/
theorem generated_universal
    (hstep : ∀ e x, h (T.step e x) = stepX e (h x))
    (hobserve : ∀ x, observeX (h x) = observe x)
    (hR : ∀ x y, R x y → h x = h y) :
    ∃! f : Quotient (generated T R).setoid → X,
      (∀ x, f (Quotient.mk (generated T R).setoid x) = h x) ∧
      (∀ e q, f ((lowerRepair T observe R
        (repairable_of_map T observe R stepX observeX h hstep hobserve hR)).step e q) =
        stepX e (f q)) ∧
      (∀ q, observeX (f q) =
        (lowerRepair T observe R
          (repairable_of_map T observe R stepX observeX h hstep hobserve hR)).observation q) := by
  refine ⟨generatedLift T R stepX h hstep hR, ?_, ?_⟩
  · exact ⟨generatedLift_mk T R stepX h hstep hR,
      generatedLift_step T observe R stepX observeX h hstep hobserve hR,
      generatedLift_observation T observe R stepX observeX h hstep hobserve hR⟩
  · intro f hf
    exact generatedLift_unique T R stepX h hstep hR f hf.1

#assert_standard_axioms_only AAT.AG.OperationRepair

end AAT.AG.OperationRepair
