import ResearchLean.AG.RelativeRepairComposition.FiniteFunctionEnumeration
import ResearchLean.AG.RelativeRepairComposition.CokernelNamedRanges
import Mathlib.LinearAlgebra.Matrix.Dual

/-!
# Finite construction of a failed-range quotient dual

All row vectors are enumerated from the original complete coefficient lists.
Tests evaluate every full always/candidate basis column and the same right-hand
side. The returned row, rather than a chosen existential dual, generates the
quotient functional. Empty index families use the same enumeration and tests.
-/
namespace AAT.AG.RelativeRepairComposition.FiniteDual
universe uk ux ue uy un
variable {k : Type uk} [Field k] [Fintype k] [DecidableEq k]
variable {n : Type un} [Fintype n] [DecidableEq n]
variable {m : Type ux} [Fintype m] [DecidableEq m]
variable {E : Type ue} [Fintype E] [DecidableEq E] {j : E → Type uy}
variable [∀ e, Fintype (j e)] [∀ e, DecidableEq (j e)]
variable (D : (m → k) →ₗ[k] (n → k)) (C : ∀ e, (j e → k) →ₗ[k] (n → k))

/-- A finite row evaluates the complete coordinate space by its ordinary dot product. -/
def row (w : n → k) : Module.Dual k (n → k) := dotProductEquiv k n w

omit [Fintype k] [DecidableEq k] in
/-- Full basis-column evaluation is exactly annihilation of the whole linear map. -/
theorem annihilates_iff (w : n → k) (L : (m → k) →ₗ[k] (n → k)) :
    (row w).comp L = 0 ↔ ∀ i, row w (L (Pi.single i 1)) = 0 := by
  constructor
  · intro h i
    exact LinearMap.congr_fun h (Pi.single i 1)
  · intro h
    apply LinearMap.pi_ext
    intro i x
    have hp : (Pi.single i x : m → k) = x • Pi.single i 1 := by
      funext l
      by_cases hl : l = i
      · subst l
        simp
      · simp [hl]
    change row w (L (Pi.single i x)) = 0
    rw [hp,map_smul,map_smul,h i,smul_zero]

variable (r : n → k) (S : Set E) [DecidablePred (· ∈ S)]

/-- Independently check every original always/allowed candidate basis and a nonzero rhs value. -/
def Valid (w : n → k) : Prop :=
  (∀ i : m, row w (D (Pi.single i 1)) = 0) ∧
  (∀ e ∈ S, ∀ i : j e, row w (C e (Pi.single i 1)) = 0) ∧ row w r ≠ 0

/-- Finite decisions use only field arithmetic and the original complete column families. -/
instance validDecidable (w : n → k) : Decidable (Valid D C r S w) :=
  inferInstanceAs (Decidable ((∀ i : m, row w (D (Pi.single i 1)) = 0) ∧
    (∀ e ∈ S, ∀ i : j e, row w (C e (Pi.single i 1)) = 0) ∧ row w r ≠ 0))

variable (enumK : FiniteElimination.Enumeration k) (enumN : FiniteElimination.Enumeration n)

/-- Enumerate all finite rows once; no rhs or allowed set changes the row list. -/
def rows : FiniteElimination.Enumeration (n → k) := enumN.pi (fun _ => enumK)

/-- Search all rows by the explicit finite column/rhs test. -/
def find : Option (n → k) :=
  (rows enumK enumN).values.find? (fun w => decide (Valid D C r S w))

omit [Fintype k] [DecidableEq k] [Fintype m] [Fintype E] [DecidableEq E]
  [∀ e, Fintype (j e)] [DecidablePred (· ∈ S)] in
include enumK enumN in
/-- Field separation and full row coordinates prove that a failed range passes a finite row test. -/
theorem valid_of_failure
    (h : LinearInterface.q D r ∉ NamedDual.ranges (CokernelNamed.column D C) S) :
    ∃ w ∈ (rows enumK enumN).values, Valid D C r S w := by
  classical
  obtain ⟨phi,hphi,hc⟩ := NamedDual.failure_witness
    (CokernelNamed.column D C) (LinearInterface.q D r) S h
  let f := phi.comp (LinearInterface.q D)
  let w := (dotProductEquiv k n).symm f
  have hw : row w = f := (dotProductEquiv k n).apply_symm_apply f
  refine ⟨w,(rows enumK enumN).complete w,?_,?_,?_⟩
  · intro i
    rw [hw]
    change phi (LinearInterface.q D (D (Pi.single i 1))) = 0
    have hz : LinearInterface.q D (D (Pi.single i 1)) = 0 :=
      (Submodule.Quotient.mk_eq_zero (LinearMap.range D)).mpr ⟨Pi.single i 1,rfl⟩
    rw [hz,map_zero]
  · intro e he i
    rw [hw]
    exact LinearMap.congr_fun (hc e he) (Pi.single i 1)
  · rw [hw]
    exact hphi

omit [Fintype k] [DecidableEq E] in
/-- A failed range makes the finite search succeed, without choosing an existential output row. -/
theorem find_isSome
    (h : LinearInterface.q D r ∉ NamedDual.ranges (CokernelNamed.column D C) S) :
    (find D C r S enumK enumN).isSome = true := by
  rw [find,List.find?_isSome]
  obtain ⟨w,hw,hv⟩ := valid_of_failure D C r S enumK enumN h
  exact ⟨w,hw,decide_eq_true hv⟩

/-- The returned row is the finite find result with its actual checked test. -/
def rowWitness
    (h : LinearInterface.q D r ∉ NamedDual.ranges (CokernelNamed.column D C) S) :
    {w : n → k // Valid D C r S w} := by
  have hf := find_isSome D C r S enumK enumN h
  refine ⟨(find D C r S enumK enumN).get hf,?_⟩
  have ht := List.find?_some (Option.some_get hf).symm
  exact of_decide_eq_true ht

/-- Descend a checked row to the actual complete always-column quotient. -/
def quotientDual (w : n → k) (hw : Valid D C r S w) :
    Module.Dual k ((n → k) ⧸ LinearMap.range D) :=
  (LinearMap.range D).liftQ (row w) (by
    rintro _ ⟨x,rfl⟩
    exact LinearMap.congr_fun ((annihilates_iff w D).mpr hw.1) x)

omit [Fintype k] [DecidableEq k] [Fintype E] [DecidableEq E]
  [∀ e, Fintype (j e)] [DecidablePred (· ∈ S)] in
/-- Quotient evaluation at any original representative is the same computed dot product. -/
theorem quotientDual_value (w : n → k) (hw : Valid D C r S w) (v : n → k) :
    quotientDual D C r S w hw (LinearInterface.q D v) = row w v := rfl

omit [Fintype k] [DecidableEq k] [Fintype E] [DecidableEq E] [DecidablePred (· ∈ S)] in
/-- The same finite row excludes rhs and annihilates every allowed full candidate kernel. -/
theorem quotientDual_spec (w : n → k) (hw : Valid D C r S w) :
    quotientDual D C r S w hw (LinearInterface.q D r) ≠ 0 ∧
      ∀ e ∈ S, (quotientDual D C r S w hw).comp (CokernelNamed.column D C e) = 0 := by
  refine ⟨hw.2.2,?_⟩
  intro e he
  apply LinearMap.ext
  intro x
  change row w (C e x) = 0
  exact LinearMap.congr_fun ((annihilates_iff w (C e)).mpr (hw.2.1 e he)) x

/-- A failed range generates its quotient dual from the computed finite row itself. -/
def computedDual
    (h : LinearInterface.q D r ∉ NamedDual.ranges (CokernelNamed.column D C) S) :
    {phi : Module.Dual k ((n → k) ⧸ LinearMap.range D) //
      phi (LinearInterface.q D r) ≠ 0 ∧ ∀ e ∈ S, phi.comp (CokernelNamed.column D C e) = 0} :=
  let w := rowWitness D C r S enumK enumN h
  ⟨quotientDual D C r S w.1 w.2,quotientDual_spec D C r S w.1 w.2⟩

end AAT.AG.RelativeRepairComposition.FiniteDual
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
