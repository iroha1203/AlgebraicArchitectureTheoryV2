import ResearchLean.AG.RelativeRepairComposition.W3AuthoredOperations
import ResearchLean.AG.RelativeRepairComposition.W3Regions
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Independent full actual repairs and W3's complete correction span

The actual affine operations, original projections and literal fixed values
define repairs independently of coordinates. Values at zero then recover
both complete correction vectors; every permitted pair restores a repair.
-/
namespace AAT.AG.RelativeRepairComposition.W3ActualRepairs
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
open NativeAffine W3LinearAction W3AffineInput W3AuthoredOperations W3Regions

/-- All independently specified actual original repairs, for every permission set. -/
abbrev RealRepairs (sheared : Bool) (S : Set (EdgeName (K := geometry))) :=
  NativeAffine.Repair geometry (reference sheared) comparison (fixedEdges S)

/-- All actual gauge arrows retain the original physically free vertices. -/
abbrev ActualCategory (sheared : Bool) (S : Set (EdgeName (K := geometry))) :=
  NativeAffine.Groupoid geometry (reference sheared) (reference sheared) comparison
    (linear_faces sheared) fixedRegion.vertices (fixedEdges S)

/-- The same original native repair groupoid with all original labels. -/
abbrev NativeCategory (sheared : Bool) (S : Set (EdgeName (K := geometry))) :=
  RepairGroupoid (originalTower sheared) fixedRegion.vertices (fixedEdges S)

/-- The complete two-vector span, before either permission or gauge quotient. -/
abbrev Parameters := A × A

/-- A forbidden original name has zero correction, with no fixed vertex added. -/
def Allowed (S : Set (EdgeName (K := geometry))) (p : Parameters) : Prop :=
  (name edgeE ∉ S → p.1 = 0) ∧ (name edgeF ∉ S → p.2 = 0)

/-- Both original operation values at zero extract their entire vectors. -/
def parameters {sheared : Bool} {S : Set (EdgeName (K := geometry))}
    (R : RealRepairs sheared S) : Parameters :=
  ⟨R.operation (name edgeE).2.2 0, R.operation (name edgeF).2.2 0⟩

/-- Every independent operation is determined by its original linear part and actual zero value. -/
theorem actual_operation_apply {sheared : Bool} {S : Set (EdgeName (K := geometry))}
    (R : RealRepairs sheared S) {i j : geometry.Vertex} (e : geometry.Edge i j) (x : A) :
    R.operation e x = (reference sheared e).linear x + R.operation e 0 := by
  rw [NativeAffine.operation_apply, R.linear]

/-- Both arbitrary correction vectors restore every actual original affine operation. -/
theorem parameters_operations {sheared : Bool} {S : Set (EdgeName (K := geometry))}
    (R : RealRepairs sheared S) :
    @operation sheared (parameters R).1 (parameters R).2 = @R.operation := by
  funext i j e
  rcases e with ⟨e,hs,ht⟩
  cases hs
  cases ht
  fin_cases e
  · apply AffineEquiv.ext
    intro x
    change operation sheared (parameters R).1 (parameters R).2 (name edgeE).2.2 x = _
    rw [operation_e_apply, actual_operation_apply]
    rfl
  · apply AffineEquiv.ext
    intro x
    change operation sheared (parameters R).1 (parameters R).2 (name edgeF).2.2 x = _
    rw [operation_f_apply, actual_operation_apply]
    rfl

/-- Independent fixed edge equalities force precisely the two correction masks. -/
theorem parameters_allowed {sheared : Bool} {S : Set (EdgeName (K := geometry))}
    (R : RealRepairs sheared S) : Allowed S (parameters R) := by
  constructor
  · intro hn
    have he : name edgeE ∈ fixedEdges S := by
      simp [fixedEdges, fixedRegion, candidates_all, hn]
    have h := congrArg (fun g : Op => g 0) (R.fixed_value (name edgeE) he)
    change R.operation (name edgeE).2.2 0 = reference sheared (name edgeE).2.2 0 at h
    rw [reference_zero] at h
    exact h
  · intro hn
    have he : name edgeF ∈ fixedEdges S := by
      simp [fixedEdges, fixedRegion, candidates_all, hn]
    have h := congrArg (fun g : Op => g 0) (R.fixed_value (name edgeF) he)
    change R.operation (name edgeF).2.2 0 = reference sheared (name edgeF).2.2 0 at h
    rw [reference_zero] at h
    exact h

/-- Each fixed original edge has exactly zero correction under the derived masks. -/
theorem correction_fixed (S : Set (EdgeName (K := geometry))) (p : Parameters)
    (hp : Allowed S p) (e : EdgeName (K := geometry)) (he : e ∈ fixedEdges S) :
    correctionValue p.1 p.2 e.2.2.1 = 0 := by
  have hn : e ∉ S := by simpa [fixedEdges, fixedRegion, candidates_all] using he
  rcases e with ⟨i,j,e,hs,ht⟩
  cases hs
  cases ht
  fin_cases e
  · exact hp.1 hn
  · exact hp.2 hn

/-- Every permitted full vector pair independently constructs its two actual repaired edges. -/
def fromParameters (sheared : Bool) (S : Set (EdgeName (K := geometry)))
    (p : Parameters) (hp : Allowed S p) : RealRepairs sheared S where
  operation := operation sheared p.1 p.2
  linear := operation_linear sheared p.1 p.2
  face f := f.elim
  fixed_value e he := by
    apply AffineEquiv.ext
    intro x
    change correctionValue p.1 p.2 e.2.2.1 + reference sheared e.2.2 x = _
    rw [correction_fixed S p hp e he, zero_add]

/-- Reading the restored actual operations recovers both entire correction vectors. -/
theorem parameters_from (sheared : Bool) (S : Set (EdgeName (K := geometry)))
    (p : Parameters) (hp : Allowed S p) : parameters (fromParameters sheared S p hp) = p := by
  apply Prod.ext
  · change operation sheared p.1 p.2 (name edgeE).2.2 0 = p.1
    rw [operation_zero]
    rfl
  · change operation sheared p.1 p.2 (name edgeF).2.2 0 = p.2
    rw [operation_zero]
    rfl

/-- All independent actual repairs and all masked vectors have exact object inverses. -/
def actualParametersEquiv (sheared : Bool) (S : Set (EdgeName (K := geometry))) :
    RealRepairs sheared S ≃ {p : Parameters // Allowed S p} where
  toFun R := ⟨parameters R, parameters_allowed R⟩
  invFun p := fromParameters sheared S p.1 p.2
  left_inv R := by
    apply NativeAffine.Repair.ext
    intro i j e
    exact congrFun (congrFun (congrFun (parameters_operations R) i) j) e
  right_inv p := Subtype.ext (parameters_from sheared S p.1 p.2)

/-- Both specified loop actions have exactly the same entire unrestricted vector span. -/
def unrestrictedParametersEquiv (sheared : Bool) : RealRepairs sheared candidates ≃ Parameters :=
  (actualParametersEquiv sheared candidates).trans {
    toFun := Subtype.val
    invFun := fun p => ⟨p, by simp [Allowed, candidates_all]⟩
    left_inv := fun p => Subtype.ext rfl
    right_inv := fun _ => rfl }

/-- Both actions have all 81 independent actual operation pairs. -/
theorem unrestricted_repair_card (sheared : Bool) :
    Nat.card (RealRepairs sheared candidates) = 81 := by
  calc
    Nat.card (RealRepairs sheared candidates) = Nat.card Parameters :=
      Nat.card_congr (unrestrictedParametersEquiv sheared)
    _ = 81 := by simp [Parameters, A, Nat.card_eq_fintype_card]

/-- The unchanged actual reference is a repair for every permission set. -/
def referenceRepair (sheared : Bool) (S : Set (EdgeName (K := geometry))) : RealRepairs sheared S where
  operation := reference sheared
  linear _ := rfl
  face f := f.elim
  fixed_value _ _ := rfl

/-- Empty permission retains one whole original actual object. -/
theorem empty_unique (sheared : Bool) (R : RealRepairs sheared ∅) :
    R = referenceRepair sheared ∅ := by
  apply NativeAffine.Repair.ext
  intro i j e
  exact R.fixed_value ⟨i,j,e⟩ (by rw [fixed_empty]; exact Set.mem_univ _)

/-- The entire empty-permission object family has point coordinates with both inverses. -/
def emptyObjectEquiv (sheared : Bool) : RealRepairs sheared ∅ ≃ Unit where
  toFun _ := ()
  invFun _ := referenceRepair sheared ∅
  left_inv R := (empty_unique sheared R).symm
  right_inv _ := rfl

/-- All original native objects and full gauge arrows correspond to independent actual repairs. -/
noncomputable def wholeAffineEquivalence (sheared : Bool) (S : Set (EdgeName (K := geometry))) :
    NativeCategory sheared S ≌ ActualCategory sheared S :=
  NativeAffine.groupoidEquivalence geometry (reference sheared) (reference sheared) comparison
    (linear_faces sheared) fixedRegion.vertices (fixedEdges S)

/-- Empty permission excludes a nonzero correction on the original forward edge. -/
theorem nonzero_forward_not_allowed :
    ¬ Allowed ∅ ((fun _ : Fin 2 => (1 : ZMod 3)), 0) := by
  intro h
  have hz := congrFun (h.1 (by simp)) (0 : Fin 2)
  norm_num at hz

end AAT.AG.RelativeRepairComposition.W3ActualRepairs
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.W3ActualRepairs
