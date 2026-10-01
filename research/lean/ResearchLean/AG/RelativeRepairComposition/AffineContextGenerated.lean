import ResearchLean.AG.RelativeRepairComposition.AffineContextEquivalence
import ResearchLean.AG.RelativeRepairComposition.AffineSharedCoordinates
import ResearchLean.AG.RelativeRepairComposition.AffineGeneratedBoundary

/-!
# The same generated public C is the original contextual boundary relation

Private elimination uses only nonshared always edges. All candidates remain
public until their zero conditions are imposed; shared projection then removes
the internal candidates. Pullback is bijective on the full named shared edge
coordinates. Enumerations and the generated section are independent of S.
-/
namespace AAT.AG.RelativeRepairComposition.NativeAffine.AffineContextInput
open TransportCoherence AbelianLiftingObstruction
universe uk uG
variable {k : Type uk} [Field k] [Fintype k] [DecidableEq k] {d : Nat}
variable {W : FiniteTransportPresentation.{uG}}
variable {LW RW : ∀ {i j : W.Vertex}, W.Edge i j → Operations k (Fin d → k)}
variable {cW : W.TwoCell → (Fin d → k)} {PW : ClosedRegion W} {CW : Set (EdgeName (K := W))}
variable (I : AffineContextInput W LW RW cW PW CW)
variable [DecidablePred (· ∈ I.fixed.edges)] [DecidablePred (· ∈ I.fixed.faces)]
variable [DecidablePred (· ∈ I.shared.edges)] [DecidablePred (· ∈ I.candidates)]
variable [DecidableEq (EdgeName (K := I.geometry))] [DecidableEq I.geometry.TwoCell]
variable (ek : FiniteElimination.Enumeration k)
variable (ee : FiniteElimination.Enumeration (EdgeName (K := I.geometry)))
variable (ef : FiniteElimination.Enumeration I.geometry.TwoCell)

/-- C after all candidate zero equations and internal-candidate elimination, in complete original W coordinates. -/
def generatedShared {S : Set (EdgeName (K := W))} (a : I.Range S) :
    Set (EdgeName (K := W) → (Fin d → k)) :=
  I.pullShared '' generatedBoundary d I.geometry I.originals I.references I.comparisons
    I.aligned I.fixed I.shared I.candidates I.fixed_faces ek ee ef a.allowed

/-- The same generated C is exactly the whole actual shared repair range for every compatible permission. -/
theorem generated_shared_actual {S : Set (EdgeName (K := W))} (a : I.Range S) :
    I.generatedShared ek ee ef a = Set.range (I.boundary a) := by
  unfold generatedShared
  rw [generated_boundary_actual,← Set.range_comp]
  congr 1
  funext s e
  exact (I.boundary_value a s e).symm

variable (J : AffineContextInput W LW RW cW PW CW)
variable [DecidablePred (· ∈ J.fixed.edges)] [DecidablePred (· ∈ J.fixed.faces)]
variable [DecidablePred (· ∈ J.shared.edges)] [DecidablePred (· ∈ J.candidates)]
variable [DecidableEq (EdgeName (K := J.geometry))] [DecidableEq J.geometry.TwoCell]
variable (ej : FiniteElimination.Enumeration (EdgeName (K := J.geometry)))
variable (fj : FiniteElimination.Enumeration J.geometry.TwoCell)

/-- All actual external environments have identical strict repair-existence outcomes exactly
when the same full generated C relations agree after candidate zero and shared projection. -/
theorem contextual_generated {S : Set (EdgeName (K := W))} (a : I.Range S) (b : J.Range S) :
    (∀ env : Environments (W := W) (LW := LW) (RW := RW) (cW := cW) (PW := PW) (CW := CW) S,
      Nonempty (ContextRelations.StrictJoin (I.boundary a) (env.1.boundary env.2)) ↔
        Nonempty (ContextRelations.StrictJoin (J.boundary b) (env.1.boundary env.2))) ↔
      I.generatedShared ek ee ef a = J.generatedShared ek ej fj b := by
  rw [generated_shared_actual,generated_shared_actual]
  exact I.contextual_actual_ranges J a b

/-- Simultaneous generated-C equality is the contextual existence criterion for all shared S,
using one original generator and section in each region. -/
theorem contextual_generated_all
    (a : ∀ S : Set (EdgeName (K := W)), I.Range S)
    (b : ∀ S : Set (EdgeName (K := W)), J.Range S) :
    (∀ S, ∀ env : Environments (W := W) (LW := LW) (RW := RW) (cW := cW) (PW := PW) (CW := CW) S,
      Nonempty (ContextRelations.StrictJoin (I.boundary (a S)) (env.1.boundary env.2)) ↔
        Nonempty (ContextRelations.StrictJoin (J.boundary (b S)) (env.1.boundary env.2))) ↔
      ∀ S, I.generatedShared ek ee ef (a S) = J.generatedShared ek ej fj (b S) := by
  constructor
  · intro h S
    exact (I.contextual_generated ek ee ef J ej fj (a S) (b S)).mp (h S)
  · intro h S
    exact (I.contextual_generated ek ee ef J ej fj (a S) (b S)).mpr (h S)

end AAT.AG.RelativeRepairComposition.NativeAffine.AffineContextInput
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.NativeAffine.AffineContextInput
