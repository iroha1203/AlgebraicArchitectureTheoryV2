import ResearchLean.AG.RepairObservationDuality.ActualAffineFamily
import ResearchLean.AG.RepairObservationDuality.LinearObservationDuality
import ResearchLean.AG.RepairObservationDuality.PointQuerySimulation
import ResearchLean.AG.RepairObservationDuality.PrimitiveInputQueries
import ResearchLean.AG.RepairObservationDuality.PrimitiveReplyTranslation

/-!
# G-131 B: observation of the same original repair predicate

A successful original input supplies the translation origin. The residual
map is built from the same whole correction differential and the negative
primitive-generated defect. Every translated parameter is realized by the
original family; the predicate remains original supported repair existence.

## Implementation notes

The independent original SupportedRepair predicate retains the physical
repair obligation. Replacing it by a kernel-membership definition would
assume the bridge that this module constructs.

-/
namespace AAT.AG.RepairObservationDuality.ActualObservationPredicate
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary
open AbelianLiftingObstruction RelativeRepairComposition PrimitiveAffineDefect
set_option autoImplicit false
universe uk uV uF uG uE uB uD vE vB vD
variable {k : Type uk} [Field k]
variable {V : Type uV} [AddCommGroup V] [Module k V]
variable {F : Type uF}
variable {K : FiniteTransportPresentation.{uG}}
variable {E : Type uE} {B : Type uB} {D : Type uD}
variable [Category.{vE} E] [Category.{vB} B] [Category.{vD} D]
variable {p : E ⥤ B} {q : B ⥤ D}
variable (T : TowerPresentation K p q)
variable [∀ v, Module k ((T.localCoefficients).A v)]
variable (edgeChange : V →ₗ[k] (C1 (T.localCoefficients)))
variable (comparisonChange : V →ₗ[k] (C2 (T.localCoefficients)))
variable (input : F → OriginalTowerPresentation K p q) (ν : F → V)
variable (hdata : ∀ X : F, (input X).toTower.toTransportData =
  data T (edgeChange (ν X)) (comparisonChange (ν X)))

variable (realize : V → F) (hrealize : ∀ v, ν (realize v) = v)
variable (P : ClosedRegion K)
variable (hfixed : ∀ X : F, ∀ f ∈ P.faces,
  (input X).toTower.upper.pathLift (K.twoLeft f) ≫
    FiberAut.hom ((input X).comparator f) =
  (input X).toTower.upper.pathLift (K.twoRight f))
variable (hlinear : ∀ {i j : K.Vertex} (e : K.Edge i j) (t : k)
  (x : (T.localCoefficients).A i),
  (T.localCoefficients).edge e (t • x) = t • (T.localCoefficients).edge e x)
variable (candidates : Set (EdgeName (K := K))) [DecidablePred (· ∈ candidates)]
variable (houtside : ∀ e ∈ candidates, e ∉ P.edges)
variable [Fintype (EdgeName (K := K))] [DecidableEq (EdgeName (K := K))]
attribute [local instance] Classical.propDecidable
local notation "D₀" => OriginalColumns.D (k := k) T.localCoefficients P candidates hlinear
local notation "C" => OriginalColumns.column (k := k) T.localCoefficients P candidates houtside hlinear
local notation "fixed" => ActualAffineFamily.model_fixed T edgeChange comparisonChange input ν hdata realize hrealize P hfixed
local notation "b₀" => RelativeAffineDefect.baseRhs T edgeChange comparisonChange P fixed
local notation "B₀" => RelativeAffineDefect.rhsLinear T hlinear edgeChange comparisonChange P fixed
local notation "DS" => SelectedCokernel.differential D₀ C
local notation "R[" S "]" => LinearMap.ker (LinearMap.comp (Submodule.mkQ (LinearMap.range (DS S))) B₀)
include hdata hrealize hfixed

/-- G-131 B / n1017 §6: the same original repair predicate translates to the same residual kernel. -/
theorem repair_shift (S : Set candidates) (base X : F)
    (hs : Nonempty (SupportedRepair (input base)
      (fixedEdgesForRange P.edges candidates (OriginalRanges.allowed candidates S))))
    (n : V) (he : ν X = ν base + n) :
    Nonempty (SupportedRepair (input X)
      (fixedEdgesForRange P.edges candidates (OriginalRanges.allowed candidates S))) ↔ n ∈ R[S] := by
  have hb := (ActualAffineFamily.actual_affine_equation_iff T edgeChange comparisonChange input ν
    hdata realize hrealize P hfixed hlinear candidates houtside base S).mp hs
  rw [ActualAffineFamily.actual_affine_equation_iff T edgeChange comparisonChange input ν
    hdata realize hrealize P hfixed hlinear candidates houtside X S, he]
  exact solvable_add_iff (DS S) B₀ b₀ hb n

/-- G-131 B / n1017 §6: every translated vector has an actual original input with that repair predicate. -/
theorem repair_realize_shift (S : Set candidates) (base : F)
    (hs : Nonempty (SupportedRepair (input base)
      (fixedEdgesForRange P.edges candidates (OriginalRanges.allowed candidates S)))) (n : V) :
    Nonempty (SupportedRepair (input (realize (ν base + n)))
      (fixedEdgesForRange P.edges candidates (OriginalRanges.allowed candidates S))) ↔ n ∈ R[S] :=
  repair_shift T edgeChange comparisonChange input ν hdata realize hrealize P hfixed hlinear
    candidates houtside S base _ hs n (hrealize _)

variable {J : Type*} (lam : J → V →ₗ[k] k)

/-- G-131 B / n1017 §6: observation factors actual repair exactly at the stated kernel inclusion. -/
theorem observation_predicate_iff (S : Set candidates) (base : F)
    (hs : Nonempty (SupportedRepair (input base)
      (fixedEdgesForRange P.edges candidates (OriginalRanges.allowed candidates S)))) (points : Finset J) :
    (∃ p : (points → k) → Prop, ∀ n : V, p (observation lam points n) ↔
      Nonempty (SupportedRepair (input (realize (ν base + n)))
        (fixedEdgesForRange P.edges candidates (OriginalRanges.allowed candidates S)))) ↔
      LinearMap.ker (observation lam points) ≤ R[S] := by
  simpa only [repair_realize_shift T edgeChange comparisonChange input ν hdata realize hrealize P
    hfixed hlinear candidates houtside S base hs] using
    LinearObservationDuality.predicate_iff (observation lam points) R[S]

/-- G-131 B / n1017 §6: an actual Boolean repair indicator factors through the identical primitive table. -/
theorem observation_decision_iff (S : Set candidates) (base : F)
    (hs : Nonempty (SupportedRepair (input base)
      (fixedEdgesForRange P.edges candidates (OriginalRanges.allowed candidates S)))) (points : Finset J) :
    (∃ f : (points → k) → Bool, ∀ n : V, f (observation lam points n) = true ↔
      Nonempty (SupportedRepair (input (realize (ν base + n)))
        (fixedEdgesForRange P.edges candidates (OriginalRanges.allowed candidates S)))) ↔
      LinearMap.ker (observation lam points) ≤ R[S] := by
  simpa only [repair_realize_shift T edgeChange comparisonChange input ν hdata realize hrealize P
    hfixed hlinear candidates houtside S base hs] using
    LinearObservationDuality.decision_iff (observation lam points) R[S]

/-- G-131 B / n1017 §6: actual repair factorization has precisely the primitive span dual condition. -/
theorem observation_predicate_dual_iff [FiniteDimensional k V] (S : Set candidates) (base : F)
    (hs : Nonempty (SupportedRepair (input base)
      (fixedEdgesForRange P.edges candidates (OriginalRanges.allowed candidates S)))) (points : Finset J) :
    (∃ p : (points → k) → Prop, ∀ n : V, p (observation lam points n) ↔
      Nonempty (SupportedRepair (input (realize (ν base + n)))
        (fixedEdgesForRange P.edges candidates (OriginalRanges.allowed candidates S)))) ↔
      (R[S]).dualAnnihilator ≤ LinearObservationDuality.evaluationSpan lam points := by
  rw [observation_predicate_iff T edgeChange comparisonChange input ν hdata realize hrealize P
    hfixed hlinear candidates houtside lam S base hs]
  exact LinearObservationDuality.kernel_iff_dual lam points R[S]

/-- G-131 B / n1017 §6: G-128's arbitrary-offset table factors the identical original repair predicate. -/
theorem point_predicate_iff [DecidableEq J] (S : Set candidates) (base : F)
    (hs : Nonempty (SupportedRepair (input base)
      (fixedEdgesForRange P.edges candidates (OriginalRanges.allowed candidates S))))
    (points : Finset (J × k)) :
    letI := AdditiveObservationAction.action lam;
    (∃ p : (points → J × k) → Prop, ∀ n : Multiplicative V,
      p (MinimalCompatibilityObservations.observe points n) ↔
      Nonempty (SupportedRepair (input (realize (ν base + n.toAdd)))
        (fixedEdgesForRange P.edges candidates (OriginalRanges.allowed candidates S)))) ↔
      LinearMap.ker (observation lam (AdditiveObservationAction.indices points)) ≤ R[S] := by
  letI := AdditiveObservationAction.action lam
  simpa only [repair_realize_shift T edgeChange comparisonChange input ν hdata realize hrealize P
    hfixed hlinear candidates houtside S base hs] using
    AdditiveObservationAction.predicate_iff lam R[S] points

/-- G-131 B / n1017 §6: the quotient dual is built from the same actual residual repair kernel. -/
noncomputable def repairQuotientDual (S : Set candidates) :
    Module.Dual k (V ⧸ R[S]) ≃ₗ[k] (R[S]).dualAnnihilator := LinearObservationDuality.quotientDual R[S]

/-- G-131 B / n1017 §6 API: the actual repair quotient dual preserves every parameter evaluation. -/
theorem repairQuotientDual_apply (S : Set candidates) (f : Module.Dual k (V ⧸ R[S])) (n : V) :
    (repairQuotientDual T edgeChange comparisonChange input ν hdata realize hrealize P hfixed
      hlinear candidates houtside S f).1 n = f ((R[S]).mkQ n) := rfl

/-- G-131 B / n1017 §6: the effective quotient is the residual image of the same original D_S and B. -/
noncomputable def repairQuotientImage (S : Set candidates) :
    (V ⧸ R[S]) ≃ₗ[k] LinearMap.range ((LinearMap.range (DS S)).mkQ.comp B₀) :=
  LinearObservationDuality.quotientImage ((LinearMap.range (DS S)).mkQ.comp B₀)

/-- G-131 B / n1017 §6: the residual-image inclusion preserves the original obstruction class. -/
theorem repairQuotientImage_apply (S : Set candidates) (n : V) :
    (repairQuotientImage T edgeChange comparisonChange input ν hdata realize hrealize P hfixed
      hlinear candidates houtside S ((R[S]).mkQ n)).1 = (LinearMap.range (DS S)).mkQ (B₀ n) :=
  LinearObservationDuality.quotientImage_apply _ n

/-- G-131 B / n1017 §6: every original input uses its exact difference from the successful origin. -/
theorem repair_difference (S : Set candidates) (base X : F)
    (hs : Nonempty (SupportedRepair (input base)
      (fixedEdgesForRange P.edges candidates (OriginalRanges.allowed candidates S)))) :
    Nonempty (SupportedRepair (input X)
      (fixedEdgesForRange P.edges candidates (OriginalRanges.allowed candidates S))) ↔
      ν X - ν base ∈ R[S] :=
  repair_shift T edgeChange comparisonChange input ν hdata realize hrealize P hfixed hlinear
    candidates houtside S base X hs (ν X - ν base) (by abel)

variable (actual : F → J → k) (heval : ∀ X j, actual X j = lam j (ν X))
include heval

/-- G-131 B / n1017 §6: the optimal actual primitive decision cost equals G-128's arbitrary-point cost. -/
theorem actual_optimum_eq_point (S : Set candidates) (base : F)
    (hs : Nonempty (SupportedRepair (input base)
      (fixedEdgesForRange P.edges candidates (OriginalRanges.allowed candidates S)))) :
    letI := AdditiveObservationAction.action lam;
    PrimitiveQueries.optimum actual Set.univ (fun X a => a = true ↔
      Nonempty (SupportedRepair (input X)
        (fixedEdgesForRange P.edges candidates (OriginalRanges.allowed candidates S)))) =
      MinimalCompatibilityObservations.optimalQueries (X := J × k)
        (AdditiveObservationAction.compatible R[S]) := by
  letI := AdditiveObservationAction.action lam
  let shifted : F → J → k := fun X j => actual X j - lam j (ν base)
  let shiftedν : F → V := fun X => ν X - ν base
  let shiftedRealize : V → F := fun n => realize (ν base + n)
  have hr : ∀ n, shiftedν (shiftedRealize n) = n := by
    intro n
    simp only [shiftedν, shiftedRealize, hrealize, add_sub_cancel_left]
  have he : ∀ X j, shifted X j = PointQuerySimulation.evaluation lam (shiftedν X) j := by
    intro X j
    simp only [shifted, shiftedν, heval, PointQuerySimulation.evaluation, map_sub]
  have hv : (fun X a => a = true ↔ Nonempty (SupportedRepair (input X)
      (fixedEdgesForRange P.edges candidates (OriginalRanges.allowed candidates S)))) =
      (fun X a => a = true ↔ shiftedν X ∈ R[S]) := by
    funext X a
    rw [repair_difference T edgeChange comparisonChange input ν hdata realize hrealize P hfixed
      hlinear candidates houtside S base X hs]
  rw [hv]
  have ht := PrimitiveReplyTranslation.optimum_eq actual shifted (fun j => lam j (ν base))
    (fun X j => by dsimp [shifted]; abel) Set.univ (fun X a => a = true ↔ shiftedν X ∈ R[S])
  rw [← ht]
  have hi := PrimitiveInputQueries.optimum_eq shiftedν shiftedRealize hr shifted
    (PointQuerySimulation.evaluation lam) he Set.univ (fun n a => a = true ↔ n ∈ R[S])
  simpa only [Set.preimage_univ] using hi.trans (PointQuerySimulation.optimum_eq lam R[S])

/-- G-131 B / n1017 §6: actual always-correct decisions have the stated minimum original-index cost. -/
theorem actual_optimum_eq_minimum [DecidableEq J] (S : Set candidates) (base : F)
    (hs : Nonempty (SupportedRepair (input base)
      (fixedEdgesForRange P.edges candidates (OriginalRanges.allowed candidates S)))) :
    PrimitiveQueries.optimum actual Set.univ (fun X a => a = true ↔
      Nonempty (SupportedRepair (input X)
        (fixedEdgesForRange P.edges candidates (OriginalRanges.allowed candidates S)))) =
      minimum lam (0 : V →ₗ[k] k) R[S] := by
  classical
  letI := AdditiveObservationAction.action lam
  rw [actual_optimum_eq_point T edgeChange comparisonChange input ν hdata realize hrealize P hfixed
    hlinear candidates houtside lam actual heval S base hs,
    MinimalCompatibilityObservations.optimalQueries_eq_minObservations,
    AdditiveObservationAction.minimum_eq lam R[S]]

/-- G-131 B / n1017 §6: absence of every sufficient primitive set gives infinite actual optimum. -/
theorem actual_optimum_eq_top_iff [DecidableEq J] (S : Set candidates) (base : F)
    (hs : Nonempty (SupportedRepair (input base)
      (fixedEdgesForRange P.edges candidates (OriginalRanges.allowed candidates S)))) :
    PrimitiveQueries.optimum actual Set.univ (fun X a => a = true ↔
      Nonempty (SupportedRepair (input X)
        (fixedEdgesForRange P.edges candidates (OriginalRanges.allowed candidates S)))) = ⊤ ↔
      ¬ ∃ points : Finset J, LinearMap.ker (observation lam points) ≤ R[S] := by
  rw [actual_optimum_eq_minimum T edgeChange comparisonChange input ν hdata realize hrealize P hfixed
    hlinear candidates houtside lam actual heval S base hs, minimum_eq_top_iff]
  simp only [sufficientSet_zero_iff]

omit heval hdata hrealize hfixed [Field k] [DecidablePred (· ∈ candidates)]
    [Fintype (EdgeName (K := K))] [DecidableEq (EdgeName (K := K))] in
/-- G-131 B / n1017 §6: an entirely impossible original family has a correct zero-query decision. -/
theorem actual_optimum_zero (S : Set candidates)
    (hn : ∀ X : F, ¬ Nonempty (SupportedRepair (input X)
      (fixedEdgesForRange P.edges candidates (OriginalRanges.allowed candidates S)))) :
    PrimitiveQueries.optimum actual Set.univ (fun X a => a = true ↔
      Nonempty (SupportedRepair (input X)
        (fixedEdgesForRange P.edges candidates (OriginalRanges.allowed candidates S)))) = 0 := by
  apply PrimitiveQueries.optimum_zero_of_constant _ _ _ false
  intro X _
  exact iff_of_false Bool.false_ne_true (hn X)

end AAT.AG.RepairObservationDuality.ActualObservationPredicate
#assert_standard_axioms_only AAT.AG.RepairObservationDuality.ActualObservationPredicate
