import ResearchLean.AG.RepairObservationDuality.SelectedCokernel
import ResearchLean.AG.RelativeRepairComposition.OriginalRangeClassification

/-!
# G-131 A: actual repairs and each permitted native correction map

## Implementation notes

Each vertex coefficient is the arbitrary actual projection kernel of the
original tower. G-130 supplies the independent actual repair equivalence and
original split equation. Restoration preserves all edge values and fixed arrows.
The affine parameter family and numerical basis coordinates remain separate bridges.
-/

namespace AAT.AG.RepairObservationDuality.NativeCorrectionEquation
open CategoryTheory TransportCoherence AbelianLiftingObstruction TransportCoherence.Arbitrary
open RelativeRepairComposition FiniteCoefficients
set_option autoImplicit false
universe uk uG uE uB uD vE vB vD
variable {k : Type uk} [Field k]
variable {K : FiniteTransportPresentation.{uG}}
variable {E : Type uE} {B : Type uB} {D : Type uD}
variable [Category.{vE} E] [Category.{vB} B] [Category.{vD} D]
variable {p : E ⥤ B} {q : B ⥤ D}
variable (T : OriginalTowerPresentation K p q)
variable [∀ v, Module k ((T.toTower.localCoefficients).A v)]
variable (P : ClosedRegion K) (candidates : Set (EdgeName (K := K)))
variable [DecidablePred (· ∈ candidates)]
variable (houtside : ∀ e ∈ candidates, e ∉ P.edges)
variable (hlinear : ∀ {i j : K.Vertex} (e : K.Edge i j) (t : k)
  (x : (T.toTower.localCoefficients).A i),
  (T.toTower.localCoefficients).edge e (t • x) = t • (T.toTower.localCoefficients).edge e x)
variable [Fintype (EdgeName (K := K))] [DecidableEq (EdgeName (K := K))]
attribute [local instance] Classical.propDecidable
local notation "M" => T.toTower.localCoefficients
local notation "D₀" => OriginalColumns.D (k := k) M P candidates hlinear
local notation "C" => OriginalColumns.column (k := k) M P candidates houtside hlinear

/-- Full always cochains and whole selected candidate kernels on original names. -/
abbrev Values (S : Set candidates) :=
  OriginalColumns.alwaysSpace (k := k) M P candidates × (∀ e : S, (T.toTower.localCoefficients).A e.1.1.2.1)

/-- A's D_S is generated from the actual always differential and original columns. -/
noncomputable def differential (S : Set candidates) :
    Values (k := k) T P candidates S →ₗ[k] RelativeCover.C2 M ClosedRegion.all P :=
  SelectedCokernel.differential D₀ C S

/-- D_S evaluates the literal original split equation. -/
theorem differential_apply (S : Set candidates) (h : Values (k := k) T P candidates S) :
    differential (k := k) T P candidates houtside hlinear S h =
      D₀ h.1 + NamedDual.sumSelected C S h.2 :=
  SelectedCokernel.differential_apply D₀ C S h

/-- The full native cokernel is the original always quotient modulo the exact
selected range; vertex modules need not coincide. -/
noncomputable def cokernelEquiv (S : Set candidates) :
    (RelativeCover.C2 M ClosedRegion.all P ⧸
      LinearMap.range (differential (k := k) T P candidates houtside hlinear S)) ≃ₗ[k]
      (OriginalRanges.ObstructionSpace (k := k) M P candidates hlinear ⧸
        NamedDual.ranges (OriginalRanges.column (k := k) M P candidates houtside hlinear) S) :=
  SelectedCokernel.nativeToResidual D₀ C S

/-- The quotient comparison preserves the complete same original face representative. -/
theorem cokernelEquiv_value (S : Set candidates) (r : RelativeCover.C2 M ClosedRegion.all P) :
    cokernelEquiv (k := k) T P candidates houtside hlinear S
      ((LinearMap.range (differential (k := k) T P candidates houtside hlinear S)).mkQ r) =
      (NamedDual.ranges (OriginalRanges.column (k := k) M P candidates houtside hlinear) S).mkQ
        (LinearInterface.q D₀ r) :=
  SelectedCokernel.nativeToResidual_value D₀ C S r

variable (hfixed : ∀ f ∈ P.faces,
  T.toTower.upper.pathLift (K.twoLeft f) ≫ FiberAut.hom (T.comparator f) =
    T.toTower.upper.pathLift (K.twoRight f))
local notation "δ" => ActualEquation.defectFamily T P hfixed

/-- Independent actual repairs exist exactly at solutions of the generated D_S
with the negative defect of the same actual paths. -/
theorem actual_equation_iff (S : Set candidates) :
    Nonempty (SupportedRepair T
      (fixedEdgesForRange P.edges candidates (OriginalRanges.allowed candidates S))) ↔
      ∃ h, differential (k := k) T P candidates houtside hlinear S h = -δ :=
  (SupportedNativeEquation.repairEquiv T P candidates (OriginalRanges.allowed candidates S)
    hfixed).nonempty_congr.trans
      ((OriginalRanges.objects_nonempty_iff_equation (k := k) M P candidates houtside
        hlinear δ S).trans (SelectedCokernel.equation_iff D₀ C S (-δ)))

/-- The independent actual repair predicate is zero of this same full native cokernel. -/
theorem actual_cokernel_iff (S : Set candidates) :
    Nonempty (SupportedRepair T
      (fixedEdgesForRange P.edges candidates (OriginalRanges.allowed candidates S))) ↔
      (LinearMap.range (differential (k := k) T P candidates houtside hlinear S)).mkQ (-δ) = 0 :=
  (actual_equation_iff (k := k) T P candidates houtside hlinear hfixed S).trans
    (SelectedCokernel.equation_iff_zero D₀ C S (-δ))

/-- Restore the supplied full coefficient solution to the same actual repair,
retaining all original candidate names and fixed arrows. -/
noncomputable def restore (S : Set candidates) (h : Values (k := k) T P candidates S)
    (hh : differential (k := k) T P candidates houtside hlinear S h = -δ) :
    SupportedRepair T
      (fixedEdgesForRange P.edges candidates (OriginalRanges.allowed candidates S)) :=
  (SupportedNativeEquation.repairEquiv T P candidates (OriginalRanges.allowed candidates S)
    hfixed).symm
      (OriginalRanges.restore (k := k) M P candidates houtside hlinear δ S h.1 h.2
        ((differential_apply (k := k) T P candidates houtside hlinear S h).symm.trans hh))

/-- Each restored actual edge has its whole always value plus the zero-extended
selected value at the same original edge name. -/
theorem restore_value (S : Set candidates) (h : Values (k := k) T P candidates S)
    (hh : differential (k := k) T P candidates houtside hlinear S h = -δ)
    (e : EdgeName (K := K)) :
    T.solutionCorrection (restore (k := k) T P candidates houtside hlinear hfixed S h hh).1 e =
      h.1.1.1 ⟨e, Set.mem_univ e⟩ +
        (OriginalRanges.selectedCorrection (k := k) M P candidates houtside S h.2).1
          ⟨e, Set.mem_univ e⟩ := by
  exact SupportedNativeEquation.repair_inverse_value T P candidates
    (OriginalRanges.allowed candidates S) hfixed _ e

/-- Every forbidden original candidate restores to zero full correction. -/
theorem restore_forbidden_zero (S : Set candidates) (h : Values (k := k) T P candidates S)
    (hh : differential (k := k) T P candidates houtside hlinear S h = -δ)
    (e : candidates) (he : e ∉ S) :
    T.solutionCorrection (restore (k := k) T P candidates houtside hlinear hfixed S h hh).1 e.1 = 0 := by
  rw [restore_value, h.1.2 e,
    OriginalRanges.selected_zero (k := k) M P candidates houtside S h.2 e he, zero_add]

/-- Restored actual morphisms retain every P arrow and every forbidden candidate arrow. -/
theorem restore_fixed_arrow (S : Set candidates) (h : Values (k := k) T P candidates S)
    (hh : differential (k := k) T P candidates houtside hlinear S h = -δ)
    (e : EdgeName (K := K))
    (he : e ∈ fixedEdgesForRange P.edges candidates (OriginalRanges.allowed candidates S)) :
    (selectedUpper K p q T.original
      (restore (k := k) T P candidates houtside hlinear hfixed S h hh).1.choice).edgeLift e.2.2 =
      T.toTower.upper.edgeLift e.2.2 :=
  (restore (k := k) T P candidates houtside hlinear hfixed S h hh).2 e he

end AAT.AG.RepairObservationDuality.NativeCorrectionEquation
#assert_standard_axioms_only AAT.AG.RepairObservationDuality.NativeCorrectionEquation
