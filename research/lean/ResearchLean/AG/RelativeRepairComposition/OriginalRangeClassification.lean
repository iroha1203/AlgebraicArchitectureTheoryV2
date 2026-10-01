import ResearchLean.AG.RelativeRepairComposition.OriginalRangeEquations
import ResearchLean.AG.RelativeRepairComposition.SupportedNativeEquation

/-!
# All original actual repair ranges and their minimal dual transversals

The same independently defined actual supported repairs are used throughout.
No linear solution, separating certificate or obstruction vanishing is assumed.
-/
namespace AAT.AG.RelativeRepairComposition
open CategoryTheory TransportCoherence AbelianLiftingObstruction TransportCoherence.Arbitrary
universe uk uG uE uB uD vE vB vD
namespace OriginalRangeClassification
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
variable (hfixed : ∀ f ∈ P.faces,
  T.toTower.upper.pathLift (K.twoLeft f) ≫ FiberAut.hom (T.comparator f) =
    T.toTower.upper.pathLift (K.twoRight f))
local notation "M" => T.toTower.localCoefficients
local notation "delta" => ActualEquation.defectFamily T P hfixed
local notation "D0" => OriginalColumns.D (k := k) M P candidates hlinear
local notation "Bcol" => OriginalRanges.column (k := k) M P candidates houtside hlinear
local notation "obs" => LinearInterface.q D0 (-delta)

/-- The class is obtained from the same actual defect by the original always quotient. -/
noncomputable def obstruction := LinearInterface.q D0 (-ActualEquation.defectFamily T P hfixed)

/-- Original actual repairs exist exactly in the full selected candidate range. -/
theorem repair_nonempty_iff_range (S : Set candidates) :
    Nonempty (SupportedRepair T (fixedEdgesForRange P.edges candidates (OriginalRanges.allowed candidates S))) ↔
      obs ∈ NamedDual.ranges Bcol S :=
  (SupportedNativeEquation.repairEquiv T P candidates (OriginalRanges.allowed candidates S) hfixed).nonempty_congr.trans
    (OriginalRanges.objects_nonempty_iff_range (k := k) M P candidates houtside hlinear delta S)

/-- The same all-S actual repair existence is equivalent to full quotient-dual hitting. -/
theorem repair_nonempty_iff_hits (S : Set candidates) :
    Nonempty (SupportedRepair T (fixedEdgesForRange P.edges candidates (OriginalRanges.allowed candidates S))) ↔
      NamedDual.Hits Bcol obs S :=
  (repair_nonempty_iff_range (k := k) T P candidates houtside hlinear hfixed S).trans
    (NamedDual.mem_ranges_iff_hits Bcol obs S)

/-- Inclusion-minimal actual repair ranges are precisely the minimal obstruction-support transversals. -/
theorem minimal_repair_iff (S : Set candidates) :
    Minimal (fun V => Nonempty (SupportedRepair T
      (fixedEdgesForRange P.edges candidates (OriginalRanges.allowed candidates V)))) S ↔
        Minimal (NamedDual.Hits Bcol obs) S := by
  constructor
  · rintro ⟨hs,hm⟩
    exact ⟨(repair_nonempty_iff_hits (k := k) T P candidates houtside hlinear hfixed S).mp hs,
      fun V hv hvs => hm
        ((repair_nonempty_iff_hits (k := k) T P candidates houtside hlinear hfixed V).mpr hv) hvs⟩
  · rintro ⟨hs,hm⟩
    exact ⟨(repair_nonempty_iff_hits (k := k) T P candidates houtside hlinear hfixed S).mpr hs,
      fun V hv hvs => hm
        ((repair_nonempty_iff_hits (k := k) T P candidates houtside hlinear hfixed V).mp hv) hvs⟩

/-- Minimal actual repair ranges are also minimal membership ranges of the same obstruction. -/
theorem minimal_repair_iff_range (S : Set candidates) :
    Minimal (fun V => Nonempty (SupportedRepair T
      (fixedEdgesForRange P.edges candidates (OriginalRanges.allowed candidates V)))) S ↔
        Minimal (fun V => obs ∈ NamedDual.ranges Bcol V) S := by
  simp only [Minimal,repair_nonempty_iff_range (k := k) T P candidates houtside hlinear hfixed]

include houtside in
/-- At zero original obstruction the empty range is the unique minimal actual repair range. -/
theorem minimal_zero_iff (hzero : obs = 0) (S : Set candidates) :
    Minimal (fun V => Nonempty (SupportedRepair T
      (fixedEdgesForRange P.edges candidates (OriginalRanges.allowed candidates V)))) S ↔ S = ∅ := by
  rw [minimal_repair_iff_range (k := k) T P candidates houtside hlinear hfixed,hzero]
  exact NamedDual.minimal_zero_iff Bcol S

/-- Every failed actual range has a dual nonzero on the same obstruction and zero on every allowed column. -/
theorem failed_repair_dual (S : Set candidates)
    (h : ¬ Nonempty (SupportedRepair T
      (fixedEdgesForRange P.edges candidates (OriginalRanges.allowed candidates S)))) :
    ∃ phi : Module.Dual k (OriginalRanges.ObstructionSpace (k := k) M P candidates hlinear),
      phi obs ≠ 0 ∧ ∀ e ∈ S, phi.comp (Bcol e) = 0 :=
  NamedDual.failure_witness Bcol obs S
    (fun hm => h ((repair_nonempty_iff_range (k := k) T P candidates houtside hlinear hfixed S).mpr hm))

/-- Failure with every original candidate allowed yields an empty obstruction support. -/
theorem impossible_dual_empty
    (h : ¬ Nonempty (SupportedRepair T
      (fixedEdgesForRange P.edges candidates (OriginalRanges.allowed candidates Set.univ)))) :
    ∃ phi : Module.Dual k (OriginalRanges.ObstructionSpace (k := k) M P candidates hlinear),
      phi obs ≠ 0 ∧ NamedDual.support Bcol phi = ∅ :=
  NamedDual.impossible_empty_support Bcol obs
    (fun hm => h ((repair_nonempty_iff_range (k := k) T P candidates houtside hlinear hfixed Set.univ).mpr hm))

/-- The empty support obtained from failure excludes every possible transversal. -/
theorem impossible_no_transversal
    (h : ¬ Nonempty (SupportedRepair T
      (fixedEdgesForRange P.edges candidates (OriginalRanges.allowed candidates Set.univ)))) :
    ∀ S, ¬ NamedDual.Hits Bcol obs S := by
  obtain ⟨phi,hphi,hs⟩ := impossible_dual_empty (k := k) T P candidates houtside hlinear hfixed h
  exact NamedDual.no_transversal_of_empty_support Bcol obs phi hphi hs

end OriginalRangeClassification
end AAT.AG.RelativeRepairComposition
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
