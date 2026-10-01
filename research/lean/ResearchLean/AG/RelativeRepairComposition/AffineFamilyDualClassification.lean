import ResearchLean.AG.RelativeRepairComposition.AffineFamilyNativeEquation
import ResearchLean.AG.RelativeRepairComposition.OriginalRangeClassification

/-!
# Primitive affine values use the same original all-range quotient and duals

## Implementation notes

The always differential and every named candidate column are generated from the
unchanged original full kernel system. Only the quotient class of the actual
input-generated defect varies. The independent actual repair correspondence
transfers the accepted all-range and dual separation theorems to each parameter.
-/
namespace AAT.AG.RelativeRepairComposition.NativeAffine
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
universe uk uA uG uV
variable {k : Type uk} [Field k] {A : Type uA} [AddCommGroup A] [Module k A]
variable {V : Type uV} [AddCommGroup V] [Module k V]
variable (K : FiniteTransportPresentation.{uG})
variable (L R : ∀ {i j : K.Vertex}, K.Edge i j → Operations k A)
variable (c : K.TwoCell → A)
variable (θL θR : V →ₗ[k] (EdgeName (K := K) → A)) (η : V →ₗ[k] (K.TwoCell → A))
variable (hf : ∀ f : K.TwoCell,
  (GroupExtension.pathValue K R (K.twoLeft f)).linear =
    (GroupExtension.pathValue K R (K.twoRight f)).linear)
local notation "M" => TowerPresentation.localCoefficients (OriginalTowerPresentation.toTower (tower K L R c hf))
local notation "Tv" v => familyTower K L R c θL θR η hf v
local notation "Mv" v => TowerPresentation.localCoefficients (OriginalTowerPresentation.toTower (Tv v))
variable (P : ClosedRegion K)

variable (hB : ∀ v : V, ∀ f ∈ P.faces, familyDefectLinear K R θR η v f = 0)
variable (hfixed : ∀ f ∈ P.faces,
  translation (k := k) (c f) * GroupExtension.pathValue K R (K.twoLeft f) =
    GroupExtension.pathValue K R (K.twoRight f))
variable (candidates : Set (EdgeName (K := K))) [DecidablePred (· ∈ candidates)]
variable (houtside : ∀ e ∈ candidates, e ∉ P.edges)
variable [Fintype (EdgeName (K := K))] [DecidableEq (EdgeName (K := K))]
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
local notation "δ₀" => ActualEquation.defectFamily (tower K L R c hf) P (fixed_native K L R c hf P hfixed)
local notation "Δ" => familyRelativeLinear K L R c θR η hf P hB
local notation "δ" v => SymbolicNativeLocal.defectFamily (M) P δ₀ Δ v
local notation "lin" => edge_linear K L R c hf
local notation "D₀" => OriginalColumns.D (k := k) (M) P candidates lin
local notation "Bcol" => OriginalRanges.column (k := k) (M) P candidates houtside lin
local notation "o" v => LinearInterface.q (D₀) (-(δ v))
local notation "allowed" S => OriginalRanges.allowed candidates S
local notation "hfixedv" v => fixed_native K (familyOriginal K L θL v) (familyReference K R θR v)
  (familyComparisons K c η v) (family_aligned K R θR hf v) P
  (family_fixed_face K R c θR η hf P.faces hfixed hB v)

omit [DecidablePred (· ∈ candidates)] [Fintype (EdgeName (K := K))] [DecidableEq (EdgeName (K := K))] in
/-- The same original always quotient changes by precisely the primitive input's generated affine term. -/
theorem family_obstruction_affine (v : V) :
    (o v) = LinearInterface.q (D₀) (-δ₀) - LinearInterface.q (D₀) (Δ v) := by
  change LinearInterface.q (D₀) (-(δ₀ + Δ v)) = _
  simp only [neg_add, map_add, map_neg, sub_eq_add_neg]

/-- Every actual primitive value and every allowed original candidate range use the same complete original column spans. -/
theorem family_repair_nonempty_iff_range (v : V) (S : Set candidates) :
    Nonempty (SupportedRepair (Tv v) (fixedEdgesForRange P.edges candidates (allowed S))) ↔
      (o v) ∈ NamedDual.ranges (Bcol) S :=
  (SupportedNativeEquation.repairEquiv (Tv v) P candidates (allowed S) (hfixedv v)).nonempty_congr.trans
    ((familyEquationObjects K L R c θL θR η hf P hB hfixed candidates (allowed S) v).nonempty_congr.trans
      (OriginalRanges.objects_nonempty_iff_range (k := k) (M) P candidates houtside lin (δ v) S))

/-- The full dual witness supports remain the same named candidate supports at every primitive value. -/
theorem family_repair_nonempty_iff_hits (v : V) (S : Set candidates) :
    Nonempty (SupportedRepair (Tv v) (fixedEdgesForRange P.edges candidates (allowed S))) ↔
      NamedDual.Hits (Bcol) (o v) S :=
  (family_repair_nonempty_iff_range K L R c θL θR η hf P hB hfixed candidates houtside v S).trans
    (NamedDual.mem_ranges_iff_hits (Bcol) (o v) S)

/-- Every failed actual parameter range has a dual certificate on the same whole original quotient. -/
theorem family_failed_repair_dual (v : V) (S : Set candidates)
    (h : ¬ Nonempty (SupportedRepair (Tv v) (fixedEdgesForRange P.edges candidates (allowed S)))) :
    ∃ phi : Module.Dual k (OriginalRanges.ObstructionSpace (k := k) (M) P candidates lin),
      phi (o v) ≠ 0 ∧ ∀ e ∈ S, phi.comp ((Bcol) e) = 0 :=
  NamedDual.failure_witness (Bcol) (o v) S
    (fun hm => h ((family_repair_nonempty_iff_range K L R c θL θR η hf P hB hfixed candidates houtside v S).mpr hm))

/-- Inclusion-minimal actual repair ranges at each primitive value are the minimal transversals of the same original dual column supports. -/
theorem family_minimal_repair_iff (v : V) (S : Set candidates) :
    Minimal (fun W => Nonempty (SupportedRepair (Tv v)
      (fixedEdgesForRange P.edges candidates (allowed W)))) S ↔
      Minimal (NamedDual.Hits (Bcol) (o v)) S := by
  simp only [Minimal, family_repair_nonempty_iff_hits K L R c θL θR η hf P hB hfixed candidates houtside v]

end AAT.AG.RelativeRepairComposition.NativeAffine
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
