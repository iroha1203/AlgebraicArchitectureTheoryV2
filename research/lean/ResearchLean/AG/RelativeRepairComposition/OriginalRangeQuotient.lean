import ResearchLean.AG.RelativeRepairComposition.OriginalCandidateColumns
import ResearchLean.AG.RelativeRepairComposition.CokernelAllColumns
import ResearchLean.AG.RelativeRepairComposition.FiniteCoefficientSecondDifferential

/-!
# The original all-column second quotient and induced three-cell differential

The candidate image and original global d1 image are compared on whole
cochains. The second quotient keeps each original representative, and the
induced d2 comes from both original typed rewrite pastings.
-/
namespace AAT.AG.RelativeRepairComposition
open TransportCoherence AbelianLiftingObstruction FiniteCoefficients
universe uk uG uA
namespace OriginalRangeQuotient
variable {k : Type uk} [Field k]
variable {K : FiniteTransportPresentation.{uG}} (M : LocalCoefficients.{uG,uA} K)
variable [∀ v, Module k (M.A v)]
variable (P : ClosedRegion K) (candidates : Set (EdgeName (K := K)))
variable [DecidablePred (· ∈ candidates)]
variable (houtside : ∀ e ∈ candidates, e ∉ P.edges)
variable (hlinear : ∀ {i j : K.Vertex} (e : K.Edge i j) (t : k) (x : M.A i),
  M.edge e (t • x) = t • M.edge e x)
variable [Fintype (EdgeName (K := K))] [DecidableEq (EdgeName (K := K))]
/-- Decide membership in the full original edge region by its universal predicate. -/
local instance allEdgesDecidable : DecidablePred (· ∈ (ClosedRegion.all (K := K)).edges) :=
  fun _ => isTrue trivial
/-- Decide membership in the full original vertex region by its universal predicate. -/
local instance allVerticesDecidable : DecidablePred (· ∈ (ClosedRegion.all (K := K)).vertices) :=
  fun _ => isTrue trivial
/-- Decide membership in the full original face region by its universal predicate. -/
local instance allFacesDecidable : DecidablePred (· ∈ (ClosedRegion.all (K := K)).faces) :=
  fun _ => isTrue trivial
local notation "d1P" => differential1 M hlinear ClosedRegion.all P
local notation "d2P" => differential2 M hlinear ClosedRegion.all P
local notation "D0" => OriginalColumns.D (k := k) M P candidates hlinear
local notation "Ecol" => OriginalColumns.column (k := k) M P candidates houtside hlinear
local notation "F0" => OriginalColumns.candidateMap (k := k) M P candidates houtside hlinear
local notation "Bcol" => CokernelNamed.column D0 Ecol

/-- The complete named finite candidate sum is the same original candidate differential. -/
theorem full_candidates_eq : CokernelNamed.fullMap Ecol = F0 :=
  OriginalColumns.sum_columns (k := k) M P candidates houtside hlinear

omit [Fintype (EdgeName (K := K))] [DecidableEq (EdgeName (K := K))] in
/-- Every original face differential value is exactly in the sum of always and full candidate images. -/
theorem range_differential : LinearMap.range d1P = LinearMap.range D0 ⊔ LinearMap.range F0 := by
  apply le_antisymm
  · rintro _ ⟨h,rfl⟩
    rw [← OriginalColumns.differential_decompose (k := k) M P candidates houtside hlinear h]
    exact Submodule.mem_sup.mpr
      ⟨_,⟨OriginalColumns.alwaysRead (k := k) M P candidates h,rfl⟩,
        _,⟨OriginalColumns.candidateRead (k := k) M P candidates h,rfl⟩,rfl⟩
  · apply sup_le
    · rintro _ ⟨x,rfl⟩
      exact ⟨x.1,rfl⟩
    · rintro _ ⟨y,rfl⟩
      exact ⟨OriginalColumns.candidateCochain (k := k) M P candidates houtside y,rfl⟩

/-- The whole original always quotient modulo all original candidate ranges is CP2 modulo original d1. -/
noncomputable def equivalence :
    ((RelativeCover.C2 M ClosedRegion.all P ⧸ LinearMap.range D0) ⧸
      NamedDual.ranges Bcol Set.univ) ≃ₗ[k]
        RelativeCover.C2 M ClosedRegion.all P ⧸ LinearMap.range d1P :=
  (CokernelNamed.secondQuotient D0 Ecol).trans
    (Submodule.quotEquivOfEq _ _ (by
      rw [full_candidates_eq (k := k) M P candidates houtside hlinear]
      exact (range_differential (k := k) M P candidates houtside hlinear).symm))

/-- The equivalence preserves the same original whole face representative. -/
theorem equivalence_value (c : RelativeCover.C2 M ClosedRegion.all P) :
    equivalence (k := k) M P candidates houtside hlinear
      ((NamedDual.ranges Bcol Set.univ).mkQ (LinearInterface.q D0 c)) =
        (LinearMap.range d1P).mkQ c := by
  rw [equivalence,LinearEquiv.trans_apply,CokernelNamed.secondQuotient_value]
  simp only [Submodule.mkQ_apply,Submodule.quotEquivOfEq_mk]

/-- Original zero composition descends the full typed d2 to CP2 modulo all original d1 columns. -/
def inducedD2 : (RelativeCover.C2 M ClosedRegion.all P ⧸ LinearMap.range d1P) →ₗ[k]
    RelativeCover.C3 M ClosedRegion.all P :=
  (LinearMap.range d1P).liftQ d2P (by
    rintro _ ⟨h,rfl⟩
    exact differential2_differential1 M hlinear ClosedRegion.all P h)

omit [DecidablePred (· ∈ candidates)] [Fintype (EdgeName (K := K))]
  [DecidableEq (EdgeName (K := K))] in
/-- Induced d2 evaluates each original representative by the same full typed original differential. -/
theorem inducedD2_value (c : RelativeCover.C2 M ClosedRegion.all P) :
    inducedD2 (k := k) M P hlinear ((LinearMap.range d1P).mkQ c) = d2P c := rfl

/-- The same original obstruction image is a cycle of the induced d2. -/
theorem obstruction_image_cycle (delta : RelativeCover.C2 M ClosedRegion.all P)
    (hdelta : RelativeCover.d2 M ClosedRegion.all P delta = 0) :
    equivalence (k := k) M P candidates houtside hlinear
      ((NamedDual.ranges Bcol Set.univ).mkQ (LinearInterface.q D0 (-delta))) ∈
        LinearMap.ker (inducedD2 (k := k) M P hlinear) := by
  rw [equivalence_value]
  change inducedD2 (k := k) M P hlinear ((LinearMap.range d1P).mkQ (-delta)) = 0
  rw [inducedD2_value,map_neg,differential2_eq,hdelta,neg_zero]

end OriginalRangeQuotient
end AAT.AG.RelativeRepairComposition
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
