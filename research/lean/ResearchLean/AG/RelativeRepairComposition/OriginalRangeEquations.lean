import ResearchLean.AG.RelativeRepairComposition.OriginalCandidateColumns
import ResearchLean.AG.RelativeRepairComposition.CokernelNamedRanges
import ResearchLean.AG.RelativeRepairComposition.SupportedEquation

/-!
# The original supported equation and every named cokernel range

The supported equation remains the independently defined original face equation
with forbidden candidate values zero. Selected columns are actual full-kernel
columns of that same differential, with no effective renaming of candidates.
-/
namespace AAT.AG.RelativeRepairComposition
open TransportCoherence AbelianLiftingObstruction FiniteCoefficients
universe uk uG uA
namespace OriginalRanges
set_option autoImplicit false
attribute [local instance] Classical.propDecidable
variable {k : Type uk} [Field k]
variable {K : FiniteTransportPresentation.{uG}} (M : LocalCoefficients.{uG,uA} K)
variable [∀ v, Module k (M.A v)]
variable (P : ClosedRegion K) (candidates : Set (EdgeName (K := K)))
variable [DecidablePred (· ∈ candidates)]
variable (houtside : ∀ e ∈ candidates, e ∉ P.edges)
variable (hlinear : ∀ {i j : K.Vertex} (e : K.Edge i j) (t : k) (x : M.A i),
  M.edge e (t • x) = t • M.edge e x)
variable [Fintype (EdgeName (K := K))] [DecidableEq (EdgeName (K := K))]
local instance allEdgesDecidable : DecidablePred (· ∈ (ClosedRegion.all (K := K)).edges) :=
  fun _ => isTrue trivial
local instance allVerticesDecidable : DecidablePred (· ∈ (ClosedRegion.all (K := K)).vertices) :=
  fun _ => isTrue trivial
local notation "C1P" => RelativeCover.C1 M ClosedRegion.all P
local notation "C2P" => RelativeCover.C2 M ClosedRegion.all P
local notation "D0" => OriginalColumns.D (k := k) M P candidates hlinear
local notation "Ecol" => OriginalColumns.column (k := k) M P candidates houtside hlinear

/-- The entire cokernel of the same original always differential. -/
abbrev ObstructionSpace := C2P ⧸ LinearMap.range D0

/-- Every original full candidate column followed by the same quotient map. -/
def column (e : candidates) : M.A e.1.2.1 →ₗ[k] ObstructionSpace (k := k) M P candidates hlinear :=
  CokernelNamed.column D0 Ecol e

/-- Restore an allowed set to the original candidate names without deleting any name. -/
def allowed (S : Set candidates) : Set (EdgeName (K := K)) :=
  {e | ∃ he : e ∈ candidates, (⟨e,he⟩ : candidates) ∈ S}

omit [DecidablePred (· ∈ candidates)] [Fintype (EdgeName (K := K))]
  [DecidableEq (EdgeName (K := K))] in
/-- Allowed membership is precisely selected membership at the same original name. -/
theorem allowed_iff (S : Set candidates) (e : candidates) :
    e.1 ∈ allowed candidates S ↔ e ∈ S :=
  ⟨fun ⟨_,he⟩ => he,fun he => ⟨e.2,he⟩⟩

/-- Selected restoration uses the complete original candidate coefficients. -/
noncomputable def selectedCorrection (S : Set candidates)
    (y : ∀ e : S, M.A e.1.1.2.1) : C1P :=
  OriginalColumns.candidateCochain (k := k) M P candidates houtside
    (NamedDual.extendSelected (k := k) S y)

/-- Its original differential is the literal sum of the same selected full columns. -/
theorem selected_differential (S : Set candidates) (y : ∀ e : S, M.A e.1.1.2.1) :
    differential1 M hlinear ClosedRegion.all P
      (selectedCorrection (k := k) M P candidates houtside S y) = NamedDual.sumSelected Ecol S y := by
  have hs := LinearMap.congr_fun (NamedDual.sum_extend Ecol S) y
  change (LinearMap.lsum k (fun e : candidates => M.A e.1.2.1) k Ecol)
    (NamedDual.extendSelected (k := k) S y) = _ at hs
  rw [OriginalColumns.sum_columns (k := k) M P candidates houtside hlinear] at hs
  exact hs

omit [Fintype (EdgeName (K := K))] [DecidableEq (EdgeName (K := K))] in
/-- A selected correction vanishes on every forbidden original candidate. -/
theorem selected_zero (S : Set candidates) (y : ∀ e : S, M.A e.1.1.2.1)
    (e : candidates) (he : e ∉ S) :
    (selectedCorrection (k := k) M P candidates houtside S y).1
      ⟨e.1,Set.mem_univ e.1⟩ = 0 :=
  (OriginalColumns.candidate_value (k := k) M P candidates houtside _ e).trans
    (NamedDual.extend_zero (k := k) (Y := fun e : candidates => M.A e.1.2.1) S y e he)

variable (δ : RelativeCover.C2 M ClosedRegion.all P)

/-- Every always correction and every selected full column solution restore a supported original equation. -/
noncomputable def restore (S : Set candidates)
    (x : OriginalColumns.alwaysSpace (k := k) M P candidates)
    (y : ∀ e : S, M.A e.1.1.2.1) (heq : D0 x + NamedDual.sumSelected Ecol S y = -δ) :
    SupportedEquation.Objects M P ClosedRegion.all candidates (allowed candidates S) δ :=
  ⟨⟨x.1 + selectedCorrection (k := k) M P candidates houtside S y,by
    rw [CoverEquation.defect_all]
    rw [← differential1_eq M hlinear]
    rw [map_add,selected_differential]
    exact heq⟩,by
      intro e he
      let ec : candidates := ⟨e.1,he.1⟩
      have hs : ec ∉ S := fun hc => he.2 ((allowed_iff candidates S ec).mpr hc)
      change x.1.1 e + (selectedCorrection (k := k) M P candidates houtside S y).1 e = 0
      rw [x.2 ec,selected_zero (k := k) M P candidates houtside S y ec hs,zero_add]⟩


/-- Independent supported original equations have exactly the same split solvability condition. -/
theorem objects_nonempty_iff_equation (S : Set candidates) :
    Nonempty (SupportedEquation.Objects M P ClosedRegion.all candidates (allowed candidates S) δ) ↔
      ∃ (x : OriginalColumns.alwaysSpace (k := k) M P candidates)
        (y : ∀ e : S, M.A e.1.1.2.1), D0 x + NamedDual.sumSelected Ecol S y = -δ := by
  constructor
  · rintro ⟨h⟩
    let values := OriginalColumns.candidateRead (k := k) M P candidates h.1.1
    have hv : ∀ e ∉ S, values e = 0 := by
      intro e he
      exact h.2 ⟨e.1,Set.mem_univ e.1⟩
        ⟨e.2,fun ha => he ((allowed_iff candidates S e).mp ha)⟩
    have hx := OriginalColumns.differential_decompose (k := k) M P candidates houtside hlinear h.1.1
    have hs := selected_differential (k := k) M P candidates houtside hlinear S (fun e => values e.1)
    have hc : selectedCorrection (k := k) M P candidates houtside S (fun e => values e.1) =
        OriginalColumns.candidateCochain (k := k) M P candidates houtside values := by
      exact congrArg (OriginalColumns.candidateCochain (k := k) M P candidates houtside)
        (NamedDual.extend_read (k := k) S values hv)
    rw [hc] at hs
    refine ⟨OriginalColumns.alwaysRead (k := k) M P candidates h.1.1,
      fun e => values e.1,?_⟩
    rw [← hs]
    change D0 (OriginalColumns.alwaysRead (k := k) M P candidates h.1.1) +
      OriginalColumns.candidateMap (k := k) M P candidates houtside hlinear values = -δ
    rw [hx,differential1_eq]
    exact h.1.2.trans (congrArg Neg.neg (CoverEquation.defect_all M P δ))
  · rintro ⟨x,y,heq⟩
    exact ⟨restore (k := k) M P candidates houtside hlinear δ S x y heq⟩

/-- Original supported equations exist exactly at membership in the named original cokernel range. -/
theorem objects_nonempty_iff_range (S : Set candidates) :
    Nonempty (SupportedEquation.Objects M P ClosedRegion.all candidates (allowed candidates S) δ) ↔
      LinearInterface.q D0 (-δ) ∈ NamedDual.ranges
        (column (k := k) M P candidates houtside hlinear) S :=
  (objects_nonempty_iff_equation (k := k) M P candidates houtside hlinear δ S).trans
    (CokernelNamed.mem_iff_equation D0 Ecol (-δ) S).symm

/-- The all-S dual criterion uses the very same obstruction class and original candidate names. -/
theorem objects_nonempty_iff_hits (S : Set candidates) :
    Nonempty (SupportedEquation.Objects M P ClosedRegion.all candidates (allowed candidates S) δ) ↔ NamedDual.Hits
      (column (k := k) M P candidates houtside hlinear) (LinearInterface.q D0 (-δ)) S :=
  (objects_nonempty_iff_range (k := k) M P candidates houtside hlinear δ S).trans
    (NamedDual.mem_ranges_iff_hits (column (k := k) M P candidates houtside hlinear)
      (LinearInterface.q D0 (-δ)) S)


end OriginalRanges
end AAT.AG.RelativeRepairComposition
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
