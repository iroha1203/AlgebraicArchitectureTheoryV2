import ResearchLean.AG.RelativeRepairComposition.OriginalRangeEquations
import ResearchLean.AG.RelativeRepairComposition.FiniteDualWitness
import ResearchLean.AG.RelativeRepairComposition.FiniteNativeMatrices

/-!
# Computed dual witnesses on the same original always quotient

Full original relative edge coordinates are masked to the always source.
The candidate columns use every coordinate of the original target kernel.
The finite find output is pulled back to the original face family and descends
to the original always quotient, retaining the same rhs and candidate names.
-/
namespace AAT.AG.RelativeRepairComposition
open TransportCoherence AbelianLiftingObstruction FiniteCoefficients
universe uk uG uA
namespace OriginalFiniteDual
set_option autoImplicit false
variable {k : Type uk} [Field k] [Fintype k] [DecidableEq k]
variable {K : FiniteTransportPresentation.{uG}} (M : LocalCoefficients.{uG,uA} K)
variable [∀ v, Module k (M.A v)]
variable (B : FiniteFamily.Bases (k := k) M.A) (P : ClosedRegion K)
variable [DecidablePred (· ∈ P.edges)] [DecidablePred (· ∈ P.faces)]
variable (candidates : Set (EdgeName (K := K))) [DecidablePred (· ∈ candidates)]
variable (houtside : ∀ e ∈ candidates, e ∉ P.edges)
variable (hlinear : ∀ {i j : K.Vertex} (e : K.Edge i j) (t : k) (x : M.A i),
  M.edge e (t • x) = t • M.edge e x)
variable [Fintype (EdgeName (K := K))] [DecidableEq (EdgeName (K := K))]
variable [Fintype K.TwoCell] [DecidableEq K.TwoCell]
/-- Decide membership in the full original edge region by its universal predicate. -/
local instance allEdgesDecidable : DecidablePred (· ∈ (ClosedRegion.all (K := K)).edges) :=
  fun _ => isTrue trivial
/-- Decide membership in the full original vertex region by its universal predicate. -/
local instance allVerticesDecidable : DecidablePred (· ∈ (ClosedRegion.all (K := K)).vertices) :=
  fun _ => isTrue trivial
/-- Decide membership in the full original face region by its universal predicate. -/
local instance allFacesDecidable : DecidablePred (· ∈ (ClosedRegion.all (K := K)).faces) :=
  fun _ => isTrue trivial
local notation "D0" => OriginalColumns.D (k := k) M P candidates hlinear
local notation "Ecol" => OriginalColumns.column (k := k) M P candidates houtside hlinear
local notation "coord1" => FiniteNative.coordinate1 M B ClosedRegion.all P
local notation "coord2" => FiniteNative.coordinate2 M B ClosedRegion.all P

/-- Test every complete original edge coordinate through the always mask. -/
def alwaysMatrixMap : (FiniteNative.Index1 M B ClosedRegion.all P → k) →ₗ[k]
    (FiniteNative.Index2 M B ClosedRegion.all P → k) :=
  (coord2).toLinearMap.comp ((D0).comp
    ((OriginalColumns.alwaysRead (k := k) M P candidates).comp (coord1).symm.toLinearMap))

/-- Each original candidate retains all coordinates of its complete target kernel. -/
def candidateMatrixMap (e : candidates) : (Fin (B.dimension e.1.2.1) → k) →ₗ[k]
    (FiniteNative.Index2 M B ClosedRegion.all P → k) :=
  (coord2).toLinearMap.comp ((Ecol e).comp (B.coordinate e.1.2.1).symm.toLinearMap)

omit [DecidablePred (· ∈ P.edges)] [DecidablePred (· ∈ P.faces)]
  [Fintype k] [DecidableEq k] [Fintype (EdgeName (K := K))]
  [DecidableEq (EdgeName (K := K))] [Fintype K.TwoCell] [DecidableEq K.TwoCell] in
/-- Masking an original always correction returns the same whole correction. -/
theorem mask_always (x : OriginalColumns.alwaysSpace (k := k) M P candidates) :
    OriginalColumns.alwaysRead (k := k) M P candidates x.1 = x := by
  apply Subtype.ext
  apply Subtype.ext
  funext e
  change (if e.1 ∈ candidates then 0 else x.1.1 e) = x.1.1 e
  by_cases he : e.1 ∈ candidates
  · rw [if_pos he]; exact (x.2 ⟨e.1,he⟩).symm
  · exact if_neg he

omit [Fintype k] [DecidableEq k] [Fintype (EdgeName (K := K))]
  [DecidableEq (EdgeName (K := K))] [Fintype K.TwoCell] [DecidableEq K.TwoCell] in
/-- The finite always test evaluates each original full always correction unchanged. -/
theorem always_value (x : OriginalColumns.alwaysSpace (k := k) M P candidates) :
    alwaysMatrixMap M B P candidates hlinear (coord1 x.1) = coord2 (D0 x) := by
  change coord2 (D0 (OriginalColumns.alwaysRead (k := k) M P candidates
    ((coord1).symm (coord1 x.1)))) = _
  rw [LinearEquiv.symm_apply_apply,mask_always]

omit [Fintype k] [DecidableEq k] [DecidablePred (· ∈ P.edges)]
  [Fintype (EdgeName (K := K))] [Fintype K.TwoCell] [DecidableEq K.TwoCell] in
/-- Full candidate coordinates evaluate the same original named whole-kernel column. -/
theorem candidate_value (e : candidates) (y : M.A e.1.2.1) :
    candidateMatrixMap M B P candidates houtside hlinear e (B.coordinate e.1.2.1 y) =
      coord2 (Ecol e y) := by
  change coord2 (Ecol e ((B.coordinate e.1.2.1).symm (B.coordinate e.1.2.1 y))) = _
  rw [LinearEquiv.symm_apply_apply]

variable (r : RelativeCover.C2 M ClosedRegion.all P)
variable (S : Set candidates) [DecidablePred (· ∈ S)]
variable (enumK : FiniteElimination.Enumeration k)
variable (enumFaces : FiniteElimination.Enumeration K.TwoCell)
local notation "Dm" => alwaysMatrixMap M B P candidates hlinear
local notation "Cm" => candidateMatrixMap M B P candidates houtside hlinear
local notation "enumN" => FiniteNative.enum2 M B ClosedRegion.all P enumFaces

/-- Enumerated arithmetic tests on the original full columns and original rhs. -/
def find : Option (FiniteNative.Index2 M B ClosedRegion.all P → k) :=
  FiniteDual.find Dm Cm (coord2 r) S enumK enumN

omit [Fintype k] [DecidableEq k] [Fintype (EdgeName (K := K))] [DecidablePred (· ∈ S)] in
include houtside enumK enumFaces in
/-- Failure in the original quotient supplies a tested row in the fixed finite row list. -/
theorem valid_of_failure
    (h : LinearInterface.q D0 r ∉ NamedDual.ranges (CokernelNamed.column D0 Ecol) S) :
    ∃ w ∈ (FiniteDual.rows enumK enumN).values, FiniteDual.Valid Dm Cm (coord2 r) S w := by
  classical
  obtain ⟨phi,hphi,hc⟩ := NamedDual.failure_witness
    (CokernelNamed.column D0 Ecol) (LinearInterface.q D0 r) S h
  let f := (phi.comp (LinearInterface.q D0)).comp (coord2).symm.toLinearMap
  let w := (dotProductEquiv k (FiniteNative.Index2 M B ClosedRegion.all P)).symm f
  have hw : FiniteDual.row w = f := (dotProductEquiv k _).apply_symm_apply f
  refine ⟨w,(FiniteDual.rows enumK enumN).complete w,?_,?_,?_⟩
  · intro i
    rw [hw]
    change phi (LinearInterface.q D0 ((coord2).symm
      (coord2 (D0 (OriginalColumns.alwaysRead (k := k) M P candidates
        ((coord1).symm (Pi.single i 1))))))) = 0
    rw [LinearEquiv.symm_apply_apply]
    have hz : LinearInterface.q D0 (D0
      (OriginalColumns.alwaysRead (k := k) M P candidates ((coord1).symm (Pi.single i 1)))) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr ⟨_,rfl⟩
    rw [hz,map_zero]
  · intro e he i
    rw [hw]
    change phi (LinearInterface.q D0 ((coord2).symm
      (coord2 (Ecol e ((B.coordinate e.1.2.1).symm (Pi.single i 1)))))) = 0
    rw [LinearEquiv.symm_apply_apply]
    exact LinearMap.congr_fun (hc e he) _
  · rw [hw]
    change phi (LinearInterface.q D0 ((coord2).symm (coord2 r))) ≠ 0
    rw [LinearEquiv.symm_apply_apply]; exact hphi

omit [Fintype k] in
/-- The finite search succeeds on exactly the required original failed-range input. -/
theorem find_isSome
    (h : LinearInterface.q D0 r ∉ NamedDual.ranges (CokernelNamed.column D0 Ecol) S) :
    (find M B P candidates houtside hlinear r S enumK enumFaces).isSome = true := by
  rw [find,FiniteDual.find,List.find?_isSome]
  obtain ⟨w,hw,hv⟩ := valid_of_failure M B P candidates houtside hlinear r S enumK enumFaces h
  exact ⟨w,hw,decide_eq_true hv⟩

/-- The actual find result has the checked original full-column predicate. -/
def rowWitness
    (h : LinearInterface.q D0 r ∉ NamedDual.ranges (CokernelNamed.column D0 Ecol) S) :
    {w : FiniteNative.Index2 M B ClosedRegion.all P → k //
      FiniteDual.Valid Dm Cm (coord2 r) S w} := by
  have hf := find_isSome M B P candidates houtside hlinear r S enumK enumFaces h
  refine ⟨(find M B P candidates houtside hlinear r S enumK enumFaces).get hf,?_⟩
  have ht := List.find?_some (Option.some_get hf).symm
  exact of_decide_eq_true ht

/-- Descend the computed row to the same original whole always quotient. -/
def quotientDual (w : FiniteNative.Index2 M B ClosedRegion.all P → k)
    (hw : FiniteDual.Valid Dm Cm (coord2 r) S w) :
    Module.Dual k (OriginalRanges.ObstructionSpace (k := k) M P candidates hlinear) :=
  (LinearMap.range D0).liftQ ((FiniteDual.row w).comp (coord2).toLinearMap) (by
    rintro _ ⟨x,rfl⟩
    have hx := LinearMap.congr_fun ((FiniteDual.annihilates_iff w Dm).mpr hw.1) (coord1 x.1)
    change FiniteDual.row w (Dm (coord1 x.1)) = 0 at hx
    change FiniteDual.row w (coord2 (D0 x)) = 0
    rw [always_value M B P candidates hlinear x] at hx
    exact hx)

omit [Fintype k] [DecidableEq k] [DecidablePred (· ∈ S)] in
/-- Every original face representative has the same computed row evaluation. -/
theorem quotientDual_value (w : FiniteNative.Index2 M B ClosedRegion.all P → k)
    (hw : FiniteDual.Valid Dm Cm (coord2 r) S w) (c : RelativeCover.C2 M ClosedRegion.all P) :
    quotientDual M B P candidates houtside hlinear r S w hw (LinearInterface.q D0 c) =
      FiniteDual.row w (coord2 c) := rfl

omit [Fintype k] [DecidableEq k] [DecidablePred (· ∈ S)] in
/-- The computed original dual excludes this rhs and kills all allowed full candidate kernels. -/
theorem quotientDual_spec (w : FiniteNative.Index2 M B ClosedRegion.all P → k)
    (hw : FiniteDual.Valid Dm Cm (coord2 r) S w) :
    quotientDual M B P candidates houtside hlinear r S w hw (LinearInterface.q D0 r) ≠ 0 ∧
      ∀ e ∈ S, (quotientDual M B P candidates houtside hlinear r S w hw).comp
        (CokernelNamed.column D0 Ecol e) = 0 := by
  refine ⟨hw.2.2,?_⟩
  intro e he
  apply LinearMap.ext
  intro y
  have hy := LinearMap.congr_fun ((FiniteDual.annihilates_iff w (Cm e)).mpr (hw.2.1 e he))
    (B.coordinate e.1.2.1 y)
  change FiniteDual.row w (Cm e (B.coordinate e.1.2.1 y)) = 0 at hy
  change FiniteDual.row w (coord2 (Ecol e y)) = 0
  rw [candidate_value M B P candidates houtside hlinear e y] at hy
  exact hy

omit [Fintype k] [DecidableEq k] [DecidablePred (· ∈ S)] in
/-- A row accepted by the independent finite test excludes the original full selected range. -/
theorem valid_excludes_range (w : FiniteNative.Index2 M B ClosedRegion.all P → k)
    (hw : FiniteDual.Valid Dm Cm (coord2 r) S w) :
    LinearInterface.q D0 r ∉ NamedDual.ranges (CokernelNamed.column D0 Ecol) S := by
  let phi := quotientDual M B P candidates houtside hlinear r S w hw
  have hs := quotientDual_spec M B P candidates houtside hlinear r S w hw
  intro hm
  exact hs.1 ((Submodule.mem_dualAnnihilator phi).mp
    ((NamedDual.annihilates_iff (CokernelNamed.column D0 Ecol) S phi).mpr hs.2)
      (LinearInterface.q D0 r) hm)

omit [Fintype k] in
/-- The computed finite failed-row decision is exactly original quotient range failure. -/
theorem find_isSome_iff :
    (find M B P candidates houtside hlinear r S enumK enumFaces).isSome = true ↔
      LinearInterface.q D0 r ∉ NamedDual.ranges (CokernelNamed.column D0 Ecol) S := by
  constructor
  · intro hf
    have ht := List.find?_some (Option.some_get hf).symm
    exact valid_excludes_range M B P candidates houtside hlinear r S _ (of_decide_eq_true ht)
  · exact find_isSome M B P candidates houtside hlinear r S enumK enumFaces

/-- Failure generates an original quotient dual from the finite returned row itself. -/
def computedDual
    (h : LinearInterface.q D0 r ∉ NamedDual.ranges (CokernelNamed.column D0 Ecol) S) :
    {phi : Module.Dual k (OriginalRanges.ObstructionSpace (k := k) M P candidates hlinear) //
      phi (LinearInterface.q D0 r) ≠ 0 ∧
        ∀ e ∈ S, phi.comp (CokernelNamed.column D0 Ecol e) = 0} :=
  let w := rowWitness M B P candidates houtside hlinear r S enumK enumFaces h
  ⟨quotientDual M B P candidates houtside hlinear r S w.1 w.2,
    quotientDual_spec M B P candidates houtside hlinear r S w.1 w.2⟩

end OriginalFiniteDual
end AAT.AG.RelativeRepairComposition
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
