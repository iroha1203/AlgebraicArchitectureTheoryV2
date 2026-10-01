import ResearchLean.AG.RelativeRepairComposition.AffineFamilyNativeEquation
import ResearchLean.AG.RelativeRepairComposition.AffineFamilyFiniteInput
import ResearchLean.AG.RelativeRepairComposition.SymbolicGlobalValues
import ResearchLean.AG.RelativeRepairComposition.NativeAffineGroupoid

/-!
# Original actual parameter repairs use the same complete symbolic cover

## Implementation notes

Full original kernel bases, all linear transports, local elimination data and
candidate names are fixed before either a parameter or an allowed range is
chosen. The primitive input generates the affine relative defect. Every value
is then connected to its full symbolic fibre by native inverse functors through
the independent actual affine repair groupoid. No existence equivalence is
asserted between different parameter values.
-/
namespace AAT.AG.RelativeRepairComposition.NativeAffine
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
universe uk uG uI uV
variable {k : Type uk} [Field k] [Fintype k] [DecidableEq k] (d : Nat)
variable (K : FiniteTransportPresentation.{uG})
variable (L R : ∀ {i j : K.Vertex}, K.Edge i j → Operations k (Fin d → k))
variable (c : K.TwoCell → (Fin d → k))
variable (hf : ∀ f : K.TwoCell,
  (GroupExtension.pathValue K R (K.twoLeft f)).linear =
    (GroupExtension.pathValue K R (K.twoRight f)).linear)
variable {V : Type uV} [AddCommGroup V] [Module k V]
variable (θL θR : V →ₗ[k] (EdgeName (K := K) → (Fin d → k)))
variable (η : V →ₗ[k] (K.TwoCell → (Fin d → k)))
variable {I : Type uI} [Fintype I] [DecidableEq I]
variable (P : ClosedRegion K) (U : I → ClosedRegion K)
variable [DecidablePred (· ∈ P.edges)] [DecidablePred (· ∈ P.faces)]
variable [∀ i, DecidablePred (· ∈ (U i).vertices)]
variable [∀ i, DecidablePred (· ∈ (U i).edges)] [∀ i, DecidablePred (· ∈ (U i).faces)]
variable (hB : ∀ v : V, ∀ f ∈ P.faces, familyDefectLinear K R θR η v f = 0)
variable (candidates : Set (EdgeName (K := K))) [DecidablePred (· ∈ candidates)]
variable (hfixed : ∀ f ∈ P.faces,
  translation (k := k) (c f) * GroupExtension.pathValue K R (K.twoLeft f) =
    GroupExtension.pathValue K R (K.twoRight f))
variable [Fintype (EdgeName (K := K))] [DecidableEq (EdgeName (K := K))]
variable [Fintype K.TwoCell] [DecidableEq K.TwoCell]
variable (enumK : FiniteElimination.Enumeration k)
variable (enumEdges : FiniteElimination.Enumeration (EdgeName (K := K)))
variable (enumFaces : FiniteElimination.Enumeration K.TwoCell)
variable (enumI : FiniteElimination.Enumeration I) (hc : ClosedRegion.IndexedCover U)
variable (allowed : Set (EdgeName (K := K))) (v : V)

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
local notation "T" => familyTower K L R c θL θR η hf v
local notation "M" => TowerPresentation.localCoefficients (OriginalTowerPresentation.toTower (tower K L R c hf))
local notation "bases" => standardBases d K L R c hf
local notation "lin" => edge_linear K L R c hf
local notation "δ₀" => ActualEquation.defectFamily (tower K L R c hf) P (fixed_native K L R c hf P hfixed)
local notation "Δ" => familyRelativeLinear K L R c θR η hf P hB
local notation "fixed" => fixedEdgesForRange P.edges candidates allowed
local notation "N" => familyNativeEquationEquivalence K L R c θL θR η hf P hB hfixed candidates allowed v
local notation "E" => SymbolicGlobalRestoration.equivalence (M) bases P U candidates lin δ₀ Δ enumK enumEdges enumFaces enumI hc allowed v
local notation "A" => groupoidEquivalence K (familyOriginal K L θL v) (familyReference K R θR v)
  (familyComparisons K c η v) (family_aligned K R θR hf v) P.vertices fixed
local notation "Fibre" => SymbolicCoverAction.Groupoid (M) bases P U candidates lin δ₀ Δ enumK enumEdges enumFaces allowed v

/-- Every full actual native parameter repair and all its arrows restore through the same fixed symbolic cover generators. -/
noncomputable def familyNativeSymbolicEquivalence : RepairGroupoid (T) P.vertices fixed ≌ Fibre :=
  (N).trans (E)

/-- The whole original parameter groupoid is restored exactly on original choices and all labels. -/
theorem family_native_symbolic_functor_inverse :
    (familyNativeSymbolicEquivalence d K L R c hf θL θR η P U hB candidates hfixed enumK enumEdges enumFaces enumI hc allowed v).functor ⋙
    (familyNativeSymbolicEquivalence d K L R c hf θL θR η P U hB candidates hfixed enumK enumEdges enumFaces enumI hc allowed v).inverse =
      𝟭 (RepairGroupoid (T) P.vertices fixed) :=
  strict_trans_functor_inverse (N) (E)
    (family_native_equation_functor_inverse K L R c θL θR η hf P hB hfixed candidates allowed v)
    (SymbolicGlobalRestoration.functor_inverse (M) bases P U candidates lin δ₀ Δ enumK enumEdges enumFaces enumI hc allowed v)

/-- Every full symbolic public/private coordinate and all original compatible labels are restored exactly. -/
theorem family_native_symbolic_inverse_functor :
    (familyNativeSymbolicEquivalence d K L R c hf θL θR η P U hB candidates hfixed enumK enumEdges enumFaces enumI hc allowed v).inverse ⋙
    (familyNativeSymbolicEquivalence d K L R c hf θL θR η P U hB candidates hfixed enumK enumEdges enumFaces enumI hc allowed v).functor = 𝟭 Fibre :=
  strict_trans_inverse_functor (N) (E)
    (family_native_equation_inverse_functor K L R c θL θR η hf P hB hfixed candidates allowed v)
    (SymbolicGlobalRestoration.inverse_functor (M) bases P U candidates lin δ₀ Δ enumK enumEdges enumFaces enumI hc allowed v)

/-- Independent real affine repairs and every original full translation arrow have the same complete symbolic fibres. -/
noncomputable def familyRealSymbolicEquivalence :
    Groupoid K (familyOriginal K L θL v) (familyReference K R θR v) (familyComparisons K c η v)
      (family_aligned K R θR hf v) P.vertices fixed ≌ Fibre :=
  (A).symm.trans (familyNativeSymbolicEquivalence d K L R c hf θL θR η P U hB candidates hfixed enumK enumEdges enumFaces enumI hc allowed v)

/-- Reconstructing actual real repairs restores every original real operation and full original translation label. -/
theorem family_real_symbolic_functor_inverse :
    (familyRealSymbolicEquivalence d K L R c hf θL θR η P U hB candidates hfixed enumK enumEdges enumFaces enumI hc allowed v).functor ⋙
    (familyRealSymbolicEquivalence d K L R c hf θL θR η P U hB candidates hfixed enumK enumEdges enumFaces enumI hc allowed v).inverse =
      𝟭 (Groupoid K (familyOriginal K L θL v) (familyReference K R θR v) (familyComparisons K c η v)
        (family_aligned K R θR hf v) P.vertices fixed) :=
  strict_trans_functor_inverse (A).symm _
    (groupoid_inverse_functor K (familyOriginal K L θL v) (familyReference K R θR v)
      (familyComparisons K c η v) (family_aligned K R θR hf v) P.vertices fixed)
    (family_native_symbolic_functor_inverse d K L R c hf θL θR η P U hB candidates hfixed enumK enumEdges enumFaces enumI hc allowed v)

/-- Actual real reconstruction followed by symbolic coordinates restores the same full symbolic objects and arrows. -/
theorem family_real_symbolic_inverse_functor :
    (familyRealSymbolicEquivalence d K L R c hf θL θR η P U hB candidates hfixed enumK enumEdges enumFaces enumI hc allowed v).inverse ⋙
    (familyRealSymbolicEquivalence d K L R c hf θL θR η P U hB candidates hfixed enumK enumEdges enumFaces enumI hc allowed v).functor = 𝟭 Fibre :=
  strict_trans_inverse_functor (A).symm _
    (groupoid_functor_inverse K (familyOriginal K L θL v) (familyReference K R θR v)
      (familyComparisons K c η v) (family_aligned K R θR hf v) P.vertices fixed)
    (family_native_symbolic_inverse_functor d K L R c hf θL θR η P U hB candidates hfixed enumK enumEdges enumFaces enumI hc allowed v)

local notation "EO" => familyEquationObjects K L R c θL θR η hf P hB hfixed candidates allowed v
local notation "RO" => SupportedNativeEquation.repairEquiv (T) P candidates allowed
  (fixed_native K (familyOriginal K L θL v) (familyReference K R θR v) (familyComparisons K c η v)
    (family_aligned K R θR hf v) P (family_fixed_face K R c θR η hf P.faces hfixed hB v))
local notation "SO" => SymbolicGlobalRestoration.objectEquiv (M) bases P U candidates lin δ₀ Δ enumK enumEdges enumFaces enumI hc allowed v
local notation "SL" => SymbolicStrictCover.originalObjectEquiv (M) bases P U candidates lin δ₀ Δ enumK enumEdges enumFaces allowed v

/-- The full original repair object has explicit symbolic coordinates with both inverse reconstructions. -/
noncomputable def familySymbolicObjects : SupportedRepair (T) fixed ≃
    SymbolicStrictCover.Objects (M) bases P U candidates lin δ₀ Δ enumK enumEdges enumFaces allowed v :=
  ((RO).trans (EO)).trans (SO)

/-- Restoring the forward symbolic object retains the correction on every same original included edge. -/
theorem family_symbolic_forward_edge_value (s : SupportedRepair (T) fixed) (i : I) (e : (U i).edges) :
    (((SL) (familySymbolicObjects d K L R c hf θL θR η P U hB candidates hfixed
      enumK enumEdges enumFaces enumI hc allowed v s)).1 i).1.1.1 e = (T).solutionCorrection s.1 e.1 := by
  change (((SL) ((SO) ((EO) ((RO) s)))).1 i).1.1.1 e = _
  rw [SymbolicGlobalRestoration.forward_edge_value]
  exact family_native_equation_edge_value K L R c θL θR η hf P hB hfixed candidates allowed v s e.1

/-- Full inverse symbolic reconstruction returns each original edge correction, with every retained private freedom. -/
theorem family_symbolic_inverse_edge_value
    (y : SymbolicStrictCover.Objects (M) bases P U candidates lin δ₀ Δ enumK enumEdges enumFaces allowed v)
    (i : I) (e : (U i).edges) :
    (T).solutionCorrection
      ((familySymbolicObjects d K L R c hf θL θR η P U hB candidates hfixed
        enumK enumEdges enumFaces enumI hc allowed v).symm y).1 e.1 =
      (((SL) y).1 i).1.1.1 e := by
  have h := family_symbolic_forward_edge_value d K L R c hf θL θR η P U hB candidates hfixed
    enumK enumEdges enumFaces enumI hc allowed v
    ((familySymbolicObjects d K L R c hf θL θR η P U hB candidates hfixed
      enumK enumEdges enumFaces enumI hc allowed v).symm y) i e
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

/-- Every forward symbolic arrow retains every full original vertex-label value on every original region. -/
theorem family_symbolic_forward_label_value
    {s t : RepairGroupoid (T) P.vertices fixed} (b : s ⟶ t) (i : I) (w : (U i).vertices) :
    ((((familyNativeSymbolicEquivalence d K L R c hf θL θR η P U hB candidates hfixed
      enumK enumEdges enumFaces enumI hc allowed v).functor.map b).1.toAdd).1 i).1.1 w =
      b.1.toAdd.1 w.1 :=
  family_native_equation_label_value K L R c θL θR η hf P hB hfixed candidates allowed v b w.1

end AAT.AG.RelativeRepairComposition.NativeAffine
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
