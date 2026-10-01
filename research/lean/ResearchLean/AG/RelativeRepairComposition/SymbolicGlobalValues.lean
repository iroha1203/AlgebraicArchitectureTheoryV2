import ResearchLean.AG.RelativeRepairComposition.SymbolicGlobalRestoration

/-!
# Symbolic restoration retains each original edge and vertex value

## Implementation notes

The complete symbolic coordinates evaluate to the same original local edge
cochains. Gluing returns their values on the original included edge. Forward
and inverse arrow maps preserve every full included vertex label, including
labels with no effective action. These are direct value identities of the
constructed native functors.
-/
namespace AAT.AG.RelativeRepairComposition
open CategoryTheory TransportCoherence AbelianLiftingObstruction
universe uk uG uA uI uV
namespace SymbolicGlobalRestoration
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
variable {k : Type uk} [Field k] [Fintype k] [DecidableEq k]
variable {V : Type uV} [AddCommGroup V] [Module k V]
variable {K : FiniteTransportPresentation.{uG}} {I : Type uI} [Fintype I] [DecidableEq I]
variable (M : LocalCoefficients.{uG,uA} K) [∀ v, Module k (M.A v)]
variable (bases : FiniteFamily.Bases (k := k) M.A) (P : ClosedRegion K) (U : I → ClosedRegion K)
variable [DecidablePred (· ∈ P.edges)] [DecidablePred (· ∈ P.faces)]
variable [∀ i, DecidablePred (· ∈ (U i).vertices)]
variable [∀ i, DecidablePred (· ∈ (U i).edges)] [∀ i, DecidablePred (· ∈ (U i).faces)]
variable (candidates : Set (EdgeName (K := K))) [DecidablePred (· ∈ candidates)]
variable (hlinear : ∀ {i j : K.Vertex} (e : K.Edge i j) (t : k) (x : M.A i),
  M.edge e (t • x) = t • M.edge e x)
variable (δ₀ : RelativeCover.C2 M ClosedRegion.all P)
variable (Δ : V →ₗ[k] RelativeCover.C2 M ClosedRegion.all P)
variable [Fintype (EdgeName (K := K))] [DecidableEq (EdgeName (K := K))]
variable [Fintype K.TwoCell] [DecidableEq K.TwoCell]
variable (ek : FiniteElimination.Enumeration k)
variable (ee : FiniteElimination.Enumeration (EdgeName (K := K)))
variable (ef : FiniteElimination.Enumeration K.TwoCell)
variable (ei : FiniteElimination.Enumeration I) (hc : ClosedRegion.IndexedCover U)
variable (allowed : Set (EdgeName (K := K))) (v : V)
local notation "δ" => SymbolicNativeLocal.defectFamily M P δ₀ Δ v
local notation "G" => StrictCoverRestoration.equivalence M P U candidates allowed (δ) ei hc
local notation "C" => GeneratedCoverAction.equivalence M bases P U candidates hlinear (δ) ek ee ef allowed
local notation "E" => SymbolicCoverAction.equivalence M bases P U candidates hlinear δ₀ Δ ek ee ef allowed v


local notation "S" => SymbolicStrictCover.originalObjectEquiv M bases P U candidates hlinear δ₀ Δ ek ee ef allowed v
local notation "O" => objectEquiv M bases P U candidates hlinear δ₀ Δ ek ee ef ei hc allowed v

/-- Evaluating full symbolic global coordinates restores the same independent original local equations. -/
theorem original_local_evaluation
    (h : SupportedEquation.Objects M P ClosedRegion.all candidates allowed (δ)) :
    (S) ((O) h) = StrictCoverRestoration.restrictObjects M P U candidates allowed (δ) h := by
  simp only [SymbolicStrictCover.originalObjectEquiv, objectEquiv, Equiv.trans_apply,
    Equiv.apply_symm_apply, Equiv.symm_apply_apply]
  rfl

/-- Every forward coordinate reconstruction retains the actual full cochain on its original included edge. -/
theorem forward_edge_value
    (h : SupportedEquation.Objects M P ClosedRegion.all candidates allowed (δ)) (i : I) (e : (U i).edges) :
    (((S) ((O) h)).1 i).1.1.1 e = h.1.1.1 ⟨e.1,Set.mem_univ e.1⟩ := by
  rw [original_local_evaluation]
  rfl

/-- Every inverse global reconstruction returns the same full local cochain value on its original edge. -/
theorem inverse_edge_value
    (y : SymbolicStrictCover.Objects M bases P U candidates hlinear δ₀ Δ ek ee ef allowed v)
    (i : I) (e : (U i).edges) :
    ((O).symm y).1.1.1 ⟨e.1,Set.mem_univ e.1⟩ = (((S) y).1 i).1.1.1 e :=
  FiniteCoverGlue.glue1_value M P U ei hc
    (StrictSupportedCover.localEdges M P U candidates allowed (δ) ((S) y)) i e

/-- Forward symbolic arrows preserve every full original vertex value on every region. -/
theorem forward_label_value
    {x y : SupportedEquation.Groupoid M P ClosedRegion.all candidates allowed (δ)}
    (b : x ⟶ y) (i : I) (w : (U i).vertices) :
    ((((equivalence M bases P U candidates hlinear δ₀ Δ ek ee ef ei hc allowed v).functor.map b).1.toAdd).1 i).1.1 w =
      b.1.toAdd.1.1 ⟨w.1,Set.mem_univ w.1⟩ := rfl

/-- Inverse symbolic arrows restore each full included original vertex value through the same finite gluing. -/
theorem inverse_label_value
    {x y : SymbolicCoverAction.Groupoid M bases P U candidates hlinear δ₀ Δ ek ee ef allowed v}
    (b : x ⟶ y) (i : I) (w : (U i).vertices) :
    ((equivalence M bases P U candidates hlinear δ₀ Δ ek ee ef ei hc allowed v).inverse.map b).1.toAdd.1.1
      ⟨w.1,Set.mem_univ w.1⟩ = (b.1.toAdd.1 i).1.1 w :=
  FiniteCoverGlue.glue0_value M P U ei hc
    (StrictSupportedCover.localLabels M P U candidates allowed b.1.toAdd) i w

end SymbolicGlobalRestoration
end AAT.AG.RelativeRepairComposition
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
