import ResearchLean.AG.RelativeRepairComposition.SymbolicCoverRanges
import ResearchLean.AG.RelativeRepairComposition.StrictCoverRestoration
import ResearchLean.AG.RelativeRepairComposition.StrictFunctorComparison

/-!
# Every symbolic parameter fibre restores the whole original global equation

## Implementation notes

The same fixed cover, original coordinate bases and one-time local generators
are used for each value and each allowed range. Full original cochain gluing and
full vertex-label gluing precede coordinate generation. The composed functors
and both strict inverses therefore restore the whole original equation groupoid.
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

/-- The full independent original global supported equation has the same complete symbolic parameter-fibre coordinates. -/
noncomputable def objectEquiv : SupportedEquation.Objects M P ClosedRegion.all candidates allowed (δ) ≃
    SymbolicStrictCover.Objects M bases P U candidates hlinear δ₀ Δ ek ee ef allowed v :=
  ((StrictCoverRestoration.objectEquiv M P U candidates allowed (δ) ei hc).trans
    (GeneratedStrictCover.objectEquiv M bases P U candidates hlinear (δ) ek ee ef allowed)).trans
      (SymbolicStrictCover.objectEquiv M bases P U candidates hlinear δ₀ Δ ek ee ef allowed v).symm

/-- Full original global arrows and all symbolic local public/private coordinates have inverse native functors. -/
noncomputable def equivalence : SupportedEquation.Groupoid M P ClosedRegion.all candidates allowed (δ) ≌
    SymbolicCoverAction.Groupoid M bases P U candidates hlinear δ₀ Δ ek ee ef allowed v :=
  ((G).trans (C)).trans (E).symm

/-- Reconstruction after symbolic global coordinates is exactly identity on every original object and full arrow. -/
theorem functor_inverse : (equivalence M bases P U candidates hlinear δ₀ Δ ek ee ef ei hc allowed v).functor ⋙
    (equivalence M bases P U candidates hlinear δ₀ Δ ek ee ef ei hc allowed v).inverse =
      𝟭 (SupportedEquation.Groupoid M P ClosedRegion.all candidates allowed (δ)) :=
  strict_trans_functor_inverse _ _
    (strict_trans_functor_inverse _ _ (StrictCoverRestoration.functor_inverse M P U candidates allowed (δ) ei hc)
      (GeneratedCoverAction.functor_inverse M bases P U candidates hlinear (δ) ek ee ef allowed))
    (SymbolicCoverAction.inverse_functor M bases P U candidates hlinear δ₀ Δ ek ee ef allowed v)

/-- Coordinates after symbolic global reconstruction are exactly identity on every public value, full private kernel and original label. -/
theorem inverse_functor : (equivalence M bases P U candidates hlinear δ₀ Δ ek ee ef ei hc allowed v).inverse ⋙
    (equivalence M bases P U candidates hlinear δ₀ Δ ek ee ef ei hc allowed v).functor =
      𝟭 (SymbolicCoverAction.Groupoid M bases P U candidates hlinear δ₀ Δ ek ee ef allowed v) :=
  strict_trans_inverse_functor _ _
    (strict_trans_inverse_functor _ _ (StrictCoverRestoration.inverse_functor M P U candidates allowed (δ) ei hc)
      (GeneratedCoverAction.inverse_functor M bases P U candidates hlinear (δ) ek ee ef allowed))
    (SymbolicCoverAction.functor_inverse M bases P U candidates hlinear δ₀ Δ ek ee ef allowed v)

/-- Evaluating the complete symbolic global coordinates gives the same original one-time generated coordinates on every object and arrow. -/
theorem evaluation_global : (equivalence M bases P U candidates hlinear δ₀ Δ ek ee ef ei hc allowed v).functor ⋙
    (E).functor = (G).functor ⋙ (C).functor := by
  change (G).functor ⋙ ((C).functor ⋙ ((E).inverse ⋙ (E).functor)) = _
  rw [SymbolicCoverAction.inverse_functor, Functor.comp_id]

end SymbolicGlobalRestoration
end AAT.AG.RelativeRepairComposition
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
