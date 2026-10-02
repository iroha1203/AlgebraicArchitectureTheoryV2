import ResearchLean.AG.RelativeRepairComposition.RelativeGeneratedStrictAction
import ResearchLean.AG.RelativeRepairComposition.GeneratedCoverAction

/-!
# Actual defect inputs to independent arbitrary strict generators

## Implementation notes

The arbitrary-right-hand-side generator is the same finite generator used for
actual signed face defects. This identification retains every component,
private kernel and native label; it does not assume any comparison of sections.
-/
namespace AAT.AG.RelativeRepairComposition.RelativeGeneratedDefectCover
open CategoryTheory TransportCoherence AbelianLiftingObstruction
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
universe uk uG uA uI
variable {k : Type uk} [Field k] [Fintype k] [DecidableEq k]
variable {K : FiniteTransportPresentation.{uG}} {I : Type uI} [Fintype I] [DecidableEq I]
variable (M : LocalCoefficients.{uG,uA} K) [∀ v, Module k (M.A v)]
variable (bases : FiniteFamily.Bases (k := k) M.A) (U : I → ClosedRegion K) (P : ClosedRegion K)
variable [DecidablePred (· ∈ P.edges)] [DecidablePred (· ∈ P.faces)]
variable [∀ j, DecidablePred (· ∈ (U j).vertices)]
variable [∀ j, DecidablePred (· ∈ (U j).edges)] [∀ j, DecidablePred (· ∈ (U j).faces)]
variable (candidates : Set (EdgeName (K := K))) [DecidablePred (· ∈ candidates)]
variable (hlinear : ∀ {s t : K.Vertex} (e : K.Edge s t) (a : k) (x : M.A s),
  M.edge e (a • x) = a • M.edge e x)
variable [Fintype (EdgeName (K := K))] [DecidableEq (EdgeName (K := K))]
variable [Fintype K.TwoCell] [DecidableEq K.TwoCell]
variable (ek : FiniteElimination.Enumeration k)
variable (ee : FiniteElimination.Enumeration (EdgeName (K := K)))
variable (ef : FiniteElimination.Enumeration K.TwoCell)


variable (δ : RelativeCover.C2 M ClosedRegion.all P)
variable (allowed : Set (EdgeName (K := K)))
local notation "values" => (fun j => -CoverEquation.defect M P δ (U j))
local notation "Labels" => StrictSupportedCover.Labels M P U candidates allowed
local notation "Old" => GeneratedStrictCover.Objects M bases P U candidates hlinear δ ek ee ef allowed
local notation "New" => RelativeGeneratedStrictCover.Objects M bases U P candidates hlinear ek ee ef values (candidates \ allowed)

/-- Actual signed defect generation and arbitrary generation retain the identical full strict object family. -/
def objectsEquiv : Old ≃ New where
  toFun y := ⟨y.1,y.2⟩
  invFun y := ⟨y.1,y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Every generated component and every private kernel value remains literal. -/
theorem component (y : Old) (j : I) :
    (objectsEquiv M bases U P candidates hlinear ek ee ef δ allowed y).1 j = y.1 j := rfl

/-- The complete native strict label action is unchanged at each generated component. -/
theorem equivariant (b : Multiplicative Labels) (y : Old) :
    objectsEquiv M bases U P candidates hlinear ek ee ef δ allowed (b • y) =
      b • objectsEquiv M bases U P candidates hlinear ek ee ef δ allowed y := by
  apply Subtype.ext
  funext j
  rw [RelativeGeneratedStrictAction.action_component]
  rfl

/-- All signed-defect and arbitrary-input generated strict arrows retain their full native labels. -/
noncomputable def equivalence : ActionCategory (Multiplicative Labels) Old ≌ ActionCategory (Multiplicative Labels) New :=
  changedLabelEquivalence (MulEquiv.refl (Multiplicative Labels))
    (objectsEquiv M bases U P candidates hlinear ek ee ef δ allowed)
    (equivariant M bases U P candidates hlinear ek ee ef δ allowed)

/-- Forward arrows retain every original strict vertex-label value. -/
theorem functor_label {x y : ActionCategory (Multiplicative Labels) Old} (f : x ⟶ y) :
    ((equivalence M bases U P candidates hlinear ek ee ef δ allowed).functor.map f).1 = f.1 := rfl

/-- Inverse arrows retain every original strict vertex-label value. -/
theorem inverse_label {x y : ActionCategory (Multiplicative Labels) New} (f : x ⟶ y) :
    ((equivalence M bases U P candidates hlinear ek ee ef δ allowed).inverse.map f).1 = f.1 := rfl

end AAT.AG.RelativeRepairComposition.RelativeGeneratedDefectCover
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.RelativeGeneratedDefectCover
