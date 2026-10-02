import ResearchLean.AG.RelativeRepairComposition.RelativeGeneratedCoverRanges
import ResearchLean.AG.RelativeRepairComposition.RelativeGeneratedStrictAction
import ResearchLean.AG.RelativeRepairComposition.GeneratedRangeInclusion

/-!
# Native range inclusions on independent generated strict objects

## Implementation notes

Candidate permission relaxes while every full coordinate and original vertex
label is retained. Native actions commute componentwise. All arrows compose
with the same labels under successive inclusions.
-/
namespace AAT.AG.RelativeRepairComposition.RelativeGeneratedNativeRanges
open CategoryTheory
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
open TransportCoherence AbelianLiftingObstruction
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


variable (S V : Set (EdgeName (K := K))) (hSV : S ⊆ V)
local notation "G" R => StrictSupportedCover.Labels M P U candidates R
local notation "X" R "at" values => RelativeGeneratedStrictCover.Objects M bases U P candidates hlinear ek ee ef values (candidates \ R)

/-- Include full strict labels with every original local vertex value. -/
def labelsInclusion : (G S) →+ (G V) :=
  GeneratedRangeInclusion.labelsInclusion M P U candidates hSV

/-- Independent full generated actions commute with every permission inclusion. -/
theorem equivariant (values : ∀ j, RelativeCover.C2 M (U j) P)
    (b : Multiplicative (G S)) (y : X S at values) :
    RelativeGeneratedCoverRanges.includeObjects M bases U P candidates hlinear ek ee ef S V hSV values (b • y) =
      (labelsInclusion M U P candidates S V hSV).toMultiplicative b •
        RelativeGeneratedCoverRanges.includeObjects M bases U P candidates hlinear ek ee ef S V hSV values y := by
  apply Subtype.ext
  funext j
  rw [RelativeGeneratedCoverRanges.include_component,
    RelativeGeneratedStrictAction.action_component,RelativeGeneratedStrictAction.action_component,
    RelativeGeneratedCoverRanges.include_component]
  rfl

/-- Every native arrow is included using its entire original label. -/
noncomputable def functor (values : ∀ j, RelativeCover.C2 M (U j) P) :
    ActionCategory (Multiplicative (G S)) (X S at values) ⥤ ActionCategory (Multiplicative (G V)) (X V at values) :=
  actionLabelFunctor (labelsInclusion M U P candidates S V hSV).toMultiplicative
    (RelativeGeneratedCoverRanges.includeObjects M bases U P candidates hlinear ek ee ef S V hSV values)
    (equivariant M bases U P candidates hlinear ek ee ef S V hSV values)

/-- Every included object retains its whole generated family. -/
theorem functor_object (values : ∀ j, RelativeCover.C2 M (U j) P)
    (y : ActionCategory (Multiplicative (G S)) (X S at values)) :
    ((functor M bases U P candidates hlinear ek ee ef S V hSV values).obj y).back.1 = y.back.1 := rfl

/-- Every included arrow retains each full original local label value. -/
theorem functor_label (values : ∀ j, RelativeCover.C2 M (U j) P)
    {x y : ActionCategory (Multiplicative (G S)) (X S at values)} (f : x ⟶ y) (j : I) (v : (U j).vertices) :
    ((((functor M bases U P candidates hlinear ek ee ef S V hSV values).map f).1.toAdd.1 j).1.1 v) =
      ((f.1.toAdd.1 j).1.1 v) := rfl

/-- Native inclusions compose on all independent objects and all original arrows. -/
theorem functor_comp (values : ∀ j, RelativeCover.C2 M (U j) P)
    (W : Set (EdgeName (K := K))) (hVW : V ⊆ W) :
    functor M bases U P candidates hlinear ek ee ef S V hSV values ⋙
      functor M bases U P candidates hlinear ek ee ef V W hVW values =
    functor M bases U P candidates hlinear ek ee ef S W (hSV.trans hVW) values := rfl

end AAT.AG.RelativeRepairComposition.RelativeGeneratedNativeRanges
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.RelativeGeneratedNativeRanges
