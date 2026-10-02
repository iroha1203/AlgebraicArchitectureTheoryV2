import ResearchLean.AG.RelativeRepairComposition.SubdivisionGeneratedCoverRanges
import ResearchLean.AG.RelativeRepairComposition.SubdivisionGeneratedGroupoidEquivalence
import ResearchLean.AG.RelativeRepairComposition.RelativeGeneratedNativeRanges

/-!
# All generated native arrows commute with the same subdivision range inclusion

## Implementation notes

Each permission range uses the independently defined full generated objects
and original strict label group. Inclusion retains all coordinates and labels.
The complete subdivision comparison and old native groupoid projection use
these same included objects and labels in both orders.
-/
namespace AAT.AG.RelativeRepairComposition.Subdivision.GeneratedNativeRanges
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
universe uk uG uI uE uB uD vE vB vD
variable {k : Type uk} [Field k] [Fintype k] [DecidableEq k]
variable {K : FiniteTransportPresentation.{uG}} {I : Type uI} [Fintype I] [DecidableEq I]
variable {E : Type uE} {B : Type uB} {D : Type uD}
variable [Category.{vE} E] [Category.{vB} B] [Category.{vD} D]
variable {p : E ⥤ B} {q : B ⥤ D}
variable (T : OriginalTowerPresentation K p q) (chosen : EdgeName (K := K))
variable (factor : Factorization T chosen)
variable [∀ v, Module k (T.toTower.localCoefficients.A v)]
attribute [local instance] LinearCoefficients.coefficientModules
variable (bases : FiniteFamily.Bases (k := k) T.toTower.localCoefficients.A)
variable (U : I → ClosedRegion K) (P : ClosedRegion K)
variable [∀ j, DecidablePred (· ∈ (U j).vertices)]
variable [∀ j, DecidablePred (· ∈ (U j).edges)] [∀ j, DecidablePred (· ∈ (U j).faces)]
variable [DecidablePred (· ∈ P.edges)] [DecidablePred (· ∈ P.faces)]
variable (candidates : Set (EdgeName (K := K))) [DecidablePred (· ∈ candidates)]
variable (owner : I) (hi : chosen ∈ ClosedRegion.privateAlwaysEdges U P candidates owner)
variable (hlinear : ∀ {s t : K.Vertex} (e : K.Edge s t) (a : k)
  (x : T.toTower.localCoefficients.A s),
  T.toTower.localCoefficients.edge e (a • x) = a • T.toTower.localCoefficients.edge e x)
variable [Fintype (EdgeName (K := K))] [DecidableEq (EdgeName (K := K))]
variable [Fintype K.TwoCell] [DecidableEq K.TwoCell]
variable (ek : FiniteElimination.Enumeration k)
variable (ee : FiniteElimination.Enumeration (EdgeName (K := K)))
variable (ef : FiniteElimination.Enumeration K.TwoCell)
local notation "Mo" => T.toTower.localCoefficients
local notation "Mn" => (TowerPresentation.localCoefficients (OriginalTowerPresentation.toTower (originalTower T chosen factor)))
local notation "Bn" => FiniteBases.expandedBases T chosen factor bases
local notation "Un" => (fun j => expandedRegion K chosen (U j))
local notation "Pn" => expandedRegion K chosen P
local notation "Cn" => oldEdgeSet K chosen candidates
local notation "en" => FiniteEnumerations.edgeEnumeration K chosen ee
local notation "Aw" => Additive (Kernel p q factor.middle)



attribute [local instance] GeneratedCoverAction.freshComm
variable (S V : Set (EdgeName (K := K))) (hSV : S ⊆ V)
local notation "L" R => StrictSupportedCover.Labels Mn Pn Un Cn (oldEdgeSet K chosen R)
local notation "N" R "at" values => GeneratedStrictObjects.NewObjects T chosen factor bases U P candidates owner hi hlinear ek ee ef values (candidates \ R)

/-- Relax all new strict label conditions while keeping every original local vertex value. -/
noncomputable def labelsInclusion : (L S) →+ (L V) :=
  GeneratedRangeInclusion.labelsInclusion Mn Pn Un Cn (old_set_mono K chosen hSV)

omit [Fintype (EdgeName (K := K))] in
/-- Full new generated native actions commute with all original range inclusions. -/
theorem equivariant (values : ∀ j, RelativeCover.C2 Mo (U j) P)
    (b : Multiplicative (L S)) (y : N S at values) :
    GeneratedCoverRanges.includeNew T chosen factor bases U P candidates owner hi hlinear ek ee ef S V hSV values (b • y) =
      (labelsInclusion T chosen factor U P candidates S V hSV).toMultiplicative b •
        GeneratedCoverRanges.includeNew T chosen factor bases U P candidates owner hi hlinear ek ee ef S V hSV values y := by
  apply Subtype.ext
  funext j
  rw [GeneratedCoverRanges.includeNew_component,GeneratedCoverAction.action_component,
    GeneratedCoverAction.action_component,GeneratedCoverRanges.includeNew_component]
  rfl

/-- Include all native new arrows by retaining their complete original local labels. -/
noncomputable def functor (values : ∀ j, RelativeCover.C2 Mo (U j) P) :
    ActionCategory (Multiplicative (L S)) (N S at values) ⥤ ActionCategory (Multiplicative (L V)) (N V at values) :=
  actionLabelFunctor (labelsInclusion T chosen factor U P candidates S V hSV).toMultiplicative
    (GeneratedCoverRanges.includeNew T chosen factor bases U P candidates owner hi hlinear ek ee ef S V hSV values)
    (equivariant T chosen factor bases U P candidates owner hi hlinear ek ee ef S V hSV values)

omit [Fintype I] [∀ j, DecidablePred (· ∈ (U j).vertices)]
  [∀ j, DecidablePred (· ∈ (U j).edges)] [∀ j, DecidablePred (· ∈ (U j).faces)]
  [DecidablePred (· ∈ P.edges)] [DecidablePred (· ∈ P.faces)]
  [DecidablePred (· ∈ candidates)] [Fintype (EdgeName (K := K))]
  [DecidableEq (EdgeName (K := K))] [Fintype K.TwoCell] [DecidableEq K.TwoCell] in
/-- Full old labels and every fresh displacement commute with the same range inclusion. -/
theorem labels_comparison (b : L S) :
    GeneratedCoverLabels.equivalence T chosen factor U P candidates V owner hi
      (labelsInclusion T chosen factor U P candidates S V hSV b) =
    (RelativeGeneratedNativeRanges.labelsInclusion Mo U P candidates S V hSV
      (GeneratedCoverLabels.equivalence T chosen factor U P candidates S owner hi b).1,
      (GeneratedCoverLabels.equivalence T chosen factor U P candidates S owner hi b).2) := by
  apply Prod.ext
  · apply Subtype.ext
    funext j
    apply Subtype.ext
    rfl
  · rfl

omit [Fintype (EdgeName (K := K))] in
/-- Included native objects retain their whole independently generated component family. -/
theorem functor_object (values : ∀ j, RelativeCover.C2 Mo (U j) P)
    (x : ActionCategory (Multiplicative (L S)) (N S at values)) :
    ((functor T chosen factor bases U P candidates owner hi hlinear ek ee ef S V hSV values).obj x).back.1 = x.back.1 := rfl

omit [Fintype (EdgeName (K := K))] in
/-- Every included native arrow retains every original local vertex label value. -/
theorem functor_label (values : ∀ j, RelativeCover.C2 Mo (U j) P)
    {x y : ActionCategory (Multiplicative (L S)) (N S at values)} (f : x ⟶ y) (j : I) (v : (Un j).vertices) :
    ((((functor T chosen factor bases U P candidates owner hi hlinear ek ee ef S V hSV values).map f).1.toAdd.1 j).1.1 v) =
      ((f.1.toAdd.1 j).1.1 v) := rfl

omit [Fintype (EdgeName (K := K))] in
/-- Native range inclusions compose on every generated object and every complete original arrow. -/
theorem functor_comp (values : ∀ j, RelativeCover.C2 Mo (U j) P)
    (W : Set (EdgeName (K := K))) (hVW : V ⊆ W) :
    functor T chosen factor bases U P candidates owner hi hlinear ek ee ef S V hSV values ⋙
      functor T chosen factor bases U P candidates owner hi hlinear ek ee ef V W hVW values =
    functor T chosen factor bases U P candidates owner hi hlinear ek ee ef S W (hSV.trans hVW) values := rfl

/-- The full native subdivision comparison and permission inclusion commute on all objects and arrows. -/
theorem comparison_functor (values : ∀ j, RelativeCover.C2 Mo (U j) P) :
    functor T chosen factor bases U P candidates owner hi hlinear ek ee ef S V hSV values ⋙
      (GeneratedGroupoidEquivalence.equivalence T chosen factor bases U P candidates owner hi hlinear ek ee ef V values).functor =
    (GeneratedGroupoidEquivalence.equivalence T chosen factor bases U P candidates owner hi hlinear ek ee ef S values).functor ⋙
      RelativeGeneratedNativeRanges.functor Mo bases U P candidates hlinear ek ee ef S V hSV values := by
  rfl

end AAT.AG.RelativeRepairComposition.Subdivision.GeneratedNativeRanges
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.Subdivision.GeneratedNativeRanges
