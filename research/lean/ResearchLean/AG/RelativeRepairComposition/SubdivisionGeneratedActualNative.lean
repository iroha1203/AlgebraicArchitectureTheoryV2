import ResearchLean.AG.RelativeRepairComposition.SubdivisionGeneratedActualComparison
import ResearchLean.AG.RelativeRepairComposition.SubdivisionGeneratedCoverAction
import ResearchLean.AG.RelativeRepairComposition.SubdivisionSupportedCochains
import ResearchLean.AG.RelativeRepairComposition.SubdivisionGaugeEquations

/-!
# Full native actual repairs and independent strict generated arrows

## Implementation notes

Actual supported labels are all original vertex reidentifications. The same
full displacement decomposition and independently generated strict comparison
supply mutually inverse label maps. Object equivariance follows from actual
collapse, actual fresh gauge equations and independent old generation.
-/
namespace AAT.AG.RelativeRepairComposition.Subdivision.GeneratedActualNative
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


variable (hfixed : ∀ f ∈ P.faces,
  T.toTower.upper.pathLift (K.twoLeft f) ≫ FiberAut.hom (T.comparator f) =
    T.toTower.upper.pathLift (K.twoRight f))
variable (ei : FiniteElimination.Enumeration I) (hc : ClosedRegion.IndexedCover U)
variable (allowed : Set (EdgeName (K := K)))
local notation "fixed" => fixedEdgesForRange P.edges candidates allowed
local notation "values" => (fun j => -CoverEquation.defect Mo P (ActualEquation.defectFamily T P hfixed) (U j))



attribute [local instance] GeneratedCoverAction.freshComm
local notation "Gn" => supportedC0 (originalTower T chosen factor) (Sum.inl '' P.vertices) (oldEdgeSet K chosen fixed)
local notation "Ln" => StrictSupportedCover.Labels Mn Pn Un Cn (oldEdgeSet K chosen allowed)
local notation "Lo" => StrictSupportedCover.Labels Mo P U candidates allowed
local notation "N" => GeneratedStrictObjects.NewObjects T chosen factor bases U P candidates owner hi hlinear ek ee ef values (candidates \ allowed)

/-- Independent old extraction commutes with every full original actual gauge label. -/
theorem old_equivariant
    (b : Multiplicative (supportedC0 T P.vertices fixed)) (R : SupportedRepair T fixed) :
    GeneratedCoverRestoration.oldObjectEquiv T bases U P candidates hlinear ek ee ef hfixed ei hc allowed (b • R) =
      (AAT.AG.RelativeRepairComposition.GeneratedCoverRestoration.labelEquiv T P U candidates ei hc allowed).toMultiplicative b •
        GeneratedCoverRestoration.oldObjectEquiv T bases U P candidates hlinear ek ee ef hfixed ei hc allowed R := by
  change RelativeGeneratedDefectCover.objectsEquiv Mo bases U P candidates hlinear ek ee ef
      (ActualEquation.defectFamily T P hfixed) allowed
      (AAT.AG.RelativeRepairComposition.GeneratedCoverRestoration.objectEquiv T bases P U candidates hlinear hfixed ek ee ef ei hc allowed (b • R)) = _
  rw [AAT.AG.RelativeRepairComposition.GeneratedCoverRestoration.equivariant,
    RelativeGeneratedDefectCover.equivariant]
  rfl

/-- Every full actual new label and every independent full strict generated label have both inverse maps. -/
noncomputable def labelEquiv : Gn ≃+ Ln :=
  ((supported0Equiv T chosen factor P.vertices fixed
    (GeneratedActualComparison.chosen_not_fixed chosen U P candidates owner hi allowed)).trans
    (AddEquiv.prodCongr
      (AAT.AG.RelativeRepairComposition.GeneratedCoverRestoration.labelEquiv T P U candidates ei hc allowed)
      (AddEquiv.refl Aw))).trans
    (GeneratedCoverLabels.equivalence T chosen factor U P candidates allowed owner hi).symm

omit [Fintype I] [∀ j, DecidablePred (· ∈ (U j).edges)]
  [∀ j, DecidablePred (· ∈ (U j).faces)] [DecidablePred (· ∈ P.edges)]
  [DecidablePred (· ∈ P.faces)] [DecidablePred (· ∈ candidates)]
  [Fintype (EdgeName (K := K))] [DecidableEq (EdgeName (K := K))]
  [Fintype K.TwoCell] [DecidableEq K.TwoCell] in
/-- Full label comparison agrees with actual old labels and actual fresh displacement. -/
theorem label_comparison (b : Gn) :
    GeneratedCoverLabels.equivalence T chosen factor U P candidates allowed owner hi
      (labelEquiv T chosen factor U P candidates owner hi ei hc allowed b) =
    (AAT.AG.RelativeRepairComposition.GeneratedCoverRestoration.labelEquiv T P U candidates ei hc allowed
      (collapseAllowedLabel T chosen factor P.vertices fixed
        (GeneratedActualComparison.chosen_not_fixed chosen U P candidates owner hi allowed) b),
      b.1 (.inr ()) - rho1AddEquiv T chosen factor (b.1 (.inl chosen.1))) :=
  (GeneratedCoverLabels.equivalence T chosen factor U P candidates allowed owner hi).apply_symm_apply _

/-- Full independent new extraction commutes with every original actual supported reidentification. -/
theorem equivariant (b : Multiplicative Gn)
    (R : SupportedRepair (originalTower T chosen factor) (oldEdgeSet K chosen fixed)) :
    GeneratedCoverRestoration.newObjectEquiv T chosen factor bases U P candidates owner hi hlinear ek ee ef hfixed ei hc allowed (b • R) =
      (labelEquiv T chosen factor U P candidates owner hi ei hc allowed).toMultiplicative b •
        GeneratedCoverRestoration.newObjectEquiv T chosen factor bases U P candidates owner hi hlinear ek ee ef hfixed ei hc allowed R := by
  apply (GeneratedStrictObjects.rangeObjectsEquiv T chosen factor bases U P candidates owner hi hlinear ek ee ef allowed values).injective
  rw [GeneratedActualComparison.comparison_actual,GeneratedCoverAction.objects_equivariant,
    GeneratedActualComparison.comparison_actual,SupplementalAction.product_action_value]
  have hb := label_comparison T chosen factor U P candidates owner hi ei hc allowed b.toAdd
  apply Prod.ext
  · change GeneratedCoverRestoration.oldObjectEquiv T bases U P candidates hlinear ek ee ef hfixed ei hc allowed
        (collapseSupported T chosen factor fixed
          (GeneratedActualComparison.chosen_not_fixed chosen U P candidates owner hi allowed)
          (repairGauge (originalTower T chosen factor) (Sum.inl '' P.vertices) (oldEdgeSet K chosen fixed) b.toAdd R)) =
      Multiplicative.ofAdd
        (GeneratedCoverLabels.equivalence T chosen factor U P candidates allowed owner hi
          (labelEquiv T chosen factor U P candidates owner hi ei hc allowed b.toAdd)).1 •
      GeneratedCoverRestoration.oldObjectEquiv T bases U P candidates hlinear ek ee ef hfixed ei hc allowed
        (collapseSupported T chosen factor fixed
          (GeneratedActualComparison.chosen_not_fixed chosen U P candidates owner hi allowed) R)
    rw [collapseSupported_gauge,hb]
    exact old_equivariant T bases U P candidates hlinear ek ee ef hfixed ei hc allowed
      (Multiplicative.ofAdd (collapseAllowedLabel T chosen factor P.vertices fixed
        (GeneratedActualComparison.chosen_not_fixed chosen U P candidates owner hi allowed) b.toAdd)) _
  · change (originalTower T chosen factor).solutionCorrection
        ((originalTower T chosen factor).vertexGauge b.toAdd.1 R.1) (firstEdgeName K chosen) =
      (show Aw from (originalTower T chosen factor).solutionCorrection R.1 (firstEdgeName K chosen)) +
        (GeneratedCoverLabels.equivalence T chosen factor U P candidates allowed owner hi
          (labelEquiv T chosen factor U P candidates owner hi ei hc allowed b.toAdd)).2
    rw [hb]
    exact vertexGauge_first T chosen factor b.toAdd.1 R.1

/-- All native actual and independently generated strict groupoids have full inverse functors. -/
noncomputable def equivalence :
    RepairGroupoid (originalTower T chosen factor) (Sum.inl '' P.vertices) (oldEdgeSet K chosen fixed) ≌
      ActionCategory (Multiplicative Ln) N :=
  changedLabelEquivalence (labelEquiv T chosen factor U P candidates owner hi ei hc allowed).toMultiplicative
    (GeneratedCoverRestoration.newObjectEquiv T chosen factor bases U P candidates owner hi hlinear ek ee ef hfixed ei hc allowed)
    (equivariant T chosen factor bases U P candidates owner hi hlinear ek ee ef hfixed ei hc allowed)

/-- Native forward arrows retain their entire independent strict generated label. -/
theorem functor_label
    {x y : RepairGroupoid (originalTower T chosen factor) (Sum.inl '' P.vertices) (oldEdgeSet K chosen fixed)} (f : x ⟶ y) :
    ((equivalence T chosen factor bases U P candidates owner hi hlinear ek ee ef hfixed ei hc allowed).functor.map f).1 =
      (labelEquiv T chosen factor U P candidates owner hi ei hc allowed).toMultiplicative f.1 := rfl

/-- Native inverse arrows restore their entire original actual vertex label. -/
theorem inverse_label {x y : ActionCategory (Multiplicative Ln) N} (f : x ⟶ y) :
    ((equivalence T chosen factor bases U P candidates owner hi hlinear ek ee ef hfixed ei hc allowed).inverse.map f).1 =
      (labelEquiv T chosen factor U P candidates owner hi ei hc allowed).toMultiplicative.symm f.1 := rfl

end AAT.AG.RelativeRepairComposition.Subdivision.GeneratedActualNative
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.Subdivision.GeneratedActualNative
