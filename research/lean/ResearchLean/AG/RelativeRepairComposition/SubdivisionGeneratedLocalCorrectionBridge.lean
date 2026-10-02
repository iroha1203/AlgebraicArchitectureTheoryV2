import ResearchLean.AG.RelativeRepairComposition.SubdivisionGeneratedCoverRestoration
import ResearchLean.AG.RelativeRepairComposition.SubdivisionGeneratedStrictObjects
import ResearchLean.AG.RelativeRepairComposition.RelativeActualGeneratedCover
import ResearchLean.AG.RelativeRepairComposition.SubdivisionPermissions

/-!
# Independent generation preserves every actual local correction

A complete local equation supplied independently from actual restoration is
sent to the same component by the original local generator. Equality is
checked at every original new edge before any generated coordinate is read.
-/
namespace AAT.AG.RelativeRepairComposition.Subdivision.GeneratedLocalCorrectionBridge
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

omit [Fintype (EdgeName (K := K))] in
/-- Full actual correction equality identifies the independent generated local component. -/
theorem component_eq
    (R : SupportedRepair (originalTower T chosen factor) (oldEdgeSet K chosen fixed)) (j : I)
    (c : {h : RelativeCover.C1 Mn (Un j) Pn //
      RelativeCover.d1 Mn (Un j) Pn h = (local2Equiv T chosen factor (U j) P).symm (values j)})
    (hcorrection : ∀ e : (Un j).edges, c.1.1 e = (originalTower T chosen factor).solutionCorrection R.1 e.1) :
    (GeneratedCoverRestoration.newObjectEquiv T chosen factor bases U P candidates owner hi
      hlinear ek ee ef hfixed ei hc allowed R).1 j =
      GeneratedRelations.newGeneratedEquiv T chosen factor bases U P candidates owner hi j
        hlinear ek ee ef (value := values j) c := by
  apply (GeneratedRelations.newGeneratedEquiv T chosen factor bases U P candidates owner hi j
    hlinear ek ee ef (value := values j)).symm.injective
  rw [Equiv.symm_apply_apply]
  apply Subtype.ext
  apply Subtype.ext
  funext e
  exact (GeneratedCoverRestoration.new_forward_edge_value T chosen factor bases U P candidates owner hi
    hlinear ek ee ef hfixed ei hc allowed R j e).trans (hcorrection e).symm

omit [Fintype (EdgeName (K := K))] in
/-- Explicit equality transport keeps every full actual local correction. -/
theorem component_heq_of_rhs_eq
    (R : SupportedRepair (originalTower T chosen factor) (oldEdgeSet K chosen fixed)) (j : I)
    (value : RelativeCover.C2 Mo (U j) P) (hrhs : values j = value)
    (c : {h : RelativeCover.C1 Mn (Un j) Pn //
      RelativeCover.d1 Mn (Un j) Pn h = (local2Equiv T chosen factor (U j) P).symm value})
    (hcorrection : ∀ e : (Un j).edges, c.1.1 e = (originalTower T chosen factor).solutionCorrection R.1 e.1) :
    HEq ((GeneratedCoverRestoration.newObjectEquiv T chosen factor bases U P candidates owner hi
      hlinear ek ee ef hfixed ei hc allowed R).1 j)
      (GeneratedRelations.newGeneratedEquiv T chosen factor bases U P candidates owner hi j
        hlinear ek ee ef (value := value) c) := by
  subst value
  exact heq_of_eq (GeneratedLocalCorrectionBridge.component_eq T chosen factor bases U P candidates owner hi
    hlinear ek ee ef hfixed ei hc allowed R j c hcorrection)


end AAT.AG.RelativeRepairComposition.Subdivision.GeneratedLocalCorrectionBridge
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.Subdivision.GeneratedLocalCorrectionBridge
