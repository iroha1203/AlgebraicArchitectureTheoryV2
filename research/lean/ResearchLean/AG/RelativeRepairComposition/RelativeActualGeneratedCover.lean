import ResearchLean.AG.RelativeRepairComposition.GeneratedCoverRestoration
import ResearchLean.AG.RelativeRepairComposition.RelativeGeneratedDefectCover

/-!
# Full actual repairs restored from arbitrary-input strict generators

## Implementation notes

Actual signed face defects are inputs to the independent finite generators.
The full original repair and label correspondences are composed with the
literal arbitrary-input identification. Every actual named correction and
native arrow is retained in both directions.
-/
namespace AAT.AG.RelativeRepairComposition
open CategoryTheory TransportCoherence AbelianLiftingObstruction TransportCoherence.Arbitrary
universe uk uG uE uB uD vE vB vD uI
variable {k : Type uk} [Field k] [Fintype k] [DecidableEq k]
variable {K : FiniteTransportPresentation.{uG}} {I : Type uI} [Fintype I] [DecidableEq I]
variable {E : Type uE} {B : Type uB} {D : Type uD}
variable [Category.{vE} E] [Category.{vB} B] [Category.{vD} D]
variable {p : E ⥤ B} {q : B ⥤ D}
namespace RelativeActualGeneratedCover
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
variable (T : OriginalTowerPresentation K p q)
local notation "M" => T.toTower.localCoefficients
variable [∀ v, Module k ((T.toTower.localCoefficients).A v)]
variable (bases : FiniteFamily.Bases (k := k) (T.toTower.localCoefficients).A)
variable (P : ClosedRegion K) (U : I → ClosedRegion K)
variable [DecidablePred (· ∈ P.edges)] [DecidablePred (· ∈ P.faces)]
variable [∀ i, DecidablePred (· ∈ (U i).vertices)]
variable [∀ i, DecidablePred (· ∈ (U i).edges)] [∀ i, DecidablePred (· ∈ (U i).faces)]
variable (candidates : Set (EdgeName (K := K))) [DecidablePred (· ∈ candidates)]
variable (hlinear : ∀ {i j : K.Vertex} (e : K.Edge i j) (t : k) (x : (T.toTower.localCoefficients).A i),
  (T.toTower.localCoefficients).edge e (t • x) = t • (T.toTower.localCoefficients).edge e x)
variable (hfixed : ∀ f ∈ P.faces,
  T.toTower.upper.pathLift (K.twoLeft f) ≫ FiberAut.hom (T.comparator f) =
    T.toTower.upper.pathLift (K.twoRight f))
local notation "δ" => ActualEquation.defectFamily T P hfixed
variable [Fintype (EdgeName (K := K))] [DecidableEq (EdgeName (K := K))]
variable [Fintype K.TwoCell] [DecidableEq K.TwoCell]
variable (enumK : FiniteElimination.Enumeration k)
variable (enumEdges : FiniteElimination.Enumeration (EdgeName (K := K)))
variable (enumFaces : FiniteElimination.Enumeration K.TwoCell)
variable (enumI : FiniteElimination.Enumeration I) (hc : ClosedRegion.IndexedCover U)
variable (allowed : Set (EdgeName (K := K)))
local notation "fixed" => fixedEdgesForRange P.edges candidates allowed


local notation "values" => (fun j => -CoverEquation.defect M P δ (U j))
local notation "Objects" => RelativeGeneratedStrictCover.Objects M bases U P candidates hlinear enumK enumEdges enumFaces values (candidates \ allowed)

/-- Every independent full actual repair has mutually inverse independent strict generated coordinates. -/
noncomputable def objectEquiv : SupportedRepair T fixed ≃ Objects :=
  (GeneratedCoverRestoration.objectEquiv T bases P U candidates hlinear hfixed
    enumK enumEdges enumFaces enumI hc allowed).trans
    (RelativeGeneratedDefectCover.objectsEquiv M bases U P candidates hlinear
      enumK enumEdges enumFaces δ allowed)

/-- The full actual and independent arbitrary-input generated groupoids are natively equivalent. -/
noncomputable def equivalence : RepairGroupoid T P.vertices fixed ≌
    ActionCategory (Multiplicative (StrictSupportedCover.Labels M P U candidates allowed)) Objects :=
  (GeneratedCoverRestoration.equivalence T bases P U candidates hlinear hfixed
    enumK enumEdges enumFaces enumI hc allowed).trans
    (RelativeGeneratedDefectCover.equivalence M bases U P candidates hlinear
      enumK enumEdges enumFaces δ allowed)

/-- Extraction reads every independent local relation, public value and private kernel unchanged. -/
theorem forward_component (R : SupportedRepair T fixed) (j : I) :
    (objectEquiv T bases P U candidates hlinear hfixed enumK enumEdges enumFaces enumI hc allowed R).1 j =
      (GeneratedCoverRestoration.objectEquiv T bases P U candidates hlinear hfixed
        enumK enumEdges enumFaces enumI hc allowed R).1 j := rfl

/-- Restoring arbitrary generated coordinates recovers the full actual correction on every original named edge. -/
theorem inverse_edge_value (y : Objects) (j : I) (e : (U j).edges) :
    T.solutionCorrection ((objectEquiv T bases P U candidates hlinear hfixed
      enumK enumEdges enumFaces enumI hc allowed).symm y).1 e.1 =
      ((FiniteNative.generatedRelativeEquiv M bases (U j) P
        (ClosedRegion.privateAlwaysEdges U P candidates j) hlinear (values j)
        enumK enumEdges enumFaces).symm (y.1 j)).1.1 e :=
  GeneratedCoverRestoration.inverse_edge_value T bases P U candidates hlinear hfixed
    enumK enumEdges enumFaces enumI hc allowed
    ((RelativeGeneratedDefectCover.objectsEquiv M bases U P candidates hlinear
      enumK enumEdges enumFaces δ allowed).symm y) j e

/-- Forward reconstruction keeps each entire actual original edge correction. -/
theorem forward_edge_value (R : SupportedRepair T fixed) (j : I) (e : (U j).edges) :
    ((FiniteNative.generatedRelativeEquiv M bases (U j) P
      (ClosedRegion.privateAlwaysEdges U P candidates j) hlinear (values j)
      enumK enumEdges enumFaces).symm
      ((objectEquiv T bases P U candidates hlinear hfixed
        enumK enumEdges enumFaces enumI hc allowed R).1 j)).1.1 e =
        T.solutionCorrection R.1 e.1 :=
  GeneratedCoverRestoration.forward_edge_value T bases P U candidates hlinear hfixed
    enumK enumEdges enumFaces enumI hc allowed R j e

/-- All forward native arrows keep the same complete original strict label family. -/
theorem functor_label {R Q : RepairGroupoid T P.vertices fixed} (f : R ⟶ Q) :
    ((equivalence T bases P U candidates hlinear hfixed
      enumK enumEdges enumFaces enumI hc allowed).functor.map f).1 =
      ((GeneratedCoverRestoration.labelEquiv T P U candidates enumI hc allowed).toMultiplicative f.1) := rfl

/-- All inverse native arrows restore the complete original actual label. -/
theorem inverse_label
    {R Q : ActionCategory (Multiplicative (StrictSupportedCover.Labels M P U candidates allowed)) Objects} (f : R ⟶ Q) :
    ((equivalence T bases P U candidates hlinear hfixed
      enumK enumEdges enumFaces enumI hc allowed).inverse.map f).1 =
      (GeneratedCoverRestoration.labelEquiv T P U candidates enumI hc allowed).toMultiplicative.symm f.1 := rfl

end RelativeActualGeneratedCover
end AAT.AG.RelativeRepairComposition
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.RelativeActualGeneratedCover
