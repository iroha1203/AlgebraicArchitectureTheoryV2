import Formal.Util.AssertStandardAxioms
import ResearchLean.AG.RelativeRepairComposition.SupportedNativeEquation
import ResearchLean.AG.RelativeRepairComposition.GeneratedCoverAction
import ResearchLean.AG.RelativeRepairComposition.GeneratedPublicRelations

/-!
# Full original actual repairs and strict generated finite-cover coordinates

## Implementation notes

The original actual supported repairs remain independently defined. The
coordinate equivalence composes the original actual-equation correspondence,
finite full-cochain gluing, and the same generated local interfaces. All
labels and original edge choices are retained in both directions.
-/
namespace AAT.AG.RelativeRepairComposition
open CategoryTheory TransportCoherence AbelianLiftingObstruction TransportCoherence.Arbitrary
universe uk uG uE uB uD vE vB vD uI
variable {k : Type uk} [Field k] [Fintype k] [DecidableEq k]
variable {K : FiniteTransportPresentation.{uG}} {I : Type uI} [Fintype I] [DecidableEq I]
variable {E : Type uE} {B : Type uB} {D : Type uD}
variable [Category.{vE} E] [Category.{vB} B] [Category.{vD} D]
variable {p : E ⥤ B} {q : B ⥤ D}
namespace GeneratedCoverRestoration
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

/-- Every original permitted vertex label and every full compatible local label are mutually inverse. -/
noncomputable def labelEquiv : supportedC0 T P.vertices fixed ≃+
    StrictSupportedCover.Labels M P U candidates allowed :=
  (SupportedNativeEquation.gaugeEquiv T P candidates allowed).trans
    (StrictCoverRestoration.labelEquiv M P U candidates allowed enumI hc)

/-- Full original actual repairs and all strict generated public and private coordinates are mutually inverse. -/
noncomputable def objectEquiv : SupportedRepair T fixed ≃
    GeneratedStrictCover.Objects M bases P U candidates hlinear δ enumK enumEdges enumFaces allowed :=
  ((SupportedNativeEquation.repairEquiv T P candidates allowed hfixed).trans
    (StrictCoverRestoration.objectEquiv M P U candidates allowed δ enumI hc)).trans
      (GeneratedStrictCover.objectEquiv M bases P U candidates hlinear δ enumK enumEdges enumFaces allowed)

/-- The original actual gauge action becomes the same generated full-label action. -/
theorem equivariant (b : Multiplicative (supportedC0 T P.vertices fixed)) (R : SupportedRepair T fixed) :
    objectEquiv T bases P U candidates hlinear hfixed enumK enumEdges enumFaces enumI hc allowed (b • R) =
      (labelEquiv T P U candidates enumI hc allowed).toMultiplicative b •
        objectEquiv T bases P U candidates hlinear hfixed enumK enumEdges enumFaces enumI hc allowed R := by
  change GeneratedStrictCover.coordinate M bases P U candidates hlinear δ enumK enumEdges enumFaces allowed
    (StrictCoverRestoration.restrictObjects M P U candidates allowed δ
      (SupportedNativeEquation.repairEquiv T P candidates allowed hfixed (b • R))) = _
  rw [SupportedNativeEquation.repair_equivariant]
  change GeneratedStrictCover.coordinate M bases P U candidates hlinear δ enumK enumEdges enumFaces allowed
    (StrictCoverRestoration.restrictObjects M P U candidates allowed δ
      (SupportedEquation.gauge M P ClosedRegion.all candidates allowed δ
        (SupportedNativeEquation.gaugeEquiv T P candidates allowed b.toAdd)
        (SupportedNativeEquation.repairEquiv T P candidates allowed hfixed R))) = _
  rw [StrictCoverRestoration.restrict_equivariant]
  exact GeneratedCoverAction.equivariant M bases P U candidates hlinear δ enumK enumEdges enumFaces allowed
    (Multiplicative.ofAdd (StrictCoverRestoration.restrictLabels M P U candidates allowed
      (SupportedNativeEquation.gaugeEquiv T P candidates allowed b.toAdd)))
    (StrictCoverRestoration.restrictObjects M P U candidates allowed δ
      (SupportedNativeEquation.repairEquiv T P candidates allowed hfixed R))

/-- Coordinate and reconstruction functors act on the independent full original repair groupoid. -/
noncomputable def equivalence : RepairGroupoid T P.vertices fixed ≌
    GeneratedCoverAction.Groupoid M bases P U candidates hlinear δ enumK enumEdges enumFaces allowed :=
  changedLabelEquivalence (labelEquiv T P U candidates enumI hc allowed).toMultiplicative
    (objectEquiv T bases P U candidates hlinear hfixed enumK enumEdges enumFaces enumI hc allowed)
    (equivariant T bases P U candidates hlinear hfixed enumK enumEdges enumFaces enumI hc allowed)

/-- Reconstruction after coordinates restores the full actual object and every original gauge arrow exactly. -/
theorem functor_inverse :
    (equivalence T bases P U candidates hlinear hfixed enumK enumEdges enumFaces enumI hc allowed).functor ⋙
      (equivalence T bases P U candidates hlinear hfixed enumK enumEdges enumFaces enumI hc allowed).inverse =
        𝟭 (RepairGroupoid T P.vertices fixed) :=
  changed_label_functor_inverse (labelEquiv T P U candidates enumI hc allowed).toMultiplicative
    (objectEquiv T bases P U candidates hlinear hfixed enumK enumEdges enumFaces enumI hc allowed)
    (equivariant T bases P U candidates hlinear hfixed enumK enumEdges enumFaces enumI hc allowed)

/-- Coordinates after reconstruction restore every public value, private vector and full arrow exactly. -/
theorem inverse_functor :
    (equivalence T bases P U candidates hlinear hfixed enumK enumEdges enumFaces enumI hc allowed).inverse ⋙
      (equivalence T bases P U candidates hlinear hfixed enumK enumEdges enumFaces enumI hc allowed).functor =
        𝟭 (GeneratedCoverAction.Groupoid M bases P U candidates hlinear δ enumK enumEdges enumFaces allowed) :=
  changed_label_inverse_functor (labelEquiv T P U candidates enumI hc allowed).toMultiplicative
    (objectEquiv T bases P U candidates hlinear hfixed enumK enumEdges enumFaces enumI hc allowed)
    (equivariant T bases P U candidates hlinear hfixed enumK enumEdges enumFaces enumI hc allowed)

/-- Restoring a coordinate family returns the same correction on every original edge in every region. -/
theorem inverse_edge_value
    (y : GeneratedStrictCover.Objects M bases P U candidates hlinear δ enumK enumEdges enumFaces allowed)
    (i : I) (e : (U i).edges) :
    T.solutionCorrection ((objectEquiv T bases P U candidates hlinear hfixed enumK enumEdges enumFaces enumI hc allowed).symm y).1 e.1 =
      ((GeneratedStrictCover.restore M bases P U candidates hlinear δ enumK enumEdges enumFaces allowed y).1 i).1.1.1 e := by
  change T.solutionCorrection ((SupportedNativeEquation.repairEquiv T P candidates allowed hfixed).symm
    (StrictCoverRestoration.glueObjects M P U candidates allowed δ enumI hc
      (GeneratedStrictCover.restore M bases P U candidates hlinear δ enumK enumEdges enumFaces allowed y))).1 e.1 = _
  rw [SupportedNativeEquation.repair_inverse_value]
  exact FiniteCoverGlue.glue1_value M P U enumI hc
    (StrictSupportedCover.localEdges M P U candidates allowed δ
      (GeneratedStrictCover.restore M bases P U candidates hlinear δ enumK enumEdges enumFaces allowed y)) i e

/-- Original actual repairs preserve every named correction under forward coordinates. -/
theorem forward_edge_value (R : SupportedRepair T fixed) (i : I) (e : (U i).edges) :
    ((GeneratedStrictCover.restore M bases P U candidates hlinear δ enumK enumEdges enumFaces allowed
      (objectEquiv T bases P U candidates hlinear hfixed enumK enumEdges enumFaces enumI hc allowed R)).1 i).1.1.1 e =
        T.solutionCorrection R.1 e.1 := by
  change ((GeneratedStrictCover.restore M bases P U candidates hlinear δ enumK enumEdges enumFaces allowed
    (GeneratedStrictCover.coordinate M bases P U candidates hlinear δ enumK enumEdges enumFaces allowed
      (StrictCoverRestoration.restrictObjects M P U candidates allowed δ
        (SupportedNativeEquation.repairEquiv T P candidates allowed hfixed R)))).1 i).1.1.1 e = _
  rw [GeneratedStrictCover.restore_coordinate]
  exact SupportedNativeEquation.repair_value T P candidates allowed hfixed R e.1

/-- Every reconstructed actual morphism is the correction of the same original reference edge. -/
theorem inverse_choice
    (y : GeneratedStrictCover.Objects M bases P U candidates hlinear δ enumK enumEdges enumFaces allowed)
    {i j : K.Vertex} (e : K.Edge i j) :
    ((objectEquiv T bases P U candidates hlinear hfixed enumK enumEdges enumFaces enumI hc allowed).symm y).1.choice e =
      T.correctionChoice (ActualEquation.originalEdgeEquiv T P
        (StrictCoverRestoration.glueObjects M P U candidates allowed δ enumI hc
          (GeneratedStrictCover.restore M bases P U candidates hlinear δ enumK enumEdges enumFaces allowed y)).1.1).1 e :=
  SupportedNativeEquation.inverse_choice T P candidates allowed hfixed
    (StrictCoverRestoration.glueObjects M P U candidates allowed δ enumI hc
      (GeneratedStrictCover.restore M bases P U candidates hlinear δ enumK enumEdges enumFaces allowed y)) e

omit [Fintype I] [DecidableEq I] [DecidablePred (· ∈ P.edges)] [DecidablePred (· ∈ P.faces)]
  [∀ i, DecidablePred (· ∈ (U i).edges)] [∀ i, DecidablePred (· ∈ (U i).faces)]
  [DecidablePred (· ∈ candidates)] [Fintype (EdgeName (K := K))] [DecidableEq (EdgeName (K := K))]
  [Fintype K.TwoCell] [DecidableEq K.TwoCell] in
/-- The forward label map preserves every original vertex value in every region. -/
theorem label_value (b : supportedC0 T P.vertices fixed) (i : I) (v : (U i).vertices) :
    ((labelEquiv T P U candidates enumI hc allowed b).1 i).1.1 v = b.1 v.1 :=
  SupportedNativeEquation.gauge_value T P candidates allowed b v.1

omit [Fintype I] [DecidableEq I] [DecidablePred (· ∈ P.edges)] [DecidablePred (· ∈ P.faces)]
  [∀ i, DecidablePred (· ∈ (U i).edges)] [∀ i, DecidablePred (· ∈ (U i).faces)]
  [DecidablePred (· ∈ candidates)] [Fintype (EdgeName (K := K))] [DecidableEq (EdgeName (K := K))]
  [Fintype K.TwoCell] [DecidableEq K.TwoCell] in
/-- The inverse label map restores every full original local label value. -/
theorem label_inverse_value (b : StrictSupportedCover.Labels M P U candidates allowed)
    (i : I) (v : (U i).vertices) :
    ((labelEquiv T P U candidates enumI hc allowed).symm b).1 v.1 = (b.1 i).1.1 v := by
  change ((SupportedNativeEquation.gaugeEquiv T P candidates allowed).symm
    (StrictCoverRestoration.glueLabels M P U candidates allowed enumI hc b)).1 v.1 = _
  rw [SupportedNativeEquation.gauge_inverse_value]
  exact FiniteCoverGlue.glue0_value M P U enumI hc
    (StrictSupportedCover.localLabels M P U candidates allowed b) i v

/-- Every forward arrow retains every original vertex label, including all stabilizers. -/
theorem functor_label_value {R Q : RepairGroupoid T P.vertices fixed} (b : R ⟶ Q) (i : I) (v : (U i).vertices) :
    ((((equivalence T bases P U candidates hlinear hfixed enumK enumEdges enumFaces enumI hc allowed).functor.map b).1.toAdd).1 i).1.1 v =
      b.1.toAdd.1 v.1 := label_value T P U candidates enumI hc allowed b.1.toAdd i v

/-- Every inverse arrow restores every original compatible local vertex label. -/
theorem inverse_label_value
    {R Q : GeneratedCoverAction.Groupoid M bases P U candidates hlinear δ enumK enumEdges enumFaces allowed}
    (b : R ⟶ Q) (i : I) (v : (U i).vertices) :
    ((equivalence T bases P U candidates hlinear hfixed enumK enumEdges enumFaces enumI hc allowed).inverse.map b).1.toAdd.1 v.1 =
      (b.1.toAdd.1 i).1.1 v := label_inverse_value T P U candidates enumI hc allowed b.1.toAdd i v

include enumI hc in
/-- The independent actual supported repair exists exactly when the public relations and zero/shared conditions are feasible. -/
theorem repair_nonempty_iff_public :
    Nonempty (SupportedRepair T fixed) ↔
      Nonempty (GeneratedPublicRelations.Objects M bases P U candidates hlinear δ enumK enumEdges enumFaces allowed) :=
  (objectEquiv T bases P U candidates hlinear hfixed enumK enumEdges enumFaces enumI hc allowed).nonempty_congr.trans
    (GeneratedPublicRelations.nonempty_iff_public M bases P U candidates hlinear δ enumK enumEdges enumFaces allowed)

end GeneratedCoverRestoration
end AAT.AG.RelativeRepairComposition
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
