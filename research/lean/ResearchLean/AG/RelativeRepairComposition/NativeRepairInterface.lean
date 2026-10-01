import Formal.Util.AssertStandardAxioms
import ResearchLean.AG.RelativeRepairComposition.NativeLocalInterface

/-!
# Generated local interfaces of actual original repairs

## Implementation notes

The input tower determines its full coefficient kernels and actual defect.
Only its supplied full bases and the linear transport regime are additional
finite coordinate data. The section is generated from its own private matrix.
-/
namespace AAT.AG.RelativeRepairComposition
open CategoryTheory TransportCoherence AbelianLiftingObstruction TransportCoherence.Arbitrary
universe uk uG uE uB uD vE vB vD
variable {k : Type uk} [Field k] [Fintype k] [DecidableEq k]
variable {K : FiniteTransportPresentation.{uG}}
variable {E : Type uE} {B : Type uB} {D : Type uD}
variable [Category.{vE} E] [Category.{vB} B] [Category.{vD} D]
variable {p : E ⥤ B} {q : B ⥤ D}
namespace NativeRepairInterface
variable (T : OriginalTowerPresentation K p q)
local notation "M" => T.toTower.localCoefficients
variable [∀ v, Module k ((T.toTower.localCoefficients).A v)]
variable (bases : FiniteFamily.Bases (k := k) (T.toTower.localCoefficients).A) (U P : ClosedRegion K)
variable [DecidablePred (· ∈ P.vertices)] [DecidablePred (· ∈ P.edges)] [DecidablePred (· ∈ P.faces)]
variable [DecidablePred (· ∈ U.vertices)] [DecidablePred (· ∈ U.edges)] [DecidablePred (· ∈ U.faces)]
variable (internalEdges : Set (EdgeName (K := K))) [DecidablePred (· ∈ internalEdges)]
variable (hlinear : ∀ {i j : K.Vertex} (e : K.Edge i j) (t : k) (x : (T.toTower.localCoefficients).A i),
  (T.toTower.localCoefficients).edge e (t • x) = t • (T.toTower.localCoefficients).edge e x)
variable (hfixed : ∀ f ∈ P.faces,
  T.toTower.upper.pathLift (K.twoLeft f) ≫ FiberAut.hom (T.comparator f) =
    T.toTower.upper.pathLift (K.twoRight f))
variable [Fintype (EdgeName (K := K))] [DecidableEq (EdgeName (K := K))]
variable [Fintype K.TwoCell] [DecidableEq K.TwoCell]
variable (enumK : FiniteElimination.Enumeration k)
variable (enumEdges : FiniteElimination.Enumeration (EdgeName (K := K)))
variable (enumFaces : FiniteElimination.Enumeration K.TwoCell)
local notation "δ" => ActualEquation.defectFamily T P hfixed

/-- The whole generated interface uses the actual tower's defect and full coefficient kernels. -/
abbrev Objects := FiniteNative.GeneratedObjects M bases U P internalEdges hlinear δ enumK enumEdges enumFaces

/-- Every independent actual repair has full mutually inverse generated coordinates. -/
noncomputable def repairEquiv :
    SupportedRepair (ClosedRegion.restrictTower U T) (ClosedRegion.nativeIntersection U P).edges ≃
      Objects T bases U P internalEdges hlinear hfixed enumK enumEdges enumFaces :=
  (ActualEquation.nativeRepairEquiv T P hfixed U).trans
    (FiniteNative.generatedSolutionEquiv M bases U P internalEdges hlinear δ enumK enumEdges enumFaces)

omit [DecidablePred (· ∈ P.vertices)] in
/-- Every full native vertex gauge acts through the same original-index label. -/
theorem repair_equivariant
    (b : Multiplicative (supportedC0 (ClosedRegion.restrictTower U T)
      (ClosedRegion.nativeIntersection U P).vertices (ClosedRegion.nativeIntersection U P).edges))
    (R : SupportedRepair (ClosedRegion.restrictTower U T) (ClosedRegion.nativeIntersection U P).edges) :
    repairEquiv T bases U P internalEdges hlinear hfixed enumK enumEdges enumFaces (b • R) =
      (ActualEquation.nativeGaugeEquiv T P U).toMultiplicative b •
        repairEquiv T bases U P internalEdges hlinear hfixed enumK enumEdges enumFaces R := by
  exact (congrArg (FiniteNative.generatedSolutionEquiv M bases U P internalEdges hlinear δ enumK enumEdges enumFaces)
    (ActualEquation.native_repair_equivariant T P hfixed U b R)).trans
      (FiniteNative.generated_solution_equivariant M bases U P internalEdges hlinear δ enumK enumEdges enumFaces
        ((ActualEquation.nativeGaugeEquiv T P U).toMultiplicative b)
        (ActualEquation.nativeRepairEquiv T P hfixed U R))

/-- All actual repairs and all original gauge arrows have the generated native interface. -/
noncomputable def equivalence : RepairGroupoid (ClosedRegion.restrictTower U T)
    (ClosedRegion.nativeIntersection U P).vertices (ClosedRegion.nativeIntersection U P).edges ≌
    FiniteNative.GeneratedGroupoid M bases U P internalEdges hlinear δ enumK enumEdges enumFaces :=
  changedLabelEquivalence (ActualEquation.nativeGaugeEquiv T P U).toMultiplicative
    (repairEquiv T bases U P internalEdges hlinear hfixed enumK enumEdges enumFaces)
    (repair_equivariant T bases U P internalEdges hlinear hfixed enumK enumEdges enumFaces)

omit [DecidablePred (· ∈ P.vertices)] in
/-- Inverse coordinates restore the entire independent actual repair. -/
theorem left_obj (R : RepairGroupoid (ClosedRegion.restrictTower U T)
    (ClosedRegion.nativeIntersection U P).vertices (ClosedRegion.nativeIntersection U P).edges) :
    (equivalence T bases U P internalEdges hlinear hfixed enumK enumEdges enumFaces).inverse.obj
      ((equivalence T bases U P internalEdges hlinear hfixed enumK enumEdges enumFaces).functor.obj R) = R :=
  changed_label_left_obj _ _
    (repair_equivariant T bases U P internalEdges hlinear hfixed enumK enumEdges enumFaces) R

omit [DecidablePred (· ∈ P.vertices)] in
/-- Forward coordinates restore every public and internal interface value. -/
theorem right_obj
    (y : FiniteNative.GeneratedGroupoid M bases U P internalEdges hlinear δ enumK enumEdges enumFaces) :
    (equivalence T bases U P internalEdges hlinear hfixed enumK enumEdges enumFaces).functor.obj
      ((equivalence T bases U P internalEdges hlinear hfixed enumK enumEdges enumFaces).inverse.obj y) = y :=
  changed_label_right_obj _ _
    (repair_equivariant T bases U P internalEdges hlinear hfixed enumK enumEdges enumFaces) y

omit [DecidablePred (· ∈ P.vertices)] in
/-- Every forward gauge arrow retains each original native vertex-label value. -/
theorem functor_label_value
    {R Q : RepairGroupoid (ClosedRegion.restrictTower U T)
      (ClosedRegion.nativeIntersection U P).vertices (ClosedRegion.nativeIntersection U P).edges}
    (b : R ⟶ Q) (v : U.vertices) :
    ((equivalence T bases U P internalEdges hlinear hfixed enumK enumEdges enumFaces).functor.map b).1.toAdd.1 v =
      b.1.toAdd.1 v := rfl

omit [DecidablePred (· ∈ P.vertices)] in
/-- Every inverse gauge arrow restores each original native vertex-label value. -/
theorem inverse_label_value
    {y y' : FiniteNative.GeneratedGroupoid M bases U P internalEdges hlinear δ enumK enumEdges enumFaces}
    (b : y ⟶ y') (v : U.vertices) :
    ((equivalence T bases U P internalEdges hlinear hfixed enumK enumEdges enumFaces).inverse.map b).1.toAdd.1 v =
      b.1.toAdd.1 v := rfl

omit [DecidablePred (· ∈ P.vertices)] in
/-- Inverse interface coordinates reconstruct the actual original morphism on each native edge. -/
theorem inverse_choice
    (y : FiniteNative.GeneratedGroupoid M bases U P internalEdges hlinear δ enumK enumEdges enumFaces)
    {i j : (ClosedRegion.presentation U).Vertex} (e : (ClosedRegion.presentation U).Edge i j) :
    ((equivalence T bases U P internalEdges hlinear hfixed enumK enumEdges enumFaces).inverse.obj y).back.1.choice e =
      (ClosedRegion.restrictTower U T).correctionChoice
        ((ActualEquation.nativeEdgeEquiv T P U)
          (((FiniteNative.generatedSolutionEquiv M bases U P internalEdges hlinear δ enumK enumEdges enumFaces).symm y.back).1)).1 e := rfl

omit [DecidablePred (· ∈ P.vertices)] in
/-- Public interface coordinates retain the complete original correction at each named public edge. -/
theorem public_value
    (R : RepairGroupoid (ClosedRegion.restrictTower U T)
      (ClosedRegion.nativeIntersection U P).vertices (ClosedRegion.nativeIntersection U P).edges)
    (e : U.edges) (hp : e.1 ∉ P.edges) (hi : e.1 ∉ internalEdges)
    (j : Fin (bases.dimension e.1.2.1)) :
    ((equivalence T bases U P internalEdges hlinear hfixed enumK enumEdges enumFaces).functor.obj R).back.1.1
      ⟨⟨⟨e.1,e.2,hp⟩,j⟩,hi⟩ =
        bases.coordinate e.1.2.1 ((ActualEquation.nativeRepairEquiv T P hfixed U R.back).1.1 e) j := rfl

end NativeRepairInterface
end AAT.AG.RelativeRepairComposition

#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
