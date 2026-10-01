import Formal.Util.AssertStandardAxioms
import ResearchLean.AG.RelativeRepairComposition.FiniteCoverDisplay
import ResearchLean.AG.RelativeRepairComposition.StrictFunctorComparison

/-!
# Full generated display changes of the same original actual repairs

## Implementation notes

A display is original finite input data. Comparison first uses computed strict
gluing to restore the independent original repair, then restricts and reads
new local generated coordinates. The whole native functors satisfy inverse,
composition and reconstruction identities, including every original gauge.
-/
namespace AAT.AG.RelativeRepairComposition
open CategoryTheory TransportCoherence AbelianLiftingObstruction TransportCoherence.Arbitrary
universe uk uG uE uB uD vE vB vD uI uJ uL
variable {k : Type uk} [Field k] [Fintype k] [DecidableEq k]
variable {K : FiniteTransportPresentation.{uG}}
variable {E : Type uE} {B : Type uB} {D : Type uD}
variable [Category.{vE} E] [Category.{vB} B] [Category.{vD} D]
variable {p : E ⥤ B} {q : B ⥤ D}
namespace GeneratedDisplay
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
variable (T : OriginalTowerPresentation K p q)
local notation "M" => T.toTower.localCoefficients
variable [∀ v, Module k ((T.toTower.localCoefficients).A v)]
variable (P : ClosedRegion K)
variable [DecidablePred (· ∈ P.edges)] [DecidablePred (· ∈ P.faces)]
variable (candidates : Set (EdgeName (K := K))) [DecidablePred (· ∈ candidates)]
variable (hlinear : ∀ {i j : K.Vertex} (e : K.Edge i j) (t : k) (x : (T.toTower.localCoefficients).A i),
  (T.toTower.localCoefficients).edge e (t • x) = t • (T.toTower.localCoefficients).edge e x)
variable (hfixed : ∀ f ∈ P.faces,
  T.toTower.upper.pathLift (K.twoLeft f) ≫ FiberAut.hom (T.comparator f) =
    T.toTower.upper.pathLift (K.twoRight f))
local notation "δ" => ActualEquation.defectFamily T P hfixed
variable [Fintype (EdgeName (K := K))] [DecidableEq (EdgeName (K := K))]
variable [Fintype K.TwoCell] [DecidableEq K.TwoCell]
variable (d : FiniteCoverDisplay.{uk,uG,vE,uI} (k := k) T.toTower.localCoefficients)
variable (e : FiniteCoverDisplay.{uk,uG,vE,uJ} (k := k) T.toTower.localCoefficients)
variable (f : FiniteCoverDisplay.{uk,uG,vE,uL} (k := k) T.toTower.localCoefficients)
variable (allowed : Set (EdgeName (K := K)))

/-- Generate full object coordinates from the original actual repair, using this finite input display. -/
noncomputable def objectEquiv : SupportedRepair T (fixedEdgesForRange P.edges candidates allowed) ≃
    FiniteCoverDisplay.Objects (k := k) M d P candidates hlinear δ allowed :=
  GeneratedCoverRestoration.objectEquiv (k := k) (I := d.Index) T d.bases P d.region candidates hlinear hfixed
    d.enumField d.enumEdges d.enumFaces d.enumIndex d.cover allowed

/-- Generate the full original-label map by finite strict vertex gluing. -/
noncomputable def labelEquiv : supportedC0 T P.vertices (fixedEdgesForRange P.edges candidates allowed) ≃+
    FiniteCoverDisplay.Labels (k := k) M d P candidates allowed :=
  GeneratedCoverRestoration.labelEquiv (I := d.Index) T P d.region candidates d.enumIndex d.cover allowed

/-- Full native coordinates use the accepted original repair construction with these input fields. -/
noncomputable def equivalence : RepairGroupoid T P.vertices (fixedEdgesForRange P.edges candidates allowed) ≌
    FiniteCoverDisplay.Groupoid (k := k) M d P candidates hlinear δ allowed :=
  GeneratedCoverRestoration.equivalence (k := k) (I := d.Index) T d.bases P d.region candidates hlinear hfixed
    d.enumField d.enumEdges d.enumFaces d.enumIndex d.cover allowed

/-- A display restores exactly the same independent original repair and all arrows. -/
theorem functor_inverse :
    (equivalence (k := k) T P candidates hlinear hfixed d allowed).functor ⋙
      (equivalence (k := k) T P candidates hlinear hfixed d allowed).inverse =
        𝟭 (RepairGroupoid T P.vertices (fixedEdgesForRange P.edges candidates allowed)) :=
  GeneratedCoverRestoration.functor_inverse (k := k) (I := d.Index) T d.bases P d.region candidates hlinear hfixed
    d.enumField d.enumEdges d.enumFaces d.enumIndex d.cover allowed

/-- A display retains every generated local public value, kernel vector and full arrow. -/
theorem inverse_functor :
    (equivalence (k := k) T P candidates hlinear hfixed d allowed).inverse ⋙
      (equivalence (k := k) T P candidates hlinear hfixed d allowed).functor =
        𝟭 (FiniteCoverDisplay.Groupoid (k := k) M d P candidates hlinear δ allowed) :=
  GeneratedCoverRestoration.inverse_functor (k := k) (I := d.Index) T d.bases P d.region candidates hlinear hfixed
    d.enumField d.enumEdges d.enumFaces d.enumIndex d.cover allowed

/-- The full object comparison is new coordinates after finite original restoration. -/
noncomputable def objectComparison : FiniteCoverDisplay.Objects (k := k) M d P candidates hlinear δ allowed ≃
    FiniteCoverDisplay.Objects (k := k) M e P candidates hlinear δ allowed :=
  (objectEquiv (k := k) T P candidates hlinear hfixed d allowed).symm.trans
    (objectEquiv (k := k) T P candidates hlinear hfixed e allowed)

/-- Full labels change through their same original vertex values. -/
noncomputable def labelComparison : FiniteCoverDisplay.Labels (k := k) M d P candidates allowed ≃+
    FiniteCoverDisplay.Labels (k := k) M e P candidates allowed :=
  (labelEquiv (k := k) T P candidates d allowed).symm.trans (labelEquiv (k := k) T P candidates e allowed)

/-- Native display comparison uses finite restoration and new local coordinates on every arrow. -/
noncomputable def comparison : FiniteCoverDisplay.Groupoid (k := k) M d P candidates hlinear δ allowed ≌
    FiniteCoverDisplay.Groupoid (k := k) M e P candidates hlinear δ allowed :=
  strictComparison (equivalence (k := k) T P candidates hlinear hfixed d allowed)
    (equivalence (k := k) T P candidates hlinear hfixed e allowed)

/-- The object part of the whole native comparison is the same full coordinate comparison. -/
theorem comparison_obj
    (y : FiniteCoverDisplay.Groupoid (k := k) M d P candidates hlinear δ allowed) :
    ((comparison (k := k) T P candidates hlinear hfixed d e allowed).functor.obj y).back =
      objectComparison (k := k) T P candidates hlinear hfixed d e allowed y.back := rfl

/-- Reconstruction commutes as whole functors, retaining all actual choices and gauges. -/
theorem comparison_rec :
    (comparison (k := k) T P candidates hlinear hfixed d e allowed).functor ⋙
      (equivalence (k := k) T P candidates hlinear hfixed e allowed).inverse =
        (equivalence (k := k) T P candidates hlinear hfixed d allowed).inverse :=
  strict_comparison_rec _ _ (functor_inverse (k := k) T P candidates hlinear hfixed e allowed)

/-- Coordinate construction commutes as whole native functors. -/
theorem comparison_coord :
    (equivalence (k := k) T P candidates hlinear hfixed d allowed).functor ⋙
      (comparison (k := k) T P candidates hlinear hfixed d e allowed).functor =
        (equivalence (k := k) T P candidates hlinear hfixed e allowed).functor :=
  strict_comparison_coord _ _ (functor_inverse (k := k) T P candidates hlinear hfixed d allowed)

/-- Three displays compose exactly, on every object and every transported arrow. -/
theorem comparison_comp :
    (comparison (k := k) T P candidates hlinear hfixed d e allowed).functor ⋙
      (comparison (k := k) T P candidates hlinear hfixed e f allowed).functor =
        (comparison (k := k) T P candidates hlinear hfixed d f allowed).functor :=
  strict_comparison_comp _ _ _ (functor_inverse (k := k) T P candidates hlinear hfixed e allowed)

/-- Display comparison and its inverse are strict on the old full groupoid. -/
theorem comparison_inverse :
    (comparison (k := k) T P candidates hlinear hfixed d e allowed).functor ⋙
      (comparison (k := k) T P candidates hlinear hfixed d e allowed).inverse =
        𝟭 (FiniteCoverDisplay.Groupoid (k := k) M d P candidates hlinear δ allowed) :=
  strict_comparison_inverse _ _ (functor_inverse (k := k) T P candidates hlinear hfixed e allowed)
    (inverse_functor (k := k) T P candidates hlinear hfixed d allowed)

/-- The inverse comparison is strict on the new full groupoid. -/
theorem inverse_comparison :
    (comparison (k := k) T P candidates hlinear hfixed d e allowed).inverse ⋙
      (comparison (k := k) T P candidates hlinear hfixed d e allowed).functor =
        𝟭 (FiniteCoverDisplay.Groupoid (k := k) M e P candidates hlinear δ allowed) :=
  strict_inverse_comparison _ _ (functor_inverse (k := k) T P candidates hlinear hfixed d allowed)
    (inverse_functor (k := k) T P candidates hlinear hfixed e allowed)

/-- Every original named edge in the new region keeps its complete physical correction. -/
theorem comparison_edge_value
    (y : FiniteCoverDisplay.Objects (k := k) M d P candidates hlinear δ allowed)
    (j : e.Index) (a : (e.region j).edges) :
    ((GeneratedStrictCover.restore (k := k) M e.bases P e.region candidates hlinear δ
      e.enumField e.enumEdges e.enumFaces allowed
      (objectComparison (k := k) T P candidates hlinear hfixed d e allowed y)).1 j).1.1.1 a =
    T.solutionCorrection ((objectEquiv (k := k) T P candidates hlinear hfixed d allowed).symm y).1 a.1 :=
  GeneratedCoverRestoration.forward_edge_value (k := k) (I := e.Index) T e.bases P e.region candidates hlinear hfixed
    e.enumField e.enumEdges e.enumFaces e.enumIndex e.cover allowed
    ((objectEquiv (k := k) T P candidates hlinear hfixed d allowed).symm y) j a

/-- Arbitrary new reconstruction restores the same original actual repair in full. -/
theorem object_comparison_rec
    (y : FiniteCoverDisplay.Objects (k := k) M d P candidates hlinear δ allowed) :
    (objectEquiv (k := k) T P candidates hlinear hfixed e allowed).symm
      (objectComparison (k := k) T P candidates hlinear hfixed d e allowed y) =
        (objectEquiv (k := k) T P candidates hlinear hfixed d allowed).symm y :=
  (objectEquiv (k := k) T P candidates hlinear hfixed e allowed).symm_apply_apply _

/-- Every original actual choice, rather than only its correction image, is preserved. -/
theorem comparison_choice
    (y : FiniteCoverDisplay.Objects (k := k) M d P candidates hlinear δ allowed)
    {i j : K.Vertex} (a : K.Edge i j) :
    ((objectEquiv (k := k) T P candidates hlinear hfixed e allowed).symm
      (objectComparison (k := k) T P candidates hlinear hfixed d e allowed y)).1.choice a =
        ((objectEquiv (k := k) T P candidates hlinear hfixed d allowed).symm y).1.choice a := by
  rw [object_comparison_rec]

omit [Fintype k] [DecidableEq k] [DecidablePred (· ∈ P.edges)] [DecidablePred (· ∈ P.faces)]
  [DecidablePred (· ∈ candidates)] [Fintype (EdgeName (K := K))] [DecidableEq (EdgeName (K := K))]
  [Fintype K.TwoCell] [DecidableEq K.TwoCell] in
/-- The compared full label evaluates to its same original global vertex value. -/
theorem comparison_label_value
    (b : FiniteCoverDisplay.Labels (k := k) M d P candidates allowed)
    (j : e.Index) (v : (e.region j).vertices) :
    ((labelComparison (k := k) T P candidates d e allowed b).1 j).1.1 v =
      ((labelEquiv (k := k) T P candidates d allowed).symm b).1 v.1 :=
  GeneratedCoverRestoration.label_value (I := e.Index) T P e.region candidates e.enumIndex e.cover allowed
    ((labelEquiv (k := k) T P candidates d allowed).symm b) j v

/-- Whole comparison arrows use exactly that same full original vertex-label map. -/
theorem comparison_map_label
    {x y : FiniteCoverDisplay.Groupoid (k := k) M d P candidates hlinear δ allowed} (b : x ⟶ y) :
    ((comparison (k := k) T P candidates hlinear hfixed d e allowed).functor.map b).1.toAdd =
      labelComparison (k := k) T P candidates d e allowed b.1.toAdd := rfl

/-- Refined local corrections are the literal restrictions of the old restored original region. -/
theorem refinement_edge_value (α : e.Index → d.Index)
    (inc : ∀ j, ClosedRegion.Inclusion (e.region j) (d.region (α j)))
    (y : FiniteCoverDisplay.Objects (k := k) M d P candidates hlinear δ allowed)
    (j : e.Index) (a : (e.region j).edges) :
    ((GeneratedStrictCover.restore (k := k) M e.bases P e.region candidates hlinear δ
      e.enumField e.enumEdges e.enumFaces allowed
      (objectComparison (k := k) T P candidates hlinear hfixed d e allowed y)).1 j).1.1.1 a =
    ((GeneratedStrictCover.restore (k := k) M d.bases P d.region candidates hlinear δ
      d.enumField d.enumEdges d.enumFaces allowed y).1 (α j)).1.1.1 ⟨a.1,(inc j).edges a.2⟩ := by
  rw [comparison_edge_value]
  exact GeneratedCoverRestoration.inverse_edge_value (k := k) (I := d.Index)
    T d.bases P d.region candidates hlinear hfixed d.enumField d.enumEdges d.enumFaces
    d.enumIndex d.cover allowed y (α j) ⟨a.1,(inc j).edges a.2⟩

omit [Fintype k] [DecidableEq k] [DecidablePred (· ∈ P.edges)] [DecidablePred (· ∈ P.faces)]
  [DecidablePred (· ∈ candidates)] [Fintype (EdgeName (K := K))] [DecidableEq (EdgeName (K := K))]
  [Fintype K.TwoCell] [DecidableEq K.TwoCell] in
/-- Refined arrows restrict every full original vertex label, including ineffective gauges. -/
theorem refinement_label_value (α : e.Index → d.Index)
    (inc : ∀ j, ClosedRegion.Inclusion (e.region j) (d.region (α j)))
    (b : FiniteCoverDisplay.Labels (k := k) M d P candidates allowed)
    (j : e.Index) (v : (e.region j).vertices) :
    ((labelComparison (k := k) T P candidates d e allowed b).1 j).1.1 v =
      (b.1 (α j)).1.1 ⟨v.1,(inc j).vertices v.2⟩ := by
  rw [comparison_label_value]
  exact GeneratedCoverRestoration.label_inverse_value (I := d.Index) T P d.region candidates
    d.enumIndex d.cover allowed b (α j) ⟨v.1,(inc j).vertices v.2⟩

variable {S V : Set (EdgeName (K := K))}
/-- The finite display range functor uses the same generated local data after relaxation. -/
noncomputable def rangeFunctor (h : S ⊆ V) :
    FiniteCoverDisplay.Groupoid (k := k) M d P candidates hlinear δ S ⥤
      FiniteCoverDisplay.Groupoid (k := k) M d P candidates hlinear δ V :=
  GeneratedRangeInclusion.functor (k := k) (I := d.Index) M d.bases P d.region candidates hlinear δ
    d.enumField d.enumEdges d.enumFaces h

/-- Every full display comparison commutes with all allowed-range inclusion functors. -/
theorem comparison_range (h : S ⊆ V) :
    rangeFunctor (k := k) T P candidates hlinear hfixed d h ⋙
      (comparison (k := k) T P candidates hlinear hfixed d e V).functor =
    (comparison (k := k) T P candidates hlinear hfixed d e S).functor ⋙
      rangeFunctor (k := k) T P candidates hlinear hfixed e h := by
  have hd : rangeFunctor (k := k) T P candidates hlinear hfixed d h ⋙
      (equivalence (k := k) T P candidates hlinear hfixed d V).inverse =
      (equivalence (k := k) T P candidates hlinear hfixed d S).inverse ⋙
        ActualRelative.rangeFunctor T P candidates h :=
    GeneratedCoverRanges.reconstruction_functor_inclusion (k := k) (I := d.Index)
      T d.bases P d.region candidates hlinear hfixed d.enumField d.enumEdges d.enumFaces
      d.enumIndex d.cover h
  have he : ActualRelative.rangeFunctor T P candidates h ⋙
      (equivalence (k := k) T P candidates hlinear hfixed e V).functor =
      (equivalence (k := k) T P candidates hlinear hfixed e S).functor ⋙
        rangeFunctor (k := k) T P candidates hlinear hfixed e h :=
    GeneratedCoverRanges.coordinate_functor_inclusion (k := k) (I := e.Index)
      T e.bases P e.region candidates hlinear hfixed e.enumField e.enumEdges e.enumFaces
      e.enumIndex e.cover h
  change (rangeFunctor (k := k) T P candidates hlinear hfixed d h ⋙
    (equivalence (k := k) T P candidates hlinear hfixed d V).inverse) ⋙
    (equivalence (k := k) T P candidates hlinear hfixed e V).functor = _
  rw [hd]
  change (equivalence (k := k) T P candidates hlinear hfixed d S).inverse ⋙
    (ActualRelative.rangeFunctor T P candidates h ⋙
      (equivalence (k := k) T P candidates hlinear hfixed e V).functor) = _
  rw [he]
  rfl

end GeneratedDisplay
end AAT.AG.RelativeRepairComposition
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
