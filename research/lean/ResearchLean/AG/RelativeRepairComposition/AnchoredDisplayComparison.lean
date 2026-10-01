import Formal.Util.AssertStandardAxioms
import ResearchLean.AG.RelativeRepairComposition.AnchoredFiniteCover
import ResearchLean.AG.RelativeRepairComposition.GeneratedDisplayComparison

/-!
# Simultaneous actual reference, full basis and finite cover comparisons

## Implementation notes

The common source is the independent original actual repair groupoid. Each raw
display uses the actual alternative lift and its -a physical anchors, then the
same original one-time generation. Comparisons reconstruct the original repair
and read the new display. Whole native inverses and comparison compositions
retain all physical choices and original gauge labels for every allowed range.
-/
namespace AAT.AG.RelativeRepairComposition
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
universe uk uG uE uB uD vE vB vD uI uJ uL
variable {k : Type uk} [Field k] [Fintype k] [DecidableEq k]
variable {K : FiniteTransportPresentation.{uG}}
variable {E : Type uE} {B : Type uB} {D : Type uD}
variable [Category.{vE} E] [Category.{vB} B] [Category.{vD} D]
variable {p : E ⥤ B} {q : B ⥤ D}
namespace AnchoredDisplay
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
variable (T : OriginalTowerPresentation K p q)
variable [∀ v, Module k ((T.toTower.localCoefficients).A v)]
variable (P : ClosedRegion K)
variable [DecidablePred (· ∈ P.edges)] [DecidablePred (· ∈ P.faces)]
variable (candidates : Set (EdgeName (K := K))) [DecidablePred (· ∈ candidates)]
variable (hlinear : ∀ {i j : K.Vertex} (e : K.Edge i j) (t : k) (x : (T.toTower.localCoefficients).A i),
  (T.toTower.localCoefficients).edge e (t • x) = t • (T.toTower.localCoefficients).edge e x)
variable (hfixed : ∀ f ∈ P.faces,
  T.toTower.upper.pathLift (K.twoLeft f) ≫ FiberAut.hom (T.comparator f) =
    T.toTower.upper.pathLift (K.twoRight f))
variable [Fintype (EdgeName (K := K))] [DecidableEq (EdgeName (K := K))]
variable [Fintype K.TwoCell] [DecidableEq K.TwoCell]
variable (d : FiniteCoverDisplay.{uk,uG,vE,uI} (k := k) T.toTower.localCoefficients)
variable (e : FiniteCoverDisplay.{uk,uG,vE,uJ} (k := k) T.toTower.localCoefficients)
variable (f : FiniteCoverDisplay.{uk,uG,vE,uL} (k := k) T.toTower.localCoefficients)
variable (other other' other'' : ∀ {i j : K.Vertex} (_ : K.Edge i j), FiberAut (p ⋙ q) (T.original.object j))
variable (hother : ∀ {i j : K.Vertex} (a : K.Edge i j),
  fiberPushforward p q (T.original.object j) (other a) = T.core a)
variable (hother' : ∀ {i j : K.Vertex} (a : K.Edge i j),
  fiberPushforward p q (T.original.object j) (other' a) = T.core a)
variable (hother'' : ∀ {i j : K.Vertex} (a : K.Edge i j),
  fiberPushforward p q (T.original.object j) (other'' a) = T.core a)
variable (allowed : Set (EdgeName (K := K)))
local notation "M" => T.toTower.localCoefficients
local notation "δ" => ActualEquation.defectFamily T P hfixed

/-- Each raw reference display is constructed from its actual lift, full bases and complete finite input. -/
noncomputable def generatedEquivalence :
    AnchoredFinite.Groupoid T other hother P d.region candidates allowed ≌
      FiniteCoverDisplay.Groupoid (k := k) M d P candidates hlinear δ allowed :=
  AnchoredFinite.generatedEquivalence (k := k) (I := d.Index) T other hother P d.region hfixed
    candidates allowed d.bases hlinear d.enumField d.enumEdges d.enumFaces

/-- The original actual source constructs independent raw displayed equations with the physical anchor -a. -/
noncomputable def sourceEquivalence : RepairGroupoid T P.vertices (fixedEdgesForRange P.edges candidates allowed) ≌
    AnchoredFinite.Groupoid T other hother P d.region candidates allowed :=
  (GeneratedDisplay.equivalence (k := k) T P candidates hlinear hfixed d allowed).trans
    (generatedEquivalence (k := k) T P candidates hlinear hfixed d other hother allowed).symm

/-- Both full source functors preserve every original physical choice and every full gauge arrow. -/
theorem source_functor_inverse :
    (sourceEquivalence (k := k) T P candidates hlinear hfixed d other hother allowed).functor ⋙
      (sourceEquivalence (k := k) T P candidates hlinear hfixed d other hother allowed).inverse =
        𝟭 (RepairGroupoid T P.vertices (fixedEdgesForRange P.edges candidates allowed)) :=
  strict_trans_functor_inverse _ _ (GeneratedDisplay.functor_inverse (k := k) T P candidates hlinear hfixed d allowed)
    (AnchoredFinite.generated_inverse_functor (k := k) (I := d.Index) T other hother P d.region hfixed
      candidates allowed d.bases hlinear d.enumField d.enumEdges d.enumFaces)

/-- Both full inverse source functors retain every independent raw local value and full label. -/
theorem source_inverse_functor :
    (sourceEquivalence (k := k) T P candidates hlinear hfixed d other hother allowed).inverse ⋙
      (sourceEquivalence (k := k) T P candidates hlinear hfixed d other hother allowed).functor =
        𝟭 (AnchoredFinite.Groupoid T other hother P d.region candidates allowed) :=
  strict_trans_inverse_functor _ _ (GeneratedDisplay.inverse_functor (k := k) T P candidates hlinear hfixed d allowed)
    (AnchoredFinite.generated_functor_inverse (k := k) (I := d.Index) T other hother P d.region hfixed
      candidates allowed d.bases hlinear d.enumField d.enumEdges d.enumFaces)

/-- Raw coordinates of every actual repair are h-a on each same original edge, including P. -/
theorem source_value (R : RepairGroupoid T P.vertices (fixedEdgesForRange P.edges candidates allowed))
    (i : d.Index) (a : (d.region i).edges) :
    (((sourceEquivalence (k := k) T P candidates hlinear hfixed d other hother allowed).functor.obj R).back.1 i).1 a =
      T.solutionCorrection R.back.1 a.1 - T.alternativeCorrection other hother a.1 := by
  change ((GeneratedStrictCover.restore (k := k) M d.bases P d.region candidates hlinear δ
    d.enumField d.enumEdges d.enumFaces allowed
    (GeneratedDisplay.objectEquiv (k := k) T P candidates hlinear hfixed d allowed R.back)).1 i).1.1.1 a -
      T.alternativeCorrection other hother a.1 = _
  exact congrArg (fun x => x - T.alternativeCorrection other hother a.1)
    (GeneratedCoverRestoration.forward_edge_value (k := k) (I := d.Index) T d.bases P d.region candidates hlinear hfixed
      d.enumField d.enumEdges d.enumFaces d.enumIndex d.cover allowed R.back i a)

/-- Restoring an arbitrary independent raw display adds its actual a on each original edge. -/
theorem source_inverse_value (y : AnchoredFinite.Groupoid T other hother P d.region candidates allowed)
    (i : d.Index) (a : (d.region i).edges) :
    T.solutionCorrection
      (((sourceEquivalence (k := k) T P candidates hlinear hfixed d other hother allowed).inverse.obj y).back.1) a.1 =
      (y.back.1 i).1 a + T.alternativeCorrection other hother a.1 := by
  have hv := GeneratedCoverRestoration.inverse_edge_value (k := k) (I := d.Index)
    T d.bases P d.region candidates hlinear hfixed d.enumField d.enumEdges d.enumFaces
    d.enumIndex d.cover allowed
    (((generatedEquivalence (k := k) T P candidates hlinear hfixed d other hother allowed).functor.obj y).back) i a
  change T.solutionCorrection _ a.1 =
    ((GeneratedStrictCover.restore (k := k) M d.bases P d.region candidates hlinear δ
      d.enumField d.enumEdges d.enumFaces allowed
      (GeneratedStrictCover.coordinate (k := k) M d.bases P d.region candidates hlinear δ
        d.enumField d.enumEdges d.enumFaces allowed
        (AnchoredFinite.normalize T other hother P d.region hfixed candidates allowed y.back))).1 i).1.1.1 a at hv
  rw [GeneratedStrictCover.restore_coordinate] at hv
  exact hv

/-- Simultaneous changes of actual lift, complete bases and finite original cover compare all objects and arrows. -/
noncomputable def comparison : AnchoredFinite.Groupoid T other hother P d.region candidates allowed ≌
    AnchoredFinite.Groupoid T other' hother' P e.region candidates allowed :=
  strictComparison (sourceEquivalence (k := k) T P candidates hlinear hfixed d other hother allowed)
    (sourceEquivalence (k := k) T P candidates hlinear hfixed e other' hother' allowed)

/-- Every simultaneous raw comparison reconstructs the identical original actual object and all arrows. -/
theorem comparison_rec :
    (comparison (k := k) T P candidates hlinear hfixed d e other other' hother hother' allowed).functor ⋙
      (sourceEquivalence (k := k) T P candidates hlinear hfixed e other' hother' allowed).inverse =
        (sourceEquivalence (k := k) T P candidates hlinear hfixed d other hother allowed).inverse :=
  strict_comparison_rec _ _ (source_functor_inverse (k := k) T P candidates hlinear hfixed e other' hother' allowed)

/-- All three simultaneous changes compose on whole native functors, including every transported arrow. -/
theorem comparison_comp :
    (comparison (k := k) T P candidates hlinear hfixed d e other other' hother hother' allowed).functor ⋙
      (comparison (k := k) T P candidates hlinear hfixed e f other' other'' hother' hother'' allowed).functor =
        (comparison (k := k) T P candidates hlinear hfixed d f other other'' hother hother'' allowed).functor :=
  strict_comparison_comp _ _ _ (source_functor_inverse (k := k) T P candidates hlinear hfixed e other' hother' allowed)

/-- Reversing a simultaneous raw display change restores every raw object and full arrow. -/
theorem comparison_inverse :
    (comparison (k := k) T P candidates hlinear hfixed d e other other' hother hother' allowed).functor ⋙
      (comparison (k := k) T P candidates hlinear hfixed d e other other' hother hother' allowed).inverse =
        𝟭 (AnchoredFinite.Groupoid T other hother P d.region candidates allowed) :=
  strict_comparison_inverse _ _ (source_functor_inverse (k := k) T P candidates hlinear hfixed e other' hother' allowed)
    (source_inverse_functor (k := k) T P candidates hlinear hfixed d other hother allowed)

/-- New raw coordinates retain the actual old reconstruction and subtract the actual new lift difference. -/
theorem comparison_value (y : AnchoredFinite.Groupoid T other hother P d.region candidates allowed)
    (j : e.Index) (a : (e.region j).edges) :
    (((comparison (k := k) T P candidates hlinear hfixed d e other other' hother hother' allowed).functor.obj y).back.1 j).1 a =
      T.solutionCorrection
        (((sourceEquivalence (k := k) T P candidates hlinear hfixed d other hother allowed).inverse.obj y).back.1) a.1 -
        T.alternativeCorrection other' hother' a.1 :=
  source_value (k := k) T P candidates hlinear hfixed e other' hother' allowed _ j a

/-- Under refinement the concrete raw comparison is h'+a-a' on every included original edge. -/
theorem refinement_value (α : e.Index → d.Index)
    (inc : ∀ j, ClosedRegion.Inclusion (e.region j) (d.region (α j)))
    (y : AnchoredFinite.Groupoid T other hother P d.region candidates allowed)
    (j : e.Index) (a : (e.region j).edges) :
    (((comparison (k := k) T P candidates hlinear hfixed d e other other' hother hother' allowed).functor.obj y).back.1 j).1 a =
      (y.back.1 (α j)).1 ⟨a.1,(inc j).edges a.2⟩ + T.alternativeCorrection other hother a.1 -
        T.alternativeCorrection other' hother' a.1 := by
  rw [comparison_value]
  rw [source_inverse_value (k := k) T P candidates hlinear hfixed d other hother allowed y (α j)
    ⟨a.1,(inc j).edges a.2⟩]

/-- Reversing a simultaneous change retains all new raw values and every new full arrow. -/
theorem inverse_comparison :
    (comparison (k := k) T P candidates hlinear hfixed d e other other' hother hother' allowed).inverse ⋙
      (comparison (k := k) T P candidates hlinear hfixed d e other other' hother hother' allowed).functor =
        𝟭 (AnchoredFinite.Groupoid T other' hother' P e.region candidates allowed) :=
  strict_inverse_comparison _ _ (source_functor_inverse (k := k) T P candidates hlinear hfixed d other hother allowed)
    (source_inverse_functor (k := k) T P candidates hlinear hfixed e other' hother' allowed)

/-- Every simultaneous comparison preserves every original actual edge choice after reconstruction. -/
theorem comparison_choice (y : AnchoredFinite.Groupoid T other hother P d.region candidates allowed)
    {i j : K.Vertex} (a : K.Edge i j) :
    (((sourceEquivalence (k := k) T P candidates hlinear hfixed e other' hother' allowed).inverse.obj
      ((comparison (k := k) T P candidates hlinear hfixed d e other other' hother hother' allowed).functor.obj y)).back.1).choice a =
        (((sourceEquivalence (k := k) T P candidates hlinear hfixed d other hother allowed).inverse.obj y).back.1).choice a := by
  have hc := congrArg (fun F => F.obj y)
    (comparison_rec (k := k) T P candidates hlinear hfixed d e other other' hother hother' allowed)
  exact congrArg (fun r => r.back.1.choice a) hc

/-- Forward source arrows retain every full original vertex label in each raw region. -/
theorem source_label_value
    {R Q : RepairGroupoid T P.vertices (fixedEdgesForRange P.edges candidates allowed)} (b : R ⟶ Q)
    (i : d.Index) (v : (d.region i).vertices) :
    ((((sourceEquivalence (k := k) T P candidates hlinear hfixed d other hother allowed).functor.map b).1.toAdd).1 i).1.1 v =
      b.1.toAdd.1 v.1 :=
  GeneratedCoverRestoration.functor_label_value (k := k) (I := d.Index) T d.bases P d.region candidates hlinear hfixed
    d.enumField d.enumEdges d.enumFaces d.enumIndex d.cover allowed b i v

/-- Inverse source arrows restore every raw compatible original vertex value, including all stabilizers. -/
theorem source_inverse_label_value
    {R Q : AnchoredFinite.Groupoid T other hother P d.region candidates allowed} (b : R ⟶ Q)
    (i : d.Index) (v : (d.region i).vertices) :
    ((sourceEquivalence (k := k) T P candidates hlinear hfixed d other hother allowed).inverse.map b).1.toAdd.1 v.1 =
      (b.1.toAdd.1 i).1.1 v :=
  GeneratedCoverRestoration.inverse_label_value (k := k) (I := d.Index) T d.bases P d.region candidates hlinear hfixed
    d.enumField d.enumEdges d.enumFaces d.enumIndex d.cover allowed
    ((generatedEquivalence (k := k) T P candidates hlinear hfixed d other hother allowed).functor.map b) i v

/-- Simultaneous comparison arrows retain the same full original reconstructed vertex label. -/
theorem comparison_label_value
    {R Q : AnchoredFinite.Groupoid T other hother P d.region candidates allowed} (b : R ⟶ Q)
    (j : e.Index) (v : (e.region j).vertices) :
    ((((comparison (k := k) T P candidates hlinear hfixed d e other other' hother hother' allowed).functor.map b).1.toAdd).1 j).1.1 v =
      ((sourceEquivalence (k := k) T P candidates hlinear hfixed d other hother allowed).inverse.map b).1.toAdd.1 v.1 :=
  source_label_value (k := k) T P candidates hlinear hfixed e other' hother' allowed _ j v

/-- Refinement restricts full original vertex labels literally, even when their gauge effects vanish. -/
theorem refinement_label_value (α : e.Index → d.Index)
    (inc : ∀ j, ClosedRegion.Inclusion (e.region j) (d.region (α j)))
    {R Q : AnchoredFinite.Groupoid T other hother P d.region candidates allowed} (b : R ⟶ Q)
    (j : e.Index) (v : (e.region j).vertices) :
    ((((comparison (k := k) T P candidates hlinear hfixed d e other other' hother hother' allowed).functor.map b).1.toAdd).1 j).1.1 v =
      (b.1.toAdd.1 (α j)).1.1 ⟨v.1,(inc j).vertices v.2⟩ := by
  rw [comparison_label_value]
  exact source_inverse_label_value (k := k) T P candidates hlinear hfixed d other hother allowed b
    (α j) ⟨v.1,(inc j).vertices v.2⟩

variable {S V : Set (EdgeName (K := K))}
/-- Original source coordinates commute with every range relaxation on the complete raw native functor. -/
theorem source_range (h : S ⊆ V) :
    ActualRelative.rangeFunctor T P candidates h ⋙
      (sourceEquivalence (k := k) T P candidates hlinear hfixed d other hother V).functor =
    (sourceEquivalence (k := k) T P candidates hlinear hfixed d other hother S).functor ⋙
      AnchoredFinite.rangeFunctor (I := d.Index) T other hother P d.region candidates h := by
  change (ActualRelative.rangeFunctor T P candidates h ⋙
    (GeneratedDisplay.equivalence (k := k) T P candidates hlinear hfixed d V).functor) ⋙
      (generatedEquivalence (k := k) T P candidates hlinear hfixed d other hother V).inverse = _
  have hg := GeneratedCoverRanges.coordinate_functor_inclusion (k := k) (I := d.Index)
    T d.bases P d.region candidates hlinear hfixed d.enumField d.enumEdges d.enumFaces d.enumIndex d.cover h
  change ActualRelative.rangeFunctor T P candidates h ⋙
    (GeneratedDisplay.equivalence (k := k) T P candidates hlinear hfixed d V).functor =
      (GeneratedDisplay.equivalence (k := k) T P candidates hlinear hfixed d S).functor ⋙
        GeneratedRangeInclusion.functor M d.bases P d.region candidates hlinear δ d.enumField d.enumEdges d.enumFaces h at hg
  rw [hg]
  change (GeneratedDisplay.equivalence (k := k) T P candidates hlinear hfixed d S).functor ⋙
    (GeneratedRangeInclusion.functor M d.bases P d.region candidates hlinear δ d.enumField d.enumEdges d.enumFaces h ⋙
      (generatedEquivalence (k := k) T P candidates hlinear hfixed d other hother V).inverse) = _
  have hr := AnchoredFinite.generated_inverse_range (k := k) (I := d.Index)
    T other hother P d.region hfixed candidates d.bases hlinear d.enumField d.enumEdges d.enumFaces h
  change GeneratedRangeInclusion.functor M d.bases P d.region candidates hlinear δ d.enumField d.enumEdges d.enumFaces h ⋙
    (generatedEquivalence (k := k) T P candidates hlinear hfixed d other hother V).inverse =
      (generatedEquivalence (k := k) T P candidates hlinear hfixed d other hother S).inverse ⋙
        AnchoredFinite.rangeFunctor (I := d.Index) T other hother P d.region candidates h at hr
  rw [hr]
  rfl

/-- Full raw reconstruction commutes with every original actual range inclusion. -/
theorem source_inverse_range (h : S ⊆ V) :
    AnchoredFinite.rangeFunctor (I := d.Index) T other hother P d.region candidates h ⋙
      (sourceEquivalence (k := k) T P candidates hlinear hfixed d other hother V).inverse =
    (sourceEquivalence (k := k) T P candidates hlinear hfixed d other hother S).inverse ⋙
      ActualRelative.rangeFunctor T P candidates h := by
  let s := sourceEquivalence (k := k) T P candidates hlinear hfixed d other hother S
  let v := sourceEquivalence (k := k) T P candidates hlinear hfixed d other hother V
  let R := AnchoredFinite.rangeFunctor (I := d.Index) T other hother P d.region candidates h
  let A := ActualRelative.rangeFunctor T P candidates h
  have he : A ⋙ v.functor = s.functor ⋙ R :=
    source_range (k := k) T P candidates hlinear hfixed d other hother h
  have hs : s.inverse ⋙ s.functor = 𝟭 _ :=
    source_inverse_functor (k := k) T P candidates hlinear hfixed d other hother S
  have hv : v.functor ⋙ v.inverse = 𝟭 _ :=
    source_functor_inverse (k := k) T P candidates hlinear hfixed d other hother V
  change R ⋙ v.inverse = s.inverse ⋙ A
  calc
    R ⋙ v.inverse = (s.inverse ⋙ (s.functor ⋙ R)) ⋙ v.inverse := by
      change R ⋙ v.inverse = ((s.inverse ⋙ s.functor) ⋙ R) ⋙ v.inverse
      rw [hs,Functor.id_comp]
    _ = (s.inverse ⋙ (A ⋙ v.functor)) ⋙ v.inverse := by rw [he]
    _ = s.inverse ⋙ A := by
      change s.inverse ⋙ (A ⋙ (v.functor ⋙ v.inverse)) = _
      rw [hv,Functor.comp_id]

/-- Simultaneous raw lift, basis and cover comparisons commute with all allowed-range inclusions. -/
theorem comparison_range (h : S ⊆ V) :
    AnchoredFinite.rangeFunctor (I := d.Index) T other hother P d.region candidates h ⋙
      (comparison (k := k) T P candidates hlinear hfixed d e other other' hother hother' V).functor =
    (comparison (k := k) T P candidates hlinear hfixed d e other other' hother hother' S).functor ⋙
      AnchoredFinite.rangeFunctor (I := e.Index) T other' hother' P e.region candidates h := by
  have hd := source_inverse_range (k := k) T P candidates hlinear hfixed d other hother h
  have he := source_range (k := k) T P candidates hlinear hfixed e other' hother' h
  change (AnchoredFinite.rangeFunctor (I := d.Index) T other hother P d.region candidates h ⋙
    (sourceEquivalence (k := k) T P candidates hlinear hfixed d other hother V).inverse) ⋙
      (sourceEquivalence (k := k) T P candidates hlinear hfixed e other' hother' V).functor = _
  rw [hd]
  change (sourceEquivalence (k := k) T P candidates hlinear hfixed d other hother S).inverse ⋙
    (ActualRelative.rangeFunctor T P candidates h ⋙
      (sourceEquivalence (k := k) T P candidates hlinear hfixed e other' hother' V).functor) = _
  rw [he]
  rfl

end AnchoredDisplay
end AAT.AG.RelativeRepairComposition
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
