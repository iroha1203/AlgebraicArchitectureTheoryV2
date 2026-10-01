import Formal.Util.AssertStandardAxioms
import ResearchLean.AG.RelativeRepairComposition.NativeRepairInterface

/-!
# Strict inverse functors for complete interface coordinates

## Implementation notes

The coordinate unit and counit have identity labels. Together with exact object
restoration, this strengthens the native equivalence to equality of both
functor composites, including all transported original gauge arrows.
-/
namespace AAT.AG.RelativeRepairComposition
open CategoryTheory
section ChangedLabels
universe uG uH uX uY
variable {G : Type uG} {H : Type uH} [Group G] [Group H]
variable {X : Type uX} {Y : Type uY} [MulAction G X] [MulAction H Y]
variable (φ : G ≃* H) (e : X ≃ Y) (he : ∀ g x, e (g • x) = φ g • e x)

/-- The inverse coordinate composite is exactly the identity functor on all original arrows. -/
theorem changed_label_functor_inverse :
    (changedLabelEquivalence φ e he).functor ⋙ (changedLabelEquivalence φ e he).inverse =
      𝟭 (ActionCategory G X) := by
  apply Functor.ext_of_iso (changedLabelEquivalence φ e he).unitIso.symm
    (changed_label_left_obj φ e he)

/-- The forward coordinate composite is exactly the identity functor on all interface arrows. -/
theorem changed_label_inverse_functor :
    (changedLabelEquivalence φ e he).inverse ⋙ (changedLabelEquivalence φ e he).functor =
      𝟭 (ActionCategory H Y) := by
  apply Functor.ext_of_iso (changedLabelEquivalence φ e he).counitIso
    (changed_label_right_obj φ e he)

end ChangedLabels
open TransportCoherence AbelianLiftingObstruction TransportCoherence.Arbitrary
universe uk uK uE uB uD vE vB vD
variable {k : Type uk} [Field k] [Fintype k] [DecidableEq k]
variable {K : FiniteTransportPresentation.{uK}}
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


omit [DecidablePred (· ∈ P.vertices)] in
/-- The generated actual-repair coordinates have exact inverse functors on every object and arrow. -/
theorem native_functor_inverse :
    (equivalence T bases U P internalEdges hlinear hfixed enumK enumEdges enumFaces).functor ⋙ (equivalence T bases U P internalEdges hlinear hfixed enumK enumEdges enumFaces).inverse =
      𝟭 (RepairGroupoid (ClosedRegion.restrictTower U T)
      (ClosedRegion.nativeIntersection U P).vertices (ClosedRegion.nativeIntersection U P).edges) :=
  changed_label_functor_inverse (ActualEquation.nativeGaugeEquiv T P U).toMultiplicative
    (repairEquiv T bases U P internalEdges hlinear hfixed enumK enumEdges enumFaces) (repair_equivariant T bases U P internalEdges hlinear hfixed enumK enumEdges enumFaces)

omit [DecidablePred (· ∈ P.vertices)] in
/-- The generated actual-repair coordinates have exact inverse functors on every object and arrow. -/
theorem native_inverse_functor :
    (equivalence T bases U P internalEdges hlinear hfixed enumK enumEdges enumFaces).inverse ⋙ (equivalence T bases U P internalEdges hlinear hfixed enumK enumEdges enumFaces).functor =
      𝟭 (FiniteNative.GeneratedGroupoid M bases U P internalEdges hlinear δ enumK enumEdges enumFaces) :=
  changed_label_inverse_functor (ActualEquation.nativeGaugeEquiv T P U).toMultiplicative
    (repairEquiv T bases U P internalEdges hlinear hfixed enumK enumEdges enumFaces) (repair_equivariant T bases U P internalEdges hlinear hfixed enumK enumEdges enumFaces)

end NativeRepairInterface

end AAT.AG.RelativeRepairComposition

#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
