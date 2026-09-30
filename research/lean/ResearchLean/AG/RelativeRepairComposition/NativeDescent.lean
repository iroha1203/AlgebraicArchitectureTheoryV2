import ResearchLean.AG.RelativeRepairComposition.CommaCoordinates
import ResearchLean.AG.RelativeRepairComposition.NativeEquationBridge

/-!
# Native actual repair descent on a closed two-region cover

## Implementation notes

G-130 B uses the original K repair groupoid as its global source. Full affine
coordinates produce the native local restriction functors and a comparison with
the accepted actual restriction. Comma objects retain the whole overlap gauge;
the closed-cover exact sequence generates their effective global restoration.
The object and arrow value APIs keep the original physical choices and vertex
labels. Isomorphism-class gluing would lose the overlap gauge and stabilizers.
-/

namespace AAT.AG.RelativeRepairComposition
open CategoryTheory TransportCoherence AbelianLiftingObstruction TransportCoherence.Arbitrary
universe uG uE uB uD vE vB vD
variable {K : FiniteTransportPresentation.{uG}}
variable {E : Type uE} {B : Type uB} {D : Type uD}
variable [Category.{vE} E] [Category.{vB} B] [Category.{vD} D]
variable {p : E ⥤ B} {q : B ⥤ D}
namespace NativeDescent
variable (T : OriginalTowerPresentation K p q) (P : ClosedRegion K)
variable (hfixed : ∀ f ∈ P.faces,
  T.toTower.upper.pathLift (K.twoLeft f) ≫ FiberAut.hom (T.comparator f) =
    T.toTower.upper.pathLift (K.twoRight f))
local notation "M" => T.toTower.localCoefficients
local notation "δ" => ActualEquation.defectFamily T P hfixed

/-- All independent actual repairs and all original gauge labels on a native region. -/
abbrev LocalGroupoid (U : ClosedRegion K) :=
  RepairGroupoid (ClosedRegion.restrictTower U T)
    (ClosedRegion.nativeIntersection U P).vertices (ClosedRegion.nativeIntersection U P).edges

/-- Native actual restriction is generated from the same included edge and vertex coordinates. -/
noncomputable def restrictionFunctor {U V : ClosedRegion K} (i : ClosedRegion.Inclusion V U) :
    LocalGroupoid T P U ⥤ LocalGroupoid T P V :=
  CommaCoordinates.leftRestriction
    (ActualEquation.nativeRepairEquationEquivalence T P hfixed U)
    (ActualEquation.nativeRepairEquationEquivalence T P hfixed V)
    (CoverEquation.restrictionFunctor M P δ i)

/-- Actual restriction preserves each original vertex value of every gauge arrow. -/
theorem restriction_map_value {U V : ClosedRegion K} (i : ClosedRegion.Inclusion V U)
    {R Q : LocalGroupoid T P U} (b : R ⟶ Q) (v : V.vertices) :
    ((restrictionFunctor T P hfixed i).map b).1.toAdd.1 v =
      b.1.toAdd.1 ⟨v.1,i.vertices v.2⟩ := rfl

/-- Actual restriction preserves each original independent edge choice. -/
theorem restriction_obj_choice {U V : ClosedRegion K} (inc : ClosedRegion.Inclusion V U)
    (R : LocalGroupoid T P U) {i j : V.vertices} (e : ClosedRegion.Edge V i j) :
    ((restrictionFunctor T P hfixed inc).obj R).back.1.choice e =
      R.back.1.choice (show ClosedRegion.Edge U
        ⟨i.1,inc.vertices i.2⟩ ⟨j.1,inc.vertices j.2⟩ from ⟨e.1,inc.edges e.2⟩) := by
  change (ClosedRegion.restrictTower U T).correctionChoice
    ((ClosedRegion.restrictTower U T).solutionCorrection R.back.1)
      (show ClosedRegion.Edge U ⟨i.1,inc.vertices i.2⟩ ⟨j.1,inc.vertices j.2⟩ from
        ⟨e.1,inc.edges e.2⟩) = _
  exact (ClosedRegion.restrictTower U T).correctionChoice_solutionCorrection R.back.1 _

/-- Global actual restriction is generated directly from the original K coordinates. -/
noncomputable def globalRestrictionFunctor (U : ClosedRegion K) :
    RepairGroupoid T P.vertices P.edges ⥤ LocalGroupoid T P U :=
  (ActualEquation.originalRepairEquationEquivalence T P hfixed).functor ⋙
    CoverEquation.restrictionFunctor M P δ (ClosedRegion.to_all U) ⋙
      (ActualEquation.nativeRepairEquationEquivalence T P hfixed U).inverse

/-- Global restriction keeps each same named original actual edge choice. -/
theorem global_restriction_obj_choice (U : ClosedRegion K)
    (R : RepairGroupoid T P.vertices P.edges) {i j : U.vertices} (e : ClosedRegion.Edge U i j) :
    ((globalRestrictionFunctor T P hfixed U).obj R).back.1.choice e = R.back.1.choice e.1 := by
  change T.correctionChoice (T.solutionCorrection R.back.1) e.1 = _
  exact T.correctionChoice_solutionCorrection R.back.1 e.1

/-- Global restriction keeps every original vertex gauge value. -/
theorem global_restriction_map_value (U : ClosedRegion K)
    {R Q : RepairGroupoid T P.vertices P.edges} (b : R ⟶ Q) (v : U.vertices) :
    ((globalRestrictionFunctor T P hfixed U).map b).1.toAdd.1 v = b.1.toAdd.1 v.1 := rfl

/-- The accepted original restriction, with its native actual groupoid made explicit. -/
noncomputable def originalRestrictionFunctor (U : ClosedRegion K) :
    RepairGroupoid T P.vertices P.edges ⥤ LocalGroupoid T P U :=
  ClosedRegion.repairRestrictionFunctor U T P.vertices P.edges

/-- The coordinate-generated global restriction is the accepted original actual restriction on objects. -/
theorem global_restriction_obj_eq (U : ClosedRegion K)
    (R : RepairGroupoid T P.vertices P.edges) :
    (globalRestrictionFunctor T P hfixed U).obj R =
      (originalRestrictionFunctor T P U).obj R := by
  apply (ActionCategory.objEquiv
    (Multiplicative (supportedC0 (ClosedRegion.restrictTower U T)
      (ClosedRegion.nativeIntersection U P).vertices (ClosedRegion.nativeIntersection U P).edges))
    (SupportedRepair (ClosedRegion.restrictTower U T) (ClosedRegion.nativeIntersection U P).edges)).symm.injective
  apply Subtype.ext
  apply Solution.ext
  intro i j e
  exact global_restriction_obj_choice T P hfixed U R e

/-- The comparison transports the same actual repair with the identity original gauge. -/
noncomputable def globalRestrictionComparisonHom (U : ClosedRegion K)
    (R : RepairGroupoid T P.vertices P.edges) :
    (globalRestrictionFunctor T P hfixed U).obj R ⟶ (originalRestrictionFunctor T P U).obj R :=
  ⟨(1 : Multiplicative (supportedC0 (ClosedRegion.restrictTower U T)
    (ClosedRegion.nativeIntersection U P).vertices (ClosedRegion.nativeIntersection U P).edges)), by
    change (1 : Multiplicative (supportedC0 (ClosedRegion.restrictTower U T)
      (ClosedRegion.nativeIntersection U P).vertices (ClosedRegion.nativeIntersection U P).edges)) •
      ((globalRestrictionFunctor T P hfixed U).obj R).back =
        ((originalRestrictionFunctor T P U).obj R).back
    rw [one_smul]
    exact congrArg ActionCategory.back (global_restriction_obj_eq T P hfixed U R)⟩

/-- Both directions of the restriction comparison retain the identity original gauge. -/
noncomputable def globalRestrictionComparisonIso (U : ClosedRegion K)
    (R : RepairGroupoid T P.vertices P.edges) :
    (globalRestrictionFunctor T P hfixed U).obj R ≅ (originalRestrictionFunctor T P U).obj R where
  hom := globalRestrictionComparisonHom T P hfixed U R
  inv := ⟨(1 : Multiplicative (supportedC0 (ClosedRegion.restrictTower U T)
      (ClosedRegion.nativeIntersection U P).vertices (ClosedRegion.nativeIntersection U P).edges)), by
    change (1 : Multiplicative (supportedC0 (ClosedRegion.restrictTower U T)
      (ClosedRegion.nativeIntersection U P).vertices (ClosedRegion.nativeIntersection U P).edges)) •
      ((originalRestrictionFunctor T P U).obj R).back =
        ((globalRestrictionFunctor T P hfixed U).obj R).back
    rw [one_smul]
    exact (congrArg ActionCategory.back (global_restriction_obj_eq T P hfixed U R)).symm⟩
  hom_inv_id := Subtype.ext (by change (1 : Multiplicative (supportedC0 (ClosedRegion.restrictTower U T)
      (ClosedRegion.nativeIntersection U P).vertices (ClosedRegion.nativeIntersection U P).edges)) * 1 = 1; rw [one_mul])
  inv_hom_id := Subtype.ext (by change (1 : Multiplicative (supportedC0 (ClosedRegion.restrictTower U T)
      (ClosedRegion.nativeIntersection U P).vertices (ClosedRegion.nativeIntersection U P).edges)) * 1 = 1; rw [one_mul])

set_option maxHeartbeats 1000000 in
/-- The whole actual restriction functors agree by their full identity-labeled arrows. -/
noncomputable def globalRestrictionComparison (U : ClosedRegion K) :
    globalRestrictionFunctor T P hfixed U ≅ originalRestrictionFunctor T P U :=
  NatIso.ofComponents (F := globalRestrictionFunctor T P hfixed U)
    (G := originalRestrictionFunctor T P U)
    (fun R => globalRestrictionComparisonIso T P hfixed U R) (by
    intro R Q b
    apply Subtype.ext
    change (1 : Multiplicative (supportedC0 (ClosedRegion.restrictTower U T)
      (ClosedRegion.nativeIntersection U P).vertices (ClosedRegion.nativeIntersection U P).edges)) *
      (show Multiplicative (supportedC0 (ClosedRegion.restrictTower U T)
      (ClosedRegion.nativeIntersection U P).vertices (ClosedRegion.nativeIntersection U P).edges) from ((globalRestrictionFunctor T P hfixed U).map b).1) =
      (show Multiplicative (supportedC0 (ClosedRegion.restrictTower U T)
      (ClosedRegion.nativeIntersection U P).vertices (ClosedRegion.nativeIntersection U P).edges) from ((originalRestrictionFunctor T P U).map b).1) * 1
    rw [one_mul, mul_one]
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    funext v
    rfl)

/-- Every component of the restriction comparison has the identity original gauge label. -/
theorem global_restriction_comparison_label (U : ClosedRegion K)
    (R : RepairGroupoid T P.vertices P.edges) :
    ((globalRestrictionComparison T P hfixed U).hom.app R).1 = (1 : Multiplicative (supportedC0 (ClosedRegion.restrictTower U T)
      (ClosedRegion.nativeIntersection U P).vertices (ClosedRegion.nativeIntersection U P).edges)) := rfl

variable (U V : ClosedRegion K)

/-- Native actual homotopy pullback includes the full overlap isomorphism and all compatible arrows. -/
abbrev Descent := Comma
  (restrictionFunctor T P hfixed (ClosedRegion.inter_left U V))
  (restrictionFunctor T P hfixed (ClosedRegion.inter_right U V))

/-- Complete affine coordinates restore the native actual comma groupoid. -/
noncomputable def commaEquivalence : CoverEquation.Descent M P δ U V ≌ Descent T P hfixed U V :=
  CommaCoordinates.equivalence
    (ActualEquation.nativeRepairEquationEquivalence T P hfixed U)
    (ActualEquation.nativeRepairEquationEquivalence T P hfixed V)
    (ActualEquation.nativeRepairEquationEquivalence T P hfixed (ClosedRegion.inter U V))
    (CoverEquation.restrictionFunctor M P δ (ClosedRegion.inter_left U V))
    (CoverEquation.restrictionFunctor M P δ (ClosedRegion.inter_right U V))

/-- A closed cover glues the original actual repair groupoid, including every stabilizer label. -/
noncomputable def equivalence (hc : ClosedRegion.Cover U V) :
    RepairGroupoid T P.vertices P.edges ≌ Descent T P hfixed U V :=
  (ActualEquation.originalRepairEquationEquivalence T P hfixed).trans
    ((CoverEquation.descentEquivalence M P δ U V hc).trans
      (commaEquivalence T P hfixed U V))

/-- The forward descent functor preserves each original edge choice in the first region. -/
theorem equivalence_left_choice (hc : ClosedRegion.Cover U V)
    (R : RepairGroupoid T P.vertices P.edges) {i j : U.vertices} (e : ClosedRegion.Edge U i j) :
    (((equivalence T P hfixed U V hc).functor.obj R).left).back.1.choice e =
      R.back.1.choice e.1 :=
  global_restriction_obj_choice T P hfixed U R e

/-- The forward descent functor preserves each original edge choice in the second region. -/
theorem equivalence_right_choice (hc : ClosedRegion.Cover U V)
    (R : RepairGroupoid T P.vertices P.edges) {i j : V.vertices} (e : ClosedRegion.Edge V i j) :
    (((equivalence T P hfixed U V hc).functor.obj R).right).back.1.choice e =
      R.back.1.choice e.1 :=
  global_restriction_obj_choice T P hfixed V R e

/-- The first component of every forward descent arrow retains the entire original vertex value. -/
theorem equivalence_left_map_value (hc : ClosedRegion.Cover U V)
    {R Q : RepairGroupoid T P.vertices P.edges} (b : R ⟶ Q) (v : U.vertices) :
    (((equivalence T P hfixed U V hc).functor.map b).left).1.toAdd.1 v =
      b.1.toAdd.1 v.1 := rfl

/-- The second component of every forward descent arrow retains the entire original vertex value. -/
theorem equivalence_right_map_value (hc : ClosedRegion.Cover U V)
    {R Q : RepairGroupoid T P.vertices P.edges} (b : R ⟶ Q) (v : V.vertices) :
    (((equivalence T P hfixed U V hc).functor.map b).right).1.toAdd.1 v =
      b.1.toAdd.1 v.1 := rfl

/-- Every compatible actual local arrow is invertible in the native homotopy pullback. -/
theorem is_groupoid : IsGroupoid (Descent T P hfixed U V) :=
  CommaCoordinates.comma_is_groupoid
    (restrictionFunctor T P hfixed (ClosedRegion.inter_left U V))
    (restrictionFunctor T P hfixed (ClosedRegion.inter_right U V))

set_option maxHeartbeats 1000000 in
/-- Global descent has the identity overlap gauge at every original overlap vertex. -/
theorem equivalence_seam_label (hc : ClosedRegion.Cover U V)
    (R : RepairGroupoid T P.vertices P.edges) :
    (((equivalence T P hfixed U V hc).functor.obj R).hom).1 =
      (1 : Multiplicative (supportedC0 (ClosedRegion.restrictTower (ClosedRegion.inter U V) T)
        (ClosedRegion.nativeIntersection (ClosedRegion.inter U V) P).vertices
        (ClosedRegion.nativeIntersection (ClosedRegion.inter U V) P).edges)) := by
  let h := (ActualEquation.originalRepairEquationEquivalence T P hfixed).functor.obj R
  change ((CommaCoordinates.restoreFunctor
    (ActualEquation.nativeRepairEquationEquivalence T P hfixed U)
    (ActualEquation.nativeRepairEquationEquivalence T P hfixed V)
    (ActualEquation.nativeRepairEquationEquivalence T P hfixed (ClosedRegion.inter U V))
    (CoverEquation.restrictionFunctor M P δ (ClosedRegion.inter_left U V))
    (CoverEquation.restrictionFunctor M P δ (ClosedRegion.inter_right U V))).obj
      (CoverEquation.diagonalObj M P δ U V h)).hom.1 = _
  rw [CommaCoordinates.restore_seam, CommaCoordinates.left_comparison_hom,
    CommaCoordinates.right_comparison_hom]
  simp only [Category.comp_id, Category.id_comp]
  change
    ((ActualEquation.nativeGaugeEquiv T P (ClosedRegion.inter U V)).toMultiplicative.symm
      ((RelativeCover.r0 M P (ClosedRegion.inter_right U V)).toMultiplicative
        (((ActualEquation.nativeRepairEquationEquivalence T P hfixed V).counitIso.inv.app
          (CoverEquation.diagonalObj M P δ U V h).right).1)) *
    (ActualEquation.nativeGaugeEquiv T P (ClosedRegion.inter U V)).toMultiplicative.symm
      ((CoverEquation.diagonalObj M P δ U V h).hom.1)) *
    (ActualEquation.nativeGaugeEquiv T P (ClosedRegion.inter U V)).toMultiplicative.symm
      ((RelativeCover.r0 M P (ClosedRegion.inter_left U V)).toMultiplicative
        (((ActualEquation.nativeRepairEquationEquivalence T P hfixed U).counitIso.hom.app
          (CoverEquation.diagonalObj M P δ U V h).left).1)) = 1
  rw [ActualEquation.native_repair_counit_inv_label,
    ActualEquation.native_repair_counit_label]
  have hs : (CoverEquation.diagonalObj M P δ U V h).hom.1 =
      (1 : Multiplicative (RelativeCover.C0 M (ClosedRegion.inter U V) P)) := rfl
  rw [hs]
  simp only [map_one, one_mul]

end NativeDescent
end AAT.AG.RelativeRepairComposition
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.NativeDescent
