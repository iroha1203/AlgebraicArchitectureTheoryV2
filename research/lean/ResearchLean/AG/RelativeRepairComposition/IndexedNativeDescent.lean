import ResearchLean.AG.RelativeRepairComposition.IndexedEquationDescent
import ResearchLean.AG.RelativeRepairComposition.NativeRestrictionCoherence

/-!
# Indexed descent of independent actual repairs

Local objects are independently defined actual repairs. Every seam is an actual
vertex reidentification satisfying its native action equation. Original-vertex
cocycles and all product gauge labels are retained. The coordinate equivalence
is generated from the accepted full-kernel actual repair equivalences.
-/
namespace AAT.AG.RelativeRepairComposition
open CategoryTheory TransportCoherence AbelianLiftingObstruction TransportCoherence.Arbitrary
universe uG uE uB uD vE vB vD uJ
variable {K : FiniteTransportPresentation.{uG}}
variable {E : Type uE} {B : Type uB} {D : Type uD} {J : Type uJ}
variable [Category.{vE} E] [Category.{vB} B] [Category.{vD} D]
variable {p : E ⥤ B} {q : B ⥤ D}
namespace IndexedNative
variable (T : OriginalTowerPresentation K p q) (P : ClosedRegion K)
variable (hfixed : ∀ f ∈ P.faces,
  T.toTower.upper.pathLift (K.twoLeft f) ≫ FiberAut.hom (T.comparator f) =
    T.toTower.upper.pathLift (K.twoRight f))
local notation "M" => T.toTower.localCoefficients
local notation "δ" => ActualEquation.defectFamily T P hfixed

/-- The complete native actual repair type on an original closed region. -/
abbrev LocalRepair (U : ClosedRegion K) :=
  SupportedRepair (ClosedRegion.restrictTower U T) (ClosedRegion.nativeIntersection U P).edges

/-- Every native vertex gauge on the same original fixed intersection. -/
noncomputable abbrev LocalLabels (U : ClosedRegion K) :=
  supportedC0 (ClosedRegion.restrictTower U T)
    (ClosedRegion.nativeIntersection U P).vertices (ClosedRegion.nativeIntersection U P).edges

/-- Read a native label at its exact original vertex in the original full kernel. -/
noncomputable def labelValue (U : ClosedRegion K) (b : LocalLabels T P U) (v : U.vertices) :
    T.toTower.localCoefficients.A v.1 := (ActualEquation.nativeGaugeEquiv T P U b).1 v

/-- Reading retains the actual original native vertex value. -/
theorem label_value_native (U : ClosedRegion K) (b : LocalLabels T P U) (v : U.vertices) :
    labelValue T P U b v = b.1 v := rfl

/-- Restrict the actual independent repair with the accepted original choice values. -/
noncomputable def restrictRepair {U V : ClosedRegion K} (inc : ClosedRegion.Inclusion V U)
    (R : LocalRepair T P U) : LocalRepair T P V :=
  ((NativeDescent.restrictionFunctor T P hfixed inc).obj ⟨(),R⟩).back

/-- Coordinates of actual restriction are the same full original restricted equation. -/
theorem restriction_coordinates {U V : ClosedRegion K} (inc : ClosedRegion.Inclusion V U)
    (R : LocalRepair T P U) :
    ActualEquation.nativeRepairEquiv T P hfixed V (restrictRepair T P hfixed inc R) =
      CoverEquation.restrictSolution M P δ inc (ActualEquation.nativeRepairEquiv T P hfixed U R) :=
  (ActualEquation.nativeRepairEquiv T P hfixed V).apply_symm_apply _

variable (U : J → ClosedRegion K)
/-- All actual local repairs and overlap gauge arrows with the full original triple cocycle. -/
@[ext] structure Datum where
  localRepair : ∀ j, LocalRepair T P (U j)
  seam : ∀ j k, LocalLabels T P (ClosedRegion.inter (U j) (U k))
  seam_arrow : ∀ j k,
    (Multiplicative.ofAdd (seam j k)) •
      restrictRepair T P hfixed (ClosedRegion.inter_left (U j) (U k)) (localRepair j) =
    restrictRepair T P hfixed (ClosedRegion.inter_right (U j) (U k)) (localRepair k)
  seam_self : ∀ j, seam j j = 0
  cocycle : ∀ j k l v (hj : v ∈ (U j).vertices) (hk : v ∈ (U k).vertices) (hl : v ∈ (U l).vertices),
    labelValue T P (ClosedRegion.inter (U j) (U k)) (seam j k) ⟨v,⟨hj,hk⟩⟩ + labelValue T P (ClosedRegion.inter (U k) (U l)) (seam k l) ⟨v,⟨hk,hl⟩⟩ =
      labelValue T P (ClosedRegion.inter (U j) (U l)) (seam j l) ⟨v,⟨hj,hl⟩⟩

/-- Coordinates retain all actual local objects and all original overlap gauge values. -/
noncomputable def coordinates (X : Datum T P hfixed U) : IndexedEquation.Datum M P δ U where
  localSolution j := ActualEquation.nativeRepairEquiv T P hfixed (U j) (X.localRepair j)
  seam j k := ActualEquation.nativeGaugeEquiv T P (ClosedRegion.inter (U j) (U k)) (X.seam j k)
  seam_equation j k := by
    have he := congrArg (ActualEquation.nativeRepairEquiv T P hfixed (ClosedRegion.inter (U j) (U k)))
      (X.seam_arrow j k)
    rw [ActualEquation.native_repair_equivariant, restriction_coordinates, restriction_coordinates] at he
    exact (congrArg Subtype.val he).symm
  seam_self j := by rw [X.seam_self, map_zero]
  cocycle j k l v hj hk hl := X.cocycle j k l v hj hk hl

/-- Restore all independent actual choices and all native seams from a full affine datum. -/
noncomputable def actual (X : IndexedEquation.Datum M P δ U) : Datum T P hfixed U where
  localRepair j := (ActualEquation.nativeRepairEquiv T P hfixed (U j)).symm (X.localSolution j)
  seam j k := (ActualEquation.nativeGaugeEquiv T P (ClosedRegion.inter (U j) (U k))).symm (X.seam j k)
  seam_arrow j k := by
    apply (ActualEquation.nativeRepairEquiv T P hfixed (ClosedRegion.inter (U j) (U k))).injective
    rw [ActualEquation.native_repair_equivariant, restriction_coordinates, restriction_coordinates]
    simp only [Equiv.apply_symm_apply]
    apply Subtype.ext
    exact (X.seam_equation j k).symm
  seam_self j := by rw [X.seam_self, map_zero]
  cocycle j k l v hj hk hl := X.cocycle j k l v hj hk hl

/-- Coordinate restoration returns every whole independent actual local repair and seam. -/
theorem actual_coordinates (X : Datum T P hfixed U) :
    actual T P hfixed U (coordinates T P hfixed U X) = X := by
  apply Datum.ext
  · funext j; exact (ActualEquation.nativeRepairEquiv T P hfixed (U j)).symm_apply_apply _
  · funext j k; exact (ActualEquation.nativeGaugeEquiv T P (ClosedRegion.inter (U j) (U k))).symm_apply_apply _

/-- Actual restoration returns the entire affine datum with all original values. -/
theorem coordinates_actual (X : IndexedEquation.Datum M P δ U) :
    coordinates T P hfixed U (actual T P hfixed U X) = X := by
  apply IndexedEquation.Datum.ext
  · funext j; exact (ActualEquation.nativeRepairEquiv T P hfixed (U j)).apply_symm_apply _
  · funext j k; exact (ActualEquation.nativeGaugeEquiv T P (ClosedRegion.inter (U j) (U k))).apply_symm_apply _

/-- All native data correspond bijectively, with every local choice and seam retained. -/
noncomputable def datumEquiv : Datum T P hfixed U ≃ IndexedEquation.Datum M P δ U where
  toFun := coordinates T P hfixed U
  invFun := actual T P hfixed U
  left_inv := actual_coordinates T P hfixed U
  right_inv := coordinates_actual T P hfixed U

/-- The complete native product of original local vertex labels. -/
noncomputable abbrev Labels := ∀ j, LocalLabels T P (U j)

/-- All native labels have the same original values as their affine coordinates. -/
noncomputable def labelEquiv : Labels T P U ≃+ IndexedEquation.Labels M P U where
  toFun c j := ActualEquation.nativeGaugeEquiv T P (U j) (c j)
  invFun c j := (ActualEquation.nativeGaugeEquiv T P (U j)).symm (c j)
  left_inv c := by funext j; exact (ActualEquation.nativeGaugeEquiv T P (U j)).symm_apply_apply _
  right_inv c := by funext j; exact (ActualEquation.nativeGaugeEquiv T P (U j)).apply_symm_apply _
  map_add' _ _ := rfl

/-- Generate the full actual gauge action from independent native data and all labels. -/
noncomputable instance addAction : AddAction (Labels T P U) (Datum T P hfixed U) where
  vadd c X := (datumEquiv T P hfixed U).symm
    (IndexedEquation.gauge M P δ U (labelEquiv T P U c) (datumEquiv T P hfixed U X))
  zero_vadd X := by
    change (datumEquiv T P hfixed U).symm
      (IndexedEquation.gauge M P δ U (labelEquiv T P U 0) (datumEquiv T P hfixed U X)) = X
    rw [map_zero, IndexedEquation.gauge_zero]
    exact (datumEquiv T P hfixed U).symm_apply_apply X
  add_vadd b c X := by
    change (datumEquiv T P hfixed U).symm
      (IndexedEquation.gauge M P δ U (labelEquiv T P U (b+c)) (datumEquiv T P hfixed U X)) =
      (datumEquiv T P hfixed U).symm
        (IndexedEquation.gauge M P δ U (labelEquiv T P U b)
          ((datumEquiv T P hfixed U) ((datumEquiv T P hfixed U).symm
            (IndexedEquation.gauge M P δ U (labelEquiv T P U c) (datumEquiv T P hfixed U X)))))
    rw [map_add, Equiv.apply_symm_apply, IndexedEquation.gauge_add]

/-- The native indexed groupoid retains every actual local repair and compatible original label. -/
abbrev Groupoid := ActionCategory (Multiplicative (Labels T P U)) (Datum T P hfixed U)

/-- The generated action is equivariant on every full native object and label. -/
theorem coordinates_gauge (c : Multiplicative (Labels T P U)) (X : Datum T P hfixed U) :
    datumEquiv T P hfixed U (c • X) =
      (labelEquiv T P U).toMultiplicative c • datumEquiv T P hfixed U X :=
  (datumEquiv T P hfixed U).apply_symm_apply _

/-- Every native descent object and arrow is equivalent to the same affine full datum. -/
noncomputable def coordinateEquivalence : Groupoid T P hfixed U ≌ IndexedEquation.Groupoid M P δ U :=
  changedLabelEquivalence (labelEquiv T P U).toMultiplicative
    (datumEquiv T P hfixed U) (coordinates_gauge T P hfixed U)

/-- Effectivity has the original K actual repair groupoid as its global source. -/
noncomputable def equivalence (hc : ClosedRegion.IndexedCover U) :
    RepairGroupoid T P.vertices P.edges ≌ Groupoid T P hfixed U :=
  (ActualEquation.originalRepairEquationEquivalence T P hfixed).trans
    ((IndexedEquation.equivalence M P δ U hc).trans (coordinateEquivalence T P hfixed U).symm)


/-- Every local component of the generated action is its independent actual vertex gauge. -/
theorem gauge_local (c : Labels T P U) (X : Datum T P hfixed U) (j : J) :
    ((Multiplicative.ofAdd c) • X).localRepair j = (Multiplicative.ofAdd (c j)) • X.localRepair j := by
  apply (ActualEquation.nativeRepairEquiv T P hfixed (U j)).injective
  have h := congrArg (fun X => X.localSolution j)
    (coordinates_gauge T P hfixed U (Multiplicative.ofAdd c) X)
  exact h.trans (ActualEquation.native_repair_equivariant T P hfixed (U j)
    (Multiplicative.ofAdd (c j)) (X.localRepair j)).symm

/-- Every overlap seam of the action retains the full original label adjustment. -/
theorem gauge_seam_value (c : Labels T P U) (X : Datum T P hfixed U) (j k : J)
    (v : (ClosedRegion.inter (U j) (U k)).vertices) :
    (((Multiplicative.ofAdd c) • X).seam j k).1 v =
      labelValue T P (ClosedRegion.inter (U j) (U k)) (X.seam j k) v + labelValue T P (U k) (c k) ⟨v.1,v.2.2⟩ - labelValue T P (U j) (c j) ⟨v.1,v.2.1⟩ := rfl

/-- Native arrows act by every independent actual local gauge. -/
theorem arrow_local {X Y : Groupoid T P hfixed U} (f : X ⟶ Y) (j : J) :
    (Multiplicative.ofAdd (f.1.toAdd j)) • X.back.localRepair j = Y.back.localRepair j := by
  rw [← gauge_local T P hfixed U f.1.toAdd X.back j]
  exact congrArg (fun X => X.localRepair j) f.2

/-- Native arrows preserve every original overlap label by its exact seam equation. -/
theorem arrow_seam_value {X Y : Groupoid T P hfixed U} (f : X ⟶ Y) (j k : J)
    (v : (ClosedRegion.inter (U j) (U k)).vertices) :
    (Y.back.seam j k).1 v = labelValue T P (ClosedRegion.inter (U j) (U k)) (X.back.seam j k) v +
      labelValue T P (U k) (f.1.toAdd k) ⟨v.1,v.2.2⟩ - labelValue T P (U j) (f.1.toAdd j) ⟨v.1,v.2.1⟩ := by
  have h := congrArg (fun X => (X.seam j k).1 v) f.2
  exact h.symm

/-- All actual local gauges with the full seam compatibility generate a native arrow. -/
noncomputable def arrowOfLabels {X Y : Groupoid T P hfixed U} (c : Labels T P U)
    (hl : ∀ j, (Multiplicative.ofAdd (c j)) • X.back.localRepair j = Y.back.localRepair j)
    (hs : ∀ j k (v : (ClosedRegion.inter (U j) (U k)).vertices),
      (Y.back.seam j k).1 v = labelValue T P (ClosedRegion.inter (U j) (U k)) (X.back.seam j k) v +
        labelValue T P (U k) (c k) ⟨v.1,v.2.2⟩ - labelValue T P (U j) (c j) ⟨v.1,v.2.1⟩) : X ⟶ Y :=
  ⟨Multiplicative.ofAdd c, by
    change (Multiplicative.ofAdd c) • X.back = Y.back
    apply Datum.ext
    · funext j; rw [gauge_local]; exact hl j
    · funext j k; apply Subtype.ext; funext v
      exact (hs j k v).symm⟩

/-- The arrow construction keeps the whole product of original native labels. -/
theorem arrow_of_labels_label {X Y : Groupoid T P hfixed U} (c : Labels T P U) (hl hs) :
    (arrowOfLabels T P hfixed U (X := X) (Y := Y) c hl hs).1.toAdd = c := rfl


/-- Every global actual edge choice restricts identically in every local native component. -/
theorem global_choice (hc : ClosedRegion.IndexedCover U) (R : RepairGroupoid T P.vertices P.edges)
    (j : J) {a b : (U j).vertices} (e : ClosedRegion.Edge (U j) a b) :
    (((equivalence T P hfixed U hc).functor.obj R).back.localRepair j).1.choice e = R.back.1.choice e.1 := by
  change ((NativeDescent.globalRestrictionFunctor T P hfixed (U j)).obj R).back.1.choice e = _
  exact NativeDescent.global_restriction_obj_choice T P hfixed (U j) R e

/-- Global actual gauge arrows retain every original vertex label in every local region. -/
theorem global_map_value (hc : ClosedRegion.IndexedCover U) {R Q : RepairGroupoid T P.vertices P.edges}
    (f : R ⟶ Q) (j : J) (v : (U j).vertices) :
    (((equivalence T P hfixed U hc).functor.map f).1.toAdd j).1 v = f.1.toAdd.1 v.1 := rfl

/-- The diagonal has the whole native zero seam, including stabilizer labels. -/
theorem global_seam (hc : ClosedRegion.IndexedCover U) (R : RepairGroupoid T P.vertices P.edges) (j k : J) :
    ((equivalence T P hfixed U hc).functor.obj R).back.seam j k = 0 :=
  (ActualEquation.nativeGaugeEquiv T P (ClosedRegion.inter (U j) (U k))).symm.map_zero

/-- Canonical restoration produces an actual repair on the original K from every native datum. -/
noncomputable def restoreActual (hc : ClosedRegion.IndexedCover U) (X : Datum T P hfixed U) :
    SupportedRepair T P.edges :=
  (ActualEquation.originalRepairEquiv T P hfixed).symm
    (IndexedEquation.restoreSolution M P δ U hc (coordinates T P hfixed U X))

/-- Every restored original actual choice is generated from its full original edge cochain. -/
theorem restore_actual_choice (hc : ClosedRegion.IndexedCover U) (X : Datum T P hfixed U)
    {a b : K.Vertex} (e : K.Edge a b) :
    (restoreActual T P hfixed U hc X).1.choice e =
      T.correctionChoice
        (ActualEquation.originalEdgeEquiv T P
          (IndexedEquation.restoreEdges M P δ U hc (coordinates T P hfixed U X))).1 e := rfl


/-- Each native seam is a full actual overlap arrow between the restricted independent repairs. -/
noncomputable def overlapArrow (X : Datum T P hfixed U) (j k : J) :
    (NativeDescent.restrictionFunctor T P hfixed (ClosedRegion.inter_left (U j) (U k))).obj
      ⟨(),X.localRepair j⟩ ⟶
    (NativeDescent.restrictionFunctor T P hfixed (ClosedRegion.inter_right (U j) (U k))).obj
      ⟨(),X.localRepair k⟩ :=
  ⟨Multiplicative.ofAdd (X.seam j k),X.seam_arrow j k⟩

/-- The actual seam arrow retains its entire original native gauge label. -/
theorem overlap_arrow_label (X : Datum T P hfixed U) (j k : J) :
    (overlapArrow T P hfixed U X j k).1.toAdd = X.seam j k := rfl

/-- Native triple coherence is equality in the full original triple-overlap gauge group. -/
theorem triple_gauge_cocycle (X : Datum T P hfixed U) (j k l : J) :
    RelativeCover.r0 M P (ClosedRegion.triple_first_pair (U j) (U k) (U l))
        (ActualEquation.nativeGaugeEquiv T P (ClosedRegion.inter (U j) (U k)) (X.seam j k)) +
      RelativeCover.r0 M P (ClosedRegion.triple_second_pair (U j) (U k) (U l))
        (ActualEquation.nativeGaugeEquiv T P (ClosedRegion.inter (U k) (U l)) (X.seam k l)) =
      RelativeCover.r0 M P (ClosedRegion.triple_outer_pair (U j) (U k) (U l))
        (ActualEquation.nativeGaugeEquiv T P (ClosedRegion.inter (U j) (U l)) (X.seam j l)) := by
  apply Subtype.ext; funext v
  exact X.cocycle j k l v.1 v.2.1 v.2.2.1 v.2.2.2


/-- Canonical native restoration has exactly the restored original affine diagonal. -/
theorem restored_coordinates (hc : ClosedRegion.IndexedCover U) (X : Datum T P hfixed U) :
    coordinates T P hfixed U
      (((equivalence T P hfixed U hc).functor.obj ⟨(),restoreActual T P hfixed U hc X⟩).back) =
      IndexedEquation.diagonalDatum M P δ U
        (IndexedEquation.restoreSolution M P δ U hc (coordinates T P hfixed U X)) := by
  change coordinates T P hfixed U (actual T P hfixed U
    (IndexedEquation.diagonalDatum M P δ U
      (ActualEquation.originalRepairEquiv T P hfixed
        ((ActualEquation.originalRepairEquiv T P hfixed).symm
          (IndexedEquation.restoreSolution M P δ U hc (coordinates T P hfixed U X)))))) = _
  rw [coordinates_actual, Equiv.apply_symm_apply]

/-- The complete native strictification labels restore every independent local actual repair and seam. -/
theorem gauge_global_restore (hc : ClosedRegion.IndexedCover U) (X : Datum T P hfixed U) :
    (Multiplicative.ofAdd ((labelEquiv T P U).symm
      (IndexedEquation.strictificationLabels M P δ U hc (coordinates T P hfixed U X)))) •
      (((equivalence T P hfixed U hc).functor.obj ⟨(),restoreActual T P hfixed U hc X⟩).back) = X := by
  apply (datumEquiv T P hfixed U).injective
  rw [coordinates_gauge]
  change IndexedEquation.gauge M P δ U
    ((labelEquiv T P U) ((labelEquiv T P U).symm
      (IndexedEquation.strictificationLabels M P δ U hc (coordinates T P hfixed U X))))
    (coordinates T P hfixed U
      (((equivalence T P hfixed U hc).functor.obj ⟨(),restoreActual T P hfixed U hc X⟩).back)) =
      coordinates T P hfixed U X
  rw [AddEquiv.apply_symm_apply, restored_coordinates]
  exact IndexedEquation.gauge_diagonal_restore M P δ U hc (coordinates T P hfixed U X)

/-- The canonical restoration is isomorphic to each full native datum with its generated actual labels. -/
noncomputable def canonicalRestorationIso (hc : ClosedRegion.IndexedCover U) (X : Groupoid T P hfixed U) :
    (equivalence T P hfixed U hc).functor.obj ⟨(),restoreActual T P hfixed U hc X.back⟩ ≅ X :=
  actionLabelIso (H := Multiplicative (Labels T P U)) (X := Datum T P hfixed U)
    (Multiplicative.ofAdd ((labelEquiv T P U).symm
      (IndexedEquation.strictificationLabels M P δ U hc (coordinates T P hfixed U X.back))))
    (gauge_global_restore T P hfixed U hc X.back)

/-- Every original vertex label of the canonical restoration is its vertexwise original seam. -/
theorem canonical_restoration_label_value (hc : ClosedRegion.IndexedCover U)
    (X : Groupoid T P hfixed U) (j : J) (v : (U j).vertices) :
    (((canonicalRestorationIso T P hfixed U hc X).hom.1.toAdd) j).1 v =
      ((X.back.seam
        (Family.coveringIndex (fun j => (U j).vertices) hc.vertices v.1) j).1
          ⟨v.1,⟨Family.covering_index_mem (fun j => (U j).vertices) hc.vertices v.1,v.2⟩⟩) := rfl

end IndexedNative
end AAT.AG.RelativeRepairComposition
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
