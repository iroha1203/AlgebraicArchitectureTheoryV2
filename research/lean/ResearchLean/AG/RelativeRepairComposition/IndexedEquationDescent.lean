import ResearchLean.AG.RelativeRepairComposition.IndexedClosedCovers
import ResearchLean.AG.RelativeRepairComposition.CoverEquation

/-!
# All affine descent data on an indexed closed cover

Objects retain all local solutions and full overlap gauge labels. The cocycle
uses each original vertex in the threefold overlap. Product gauge action retains
all compatible local arrows; it never replaces them with their orbit classes.
-/
namespace AAT.AG.RelativeRepairComposition
open CategoryTheory TransportCoherence AbelianLiftingObstruction
universe uG uA uJ
namespace IndexedEquation
variable {K : FiniteTransportPresentation.{uG}} {J : Type uJ}
variable (M : LocalCoefficients.{uG,uA} K) (P : ClosedRegion K)
variable (δ : RelativeCover.C2 M ClosedRegion.all P) (U : J → ClosedRegion K)

/-- Full local affine objects and their original overlap arrows with triple cocycle. -/
@[ext] structure Datum where
  localSolution : ∀ j, CoverEquation.Solution M P δ (U j)
  seam : ∀ j k, RelativeCover.C0 M (ClosedRegion.inter (U j) (U k)) P
  seam_equation : ∀ j k,
    RelativeCover.r1 M P (ClosedRegion.inter_right (U j) (U k)) (localSolution k).1 =
      RelativeCover.r1 M P (ClosedRegion.inter_left (U j) (U k)) (localSolution j).1 +
        RelativeCover.d0 M (ClosedRegion.inter (U j) (U k)) P (seam j k)
  seam_self : ∀ j, seam j j = 0
  cocycle : ∀ j k l v (hj : v ∈ (U j).vertices) (hk : v ∈ (U k).vertices)
      (hl : v ∈ (U l).vertices),
    (seam j k).1 ⟨v,⟨hj,hk⟩⟩ + (seam k l).1 ⟨v,⟨hk,hl⟩⟩ =
      (seam j l).1 ⟨v,⟨hj,hl⟩⟩

/-- Every original vertex label in each local region. -/
abbrev Labels := ∀ j, RelativeCover.C0 M (U j) P

/-- Product gauge action on every local solution and overlap arrow. -/
noncomputable def gauge (c : Labels M P U) (X : Datum M P δ U) : Datum M P δ U where
  localSolution j := Equation.gauge _ _ _ _ (c j) (X.localSolution j)
  seam j k := X.seam j k + RelativeCover.r0 M P (ClosedRegion.inter_right (U j) (U k)) (c k) -
    RelativeCover.r0 M P (ClosedRegion.inter_left (U j) (U k)) (c j)
  seam_equation j k := by
    change RelativeCover.r1 M P _ ((X.localSolution k).1 + RelativeCover.d0 M (U k) P (c k)) =
      RelativeCover.r1 M P _ ((X.localSolution j).1 + RelativeCover.d0 M (U j) P (c j)) + _
    rw [map_add, map_add, RelativeCover.r_d0, RelativeCover.r_d0,
      map_sub, map_add, X.seam_equation]
    abel
  seam_self j := by
    apply Subtype.ext
    funext v
    change (X.seam j j).1 v + (c j).1 ⟨v.1,v.2.2⟩ - (c j).1 ⟨v.1,v.2.1⟩ = 0
    rw [X.seam_self]
    change 0 + (c j).1 ⟨v.1,v.2.2⟩ - (c j).1 ⟨v.1,v.2.1⟩ = 0
    simp
  cocycle j k l v hj hk hl := by
    change ((X.seam j k).1 ⟨v,⟨hj,hk⟩⟩ + (c k).1 ⟨v,hk⟩ - (c j).1 ⟨v,hj⟩) +
      ((X.seam k l).1 ⟨v,⟨hk,hl⟩⟩ + (c l).1 ⟨v,hl⟩ - (c k).1 ⟨v,hk⟩) =
      (X.seam j l).1 ⟨v,⟨hj,hl⟩⟩ + (c l).1 ⟨v,hl⟩ - (c j).1 ⟨v,hj⟩
    have h := X.cocycle j k l v hj hk hl
    calc
      _ = ((X.seam j k).1 ⟨v,⟨hj,hk⟩⟩ + (X.seam k l).1 ⟨v,⟨hk,hl⟩⟩) +
        (c l).1 ⟨v,hl⟩ - (c j).1 ⟨v,hj⟩ := by abel
      _ = _ := by rw [h]

/-- Zero local gauge keeps the whole descent datum. -/
theorem gauge_zero (X : Datum M P δ U) : gauge M P δ U 0 X = X := by
  apply Datum.ext
  · funext j; apply Subtype.ext
    change (X.localSolution j).1 + RelativeCover.d0 M (U j) P 0 = (X.localSolution j).1
    rw [map_zero, add_zero]
  · funext j k
    change X.seam j k + RelativeCover.r0 M P _ 0 - RelativeCover.r0 M P _ 0 = X.seam j k
    rw [map_zero, map_zero, add_zero, sub_zero]

/-- Successive gauges compose with the complete product of labels. -/
theorem gauge_add (b c : Labels M P U) (X : Datum M P δ U) :
    gauge M P δ U (b + c) X = gauge M P δ U b (gauge M P δ U c X) := by
  apply Datum.ext
  · funext j; apply Subtype.ext
    change (X.localSolution j).1 + RelativeCover.d0 M (U j) P (b j + c j) =
      ((X.localSolution j).1 + RelativeCover.d0 M (U j) P (c j)) + RelativeCover.d0 M (U j) P (b j)
    rw [map_add]; abel
  · funext j k
    change X.seam j k + RelativeCover.r0 M P _ (b k + c k) - RelativeCover.r0 M P _ (b j + c j) =
      (X.seam j k + RelativeCover.r0 M P _ (c k) - RelativeCover.r0 M P _ (c j)) +
        RelativeCover.r0 M P _ (b k) - RelativeCover.r0 M P _ (b j)
    rw [map_add, map_add]; abel

/-- The full action is generated from the actual local equations and cocycle. -/
noncomputable instance addAction : AddAction (Labels M P U) (Datum M P δ U) where
  vadd := gauge M P δ U
  zero_vadd := gauge_zero M P δ U
  add_vadd := gauge_add M P δ U

/-- The indexed affine descent groupoid with every compatible local label. -/
abbrev Groupoid := ActionCategory (Multiplicative (Labels M P U)) (Datum M P δ U)

/-- Global solutions restrict with their full local values and zero overlap seam. -/
noncomputable def diagonalDatum (h : CoverEquation.Solution M P δ ClosedRegion.all) :
    Datum M P δ U where
  localSolution j := CoverEquation.restrictSolution M P δ (ClosedRegion.to_all (U j)) h
  seam _ _ := 0
  seam_equation _ _ := by rw [map_zero, add_zero]; rfl
  seam_self _ := rfl
  cocycle _ _ _ _ _ _ _ := zero_add 0

/-- Global original gauges restrict to the full product of local original gauges. -/
def diagonalLabels : RelativeCover.C0 M ClosedRegion.all P →+ Labels M P U where
  toFun b j := RelativeCover.r0 M P (ClosedRegion.to_all (U j)) b
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The diagonal retains the full gauge action, including all seam labels. -/
theorem diagonal_gauge (b : Multiplicative (RelativeCover.C0 M ClosedRegion.all P))
    (h : CoverEquation.Solution M P δ ClosedRegion.all) :
    diagonalDatum M P δ U (b • h) =
      (Multiplicative.ofAdd (diagonalLabels M P U b.toAdd)) • diagonalDatum M P δ U h := by
  apply Datum.ext
  · funext j; exact CoverEquation.restrict_gauge M P δ (ClosedRegion.to_all (U j)) b h
  · funext j k; apply Subtype.ext; funext v
    change 0 = 0 + b.toAdd.1 ⟨v.1,Set.mem_univ v.1⟩ - b.toAdd.1 ⟨v.1,Set.mem_univ v.1⟩
    abel

/-- All global objects and all global arrows give indexed descent data. -/
noncomputable def diagonalFunctor : CoverEquation.Groupoid M P δ ClosedRegion.all ⥤ Groupoid M P δ U :=
  actionLabelFunctor (diagonalLabels M P U).toMultiplicative
    (diagonalDatum M P δ U) (diagonal_gauge M P δ U)


/-- Vertexwise seams from a covering region supply every local strictification label. -/
noncomputable def strictificationLabels (hc : ClosedRegion.IndexedCover U)
    (X : Datum M P δ U) : Labels M P U := fun j =>
  ⟨fun v => (X.seam (Family.coveringIndex (fun j => (U j).vertices) hc.vertices v.1) j).1
      ⟨v.1,⟨Family.covering_index_mem (fun j => (U j).vertices) hc.vertices v.1,v.2⟩⟩,
    fun _ hv => (X.seam _ j).2 _ hv⟩

/-- The full triple cocycle generates the difference of local strictification labels. -/
theorem strictification_difference (hc : ClosedRegion.IndexedCover U)
    (X : Datum M P δ U) (j k : J) :
    RelativeCover.r0 M P (ClosedRegion.inter_right (U j) (U k))
        (strictificationLabels M P δ U hc X k) -
      RelativeCover.r0 M P (ClosedRegion.inter_left (U j) (U k))
        (strictificationLabels M P δ U hc X j) = X.seam j k := by
  apply Subtype.ext; funext v
  let r := Family.coveringIndex (fun j => (U j).vertices) hc.vertices v.1
  have hr := Family.covering_index_mem (fun j => (U j).vertices) hc.vertices v.1
  change (X.seam r k).1 ⟨v.1,⟨hr,v.2.2⟩⟩ - (X.seam r j).1 ⟨v.1,⟨hr,v.2.1⟩⟩ =
    (X.seam j k).1 v
  rw [← X.cocycle r j k v.1 hr v.2.1 v.2.2]
  abel

/-- Strictification keeps every local solution and makes every overlap seam zero. -/
theorem strictification_seam_zero (hc : ClosedRegion.IndexedCover U)
    (X : Datum M P δ U) (j k : J) :
    (gauge M P δ U (-strictificationLabels M P δ U hc X) X).seam j k = 0 := by
  change X.seam j k + RelativeCover.r0 M P _ (-(strictificationLabels M P δ U hc X k)) -
    RelativeCover.r0 M P _ (-(strictificationLabels M P δ U hc X j)) = 0
  rw [map_neg, map_neg]
  have h := strictification_difference M P δ U hc X j k
  rw [← h]
  abel

/-- Corrected local solutions agree at every original shared edge. -/
noncomputable def strictCompatible (hc : ClosedRegion.IndexedCover U)
    (X : Datum M P δ U) : IndexedCover.Compatible1 M P U :=
  ⟨fun j => ((gauge M P δ U (-strictificationLabels M P δ U hc X) X).localSolution j).1, by
    intro j k e hj hk
    have he := (gauge M P δ U (-strictificationLabels M P δ U hc X) X).seam_equation j k
    rw [strictification_seam_zero, map_zero, add_zero] at he
    exact (congrArg (fun h => h.1 ⟨e,⟨hj,hk⟩⟩) he).symm⟩

/-- All original global edge values restored from the corrected local affine solutions. -/
noncomputable def restoreEdges (hc : ClosedRegion.IndexedCover U) (X : Datum M P δ U) :
    RelativeCover.C1 M ClosedRegion.all P :=
  IndexedCover.glue1 M P U hc (strictCompatible M P δ U hc X)

/-- Restoration returns every corrected original local edge value. -/
theorem restore_restriction (hc : ClosedRegion.IndexedCover U) (X : Datum M P δ U) (j : J) :
    RelativeCover.r1 M P (ClosedRegion.to_all (U j)) (restoreEdges M P δ U hc X) =
      ((gauge M P δ U (-strictificationLabels M P δ U hc X) X).localSolution j).1 := by
  exact congrArg (fun b => b.1 j) (IndexedCover.restrict_glue1 M P U hc (strictCompatible M P δ U hc X))

/-- Every restored edge family satisfies every original affine face equation. -/
theorem restore_equation (hc : ClosedRegion.IndexedCover U) (X : Datum M P δ U) :
    RelativeCover.d1 M ClosedRegion.all P (restoreEdges M P δ U hc X) = -δ := by
  apply IndexedCover.restriction2_injective M P U hc
  apply Subtype.ext; funext j
  change RelativeCover.r2 M P (ClosedRegion.to_all (U j))
    (RelativeCover.d1 M ClosedRegion.all P (restoreEdges M P δ U hc X)) =
      RelativeCover.r2 M P (ClosedRegion.to_all (U j)) (-δ)
  rw [RelativeCover.r_d1, restore_restriction, map_neg]
  exact ((gauge M P δ U (-strictificationLabels M P δ U hc X) X).localSolution j).2

/-- The global original affine solution is generated from every descent datum. -/
noncomputable def restoreSolution (hc : ClosedRegion.IndexedCover U) (X : Datum M P δ U) :
    CoverEquation.Solution M P δ ClosedRegion.all :=
  ⟨restoreEdges M P δ U hc X, by rw [CoverEquation.defect_all]; exact restore_equation M P δ U hc X⟩


/-- The restored solution's full diagonal is the whole strictified datum. -/
theorem diagonal_restore (hc : ClosedRegion.IndexedCover U) (X : Datum M P δ U) :
    diagonalDatum M P δ U (restoreSolution M P δ U hc X) =
      gauge M P δ U (-strictificationLabels M P δ U hc X) X := by
  apply Datum.ext
  · funext j; apply Subtype.ext
    exact restore_restriction M P δ U hc X j
  · funext j k; exact (strictification_seam_zero M P δ U hc X j k).symm

/-- Every local solution and seam are recovered by their generated strictification labels. -/
theorem gauge_diagonal_restore (hc : ClosedRegion.IndexedCover U) (X : Datum M P δ U) :
    gauge M P δ U (strictificationLabels M P δ U hc X)
      (diagonalDatum M P δ U (restoreSolution M P δ U hc X)) = X := by
  rw [diagonal_restore, ← gauge_add, add_neg_cancel, gauge_zero]

/-- A cover detects every original global arrow label. -/
theorem diagonal_faithful (hc : ClosedRegion.IndexedCover U) :
    (diagonalFunctor M P δ U).Faithful where
  map_injective := by
    intro h k f g he
    apply Subtype.ext; apply Multiplicative.toAdd.injective
    apply IndexedCover.restriction0_injective M P U hc
    apply Subtype.ext
    exact congrArg (fun b => b.1.toAdd) he

/-- Every compatible local arrow between diagonal objects restores its original global label. -/
theorem diagonal_full (hc : ClosedRegion.IndexedCover U) :
    (diagonalFunctor M P δ U).Full where
  map_surjective := by
    intro h k f
    let c := f.1.toAdd
    have hcompat : c ∈ IndexedCover.Compatible0 M P U := by
      intro j l v hj hl
      have hs := congrArg (fun X => (X.seam j l).1 ⟨v,⟨hj,hl⟩⟩) f.2
      change 0 + (c l).1 ⟨v,hl⟩ - (c j).1 ⟨v,hj⟩ = 0 at hs
      exact (sub_eq_zero.mp (by simpa only [zero_add] using hs)).symm
    let b := IndexedCover.glue0 M P U hc ⟨c,hcompat⟩
    have hb (j : J) : RelativeCover.r0 M P (ClosedRegion.to_all (U j)) b = c j :=
      congrArg (fun a => a.1 j) (IndexedCover.restrict_glue0 M P U hc ⟨c,hcompat⟩)
    have hg : k.back.1 = h.back.1 + RelativeCover.d0 M ClosedRegion.all P b := by
      apply IndexedCover.restriction1_injective M P U hc
      apply Subtype.ext; funext j
      have he := congrArg (fun X => (X.localSolution j).1) f.2
      change RelativeCover.r1 M P (ClosedRegion.to_all (U j)) h.back.1 +
          RelativeCover.d0 M (U j) P (c j) =
        RelativeCover.r1 M P (ClosedRegion.to_all (U j)) k.back.1 at he
      change RelativeCover.r1 M P (ClosedRegion.to_all (U j)) k.back.1 =
        RelativeCover.r1 M P (ClosedRegion.to_all (U j)) (h.back.1 + RelativeCover.d0 M ClosedRegion.all P b)
      rw [map_add, RelativeCover.r_d0, hb]
      exact he.symm
    refine ⟨Equation.homOfLabel _ _ _ _ b hg, ?_⟩
    apply Subtype.ext; apply Multiplicative.toAdd.injective
    funext j
    exact hb j

set_option synthInstance.maxHeartbeats 1000000 in
/-- Every full descent object comes from the original global affine solution up to its full gauges. -/
theorem diagonal_essSurj (hc : ClosedRegion.IndexedCover U) :
    (diagonalFunctor M P δ U).EssSurj where
  mem_essImage X := by
    let h : CoverEquation.Groupoid M P δ ClosedRegion.all :=
      ⟨(),restoreSolution M P δ U hc X.back⟩
    let f : (diagonalFunctor M P δ U).obj h ⟶ X :=
      ⟨Multiplicative.ofAdd (strictificationLabels M P δ U hc X.back),
        gauge_diagonal_restore M P δ U hc X.back⟩
    exact ⟨h,⟨asIso f⟩⟩

/-- Indexed descent is effective on all objects and all original gauge arrows. -/
theorem diagonal_is_equivalence (hc : ClosedRegion.IndexedCover U) :
    (diagonalFunctor M P δ U).IsEquivalence := by
  letI := diagonal_faithful M P δ U hc
  letI := diagonal_full M P δ U hc
  letI := diagonal_essSurj M P δ U hc
  exact { faithful := inferInstance, full := inferInstance, essSurj := inferInstance }

/-- The full indexed affine equivalence retains inverse functors, unit and counit. -/
noncomputable def equivalence (hc : ClosedRegion.IndexedCover U) :
    CoverEquation.Groupoid M P δ ClosedRegion.all ≌ Groupoid M P δ U := by
  letI := diagonal_is_equivalence M P δ U hc
  exact (diagonalFunctor M P δ U).asEquivalence

end IndexedEquation
end AAT.AG.RelativeRepairComposition
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
