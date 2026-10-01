import ResearchLean.AG.RelativeRepairComposition.IndexedEquationDescent
import ResearchLean.AG.RelativeRepairComposition.IndexedNativeDescent
import ResearchLean.AG.RelativeRepairComposition.NativeRestrictionCoherence

/-!
# Refinement and assembly of indexed affine descent

All local objects, arrows and seams restrict by their original cell values.
The refinement comparison uses the full global restriction functor. Equivalences
with that common global source compare restoration naturally; vertexwise choices
of strictification are not assumed equal under refinement.
-/
namespace AAT.AG.RelativeRepairComposition
open CategoryTheory TransportCoherence AbelianLiftingObstruction
universe uG uA uJ uL uN
namespace ClosedRegion
variable {K : FiniteTransportPresentation.{uG}}
/-- Region intersections retain both original-cell inclusions of a refinement. -/
theorem inter_inclusion {U V X Y : ClosedRegion K} (i : Inclusion U X) (j : Inclusion V Y) :
    Inclusion (inter U V) (inter X Y) :=
  ⟨fun _ h => ⟨i.vertices h.1,j.vertices h.2⟩,fun _ h => ⟨i.edges h.1,j.edges h.2⟩,
    fun _ h => ⟨i.faces h.1,j.faces h.2⟩,fun _ h => ⟨i.triples h.1,j.triples h.2⟩⟩
end ClosedRegion
namespace IndexedEquation
variable {K : FiniteTransportPresentation.{uG}} {J : Type uJ} {L : Type uL}
variable (M : LocalCoefficients.{uG,uA} K) (P : ClosedRegion K)
variable (δ : RelativeCover.C2 M ClosedRegion.all P)
variable (U : J → ClosedRegion K) (V : L → ClosedRegion K) (α : L → J)
variable (inc : ∀ l, ClosedRegion.Inclusion (V l) (U (α l)))

/-- Refine every local solution and the same complete original overlap gauge. -/
noncomputable def refineDatum (X : Datum M P δ U) : Datum M P δ V where
  localSolution l := CoverEquation.restrictSolution M P δ (inc l) (X.localSolution (α l))
  seam j k := RelativeCover.r0 M P (ClosedRegion.inter_inclusion (inc j) (inc k)) (X.seam (α j) (α k))
  seam_equation j k := by
    have he := congrArg (RelativeCover.r1 M P (ClosedRegion.inter_inclusion (inc j) (inc k)))
      (X.seam_equation (α j) (α k))
    rw [map_add, RelativeCover.r_d0] at he
    exact he
  seam_self j := by rw [X.seam_self, map_zero]
  cocycle j k l v hj hk hl :=
    X.cocycle (α j) (α k) (α l) v ((inc j).vertices hj) ((inc k).vertices hk) ((inc l).vertices hl)

/-- All local gauge values restrict on the identical original vertices. -/
def refineLabels : Labels M P U →+ Labels M P V where
  toFun c l := RelativeCover.r0 M P (inc l) (c (α l))
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Refinement preserves the entire gauge action and every overlap arrow. -/
theorem refine_gauge (c : Multiplicative (Labels M P U)) (X : Datum M P δ U) :
    refineDatum M P δ U V α inc (c • X) =
      (Multiplicative.ofAdd (refineLabels M P U V α inc c.toAdd)) • refineDatum M P δ U V α inc X := by
  apply Datum.ext
  · funext l
    exact CoverEquation.restrict_gauge M P δ (inc l) (Multiplicative.ofAdd (c.toAdd (α l))) (X.localSolution (α l))
  · funext j k
    change RelativeCover.r0 M P _ (X.seam (α j) (α k) + _ - _) =
      RelativeCover.r0 M P _ (X.seam (α j) (α k)) + _ - _
    rw [map_sub, map_add]
    rfl

/-- The complete refinement functor acts on all objects and all original gauge labels. -/
noncomputable def refinementFunctor : Groupoid M P δ U ⥤ Groupoid M P δ V :=
  actionLabelFunctor (refineLabels M P U V α inc).toMultiplicative
    (refineDatum M P δ U V α inc) (refine_gauge M P δ U V α inc)

/-- Refined local object values are exactly the included original edge values. -/
theorem refinement_obj_value (X : Groupoid M P δ U) (l : L) (e : (V l).edges) :
    (((refinementFunctor M P δ U V α inc).obj X).back.localSolution l).1.1 e =
      (X.back.localSolution (α l)).1.1 ⟨e.1,(inc l).edges e.2⟩ := rfl

/-- Refined arrows keep every included original vertex value. -/
theorem refinement_map_value {X Y : Groupoid M P δ U} (f : X ⟶ Y) (l : L) (v : (V l).vertices) :
    (((refinementFunctor M P δ U V α inc).map f).1.toAdd l).1 v =
      (f.1.toAdd (α l)).1 ⟨v.1,(inc l).vertices v.2⟩ := rfl

/-- Refinement keeps every original value of the overlap seam. -/
theorem refinement_seam_value (X : Groupoid M P δ U) (j k : L)
    (v : (ClosedRegion.inter (V j) (V k)).vertices) :
    (((refinementFunctor M P δ U V α inc).obj X).back.seam j k).1 v =
      (X.back.seam (α j) (α k)).1 ⟨v.1,⟨(inc j).vertices v.2.1,(inc k).vertices v.2.2⟩⟩ := rfl

/-- Both global diagonals keep exactly the same full original affine solution. -/
theorem refine_diagonal (h : CoverEquation.Solution M P δ ClosedRegion.all) :
    refineDatum M P δ U V α inc (diagonalDatum M P δ U h) = diagonalDatum M P δ V h := by
  apply Datum.ext
  · funext j; apply Subtype.ext; rfl
  · funext j k; exact map_zero _

/-- The entire refinement commutes with the common original global source. -/
noncomputable def diagonalRefinementComparison :
    diagonalFunctor M P δ U ⋙ refinementFunctor M P δ U V α inc ≅ diagonalFunctor M P δ V :=
  identityLabelComparison _ _ (fun h => refine_diagonal M P δ U V α inc h.back) (by
    intro h k f
    apply Multiplicative.toAdd.injective
    funext l
    rfl)

/-- Every global comparison retains all identity vertex labels. -/
theorem diagonal_refinement_comparison_label (h : CoverEquation.Groupoid M P δ ClosedRegion.all) :
    ((diagonalRefinementComparison M P δ U V α inc).hom.app h).1 =
      (1 : Multiplicative (Labels M P V)) := rfl


/-- Refinement of two genuine original-cell covers is an equivalence on all objects and arrows. -/
theorem refinement_is_equivalence (hu : ClosedRegion.IndexedCover U) (hv : ClosedRegion.IndexedCover V) :
    (refinementFunctor M P δ U V α inc).IsEquivalence := by
  letI := diagonal_is_equivalence M P δ U hu
  letI := diagonal_is_equivalence M P δ V hv
  letI : (diagonalFunctor M P δ U ⋙ refinementFunctor M P δ U V α inc).IsEquivalence :=
    Functor.isEquivalence_of_iso (diagonalRefinementComparison M P δ U V α inc).symm
  exact Functor.isEquivalence_of_comp_left (diagonalFunctor M P δ U) (refinementFunctor M P δ U V α inc)

/-- All inverse functors and unit/counit maps for raw original-cell refinement. -/
noncomputable def refinementEquivalence (hu : ClosedRegion.IndexedCover U) (hv : ClosedRegion.IndexedCover V) :
    Groupoid M P δ U ≌ Groupoid M P δ V := by
  letI := refinement_is_equivalence M P δ U V α inc hu hv
  exact (refinementFunctor M P δ U V α inc).asEquivalence

/-- Both restoration functors recover the same original global object up to their full natural gauges. -/
noncomputable def restorationRefinementComparison
    (hu : ClosedRegion.IndexedCover U) (hv : ClosedRegion.IndexedCover V) :
    (equivalence M P δ U hu).inverse ≅
      refinementFunctor M P δ U V α inc ⋙ (equivalence M P δ V hv).inverse :=
  let e := equivalence M P δ U hu
  let f := equivalence M P δ V hv
  let R := refinementFunctor M P δ U V α inc
  e.inverse.rightUnitor.symm ≪≫ Functor.isoWhiskerLeft e.inverse f.unitIso ≪≫
    Functor.isoWhiskerLeft e.inverse (Functor.isoWhiskerRight (diagonalRefinementComparison M P δ U V α inc).symm f.inverse) ≪≫
    Functor.isoWhiskerLeft e.inverse (Functor.associator e.functor R f.inverse) ≪≫
    (Functor.associator e.inverse e.functor (R ⋙ f.inverse)).symm ≪≫
    Functor.isoWhiskerRight e.counitIso (R ⋙ f.inverse) ≪≫ (R ⋙ f.inverse).leftUnitor

end IndexedEquation
namespace ClosedRegion
variable {K : FiniteTransportPresentation.{uG}} {J : Type uJ} {L : Type uL}
/-- Assemble each nonempty or empty index fiber using all its original closed cells. -/
def assembly (U : J → ClosedRegion K) (α : J → L) (l : L) : ClosedRegion K :=
  indexedUnion (fun j : {j // α j = l} => U j.1)

/-- Every original region includes into its assembled group. -/
theorem to_assembly (U : J → ClosedRegion K) (α : J → L) (j : J) :
    Inclusion (U j) (assembly U α (α j)) :=
  to_indexed_union (fun k : {k // α k = α j} => U k.1) ⟨j,rfl⟩

/-- Assembly preserves every original zero-through-three-cell cover condition. -/
theorem assembly_cover (U : J → ClosedRegion K) (α : J → L) (hc : IndexedCover U) :
    IndexedCover (assembly U α) where
  vertices v := by obtain ⟨j,hj⟩ := hc.vertices v; exact ⟨α j,⟨⟨j,rfl⟩,hj⟩⟩
  edges e := by obtain ⟨j,hj⟩ := hc.edges e; exact ⟨α j,⟨⟨j,rfl⟩,hj⟩⟩
  faces f := by obtain ⟨j,hj⟩ := hc.faces f; exact ⟨α j,⟨⟨j,rfl⟩,hj⟩⟩
  triples t := by obtain ⟨j,hj⟩ := hc.triples t; exact ⟨α j,⟨⟨j,rfl⟩,hj⟩⟩
variable {N : Type uN}
/-- Flattening nested closed unions preserves all original cell names and incidences. -/
theorem assembly_flatten (U : J → ClosedRegion K) (α : J → L) (β : L → N) (n : N) :
    Inclusion (assembly (assembly U α) β n) (assembly U (fun j => β (α j)) n) := by
  constructor <;> intro v hv <;>
    obtain ⟨⟨l,hl⟩,⟨⟨j,hj⟩,hv⟩⟩ := hv <;>
    exact ⟨⟨j,(congrArg β hj).trans hl⟩,hv⟩

/-- Rebracketing nested closed unions retains all original cell values in the reverse direction. -/
theorem assembly_unflatten (U : J → ClosedRegion K) (α : J → L) (β : L → N) (n : N) :
    Inclusion (assembly U (fun j => β (α j)) n) (assembly (assembly U α) β n) := by
  constructor <;> intro v hv <;>
    obtain ⟨⟨j,hj⟩,hv⟩ := hv <;>
    exact ⟨⟨α j,hj⟩,⟨⟨j,rfl⟩,hv⟩⟩

/-- Reordering index names preserves the cover of every original cell. -/
theorem reindex_cover (U : J → ClosedRegion K) (σ : L ≃ J) (hc : IndexedCover U) :
    IndexedCover (fun l => U (σ l)) where
  vertices v := by obtain ⟨j,hj⟩ := hc.vertices v; exact ⟨σ.symm j,by simpa only [Equiv.apply_symm_apply] using hj⟩
  edges e := by obtain ⟨j,hj⟩ := hc.edges e; exact ⟨σ.symm j,by simpa only [Equiv.apply_symm_apply] using hj⟩
  faces f := by obtain ⟨j,hj⟩ := hc.faces f; exact ⟨σ.symm j,by simpa only [Equiv.apply_symm_apply] using hj⟩
  triples t := by obtain ⟨j,hj⟩ := hc.triples t; exact ⟨σ.symm j,by simpa only [Equiv.apply_symm_apply] using hj⟩
end ClosedRegion

open TransportCoherence.Arbitrary
universe uE uB uD vE vB vD
variable {K : FiniteTransportPresentation.{uG}} {J : Type uJ} {L : Type uL}
variable {E : Type uE} {B : Type uB} {D : Type uD}
variable [Category.{vE} E] [Category.{vB} B] [Category.{vD} D]
variable {p : E ⥤ B} {q : B ⥤ D}
namespace IndexedNative
variable (T : OriginalTowerPresentation K p q) (P : ClosedRegion K)
variable (hfixed : ∀ f ∈ P.faces,
  T.toTower.upper.pathLift (K.twoLeft f) ≫ FiberAut.hom (T.comparator f) =
    T.toTower.upper.pathLift (K.twoRight f))
local notation "M" => T.toTower.localCoefficients
local notation "δ" => ActualEquation.defectFamily T P hfixed
variable (U : J → ClosedRegion K) (V : L → ClosedRegion K) (α : L → J)
variable (inc : ∀ l, ClosedRegion.Inclusion (V l) (U (α l)))

/-- Native raw refinement retains all independent local actual repairs and their full gauge seams. -/
noncomputable def refinementFunctor : Groupoid T P hfixed U ⥤ Groupoid T P hfixed V :=
  (coordinateEquivalence T P hfixed U).functor ⋙
    IndexedEquation.refinementFunctor M P δ U V α inc ⋙ (coordinateEquivalence T P hfixed V).inverse

/-- Every refined physical edge choice is the exact included original local choice. -/
theorem refinement_local_choice (X : Groupoid T P hfixed U) (l : L)
    {a b : (V l).vertices} (e : ClosedRegion.Edge (V l) a b) :
    (((refinementFunctor T P hfixed U V α inc).obj X).back.localRepair l).1.choice e =
      (X.back.localRepair (α l)).1.choice
        (show ClosedRegion.Edge (U (α l)) ⟨a.1,(inc l).vertices a.2⟩ ⟨b.1,(inc l).vertices b.2⟩ from
          ⟨e.1,(inc l).edges e.2⟩) := by
  exact NativeDescent.restriction_obj_choice T P hfixed (inc l) ⟨(),X.back.localRepair (α l)⟩ e

/-- Every native refined arrow preserves the full original vertex gauge value. -/
theorem refinement_map_value {X Y : Groupoid T P hfixed U} (f : X ⟶ Y) (l : L) (v : (V l).vertices) :
    (((refinementFunctor T P hfixed U V α inc).map f).1.toAdd l).1 v =
      (f.1.toAdd (α l)).1 ⟨v.1,(inc l).vertices v.2⟩ := rfl

/-- Every actual overlap seam is restricted with exactly its original native vertex value. -/
theorem refinement_seam_value (X : Groupoid T P hfixed U) (j k : L)
    (v : (ClosedRegion.inter (V j) (V k)).vertices) :
    (((refinementFunctor T P hfixed U V α inc).obj X).back.seam j k).1 v =
      (X.back.seam (α j) (α k)).1 ⟨v.1,⟨(inc j).vertices v.2.1,(inc k).vertices v.2.2⟩⟩ := rfl

set_option maxHeartbeats 1000000 in
/-- The native diagonals agree with raw refinement using complete identity gauge labels. -/
noncomputable def diagonalRefinementComparison
    (hu : ClosedRegion.IndexedCover U) (hv : ClosedRegion.IndexedCover V) :
    (equivalence T P hfixed U hu).functor ⋙ refinementFunctor T P hfixed U V α inc ≅
      (equivalence T P hfixed V hv).functor :=
  identityLabelComparison _ _ (fun R => by
    change actual T P hfixed V
      (IndexedEquation.refineDatum M P δ U V α inc
        (coordinates T P hfixed U
          (actual T P hfixed U (IndexedEquation.diagonalDatum M P δ U
            ((ActualEquation.originalRepairEquationEquivalence T P hfixed).functor.obj R).back)))) =
      actual T P hfixed V (IndexedEquation.diagonalDatum M P δ V
        ((ActualEquation.originalRepairEquationEquivalence T P hfixed).functor.obj R).back)
    rw [coordinates_actual, IndexedEquation.refine_diagonal]) (by
    intro R Q f
    apply Multiplicative.toAdd.injective; funext l
    apply Subtype.ext; funext v
    rfl)

/-- Raw native refinement is an equivalence for both genuine original-cell covers. -/
theorem refinement_is_equivalence (hu : ClosedRegion.IndexedCover U) (hv : ClosedRegion.IndexedCover V) :
    (refinementFunctor T P hfixed U V α inc).IsEquivalence := by
  letI := IndexedEquation.refinement_is_equivalence M P δ U V α inc hu hv
  unfold refinementFunctor
  infer_instance

/-- Native refinement supplies its whole inverse, unit and counit on actual repairs and gauges. -/
noncomputable def refinementEquivalence (hu : ClosedRegion.IndexedCover U) (hv : ClosedRegion.IndexedCover V) :
    Groupoid T P hfixed U ≌ Groupoid T P hfixed V := by
  letI := refinement_is_equivalence T P hfixed U V α inc hu hv
  exact (refinementFunctor T P hfixed U V α inc).asEquivalence

/-- Both native restoration functors recover the same original K up to their full natural gauges. -/
noncomputable def restorationRefinementComparison
    (hu : ClosedRegion.IndexedCover U) (hv : ClosedRegion.IndexedCover V) :
    (equivalence T P hfixed U hu).inverse ≅
      refinementFunctor T P hfixed U V α inc ⋙ (equivalence T P hfixed V hv).inverse :=
  let e := equivalence T P hfixed U hu
  let f := equivalence T P hfixed V hv
  let R := refinementFunctor T P hfixed U V α inc
  e.inverse.rightUnitor.symm ≪≫ Functor.isoWhiskerLeft e.inverse f.unitIso ≪≫
    Functor.isoWhiskerLeft e.inverse
      (Functor.isoWhiskerRight (diagonalRefinementComparison T P hfixed U V α inc hu hv).symm f.inverse) ≪≫
    Functor.isoWhiskerLeft e.inverse (Functor.associator e.functor R f.inverse) ≪≫
    (Functor.associator e.inverse e.functor (R ⋙ f.inverse)).symm ≪≫
    Functor.isoWhiskerRight e.counitIso (R ⋙ f.inverse) ≪≫ (R ⋙ f.inverse).leftUnitor

/-- All closed-union assembly choices compare as full native equivalences with original restoration. -/
noncomputable def assemblyEquivalence (U : J → ClosedRegion K) (α : J → L) (hc : ClosedRegion.IndexedCover U) :
    Groupoid T P hfixed (ClosedRegion.assembly U α) ≌ Groupoid T P hfixed U :=
  refinementEquivalence T P hfixed (ClosedRegion.assembly U α) U α (ClosedRegion.to_assembly U α)
    (ClosedRegion.assembly_cover U α hc) hc

/-- Assembly and unassembled native descent restore the same original K by a full natural comparison. -/
noncomputable def restorationAssemblyComparison
    (U : J → ClosedRegion K) (α : J → L) (hc : ClosedRegion.IndexedCover U) :
    (equivalence T P hfixed (ClosedRegion.assembly U α) (ClosedRegion.assembly_cover U α hc)).inverse ≅
      (assemblyEquivalence T P hfixed U α hc).functor ⋙ (equivalence T P hfixed U hc).inverse :=
  restorationRefinementComparison T P hfixed (ClosedRegion.assembly U α) U α
    (ClosedRegion.to_assembly U α) (ClosedRegion.assembly_cover U α hc) hc


/-- Reordering the cover retains the full native objects, seams and arrows as an equivalence. -/
noncomputable def reorderEquivalence (U : J → ClosedRegion K) (σ : L ≃ J) (hc : ClosedRegion.IndexedCover U) :
    Groupoid T P hfixed U ≌ Groupoid T P hfixed (fun l => U (σ l)) :=
  refinementEquivalence T P hfixed U (fun l => U (σ l)) σ
    (fun l => ClosedRegion.Inclusion.refl (U (σ l))) hc (ClosedRegion.reindex_cover U σ hc)

/-- Both cover orders restore the same original K with the full natural gauge comparison. -/
noncomputable def restorationReorderComparison
    (U : J → ClosedRegion K) (σ : L ≃ J) (hc : ClosedRegion.IndexedCover U) :
    (equivalence T P hfixed U hc).inverse ≅
      (reorderEquivalence T P hfixed U σ hc).functor ⋙
        (equivalence T P hfixed (fun l => U (σ l)) (ClosedRegion.reindex_cover U σ hc)).inverse :=
  restorationRefinementComparison T P hfixed U (fun l => U (σ l)) σ
    (fun l => ClosedRegion.Inclusion.refl (U (σ l))) hc (ClosedRegion.reindex_cover U σ hc)


variable {N : Type uN}
/-- Changing the grouping of closed-union assembly keeps the complete native descent category. -/
noncomputable def assemblyBracketEquivalence (U : J → ClosedRegion K) (α : J → L) (β : L → N)
    (hc : ClosedRegion.IndexedCover U) :
    Groupoid T P hfixed (ClosedRegion.assembly (ClosedRegion.assembly U α) β) ≌
      Groupoid T P hfixed (ClosedRegion.assembly U (fun j => β (α j))) :=
  refinementEquivalence T P hfixed
    (ClosedRegion.assembly (ClosedRegion.assembly U α) β)
    (ClosedRegion.assembly U (fun j => β (α j))) id (ClosedRegion.assembly_unflatten U α β)
    (ClosedRegion.assembly_cover _ β (ClosedRegion.assembly_cover U α hc))
    (ClosedRegion.assembly_cover U (fun j => β (α j)) hc)

/-- Both assembly brackets restore the same original K through a full native natural comparison. -/
noncomputable def restorationAssemblyBracketComparison (U : J → ClosedRegion K) (α : J → L) (β : L → N)
    (hc : ClosedRegion.IndexedCover U) :
    (equivalence T P hfixed (ClosedRegion.assembly (ClosedRegion.assembly U α) β)
      (ClosedRegion.assembly_cover _ β (ClosedRegion.assembly_cover U α hc))).inverse ≅
      (assemblyBracketEquivalence T P hfixed U α β hc).functor ⋙
        (equivalence T P hfixed (ClosedRegion.assembly U (fun j => β (α j)))
          (ClosedRegion.assembly_cover U (fun j => β (α j)) hc)).inverse :=
  restorationRefinementComparison T P hfixed
    (ClosedRegion.assembly (ClosedRegion.assembly U α) β)
    (ClosedRegion.assembly U (fun j => β (α j))) id (ClosedRegion.assembly_unflatten U α β)
    (ClosedRegion.assembly_cover _ β (ClosedRegion.assembly_cover U α hc))
    (ClosedRegion.assembly_cover U (fun j => β (α j)) hc)

end IndexedNative
end AAT.AG.RelativeRepairComposition
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
