import Formal.Util.AssertStandardAxioms
import ResearchLean.AG.RelativeRepairComposition.AnchoredFiniteCover
import ResearchLean.AG.RelativeRepairComposition.GeneratedCoverRestoration

/-!
# Actual original repairs and independent raw finite reference equations

## Implementation notes

The original actual edge choices remain the source of truth. The construction
changes their coordinate reference, restricts on the original closed cells, and
normalizes the independent raw equations by the actual lift difference. Both
native inverse composites retain every original physical edge and gauge arrow.
-/
namespace AAT.AG.RelativeRepairComposition
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
universe uG uE uB uD vE vB vD uI
variable {K : FiniteTransportPresentation.{uG}} {I : Type uI}
variable {E : Type uE} {B : Type uB} {D : Type uD}
variable [Category.{vE} E] [Category.{vB} B] [Category.{vD} D]
variable {p : E ⥤ B} {q : B ⥤ D}
namespace AnchoredActualCover
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
variable (T : OriginalTowerPresentation K p q)
variable (other : ∀ {i j : K.Vertex} (_ : K.Edge i j), FiberAut (p ⋙ q) (T.original.object j))
variable (hother : ∀ {i j : K.Vertex} (e : K.Edge i j),
  fiberPushforward p q (T.original.object j) (other e) = T.core e)
variable (P : ClosedRegion K) (U : I → ClosedRegion K)
variable (hfixed : ∀ f ∈ P.faces,
  T.toTower.upper.pathLift (K.twoLeft f) ≫ FiberAut.hom (T.comparator f) =
    T.toTower.upper.pathLift (K.twoRight f))
variable (candidates allowed : Set (EdgeName (K := K)))
variable [∀ i, DecidablePred (· ∈ (U i).vertices)] [∀ i, DecidablePred (· ∈ (U i).edges)]
variable (enumI : FiniteElimination.Enumeration I) (hc : ClosedRegion.IndexedCover U)
local notation "M" => T.toTower.localCoefficients
local notation "δ" => ActualEquation.defectFamily T P hfixed
local notation "fixed" => fixedEdgesForRange P.edges candidates allowed

/-- Actual reference change is strict on every original object and full original arrow. -/
theorem reference_functor_inverse :
    (ActualRelative.referenceGroupoidEquiv T other hother P.vertices fixed).functor ⋙
      (ActualRelative.referenceGroupoidEquiv T other hother P.vertices fixed).inverse =
        𝟭 (RepairGroupoid T P.vertices fixed) := by
  apply Functor.ext_of_iso (ActualRelative.referenceGroupoidEquiv T other hother P.vertices fixed).unitIso.symm
    (labeledAction_left_obj (ActualRelative.referenceRepairEquiv T other hother fixed)
      (ActualRelative.reference_repair_equivariant T other hother P.vertices fixed))

/-- The actual inverse reference change is strict on all physically anchored choices and arrows. -/
theorem reference_inverse_functor :
    (ActualRelative.referenceGroupoidEquiv T other hother P.vertices fixed).inverse ⋙
      (ActualRelative.referenceGroupoidEquiv T other hother P.vertices fixed).functor =
        𝟭 (ActualRelative.AnchoredGroupoid T other hother P.vertices fixed) := by
  apply Functor.ext_of_iso (ActualRelative.referenceGroupoidEquiv T other hother P.vertices fixed).counitIso
    (labeledAction_right_obj (ActualRelative.referenceRepairEquiv T other hother fixed)
      (ActualRelative.reference_repair_equivariant T other hother P.vertices fixed))

/-- The original actual groupoid restricts by finite full-cochain gluing to strict normalized local equations. -/
noncomputable def originalEquivalence : RepairGroupoid T P.vertices fixed ≌
    StrictSupportedCover.Groupoid M P U candidates allowed δ :=
  (SupportedNativeEquation.equivalence T P candidates allowed hfixed).trans
    (StrictCoverRestoration.equivalence M P U candidates allowed δ enumI hc)

/-- Original actual finite restriction and restoration are inverse on every object and arrow. -/
theorem original_functor_inverse : (originalEquivalence T P U hfixed candidates allowed enumI hc).functor ⋙
    (originalEquivalence T P U hfixed candidates allowed enumI hc).inverse =
      𝟭 (RepairGroupoid T P.vertices fixed) :=
  strict_trans_functor_inverse _ _ (SupportedNativeEquation.functor_inverse T P candidates allowed hfixed)
    (StrictCoverRestoration.functor_inverse M P U candidates allowed δ enumI hc)

/-- Original actual finite restoration and restriction retain every local freedom and full arrow. -/
theorem original_inverse_functor : (originalEquivalence T P U hfixed candidates allowed enumI hc).inverse ⋙
    (originalEquivalence T P U hfixed candidates allowed enumI hc).functor =
      𝟭 (StrictSupportedCover.Groupoid M P U candidates allowed δ) :=
  strict_trans_inverse_functor _ _ (SupportedNativeEquation.inverse_functor T P candidates allowed hfixed)
    (StrictCoverRestoration.inverse_functor M P U candidates allowed δ enumI hc)

/-- Independent anchored actual repairs and independent raw strict finite equations have full native coordinates. -/
noncomputable def equivalence : ActualRelative.AnchoredGroupoid T other hother P.vertices fixed ≌
    AnchoredFinite.Groupoid T other hother P U candidates allowed :=
  (ActualRelative.referenceGroupoidEquiv T other hother P.vertices fixed).symm.trans
    ((originalEquivalence T P U hfixed candidates allowed enumI hc).trans
      (AnchoredFinite.equivalence T other hother P U hfixed candidates allowed).symm)

/-- The entire actual-raw composite restores every original physical choice and original full label. -/
theorem functor_inverse : (equivalence T other hother P U hfixed candidates allowed enumI hc).functor ⋙
    (equivalence T other hother P U hfixed candidates allowed enumI hc).inverse =
      𝟭 (ActualRelative.AnchoredGroupoid T other hother P.vertices fixed) :=
  strict_trans_functor_inverse _ _ (reference_inverse_functor T other hother P candidates allowed)
    (strict_trans_functor_inverse _ _ (original_functor_inverse T P U hfixed candidates allowed enumI hc)
      (AnchoredFinite.inverse_functor T other hother P U hfixed candidates allowed))

/-- The entire raw-actual composite retains all raw local freedoms and all compatible full labels. -/
theorem inverse_functor : (equivalence T other hother P U hfixed candidates allowed enumI hc).inverse ⋙
    (equivalence T other hother P U hfixed candidates allowed enumI hc).functor =
      𝟭 (AnchoredFinite.Groupoid T other hother P U candidates allowed) :=
  strict_trans_inverse_functor _ _ (reference_functor_inverse T other hother P candidates allowed)
    (strict_trans_inverse_functor _ _ (original_inverse_functor T P U hfixed candidates allowed enumI hc)
      (AnchoredFinite.functor_inverse T other hother P U hfixed candidates allowed))

/-- Every finite raw coordinate is the actual new-reference correction on the same original edge. -/
theorem forward_value
    (R : ActualRelative.AnchoredGroupoid T other hother P.vertices fixed) (i : I) (e : (U i).edges) :
    (((equivalence T other hother P U hfixed candidates allowed enumI hc).functor.obj R).back.1 i).1 e =
      (T.withAlternativeLift other hother).solutionCorrection R.back.1 e.1 := by
  change (SupportedNativeEquation.repairEquiv T P candidates allowed hfixed
    ((ActualRelative.referenceRepairEquiv T other hother fixed).symm R.back)).1.1.1
      ⟨e.1,Set.mem_univ e.1⟩ - T.alternativeCorrection other hother e.1 = _
  rw [SupportedNativeEquation.repair_value]
  exact (congrFun (ActualRelative.anchored_coord_inv_reference T other hother fixed R.back) e.1).symm

/-- Raw finite reconstruction restores each actual original new-reference correction value. -/
theorem inverse_value (y : AnchoredFinite.Groupoid T other hother P U candidates allowed)
    (i : I) (e : (U i).edges) :
    (T.withAlternativeLift other hother).solutionCorrection
      (((equivalence T other hother P U hfixed candidates allowed enumI hc).inverse.obj y).back.1) e.1 =
        (y.back.1 i).1 e := by
  have hf := forward_value T other hother P U hfixed candidates allowed enumI hc
    ((equivalence T other hother P U hfixed candidates allowed enumI hc).inverse.obj y) i e
  have hi := congrArg (fun F => F.obj y)
    (inverse_functor T other hother P U hfixed candidates allowed enumI hc)
  exact hf.symm.trans (congrArg (fun r => (r.back.1 i).1 e) hi)

end AnchoredActualCover
end AAT.AG.RelativeRepairComposition
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
