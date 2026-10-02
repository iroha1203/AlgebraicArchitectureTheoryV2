import ResearchLean.AG.RelativeRepairComposition.SubdivisionGeneratedActualNative
import ResearchLean.AG.RelativeRepairComposition.SubdivisionExternalRestoration

/-!
# Independent strict generated objects preserve full actual shared choices

## Implementation notes

The old and new shared readings restore their own independent actual repairs.
Actual collapse and arbitrary-factor restoration prove the readings agree.
Every independently supplied external object is retained in a two-sided strict
join comparison. All original actual external arrows remain unchanged.
-/
namespace AAT.AG.RelativeRepairComposition.Subdivision.GeneratedExternal
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
universe uk uG uI uE uB uD vE vB vD
variable {k : Type uk} [Field k] [Fintype k] [DecidableEq k]
variable {K : FiniteTransportPresentation.{uG}} {I : Type uI} [Fintype I] [DecidableEq I]
variable {E : Type uE} {B : Type uB} {D : Type uD}
variable [Category.{vE} E] [Category.{vB} B] [Category.{vD} D]
variable {p : E ⥤ B} {q : B ⥤ D}
variable (T : OriginalTowerPresentation K p q) (chosen : EdgeName (K := K))
variable (factor : Factorization T chosen)
variable [∀ v, Module k (T.toTower.localCoefficients.A v)]
attribute [local instance] LinearCoefficients.coefficientModules
variable (bases : FiniteFamily.Bases (k := k) T.toTower.localCoefficients.A)
variable (U : I → ClosedRegion K) (P : ClosedRegion K)
variable [∀ j, DecidablePred (· ∈ (U j).vertices)]
variable [∀ j, DecidablePred (· ∈ (U j).edges)] [∀ j, DecidablePred (· ∈ (U j).faces)]
variable [DecidablePred (· ∈ P.edges)] [DecidablePred (· ∈ P.faces)]
variable (candidates : Set (EdgeName (K := K))) [DecidablePred (· ∈ candidates)]
variable (owner : I) (hi : chosen ∈ ClosedRegion.privateAlwaysEdges U P candidates owner)
variable (hlinear : ∀ {s t : K.Vertex} (e : K.Edge s t) (a : k)
  (x : T.toTower.localCoefficients.A s),
  T.toTower.localCoefficients.edge e (a • x) = a • T.toTower.localCoefficients.edge e x)
variable [Fintype (EdgeName (K := K))] [DecidableEq (EdgeName (K := K))]
variable [Fintype K.TwoCell] [DecidableEq K.TwoCell]
variable (ek : FiniteElimination.Enumeration k)
variable (ee : FiniteElimination.Enumeration (EdgeName (K := K)))
variable (ef : FiniteElimination.Enumeration K.TwoCell)
local notation "Mo" => T.toTower.localCoefficients
local notation "Mn" => (TowerPresentation.localCoefficients (OriginalTowerPresentation.toTower (originalTower T chosen factor)))
local notation "Bn" => FiniteBases.expandedBases T chosen factor bases
local notation "Un" => (fun j => expandedRegion K chosen (U j))
local notation "Pn" => expandedRegion K chosen P
local notation "Cn" => oldEdgeSet K chosen candidates
local notation "en" => FiniteEnumerations.edgeEnumeration K chosen ee
local notation "Aw" => Additive (Kernel p q factor.middle)


variable (hfixed : ∀ f ∈ P.faces,
  T.toTower.upper.pathLift (K.twoLeft f) ≫ FiberAut.hom (T.comparator f) =
    T.toTower.upper.pathLift (K.twoRight f))
variable (ei : FiniteElimination.Enumeration I) (hc : ClosedRegion.IndexedCover U)
variable (allowed : Set (EdgeName (K := K)))
local notation "fixed" => fixedEdgesForRange P.edges candidates allowed
local notation "values" => (fun j => -CoverEquation.defect Mo P (ActualEquation.defectFamily T P hfixed) (U j))



universe uX vX
variable (W : ClosedRegion K) (hw : chosen ∉ W.edges)
local notation "N" => GeneratedStrictObjects.NewObjects T chosen factor bases U P candidates owner hi hlinear ek ee ef values (candidates \ allowed)
local notation "O" => GeneratedStrictObjects.OldObjects T bases U P candidates hlinear ek ee ef values (candidates \ allowed)
local notation "C" => GeneratedStrictObjects.rangeObjectsEquiv T chosen factor bases U P candidates owner hi hlinear ek ee ef allowed values
local notation "EN" => GeneratedCoverRestoration.newObjectEquiv T chosen factor bases U P candidates owner hi hlinear ek ee ef hfixed ei hc allowed
local notation "EO" => GeneratedCoverRestoration.oldObjectEquiv T bases U P candidates hlinear ek ee ef hfixed ei hc allowed

/-- Every independent new generated object restores the full actual old repair and full actual fresh value. -/
theorem restored_actual (y : N) :
    (EN).symm y = expandSupported T chosen factor fixed ((EO).symm ((C) y).1) ((C) y).2 := by
  apply (EN).injective
  rw [Equiv.apply_symm_apply]
  have h := GeneratedActualComparison.comparison_actual_restore T chosen factor bases U P candidates owner hi hlinear ek ee ef
    hfixed ei hc allowed ((EO).symm ((C) y).1) ((C) y).2
  rw [Equiv.apply_symm_apply,Equiv.symm_apply_apply] at h
  exact h

/-- New shared choices are read from the entire independently restored original new repair. -/
noncomputable def sharedNew (y : N) : SharedValues T W :=
  Subdivision.sharedNew T chosen factor W hw ((EN).symm y).1

/-- Old shared choices are read from the entire independently restored original old repair. -/
noncomputable def sharedOld (y : O) : SharedValues T W :=
  Subdivision.sharedOld T W ((EO).symm y).1

/-- The complete independent generated comparison preserves every full actual shared choice literally. -/
theorem shared_comparison (y : N) :
    sharedNew T chosen factor bases U P candidates owner hi hlinear ek ee ef hfixed ei hc allowed W hw y =
    sharedOld T bases U P candidates hlinear ek ee ef hfixed ei hc allowed W ((C) y).1 := by
  change Subdivision.sharedNew T chosen factor W hw ((EN).symm y).1 = _
  rw [restored_actual]
  exact shared_expand T chosen factor W hw ((EO).symm ((C) y).1).1 ((C) y).2

/-- Every independent external strict join has full inverse generated comparisons and the entire fresh kernel. -/
noncomputable def objectEquiv {X : Type uX} (boundary : X → SharedValues T W) :
    ContextRelations.StrictJoin
      (sharedNew T chosen factor bases U P candidates owner hi hlinear ek ee ef hfixed ei hc allowed W hw) boundary ≃
    ContextRelations.StrictJoin
      (sharedOld T bases U P candidates hlinear ek ee ef hfixed ei hc allowed W) boundary × Aw where
  toFun y := (⟨(((C) y.1.1).1,y.1.2),
    (shared_comparison T chosen factor bases U P candidates owner hi hlinear ek ee ef hfixed ei hc allowed W hw y.1.1).symm.trans y.2⟩,
    ((C) y.1.1).2)
  invFun y := ⟨((C).symm (y.1.1.1,y.2),y.1.1.2),by
    rw [shared_comparison,Equiv.apply_symm_apply]
    exact y.1.2⟩
  left_inv y := by
    apply Subtype.ext
    exact Prod.ext ((C).symm_apply_apply y.1.1) rfl
  right_inv y := by
    apply Prod.ext
    · apply Subtype.ext
      change (((C) ((C).symm (y.1.1.1,y.2))).1,y.1.1.2) = (y.1.1.1,y.1.1.2)
      rw [Equiv.apply_symm_apply]
    · change ((C) ((C).symm (y.1.1.1,y.2))).2 = y.2
      rw [Equiv.apply_symm_apply]

/-- The entire external object remains unchanged under full strict generated comparison. -/
theorem external_object_value {X : Type uX} (boundary : X → SharedValues T W)
    (y : ContextRelations.StrictJoin
      (sharedNew T chosen factor bases U P candidates owner hi hlinear ek ee ef hfixed ei hc allowed W hw) boundary) :
    (objectEquiv T chosen factor bases U P candidates owner hi hlinear ek ee ef hfixed ei hc allowed W hw boundary y).1.1.2 = y.1.2 := rfl

end AAT.AG.RelativeRepairComposition.Subdivision.GeneratedExternal
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.Subdivision.GeneratedExternal
