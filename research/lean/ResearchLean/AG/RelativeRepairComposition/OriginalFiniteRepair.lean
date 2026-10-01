import ResearchLean.AG.RelativeRepairComposition.OriginalFiniteCorrection
import ResearchLean.AG.RelativeRepairComposition.OriginalRangeClassification

/-! # Finite failed duals and successful full corrections for the original actual tower -/
namespace AAT.AG.RelativeRepairComposition
open CategoryTheory TransportCoherence AbelianLiftingObstruction TransportCoherence.Arbitrary
universe uk uG uE uB uD vE vB vD
namespace OriginalFiniteRepair
variable {k : Type uk} [Field k] [Fintype k] [DecidableEq k]
variable {K : FiniteTransportPresentation.{uG}}
variable {E : Type uE} {B : Type uB} {D : Type uD}
variable [Category.{vE} E] [Category.{vB} B] [Category.{vD} D]
variable {p : E ⥤ B} {q : B ⥤ D}
variable (T : OriginalTowerPresentation K p q)
variable [∀ v, Module k ((T.toTower.localCoefficients).A v)]
variable (P : ClosedRegion K) (candidates : Set (EdgeName (K := K)))
variable [DecidablePred (· ∈ candidates)]
variable (houtside : ∀ e ∈ candidates, e ∉ P.edges)
variable (hlinear : ∀ {i j : K.Vertex} (e : K.Edge i j) (t : k)
  (x : (T.toTower.localCoefficients).A i),
  (T.toTower.localCoefficients).edge e (t • x) = t • (T.toTower.localCoefficients).edge e x)
variable [Fintype (EdgeName (K := K))] [DecidableEq (EdgeName (K := K))]
variable (hfixed : ∀ f ∈ P.faces,
  T.toTower.upper.pathLift (K.twoLeft f) ≫ FiberAut.hom (T.comparator f) =
    T.toTower.upper.pathLift (K.twoRight f))
variable [DecidablePred (· ∈ P.edges)] [DecidablePred (· ∈ P.faces)]
variable [Fintype K.TwoCell] [DecidableEq K.TwoCell]
variable (basis : FiniteFamily.Bases (k := k) T.toTower.localCoefficients.A)
variable (enumK : FiniteElimination.Enumeration k)
variable (enumEdges : FiniteElimination.Enumeration (EdgeName (K := K)))
variable (enumFaces : FiniteElimination.Enumeration K.TwoCell)
variable (S : Set candidates) [DecidablePred (· ∈ S)]
local notation "M" => T.toTower.localCoefficients
local notation "delta" => ActualEquation.defectFamily T P hfixed
local notation "D0" => OriginalColumns.D (k := k) M P candidates hlinear
local notation "Bcol" => OriginalRanges.column (k := k) M P candidates houtside hlinear
local notation "obs" => LinearInterface.q D0 (-delta)

omit [Fintype k] [DecidableEq K.TwoCell] in
/-- The unconditional finite original-edge decision is exactly actual supported repair existence. -/
theorem success_decision_iff :
    (OriginalFiniteCorrection.find M basis P candidates hlinear delta S enumK enumEdges).isSome = true ↔
      Nonempty (SupportedRepair T
        (fixedEdgesForRange P.edges candidates (OriginalRanges.allowed candidates S))) :=
  (OriginalFiniteCorrection.find_isSome_iff M basis P candidates hlinear delta S enumK enumEdges).trans
    (SupportedNativeEquation.repairEquiv T P candidates
      (OriginalRanges.allowed candidates S) hfixed).nonempty_congr.symm

omit [Fintype k] in
/-- The unconditional finite original-row decision is exactly actual supported repair failure. -/
theorem failure_decision_iff :
    (OriginalFiniteDual.find M basis P candidates houtside hlinear (-delta) S enumK enumFaces).isSome = true ↔
      ¬ Nonempty (SupportedRepair T
        (fixedEdgesForRange P.edges candidates (OriginalRanges.allowed candidates S))) :=
  (OriginalFiniteDual.find_isSome_iff M basis P candidates houtside hlinear (-delta) S enumK enumFaces).trans
    (not_congr (OriginalRangeClassification.repair_nonempty_iff_range (k := k)
      T P candidates houtside hlinear hfixed S)).symm

/-- A finite successful result supplies all equation premises and restores actual original morphisms. -/
noncomputable def restoreFound
    (x : FiniteNative.Index1 M basis ClosedRegion.all P → k)
    (hx : OriginalFiniteCorrection.find M basis P candidates hlinear delta S enumK enumEdges = some x) :
    SupportedRepair T (fixedEdgesForRange P.edges candidates (OriginalRanges.allowed candidates S)) :=
  (SupportedNativeEquation.repairEquiv T P candidates (OriginalRanges.allowed candidates S) hfixed).symm
    (OriginalFiniteCorrection.restoreFound M basis P candidates hlinear delta S enumK enumEdges x hx)

/-- A failed actual repair range generates its original quotient dual from finite full-coordinate tests. -/
noncomputable def computedDual
    (h : ¬ Nonempty (SupportedRepair T
      (fixedEdgesForRange P.edges candidates (OriginalRanges.allowed candidates S)))) :
    {phi : Module.Dual k (OriginalRanges.ObstructionSpace (k := k) M P candidates hlinear) //
      phi obs ≠ 0 ∧ ∀ e ∈ S, phi.comp (Bcol e) = 0} :=
  OriginalFiniteDual.computedDual M basis P candidates houtside hlinear (-delta) S enumK enumFaces
    (fun hm => h ((OriginalRangeClassification.repair_nonempty_iff_range (k := k)
      T P candidates houtside hlinear hfixed S).mpr hm))

/-- A successful actual range generates its full original correction by finite enumeration. -/
noncomputable def computedRepair
    (h : Nonempty (SupportedRepair T
      (fixedEdgesForRange P.edges candidates (OriginalRanges.allowed candidates S)))) :
    SupportedRepair T (fixedEdgesForRange P.edges candidates (OriginalRanges.allowed candidates S)) :=
  (SupportedNativeEquation.repairEquiv T P candidates (OriginalRanges.allowed candidates S) hfixed).symm
    (OriginalFiniteCorrection.computedObject M basis P candidates hlinear delta S enumK enumEdges
      ((SupportedNativeEquation.repairEquiv T P candidates
        (OriginalRanges.allowed candidates S) hfixed).nonempty_congr.mp h))

end OriginalFiniteRepair
end AAT.AG.RelativeRepairComposition
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
