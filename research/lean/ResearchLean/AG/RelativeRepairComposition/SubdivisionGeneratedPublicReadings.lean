import ResearchLean.AG.RelativeRepairComposition.FiniteNativePublicCoordinates
import ResearchLean.AG.RelativeRepairComposition.SubdivisionFiniteIncidence

/-!
# Public finite coordinates read the same actual local corrections

## Implementation notes

Both edge splits are independently applied to their actual full local families.
The comparison of finite public indices is then proved to commute with the
actual local collapse. The complete physical family is compared separately so
that fixed public names and prescribed values are retained as well.
-/
namespace AAT.AG.RelativeRepairComposition.Subdivision.GeneratedPublicReadings
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
universe uk uG uI uE uB uD vE vB vD
variable {k : Type uk} [Field k]
variable {K : FiniteTransportPresentation.{uG}}
variable {E : Type uE} {B : Type uB} {D : Type uD}
variable [Category.{vE} E] [Category.{vB} B] [Category.{vD} D]
variable {p : E ⥤ B} {q : B ⥤ D}
variable (T : OriginalTowerPresentation K p q) (chosen : EdgeName (K := K))
variable (F : Factorization T chosen)
variable [∀ v, Module k (T.toTower.localCoefficients.A v)]
attribute [local instance] LinearCoefficients.coefficientModules
variable (bases : FiniteFamily.Bases (k := k) T.toTower.localCoefficients.A)
variable {I : Type uI} [Fintype I] [DecidableEq I]
variable (U : I → ClosedRegion K) (P : ClosedRegion K)
variable [∀ j, DecidablePred (· ∈ (U j).edges)] [DecidablePred (· ∈ P.edges)]
variable (candidates : Set (EdgeName (K := K))) [DecidablePred (· ∈ candidates)]
variable (i : I) (hi : chosen ∈ ClosedRegion.privateAlwaysEdges U P candidates i) (j : I)

/-- The new retained candidate predicate is computed from the original permission data. -/
def retainedCandidatesDecidable : DecidablePred (· ∈ oldEdgeSet K chosen candidates) :=
  FiniteIncidence.retainedSetDecidable K chosen candidates hi.2.2.1

attribute [local instance] retainedCandidatesDecidable

/-- Old public reading uses every original nonfixed public basis coordinate. -/
noncomputable def oldPublic (h : RelativeCover.C1 T.toTower.localCoefficients (U j) P) :
    FiniteNative.ZIndex T.toTower.localCoefficients bases (U j) P
      (ClosedRegion.privateAlwaysEdges U P candidates j) → k :=
  (FiniteNative.edgeSplit T.toTower.localCoefficients bases (U j) P
    (ClosedRegion.privateAlwaysEdges U P candidates j) h).2

/-- New public reading independently uses every new nonfixed public basis coordinate. -/
noncomputable def newPublic
    (h : RelativeCover.C1 (originalTower T chosen F).toTower.localCoefficients
      (expandedRegion K chosen (U j)) (expandedRegion K chosen P)) :
    FiniteNative.ZIndex (originalTower T chosen F).toTower.localCoefficients
      (FiniteBases.expandedBases T chosen F bases) (expandedRegion K chosen (U j))
      (expandedRegion K chosen P)
      (ClosedRegion.privateAlwaysEdges (fun l => expandedRegion K chosen (U l))
        (expandedRegion K chosen P) (oldEdgeSet K chosen candidates) j) → k :=
  letI := retainedCandidatesDecidable chosen U P candidates i hi
  letI : ∀ l, DecidablePred (· ∈ (expandedRegion K chosen (U l)).edges) :=
    fun l => FiniteIncidence.expandedEdgesDecidable K chosen (U l)
  letI : DecidablePred (· ∈ (expandedRegion K chosen P).edges) :=
    FiniteIncidence.expandedEdgesDecidable K chosen P
  (FiniteNative.edgeSplit (originalTower T chosen F).toTower.localCoefficients
    (FiniteBases.expandedBases T chosen F bases) (expandedRegion K chosen (U j))
    (expandedRegion K chosen P)
    (ClosedRegion.privateAlwaysEdges (fun l => expandedRegion K chosen (U l))
      (expandedRegion K chosen P) (oldEdgeSet K chosen candidates) j) h).2

/-- Finite public coordinate comparison commutes with the actual full local collapse. -/
theorem public_reading_collapse
    (h : RelativeCover.C1 (originalTower T chosen F).toTower.localCoefficients
      (expandedRegion K chosen (U j)) (expandedRegion K chosen P)) :
    GeneratedPublic.publicCoordinateEquiv T chosen F bases U P candidates i hi j
      (newPublic T chosen F bases U P candidates i hi j h) =
    oldPublic T bases U P candidates j (local1Equiv T chosen F (U j) P hi.2.1 h).1 := by
  funext z
  rw [GeneratedPublic.publicCoordinateEquiv_value]
  let e : publicEdges K U P candidates j :=
    ⟨z.1.1.1,z.1.1.2.1,z.1.1.2.2,z.2⟩
  have he : e.1 ≠ chosen := fun hz => chosen_not_public K chosen U P candidates i hi j (hz ▸ e.2)
  change bases.coordinate e.1.2.1
      (h.1 ⟨oldEdgeName K chosen e.1 he,e.2.1⟩) z.1.2 =
    bases.coordinate e.1.2.1
      ((local1Equiv T chosen F (U j) P hi.2.1 h).1.1 ⟨e.1,e.2.1⟩) z.1.2
  rw [local1Equiv_retained T chosen F (U j) P hi.2.1 h ⟨e.1,e.2.1⟩ he]

omit [Fintype I] [DecidableEq I] [∀ j, DecidablePred (· ∈ (U j).edges)]
  [DecidablePred (· ∈ P.edges)] [DecidablePred (· ∈ candidates)] in
/-- Complete physical public values, including every fixed name, commute with actual collapse. -/
theorem physical_reading_collapse
    (h : RelativeCover.C1 (originalTower T chosen F).toTower.localCoefficients
      (expandedRegion K chosen (U j)) (expandedRegion K chosen P)) :
    CompletePublic.PublicKernels.physicalFamilyEquiv K chosen U P candidates T F i hi j
      (CompletePublic.PublicKernels.relativePublic (presentation K chosen)
        (fun l => expandedRegion K chosen (U l)) (expandedRegion K chosen P)
        (oldEdgeSet K chosen candidates) (originalTower T chosen F) j h) =
      CompletePublic.PublicKernels.relativePublic K U P candidates T j
        (local1Equiv T chosen F (U j) P hi.2.1 h).1 := by
  apply Subtype.ext
  funext e
  rw [CompletePublic.PublicKernels.physicalFamilyEquiv_value]
  have he : e.1 ≠ chosen := fun hz =>
    CompletePublic.chosen_not_public K chosen U P candidates i hi j (hz ▸ e.2)
  change h.1 ⟨oldEdgeName K chosen e.1 he,e.2.1⟩ =
    (local1Equiv T chosen F (U j) P hi.2.1 h).1.1 ⟨e.1,e.2.1⟩
  exact (local1Equiv_retained T chosen F (U j) P hi.2.1 h ⟨e.1,e.2.1⟩ he).symm

end AAT.AG.RelativeRepairComposition.Subdivision.GeneratedPublicReadings
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.Subdivision.GeneratedPublicReadings
