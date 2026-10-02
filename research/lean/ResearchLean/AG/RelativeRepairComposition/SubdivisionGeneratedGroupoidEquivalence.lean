import ResearchLean.AG.RelativeRepairComposition.SubdivisionGeneratedCoverAction
import ResearchLean.AG.RelativeRepairComposition.SupplementalGroupoidContraction

/-!
# Independent generated strict groupoid equivalence for every range

## Implementation notes

The full old-label and fresh-displacement comparison first retains every
object and every native arrow. Only the entire supplemental translation
factor is then contracted by its native projection, inverse section and full
natural isomorphism. Every original stabilizer and all private freedoms remain.
-/
namespace AAT.AG.RelativeRepairComposition.Subdivision.GeneratedGroupoidEquivalence
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



variable (allowed : Set (EdgeName (K := K)))
local notation "Ln" => StrictSupportedCover.Labels Mn Pn Un Cn (oldEdgeSet K chosen allowed)
local notation "Lo" => StrictSupportedCover.Labels Mo P U candidates allowed
local notation "N" values => GeneratedStrictObjects.NewObjects T chosen factor bases U P candidates owner hi hlinear ek ee ef values (candidates \ allowed)
local notation "O" values => GeneratedStrictObjects.OldObjects T bases U P candidates hlinear ek ee ef values (candidates \ allowed)
local notation "En" values => GeneratedStrictObjects.newExtraction T chosen factor bases U P candidates owner hi hlinear ek ee ef (candidates \ allowed) Set.diff_subset values


attribute [local instance] GeneratedCoverAction.freshComm

/-- Every independently generated new strict groupoid is natively equivalent to the whole old strict groupoid. -/
noncomputable def equivalence (values : ∀ j, RelativeCover.C2 Mo (U j) P) :
    ActionCategory (Multiplicative Ln) (N values) ≌ ActionCategory (Multiplicative Lo) (O values) :=
  (GeneratedCoverAction.equivalence T chosen factor bases U P candidates owner hi hlinear ek ee ef allowed values).trans
    (SupplementalGroupoidContraction.equivalence Lo (O values) Aw).symm

/-- The native collapse functor preserves every old strict label value and all original stabilizers. -/
theorem functor_label (values : ∀ j, RelativeCover.C2 Mo (U j) P)
    {x y : ActionCategory (Multiplicative Ln) (N values)} (f : x ⟶ y) :
    ((equivalence T chosen factor bases U P candidates owner hi hlinear ek ee ef allowed values).functor.map f).1 =
      Multiplicative.ofAdd (GeneratedCoverLabels.equivalence T chosen factor U P candidates allowed owner hi f.1.toAdd).1 := rfl

/-- The inverse native functor restores every old strict label through the full new label inverse. -/
theorem inverse_label (values : ∀ j, RelativeCover.C2 Mo (U j) P)
    {x y : ActionCategory (Multiplicative Lo) (O values)} (f : x ⟶ y) :
    ((equivalence T chosen factor bases U P candidates owner hi hlinear ek ee ef allowed values).inverse.map f).1 =
      (GeneratedCoverLabels.equivalence T chosen factor U P candidates allowed owner hi).toMultiplicative.symm
        (Multiplicative.ofAdd (f.1.toAdd,0)) := rfl

/-- The functor reads exactly the old full strict objects in the independently generated object comparison. -/
theorem functor_object (values : ∀ j, RelativeCover.C2 Mo (U j) P)
    (x : ActionCategory (Multiplicative Ln) (N values)) :
    ((equivalence T chosen factor bases U P candidates owner hi hlinear ek ee ef allowed values).functor.obj x).back =
      (GeneratedStrictObjects.rangeObjectsEquiv T chosen factor bases U P candidates owner hi hlinear ek ee ef allowed values x.back).1 := rfl

/-- Every arbitrary full new object is related naturally to its zero-supplement inverse representative. -/
noncomputable def fullRestoreIso (values : ∀ j, RelativeCover.C2 Mo (U j) P)
    (x : ActionCategory (Multiplicative Ln) (N values)) :
    (GeneratedCoverAction.equivalence T chosen factor bases U P candidates owner hi hlinear ek ee ef allowed values).inverse.obj
      ((SupplementalGroupoidContraction.projection Lo (O values) Aw ⋙
        SupplementalGroupoidContraction.sectionFunctor Lo (O values) Aw).obj
        ((GeneratedCoverAction.equivalence T chosen factor bases U P candidates owner hi hlinear ek ee ef allowed values).functor.obj x)) ≅ x :=
  ((GeneratedCoverAction.equivalence T chosen factor bases U P candidates owner hi hlinear ek ee ef allowed values).inverse.mapIso
    (SupplementalGroupoidContraction.counitComponent Lo (O values) Aw
      ((GeneratedCoverAction.equivalence T chosen factor bases U P candidates owner hi hlinear ek ee ef allowed values).functor.obj x))).trans
    ((GeneratedCoverAction.equivalence T chosen factor bases U P candidates owner hi hlinear ek ee ef allowed values).unitIso.app x).symm

end AAT.AG.RelativeRepairComposition.Subdivision.GeneratedGroupoidEquivalence
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.Subdivision.GeneratedGroupoidEquivalence
