import ResearchLean.AG.RelativeRepairComposition.SubdivisionGeneratedStrictObjects
import ResearchLean.AG.RelativeRepairComposition.RelativeGeneratedCoverRanges

/-!
# All candidate range inclusions commute with independent subdivision generation

## Implementation notes

The same local generators, sections, relations and full private kernels are
used for every permission set. Inclusions only relax the independent public
zero predicate. Full subdivision comparison retains all coordinates and every
fresh value under each inclusion.
-/
namespace AAT.AG.RelativeRepairComposition.Subdivision.GeneratedCoverRanges
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


variable (S V : Set (EdgeName (K := K))) (hSV : S ⊆ V)

/-- A permission inclusion leaves every independently generated new component literal. -/
noncomputable def includeNew (values : ∀ j, RelativeCover.C2 Mo (U j) P)
    (y : GeneratedStrictObjects.NewObjects T chosen factor bases U P candidates owner hi
      hlinear ek ee ef values (candidates \ S)) :
    GeneratedStrictObjects.NewObjects T chosen factor bases U P candidates owner hi
      hlinear ek ee ef values (candidates \ V) := by
  letI := GeneratedPublicReadings.retainedCandidatesDecidable chosen U P candidates owner hi
  letI : ∀ j, DecidablePred (· ∈ (Un j).vertices) := fun j => FiniteIncidence.expandedVerticesDecidable K chosen (U j)
  letI : ∀ j, DecidablePred (· ∈ (Un j).edges) := fun j => FiniteIncidence.expandedEdgesDecidable K chosen (U j)
  letI : ∀ j, DecidablePred (· ∈ (Un j).faces) := fun j => FiniteIncidence.expandedFacesDecidable K chosen (U j)
  letI : DecidablePred (· ∈ (Pn).edges) := FiniteIncidence.expandedEdgesDecidable K chosen P
  letI : DecidablePred (· ∈ (Pn).faces) := FiniteIncidence.expandedFacesDecidable K chosen P
  letI : Fintype (EdgeName (K := presentation K chosen)) := FiniteEnumerations.edgeFintype K chosen ee
  letI : Fintype (presentation K chosen).TwoCell := inferInstanceAs (Fintype K.TwoCell)
  letI : DecidableEq (presentation K chosen).TwoCell := inferInstanceAs (DecidableEq K.TwoCell)
  refine ⟨y.1,⟨?_,y.2.2⟩⟩
  intro j e he
  obtain ⟨a,ha,hea⟩ := he
  exact y.2.1 j e ⟨a,⟨ha.1,fun hs => ha.2 (hSV hs)⟩,hea⟩

omit [Fintype (EdgeName (K := K))] in
/-- Every new relation, public coordinate and private kernel value is retained by each inclusion. -/
theorem includeNew_component (values : ∀ j, RelativeCover.C2 Mo (U j) P)
    (y : GeneratedStrictObjects.NewObjects T chosen factor bases U P candidates owner hi
      hlinear ek ee ef values (candidates \ S)) (j : I) :
    (includeNew T chosen factor bases U P candidates owner hi hlinear ek ee ef S V hSV values y).1 j = y.1 j := rfl

/-- The full independently generated subdivision comparison commutes with every permission inclusion. -/
theorem comparison_include (values : ∀ j, RelativeCover.C2 Mo (U j) P)
    (y : GeneratedStrictObjects.NewObjects T chosen factor bases U P candidates owner hi
      hlinear ek ee ef values (candidates \ S)) :
    GeneratedStrictObjects.rangeObjectsEquiv T chosen factor bases U P candidates owner hi hlinear ek ee ef V values
      (includeNew T chosen factor bases U P candidates owner hi hlinear ek ee ef S V hSV values y) =
    (RelativeGeneratedCoverRanges.includeObjects Mo bases U P candidates hlinear ek ee ef S V hSV values
      (GeneratedStrictObjects.rangeObjectsEquiv T chosen factor bases U P candidates owner hi hlinear ek ee ef S values y).1,
      (GeneratedStrictObjects.rangeObjectsEquiv T chosen factor bases U P candidates owner hi hlinear ek ee ef S values y).2) := by
  apply Prod.ext
  · apply Subtype.ext
    rfl
  · rfl

/-- Inverse full restoration commutes with every permission inclusion. -/
theorem restoration_include (values : ∀ j, RelativeCover.C2 Mo (U j) P)
    (y : GeneratedStrictObjects.OldObjects T bases U P candidates hlinear ek ee ef values (candidates \ S)) (r : Aw) :
    (GeneratedStrictObjects.rangeObjectsEquiv T chosen factor bases U P candidates owner hi hlinear ek ee ef V values).symm
      (RelativeGeneratedCoverRanges.includeObjects Mo bases U P candidates hlinear ek ee ef S V hSV values y,r) =
    includeNew T chosen factor bases U P candidates owner hi hlinear ek ee ef S V hSV values
      ((GeneratedStrictObjects.rangeObjectsEquiv T chosen factor bases U P candidates owner hi hlinear ek ee ef S values).symm (y,r)) := by
  apply (GeneratedStrictObjects.rangeObjectsEquiv T chosen factor bases U P candidates owner hi hlinear ek ee ef V values).injective
  rw [Equiv.apply_symm_apply,comparison_include,Equiv.apply_symm_apply]

omit [Fintype (EdgeName (K := K))] in
/-- Successive range inclusions keep the same full new generated object family. -/
theorem includeNew_comp (values : ∀ j, RelativeCover.C2 Mo (U j) P)
    (W : Set (EdgeName (K := K))) (hVW : V ⊆ W)
    (y : GeneratedStrictObjects.NewObjects T chosen factor bases U P candidates owner hi hlinear ek ee ef values (candidates \ S)) :
    includeNew T chosen factor bases U P candidates owner hi hlinear ek ee ef V W hVW values
      (includeNew T chosen factor bases U P candidates owner hi hlinear ek ee ef S V hSV values y) =
    includeNew T chosen factor bases U P candidates owner hi hlinear ek ee ef S W (Set.Subset.trans hSV hVW) values y := rfl

end AAT.AG.RelativeRepairComposition.Subdivision.GeneratedCoverRanges
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.Subdivision.GeneratedCoverRanges
