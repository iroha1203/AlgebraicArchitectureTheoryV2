import ResearchLean.AG.RelativeRepairComposition.SubdivisionGeneratedRelations
import ResearchLean.AG.RelativeRepairComposition.SupplementalAction

/-!
# Full independent generated interfaces under actual local subdivision

## Implementation notes

The object comparison restores the new generated section, applies the actual
full local cochain comparison, and then extracts the independently generated
old coordinates. Different computed sections are allowed. Native actions use
all original relative labels, paired with every fresh displacement, so no
stabilizer or supplemental freedom is removed.
-/
namespace AAT.AG.RelativeRepairComposition.Subdivision.GeneratedInterfaces
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
universe uk uG uI uE uB uD vE vB vD
variable {K : FiniteTransportPresentation.{uG}}
variable {E : Type uE} {B : Type uB} {D : Type uD}
variable [Category.{vE} E] [Category.{vB} B] [Category.{vD} D]
variable {p : E ⥤ B} {q : B ⥤ D}
variable (T : OriginalTowerPresentation K p q) (chosen : EdgeName (K := K))
variable (factor : Factorization T chosen)
variable {I : Type uI} (U : I → ClosedRegion K) (P : ClosedRegion K)
variable (candidates : Set (EdgeName (K := K))) (i : I)
variable (hi : chosen ∈ ClosedRegion.privateAlwaysEdges U P candidates i) (j : I)
local notation "Mo" => (T.toTower.localCoefficients)
local notation "Mn" => (TowerPresentation.localCoefficients (OriginalTowerPresentation.toTower (originalTower T chosen factor)))
local notation "Un" => expandedRegion K chosen (U j)
local notation "Pn" => expandedRegion K chosen P
local notation "R" => localSupplement T chosen factor (U j)

/-- Full native labels are compared by every old label and every actual fresh displacement. -/
noncomputable def labelsEquiv : Multiplicative (RelativeCover.C0 Mn Un Pn) ≃*
    Multiplicative (RelativeCover.C0 Mo (U j) P × R) :=
  (local0Equiv T chosen factor (U j) P hi.2.1).toMultiplicative

/-- Every label comparison reads the unchanged complete actual local zero-cochain coordinates. -/
theorem labelsEquiv_value (b : Multiplicative (RelativeCover.C0 Mn Un Pn)) :
    (labelsEquiv T chosen factor U P candidates i hi j b).toAdd =
      local0Equiv T chosen factor (U j) P hi.2.1 b.toAdd := rfl

end AAT.AG.RelativeRepairComposition.Subdivision.GeneratedInterfaces

namespace AAT.AG.RelativeRepairComposition.Subdivision.GeneratedInterfaces
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
universe uk uG uI uE uB uD vE vB vD
variable {k : Type uk} [Field k]
variable {K : FiniteTransportPresentation.{uG}}
variable {E : Type uE} {B : Type uB} {D : Type uD}
variable [Category.{vE} E] [Category.{vB} B] [Category.{vD} D]
variable {p : E ⥤ B} {q : B ⥤ D}
variable (T : OriginalTowerPresentation K p q) (chosen : EdgeName (K := K))
variable (factor : Factorization T chosen)
variable [∀ v, Module k (T.toTower.localCoefficients.A v)]
attribute [local instance] LinearCoefficients.coefficientModules
variable (bases : FiniteFamily.Bases (k := k) T.toTower.localCoefficients.A)
variable {I : Type uI} [Fintype I] [DecidableEq I]
variable (U : I → ClosedRegion K) (P : ClosedRegion K)
variable [∀ j, DecidablePred (· ∈ (U j).edges)] [DecidablePred (· ∈ P.edges)]
variable (candidates : Set (EdgeName (K := K))) [DecidablePred (· ∈ candidates)]
variable (i : I) (hi : chosen ∈ ClosedRegion.privateAlwaysEdges U P candidates i) (j : I)
variable (hlinear : ∀ {s t : K.Vertex} (e : K.Edge s t) (a : k)
  (x : T.toTower.localCoefficients.A s),
  T.toTower.localCoefficients.edge e (a • x) = a • T.toTower.localCoefficients.edge e x)

local notation "Mo" => (T.toTower.localCoefficients)
local notation "Mn" => (TowerPresentation.localCoefficients (OriginalTowerPresentation.toTower (originalTower T chosen factor)))
local notation "Bn" => FiniteBases.expandedBases T chosen factor bases
local notation "Un" => expandedRegion K chosen (U j)
local notation "Pn" => expandedRegion K chosen P
local notation "Io" => ClosedRegion.privateAlwaysEdges U P candidates j
local notation "In" => ClosedRegion.privateAlwaysEdges (fun l => expandedRegion K chosen (U l))
  Pn (oldEdgeSet K chosen candidates) j
local notation "Xo" => (FiniteNative.XIndex Mo bases (U j) P Io → k)
local notation "Zo" => (FiniteNative.ZIndex Mo bases (U j) P Io → k)
local notation "Xn" => (FiniteNative.XIndex Mn Bn Un Pn In → k)
local notation "Zn" => (FiniteNative.ZIndex Mn Bn Un Pn In → k)
local notation "R" => localSupplement T chosen factor (U j)


variable [Fintype k] [DecidableEq k]
variable [Fintype (EdgeName (K := K))] [DecidableEq (EdgeName (K := K))]
variable [Fintype K.TwoCell] [DecidableEq K.TwoCell]
variable [∀ l, DecidablePred (· ∈ (U l).vertices)] [∀ l, DecidablePred (· ∈ (U l).faces)]
variable [DecidablePred (· ∈ P.faces)]
variable (enumK : FiniteElimination.Enumeration k)
variable (enumEdges : FiniteElimination.Enumeration (EdgeName (K := K)))
variable (enumFaces : FiniteElimination.Enumeration K.TwoCell)

/-- Independent new interfaces retain the native action of every full original new label. -/
noncomputable instance newGeneratedAddAction (value : RelativeCover.C2 Mo (U j) P) :
    AddAction (RelativeCover.C0 Mn Un Pn) (GeneratedRelations.newGeneratedObjects T chosen factor bases U P candidates i hi j hlinear enumK enumEdges enumFaces (value := value)) := by
  letI := GeneratedPublicReadings.retainedCandidatesDecidable chosen U P candidates i hi
  letI : ∀ l, DecidablePred (· ∈ (expandedRegion K chosen (U l)).edges) :=
    fun l => FiniteIncidence.expandedEdgesDecidable K chosen (U l)
  letI : DecidablePred (· ∈ (Pn).edges) := FiniteIncidence.expandedEdgesDecidable K chosen P
  letI : DecidablePred (· ∈ (Un).vertices) := FiniteIncidence.expandedVerticesDecidable K chosen (U j)
  letI : DecidablePred (· ∈ (Un).faces) := FiniteIncidence.expandedFacesDecidable K chosen (U j)
  letI : Fintype (EdgeName (K := presentation K chosen)) := FiniteEnumerations.edgeFintype K chosen enumEdges
  letI : Fintype (presentation K chosen).TwoCell := inferInstanceAs (Fintype K.TwoCell)
  letI : DecidableEq (presentation K chosen).TwoCell := inferInstanceAs (DecidableEq K.TwoCell)
  exact inferInstanceAs (AddAction (RelativeCover.C0 Mn Un Pn)
    (FiniteNative.GeneratedRelativeObjects Mn Bn Un Pn In
      (LinearCoefficients.edge_linear T chosen factor hlinear)
      ((local2Equiv T chosen factor (U j) P).symm value) enumK
      (FiniteEnumerations.edgeEnumeration K chosen enumEdges) enumFaces))

omit [Fintype (EdgeName (K := K))] in
/-- Independent new extraction commutes with every full original native label. -/
theorem new_generated_equivariant (value : RelativeCover.C2 Mo (U j) P)
    (b : Multiplicative (RelativeCover.C0 Mn Un Pn))
    (h : FiniteNative.RelativeEquation Mn Un Pn ((local2Equiv T chosen factor (U j) P).symm value)) :
    (GeneratedRelations.newGeneratedEquiv T chosen factor bases U P candidates i hi j hlinear enumK enumEdges enumFaces (value := value)) (b • h) = b • (GeneratedRelations.newGeneratedEquiv T chosen factor bases U P candidates i hi j hlinear enumK enumEdges enumFaces (value := value)) h := by
  letI := GeneratedPublicReadings.retainedCandidatesDecidable chosen U P candidates i hi
  letI : ∀ l, DecidablePred (· ∈ (expandedRegion K chosen (U l)).edges) :=
    fun l => FiniteIncidence.expandedEdgesDecidable K chosen (U l)
  letI : DecidablePred (· ∈ (Pn).edges) := FiniteIncidence.expandedEdgesDecidable K chosen P
  letI : DecidablePred (· ∈ (Un).vertices) := FiniteIncidence.expandedVerticesDecidable K chosen (U j)
  letI : DecidablePred (· ∈ (Un).faces) := FiniteIncidence.expandedFacesDecidable K chosen (U j)
  letI : Fintype (EdgeName (K := presentation K chosen)) := FiniteEnumerations.edgeFintype K chosen enumEdges
  letI : Fintype (presentation K chosen).TwoCell := inferInstanceAs (Fintype K.TwoCell)
  letI : DecidableEq (presentation K chosen).TwoCell := inferInstanceAs (DecidableEq K.TwoCell)
  exact FiniteNative.generated_relative_equivariant Mn Bn Un Pn In
    (LinearCoefficients.edge_linear T chosen factor hlinear)
    ((local2Equiv T chosen factor (U j) P).symm value) enumK
    (FiniteEnumerations.edgeEnumeration K chosen enumEdges) enumFaces b h

/-- Complete independent generated objects have both inverse maps and the entire supplement. -/
noncomputable def objectsEquiv (value : RelativeCover.C2 Mo (U j) P) :
    (GeneratedRelations.newGeneratedObjects T chosen factor bases U P candidates i hi j hlinear enumK enumEdges enumFaces (value := value)) ≃ ((FiniteNative.GeneratedRelativeObjects Mo bases (U j) P Io hlinear value enumK enumEdges enumFaces) × R) :=
  (GeneratedRelations.newGeneratedEquiv T chosen factor bases U P candidates i hi j hlinear enumK enumEdges enumFaces (value := value)).symm.trans
    ((localEquationEquiv T chosen factor (U j) P hi.2.1 value).trans
      (Equiv.prodCongr (FiniteNative.generatedRelativeEquiv Mo bases (U j) P Io hlinear value enumK enumEdges enumFaces) (Equiv.refl R)))

/-- The full object comparison uses actual restoration and complete old coordinate extraction. -/
theorem objectsEquiv_value (value : RelativeCover.C2 Mo (U j) P) (y : GeneratedRelations.newGeneratedObjects T chosen factor bases U P candidates i hi j hlinear enumK enumEdges enumFaces (value := value)) :
    objectsEquiv T chosen factor bases U P candidates i hi j hlinear enumK enumEdges enumFaces (value := value) y =
    ((FiniteNative.generatedRelativeEquiv Mo bases (U j) P Io hlinear value enumK enumEdges enumFaces)
      (localEquationEquiv T chosen factor (U j) P hi.2.1 value ((GeneratedRelations.newGeneratedEquiv T chosen factor bases U P candidates i hi j hlinear enumK enumEdges enumFaces (value := value)).symm y)).1,
      (localEquationEquiv T chosen factor (U j) P hi.2.1 value ((GeneratedRelations.newGeneratedEquiv T chosen factor bases U P candidates i hi j hlinear enumK enumEdges enumFaces (value := value)).symm y)).2) := rfl

/-- Restoring both independently generated objects recovers the same full old correction and supplement. -/
theorem objectsEquiv_coordinates (value : RelativeCover.C2 Mo (U j) P) (y : GeneratedRelations.newGeneratedObjects T chosen factor bases U P candidates i hi j hlinear enumK enumEdges enumFaces (value := value)) :
    (((FiniteNative.generatedRelativeEquiv Mo bases (U j) P Io hlinear value enumK enumEdges enumFaces).symm (objectsEquiv T chosen factor bases U P candidates i hi j hlinear enumK enumEdges enumFaces (value := value) y).1).1,(objectsEquiv T chosen factor bases U P candidates i hi j hlinear enumK enumEdges enumFaces (value := value) y).2) =
      local1Equiv T chosen factor (U j) P hi.2.1 ((GeneratedRelations.newGeneratedEquiv T chosen factor bases U P candidates i hi j hlinear enumK enumEdges enumFaces (value := value)).symm y).1 := by
  rw [objectsEquiv_value,Equiv.symm_apply_apply]
  exact localEquationEquiv_coordinates T chosen factor (U j) P hi.2.1 value _

/-- Every old generated object and every supplemental value restore through the full actual inverse. -/
theorem objectsEquiv_inverse_coordinates (value : RelativeCover.C2 Mo (U j) P)
    (y : FiniteNative.GeneratedRelativeObjects Mo bases (U j) P Io hlinear value enumK enumEdges enumFaces) (r : R) :
    local1Equiv T chosen factor (U j) P hi.2.1
      ((GeneratedRelations.newGeneratedEquiv T chosen factor bases U P candidates i hi j hlinear enumK enumEdges enumFaces (value := value)).symm ((objectsEquiv T chosen factor bases U P candidates i hi j hlinear enumK enumEdges enumFaces (value := value)).symm (y,r))).1 = (((FiniteNative.generatedRelativeEquiv Mo bases (U j) P Io hlinear value enumK enumEdges enumFaces).symm y).1,r) := by
  have h := objectsEquiv_coordinates T chosen factor bases U P candidates i hi j hlinear enumK enumEdges enumFaces
    (value := value) ((objectsEquiv T chosen factor bases U P candidates i hi j hlinear enumK enumEdges enumFaces (value := value)).symm (y,r))
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

set_option maxHeartbeats 1000000 in
/-- The full generated object comparison commutes with every old label and fresh displacement. -/
theorem objects_equivariant (value : RelativeCover.C2 Mo (U j) P)
    (b : Multiplicative (RelativeCover.C0 Mn Un Pn)) (y : GeneratedRelations.newGeneratedObjects T chosen factor bases U P candidates i hi j hlinear enumK enumEdges enumFaces (value := value)) :
    objectsEquiv T chosen factor bases U P candidates i hi j hlinear enumK enumEdges enumFaces (value := value) (b • y) = labelsEquiv T chosen factor U P candidates i hi j b • objectsEquiv T chosen factor bases U P candidates i hi j hlinear enumK enumEdges enumFaces (value := value) y := by
  have hn := inverse_equivariant (GeneratedRelations.newGeneratedEquiv T chosen factor bases U P candidates i hi j hlinear enumK enumEdges enumFaces (value := value))
    (new_generated_equivariant T chosen factor bases U P candidates i hi j hlinear enumK enumEdges enumFaces
      (value := value)) b y
  rw [objectsEquiv_value,objectsEquiv_value,hn,SupplementalAction.product_action_value,labelsEquiv_value]
  have hc := local_label_action T chosen factor (U j) P hi.2.1 ((GeneratedRelations.newGeneratedEquiv T chosen factor bases U P candidates i hi j hlinear enumK enumEdges enumFaces (value := value)).symm y).1 b.toAdd
  apply Prod.ext
  · rw [← FiniteNative.generated_relative_equivariant]
    apply congrArg (FiniteNative.generatedRelativeEquiv Mo bases (U j) P Io hlinear value enumK enumEdges enumFaces)
    apply Subtype.ext
    change (local1Equiv T chosen factor (U j) P hi.2.1
      (((GeneratedRelations.newGeneratedEquiv T chosen factor bases U P candidates i hi j hlinear enumK enumEdges enumFaces (value := value)).symm y).1 + RelativeCover.d0 Mn Un Pn b.toAdd)).1 =
      (local1Equiv T chosen factor (U j) P hi.2.1 ((GeneratedRelations.newGeneratedEquiv T chosen factor bases U P candidates i hi j hlinear enumK enumEdges enumFaces (value := value)).symm y).1).1 +
        RelativeCover.d0 Mo (U j) P (local0Equiv T chosen factor (U j) P hi.2.1 b.toAdd).1
    exact congrArg Prod.fst hc
  · change (local1Equiv T chosen factor (U j) P hi.2.1
      (((GeneratedRelations.newGeneratedEquiv T chosen factor bases U P candidates i hi j hlinear enumK enumEdges enumFaces (value := value)).symm y).1 + RelativeCover.d0 Mn Un Pn b.toAdd)).2 =
      (local1Equiv T chosen factor (U j) P hi.2.1 ((GeneratedRelations.newGeneratedEquiv T chosen factor bases U P candidates i hi j hlinear enumK enumEdges enumFaces (value := value)).symm y).1).2 +
        (local0Equiv T chosen factor (U j) P hi.2.1 b.toAdd).2
    exact congrArg Prod.snd hc

/-- The native independent interface groupoids retain all original and supplemental label arrows. -/
noncomputable def groupoidEquivalence (value : RelativeCover.C2 Mo (U j) P) :
    ActionCategory (Multiplicative (RelativeCover.C0 Mn Un Pn)) (GeneratedRelations.newGeneratedObjects T chosen factor bases U P candidates i hi j hlinear enumK enumEdges enumFaces (value := value)) ≌
    ActionCategory (Multiplicative (RelativeCover.C0 Mo (U j) P × R)) ((FiniteNative.GeneratedRelativeObjects Mo bases (U j) P Io hlinear value enumK enumEdges enumFaces) × R) :=
  changedLabelEquivalence (labelsEquiv T chosen factor U P candidates i hi j) (objectsEquiv T chosen factor bases U P candidates i hi j hlinear enumK enumEdges enumFaces (value := value))
    (objects_equivariant T chosen factor bases U P candidates i hi j hlinear enumK enumEdges enumFaces (value := value))

/-- Each full native arrow maps by the complete actual old-label and displacement comparison. -/
theorem groupoid_functor_label (value : RelativeCover.C2 Mo (U j) P)
    {x y : ActionCategory (Multiplicative (RelativeCover.C0 Mn Un Pn)) (GeneratedRelations.newGeneratedObjects T chosen factor bases U P candidates i hi j hlinear enumK enumEdges enumFaces (value := value))} (f : x ⟶ y) :
    ((groupoidEquivalence T chosen factor bases U P candidates i hi j hlinear enumK enumEdges enumFaces (value := value)).functor.map f).1 =
      labelsEquiv T chosen factor U P candidates i hi j f.1 := rfl

/-- Inverse native arrows restore every full new label through the complete inverse comparison. -/
theorem groupoid_inverse_label (value : RelativeCover.C2 Mo (U j) P)
    {x y : ActionCategory (Multiplicative (RelativeCover.C0 Mo (U j) P × R)) ((FiniteNative.GeneratedRelativeObjects Mo bases (U j) P Io hlinear value enumK enumEdges enumFaces) × R)} (f : x ⟶ y) :
    ((groupoidEquivalence T chosen factor bases U P candidates i hi j hlinear enumK enumEdges enumFaces (value := value)).inverse.map f).1 =
      (labelsEquiv T chosen factor U P candidates i hi j).symm f.1 := rfl

/-- Every full public basis value survives comparison between the two independently generated objects. -/
theorem objectsEquiv_public (value : RelativeCover.C2 Mo (U j) P) (y : GeneratedRelations.newGeneratedObjects T chosen factor bases U P candidates i hi j hlinear enumK enumEdges enumFaces (value := value)) :
    GeneratedPublic.publicCoordinateEquiv T chosen factor bases U P candidates i hi j y.1.1 =
      (objectsEquiv T chosen factor bases U P candidates i hi j hlinear enumK enumEdges enumFaces (value := value) y).1.1.1 := by
  rw [objectsEquiv_value,FiniteNative.generatedRelativeEquiv_public]
  have ho := congrArg Prod.fst (localEquationEquiv_coordinates T chosen factor (U j) P hi.2.1 value ((GeneratedRelations.newGeneratedEquiv T chosen factor bases U P candidates i hi j hlinear enumK enumEdges enumFaces (value := value)).symm y))
  change (localEquationEquiv T chosen factor (U j) P hi.2.1 value ((GeneratedRelations.newGeneratedEquiv T chosen factor bases U P candidates i hi j hlinear enumK enumEdges enumFaces (value := value)).symm y)).1.1 =
    (local1Equiv T chosen factor (U j) P hi.2.1 ((GeneratedRelations.newGeneratedEquiv T chosen factor bases U P candidates i hi j hlinear enumK enumEdges enumFaces (value := value)).symm y).1).1 at ho
  rw [ho]
  have hc := GeneratedPublicReadings.public_reading_collapse T chosen factor bases U P candidates i hi j ((GeneratedRelations.newGeneratedEquiv T chosen factor bases U P candidates i hi j hlinear enumK enumEdges enumFaces (value := value)).symm y).1
  rw [← GeneratedPrivate.newSplit_public,GeneratedRelations.newGeneratedEquiv_inverse_public] at hc
  exact hc

/-- All old generated kernel choices and all supplements restore the same complete actual new correction. -/
theorem objectsEquiv_inverse_correction (value : RelativeCover.C2 Mo (U j) P)
    (y : FiniteNative.GeneratedRelativeObjects Mo bases (U j) P Io hlinear value enumK enumEdges enumFaces) (r : R) :
    ((GeneratedRelations.newGeneratedEquiv T chosen factor bases U P candidates i hi j hlinear enumK enumEdges enumFaces (value := value)).symm ((objectsEquiv T chosen factor bases U P candidates i hi j hlinear enumK enumEdges enumFaces (value := value)).symm (y,r))).1 =
      (local1Equiv T chosen factor (U j) P hi.2.1).symm (((FiniteNative.generatedRelativeEquiv Mo bases (U j) P Io hlinear value enumK enumEdges enumFaces).symm y).1,r) := by
  apply (local1Equiv T chosen factor (U j) P hi.2.1).injective
  rw [AddEquiv.apply_symm_apply]
  exact objectsEquiv_inverse_coordinates T chosen factor bases U P candidates i hi j hlinear enumK enumEdges enumFaces
    (value := value) y r

end AAT.AG.RelativeRepairComposition.Subdivision.GeneratedInterfaces
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.Subdivision.GeneratedInterfaces
