import ResearchLean.AG.RelativeRepairComposition.RelativeGeneratedStrictCover
import ResearchLean.AG.RelativeRepairComposition.SubdivisionStrictEquationObjects
import ResearchLean.AG.RelativeRepairComposition.SubdivisionGeneratedInterfaces

/-!
# Independent generated strict objects and all actual subdivision coordinates

## Implementation notes

Both sides apply the finite generator to their own full local differential and
then impose their own public support and shared-value conditions. Full actual
restoration connects them. Every old private kernel and every actual fresh
value remains, and the comparison agrees componentwise with the independent
local comparison.
-/
namespace AAT.AG.RelativeRepairComposition.Subdivision.GeneratedStrictObjects
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

/-- Independent original strict generated objects, with every local private kernel. -/
abbrev OldObjects (values : ∀ j, RelativeCover.C2 Mo (U j) P)
    (forbidden : Set (EdgeName (K := K))) :=
  RelativeGeneratedStrictCover.Objects Mo bases U P candidates hlinear ek ee ef values forbidden

/-- Independently generated new strict objects from the new full local differential. -/
noncomputable def NewObjects (values : ∀ j, RelativeCover.C2 Mo (U j) P)
    (forbidden : Set (EdgeName (K := K))) : Type (max uk uG uI) := by
  letI := GeneratedPublicReadings.retainedCandidatesDecidable chosen U P candidates owner hi
  letI : ∀ j, DecidablePred (· ∈ (Un j).vertices) := fun j => FiniteIncidence.expandedVerticesDecidable K chosen (U j)
  letI : ∀ j, DecidablePred (· ∈ (Un j).edges) := fun j => FiniteIncidence.expandedEdgesDecidable K chosen (U j)
  letI : ∀ j, DecidablePred (· ∈ (Un j).faces) := fun j => FiniteIncidence.expandedFacesDecidable K chosen (U j)
  letI : DecidablePred (· ∈ (Pn).edges) := FiniteIncidence.expandedEdgesDecidable K chosen P
  letI : DecidablePred (· ∈ (Pn).faces) := FiniteIncidence.expandedFacesDecidable K chosen P
  letI : Fintype (EdgeName (K := presentation K chosen)) := FiniteEnumerations.edgeFintype K chosen ee
  letI : Fintype (presentation K chosen).TwoCell := inferInstanceAs (Fintype K.TwoCell)
  letI : DecidableEq (presentation K chosen).TwoCell := inferInstanceAs (DecidableEq K.TwoCell)
  exact { y : ∀ j, GeneratedRelations.newGeneratedObjects T chosen factor bases U P candidates owner hi j
      hlinear ek ee ef (value := values j) //
    RelativeGeneratedStrictCover.PublicCompatible Mn Bn Un Pn Cn
      (LinearCoefficients.edge_linear T chosen factor hlinear) ek en ef
      (fun j => (local2Equiv T chosen factor (U j) P).symm (values j)) (oldEdgeSet K chosen forbidden) y }

variable (forbidden : Set (EdgeName (K := K))) (hf : forbidden ⊆ candidates)

/-- Actual new strict equations and independently generated new strict objects have full inverse maps. -/
noncomputable def newExtraction (values : ∀ j, RelativeCover.C2 Mo (U j) P) :
    StrictEquationObjects.NewObjects T chosen factor U P values forbidden ≃
      NewObjects T chosen factor bases U P candidates owner hi hlinear ek ee ef values forbidden := by
  letI := GeneratedPublicReadings.retainedCandidatesDecidable chosen U P candidates owner hi
  letI : ∀ j, DecidablePred (· ∈ (Un j).vertices) := fun j => FiniteIncidence.expandedVerticesDecidable K chosen (U j)
  letI : ∀ j, DecidablePred (· ∈ (Un j).edges) := fun j => FiniteIncidence.expandedEdgesDecidable K chosen (U j)
  letI : ∀ j, DecidablePred (· ∈ (Un j).faces) := fun j => FiniteIncidence.expandedFacesDecidable K chosen (U j)
  letI : DecidablePred (· ∈ (Pn).edges) := FiniteIncidence.expandedEdgesDecidable K chosen P
  letI : DecidablePred (· ∈ (Pn).faces) := FiniteIncidence.expandedFacesDecidable K chosen P
  letI : Fintype (EdgeName (K := presentation K chosen)) := FiniteEnumerations.edgeFintype K chosen ee
  letI : Fintype (presentation K chosen).TwoCell := inferInstanceAs (Fintype K.TwoCell)
  letI : DecidableEq (presentation K chosen).TwoCell := inferInstanceAs (DecidableEq K.TwoCell)
  exact RelativeGeneratedStrictCover.objectEquiv Mn Bn Un Pn Cn
    (LinearCoefficients.edge_linear T chosen factor hlinear) ek en ef
    (oldEdgeSet K chosen forbidden) (by
      rintro e ⟨a,ha,he⟩
      exact ⟨a,hf ha,he⟩)
    (fun j => (local2Equiv T chosen factor (U j) P).symm (values j))

/-- Full new generated strict objects retain all original generated strict objects and all fresh values. -/
noncomputable def objectsEquiv (values : ∀ j, RelativeCover.C2 Mo (U j) P) :
    NewObjects T chosen factor bases U P candidates owner hi hlinear ek ee ef values forbidden ≃
      OldObjects T bases U P candidates hlinear ek ee ef values forbidden × Aw :=
  (newExtraction T chosen factor bases U P candidates owner hi hlinear ek ee ef forbidden hf values).symm.trans
    ((StrictEquationObjects.objectsEquiv T chosen factor U P candidates owner hi forbidden
      (fun h => hi.2.2.1 (hf h)) values).trans
      (Equiv.prodCongr
        (RelativeGeneratedStrictCover.objectEquiv Mo bases U P candidates hlinear ek ee ef forbidden hf values)
        (Equiv.refl Aw)))

omit [Fintype (EdgeName (K := K))] in
/-- Reading each new generated component uses exactly its independently computed local generator. -/
theorem newExtraction_component (values : ∀ j, RelativeCover.C2 Mo (U j) P)
    (h : StrictEquationObjects.NewObjects T chosen factor U P values forbidden) (j : I) :
    ((newExtraction T chosen factor bases U P candidates owner hi hlinear ek ee ef forbidden hf values h).1 j) =
      GeneratedRelations.newGeneratedEquiv T chosen factor bases U P candidates owner hi j hlinear ek ee ef
        (value := values j) (h.1 j) := rfl

omit [Fintype (EdgeName (K := K))] in
/-- Restoring any generated new component returns the entire original new local equation. -/
theorem newRestoration_component (values : ∀ j, RelativeCover.C2 Mo (U j) P)
    (y : NewObjects T chosen factor bases U P candidates owner hi hlinear ek ee ef values forbidden) (j : I) :
    (((newExtraction T chosen factor bases U P candidates owner hi hlinear ek ee ef forbidden hf values).symm y).1 j) =
      (GeneratedRelations.newGeneratedEquiv T chosen factor bases U P candidates owner hi j hlinear ek ee ef
        (value := values j)).symm (y.1 j) := rfl

/-- The full strict comparison agrees at every region with the independently generated local comparison. -/
theorem objectsEquiv_component (values : ∀ j, RelativeCover.C2 Mo (U j) P)
    (y : NewObjects T chosen factor bases U P candidates owner hi hlinear ek ee ef values forbidden) (j : I) :
    ((objectsEquiv T chosen factor bases U P candidates owner hi hlinear ek ee ef forbidden hf values y).1.1 j,
      SupplementFamilies.restore T chosen factor U P candidates owner hi
        (objectsEquiv T chosen factor bases U P candidates owner hi hlinear ek ee ef forbidden hf values y).2 j) =
      GeneratedInterfaces.objectsEquiv T chosen factor bases U P candidates owner hi j hlinear ek ee ef
        (value := values j) (y.1 j) := by
  apply Prod.ext
  · rfl
  · exact congrFun ((SupplementFamilies.equivalence T chosen factor U P candidates owner hi).symm_apply_apply
      (StrictEquationObjects.familyEquiv T chosen factor U P candidates owner hi values
        ((newExtraction T chosen factor bases U P candidates owner hi hlinear ek ee ef forbidden hf values).symm y).1).2) j

/-- Every public coordinate agrees with the actual independently generated local comparison. -/
theorem objectsEquiv_public (values : ∀ j, RelativeCover.C2 Mo (U j) P)
    (y : NewObjects T chosen factor bases U P candidates owner hi hlinear ek ee ef values forbidden) (j : I) :
    GeneratedPublic.publicCoordinateEquiv T chosen factor bases U P candidates owner hi j (y.1 j).1.1 =
      ((objectsEquiv T chosen factor bases U P candidates owner hi hlinear ek ee ef forbidden hf values y).1.1 j).1.1 := by
  have hc := congrArg (fun z => z.1.1.1)
    (objectsEquiv_component T chosen factor bases U P candidates owner hi hlinear ek ee ef forbidden hf values y j)
  exact (GeneratedInterfaces.objectsEquiv_public T chosen factor bases U P candidates owner hi j
    hlinear ek ee ef (value := values j) (y.1 j)).trans hc.symm

/-- Every old generated strict object and every actual fresh value restore all actual factor coordinates. -/
theorem objectsEquiv_inverse_correction (values : ∀ j, RelativeCover.C2 Mo (U j) P)
    (y : OldObjects T bases U P candidates hlinear ek ee ef values forbidden) (r : Aw) (j : I) :
    (((newExtraction T chosen factor bases U P candidates owner hi hlinear ek ee ef forbidden hf values).symm
      ((objectsEquiv T chosen factor bases U P candidates owner hi hlinear ek ee ef forbidden hf values).symm (y,r))).1 j).1 =
      (local1Equiv T chosen factor (U j) P hi.2.1).symm
        (((FiniteNative.generatedRelativeEquiv Mo bases (U j) P
          (ClosedRegion.privateAlwaysEdges U P candidates j) hlinear (values j) ek ee ef).symm (y.1 j)).1,
          SupplementFamilies.restore T chosen factor U P candidates owner hi r j) := by
  have he := (newExtraction T chosen factor bases U P candidates owner hi hlinear ek ee ef forbidden hf values).symm_apply_apply
    ((StrictEquationObjects.objectsEquiv T chosen factor U P candidates owner hi forbidden
      (fun h => hi.2.2.1 (hf h)) values).symm
      ((RelativeGeneratedStrictCover.objectEquiv Mo bases U P candidates hlinear ek ee ef forbidden hf values).symm y,r))
  change (((newExtraction T chosen factor bases U P candidates owner hi hlinear ek ee ef forbidden hf values).symm
    ((newExtraction T chosen factor bases U P candidates owner hi hlinear ek ee ef forbidden hf values)
      ((StrictEquationObjects.objectsEquiv T chosen factor U P candidates owner hi forbidden
        (fun h => hi.2.2.1 (hf h)) values).symm
        ((RelativeGeneratedStrictCover.objectEquiv Mo bases U P candidates hlinear ek ee ef forbidden hf values).symm y,r)))).1 j).1 = _
  rw [he]
  exact StrictEquationObjects.objectsEquiv_inverse_correction T chosen factor U P candidates owner hi forbidden
    (fun h => hi.2.2.1 (hf h)) values
    ((RelativeGeneratedStrictCover.objectEquiv Mo bases U P candidates hlinear ek ee ef forbidden hf values).symm y) r j

/-- Every permission range uses the same independent generators and the same full inverse comparison. -/
noncomputable def rangeObjectsEquiv (allowed : Set (EdgeName (K := K)))
    (values : ∀ j, RelativeCover.C2 Mo (U j) P) :
    NewObjects T chosen factor bases U P candidates owner hi hlinear ek ee ef values (candidates \ allowed) ≃
      OldObjects T bases U P candidates hlinear ek ee ef values (candidates \ allowed) × Aw :=
  objectsEquiv T chosen factor bases U P candidates owner hi hlinear ek ee ef (candidates \ allowed)
    (fun _ h => h.1) values

end AAT.AG.RelativeRepairComposition.Subdivision.GeneratedStrictObjects
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.Subdivision.GeneratedStrictObjects
