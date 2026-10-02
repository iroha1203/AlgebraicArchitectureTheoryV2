import ResearchLean.AG.RelativeRepairComposition.SubdivisionGeneratedStrictConditions
import ResearchLean.AG.RelativeRepairComposition.SubdivisionSupplementFamilies
import ResearchLean.AG.RelativeRepairComposition.SubdivisionLocalEquations
import ResearchLean.AG.RelativeRepairComposition.FiniteNativeArbitraryEquation

/-!
# All independent strict local equations and every factor restoration

## Implementation notes

New and old equations use their own actual differentials and literal strict
predicates. The full family comparison first uses every local equation inverse;
only afterwards are the incidence-forced supplemental zeros identified with
the owner's full actual kernel. Right-hand sides and forbidden sets are
arbitrary. Neither solution family is defined as the image of restoration.
-/
namespace AAT.AG.RelativeRepairComposition.Subdivision.StrictEquationObjects
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
universe uG uI uE uB uD vE vB vD
variable {K : FiniteTransportPresentation.{uG}} {I : Type uI}
variable {E : Type uE} {B : Type uB} {D : Type uD}
variable [Category.{vE} E] [Category.{vB} B] [Category.{vD} D]
variable {p : E ⥤ B} {q : B ⥤ D}
variable (T : OriginalTowerPresentation K p q) (chosen : EdgeName (K := K))
variable (factor : Factorization T chosen) (U : I → ClosedRegion K)
variable (P : ClosedRegion K) (candidates : Set (EdgeName (K := K)))
variable (owner : I) (hi : chosen ∈ ClosedRegion.privateAlwaysEdges U P candidates owner)
local notation "Mo" => (T.toTower.localCoefficients)
local notation "Mn" => (TowerPresentation.localCoefficients
  (OriginalTowerPresentation.toTower (originalTower T chosen factor)))
local notation "Un" => (fun j => expandedRegion K chosen (U j))
local notation "Pn" => expandedRegion K chosen P
variable (values : ∀ j, RelativeCover.C2 Mo (U j) P)

/-- Every original local equation, using its entire actual relative coefficient family. -/
abbrev OldFamily (values : ∀ j, RelativeCover.C2 Mo (U j) P) :=
  ∀ j, FiniteNative.RelativeEquation Mo (U j) P (values j)

/-- Every new local equation, using the independent actual subdivided differential. -/
abbrev NewFamily (values : ∀ j, RelativeCover.C2 Mo (U j) P) :=
  ∀ j, FiniteNative.RelativeEquation Mn (Un j) Pn
  ((local2Equiv T chosen factor (U j) P).symm (values j))

/-- The full independent equation families have all pointwise inverse maps. -/
noncomputable def familyEquiv (values : ∀ j, RelativeCover.C2 Mo (U j) P) : NewFamily T chosen factor U P values ≃
    OldFamily T U P values × SupplementFamilies.Family T chosen factor U where
  toFun h := (fun j => (localEquationEquiv T chosen factor (U j) P hi.2.1 (values j) (h j)).1,
    fun j => (localEquationEquiv T chosen factor (U j) P hi.2.1 (values j) (h j)).2)
  invFun h := fun j => (localEquationEquiv T chosen factor (U j) P hi.2.1 (values j)).symm (h.1 j,h.2 j)
  left_inv h := by
    funext j
    exact (localEquationEquiv T chosen factor (U j) P hi.2.1 (values j)).symm_apply_apply (h j)
  right_inv h := by
    apply Prod.ext
    · funext j
      exact congrArg Prod.fst ((localEquationEquiv T chosen factor (U j) P hi.2.1 (values j)).apply_symm_apply (h.1 j,h.2 j))
    · funext j
      exact congrArg Prod.snd ((localEquationEquiv T chosen factor (U j) P hi.2.1 (values j)).apply_symm_apply (h.1 j,h.2 j))

/-- All compared old corrections and supplements are exactly the actual local collapse coordinates. -/
theorem family_coordinates (values : ∀ j, RelativeCover.C2 Mo (U j) P) (h : NewFamily T chosen factor U P values) (j : I) :
    (((familyEquiv T chosen factor U P candidates owner hi values h).1 j).1,
      (familyEquiv T chosen factor U P candidates owner hi values h).2 j) =
    local1Equiv T chosen factor (U j) P hi.2.1 (h j).1 := rfl

variable (forbidden : Set (EdgeName (K := K))) (hf : chosen ∉ forbidden)

/-- Independent old strict objects retain all original local equation solutions. -/
def OldObjects (values : ∀ j, RelativeCover.C2 Mo (U j) P) (forbidden : Set (EdgeName (K := K))) := {h : OldFamily T U P values //
  GeneratedStrictConditions.Compatible Mo U P forbidden (fun j => (h j).1)}

/-- Independent new strict objects impose their own original forbidden and shared values. -/
def NewObjects (values : ∀ j, RelativeCover.C2 Mo (U j) P) (forbidden : Set (EdgeName (K := K))) := {h : NewFamily T chosen factor U P values //
  GeneratedStrictConditions.Compatible Mn Un Pn (oldEdgeSet K chosen forbidden) (fun j => (h j).1)}

include hf in
/-- Full local equation comparison preserves and reflects each independent strict predicate. -/
theorem family_compatibility (values : ∀ j, RelativeCover.C2 Mo (U j) P) (h : NewFamily T chosen factor U P values) :
    GeneratedStrictConditions.Compatible Mn Un Pn (oldEdgeSet K chosen forbidden) (fun j => (h j).1) ↔
      GeneratedStrictConditions.Compatible Mo U P forbidden
        (fun j => ((familyEquiv T chosen factor U P candidates owner hi values h).1 j).1) :=
  GeneratedStrictConditions.compatibility_iff T chosen factor U P candidates owner hi forbidden hf
    (fun j => (h j).1)

/-- Strict independent new equations retain every old strict equation and every local supplement. -/
noncomputable def strictFamilyEquiv (values : ∀ j, RelativeCover.C2 Mo (U j) P) : NewObjects T chosen factor U P values forbidden ≃
    OldObjects T U P values forbidden × SupplementFamilies.Family T chosen factor U where
  toFun h := (⟨(familyEquiv T chosen factor U P candidates owner hi values h.1).1,
    (family_compatibility T chosen factor U P candidates owner hi forbidden hf values h.1).mp h.2⟩,
    (familyEquiv T chosen factor U P candidates owner hi values h.1).2)
  invFun h := ⟨(familyEquiv T chosen factor U P candidates owner hi values).symm (h.1.1,h.2),by
    apply (family_compatibility T chosen factor U P candidates owner hi forbidden hf values _).mpr
    rw [Equiv.apply_symm_apply]
    exact h.1.2⟩
  left_inv h := Subtype.ext ((familyEquiv T chosen factor U P candidates owner hi values).symm_apply_apply h.1)
  right_inv h := by
    have he := (familyEquiv T chosen factor U P candidates owner hi values).apply_symm_apply (h.1.1,h.2)
    have hs : (familyEquiv T chosen factor U P candidates owner hi values
        ((familyEquiv T chosen factor U P candidates owner hi values).symm (h.1.1,h.2))).2 = h.2 :=
      congrArg Prod.snd he
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst he
    · exact hs

variable [DecidableEq I]

/-- All strict actual local equations are the old full strict objects and an arbitrary full fresh kernel value. -/
noncomputable def objectsEquiv (values : ∀ j, RelativeCover.C2 Mo (U j) P) : NewObjects T chosen factor U P values forbidden ≃
    OldObjects T U P values forbidden × Additive (Kernel p q factor.middle) :=
  (strictFamilyEquiv T chosen factor U P candidates owner hi forbidden hf values).trans
    (Equiv.prodCongr (Equiv.refl _) (SupplementFamilies.equivalence T chosen factor U P candidates owner hi).toEquiv)

/-- The full strict comparison keeps the complete actual old correction in every region. -/
theorem objectsEquiv_old_value (values : ∀ j, RelativeCover.C2 Mo (U j) P)
    (h : NewObjects T chosen factor U P values forbidden) (j : I) :
    (((objectsEquiv T chosen factor U P candidates owner hi forbidden hf values h).1.1 j).1) =
      (local1Equiv T chosen factor (U j) P hi.2.1 (h.1 j).1).1 := rfl

/-- The global supplemental value is exactly the owner's complete actual first-factor correction. -/
theorem objectsEquiv_fresh_value (values : ∀ j, RelativeCover.C2 Mo (U j) P)
    (h : NewObjects T chosen factor U P values forbidden) :
    (objectsEquiv T chosen factor U P candidates owner hi forbidden hf values h).2 =
      (local1Equiv T chosen factor (U owner) P hi.2.1 (h.1 owner).1).2.1 := rfl

/-- Arbitrary old strict solutions and arbitrary full fresh values restore every local correction. -/
theorem objectsEquiv_inverse_coordinates (values : ∀ j, RelativeCover.C2 Mo (U j) P)
    (h : OldObjects T U P values forbidden) (r : Additive (Kernel p q factor.middle)) (j : I) :
    local1Equiv T chosen factor (U j) P hi.2.1
      (((objectsEquiv T chosen factor U P candidates owner hi forbidden hf values).symm (h,r)).1 j).1 =
    ((h.1 j).1,SupplementFamilies.restore T chosen factor U P candidates owner hi r j) :=
  localEquationEquiv_inverse_coordinates T chosen factor (U j) P hi.2.1 (values j) (h.1 j)
    (SupplementFamilies.restore T chosen factor U P candidates owner hi r j)

/-- The complete actual inverse is the same local inverse at all original edges and both factors. -/
theorem objectsEquiv_inverse_correction (values : ∀ j, RelativeCover.C2 Mo (U j) P)
    (h : OldObjects T U P values forbidden) (r : Additive (Kernel p q factor.middle)) (j : I) :
    (((objectsEquiv T chosen factor U P candidates owner hi forbidden hf values).symm (h,r)).1 j).1 =
      (local1Equiv T chosen factor (U j) P hi.2.1).symm
        ((h.1 j).1,SupplementFamilies.restore T chosen factor U P candidates owner hi r j) := by
  apply (local1Equiv T chosen factor (U j) P hi.2.1).injective
  rw [AddEquiv.apply_symm_apply]
  exact objectsEquiv_inverse_coordinates T chosen factor U P candidates owner hi forbidden hf values h r j

/-- Every candidate permission range uses this same comparison and the same independent equations. -/
noncomputable def rangeObjectsEquiv (allowed : Set (EdgeName (K := K)))
    (values : ∀ j, RelativeCover.C2 Mo (U j) P) :
    NewObjects T chosen factor U P values (candidates \ allowed) ≃
      OldObjects T U P values (candidates \ allowed) × Additive (Kernel p q factor.middle) :=
  objectsEquiv T chosen factor U P candidates owner hi (candidates \ allowed)
    (fun h => hi.2.2.1 h.1) values

end AAT.AG.RelativeRepairComposition.Subdivision.StrictEquationObjects
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.Subdivision.StrictEquationObjects
