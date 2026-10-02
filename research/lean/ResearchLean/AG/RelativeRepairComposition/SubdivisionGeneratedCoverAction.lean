import ResearchLean.AG.RelativeRepairComposition.SubdivisionGeneratedStrictObjects
import ResearchLean.AG.RelativeRepairComposition.SubdivisionGeneratedCoverLabels
import ResearchLean.AG.RelativeRepairComposition.RelativeGeneratedStrictAction
import ResearchLean.AG.RelativeRepairComposition.SubdivisionPermissions

/-!
# Native strict generated actions retain every original label and fresh displacement

## Implementation notes

The new strict action is the full generated native action at every region.
Support and shared values are proved from the independent full actual equations
and full strict vertex labels. The comparison uses the same independently
generated local object and label coordinates in every component.
-/
namespace AAT.AG.RelativeRepairComposition.Subdivision.GeneratedCoverAction
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
noncomputable def freshComm : AddCommGroup (Aw) :=
  inferInstanceAs (AddCommGroup ((originalTower T chosen factor).toTower.localCoefficients.A (.inr ())))
attribute [local instance] freshComm


variable (allowed : Set (EdgeName (K := K)))
local notation "Ln" => StrictSupportedCover.Labels Mn Pn Un Cn (oldEdgeSet K chosen allowed)
local notation "Lo" => StrictSupportedCover.Labels Mo P U candidates allowed
local notation "N" values => GeneratedStrictObjects.NewObjects T chosen factor bases U P candidates owner hi hlinear ek ee ef values (candidates \ allowed)
local notation "O" values => GeneratedStrictObjects.OldObjects T bases U P candidates hlinear ek ee ef values (candidates \ allowed)
local notation "En" values => GeneratedStrictObjects.newExtraction T chosen factor bases U P candidates owner hi hlinear ek ee ef (candidates \ allowed) Set.diff_subset values

/-- Every complete new strict label acts on every independent actual new local equation. -/
noncomputable def actualGauge (values : ∀ j, RelativeCover.C2 Mo (U j) P) (b : Ln)
    (h : StrictEquationObjects.NewObjects T chosen factor U P values (candidates \ allowed)) :
    StrictEquationObjects.NewObjects T chosen factor U P values (candidates \ allowed) :=
  ⟨fun j => Multiplicative.ofAdd (b.1 j).1 • (h.1 j),by
    constructor
    · intro j e he
      have hm : e.1 ∈ Cn \ oldEdgeSet K chosen allowed := by
        rw [← old_set_diff]
        exact he
      change (h.1 j).1.1 e + (RelativeCover.d0 Mn (Un j) Pn (b.1 j).1).1 e = 0
      rw [h.2.1 j e he,(b.1 j).2 e hm,add_zero]
    · intro j l e hj hl hlj
      have hd := congrArg (RelativeCover.d0 Mn (ClosedRegion.inter (Un j) (Un l)) Pn)
        (StrictSupportedCover.label_overlap Mn Pn Un Cn (oldEdgeSet K chosen allowed) b j l)
      rw [← RelativeCover.r_d0,← RelativeCover.r_d0] at hd
      have hv := congrArg (fun c => c.1 ⟨e,⟨hj,hl⟩⟩) hd
      exact congrArg₂ (· + ·) (h.2.2 j l e hj hl hlj) hv⟩

/-- The independent generated new strict object space carries every native strict label action. -/
noncomputable def gauge (values : ∀ j, RelativeCover.C2 Mo (U j) P) (b : Ln) (y : N values) : N values :=
  (En values) (actualGauge T chosen factor U P candidates allowed values b ((En values).symm y))

omit [Fintype (EdgeName (K := K))] in
/-- Each component is exactly the full independently generated native local action. -/
theorem gauge_component (values : ∀ j, RelativeCover.C2 Mo (U j) P) (b : Ln) (y : N values) (j : I) :
    (gauge T chosen factor bases U P candidates owner hi hlinear ek ee ef allowed values b y).1 j =
      Multiplicative.ofAdd (b.1 j).1 • (y.1 j) := by
  change GeneratedRelations.newGeneratedEquiv T chosen factor bases U P candidates owner hi j hlinear ek ee ef
      (value := values j) (Multiplicative.ofAdd (b.1 j).1 •
        (GeneratedRelations.newGeneratedEquiv T chosen factor bases U P candidates owner hi j hlinear ek ee ef
          (value := values j)).symm (y.1 j)) = _
  rw [GeneratedInterfaces.new_generated_equivariant,Equiv.apply_symm_apply]

omit [Fintype (EdgeName (K := K))] in
/-- The zero full new strict label fixes the whole generated family. -/
theorem gauge_zero (values : ∀ j, RelativeCover.C2 Mo (U j) P) (y : N values) :
    gauge T chosen factor bases U P candidates owner hi hlinear ek ee ef allowed values 0 y = y := by
  apply Subtype.ext
  funext j
  rw [gauge_component]
  change (0 : RelativeCover.C0 Mn (Un j) Pn) +ᵥ (y.1 j) = y.1 j
  exact zero_vadd _ _

omit [Fintype (EdgeName (K := K))] in
/-- Every full strict label sum composes its native action on the entire generated family. -/
theorem gauge_add (values : ∀ j, RelativeCover.C2 Mo (U j) P) (b c : Ln) (y : N values) :
    gauge T chosen factor bases U P candidates owner hi hlinear ek ee ef allowed values (b+c) y =
      gauge T chosen factor bases U P candidates owner hi hlinear ek ee ef allowed values b
        (gauge T chosen factor bases U P candidates owner hi hlinear ek ee ef allowed values c y) := by
  apply Subtype.ext
  funext j
  rw [gauge_component,gauge_component,gauge_component]
  change ((b.1 j).1 + (c.1 j).1) +ᵥ (y.1 j) = (b.1 j).1 +ᵥ ((c.1 j).1 +ᵥ (y.1 j))
  exact add_vadd _ _ _

/-- Every full new strict vertex label remains an original native groupoid label. -/
noncomputable instance addAction (values : ∀ j, RelativeCover.C2 Mo (U j) P) : AddAction Ln (N values) where
  vadd := gauge T chosen factor bases U P candidates owner hi hlinear ek ee ef allowed values
  zero_vadd := gauge_zero T chosen factor bases U P candidates owner hi hlinear ek ee ef allowed values
  add_vadd := gauge_add T chosen factor bases U P candidates owner hi hlinear ek ee ef allowed values

omit [Fintype (EdgeName (K := K))] in
/-- The full new native action retains the original complete local label at every region. -/
theorem action_component (values : ∀ j, RelativeCover.C2 Mo (U j) P)
    (b : Multiplicative Ln) (y : N values) (j : I) :
    (b • y).1 j = Multiplicative.ofAdd (b.toAdd.1 j).1 • (y.1 j) :=
  gauge_component T chosen factor bases U P candidates owner hi hlinear ek ee ef allowed values b.toAdd y j

/-- The full independent strict comparison commutes with every old label and actual fresh displacement. -/
theorem objects_equivariant (values : ∀ j, RelativeCover.C2 Mo (U j) P)
    (b : Multiplicative Ln) (y : N values) :
    GeneratedStrictObjects.rangeObjectsEquiv T chosen factor bases U P candidates owner hi hlinear ek ee ef allowed values (b • y) =
      (GeneratedCoverLabels.equivalence T chosen factor U P candidates allowed owner hi).toMultiplicative b •
        GeneratedStrictObjects.rangeObjectsEquiv T chosen factor bases U P candidates owner hi hlinear ek ee ef allowed values y := by
  rw [SupplementalAction.product_action_value]
  have component (j : I) :
      (((GeneratedStrictObjects.rangeObjectsEquiv T chosen factor bases U P candidates owner hi hlinear ek ee ef allowed values (b • y)).1.1 j),
        SupplementFamilies.restore T chosen factor U P candidates owner hi
          (GeneratedStrictObjects.rangeObjectsEquiv T chosen factor bases U P candidates owner hi hlinear ek ee ef allowed values (b • y)).2 j) =
      (Multiplicative.ofAdd (((GeneratedCoverLabels.equivalence T chosen factor U P candidates allowed owner hi b.toAdd).1.1 j).1) •
          ((GeneratedStrictObjects.rangeObjectsEquiv T chosen factor bases U P candidates owner hi hlinear ek ee ef allowed values y).1.1 j),
        SupplementFamilies.restore T chosen factor U P candidates owner hi
          (GeneratedStrictObjects.rangeObjectsEquiv T chosen factor bases U P candidates owner hi hlinear ek ee ef allowed values y).2 j +
        SupplementFamilies.restore T chosen factor U P candidates owner hi
          (GeneratedCoverLabels.equivalence T chosen factor U P candidates allowed owner hi b.toAdd).2 j) := by
    have hg := GeneratedStrictObjects.objectsEquiv_component T chosen factor bases U P candidates owner hi hlinear ek ee ef
      (candidates \ allowed) Set.diff_subset values (b • y) j
    have hy := GeneratedStrictObjects.objectsEquiv_component T chosen factor bases U P candidates owner hi hlinear ek ee ef
      (candidates \ allowed) Set.diff_subset values y j
    have hb := GeneratedCoverLabels.equivalence_component T chosen factor U P candidates allowed owner hi b.toAdd j
    rw [action_component] at hg
    have hp := GeneratedInterfaces.objects_equivariant T chosen factor bases U P candidates owner hi j hlinear ek ee ef
      (value := values j) (Multiplicative.ofAdd (b.toAdd.1 j).1) (y.1 j)
    change GeneratedInterfaces.objectsEquiv T chosen factor bases U P candidates owner hi j hlinear ek ee ef
        (value := values j) (Multiplicative.ofAdd (b.toAdd.1 j).1 • (y.1 j)) =
      (Multiplicative.ofAdd (local0Equiv T chosen factor (U j) P hi.2.1 (b.toAdd.1 j).1).1 •
          (GeneratedInterfaces.objectsEquiv T chosen factor bases U P candidates owner hi j hlinear ek ee ef (value := values j) (y.1 j)).1,
        (GeneratedInterfaces.objectsEquiv T chosen factor bases U P candidates owner hi j hlinear ek ee ef (value := values j) (y.1 j)).2 +
          (local0Equiv T chosen factor (U j) P hi.2.1 (b.toAdd.1 j).1).2) at hp
    rw [← hb,← hy] at hp
    exact hg.trans hp
  apply Prod.ext
  · apply Subtype.ext
    funext j
    exact (congrArg Prod.fst (component j)).trans
      (RelativeGeneratedStrictAction.action_component Mo bases U P candidates hlinear ek ee ef allowed values
        (Multiplicative.ofAdd (GeneratedCoverLabels.equivalence T chosen factor U P candidates allowed owner hi b.toAdd).1)
        (GeneratedStrictObjects.rangeObjectsEquiv T chosen factor bases U P candidates owner hi hlinear ek ee ef allowed values y).1 j).symm
  · have he := congrArg (fun z => z.2.1) (component owner)
    change (SupplementFamilies.restore T chosen factor U P candidates owner hi
      (GeneratedStrictObjects.rangeObjectsEquiv T chosen factor bases U P candidates owner hi hlinear ek ee ef allowed values (b • y)).2 owner).1 =
      (SupplementFamilies.restore T chosen factor U P candidates owner hi
        (GeneratedStrictObjects.rangeObjectsEquiv T chosen factor bases U P candidates owner hi hlinear ek ee ef allowed values y).2 owner).1 +
      (SupplementFamilies.restore T chosen factor U P candidates owner hi
        (GeneratedCoverLabels.equivalence T chosen factor U P candidates allowed owner hi b.toAdd).2 owner).1 at he
    simpa only [SupplementFamilies.restore_owner] using he

/-- All native independent generated strict arrows compare through the complete old labels and fresh displacement. -/
noncomputable def equivalence (values : ∀ j, RelativeCover.C2 Mo (U j) P) :
    ActionCategory (Multiplicative Ln) (N values) ≌
      ActionCategory (Multiplicative (Lo × Aw)) ((O values) × Aw) :=
  changedLabelEquivalence (GeneratedCoverLabels.equivalence T chosen factor U P candidates allowed owner hi).toMultiplicative
    (GeneratedStrictObjects.rangeObjectsEquiv T chosen factor bases U P candidates owner hi hlinear ek ee ef allowed values)
    (objects_equivariant T chosen factor bases U P candidates owner hi hlinear ek ee ef allowed values)

/-- Every mapped native arrow retains all old original labels and its whole actual fresh displacement. -/
theorem functor_label (values : ∀ j, RelativeCover.C2 Mo (U j) P)
    {x y : ActionCategory (Multiplicative Ln) (N values)} (f : x ⟶ y) :
    ((equivalence T chosen factor bases U P candidates owner hi hlinear ek ee ef allowed values).functor.map f).1 =
      (GeneratedCoverLabels.equivalence T chosen factor U P candidates allowed owner hi).toMultiplicative f.1 := rfl

/-- Every inverse native arrow restores all original new labels through the full inverse comparison. -/
theorem inverse_label (values : ∀ j, RelativeCover.C2 Mo (U j) P)
    {x y : ActionCategory (Multiplicative (Lo × Aw)) ((O values) × Aw)} (f : x ⟶ y) :
    ((equivalence T chosen factor bases U P candidates owner hi hlinear ek ee ef allowed values).inverse.map f).1 =
      (GeneratedCoverLabels.equivalence T chosen factor U P candidates allowed owner hi).toMultiplicative.symm f.1 := rfl

end AAT.AG.RelativeRepairComposition.Subdivision.GeneratedCoverAction
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.Subdivision.GeneratedCoverAction
