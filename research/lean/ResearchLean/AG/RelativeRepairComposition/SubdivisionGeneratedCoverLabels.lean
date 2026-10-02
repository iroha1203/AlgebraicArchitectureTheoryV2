import ResearchLean.AG.RelativeRepairComposition.SubdivisionSupplementFamilies
import ResearchLean.AG.RelativeRepairComposition.SubdivisionLocalDifferentials
import ResearchLean.AG.RelativeRepairComposition.StrictSupportedCover

/-!
# Every strict local vertex label and the full fresh displacement

## Implementation notes

Both label groups independently retain the full relative vertex families,
forbidden-edge coboundaries and literal shared-vertex equality. Private owner
incidence excludes the fresh vertex from every overlap. The comparison keeps
all old labels and every actual fresh displacement, with full inverse maps.
-/
namespace AAT.AG.RelativeRepairComposition.Subdivision.GeneratedCoverLabels
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
universe uG uI uE uB uD vE vB vD
variable {K : FiniteTransportPresentation.{uG}} {I : Type uI} [DecidableEq I]
variable {E : Type uE} {B : Type uB} {D : Type uD}
variable [Category.{vE} E] [Category.{vB} B] [Category.{vD} D]
variable {p : E ⥤ B} {q : B ⥤ D}
variable (T : OriginalTowerPresentation K p q) (chosen : EdgeName (K := K))
variable (factor : Factorization T chosen) (U : I → ClosedRegion K) (P : ClosedRegion K)
variable (candidates allowed : Set (EdgeName (K := K)))
variable (owner : I) (hi : chosen ∈ ClosedRegion.privateAlwaysEdges U P candidates owner)
local notation "Mo" => T.toTower.localCoefficients
local notation "Mn" => (TowerPresentation.localCoefficients (OriginalTowerPresentation.toTower (originalTower T chosen factor)))
local notation "Un" => (fun j => expandedRegion K chosen (U j))
local notation "Pn" => expandedRegion K chosen P
local notation "Ln" => StrictSupportedCover.Labels Mn Pn Un (oldEdgeSet K chosen candidates) (oldEdgeSet K chosen allowed)
local notation "Lo" => StrictSupportedCover.Labels Mo P U candidates allowed
local notation "Aw" => Additive (Kernel p q factor.middle)

omit [DecidableEq I] in
/-- Every original forbidden edge is retained with the same strict zero requirement. -/
theorem forbidden_retained (e : EdgeName (K := K)) (he : e ∈ candidates \ allowed) :
    retainedEdgeName K chosen ⟨e,fun h => hi.2.2.1 (h ▸ he.1)⟩ ∈
      oldEdgeSet K chosen candidates \ oldEdgeSet K chosen allowed := by
  constructor
  · exact ⟨⟨e,fun h => hi.2.2.1 (h ▸ he.1)⟩,he.1,rfl⟩
  · rintro ⟨a,ha,hn⟩
    have hv := retained_injective K chosen hn
    apply he.2
    change a.1 ∈ allowed at ha
    have hva : a.1 = e := congrArg Subtype.val hv
    rw [← hva]
    exact ha

/-- All old local labels satisfy the original independent forbidden conditions. -/
noncomputable def oldLocal (b : Ln) (j : I) : SupportedEquation.Labels Mo P (U j) candidates allowed :=
  ⟨(local0Equiv T chosen factor (U j) P hi.2.1 (b.1 j).1).1,by
    intro e he
    have hn : e.1 ≠ chosen := fun h => hi.2.2.1 (h ▸ he.1)
    have hd := congrArg (fun z => z.1.1 e) (local_d0 T chosen factor (U j) P hi.2.1 (b.1 j).1)
    have hr := local1Equiv_retained T chosen factor (U j) P hi.2.1
      (RelativeCover.d0 Mn (Un j) Pn (b.1 j).1) e hn
    exact hd.symm.trans (hr.trans ((b.1 j).2
      ⟨retainedEdgeName K chosen ⟨e.1,hn⟩,e.2⟩
      (forbidden_retained chosen U P candidates allowed owner hi e.1 he)))⟩

/-- All full old labels, including stabilizers, are retained with literal strict vertex agreement. -/
noncomputable def collapse : Ln →+ Lo where
  toFun b := ⟨fun j => oldLocal T chosen factor U P candidates allowed owner hi b j,by
    intro j l v hj hl
    exact b.2 j l (.inl v) hj hl⟩
  map_zero' := by apply Subtype.ext; funext j; apply Subtype.ext; exact congrArg Prod.fst (map_zero (local0Equiv T chosen factor (U j) P hi.2.1))
  map_add' b c := by apply Subtype.ext; funext j; apply Subtype.ext; exact congrArg Prod.fst (map_add (local0Equiv T chosen factor (U j) P hi.2.1) (b.1 j).1 (c.1 j).1)

/-- Read all independent actual local fresh displacements before using owner incidence. -/
noncomputable def displacements : Ln →+ SupplementFamilies.Family T chosen factor U where
  toFun b := fun j => (local0Equiv T chosen factor (U j) P hi.2.1 (b.1 j).1).2
  map_zero' := by funext j; exact congrArg Prod.snd (map_zero (local0Equiv T chosen factor (U j) P hi.2.1))
  map_add' b c := by funext j; exact congrArg Prod.snd (map_add (local0Equiv T chosen factor (U j) P hi.2.1) (b.1 j).1 (c.1 j).1)

/-- Restore every full old strict label and every supplemental family as independent new strict labels. -/
noncomputable def expand (b : Lo) (r : SupplementFamilies.Family T chosen factor U) : Ln :=
  ⟨fun j => ⟨(local0Equiv T chosen factor (U j) P hi.2.1).symm ((b.1 j).1,r j),by
    rintro ⟨e,hu⟩ ⟨hc,ha⟩
    obtain ⟨a,hac,he⟩ := hc
    change retainedEdgeName K chosen a = e at he
    subst e
    have hnot : a.1 ∉ allowed := fun h => ha ⟨a,h,rfl⟩
    rw [RelativeCover.d0_value]
    let bn := (local0Equiv T chosen factor (U j) P hi.2.1).symm ((b.1 j).1,r j)
    change bn.1 ⟨.inl a.1.2.1,((U j).edge_closed _ hu).2⟩ -
      (Mn).edge (oldEdge K chosen a.1 a.2) (bn.1 ⟨.inl a.1.1,((U j).edge_closed _ hu).1⟩) = 0
    rw [coefficient_edge_old]
    change (b.1 j).1.1 ⟨a.1.2.1,((U j).edge_closed _ hu).2⟩ -
      (Mo).edge a.1.2.2 ((b.1 j).1.1 ⟨a.1.1,((U j).edge_closed _ hu).1⟩) = 0
    simpa only [RelativeCover.d0_value] using (b.1 j).2 ⟨a.1,hu⟩ ⟨hac,hnot⟩⟩,by
    intro j l v hj hl
    cases v with
    | inl v => exact b.2 j l v hj hl
    | inr v =>
      cases v
      have hjOwner : j = owner := by
        by_contra hn
        exact chosen_outside_other K chosen U P candidates owner j hi hn hj
      have hlOwner : l = owner := by
        by_contra hn
        exact chosen_outside_other K chosen U P candidates owner l hi hn hl
      subst j
      subst l
      rfl⟩

/-- All strict labels compare with every old strict label and the complete actual owner displacement. -/
noncomputable def equivalence : Ln ≃+ (Lo × Aw) where
  toFun b := (collapse T chosen factor U P candidates allowed owner hi b,
    SupplementFamilies.equivalence T chosen factor U P candidates owner hi
      (displacements T chosen factor U P candidates allowed owner hi b))
  invFun b := expand T chosen factor U P candidates allowed owner hi b.1
    ((SupplementFamilies.equivalence T chosen factor U P candidates owner hi).symm b.2)
  left_inv b := by
    apply Subtype.ext
    funext j
    apply Subtype.ext
    apply (local0Equiv T chosen factor (U j) P hi.2.1).injective
    change local0Equiv T chosen factor (U j) P hi.2.1
      ((local0Equiv T chosen factor (U j) P hi.2.1).symm
        ((collapse T chosen factor U P candidates allowed owner hi b).1 j |>.1,
          (SupplementFamilies.equivalence T chosen factor U P candidates owner hi).symm
            (SupplementFamilies.equivalence T chosen factor U P candidates owner hi
              (displacements T chosen factor U P candidates allowed owner hi b)) j)) = _
    rw [AddEquiv.apply_symm_apply,AddEquiv.symm_apply_apply]
    rfl
  right_inv b := by
    apply Prod.ext
    · apply Subtype.ext
      funext j
      apply Subtype.ext
      exact congrArg Prod.fst ((local0Equiv T chosen factor (U j) P hi.2.1).apply_symm_apply
        ((b.1.1 j).1,(SupplementFamilies.equivalence T chosen factor U P candidates owner hi).symm b.2 j))
    · change (local0Equiv T chosen factor (U owner) P hi.2.1
        ((local0Equiv T chosen factor (U owner) P hi.2.1).symm
          ((b.1.1 owner).1,(SupplementFamilies.equivalence T chosen factor U P candidates owner hi).symm b.2 owner))).2.1 = b.2
      rw [AddEquiv.apply_symm_apply]
      exact SupplementFamilies.restore_owner T chosen factor U P candidates owner hi b.2
  map_add' b c := by
    apply Prod.ext
    · exact map_add (collapse T chosen factor U P candidates allowed owner hi) b c
    · exact map_add ((SupplementFamilies.equivalence T chosen factor U P candidates owner hi).toAddMonoidHom.comp
        (displacements T chosen factor U P candidates allowed owner hi)) b c

/-- Every local old label and every local displacement agree with the complete independent local comparison. -/
theorem equivalence_component (b : Ln) (j : I) :
    (((equivalence T chosen factor U P candidates allowed owner hi b).1.1 j).1,
      SupplementFamilies.restore T chosen factor U P candidates owner hi
        (equivalence T chosen factor U P candidates allowed owner hi b).2 j) =
      local0Equiv T chosen factor (U j) P hi.2.1 (b.1 j).1 := by
  apply Prod.ext
  · rfl
  · exact congrFun (SupplementFamilies.restore_read T chosen factor U P candidates owner hi
      (displacements T chosen factor U P candidates allowed owner hi b)) j

end AAT.AG.RelativeRepairComposition.Subdivision.GeneratedCoverLabels
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.Subdivision.GeneratedCoverLabels
