import ResearchLean.AG.RelativeRepairComposition.RelativeComplex

/-!
# Isomorphism classes and automorphisms of supported actual repairs

G-130 A / n1017 §2.2・2.5: the same supported cocycles act on the original
actual repair objects. Their differences descend to H1, giving a torsor when
repairs exist. Native action-groupoid automorphisms keep every vertex label and
are isomorphic to the original relative H0, independently of the allowed range.

## Implementation notes

The orbit quotient is taken only for isomorphism classes; the native groupoid
continues to retain all arrows. The quotient action is transported through an
actual base repair, following the G-129 classification construction; the formulas
on representatives establish its independence from that internal choice.
Quotienting vertex labels themselves would erase stabilizers, so automorphisms
are constructed from the original labels as native isomorphisms. The H0 comparison
uses those labels in both directions, including their inverse and composition.
-/

namespace AAT.AG.RelativeRepairComposition
open CategoryTheory TransportCoherence AbelianLiftingObstruction
universe uG uE uB uD vE vB vD
namespace ActualRelative
variable {K : FiniteTransportPresentation.{uG}}
variable {E : Type uE} {B : Type uB} {D : Type uD}
variable [Category.{vE} E] [Category.{vB} B] [Category.{vD} D]
variable {p : E ⥤ B} {q : B ⥤ D}
variable (T : OriginalTowerPresentation K p q) (P : ClosedRegion K)
variable (candidates allowed : Set (EdgeName (K := K)))
local notation "M" => T.toTower.localCoefficients
local notation "F" => fixedEdgesForRange P.edges candidates allowed

/-- The original supported coordinate difference of two actual repairs is a cocycle. -/
noncomputable def repairDifference (Q R : SupportedRepair T F) :
    RelativeComplex.Z1 M P candidates allowed :=
  ⟨⟨(repairCoord T F Q).1.1 - (repairCoord T F R).1.1,
    (RelativeComplex.C1Group M P candidates allowed).sub_mem
      (repairCoord T F Q).1.2 (repairCoord T F R).1.2⟩, by
      apply Subtype.ext
      change (d1Hom M) (_ - _) = 0
      rw [map_sub, show (d1Hom M) (repairCoord T F Q).1.1 = -T.toTower.defect
        from (repairCoord T F Q).2,
        show (d1Hom M) (repairCoord T F R).1.1 = -T.toTower.defect
        from (repairCoord T F R).2, sub_self]⟩

/-- Add any supported cocycle and restore the same original actual edge choices. -/
noncomputable def repairCocycleAction (z : RelativeComplex.Z1 M P candidates allowed)
    (R : SupportedRepair T F) : SupportedRepair T F :=
  repairRec T F ⟨⟨z.1.1 + (repairCoord T F R).1.1,
    (RelativeComplex.C1Group M P candidates allowed).add_mem z.1.2 (repairCoord T F R).1.2⟩, by
      rw [d1_add, show d1 M z.1.1 = 0 from congrArg Subtype.val z.2,
        (repairCoord T F R).2, zero_add]⟩

/-- The cocycle action has exactly the indicated original coordinate sum. -/
theorem repairCocycleAction_coord (z : RelativeComplex.Z1 M P candidates allowed)
    (R : SupportedRepair T F) :
    (repairCoord T F (repairCocycleAction T P candidates allowed z R)).1.1 =
      z.1.1 + (repairCoord T F R).1.1 := by
  unfold repairCocycleAction
  rw [repairCoord_rec]

/-- Difference after cocycle action recovers the entire cocycle. -/
theorem repairDifference_action (z : RelativeComplex.Z1 M P candidates allowed)
    (R : SupportedRepair T F) :
    repairDifference T P candidates allowed (repairCocycleAction T P candidates allowed z R) R = z := by
  apply Subtype.ext; apply Subtype.ext
  change (repairCoord T F _).1.1 - (repairCoord T F R).1.1 = z.1.1
  rw [repairCocycleAction_coord, add_sub_cancel_right]

/-- Acting by the difference recovers the entire independent actual repair. -/
theorem repairCocycleAction_difference (Q R : SupportedRepair T F) :
    repairCocycleAction T P candidates allowed (repairDifference T P candidates allowed Q R) R = Q := by
  apply (repairEquiv T F).injective
  apply Subtype.ext; apply Subtype.ext
  change (repairCoord T F _).1.1 = (repairCoord T F Q).1.1
  rw [repairCocycleAction_coord]
  change ((repairCoord T F Q).1.1 - (repairCoord T F R).1.1) +
    (repairCoord T F R).1.1 = (repairCoord T F Q).1.1
  exact sub_add_cancel _ _

/-- The actual difference obeys the torsor subtraction identity. -/
theorem repairDifference_sub (Q R U : SupportedRepair T F) :
    repairDifference T P candidates allowed Q R =
      repairDifference T P candidates allowed Q U - repairDifference T P candidates allowed R U := by
  apply Subtype.ext; apply Subtype.ext
  change _ - _ = (_ - _) - (_ - _)
  abel

/-- Isomorphism classes of the original repairs under all permitted vertex labels. -/
abbrev RepairOrbit := Quotient (AddAction.orbitRel
  (supportedC0 T P.vertices F) (SupportedRepair T F))

/-- Two classes agree exactly when an original permitted reidentification connects them. -/
theorem repairOrbit_mk_eq_iff (Q R : SupportedRepair T F) :
    (⟦Q⟧ : RepairOrbit T P candidates allowed) = ⟦R⟧ ↔
      ∃ b : supportedC0 T P.vertices F, repairGauge T P.vertices F b R = Q := by
  rw [Quotient.eq'', AddAction.orbitRel_apply, AddAction.mem_orbit_iff]
  rfl

/-- Orbit equality is vanishing of the same supported difference in H1. -/
theorem repairOrbit_mk_eq_iff_difference_zero (Q R : SupportedRepair T F) :
    (⟦Q⟧ : RepairOrbit T P candidates allowed) = ⟦R⟧ ↔
      (QuotientAddGroup.mk (repairDifference T P candidates allowed Q R) :
        RelativeComplex.H1 M P candidates allowed) = 0 := by
  rw [repairOrbit_mk_eq_iff, RelativeComplex.h1_eq_zero_iff]
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨⟨b.1, by rw [← supportedC0_eq]; exact b.2⟩, ?_⟩
    apply Subtype.ext; apply Subtype.ext
    change d0 M b.1 = (repairCoord T F Q).1.1 - (repairCoord T F R).1.1
    rw [← hb, repairGauge_coord, add_sub_cancel_left]
  · rintro ⟨b, hb⟩
    refine ⟨⟨b.1, by rw [supportedC0_eq]; exact b.2⟩, ?_⟩
    apply (repairEquiv T F).injective
    apply Subtype.ext; apply Subtype.ext
    change (repairCoord T F _).1.1 = (repairCoord T F Q).1.1
    rw [repairGauge_coord]
    have hh : d0 M b.1 = (repairCoord T F Q).1.1 - (repairCoord T F R).1.1 :=
      congrArg (fun z => z.1.1) hb
    rw [hh]
    abel

/-- Equality of orbit classes is equality of H1 coordinates at any actual base repair. -/
theorem repairOrbit_mk_eq_iff_coord (base Q R : SupportedRepair T F) :
    (⟦Q⟧ : RepairOrbit T P candidates allowed) = ⟦R⟧ ↔
      (QuotientAddGroup.mk (repairDifference T P candidates allowed Q base) :
        RelativeComplex.H1 M P candidates allowed) =
      QuotientAddGroup.mk (repairDifference T P candidates allowed R base) := by
  rw [repairOrbit_mk_eq_iff_difference_zero, repairDifference_sub T P candidates allowed Q R base]
  have hmap : (QuotientAddGroup.mk
      (repairDifference T P candidates allowed Q base - repairDifference T P candidates allowed R base) :
        RelativeComplex.H1 M P candidates allowed) =
      QuotientAddGroup.mk (repairDifference T P candidates allowed Q base) -
        QuotientAddGroup.mk (repairDifference T P candidates allowed R base) :=
    (QuotientAddGroup.mk' (RelativeComplex.d0ToZ1 M P candidates allowed).range).map_sub _ _
  rw [hmap, sub_eq_zero]

/-- Coordinates of isomorphism classes at an actual base repair. -/
noncomputable def repairOrbitCoord (base : SupportedRepair T F) :
    RepairOrbit T P candidates allowed → RelativeComplex.H1 M P candidates allowed :=
  fun Q => Quotient.liftOn' Q
    (fun R => QuotientAddGroup.mk (repairDifference T P candidates allowed R base)) (by
      intro R Q h
      exact (repairOrbit_mk_eq_iff_coord T P candidates allowed base R Q).mp (Quotient.sound h))

/-- Restore every isomorphism class from a supported H1 class. -/
noncomputable def repairOrbitFromH1 (base : SupportedRepair T F) :
    RelativeComplex.H1 M P candidates allowed → RepairOrbit T P candidates allowed :=
  fun c => Quotient.liftOn' c
    (fun z => (⟦repairCocycleAction T P candidates allowed z base⟧ : RepairOrbit T P candidates allowed)) (by
      intro z w h
      apply (repairOrbit_mk_eq_iff_coord T P candidates allowed base _ _).mpr
      simpa only [repairDifference_action] using (Quotient.sound h :
        (QuotientAddGroup.mk z : RelativeComplex.H1 M P candidates allowed) = QuotientAddGroup.mk w))

/-- An actual base repair identifies all its isomorphism classes with the same H1. -/
noncomputable def repairOrbitEquivH1 (base : SupportedRepair T F) :
    RelativeComplex.H1 M P candidates allowed ≃ RepairOrbit T P candidates allowed where
  toFun := repairOrbitFromH1 T P candidates allowed base
  invFun := repairOrbitCoord T P candidates allowed base
  left_inv := by
    intro c
    induction c using Quotient.inductionOn' with
    | _ z =>
      change (QuotientAddGroup.mk (repairDifference T P candidates allowed
        (repairCocycleAction T P candidates allowed z base) base) :
        RelativeComplex.H1 M P candidates allowed) = QuotientAddGroup.mk z
      rw [repairDifference_action]
  right_inv := by
    intro Q
    induction Q using Quotient.inductionOn' with
    | _ R =>
      change (⟦repairCocycleAction T P candidates allowed
        (repairDifference T P candidates allowed R base) base⟧ : RepairOrbit T P candidates allowed) = ⟦R⟧
      rw [repairCocycleAction_difference]

/-- An internal choice used only to transport the standard torsor structure. -/
private noncomputable def orbitBase [Nonempty (SupportedRepair T F)] : SupportedRepair T F :=
  Classical.choice inferInstance

/-- G-130 A: nonempty actual repair classes form a torsor for the same supported H1. -/
noncomputable instance repairOrbitAddTorsor [Nonempty (SupportedRepair T F)] :
    AddTorsor (RelativeComplex.H1 M P candidates allowed) (RepairOrbit T P candidates allowed) := by
  let e := repairOrbitEquivH1 T P candidates allowed (orbitBase T P candidates allowed)
  exact {
    vadd := fun c Q => e (c + e.symm Q)
    zero_vadd := by intro Q; change e (0 + e.symm Q) = Q; rw [zero_add, e.apply_symm_apply]
    add_vadd := by
      intro c d Q
      change e ((c+d)+e.symm Q) = e (c+e.symm (e (d+e.symm Q)))
      rw [e.symm_apply_apply]
      congr 1
      exact add_assoc _ _ _
    vsub := fun Q R => e.symm Q - e.symm R
    nonempty := ⟨e 0⟩
    vsub_vadd' := by
      intro Q R
      change e ((e.symm Q - e.symm R) + e.symm R) = Q
      rw [sub_add_cancel, e.apply_symm_apply]
    vadd_vsub' := by
      intro c Q
      change e.symm (e (c+e.symm Q)) - e.symm Q = c
      rw [e.symm_apply_apply, add_sub_cancel_right] }

/-- Cocycle action shifts every actual difference coordinate by that cocycle. -/
theorem repairDifference_action_base (z : RelativeComplex.Z1 M P candidates allowed)
    (Q base : SupportedRepair T F) :
    repairDifference T P candidates allowed (repairCocycleAction T P candidates allowed z Q) base =
      z + repairDifference T P candidates allowed Q base := by
  apply Subtype.ext; apply Subtype.ext
  change (repairCoord T F _).1.1 - (repairCoord T F base).1.1 =
    z.1.1 + ((repairCoord T F Q).1.1 - (repairCoord T F base).1.1)
  rw [repairCocycleAction_coord]
  abel

/-- The native H1 torsor action is the actual cocycle action on representatives. -/
theorem repairOrbit_vadd_mk [Nonempty (SupportedRepair T F)]
    (z : RelativeComplex.Z1 M P candidates allowed) (Q : SupportedRepair T F) :
    (QuotientAddGroup.mk z : RelativeComplex.H1 M P candidates allowed) +ᵥ
      (⟦Q⟧ : RepairOrbit T P candidates allowed) =
        ⟦repairCocycleAction T P candidates allowed z Q⟧ := by
  let base := orbitBase T P candidates allowed
  let e := repairOrbitEquivH1 T P candidates allowed base
  change e ((QuotientAddGroup.mk z : RelativeComplex.H1 M P candidates allowed) + e.symm ⟦Q⟧) = _
  apply e.symm.injective
  rw [e.symm_apply_apply]
  change (QuotientAddGroup.mk z : RelativeComplex.H1 M P candidates allowed) +
    QuotientAddGroup.mk (repairDifference T P candidates allowed Q base) =
    QuotientAddGroup.mk (repairDifference T P candidates allowed
      (repairCocycleAction T P candidates allowed z Q) base)
  rw [repairDifference_action_base]
  exact ((QuotientAddGroup.mk' (RelativeComplex.d0ToZ1 M P candidates allowed).range).map_add _ _).symm

/-- The native torsor difference is the same actual difference mapped to H1. -/
theorem repairOrbit_vsub_mk [Nonempty (SupportedRepair T F)] (Q R : SupportedRepair T F) :
    ((⟦Q⟧ : RepairOrbit T P candidates allowed) -ᵥ ⟦R⟧ : RelativeComplex.H1 M P candidates allowed) =
      QuotientAddGroup.mk (repairDifference T P candidates allowed Q R) := by
  let base := orbitBase T P candidates allowed
  change (QuotientAddGroup.mk (repairDifference T P candidates allowed Q base) :
    RelativeComplex.H1 M P candidates allowed) -
      QuotientAddGroup.mk (repairDifference T P candidates allowed R base) =
        QuotientAddGroup.mk (repairDifference T P candidates allowed Q R)
  have hmap := (QuotientAddGroup.mk' (RelativeComplex.d0ToZ1 M P candidates allowed).range).map_sub
    (repairDifference T P candidates allowed Q base) (repairDifference T P candidates allowed R base)
  exact hmap.symm.trans (congrArg QuotientAddGroup.mk (repairDifference_sub T P candidates allowed Q R base).symm)

/-- Every original relative zero-cocycle is a permitted label for every change range. -/
noncomputable def relativeLabel (b : RelativeComplex.relativeH0 M P) :
    supportedC0 T P.vertices F :=
  ⟨b.1, by
    rw [supportedC0_eq, RelativeComplex.mem_C0Group]
    have hb := (RelativeComplex.mem_relativeH0 M P b.1).mp b.2
    refine ⟨(RelativeComplex.family_restrict_eq_zero _ _ _).mp hb.1, ?_⟩
    rw [show d0 M b.1 = 0 from hb.2]
    exact (RelativeComplex.C1Group M P candidates allowed).zero_mem⟩

/-- Construct a native actual automorphism and its inverse from each H0 label. -/
noncomputable def labelAut (R : RepairGroupoid T P.vertices F)
    (b : RelativeComplex.relativeH0 M P) : Aut R where
  hom := ⟨Multiplicative.ofAdd (relativeLabel T P candidates allowed b),
    (repairGauge_eq_self_iff T P.vertices F _ R.back).mpr
      ((RelativeComplex.mem_relativeH0 M P b.1).mp b.2).2⟩
  inv := ⟨Multiplicative.ofAdd (-relativeLabel T P candidates allowed b), by
    apply (repairGauge_eq_self_iff T P.vertices F _ R.back).mpr
    change (d0Hom M) (-b.1) = 0
    rw [map_neg, show (d0Hom M) b.1 = 0 from
      ((RelativeComplex.mem_relativeH0 M P b.1).mp b.2).2, neg_zero]⟩
  hom_inv_id := by
    apply Subtype.ext
    change Multiplicative.ofAdd (-relativeLabel T P candidates allowed b +
      relativeLabel T P candidates allowed b) = Multiplicative.ofAdd 0
    rw [neg_add_cancel]
  inv_hom_id := by
    apply Subtype.ext
    change Multiplicative.ofAdd (relativeLabel T P candidates allowed b +
      -relativeLabel T P candidates allowed b) = Multiplicative.ofAdd 0
    rw [add_neg_cancel]

/-- Native actual automorphisms are the same relative H0 group, with the original labels. -/
noncomputable def autH0Equiv (R : RepairGroupoid T P.vertices F) :
    Aut R ≃* Multiplicative (RelativeComplex.relativeH0 M P) where
  toFun f := Multiplicative.ofAdd ⟨f.hom.1.toAdd.1,
    (RelativeComplex.mem_relativeH0 M P _).mpr ⟨by
      apply (RelativeComplex.family_restrict_eq_zero (T.toTower.localCoefficients).A P.vertices _).mpr
      exact supportedC0_vertex_zero T P.vertices F f.hom.1.toAdd,
      (repairGauge_eq_self_iff T P.vertices F f.hom.1.toAdd R.back).mp f.hom.2⟩⟩
  invFun b := labelAut T P candidates allowed R b.toAdd
  left_inv f := by
    apply Aut.ext
    apply Subtype.ext
    rfl
  right_inv b := congrArg Multiplicative.ofAdd (Subtype.ext rfl)
  map_mul' f g := congrArg Multiplicative.ofAdd (Subtype.ext rfl)

/-- The Aut-to-H0 equivalence retains the forward arrow's original vertex label. -/
theorem autH0Equiv_label (R : RepairGroupoid T P.vertices F) (f : Aut R) :
    ((autH0Equiv T P candidates allowed R f).toAdd).1 = f.hom.1.toAdd.1 := rfl

/-- Native automorphisms are also isomorphic to H0 of the supported complex itself. -/
noncomputable def autSupportedH0Equiv (R : RepairGroupoid T P.vertices F) :
    Aut R ≃* Multiplicative (RelativeComplex.H0 M P candidates allowed) :=
  (autH0Equiv T P candidates allowed R).trans
    (RelativeComplex.h0Equiv M P candidates allowed).symm.toMultiplicative

/-- The supported H0 isomorphism also preserves the entire original vertex label. -/
theorem autSupportedH0Equiv_label (R : RepairGroupoid T P.vertices F) (f : Aut R) :
    ((autSupportedH0Equiv T P candidates allowed R f).toAdd).1.1 = f.hom.1.toAdd.1 := rfl

/-- The H0-to-Aut construction retains the same original vertex label. -/
theorem labelAut_label (R : RepairGroupoid T P.vertices F)
    (b : RelativeComplex.relativeH0 M P) :
    (labelAut T P candidates allowed R b).hom.1.toAdd.1 = b.1 := rfl

/-- The orbit quotient classifies isomorphisms in the native actual repair groupoid. -/
theorem repairOrbit_mk_eq_iff_iso (Q R : SupportedRepair T F) :
    (⟦Q⟧ : RepairOrbit T P candidates allowed) = ⟦R⟧ ↔
      Nonempty (@Iso (RepairGroupoid T P.vertices F) inferInstance Q R) := by
  rw [repairOrbit_mk_eq_iff]
  constructor
  · rintro ⟨b, hb⟩
    let f : @Quiver.Hom (RepairGroupoid T P.vertices F) inferInstance R Q :=
      ⟨Multiplicative.ofAdd b, hb⟩
    exact ⟨((@Groupoid.isoEquivHom (RepairGroupoid T P.vertices F)
      inferInstance R Q).symm f).symm⟩
  · rintro ⟨f⟩
    exact ⟨f.inv.1.toAdd, f.inv.2⟩

end ActualRelative
end AAT.AG.RelativeRepairComposition
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
