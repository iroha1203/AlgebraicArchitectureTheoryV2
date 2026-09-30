import ResearchLean.AG.RelativeRepairComposition.SupportedClassification

/-!
# Support relaxation and the same actual repair classifications

G-130 A / n1017 §2.2・2.5: increasing the allowed candidate set includes the
original supported cochains and actual repairs, keeping every vertex label.
The native chain map, H1/H2 maps, orbit map, torsor action and difference,
automorphism/H0 comparison, and obstruction class use these same inclusions.

## Implementation notes

Higher relative cochains are unchanged; only degrees zero and one relax support.
The quotient maps descend by explicit boundary inclusion. Native functors keep
the actual original edge choices and gauge labels on all morphisms.
-/
namespace AAT.AG.RelativeRepairComposition
open CategoryTheory TransportCoherence AbelianLiftingObstruction
universe uG uA
variable {K : FiniteTransportPresentation.{uG}}
namespace RelativeComplex
variable (M : LocalCoefficients.{uG,uA} K) (P : ClosedRegion K)
variable (candidates : Set (EdgeName (K := K))) {S U : Set (EdgeName (K := K))}

/-- G-130 A: Construct support relaxation from the antitone original fixed-edge sets. -/
def c1Inclusion (h : S ⊆ U) : C1Group M P candidates S →+ C1Group M P candidates U where
  toFun z := ⟨z.1, fun e he => z.2 e (fixedEdgesForRange_antitone P.edges candidates h he)⟩
  map_zero' := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl

/-- G-130 A: Retain original vertex labels whose coboundaries satisfy the relaxed support condition. -/
def c0Inclusion (h : S ⊆ U) : C0Group M P candidates S →+ C0Group M P candidates U where
  toFun b := ⟨b.1, (mem_C0Group M P candidates U _).mpr
    ⟨((mem_C0Group M P candidates S _).mp b.2).1,
      (c1Inclusion M P candidates h ⟨d0 M b.1, C0Group_d0_mem M P candidates S b⟩).2⟩⟩
  map_zero' := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl

/-- G-130 A: API connecting support relaxation to the original vertex-gauge differential. -/
theorem inclusion_d0 (h : S ⊆ U) (b : C0Group M P candidates S) :
    c1Inclusion M P candidates h (d0Supported M P candidates S b) =
      d0Supported M P candidates U (c0Inclusion M P candidates h b) := rfl

/-- G-130 A: API connecting support relaxation to the original face-correction differential. -/
theorem inclusion_d1 (h : S ⊆ U) (z : C1Group M P candidates S) :
    d1Supported M P candidates U (c1Inclusion M P candidates h z) =
      d1Supported M P candidates S z := rfl

/-- G-130 A: Construct cocycle relaxation from the differential compatibility API. -/
noncomputable def z1Inclusion (h : S ⊆ U) : Z1 M P candidates S →+ Z1 M P candidates U where
  toFun z := ⟨c1Inclusion M P candidates h z.1, by
    change d1Supported M P candidates U (c1Inclusion M P candidates h z.1) = 0
    rw [inclusion_d1]
    exact z.2⟩
  map_zero' := Subtype.ext (Subtype.ext rfl)
  map_add' _ _ := Subtype.ext (Subtype.ext rfl)

/-- G-130 A: API sending the original gauge boundary into the relaxed cocycle group. -/
theorem inclusion_d0_to_z1 (h : S ⊆ U) (b : C0Group M P candidates S) :
    z1Inclusion M P candidates h (d0ToZ1 M P candidates S b) =
      d0ToZ1 M P candidates U (c0Inclusion M P candidates h b) := rfl

/-- G-130 A: Generate the boundary containment required for the same H1 quotient map. -/
theorem h1_boundaries_inclusion (h : S ⊆ U) :
    (d0ToZ1 M P candidates S).range ≤
      (d0ToZ1 M P candidates U).range.comap (z1Inclusion M P candidates h) := by
  rintro z ⟨b, rfl⟩
  exact ⟨c0Inclusion M P candidates h b, (inclusion_d0_to_z1 M P candidates h b).symm⟩

/-- G-130 A: Descend the original cocycle inclusion to H1 using its proved boundary containment. -/
noncomputable def h1Inclusion (h : S ⊆ U) : H1 M P candidates S →+ H1 M P candidates U :=
  QuotientAddGroup.map _ _ (z1Inclusion M P candidates h) (h1_boundaries_inclusion M P candidates h)

/-- G-130 A: Representative API for the H1 support-relaxation map. -/
theorem h1_inclusion_mk (h : S ⊆ U) (z : Z1 M P candidates S) :
    h1Inclusion M P candidates h (QuotientAddGroup.mk z) =
      QuotientAddGroup.mk (z1Inclusion M P candidates h z) := rfl

/-- G-130 A: API retaining each original face-boundary cocycle under support relaxation. -/
theorem inclusion_d1_to_z2 (h : S ⊆ U) (z : C1Group M P candidates S) :
    d1ToZ2 M P candidates U (c1Inclusion M P candidates h z) =
      d1ToZ2 M P candidates S z := rfl

/-- G-130 A: Generate containment of the original face boundaries for the same H2 quotient. -/
theorem h2_boundaries_inclusion (h : S ⊆ U) :
    (d1ToZ2 M P candidates S).range ≤ (d1ToZ2 M P candidates U).range := by
  rintro z ⟨a, rfl⟩
  exact ⟨c1Inclusion M P candidates h a, inclusion_d1_to_z2 M P candidates h a⟩

/-- G-130 A: Descend the identity on relative two-cocycles to the relaxed H2 quotient. -/
noncomputable def h2Inclusion (h : S ⊆ U) : H2 M P candidates S →+ H2 M P candidates U :=
  QuotientAddGroup.map _ _ (AddMonoidHom.id _) (h2_boundaries_inclusion M P candidates h)

/-- G-130 A: Representative API for the H2 map on the same relative cocycle. -/
theorem h2_inclusion_mk (h : S ⊆ U) (z : Z2 M P) :
    h2Inclusion M P candidates h (QuotientAddGroup.mk z) = QuotientAddGroup.mk z := rfl

/-- Value APIs keep each original cochain under support relaxation. -/
theorem c1_inclusion_val (h : S ⊆ U) (z : C1Group M P candidates S) :
    (c1Inclusion M P candidates h z).1 = z.1 := rfl

/-- G-130 A: Value API for the original vertex labels retained by c0Inclusion. -/
theorem c0_inclusion_val (h : S ⊆ U) (b : C0Group M P candidates S) :
    (c0Inclusion M P candidates h b).1 = b.1 := rfl

/-- G-130 A: Value API retaining the original edge cocycle in z1Inclusion. -/
theorem z1_inclusion_val (h : S ⊆ U) (z : Z1 M P candidates S) :
    (z1Inclusion M P candidates h z).1.1 = z.1.1 := rfl

/-- G-130 A: Identity API for the H1 quotient maps of support relaxation. -/
theorem h1_inclusion_refl (z : H1 M P candidates S) :
    h1Inclusion M P candidates (Set.Subset.refl S) z = z := by
  induction z using QuotientAddGroup.induction_on with
  | H z => rfl

/-- G-130 A: Composition API for the H1 quotient maps of successive support relaxation. -/
theorem h1_inclusion_trans {V : Set (EdgeName (K := K))} (h : S ⊆ U) (k : U ⊆ V)
    (z : H1 M P candidates S) :
    h1Inclusion M P candidates k (h1Inclusion M P candidates h z) =
      h1Inclusion M P candidates (h.trans k) z := by
  induction z using QuotientAddGroup.induction_on with
  | H z => rfl

/-- G-130 A: Identity API for the H2 quotient maps of support relaxation. -/
theorem h2_inclusion_refl (z : H2 M P candidates S) :
    h2Inclusion M P candidates (Set.Subset.refl S) z = z := by
  induction z using QuotientAddGroup.induction_on with
  | H z => rfl

/-- G-130 A: Composition API for the H2 quotient maps of successive support relaxation. -/
theorem h2_inclusion_trans {V : Set (EdgeName (K := K))} (h : S ⊆ U) (k : U ⊆ V)
    (z : H2 M P candidates S) :
    h2Inclusion M P candidates k (h2Inclusion M P candidates h z) =
      h2Inclusion M P candidates (h.trans k) z := by
  induction z using QuotientAddGroup.induction_on with
  | H z => rfl

/-- Degreewise support relaxation, retaining the original higher cochains identically. -/
noncomputable def cochainInclusion (h : S ⊆ U) : ∀ n : ℕ,
    cochainObject M P candidates S n ⟶ cochainObject M P candidates U n
  | 0 => AddCommGrpCat.ofHom (c0Inclusion M P candidates h)
  | 1 => AddCommGrpCat.ofHom (c1Inclusion M P candidates h)
  | 2 => 𝟙 _
  | 3 => 𝟙 _
  | _ + 4 => 𝟙 _

/-- The degreewise inclusions commute with every original differential. -/
theorem cochain_inclusion_comm (h : S ⊆ U) (n : ℕ) :
    cochainInclusion M P candidates h n ≫ cochainDifferential M P candidates U n =
      cochainDifferential M P candidates S n ≫ cochainInclusion M P candidates h (n+1) := by
  cases n with
  | zero =>
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro b
    exact (inclusion_d0 M P candidates h b).symm
  | succ n =>
    cases n with
    | zero =>
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro z
      exact inclusion_d1 M P candidates h z
    | succ n =>
      cases n with
      | zero =>
        change 𝟙 _ ≫ _ = _ ≫ 𝟙 _
        rw [Category.id_comp, Category.comp_id]
        rfl
      | succ n =>
        cases n <;> change 𝟙 _ ≫ (0 : _ ⟶ _) = (0 : _ ⟶ _) ≫ 𝟙 _
        all_goals rw [Category.id_comp, Category.comp_id]

/-- Support relaxation is a native map of the same four-term relative complexes. -/
noncomputable def cochainMap (h : S ⊆ U) :
    cochainComplex M P candidates S ⟶ cochainComplex M P candidates U :=
  CochainComplex.ofHom _ _ _ _ _ _ (cochainInclusion M P candidates h)
    (cochain_inclusion_comm M P candidates h)

/-- G-130 A: Degree-zero API exposing the original allowed vertex-label inclusion. -/
theorem cochain_map_f_zero (h : S ⊆ U) :
    (cochainMap M P candidates h).f 0 = AddCommGrpCat.ofHom (c0Inclusion M P candidates h) := rfl

/-- G-130 A: Degree-one API exposing the original supported edge-cochain inclusion. -/
theorem cochain_map_f_one (h : S ⊆ U) :
    (cochainMap M P candidates h).f 1 = AddCommGrpCat.ofHom (c1Inclusion M P candidates h) := rfl

/-- G-130 A: Degree-two API retaining all original relative face-cochain values. -/
theorem cochain_map_f_two (h : S ⊆ U) :
    (cochainMap M P candidates h).f 2 = 𝟙 _ := rfl

/-- G-130 A: Degree-three API retaining all original relative syzygy-cochain values. -/
theorem cochain_map_f_three (h : S ⊆ U) :
    (cochainMap M P candidates h).f 3 = 𝟙 _ := rfl

/-- G-130 A: API identifying the unchanged zero tail of the four-term complex. -/
theorem cochain_map_f_above (h : S ⊆ U) (n : ℕ) :
    (cochainMap M P candidates h).f (n+4) = 𝟙 _ := rfl

/-- Native support-relaxation maps compose without changing any original cochain. -/
theorem cochain_map_comp {V : Set (EdgeName (K := K))} (h : S ⊆ U) (k : U ⊆ V) :
    cochainMap M P candidates h ≫ cochainMap M P candidates k =
      cochainMap M P candidates (h.trans k) := by
  apply HomologicalComplex.Hom.ext
  funext n
  cases n with
  | zero => rfl
  | succ n =>
    cases n with
    | zero => rfl
    | succ n =>
      cases n with
      | zero => exact Category.id_comp _
      | succ n => cases n <;> exact Category.id_comp _

/-- Compatibility spelling for the G-130 A API `inclusion_d0_to_z1`; retained for declaration tracing. -/
@[deprecated inclusion_d0_to_z1 (since := "2026-10-01")] alias inclusion_d0ToZ1 := inclusion_d0_to_z1

/-- Compatibility spelling for the G-130 A API `h1_inclusion_mk`; retained for declaration tracing. -/
@[deprecated h1_inclusion_mk (since := "2026-10-01")] alias h1Inclusion_mk := h1_inclusion_mk

/-- Compatibility spelling for the G-130 A API `inclusion_d1_to_z2`; retained for declaration tracing. -/
@[deprecated inclusion_d1_to_z2 (since := "2026-10-01")] alias inclusion_d1ToZ2 := inclusion_d1_to_z2

/-- Compatibility spelling for the G-130 A API `h2_inclusion_mk`; retained for declaration tracing. -/
@[deprecated h2_inclusion_mk (since := "2026-10-01")] alias h2Inclusion_mk := h2_inclusion_mk

/-- Compatibility spelling for the G-130 A API `c1_inclusion_val`; retained for declaration tracing. -/
@[deprecated c1_inclusion_val (since := "2026-10-01")] alias c1Inclusion_val := c1_inclusion_val

/-- Compatibility spelling for the G-130 A API `c0_inclusion_val`; retained for declaration tracing. -/
@[deprecated c0_inclusion_val (since := "2026-10-01")] alias c0Inclusion_val := c0_inclusion_val

/-- Compatibility spelling for the G-130 A API `z1_inclusion_val`; retained for declaration tracing. -/
@[deprecated z1_inclusion_val (since := "2026-10-01")] alias z1Inclusion_val := z1_inclusion_val

/-- Compatibility spelling for the G-130 A API `h1_inclusion_refl`; retained for declaration tracing. -/
@[deprecated h1_inclusion_refl (since := "2026-10-01")] alias h1Inclusion_refl := h1_inclusion_refl

/-- Compatibility spelling for the G-130 A API `h1_inclusion_trans`; retained for declaration tracing. -/
@[deprecated h1_inclusion_trans (since := "2026-10-01")] alias h1Inclusion_trans := h1_inclusion_trans

/-- Compatibility spelling for the G-130 A API `h2_inclusion_refl`; retained for declaration tracing. -/
@[deprecated h2_inclusion_refl (since := "2026-10-01")] alias h2Inclusion_refl := h2_inclusion_refl

/-- Compatibility spelling for the G-130 A API `h2_inclusion_trans`; retained for declaration tracing. -/
@[deprecated h2_inclusion_trans (since := "2026-10-01")] alias h2Inclusion_trans := h2_inclusion_trans

/-- Compatibility spelling for the G-130 A API `cochain_inclusion_comm`; retained for declaration tracing. -/
@[deprecated cochain_inclusion_comm (since := "2026-10-01")] alias cochainInclusion_comm := cochain_inclusion_comm

/-- Compatibility spelling for the G-130 A API `cochain_map_f_zero`; retained for declaration tracing. -/
@[deprecated cochain_map_f_zero (since := "2026-10-01")] alias cochainMap_f_zero := cochain_map_f_zero

/-- Compatibility spelling for the G-130 A API `cochain_map_f_one`; retained for declaration tracing. -/
@[deprecated cochain_map_f_one (since := "2026-10-01")] alias cochainMap_f_one := cochain_map_f_one

/-- Compatibility spelling for the G-130 A API `cochain_map_f_two`; retained for declaration tracing. -/
@[deprecated cochain_map_f_two (since := "2026-10-01")] alias cochainMap_f_two := cochain_map_f_two

/-- Compatibility spelling for the G-130 A API `cochain_map_f_three`; retained for declaration tracing. -/
@[deprecated cochain_map_f_three (since := "2026-10-01")] alias cochainMap_f_three := cochain_map_f_three

/-- Compatibility spelling for the G-130 A API `cochain_map_f_above`; retained for declaration tracing. -/
@[deprecated cochain_map_f_above (since := "2026-10-01")] alias cochainMap_f_above := cochain_map_f_above

/-- Compatibility spelling for the G-130 A API `cochain_map_comp`; retained for declaration tracing. -/
@[deprecated cochain_map_comp (since := "2026-10-01")] alias cochainMap_comp := cochain_map_comp

end RelativeComplex

namespace ActualRelative
open TransportCoherence.Arbitrary
universe uE uB uD vE vB vD
variable {E : Type uE} {B : Type uB} {D : Type uD}
variable [Category.{vE} E] [Category.{vB} B] [Category.{vD} D]
variable {p : E ⥤ B} {q : B ⥤ D}
variable (T : OriginalTowerPresentation K p q) (P : ClosedRegion K)
variable (candidates : Set (EdgeName (K := K))) {S U : Set (EdgeName (K := K))}
local notation "M" => T.toTower.localCoefficients
local notation "FS" => fixedEdgesForRange P.edges candidates S
local notation "FU" => fixedEdgesForRange P.edges candidates U

/-- G-130 A: Construct the native actual repair inclusion while retaining every original gauge label. -/
noncomputable def rangeFunctor (h : S ⊆ U) :
    RepairGroupoid T P.vertices FS ⥤ RepairGroupoid T P.vertices FU where
  obj R := (repairInclusion T (fixedEdgesForRange_antitone P.edges candidates h) R.back :
    RepairGroupoid T P.vertices FU)
  map {R _} b :=
    ⟨Multiplicative.ofAdd (gaugeInclusion T P.vertices
      (fixedEdgesForRange_antitone P.edges candidates h) b.1.toAdd),
      (gauge_inclusion T P.vertices (fixedEdgesForRange_antitone P.edges candidates h)
        b.1.toAdd R.back).symm.trans
      (congrArg (repairInclusion T (fixedEdgesForRange_antitone P.edges candidates h)) b.2)⟩
  map_id _ := Subtype.ext (congrArg Multiplicative.ofAdd (Subtype.ext rfl))
  map_comp _ _ := Subtype.ext (congrArg Multiplicative.ofAdd (Subtype.ext rfl))

/-- G-130 A: Label API for every native morphism of the actual range-inclusion functor. -/
theorem range_functor_map_label (h : S ⊆ U)
    {R Q : RepairGroupoid T P.vertices FS} (b : R ⟶ Q) :
    ((rangeFunctor T P candidates h).map b).1.toAdd.1 = b.1.toAdd.1 := rfl

/-- G-130 A: Descend the actual repair inclusion to classes using its preserved gauge labels. -/
noncomputable def rangeOrbitInclusion (h : S ⊆ U) :
    RepairOrbit T P candidates S → RepairOrbit T P candidates U :=
  fun Q => Quotient.liftOn' Q
    (fun R => (⟦repairInclusion T (fixedEdgesForRange_antitone P.edges candidates h) R⟧ :
      RepairOrbit T P candidates U)) (by
        intro R Q hr
        apply (repairOrbit_mk_eq_iff T P candidates U _ _).mpr
        obtain ⟨b, hb⟩ := (repairOrbit_mk_eq_iff T P candidates S R Q).mp (Quotient.sound hr)
        refine ⟨gaugeInclusion T P.vertices (fixedEdgesForRange_antitone P.edges candidates h) b, ?_⟩
        rw [← gauge_inclusion, hb])

/-- G-130 A: Representative API retaining the actual repair under orbit inclusion. -/
theorem range_orbit_inclusion_mk (h : S ⊆ U) (R : SupportedRepair T FS) :
    rangeOrbitInclusion T P candidates h (⟦R⟧ : RepairOrbit T P candidates S) =
      ⟦repairInclusion T (fixedEdgesForRange_antitone P.edges candidates h) R⟧ := rfl

/-- G-130 A: API comparing original actual repair differences with cocycle support relaxation. -/
theorem range_difference_inclusion (h : S ⊆ U) (R Q : SupportedRepair T FS) :
    repairDifference T P candidates U
      (repairInclusion T (fixedEdgesForRange_antitone P.edges candidates h) R)
      (repairInclusion T (fixedEdgesForRange_antitone P.edges candidates h) Q) =
    RelativeComplex.z1Inclusion M P candidates h (repairDifference T P candidates S R Q) := rfl

/-- G-130 A: Compare H1 coordinates based at the same actual repair under range inclusion. -/
theorem range_orbit_coord_inclusion (h : S ⊆ U) (base : SupportedRepair T FS)
    (Q : RepairOrbit T P candidates S) :
    repairOrbitCoord T P candidates U
      (repairInclusion T (fixedEdgesForRange_antitone P.edges candidates h) base)
      (rangeOrbitInclusion T P candidates h Q) =
    RelativeComplex.h1Inclusion M P candidates h (repairOrbitCoord T P candidates S base Q) := by
  induction Q using Quotient.inductionOn' with
  | _ R =>
    rw [range_orbit_inclusion_mk, repairOrbitCoord_mk, repairOrbitCoord_mk,
      RelativeComplex.h1_inclusion_mk, range_difference_inclusion]

/-- G-130 A: Match the same original relative defect class under H2 support relaxation. -/
theorem obstruction_inclusion (h : S ⊆ U)
    (hfixed : ∀ f ∈ P.faces,
      T.toTower.upper.pathLift (K.twoLeft f) ≫ FiberAut.hom (T.comparator f) =
        T.toTower.upper.pathLift (K.twoRight f))
    (hsyzygy : ∀ s : K.ThreeCell, TransportCoherence.Arbitrary.AuthoredSyzygy
      T.toTower.toTransportData 1 (K.threeLeft s) (K.threeRight s)) :
    RelativeComplex.h2Inclusion M P candidates h
      (obstructionClass T P candidates S hfixed hsyzygy) =
      obstructionClass T P candidates U hfixed hsyzygy := rfl

/-- Object API: the functor retains the actual choices on every original edge. -/
theorem range_functor_obj (h : S ⊆ U) (R : RepairGroupoid T P.vertices FS) :
    ((rangeFunctor T P candidates h).obj R).back =
      repairInclusion T (fixedEdgesForRange_antitone P.edges candidates h) R.back := rfl

/-- G-130 A: Choice API retaining each original named actual edge under inclusion. -/
theorem range_functor_obj_choice (h : S ⊆ U) (R : RepairGroupoid T P.vertices FS)
    {i j : K.Vertex} (e : K.Edge i j) :
    ((rangeFunctor T P candidates h).obj R).back.1.choice e = R.back.1.choice e := rfl

/-- G-130 A: Identity API for inclusion of actual repair classes. -/
theorem range_orbit_inclusion_refl (Q : RepairOrbit T P candidates S) :
    rangeOrbitInclusion T P candidates (Set.Subset.refl S) Q = Q := by
  induction Q using Quotient.inductionOn' with
  | _ R => rfl

/-- G-130 A: Composition API for successive inclusion of actual repair classes. -/
theorem range_orbit_inclusion_trans {V : Set (EdgeName (K := K))} (h : S ⊆ U) (k : U ⊆ V)
    (Q : RepairOrbit T P candidates S) :
    rangeOrbitInclusion T P candidates k (rangeOrbitInclusion T P candidates h Q) =
      rangeOrbitInclusion T P candidates (h.trans k) Q := by
  induction Q using Quotient.inductionOn' with
  | _ R => rfl

/-- G-130 A: Object identity API for the native actual repair inclusion. -/
theorem range_functor_refl (R : RepairGroupoid T P.vertices FS) :
    (rangeFunctor T P candidates (Set.Subset.refl S)).obj R = R := by
  change (R.back : RepairGroupoid T P.vertices FS) = R
  exact ActionCategory.back_coe R

/-- G-130 A: Object composition API for the native actual repair inclusions. -/
theorem range_functor_trans {V : Set (EdgeName (K := K))} (h : S ⊆ U) (k : U ⊆ V)
    (R : RepairGroupoid T P.vertices FS) :
    (rangeFunctor T P candidates k).obj ((rangeFunctor T P candidates h).obj R) =
      (rangeFunctor T P candidates (h.trans k)).obj R := rfl

/-- Inclusion of all actual automorphisms agrees with the same range-independent H0. -/
theorem range_aut_h0 (h : S ⊆ U) (R : RepairGroupoid T P.vertices FS) (b : Aut R) :
    autH0Equiv T P candidates U ((rangeFunctor T P candidates h).obj R)
      ((rangeFunctor T P candidates h).mapIso b) =
      autH0Equiv T P candidates S R b := by
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  rfl

/-- The H1 coordinate equivalences commute with support relaxation. -/
theorem range_orbit_equiv_h1 (h : S ⊆ U) (base : SupportedRepair T FS)
    (Q : RepairOrbit T P candidates S) :
    (repairOrbitEquivH1 T P candidates U
      (repairInclusion T (fixedEdgesForRange_antitone P.edges candidates h) base)).symm
      (rangeOrbitInclusion T P candidates h Q) =
      RelativeComplex.h1Inclusion M P candidates h ((repairOrbitEquivH1 T P candidates S base).symm Q) :=
by
  rw [repairOrbitEquivH1_symm_apply, repairOrbitEquivH1_symm_apply]
  exact range_orbit_coord_inclusion T P candidates h base Q

/-- G-130 A value API of the original correction inclusion, with the same named edge values. -/
theorem correction_inclusion_val {fixed larger : Set (EdgeName (K := K))}
    (h : fixed ⊆ larger) (x : SupportedCorrection T larger) :
    (correctionInclusion T h x).1.1 = x.1.1 := rfl

/-- Every cocycle action commutes with the same actual inclusion. -/
theorem range_cocycle_action (h : S ⊆ U) (z : RelativeComplex.Z1 M P candidates S)
    (R : SupportedRepair T FS) :
    repairInclusion T (fixedEdgesForRange_antitone P.edges candidates h)
      (repairCocycleAction T P candidates S z R) =
    repairCocycleAction T P candidates U (RelativeComplex.z1Inclusion M P candidates h z)
      (repairInclusion T (fixedEdgesForRange_antitone P.edges candidates h) R) := by
  apply (repairEquiv T FU).injective
  apply Subtype.ext
  apply Subtype.ext
  change (repairCoord T FU _).1.1 = (repairCoord T FU _).1.1
  rw [coord_inclusion, correction_inclusion_val, repairCocycleAction_coord,
    repairCocycleAction_coord]
  rfl

/-- G-130 A: Compare the native H1 actions under range relaxation, only when repairs exist. -/
theorem range_orbit_inclusion_vadd (h : S ⊆ U) [Nonempty (SupportedRepair T FS)]
    (z : RelativeComplex.H1 M P candidates S) (Q : RepairOrbit T P candidates S) :
    letI : Nonempty (SupportedRepair T FU) := ⟨repairInclusion T
      (fixedEdgesForRange_antitone P.edges candidates h) (Classical.choice inferInstance)⟩
    rangeOrbitInclusion T P candidates h (z +ᵥ Q) =
      RelativeComplex.h1Inclusion M P candidates h z +ᵥ rangeOrbitInclusion T P candidates h Q := by
  letI : Nonempty (SupportedRepair T FU) := ⟨repairInclusion T
    (fixedEdgesForRange_antitone P.edges candidates h) (Classical.choice inferInstance)⟩
  induction z using QuotientAddGroup.induction_on with
  | H z =>
    induction Q using Quotient.inductionOn' with
    | _ R =>
      rw [repairOrbit_vadd_mk, range_orbit_inclusion_mk, RelativeComplex.h1_inclusion_mk,
        range_orbit_inclusion_mk, repairOrbit_vadd_mk, range_cocycle_action]

/-- G-130 A: Compare native torsor differences under the same actual range inclusion. -/
theorem range_orbit_inclusion_vsub (h : S ⊆ U) [Nonempty (SupportedRepair T FS)]
    (Q R : RepairOrbit T P candidates S) :
    letI : Nonempty (SupportedRepair T FU) := ⟨repairInclusion T
      (fixedEdgesForRange_antitone P.edges candidates h) (Classical.choice inferInstance)⟩
    RelativeComplex.h1Inclusion M P candidates h (Q -ᵥ R) =
      rangeOrbitInclusion T P candidates h Q -ᵥ rangeOrbitInclusion T P candidates h R := by
  letI : Nonempty (SupportedRepair T FU) := ⟨repairInclusion T
    (fixedEdgesForRange_antitone P.edges candidates h) (Classical.choice inferInstance)⟩
  induction Q using Quotient.inductionOn' with
  | _ Q =>
    induction R using Quotient.inductionOn' with
    | _ R =>
      rw [repairOrbit_vsub_mk, RelativeComplex.h1_inclusion_mk,
        range_orbit_inclusion_mk, range_orbit_inclusion_mk, repairOrbit_vsub_mk,
        range_difference_inclusion]

/-- Inclusion functors compose on both actual objects and every labeled morphism. -/
theorem range_functor_comp {V : Set (EdgeName (K := K))} (h : S ⊆ U) (k : U ⊆ V) :
    rangeFunctor T P candidates h ⋙ rangeFunctor T P candidates k =
      rangeFunctor T P candidates (h.trans k) := rfl

/-- Compatibility spelling for the G-130 A API `range_functor_map_label`; retained for declaration tracing. -/
@[deprecated range_functor_map_label (since := "2026-10-01")] alias rangeFunctor_map_label := range_functor_map_label

/-- Compatibility spelling for the G-130 A API `range_orbit_inclusion_mk`; retained for declaration tracing. -/
@[deprecated range_orbit_inclusion_mk (since := "2026-10-01")] alias rangeOrbitInclusion_mk := range_orbit_inclusion_mk

/-- Compatibility spelling for the G-130 A API `range_difference_inclusion`; retained for declaration tracing. -/
@[deprecated range_difference_inclusion (since := "2026-10-01")] alias rangeDifference_inclusion := range_difference_inclusion

/-- Compatibility spelling for the G-130 A API `range_orbit_coord_inclusion`; retained for declaration tracing. -/
@[deprecated range_orbit_coord_inclusion (since := "2026-10-01")] alias rangeOrbitCoord_inclusion := range_orbit_coord_inclusion

/-- Compatibility spelling for the G-130 A API `range_functor_obj`; retained for declaration tracing. -/
@[deprecated range_functor_obj (since := "2026-10-01")] alias rangeFunctor_obj := range_functor_obj

/-- Compatibility spelling for the G-130 A API `range_functor_obj_choice`; retained for declaration tracing. -/
@[deprecated range_functor_obj_choice (since := "2026-10-01")] alias rangeFunctor_obj_choice := range_functor_obj_choice

/-- Compatibility spelling for the G-130 A API `range_orbit_inclusion_refl`; retained for declaration tracing. -/
@[deprecated range_orbit_inclusion_refl (since := "2026-10-01")] alias rangeOrbitInclusion_refl := range_orbit_inclusion_refl

/-- Compatibility spelling for the G-130 A API `range_orbit_inclusion_trans`; retained for declaration tracing. -/
@[deprecated range_orbit_inclusion_trans (since := "2026-10-01")] alias rangeOrbitInclusion_trans := range_orbit_inclusion_trans

/-- Compatibility spelling for the G-130 A API `range_functor_refl`; retained for declaration tracing. -/
@[deprecated range_functor_refl (since := "2026-10-01")] alias rangeFunctor_refl := range_functor_refl

/-- Compatibility spelling for the G-130 A API `range_functor_trans`; retained for declaration tracing. -/
@[deprecated range_functor_trans (since := "2026-10-01")] alias rangeFunctor_trans := range_functor_trans

/-- Compatibility spelling for the G-130 A API `range_aut_h0`; retained for declaration tracing. -/
@[deprecated range_aut_h0 (since := "2026-10-01")] alias rangeAut_h0 := range_aut_h0

/-- Compatibility spelling for the G-130 A API `range_orbit_equiv_h1`; retained for declaration tracing. -/
@[deprecated range_orbit_equiv_h1 (since := "2026-10-01")] alias rangeOrbitEquivH1 := range_orbit_equiv_h1

/-- Compatibility spelling for the G-130 A API `range_cocycle_action`; retained for declaration tracing. -/
@[deprecated range_cocycle_action (since := "2026-10-01")] alias rangeCocycleAction := range_cocycle_action

/-- Compatibility spelling for the G-130 A API `range_orbit_inclusion_vadd`; retained for declaration tracing. -/
@[deprecated range_orbit_inclusion_vadd (since := "2026-10-01")] alias rangeOrbitInclusion_vadd := range_orbit_inclusion_vadd

/-- Compatibility spelling for the G-130 A API `range_orbit_inclusion_vsub`; retained for declaration tracing. -/
@[deprecated range_orbit_inclusion_vsub (since := "2026-10-01")] alias rangeOrbitInclusion_vsub := range_orbit_inclusion_vsub

/-- Compatibility spelling for the G-130 A API `range_functor_comp`; retained for declaration tracing. -/
@[deprecated range_functor_comp (since := "2026-10-01")] alias rangeFunctor_comp := range_functor_comp

end ActualRelative
end AAT.AG.RelativeRepairComposition
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
