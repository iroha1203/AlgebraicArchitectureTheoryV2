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

def c1Inclusion (h : S ⊆ U) : C1Group M P candidates S →+ C1Group M P candidates U where
  toFun z := ⟨z.1, fun e he => z.2 e (fixedEdgesForRange_antitone P.edges candidates h he)⟩
  map_zero' := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl

def c0Inclusion (h : S ⊆ U) : C0Group M P candidates S →+ C0Group M P candidates U where
  toFun b := ⟨b.1, (mem_C0Group M P candidates U _).mpr
    ⟨((mem_C0Group M P candidates S _).mp b.2).1,
      (c1Inclusion M P candidates h ⟨d0 M b.1, C0Group_d0_mem M P candidates S b⟩).2⟩⟩
  map_zero' := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl

theorem inclusion_d0 (h : S ⊆ U) (b : C0Group M P candidates S) :
    c1Inclusion M P candidates h (d0Supported M P candidates S b) =
      d0Supported M P candidates U (c0Inclusion M P candidates h b) := rfl

theorem inclusion_d1 (h : S ⊆ U) (z : C1Group M P candidates S) :
    d1Supported M P candidates U (c1Inclusion M P candidates h z) =
      d1Supported M P candidates S z := rfl

noncomputable def z1Inclusion (h : S ⊆ U) : Z1 M P candidates S →+ Z1 M P candidates U where
  toFun z := ⟨c1Inclusion M P candidates h z.1, by
    change d1Supported M P candidates U (c1Inclusion M P candidates h z.1) = 0
    rw [inclusion_d1]
    exact z.2⟩
  map_zero' := Subtype.ext (Subtype.ext rfl)
  map_add' _ _ := Subtype.ext (Subtype.ext rfl)

theorem inclusion_d0ToZ1 (h : S ⊆ U) (b : C0Group M P candidates S) :
    z1Inclusion M P candidates h (d0ToZ1 M P candidates S b) =
      d0ToZ1 M P candidates U (c0Inclusion M P candidates h b) := rfl

theorem h1_boundaries_inclusion (h : S ⊆ U) :
    (d0ToZ1 M P candidates S).range ≤
      (d0ToZ1 M P candidates U).range.comap (z1Inclusion M P candidates h) := by
  rintro z ⟨b, rfl⟩
  exact ⟨c0Inclusion M P candidates h b, (inclusion_d0ToZ1 M P candidates h b).symm⟩

noncomputable def h1Inclusion (h : S ⊆ U) : H1 M P candidates S →+ H1 M P candidates U :=
  QuotientAddGroup.map _ _ (z1Inclusion M P candidates h) (h1_boundaries_inclusion M P candidates h)

theorem h1Inclusion_mk (h : S ⊆ U) (z : Z1 M P candidates S) :
    h1Inclusion M P candidates h (QuotientAddGroup.mk z) =
      QuotientAddGroup.mk (z1Inclusion M P candidates h z) := rfl

theorem inclusion_d1ToZ2 (h : S ⊆ U) (z : C1Group M P candidates S) :
    d1ToZ2 M P candidates U (c1Inclusion M P candidates h z) =
      d1ToZ2 M P candidates S z := rfl

theorem h2_boundaries_inclusion (h : S ⊆ U) :
    (d1ToZ2 M P candidates S).range ≤ (d1ToZ2 M P candidates U).range := by
  rintro z ⟨a, rfl⟩
  exact ⟨c1Inclusion M P candidates h a, inclusion_d1ToZ2 M P candidates h a⟩

noncomputable def h2Inclusion (h : S ⊆ U) : H2 M P candidates S →+ H2 M P candidates U :=
  QuotientAddGroup.map _ _ (AddMonoidHom.id _) (h2_boundaries_inclusion M P candidates h)

theorem h2Inclusion_mk (h : S ⊆ U) (z : Z2 M P) :
    h2Inclusion M P candidates h (QuotientAddGroup.mk z) = QuotientAddGroup.mk z := rfl

/-- Value APIs keep each original cochain under support relaxation. -/
theorem c1Inclusion_val (h : S ⊆ U) (z : C1Group M P candidates S) :
    (c1Inclusion M P candidates h z).1 = z.1 := rfl

theorem c0Inclusion_val (h : S ⊆ U) (b : C0Group M P candidates S) :
    (c0Inclusion M P candidates h b).1 = b.1 := rfl

theorem z1Inclusion_val (h : S ⊆ U) (z : Z1 M P candidates S) :
    (z1Inclusion M P candidates h z).1.1 = z.1.1 := rfl

theorem h1Inclusion_refl (z : H1 M P candidates S) :
    h1Inclusion M P candidates (Set.Subset.refl S) z = z := by
  induction z using QuotientAddGroup.induction_on with
  | H z => rfl

theorem h1Inclusion_trans {V : Set (EdgeName (K := K))} (h : S ⊆ U) (k : U ⊆ V)
    (z : H1 M P candidates S) :
    h1Inclusion M P candidates k (h1Inclusion M P candidates h z) =
      h1Inclusion M P candidates (h.trans k) z := by
  induction z using QuotientAddGroup.induction_on with
  | H z => rfl

theorem h2Inclusion_refl (z : H2 M P candidates S) :
    h2Inclusion M P candidates (Set.Subset.refl S) z = z := by
  induction z using QuotientAddGroup.induction_on with
  | H z => rfl

theorem h2Inclusion_trans {V : Set (EdgeName (K := K))} (h : S ⊆ U) (k : U ⊆ V)
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
theorem cochainInclusion_comm (h : S ⊆ U) (n : ℕ) :
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
    (cochainInclusion_comm M P candidates h)

theorem cochainMap_f_zero (h : S ⊆ U) :
    (cochainMap M P candidates h).f 0 = AddCommGrpCat.ofHom (c0Inclusion M P candidates h) := rfl

theorem cochainMap_f_one (h : S ⊆ U) :
    (cochainMap M P candidates h).f 1 = AddCommGrpCat.ofHom (c1Inclusion M P candidates h) := rfl

theorem cochainMap_f_two (h : S ⊆ U) :
    (cochainMap M P candidates h).f 2 = 𝟙 _ := rfl

theorem cochainMap_f_three (h : S ⊆ U) :
    (cochainMap M P candidates h).f 3 = 𝟙 _ := rfl

theorem cochainMap_f_above (h : S ⊆ U) (n : ℕ) :
    (cochainMap M P candidates h).f (n+4) = 𝟙 _ := rfl

/-- Native support-relaxation maps compose without changing any original cochain. -/
theorem cochainMap_comp {V : Set (EdgeName (K := K))} (h : S ⊆ U) (k : U ⊆ V) :
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

theorem rangeFunctor_map_label (h : S ⊆ U)
    {R Q : RepairGroupoid T P.vertices FS} (b : R ⟶ Q) :
    ((rangeFunctor T P candidates h).map b).1.toAdd.1 = b.1.toAdd.1 := rfl

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

theorem rangeOrbitInclusion_mk (h : S ⊆ U) (R : SupportedRepair T FS) :
    rangeOrbitInclusion T P candidates h (⟦R⟧ : RepairOrbit T P candidates S) =
      ⟦repairInclusion T (fixedEdgesForRange_antitone P.edges candidates h) R⟧ := rfl

theorem rangeDifference_inclusion (h : S ⊆ U) (R Q : SupportedRepair T FS) :
    repairDifference T P candidates U
      (repairInclusion T (fixedEdgesForRange_antitone P.edges candidates h) R)
      (repairInclusion T (fixedEdgesForRange_antitone P.edges candidates h) Q) =
    RelativeComplex.z1Inclusion M P candidates h (repairDifference T P candidates S R Q) := rfl

theorem rangeOrbitCoord_inclusion (h : S ⊆ U) (base : SupportedRepair T FS)
    (Q : RepairOrbit T P candidates S) :
    repairOrbitCoord T P candidates U
      (repairInclusion T (fixedEdgesForRange_antitone P.edges candidates h) base)
      (rangeOrbitInclusion T P candidates h Q) =
    RelativeComplex.h1Inclusion M P candidates h (repairOrbitCoord T P candidates S base Q) := by
  induction Q using Quotient.inductionOn' with
  | _ R =>
    rw [rangeOrbitInclusion_mk, repairOrbitCoord_mk, repairOrbitCoord_mk,
      RelativeComplex.h1Inclusion_mk, rangeDifference_inclusion]

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
theorem rangeFunctor_obj (h : S ⊆ U) (R : RepairGroupoid T P.vertices FS) :
    ((rangeFunctor T P candidates h).obj R).back =
      repairInclusion T (fixedEdgesForRange_antitone P.edges candidates h) R.back := rfl

theorem rangeFunctor_obj_choice (h : S ⊆ U) (R : RepairGroupoid T P.vertices FS)
    {i j : K.Vertex} (e : K.Edge i j) :
    ((rangeFunctor T P candidates h).obj R).back.1.choice e = R.back.1.choice e := rfl

theorem rangeOrbitInclusion_refl (Q : RepairOrbit T P candidates S) :
    rangeOrbitInclusion T P candidates (Set.Subset.refl S) Q = Q := by
  induction Q using Quotient.inductionOn' with
  | _ R => rfl

theorem rangeOrbitInclusion_trans {V : Set (EdgeName (K := K))} (h : S ⊆ U) (k : U ⊆ V)
    (Q : RepairOrbit T P candidates S) :
    rangeOrbitInclusion T P candidates k (rangeOrbitInclusion T P candidates h Q) =
      rangeOrbitInclusion T P candidates (h.trans k) Q := by
  induction Q using Quotient.inductionOn' with
  | _ R => rfl

theorem rangeFunctor_refl (R : RepairGroupoid T P.vertices FS) :
    (rangeFunctor T P candidates (Set.Subset.refl S)).obj R = R := by
  change (R.back : RepairGroupoid T P.vertices FS) = R
  exact ActionCategory.back_coe R

theorem rangeFunctor_trans {V : Set (EdgeName (K := K))} (h : S ⊆ U) (k : U ⊆ V)
    (R : RepairGroupoid T P.vertices FS) :
    (rangeFunctor T P candidates k).obj ((rangeFunctor T P candidates h).obj R) =
      (rangeFunctor T P candidates (h.trans k)).obj R := rfl

/-- Inclusion of all actual automorphisms agrees with the same range-independent H0. -/
theorem rangeAut_h0 (h : S ⊆ U) (R : RepairGroupoid T P.vertices FS) (b : Aut R) :
    autH0Equiv T P candidates U ((rangeFunctor T P candidates h).obj R)
      ((rangeFunctor T P candidates h).mapIso b) =
      autH0Equiv T P candidates S R b := by
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  rfl

/-- The H1 coordinate equivalences commute with support relaxation. -/
theorem rangeOrbitEquivH1 (h : S ⊆ U) (base : SupportedRepair T FS)
    (Q : RepairOrbit T P candidates S) :
    (repairOrbitEquivH1 T P candidates U
      (repairInclusion T (fixedEdgesForRange_antitone P.edges candidates h) base)).symm
      (rangeOrbitInclusion T P candidates h Q) =
      RelativeComplex.h1Inclusion M P candidates h ((repairOrbitEquivH1 T P candidates S base).symm Q) :=
by
  rw [repairOrbitEquivH1_symm_apply, repairOrbitEquivH1_symm_apply]
  exact rangeOrbitCoord_inclusion T P candidates h base Q

/-- Every cocycle action commutes with the same actual inclusion. -/
theorem rangeCocycleAction (h : S ⊆ U) (z : RelativeComplex.Z1 M P candidates S)
    (R : SupportedRepair T FS) :
    repairInclusion T (fixedEdgesForRange_antitone P.edges candidates h)
      (repairCocycleAction T P candidates S z R) =
    repairCocycleAction T P candidates U (RelativeComplex.z1Inclusion M P candidates h z)
      (repairInclusion T (fixedEdgesForRange_antitone P.edges candidates h) R) := by
  apply (repairEquiv T FU).injective
  apply Subtype.ext
  apply Subtype.ext
  change (repairCoord T FU _).1.1 = (repairCoord T FU _).1.1
  rw [show (repairCoord T FU
      (repairInclusion T _ (repairCocycleAction T P candidates S z R))).1.1 =
    (repairCoord T FS (repairCocycleAction T P candidates S z R)).1.1 from rfl,
    repairCocycleAction_coord, repairCocycleAction_coord]
  rfl

theorem rangeOrbitInclusion_vadd (h : S ⊆ U) [Nonempty (SupportedRepair T FS)]
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
      rw [repairOrbit_vadd_mk, rangeOrbitInclusion_mk, RelativeComplex.h1Inclusion_mk,
        rangeOrbitInclusion_mk, repairOrbit_vadd_mk, rangeCocycleAction]

theorem rangeOrbitInclusion_vsub (h : S ⊆ U) [Nonempty (SupportedRepair T FS)]
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
      rw [repairOrbit_vsub_mk, RelativeComplex.h1Inclusion_mk,
        rangeOrbitInclusion_mk, rangeOrbitInclusion_mk, repairOrbit_vsub_mk,
        rangeDifference_inclusion]

/-- Inclusion functors compose on both actual objects and every labeled morphism. -/
theorem rangeFunctor_comp {V : Set (EdgeName (K := K))} (h : S ⊆ U) (k : U ⊆ V) :
    rangeFunctor T P candidates h ⋙ rangeFunctor T P candidates k =
      rangeFunctor T P candidates (h.trans k) := rfl

end ActualRelative
end AAT.AG.RelativeRepairComposition
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
