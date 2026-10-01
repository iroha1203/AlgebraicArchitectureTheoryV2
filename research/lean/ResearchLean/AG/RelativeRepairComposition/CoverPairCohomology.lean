import ResearchLean.AG.RelativeRepairComposition.CoverCohomology

/-!
# Full cohomology of both local relative complexes

The pair quotient retains every local cycle and boundary. Its comparison with
the product of the two local cohomology groups is generated from the component
maps, including all representatives and both directions.
## Implementation notes

G-130 B requires the entire local pair in the cover short exact sequence.
The quotient by actual pair boundaries is compared with the full product
through component maps and their generated inverse. Keeping only a
selected range would remove classes needed for native exactness.
-/
namespace AAT.AG.RelativeRepairComposition
open CategoryTheory TransportCoherence AbelianLiftingObstruction
universe uG uA
namespace CoverPairCohomology
variable {K : FiniteTransportPresentation.{uG}}
variable (M : LocalCoefficients.{uG,uA} K) (P U V : ClosedRegion K)
/-- Full one-cycles of both local complexes. -/
noncomputable abbrev Z1 := (RelativeCover.pairD1 M P U V).ker
/-- Full vertex boundaries of both local complexes. -/
noncomputable def boundary1 : RelativeCover.C0 M U P × RelativeCover.C0 M V P →+ Z1 M P U V where
  toFun b := ⟨RelativeCover.pairD0 M P U V b,by
    change (RelativeCover.d1 M U P (RelativeCover.d0 M U P b.1),
      RelativeCover.d1 M V P (RelativeCover.d0 M V P b.2)) = 0
    rw [RelativeCover.d1_d0,RelativeCover.d1_d0]
    rfl⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)
/-- First cohomology of the full local pair. -/
abbrev H1 := Z1 M P U V ⧸ (boundary1 M P U V).range
/-- The first component retains all original local cycle values. -/
noncomputable def cycleLeft : Z1 M P U V →+ CoverCohomology.Z1 M P U where
  toFun z := ⟨z.1.1,congrArg Prod.fst z.2⟩
  map_zero' := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl
/-- The second component retains all original local cycle values. -/
noncomputable def cycleRight : Z1 M P U V →+ CoverCohomology.Z1 M P V where
  toFun z := ⟨z.1.2,congrArg Prod.snd z.2⟩
  map_zero' := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl
/-- Component classes are the entire local H1 classes. -/
noncomputable def cycleClasses : Z1 M P U V →+
    CoverCohomology.H1 M P U × CoverCohomology.H1 M P V :=
  ((QuotientAddGroup.mk' (CoverCohomology.boundary1 M P U).range).comp (cycleLeft M P U V)).prod
    ((QuotientAddGroup.mk' (CoverCohomology.boundary1 M P V).range).comp (cycleRight M P U V))
/-- Every local-pair boundary has both component classes zero. -/
theorem cycle_classes_boundary (b : RelativeCover.C0 M U P × RelativeCover.C0 M V P) :
    cycleClasses M P U V (boundary1 M P U V b) = 0 := by
  apply Prod.ext
  · change (QuotientAddGroup.mk (CoverCohomology.boundary1 M P U b.1) :
      CoverCohomology.H1 M P U) = 0
    rw [QuotientAddGroup.eq_zero_iff]
    exact ⟨b.1,rfl⟩
  · change (QuotientAddGroup.mk (CoverCohomology.boundary1 M P V b.2) :
      CoverCohomology.H1 M P V) = 0
    rw [QuotientAddGroup.eq_zero_iff]
    exact ⟨b.2,rfl⟩
/-- Full local-pair H1 maps to both entire component H1 groups. -/
noncomputable def componentH1 : H1 M P U V →+
    CoverCohomology.H1 M P U × CoverCohomology.H1 M P V :=
  QuotientAddGroup.lift _ (cycleClasses M P U V) (by
    rintro z ⟨b,rfl⟩
    exact cycle_classes_boundary M P U V b)
/-- The component comparison retains all original representative values. -/
theorem component_h1_mk (z : Z1 M P U V) :
    componentH1 M P U V (QuotientAddGroup.mk z) =
      (QuotientAddGroup.mk (cycleLeft M P U V z),
        QuotientAddGroup.mk (cycleRight M P U V z)) := rfl
/-- Every pair of local cohomology classes is represented by a full local-pair cycle. -/
theorem component_h1_surjective : Function.Surjective (componentH1 M P U V) := by
  rintro ⟨a,b⟩
  obtain ⟨u,rfl⟩ := QuotientAddGroup.mk'_surjective (CoverCohomology.boundary1 M P U).range a
  obtain ⟨v,rfl⟩ := QuotientAddGroup.mk'_surjective (CoverCohomology.boundary1 M P V).range b
  let z : Z1 M P U V := ⟨(u.1,v.1),Prod.ext u.2 v.2⟩
  exact ⟨QuotientAddGroup.mk z,rfl⟩
/-- Zero component classes mean exactly an original local-pair boundary. -/
theorem component_h1_kernel (x : H1 M P U V) :
    componentH1 M P U V x = 0 → x = 0 := by
  induction x using QuotientAddGroup.induction_on with
  | H z =>
    intro hz
    have hu := congrArg Prod.fst hz
    have hv := congrArg Prod.snd hz
    obtain ⟨a,ha⟩ := (CoverCohomology.h1_eq_zero_iff M P U (cycleLeft M P U V z)).mp hu
    obtain ⟨b,hb⟩ := (CoverCohomology.h1_eq_zero_iff M P V (cycleRight M P U V z)).mp hv
    rw [QuotientAddGroup.eq_zero_iff]
    refine ⟨(a,b),Subtype.ext ?_⟩
    exact Prod.ext (congrArg Subtype.val ha) (congrArg Subtype.val hb)
/-- Distinct local-pair H1 classes remain distinct under the component comparison. -/
theorem component_h1_injective : Function.Injective (componentH1 M P U V) := by
  intro x y h
  apply sub_eq_zero.mp
  apply component_h1_kernel M P U V
  rw [map_sub,h,sub_self]
/-- Native first cohomology of the local pair is the full product, in both directions. -/
noncomputable def componentEquiv : H1 M P U V ≃+
    CoverCohomology.H1 M P U × CoverCohomology.H1 M P V :=
  AddEquiv.ofBijective (componentH1 M P U V)
    ⟨component_h1_injective M P U V,component_h1_surjective M P U V⟩
/-- The first short segment uses the entire original local-pair differentials. -/
noncomputable def firstShortComplex : ShortComplex Ab where
  X₁ := AddCommGrpCat.of (RelativeCover.C0 M U P × RelativeCover.C0 M V P)
  X₂ := AddCommGrpCat.of (RelativeCover.C1 M U P × RelativeCover.C1 M V P)
  X₃ := AddCommGrpCat.of (RelativeCover.C2 M U P × RelativeCover.C2 M V P)
  f := AddCommGrpCat.ofHom (RelativeCover.pairD0 M P U V)
  g := AddCommGrpCat.ofHom (RelativeCover.pairD1 M P U V)
  zero := by
    apply AddCommGrpCat.hom_ext; apply AddMonoidHom.ext
    intro b
    exact (boundary1 M P U V b).2
/-- The local-pair first segment is degree one of the accepted native pair complex. -/
theorem first_eq_sc : firstShortComplex M P U V = (RelativeCover.pairComplex M P U V).sc 1 := by
  have hprev : (ComplexShape.up ℕ).prev 1 = 0 := by simp
  simp [HomologicalComplex.sc,HomologicalComplex.shortComplexFunctor,
    HomologicalComplex.shortComplexFunctor',RelativeCover.pairComplex,
    RelativeCover.pairObject,RelativeCover.pairDifferential,CochainComplex.of,
    firstShortComplex,hprev]
  rw [hprev]
/-- The explicit pair segment comparison preserves every middle original value. -/
noncomputable def firstNormalizedIso : (RelativeCover.pairComplex M P U V).sc' 0 1 2 ≅
    firstShortComplex M P U V :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) (by
    change 𝟙 _ ≫ _ = (RelativeCover.pairComplex M P U V).d 0 1 ≫ 𝟙 _
    rw [Category.comp_id,Category.id_comp]
    simp [RelativeCover.pairComplex,CochainComplex.of,RelativeCover.pairDifferential,
      firstShortComplex]) (by
    change 𝟙 _ ≫ _ = (RelativeCover.pairComplex M P U V).d 1 2 ≫ 𝟙 _
    rw [Category.comp_id,Category.id_comp]
    simp [RelativeCover.pairComplex,CochainComplex.of,RelativeCover.pairDifferential,
      firstShortComplex])
/-- The native pair segment comparison retains the same entire cochain. -/
noncomputable def firstShortIso : (RelativeCover.pairComplex M P U V).sc 1 ≅
    firstShortComplex M P U V :=
  (RelativeCover.pairComplex M P U V).isoSc' 0 1 2 (by simp) (by simp) ≪≫
    firstNormalizedIso M P U V
/-- Native homology of the full pair is the same explicit quotient with its cochain comparison. -/
noncomputable def firstHomologyIso : (RelativeCover.pairComplex M P U V).homology 1 ≅
    AddCommGrpCat.of (H1 M P U V) :=
  ShortComplex.homologyMapIso (firstShortIso M P U V) ≪≫
    (firstShortComplex M P U V).abHomologyIso
/-- The native first homology has the complete two-component comparison. -/
noncomputable def nativeFirstProductIso : (RelativeCover.pairComplex M P U V).homology 1 ≅
    AddCommGrpCat.of (CoverCohomology.H1 M P U × CoverCohomology.H1 M P V) :=
  firstHomologyIso M P U V ≪≫ (componentEquiv M P U V).toAddCommGrpIso
/-- Full two-cycles of both local complexes. -/
noncomputable abbrev Z2 := (RelativeCover.pairD2 M P U V).ker
/-- Full edge boundaries of both local complexes. -/
noncomputable def boundary2 : RelativeCover.C1 M U P × RelativeCover.C1 M V P →+ Z2 M P U V where
  toFun b := ⟨RelativeCover.pairD1 M P U V b,by
    change (RelativeCover.d2 M U P (RelativeCover.d1 M U P b.1),
      RelativeCover.d2 M V P (RelativeCover.d1 M V P b.2)) = 0
    rw [RelativeCover.d2_d1,RelativeCover.d2_d1]
    rfl⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)
/-- Second cohomology of the full local pair. -/
abbrev H2 := Z2 M P U V ⧸ (boundary2 M P U V).range
/-- The first component retains all original local cycle values. -/
noncomputable def cycleLeft2 : Z2 M P U V →+ CoverCohomology.Z2 M P U where
  toFun z := ⟨z.1.1,congrArg Prod.fst z.2⟩
  map_zero' := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl
/-- The second component retains all original local cycle values. -/
noncomputable def cycleRight2 : Z2 M P U V →+ CoverCohomology.Z2 M P V where
  toFun z := ⟨z.1.2,congrArg Prod.snd z.2⟩
  map_zero' := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl
/-- Component classes are the entire local H2 classes. -/
noncomputable def cycleClasses2 : Z2 M P U V →+
    CoverCohomology.H2 M P U × CoverCohomology.H2 M P V :=
  ((QuotientAddGroup.mk' (CoverCohomology.boundary2 M P U).range).comp (cycleLeft2 M P U V)).prod
    ((QuotientAddGroup.mk' (CoverCohomology.boundary2 M P V).range).comp (cycleRight2 M P U V))
/-- Every local-pair boundary has both component classes zero. -/
theorem cycle_classes_boundary2 (b : RelativeCover.C1 M U P × RelativeCover.C1 M V P) :
    cycleClasses2 M P U V (boundary2 M P U V b) = 0 := by
  apply Prod.ext
  · change (QuotientAddGroup.mk (CoverCohomology.boundary2 M P U b.1) :
      CoverCohomology.H2 M P U) = 0
    rw [QuotientAddGroup.eq_zero_iff]
    exact ⟨b.1,rfl⟩
  · change (QuotientAddGroup.mk (CoverCohomology.boundary2 M P V b.2) :
      CoverCohomology.H2 M P V) = 0
    rw [QuotientAddGroup.eq_zero_iff]
    exact ⟨b.2,rfl⟩
/-- Full local-pair H2 maps to both entire component H2 groups. -/
noncomputable def componentH2 : H2 M P U V →+
    CoverCohomology.H2 M P U × CoverCohomology.H2 M P V :=
  QuotientAddGroup.lift _ (cycleClasses2 M P U V) (by
    rintro z ⟨b,rfl⟩
    exact cycle_classes_boundary2 M P U V b)
/-- The component comparison retains all original representative values. -/
theorem component_h2_mk (z : Z2 M P U V) :
    componentH2 M P U V (QuotientAddGroup.mk z) =
      (QuotientAddGroup.mk (cycleLeft2 M P U V z),
        QuotientAddGroup.mk (cycleRight2 M P U V z)) := rfl
/-- Every pair of local cohomology classes is represented by a full local-pair cycle. -/
theorem component_h2_surjective : Function.Surjective (componentH2 M P U V) := by
  rintro ⟨a,b⟩
  obtain ⟨u,rfl⟩ := QuotientAddGroup.mk'_surjective (CoverCohomology.boundary2 M P U).range a
  obtain ⟨v,rfl⟩ := QuotientAddGroup.mk'_surjective (CoverCohomology.boundary2 M P V).range b
  let z : Z2 M P U V := ⟨(u.1,v.1),Prod.ext u.2 v.2⟩
  exact ⟨QuotientAddGroup.mk z,rfl⟩
/-- Zero component classes mean exactly an original local-pair boundary. -/
theorem component_h2_kernel (x : H2 M P U V) :
    componentH2 M P U V x = 0 → x = 0 := by
  induction x using QuotientAddGroup.induction_on with
  | H z =>
    intro hz
    have hu := congrArg Prod.fst hz
    have hv := congrArg Prod.snd hz
    obtain ⟨a,ha⟩ := (CoverCohomology.h2_eq_zero_iff M P U (cycleLeft2 M P U V z)).mp hu
    obtain ⟨b,hb⟩ := (CoverCohomology.h2_eq_zero_iff M P V (cycleRight2 M P U V z)).mp hv
    rw [QuotientAddGroup.eq_zero_iff]
    refine ⟨(a,b),Subtype.ext ?_⟩
    exact Prod.ext (congrArg Subtype.val ha) (congrArg Subtype.val hb)
/-- Distinct local-pair H2 classes remain distinct under the component comparison. -/
theorem component_h2_injective : Function.Injective (componentH2 M P U V) := by
  intro x y h
  apply sub_eq_zero.mp
  apply component_h2_kernel M P U V
  rw [map_sub,h,sub_self]
/-- Native second cohomology of the local pair is the full product, in both directions. -/
noncomputable def secondComponentEquiv : H2 M P U V ≃+
    CoverCohomology.H2 M P U × CoverCohomology.H2 M P V :=
  AddEquiv.ofBijective (componentH2 M P U V)
    ⟨component_h2_injective M P U V,component_h2_surjective M P U V⟩
/-- The second short segment uses the entire original local-pair differentials. -/
noncomputable def secondShortComplex : ShortComplex Ab where
  X₁ := AddCommGrpCat.of (RelativeCover.C1 M U P × RelativeCover.C1 M V P)
  X₂ := AddCommGrpCat.of (RelativeCover.C2 M U P × RelativeCover.C2 M V P)
  X₃ := AddCommGrpCat.of (RelativeCover.C3 M U P × RelativeCover.C3 M V P)
  f := AddCommGrpCat.ofHom (RelativeCover.pairD1 M P U V)
  g := AddCommGrpCat.ofHom (RelativeCover.pairD2 M P U V)
  zero := by
    apply AddCommGrpCat.hom_ext; apply AddMonoidHom.ext
    intro b
    exact (boundary2 M P U V b).2
/-- The local-pair second segment is degree two of the accepted native pair complex. -/
theorem second_eq_sc : secondShortComplex M P U V = (RelativeCover.pairComplex M P U V).sc 2 := by
  have hprev : (ComplexShape.up ℕ).prev 2 = 1 := by simp
  simp [HomologicalComplex.sc,HomologicalComplex.shortComplexFunctor,
    HomologicalComplex.shortComplexFunctor',RelativeCover.pairComplex,
    RelativeCover.pairObject,RelativeCover.pairDifferential,CochainComplex.of,
    secondShortComplex,hprev]
  rw [hprev]
/-- The explicit pair segment comparison preserves every middle original value. -/
noncomputable def secondNormalizedIso : (RelativeCover.pairComplex M P U V).sc' 1 2 3 ≅
    secondShortComplex M P U V :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) (by
    change 𝟙 _ ≫ _ = (RelativeCover.pairComplex M P U V).d 1 2 ≫ 𝟙 _
    rw [Category.comp_id,Category.id_comp]
    simp [RelativeCover.pairComplex,CochainComplex.of,RelativeCover.pairDifferential,
      secondShortComplex]) (by
    change 𝟙 _ ≫ _ = (RelativeCover.pairComplex M P U V).d 2 3 ≫ 𝟙 _
    rw [Category.comp_id,Category.id_comp]
    simp [RelativeCover.pairComplex,CochainComplex.of,RelativeCover.pairDifferential,
      secondShortComplex])
/-- The native pair segment comparison retains the same entire cochain. -/
noncomputable def secondShortIso : (RelativeCover.pairComplex M P U V).sc 2 ≅
    secondShortComplex M P U V :=
  (RelativeCover.pairComplex M P U V).isoSc' 1 2 3 (by simp) (by simp) ≪≫
    secondNormalizedIso M P U V
/-- Native homology of the full pair is the same explicit quotient with its cochain comparison. -/
noncomputable def secondHomologyIso : (RelativeCover.pairComplex M P U V).homology 2 ≅
    AddCommGrpCat.of (H2 M P U V) :=
  ShortComplex.homologyMapIso (secondShortIso M P U V) ≪≫
    (secondShortComplex M P U V).abHomologyIso
/-- The native second homology has the complete two-component comparison. -/
noncomputable def nativeSecondProductIso : (RelativeCover.pairComplex M P U V).homology 2 ≅
    AddCommGrpCat.of (CoverCohomology.H2 M P U × CoverCohomology.H2 M P V) :=
  secondHomologyIso M P U V ≪≫ (secondComponentEquiv M P U V).toAddCommGrpIso

end CoverPairCohomology
end AAT.AG.RelativeRepairComposition
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
