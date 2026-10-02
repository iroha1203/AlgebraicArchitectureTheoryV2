import ResearchLean.AG.RelativeRepairComposition.ClosedRegions

/-!
# The relative complex with supported degree-one corrections

Every group is a subgroup of the original coefficient family. The differential
is the original differential with its codomain restricted by closed incidence.
In degree zero we retain the entire inverse image of the supported group inside
the kernel of restriction to the fixed vertices.

This constructs the relative/support complex and its actual existence obstruction
in G-130 A and n1017 §2.2・2.5.

## Implementation notes

Subgroups of the original cochains retain their original values and identify the
complex directly with the actual-repair coordinates. Supplying an abstract complex
instead would leave its correspondence to the original differential unproved.
Degree zero is the inverse image inside the fixed-vertex kernel: fixing each
endpoint of every forbidden edge would discard permitted reidentifications with
zero coboundary on that edge. Native Mathlib homology is connected to the same
kernel/image quotient, so no separate analogue of cohomology is introduced.
-/

namespace AAT.AG.RelativeRepairComposition
open CategoryTheory TransportCoherence AbelianLiftingObstruction
universe uG uA
variable {K : FiniteTransportPresentation.{uG}}

namespace RelativeComplex
variable (M : LocalCoefficients.{uG,uA} K) (P : ClosedRegion K)
variable (candidates allowed : Set (EdgeName (K := K)))

/-- Original vertex cochains vanishing on the fixed vertices. -/
abbrev relativeC0 := (ClosedRegion.r0 M P).ker
/-- Original edge cochains vanishing on the fixed edges. -/
abbrev relativeC1 := (ClosedRegion.r1 M P).ker
/-- Original face cochains vanishing on the fixed faces. -/
abbrev relativeC2 := (ClosedRegion.r2 M P).ker
/-- Original triple cochains vanishing on the fixed triples. -/
abbrev relativeC3 := (ClosedRegion.r3 M P).ker

/-- API: restriction is zero precisely when all selected original values vanish. -/
theorem family_restrict_eq_zero {I : Type*} (A : I → Type*) [∀ i, AddCommGroup (A i)]
    (s : Set I) (b : ∀ i, A i) : Family.restrict A s b = 0 ↔ ∀ i ∈ s, b i = 0 := by
  constructor
  · intro h i hi
    exact congrFun h ⟨i, hi⟩
  · intro h
    funext i
    exact h i.1 i.2

/-- Degree one retains precisely the fixed-part and forbidden-candidate zero conditions. -/
def C1Group : AddSubgroup (AbelianLiftingObstruction.C1 M) where
  carrier := {h | ∀ e ∈ fixedEdgesForRange P.edges candidates allowed, h e = 0}
  zero_mem' := by intro e _; rfl
  add_mem' := by intro h k hh hk e he; simp [hh e he, hk e he]
  neg_mem' := by intro h hh e he; simp [hh e he]

/-- Membership API for supported original edge cochains. -/
theorem mem_C1Group (h : AbelianLiftingObstruction.C1 M) :
    h ∈ C1Group M P candidates allowed ↔
      ∀ e ∈ fixedEdgesForRange P.edges candidates allowed, h e = 0 := Iff.rfl

/-- Supported cochains lie in the kernel of restriction to the fixed part. -/
theorem C1Group_le_relativeC1 : C1Group M P candidates allowed ≤ relativeC1 M P := by
  intro h hh
  apply (family_restrict_eq_zero _ _ _).mpr
  intro e he
  exact hh e (Or.inl he)

/-- Allowed vertices fix P and have their original d0 in the supported edge group. -/
def C0Group : AddSubgroup (AbelianLiftingObstruction.C0 M) :=
  relativeC0 M P ⊓ (C1Group M P candidates allowed).comap (d0Hom M)

/-- Membership API for the entire permitted vertex-label group. -/
theorem mem_C0Group (b : AbelianLiftingObstruction.C0 M) :
    b ∈ C0Group M P candidates allowed ↔
      (∀ v ∈ P.vertices, b v = 0) ∧ d0 M b ∈ C1Group M P candidates allowed := by
  change (Family.restrict M.A P.vertices b = 0 ∧
    d0 M b ∈ C1Group M P candidates allowed) ↔ _
  rw [family_restrict_eq_zero]

/-- Each allowed label has supported coboundary. -/
theorem C0Group_d0_mem (b : C0Group M P candidates allowed) :
    d0 M b.1 ∈ C1Group M P candidates allowed := b.2.2

/-- Destructor API: every permitted vertex label vanishes on the fixed part. -/
theorem C0Group_le_relativeC0 : C0Group M P candidates allowed ≤ relativeC0 M P :=
  fun _ hb => hb.1

/-- Closure makes the original d0 preserve the relative kernel. -/
theorem d0_mem_relative (b : relativeC0 M P) : d0 M b.1 ∈ relativeC1 M P := by
  change ClosedRegion.r1 M P (d0 M b.1) = 0
  rw [ClosedRegion.r_d0, b.2, map_zero]

/-- Closure makes the original d1 preserve the relative kernel. -/
theorem d1_mem_relative (h : relativeC1 M P) : d1 M h.1 ∈ relativeC2 M P := by
  change ClosedRegion.r2 M P (d1 M h.1) = 0
  rw [ClosedRegion.r_d1, h.2, map_zero]

/-- Closure makes the original d2 preserve the relative kernel. -/
theorem d2_mem_relative (c : relativeC2 M P) : d2 M c.1 ∈ relativeC3 M P := by
  change ClosedRegion.r3 M P (d2 M c.1) = 0
  rw [ClosedRegion.r_d2, c.2, map_zero]

/-- With every candidate permitted, degree one is precisely the relative kernel. -/
theorem C1Group_all : C1Group M P candidates candidates = relativeC1 M P := by
  ext h
  rw [mem_C1Group]
  change (∀ e ∈ fixedEdgesForRange P.edges candidates candidates, h e = 0) ↔
    Family.restrict (fun e : EdgeName (K := K) => M.A e.2.1) P.edges h = 0
  rw [family_restrict_eq_zero]
  simp [fixedEdgesForRange]

/-- With all candidates permitted, degree zero is precisely the relative kernel. -/
theorem C0Group_all : C0Group M P candidates candidates = relativeC0 M P := by
  ext b
  constructor
  · intro hb; exact hb.1
  · intro hb
    refine ⟨hb, ?_⟩
    rw [C1Group_all]
    exact d0_mem_relative M P ⟨b, hb⟩

/-- The same d0 with supported codomain, retaining every allowed vertex label. -/
def d0Supported : C0Group M P candidates allowed →+ C1Group M P candidates allowed where
  toFun b := ⟨d0 M b.1, C0Group_d0_mem M P candidates allowed b⟩
  map_zero' := Subtype.ext (map_zero (d0Hom M))
  map_add' b c := Subtype.ext (map_add (d0Hom M) b.1 c.1)

/-- The same d1 with relative codomain, justified by closed restriction. -/
noncomputable def d1Supported : C1Group M P candidates allowed →+ relativeC2 M P where
  toFun h := ⟨d1 M h.1, d1_mem_relative M P
    ⟨h.1, C1Group_le_relativeC1 M P candidates allowed h.2⟩⟩
  map_zero' := Subtype.ext (map_zero (d1Hom M))
  map_add' h k := Subtype.ext (map_add (d1Hom M) h.1 k.1)

/-- The same d2 on the relative second and third groups. -/
noncomputable def d2Relative : relativeC2 M P →+ relativeC3 M P where
  toFun c := ⟨d2 M c.1, d2_mem_relative M P c⟩
  map_zero' := Subtype.ext (map_zero (d2Hom M))
  map_add' c d := Subtype.ext (map_add (d2Hom M) c.1 d.1)

/-- Supported d1 d0 is zero because it is the same original composite. -/
theorem d1Supported_d0Supported (b : C0Group M P candidates allowed) :
    d1Supported M P candidates allowed (d0Supported M P candidates allowed b) = 0 :=
  Subtype.ext (d1_d0 M b.1)

/-- Relative d2 d1 is zero because it is the same original composite. -/
theorem d2Relative_d1Supported (h : C1Group M P candidates allowed) :
    d2Relative M P (d1Supported M P candidates allowed h) = 0 :=
  Subtype.ext (d2_d1 M h.1)

/-- Degree-zero cohomology retains the original stabilizer labels. -/
abbrev H0 := (d0Supported M P candidates allowed).ker
/-- First cocycles in the supported group. -/
noncomputable abbrev Z1 := (d1Supported M P candidates allowed).ker
/-- Second cocycles in the relative group. -/
noncomputable abbrev Z2 := (d2Relative M P).ker

/-- The same supported vertex boundaries regarded as cocycles. -/
noncomputable def d0ToZ1 : C0Group M P candidates allowed →+ Z1 M P candidates allowed where
  toFun b := ⟨d0Supported M P candidates allowed b, d1Supported_d0Supported M P candidates allowed b⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' b c := Subtype.ext (map_add _ b c)

/-- The same supported face boundaries regarded as relative cocycles. -/
noncomputable def d1ToZ2 : C1Group M P candidates allowed →+ Z2 M P where
  toFun h := ⟨d1Supported M P candidates allowed h, d2Relative_d1Supported M P candidates allowed h⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' h k := Subtype.ext (map_add _ h k)

/-- Supported first cohomology is the quotient of these cycles by these boundaries. -/
abbrev H1 := Z1 M P candidates allowed ⧸ (d0ToZ1 M P candidates allowed).range
/-- Supported second cohomology is the quotient of the relative cycles by supported boundaries. -/
abbrev H2 := Z2 M P ⧸ (d1ToZ2 M P candidates allowed).range

/-- A supported H1 class vanishes exactly when the same vertex coboundary represents it. -/
theorem h1_eq_zero_iff (z : Z1 M P candidates allowed) :
    (QuotientAddGroup.mk z : H1 M P candidates allowed) = 0 ↔
      ∃ b, d0ToZ1 M P candidates allowed b = z := by
  rw [QuotientAddGroup.eq_zero_iff, AddMonoidHom.mem_range]

/-- A relative H2 class vanishes exactly when the same supported face coboundary represents it. -/
theorem h2_eq_zero_iff (z : Z2 M P) :
    (QuotientAddGroup.mk z : H2 M P candidates allowed) = 0 ↔
      ∃ h, d1ToZ2 M P candidates allowed h = z := by
  rw [QuotientAddGroup.eq_zero_iff, AddMonoidHom.mem_range]

/-- The degree-one segment of the supported complex, in native abelian groups. -/
noncomputable def firstShortComplex : ShortComplex Ab where
  X₁ := AddCommGrpCat.of (C0Group M P candidates allowed)
  X₂ := AddCommGrpCat.of (C1Group M P candidates allowed)
  X₃ := AddCommGrpCat.of (relativeC2 M P)
  f := AddCommGrpCat.ofHom (d0Supported M P candidates allowed)
  g := AddCommGrpCat.ofHom (d1Supported M P candidates allowed)
  zero := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    exact d1Supported_d0Supported M P candidates allowed

/-- The degree-two segment, with precisely the supported boundaries. -/
noncomputable def secondShortComplex : ShortComplex Ab where
  X₁ := AddCommGrpCat.of (C1Group M P candidates allowed)
  X₂ := AddCommGrpCat.of (relativeC2 M P)
  X₃ := AddCommGrpCat.of (relativeC3 M P)
  f := AddCommGrpCat.ofHom (d1Supported M P candidates allowed)
  g := AddCommGrpCat.ofHom (d2Relative M P)
  zero := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    exact d2Relative_d1Supported M P candidates allowed

/-- Original relative groups with supported degrees zero and one, zero above degree three. -/
def cochainObject : ℕ → Ab
  | 0 => AddCommGrpCat.of (C0Group M P candidates allowed)
  | 1 => AddCommGrpCat.of (C1Group M P candidates allowed)
  | 2 => AddCommGrpCat.of (relativeC2 M P)
  | 3 => AddCommGrpCat.of (relativeC3 M P)
  | _ => AddCommGrpCat.of PUnit

/-- The original three differentials with their relative codomains. -/
noncomputable def cochainDifferential : ∀ n : ℕ,
    cochainObject M P candidates allowed n ⟶ cochainObject M P candidates allowed (n + 1)
  | 0 => AddCommGrpCat.ofHom (d0Supported M P candidates allowed)
  | 1 => AddCommGrpCat.ofHom (d1Supported M P candidates allowed)
  | 2 => AddCommGrpCat.ofHom (d2Relative M P)
  | _ + 3 => 0

/-- The supported relative groups and maps form a native four-term cochain complex. -/
noncomputable def cochainComplex : CochainComplex Ab ℕ :=
  CochainComplex.of (cochainObject M P candidates allowed)
    (cochainDifferential M P candidates allowed) (by
      intro n
      cases n with
      | zero => exact (firstShortComplex M P candidates allowed).zero
      | succ n =>
        cases n with
        | zero => exact (secondShortComplex M P candidates allowed).zero
        | succ n => cases n <;> rfl)

/-- The explicit H1 quotient is native homology of the same degree-one segment. -/
noncomputable def firstHomologyIso :
    (firstShortComplex M P candidates allowed).homology ≅
      AddCommGrpCat.of (H1 M P candidates allowed) :=
  (firstShortComplex M P candidates allowed).abHomologyIso

/-- The explicit H2 quotient is native homology of the same degree-two segment. -/
noncomputable def secondHomologyIso :
    (secondShortComplex M P candidates allowed).homology ≅
      AddCommGrpCat.of (H2 M P candidates allowed) :=
  (secondShortComplex M P candidates allowed).abHomologyIso

/-- The native degree-one segment has exactly the specified supported maps. -/
theorem firstShortComplex_eq_sc : firstShortComplex M P candidates allowed =
    (cochainComplex M P candidates allowed).sc 1 := by
  have hprev : (ComplexShape.up ℕ).prev 1 = 0 := by simp
  simp [HomologicalComplex.sc, HomologicalComplex.shortComplexFunctor,
    HomologicalComplex.shortComplexFunctor', cochainComplex, cochainObject,
    cochainDifferential, CochainComplex.of, firstShortComplex, hprev]
  rw [hprev]

/-- The native degree-two segment has exactly the specified relative maps. -/
theorem secondShortComplex_eq_sc : secondShortComplex M P candidates allowed =
    (cochainComplex M P candidates allowed).sc 2 := by
  have hprev : (ComplexShape.up ℕ).prev 2 = 1 := by simp
  simp [HomologicalComplex.sc, HomologicalComplex.shortComplexFunctor,
    HomologicalComplex.shortComplexFunctor', cochainComplex, cochainObject,
    cochainDifferential, CochainComplex.of, secondShortComplex, hprev]
  rw [hprev]

/-- Supported H1 is degree-one homology of the native relative complex. -/
noncomputable def firstCochainHomologyIso :
    (cochainComplex M P candidates allowed).homology 1 ≅
      AddCommGrpCat.of (H1 M P candidates allowed) := by
  change ((cochainComplex M P candidates allowed).sc 1).homology ≅ _
  simpa only [← firstShortComplex_eq_sc] using firstHomologyIso M P candidates allowed

/-- Supported H2 is degree-two homology of the native relative complex. -/
noncomputable def secondCochainHomologyIso :
    (cochainComplex M P candidates allowed).homology 2 ≅
      AddCommGrpCat.of (H2 M P candidates allowed) := by
  change ((cochainComplex M P candidates allowed).sc 2).homology ≅ _
  simpa only [← secondShortComplex_eq_sc] using secondHomologyIso M P candidates allowed

/-- The original relative zero-cocycles, without a supported-range parameter. -/
def relativeH0 : AddSubgroup (AbelianLiftingObstruction.C0 M) :=
  relativeC0 M P ⊓ (d0Hom M).ker

/-- Membership API for original relative zero-cocycles. -/
theorem mem_relativeH0 (b : AbelianLiftingObstruction.C0 M) :
    b ∈ relativeH0 M P ↔ b ∈ relativeC0 M P ∧ d0 M b = 0 := Iff.rfl

/-- A supported zero-cocycle is precisely an original relative zero-cocycle. -/
theorem mem_H0_iff (b : C0Group M P candidates allowed) :
    b ∈ H0 M P candidates allowed ↔ d0 M b.1 = 0 := by
  change d0Supported M P candidates allowed b = 0 ↔ _
  constructor
  · exact fun h => congrArg Subtype.val h
  · exact fun h => Subtype.ext h

/-- H0 is independent of the range, preserving the original vertex label exactly. -/
def h0Equiv : H0 M P candidates allowed ≃+ relativeH0 M P where
  toFun b := ⟨b.1.1, (mem_relativeH0 M P _).mpr
    ⟨C0Group_le_relativeC0 M P candidates allowed b.1.2,
      (mem_H0_iff M P candidates allowed b.1).mp b.2⟩⟩
  invFun b := ⟨⟨b.1, ((mem_relativeH0 M P b.1).mp b.2).1, by
    change d0 M b.1 ∈ C1Group M P candidates allowed
    rw [show d0 M b.1 = 0 from ((mem_relativeH0 M P b.1).mp b.2).2]
    exact (C1Group M P candidates allowed).zero_mem⟩,
    (mem_H0_iff M P candidates allowed _).mpr ((mem_relativeH0 M P b.1).mp b.2).2⟩
  left_inv _ := Subtype.ext (Subtype.ext rfl)
  right_inv _ := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl

/-- The H0 comparison retains the same actual vertex label. -/
theorem h0Equiv_label (b : H0 M P candidates allowed) :
    (h0Equiv M P candidates allowed b).1 = b.1.1 := rfl

end RelativeComplex

namespace ActualRelative
open TransportCoherence.Arbitrary
universe uE uB uD vE vB vD
variable {E : Type uE} {B : Type uB} {D : Type uD}
variable [Category.{vE} E] [Category.{vB} B] [Category.{vD} D]
variable {p : E ⥤ B} {q : B ⥤ D}
variable (T : OriginalTowerPresentation K p q) (P : ClosedRegion K)
variable (candidates allowed : Set (EdgeName (K := K)))

/-- The degree-one subgroup is exactly the subgroup used for independent actual repairs. -/
theorem supportedC1_eq :
    supportedC1 T (fixedEdgesForRange P.edges candidates allowed) =
      RelativeComplex.C1Group T.toTower.localCoefficients P candidates allowed := rfl

/-- The degree-zero subgroup retains exactly the original allowed reidentifications. -/
theorem supportedC0_eq :
    supportedC0 T P.vertices (fixedEdgesForRange P.edges candidates allowed) =
      RelativeComplex.C0Group T.toTower.localCoefficients P candidates allowed := by
  ext b
  rw [mem_supportedC0, RelativeComplex.mem_C0Group, supportedC1_eq]

/-- A coherent original reference face has zero actual full-kernel defect. -/
theorem defect_zero_of_face (f : K.TwoCell)
    (hf : T.toTower.upper.pathLift (K.twoLeft f) ≫ FiberAut.hom (T.comparator f) =
      T.toTower.upper.pathLift (K.twoRight f)) : T.toTower.defect f = 0 := by
  have hraw : rawFaceDefect T.toTower.toTransportData 1 f = 1 := by
    apply (rawFaceDefect_eq_one_iff_coherent T.toTower.toTransportData 1 f).mpr
    simpa only [Arbitrary.reselectedPathLift_one] using hf
  have hkernel : T.toTower.faceDefect f = 1 := by
    apply kernelInclusion_injective p q _
    rw [T.toTower.faceDefect_eq_raw, hraw, map_one]
  change Additive.ofMul (T.toTower.faceDefect f) = 0
  rw [hkernel]
  rfl

/-- Actual reference coherence on P makes the same actual defect relative. -/
theorem defect_mem_relative
    (hfixed : ∀ f ∈ P.faces,
      T.toTower.upper.pathLift (K.twoLeft f) ≫ FiberAut.hom (T.comparator f) =
        T.toTower.upper.pathLift (K.twoRight f)) :
    T.toTower.defect ∈ RelativeComplex.relativeC2 T.toTower.localCoefficients P := by
  apply (RelativeComplex.family_restrict_eq_zero _ _ _).mpr
  exact fun f hf => defect_zero_of_face T f (hfixed f hf)

/-- The actual relative defect is a cocycle by the same authored three-cell equations. -/
noncomputable def obstructionCocycle
    (hfixed : ∀ f ∈ P.faces,
      T.toTower.upper.pathLift (K.twoLeft f) ≫ FiberAut.hom (T.comparator f) =
        T.toTower.upper.pathLift (K.twoRight f))
    (hsyzygy : ∀ s : K.ThreeCell, AuthoredSyzygy T.toTower.toTransportData 1
      (K.threeLeft s) (K.threeRight s)) : RelativeComplex.Z2 T.toTower.localCoefficients P :=
  ⟨⟨T.toTower.defect, defect_mem_relative T P hfixed⟩,
    Subtype.ext (T.toTower.defect_cocycle hsyzygy)⟩

/-- The class of the same actual defect in the supported relative complex. -/
noncomputable def obstructionClass
    (hfixed : ∀ f ∈ P.faces,
      T.toTower.upper.pathLift (K.twoLeft f) ≫ FiberAut.hom (T.comparator f) =
        T.toTower.upper.pathLift (K.twoRight f))
    (hsyzygy : ∀ s : K.ThreeCell, AuthoredSyzygy T.toTower.toTransportData 1
      (K.threeLeft s) (K.threeRight s)) :
    RelativeComplex.H2 T.toTower.localCoefficients P candidates allowed :=
  QuotientAddGroup.mk (obstructionCocycle T P hfixed hsyzygy)

/-- The actual obstruction class is represented by its complete actual relative defect cocycle. -/
theorem obstructionClass_eq_mk
    (hfixed : ∀ f ∈ P.faces,
      T.toTower.upper.pathLift (K.twoLeft f) ≫ FiberAut.hom (T.comparator f) =
        T.toTower.upper.pathLift (K.twoRight f))
    (hsyzygy : ∀ s : K.ThreeCell, AuthoredSyzygy T.toTower.toTransportData 1
      (K.threeLeft s) (K.threeRight s)) :
    obstructionClass T P candidates allowed hfixed hsyzygy =
      (QuotientAddGroup.mk (obstructionCocycle T P hfixed hsyzygy) :
        RelativeComplex.H2 T.toTower.localCoefficients P candidates allowed) := rfl

/-- The actual supported repairs exist exactly when their relative obstruction vanishes. -/
theorem repair_nonempty_iff_obstruction_zero
    (hfixed : ∀ f ∈ P.faces,
      T.toTower.upper.pathLift (K.twoLeft f) ≫ FiberAut.hom (T.comparator f) =
        T.toTower.upper.pathLift (K.twoRight f))
    (hsyzygy : ∀ s : K.ThreeCell, AuthoredSyzygy T.toTower.toTransportData 1
      (K.threeLeft s) (K.threeRight s)) :
    Nonempty (SupportedRepair T (fixedEdgesForRange P.edges candidates allowed)) ↔
      obstructionClass T P candidates allowed hfixed hsyzygy = 0 := by
  rw [supported_repair_nonempty_iff]
  change _ ↔ (QuotientAddGroup.mk (obstructionCocycle T P hfixed hsyzygy) :
    RelativeComplex.H2 T.toTower.localCoefficients P candidates allowed) = 0
  rw [RelativeComplex.h2_eq_zero_iff]
  constructor
  · rintro ⟨h, hh, hd⟩
    refine ⟨-⟨h, hh⟩, ?_⟩
    apply Subtype.ext; apply Subtype.ext
    change d1 T.toTower.localCoefficients (-h) = T.toTower.defect
    change (d1Hom T.toTower.localCoefficients) (-h) = _
    rw [map_neg, show (d1Hom T.toTower.localCoefficients) h = -T.toTower.defect from hd,
      neg_neg]
  · rintro ⟨h, hh⟩
    have hd : d1 T.toTower.localCoefficients h.1 = T.toTower.defect :=
      congrArg (fun c => c.1.1) hh
    refine ⟨-h.1, (RelativeComplex.C1Group _ P candidates allowed).neg_mem h.2, ?_⟩
    change (d1Hom T.toTower.localCoefficients) (-h.1) = -T.toTower.defect
    rw [map_neg, show (d1Hom T.toTower.localCoefficients) h.1 = T.toTower.defect from hd]

end ActualRelative
end AAT.AG.RelativeRepairComposition

#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
