import Formal.AG.LawAlgebra.ClosedEquationalGeometryLegacy
import Formal.AG.LawAlgebra.StandardSchemeFiniteExample
import Formal.AG.LawAlgebra.FiniteExamples

noncomputable section

namespace AAT.AG.LawAlgebra.FiniteExamples.ClosedEquationalGeometry

open CategoryTheory Opposite
open AlgebraicGeometry
open scoped AlgebraicGeometry
open AAT.AG.FiniteModel
open AAT.AG.LawAlgebra.FiniteExamples.RingedSite.FiniteModel
open AAT.AG.LawAlgebra.FiniteExamples.StandardArchitectureScheme

/-!
# Legacy compatibility finite examples for closed equational geometry

This compatibility leaf is intentionally excluded from the standard
`Formal.AG.LawAlgebra` aggregate. It checks that equation-generated legacy
displays still drive the older closed-equational examples while the standard
LawAlgebra entrypoint remains equation-native.

## Implementation notes

The first SD9 fixture keeps the existing two-chart Scheme and compares the concrete equations
`x - 1` and `x + 1`. The second fixture retargets the same context geometry, raw relation, and
underlying Scheme to a two-law universe so that the required and all-selected ideals can be
compared without changing the ambient object.

The positive and negative firing theorems use explicit evaluations, basic opens, and Scheme
morphisms. Degenerate witnesses based only on the zero or unit ideal, an empty Scheme, or an
identity morphism were rejected. Local firing proofs unfold the concrete fixture constructors
only to calculate their generators; downstream use is through the named characterization and
comparison theorems.
-/

/-! ## Raw quotient coordinates -/

private noncomputable def orientedRawCoordinate
    (W : RingedSite.FiniteModel.site.category) :
    rawSystem.rawAlgebra W :=
  (rawSystem.relationFamily W).quotientMap
    (MvPolynomial.C (RawPresheaf.gauge W) * MvPolynomial.X ())

private theorem orientedRawCoordinate_restrict
    {source target : RingedSite.FiniteModel.site.category} (f : source ⟶ target) :
    (rawSystem.restrictionStable f).quotientDesc
        (orientedRawCoordinate target) =
      orientedRawCoordinate source := by
  rw [orientedRawCoordinate, orientedRawCoordinate,
    RestrictionStableStructuralRelations.quotientDesc_mk,
    rawSystem_restrictionStable, RawPresheaf.system_restriction,
    map_mul]
  erw [(RawPresheaf.coordinateRestriction f).polynomialMap_C]
  erw [(RawPresheaf.coordinateRestriction f).polynomialMap_X]
  have hcoeff :
      RawPresheaf.gauge target *
          (RawPresheaf.gauge source * RawPresheaf.gauge target) =
        RawPresheaf.gauge source := by
    calc
      RawPresheaf.gauge target *
          (RawPresheaf.gauge source * RawPresheaf.gauge target) =
          RawPresheaf.gauge source *
            (RawPresheaf.gauge target * RawPresheaf.gauge target) := by ring
      _ = RawPresheaf.gauge source := by
        rw [RawPresheaf.gauge_sq, mul_one]
  change
    (rawSystem.relationFamily source).quotientMap
        (MvPolynomial.C (RawPresheaf.gauge target) *
          (MvPolynomial.C
            (RawPresheaf.gauge source * RawPresheaf.gauge target) *
              MvPolynomial.X ())) =
      (rawSystem.relationFamily source).quotientMap
        (MvPolynomial.C (RawPresheaf.gauge source) * MvPolynomial.X ())
  calc
    (rawSystem.relationFamily source).quotientMap
        (MvPolynomial.C (RawPresheaf.gauge target) *
          (MvPolynomial.C
            (RawPresheaf.gauge source * RawPresheaf.gauge target) *
              MvPolynomial.X ())) =
      (rawSystem.relationFamily source).quotientMap
        (MvPolynomial.C
            (RawPresheaf.gauge target *
              (RawPresheaf.gauge source * RawPresheaf.gauge target)) *
          MvPolynomial.X ()) := by
        congr 1
        simp only [MvPolynomial.C_mul]
        ring
    _ = _ := by rw [hcoeff]

private theorem base_ctx_ne_left_ctx : base.ctx ≠ RawPresheaf.left.ctx := by
  intro h
  have heq := congrArg
    (fun W : Site.ArchitectureContext corePackage.object =>
      (⟨W.Extension, W.extension⟩ : Sigma fun T : Type => T)) h
  injection heq with _ hindex
  exact TwoPatchContextIndex.noConfusion hindex

private theorem gauge_base : RawPresheaf.gauge base = 1 := by
  unfold RawPresheaf.gauge
  rw [if_neg base_ctx_ne_left_ctx]

private theorem rawRestriction_id (W : RingedSite.FiniteModel.site.category)
    (x : rawSystem.rawAlgebra W) :
    (rawSystem.restrictionStable (𝟙 W)).quotientDesc x = x := by
  have h := congrArg (fun q => q x) (rawSystem.quotientDesc_id W)
  simpa using h

private theorem rawRestriction_comp
    {W₀ W₁ W₂ : RingedSite.FiniteModel.site.category}
    (f : W₀ ⟶ W₁) (g : W₁ ⟶ W₂)
    (x : rawSystem.rawAlgebra W₂) :
    (rawSystem.restrictionStable (f ≫ g)).quotientDesc x =
      (rawSystem.restrictionStable f).quotientDesc
        ((rawSystem.restrictionStable g).quotientDesc x) := by
  have h := congrArg (fun q => q x) (rawSystem.quotientDesc_comp f g)
  simpa [RingHom.comp_apply] using h

/-! ## Weak and strong semantic equation cores -/

/-- The singleton weak law core generated by the oriented equation `x - 1`. -/
noncomputable def weakLawEquationCore :
    SemanticLawEquationWitnessIdealCore RingedSite.FiniteModel.site where
  Observable W := rawSystem.rawAlgebra W
  observableCommRing W := inferInstance
  restrict f := (rawSystem.restrictionStable f).quotientDesc
  restrict_id := rawRestriction_id
  restrict_comp := rawRestriction_comp
  violationWitness W _ a :=
    match a with
    | FiniteAtom.componentA => orientedRawCoordinate W - 1
    | _ => 0
  violationWitness_restrict := by
    intro source target f lawIndex atom
    cases atom <;>
      simp only [map_sub, map_one, map_zero, orientedRawCoordinate_restrict]
  supportAtom := FiniteAtom.componentA
  supportLawIndex := PUnit.unit
  supportLawIndex_required := RingedSite.FiniteModel.site_equation_required PUnit.unit

/-- The singleton strong law core generated by `x - 1` and `x + 1`. -/
noncomputable def strongLawEquationCore :
    SemanticLawEquationWitnessIdealCore RingedSite.FiniteModel.site where
  Observable W := rawSystem.rawAlgebra W
  observableCommRing W := inferInstance
  restrict f := (rawSystem.restrictionStable f).quotientDesc
  restrict_id := rawRestriction_id
  restrict_comp := rawRestriction_comp
  violationWitness W _ a :=
    match a with
    | FiniteAtom.componentA => orientedRawCoordinate W - 1
    | FiniteAtom.componentB => orientedRawCoordinate W + 1
    | _ => 0
  violationWitness_restrict := by
    intro source target f lawIndex atom
    cases atom <;>
      simp only [map_sub, map_add, map_one, map_zero, orientedRawCoordinate_restrict]
  supportAtom := FiniteAtom.componentA
  supportLawIndex := PUnit.unit
  supportLawIndex_required := RingedSite.FiniteModel.site_equation_required PUnit.unit

/-- The weak core is identified objectwise with the existing raw quotient presentation. -/
noncomputable def weakSchemeBridge :
    SemanticLawEquationSchemeBridge rawSystem weakLawEquationCore where
  toRawPresentation W := RingEquiv.refl (rawSystem.rawAlgebra W)

/-- The strong core is identified objectwise with the existing raw quotient presentation. -/
noncomputable def strongSchemeBridge :
    SemanticLawEquationSchemeBridge rawSystem strongLawEquationCore where
  toRawPresentation W := RingEquiv.refl (rawSystem.rawAlgebra W)

/-- The weak identity bridge is restriction-natural and uses the canonical presentation. -/
theorem weakSchemeBridge_valid :
    IsSemanticLawEquationSchemeBridge rawSystem
      weakLawEquationCore weakSchemeBridge where
  restriction_natural := by
    intro source target f x
    have hn := rawSystem.toRingedSite.canonical.naturality f.op
    have ha := congrArg (fun q => q.right x) hn
    change
      (rawSystem.toRingedSite.canonical.app (op source)).right
          ((rawSystem.restrictionStable f).quotientDesc x) =
        (rawSystem.toRingedSite.structureSheaf.val.map f.op).right
          ((rawSystem.toRingedSite.canonical.app (op target)).right x)
    simpa only [CommRingCat.comp_apply,
      RawAmbientRestrictionSystem.toRingedSite_raw] using ha
  presentation_stable W := {
    canonical_isIso := StandardSchemeReading.canonicalComponentIsIso W
  }

/-- The strong identity bridge is restriction-natural and uses the canonical presentation. -/
theorem strongSchemeBridge_valid :
    IsSemanticLawEquationSchemeBridge rawSystem
      strongLawEquationCore strongSchemeBridge where
  restriction_natural := by
    intro source target f x
    have hn := rawSystem.toRingedSite.canonical.naturality f.op
    have ha := congrArg (fun q => q.right x) hn
    change
      (rawSystem.toRingedSite.canonical.app (op source)).right
          ((rawSystem.restrictionStable f).quotientDesc x) =
        (rawSystem.toRingedSite.structureSheaf.val.map f.op).right
          ((rawSystem.toRingedSite.canonical.app (op target)).right x)
    simpa only [CommRingCat.comp_apply,
      RawAmbientRestrictionSystem.toRingedSite_raw] using ha
  presentation_stable W := {
    canonical_isIso := StandardSchemeReading.canonicalComponentIsIso W
  }

/-- Every finite context supplies the canonical presentation used by the weak bridge. -/
theorem weakSchemeBridge_presentationStable
    (W : RingedSite.FiniteModel.site.category) :
    AffineChart.AffineAATChart.SheafifiedChartPresentation rawSystem W :=
  weakSchemeBridge_valid.presentation_stable W

/-- The weak bridge map is a bijection on every finite context. -/
theorem weakSchemeBridge_toSheafifiedSection_bijective
    (W : RingedSite.FiniteModel.site.category) :
    Function.Bijective (weakSchemeBridge.toSheafifiedSection W) :=
  SemanticLawEquationSchemeBridge.toSheafifiedSection_bijective
    rawSystem weakLawEquationCore weakSchemeBridge weakSchemeBridge_valid W

/-- The weak bridge reflects its atom-generated core witness ideal. -/
theorem weakCore_witnessIdeal_reflected
    (W : RingedSite.FiniteModel.site.category) (i : RingedSite.FiniteModel.site.equationSystem.Index) :
    Ideal.comap (weakSchemeBridge.toSheafifiedSection W)
        (Ideal.map (weakSchemeBridge.toSheafifiedSection W)
          (weakLawEquationCore.lawWitnessIdeal W i)) =
      weakLawEquationCore.lawWitnessIdeal W i :=
  semanticCoreLawWitnessIdeal_comap_map rawSystem weakLawEquationCore
    weakSchemeBridge weakSchemeBridge_valid W i

/-- The selected global coordinate on the finite two-chart reference model. -/
noncomputable def baseGlobalCoordinate :
    Γ(twoChartReferenceModel.underlying, ⊤) :=
  twoChartReferenceModel.decoration.coordinateSection rawSystem ()

private theorem weak_componentA_raw_equation :
    weakLawEquationCore.violationWitness base PUnit.unit FiniteAtom.componentA =
      ((rawSystem.relationFamily base).quotientMap (MvPolynomial.X ()) - 1 :
        rawSystem.rawAlgebra base) := by
  simp only [weakLawEquationCore]
  rw [orientedRawCoordinate, gauge_base]
  simp

private theorem strong_componentA_raw_equation :
    strongLawEquationCore.violationWitness base PUnit.unit FiniteAtom.componentA =
      ((rawSystem.relationFamily base).quotientMap (MvPolynomial.X ()) - 1 :
        rawSystem.rawAlgebra base) := by
  simp only [strongLawEquationCore]
  rw [orientedRawCoordinate, gauge_base]
  simp

private theorem strong_componentB_raw_equation :
    strongLawEquationCore.violationWitness base PUnit.unit FiniteAtom.componentB =
      ((rawSystem.relationFamily base).quotientMap (MvPolynomial.X ()) + 1 :
        rawSystem.rawAlgebra base) := by
  simp only [strongLawEquationCore]
  rw [orientedRawCoordinate, gauge_base]
  simp

/-- The weak component-A core equation is the global equation `x - 1`. -/
theorem weakCore_componentA_equation :
    semanticCoreGlobalEquation rawSystem twoChartReferenceModel
        weakLawEquationCore weakSchemeBridge PUnit.unit FiniteAtom.componentA =
      baseGlobalCoordinate - 1 := by
  rw [semanticCoreGlobalEquation]
  change
    (AATReadingDecoration.ofContext rawSystem base).interpretation
      (weakSchemeBridge.toSheafifiedSection base
        (weakLawEquationCore.violationWitness base PUnit.unit
          FiniteAtom.componentA)) =
      (AATReadingDecoration.ofContext rawSystem base).coordinateSection
        rawSystem () - 1
  rw [weak_componentA_raw_equation]
  simp only [SemanticLawEquationSchemeBridge.toSheafifiedSection,
    weakSchemeBridge, RingHom.comp_apply, map_sub, map_one,
    AATReadingDecoration.coordinateSection_apply]
  rfl

/-- Every weak-core atom other than component A carries the zero equation. -/
theorem weakCore_other_equation
    (a : carrier.Atom) (ha : a ≠ FiniteAtom.componentA) :
    semanticCoreGlobalEquation rawSystem twoChartReferenceModel
        weakLawEquationCore weakSchemeBridge PUnit.unit a = 0 := by
  cases a <;> simp_all [semanticCoreGlobalEquation, weakLawEquationCore,
    weakSchemeBridge, SemanticLawEquationSchemeBridge.toSheafifiedSection]

/-- The strong component-A core equation is the global equation `x - 1`. -/
theorem strongCore_componentA_equation :
    semanticCoreGlobalEquation rawSystem twoChartReferenceModel
        strongLawEquationCore strongSchemeBridge PUnit.unit FiniteAtom.componentA =
      baseGlobalCoordinate - 1 := by
  rw [semanticCoreGlobalEquation]
  change
    (AATReadingDecoration.ofContext rawSystem base).interpretation
      (strongSchemeBridge.toSheafifiedSection base
        (strongLawEquationCore.violationWitness base PUnit.unit
          FiniteAtom.componentA)) =
      (AATReadingDecoration.ofContext rawSystem base).coordinateSection
        rawSystem () - 1
  rw [strong_componentA_raw_equation]
  simp only [SemanticLawEquationSchemeBridge.toSheafifiedSection,
    strongSchemeBridge, RingHom.comp_apply, map_sub, map_one,
    AATReadingDecoration.coordinateSection_apply]
  rfl

/-- The strong component-B core equation is the global equation `x + 1`. -/
theorem strongCore_componentB_equation :
    semanticCoreGlobalEquation rawSystem twoChartReferenceModel
        strongLawEquationCore strongSchemeBridge PUnit.unit FiniteAtom.componentB =
      baseGlobalCoordinate + 1 := by
  rw [semanticCoreGlobalEquation]
  change
    (AATReadingDecoration.ofContext rawSystem base).interpretation
      (strongSchemeBridge.toSheafifiedSection base
        (strongLawEquationCore.violationWitness base PUnit.unit
          FiniteAtom.componentB)) =
      (AATReadingDecoration.ofContext rawSystem base).coordinateSection
        rawSystem () + 1
  rw [strong_componentB_raw_equation]
  simp only [SemanticLawEquationSchemeBridge.toSheafifiedSection,
    strongSchemeBridge, RingHom.comp_apply, map_add, map_one,
    AATReadingDecoration.coordinateSection_apply]
  rfl

/-- Every strong-core atom other than components A and B carries the zero equation. -/
theorem strongCore_other_equation
    (a : carrier.Atom)
    (ha : a ≠ FiniteAtom.componentA) (hb : a ≠ FiniteAtom.componentB) :
    semanticCoreGlobalEquation rawSystem twoChartReferenceModel
        strongLawEquationCore strongSchemeBridge PUnit.unit a = 0 := by
  cases a <;> simp_all [semanticCoreGlobalEquation, strongLawEquationCore,
    strongSchemeBridge, SemanticLawEquationSchemeBridge.toSheafifiedSection]

/-- The left chart pulls each weak global equation back to its core witness section. -/
theorem weakCore_leftChart_provenance_fires
    (a : carrier.Atom) :
    ((twoChartReferenceModel.atlas.chart leftIndex).map.appTop ≫
        (AlgebraicGeometry.Scheme.ΓSpecIso
          (SheafifiedSectionRing rawSystem
            (twoChartReferenceModel.atlas.chart leftIndex).context)).hom)
        (semanticCoreGlobalEquation rawSystem twoChartReferenceModel
          weakLawEquationCore weakSchemeBridge PUnit.unit a) =
      weakSchemeBridge.toSheafifiedSection
        (twoChartReferenceModel.atlas.chart leftIndex).context
        (weakLawEquationCore.violationWitness
          (twoChartReferenceModel.atlas.chart leftIndex).context PUnit.unit a) :=
  semanticCoreGlobalEquation_on_chart rawSystem twoChartReferenceModel
    weakLawEquationCore weakSchemeBridge weakSchemeBridge_valid
    leftIndex PUnit.unit a

/-- On the left chart, the bridge image of the weak core ideal is its coordinate span. -/
theorem weakCore_leftChart_witnessIdeal_realization_fires :
    Ideal.map
        (weakSchemeBridge.toSheafifiedSection
          (twoChartReferenceModel.atlas.chart leftIndex).context)
        (weakLawEquationCore.lawWitnessIdeal
          (twoChartReferenceModel.atlas.chart leftIndex).context PUnit.unit) =
      Ideal.span (Set.range (fun a =>
        weakSchemeBridge.toSheafifiedSection
          (twoChartReferenceModel.atlas.chart leftIndex).context
          (weakLawEquationCore.violationWitness
            (twoChartReferenceModel.atlas.chart leftIndex).context
            PUnit.unit a))) :=
  semanticCoreLawWitnessIdeal_map rawSystem weakLawEquationCore weakSchemeBridge
    (twoChartReferenceModel.atlas.chart leftIndex).context PUnit.unit

/-! ## Canonical weak and strong readings -/

/-- The closed-equational reading induced by the weak semantic equation core. -/
noncomputable def weakReading :
    ClosedEquationalLawReading rawSystem twoChartReferenceModel :=
  ClosedEquationalLawReading.ofSemanticCore rawSystem twoChartReferenceModel
    weakLawEquationCore weakSchemeBridge

/-- The closed-equational reading induced by the strong semantic equation core. -/
noncomputable def strongReading :
    ClosedEquationalLawReading rawSystem twoChartReferenceModel :=
  ClosedEquationalLawReading.ofSemanticCore rawSystem twoChartReferenceModel
    strongLawEquationCore strongSchemeBridge

/-- Weak semantic truth is generatorwise vanishing of the weak global equations. -/
@[simp] theorem weakReading_holdsOn_iff
    {T : AlgebraicGeometry.Scheme}
    (s : T ⟶ twoChartReferenceModel.underlying) (i : RingedSite.FiniteModel.site.equationSystem.Index) :
    weakReading.geometric.HoldsOn s i ↔
      ∀ a, s.appTop
        (semanticCoreGlobalEquation rawSystem twoChartReferenceModel
          weakLawEquationCore weakSchemeBridge i a) = 0 :=
  GeometricLawReading.ofSemanticCore_holdsOn rawSystem twoChartReferenceModel
    weakLawEquationCore weakSchemeBridge s i

/-- Strong semantic truth is generatorwise vanishing of the strong global equations. -/
@[simp] theorem strongReading_holdsOn_iff
    {T : AlgebraicGeometry.Scheme}
    (s : T ⟶ twoChartReferenceModel.underlying) (i : RingedSite.FiniteModel.site.equationSystem.Index) :
    strongReading.geometric.HoldsOn s i ↔
      ∀ a, s.appTop
        (semanticCoreGlobalEquation rawSystem twoChartReferenceModel
          strongLawEquationCore strongSchemeBridge i a) = 0 :=
  GeometricLawReading.ofSemanticCore_holdsOn rawSystem twoChartReferenceModel
    strongLawEquationCore strongSchemeBridge s i

/-- The weak reading stores the canonical witness induced by its semantic core. -/
@[simp] theorem weakReading_witness_eq_ofSemanticCore
    (i : RingedSite.FiniteModel.site.equationSystem.Index) (hi : weakReading.closed i) :
    weakReading.witness i hi =
      ClosedEquationalLawWitness.ofSemanticCore rawSystem twoChartReferenceModel
        weakLawEquationCore weakSchemeBridge i :=
  ClosedEquationalLawReading.ofSemanticCore_witness rawSystem
    twoChartReferenceModel weakLawEquationCore weakSchemeBridge i hi

/-- The strong reading stores the canonical witness induced by its semantic core. -/
@[simp] theorem strongReading_witness_eq_ofSemanticCore
    (i : RingedSite.FiniteModel.site.equationSystem.Index) (hi : strongReading.closed i) :
    strongReading.witness i hi =
      ClosedEquationalLawWitness.ofSemanticCore rawSystem twoChartReferenceModel
        strongLawEquationCore strongSchemeBridge i :=
  ClosedEquationalLawReading.ofSemanticCore_witness rawSystem
    twoChartReferenceModel strongLawEquationCore strongSchemeBridge i hi

/-- The weak semantic predicate is stable under base change. -/
theorem weakGeometricReading_valid :
    IsGeometricLawReading rawSystem twoChartReferenceModel weakReading.geometric :=
  GeometricLawReading.ofSemanticCore_valid rawSystem twoChartReferenceModel
    weakLawEquationCore weakSchemeBridge

/-- The strong semantic predicate is stable under base change. -/
theorem strongGeometricReading_valid :
    IsGeometricLawReading rawSystem twoChartReferenceModel strongReading.geometric :=
  GeometricLawReading.ofSemanticCore_valid rawSystem twoChartReferenceModel
    strongLawEquationCore strongSchemeBridge

/-- Every weak witness is compatible with basic-open restriction. -/
theorem weakReading_witnessCompatible :
    IsClosedEquationalWitnessReading rawSystem twoChartReferenceModel weakReading :=
  ClosedEquationalLawReading.ofSemanticCore_witnessCompatible rawSystem
    twoChartReferenceModel weakLawEquationCore weakSchemeBridge

/-- Every strong witness is compatible with basic-open restriction. -/
theorem strongReading_witnessCompatible :
    IsClosedEquationalWitnessReading rawSystem twoChartReferenceModel strongReading :=
  ClosedEquationalLawReading.ofSemanticCore_witnessCompatible rawSystem
    twoChartReferenceModel strongLawEquationCore strongSchemeBridge

/-- The weak reading combines its independently established semantic and witness validity. -/
theorem weakReading_valid :
    IsClosedEquationalLawReading rawSystem twoChartReferenceModel weakReading where
  geometric_stable := weakGeometricReading_valid
  witness_compatible := weakReading_witnessCompatible
  selected_closed := fun _ i _ => Set.mem_univ i
  selected_basicOpen := fun _ _ i =>
    iff_of_true (Set.mem_univ i) (Set.mem_univ i)

/-- The strong reading combines its independently established semantic and witness validity. -/
theorem strongReading_valid :
    IsClosedEquationalLawReading rawSystem twoChartReferenceModel strongReading where
  geometric_stable := strongGeometricReading_valid
  witness_compatible := strongReading_witnessCompatible
  selected_closed := fun _ i _ => Set.mem_univ i
  selected_basicOpen := fun _ _ i =>
    iff_of_true (Set.mem_univ i) (Set.mem_univ i)

/-- The singleton law is closed in the weak reading. -/
theorem weakReading_closed_unit :
    weakReading.closed PUnit.unit :=
  by
    change PUnit.unit ∈ (Set.univ : Set RingedSite.FiniteModel.site.equationSystem.Index)
    simp

/-- Every finite affine context selects the weak law. -/
theorem weakReading_selected
    (V : twoChartReferenceModel.underlying.affineOpens)
    (i : RingedSite.FiniteModel.site.equationSystem.Index) :
    weakReading.selected V i :=
  Set.mem_univ i

/-- Every finite affine context selects the strong law. -/
theorem strongReading_selected
    (V : twoChartReferenceModel.underlying.affineOpens)
    (i : RingedSite.FiniteModel.site.equationSystem.Index) :
    strongReading.selected V i :=
  Set.mem_univ i

/-- The weak core ideal sheaf realizes its bridge image on the left actual chart. -/
theorem weakCore_leftChart_idealSheaf_realization_fires :
    ((lawWitnessIdealSheaf rawSystem twoChartReferenceModel weakReading
        weakReading_witnessCompatible PUnit.unit weakReading_closed_unit).comap
        (twoChartReferenceModel.atlas.chart leftIndex).map) =
      Scheme.IdealSheafData.ofIdealTop
        (X := (twoChartReferenceModel.atlas.chart leftIndex).domain)
        (Ideal.map
          (AlgebraicGeometry.Scheme.ΓSpecIso
            (SheafifiedSectionRing rawSystem
              (twoChartReferenceModel.atlas.chart leftIndex).context)).inv.hom
          (Ideal.map
            (weakSchemeBridge.toSheafifiedSection
              (twoChartReferenceModel.atlas.chart leftIndex).context)
            (weakLawEquationCore.lawWitnessIdeal
              (twoChartReferenceModel.atlas.chart leftIndex).context PUnit.unit))) := by
  simpa only [weakReading] using
    (semanticCoreIdealSheaf_realized rawSystem twoChartReferenceModel
      weakLawEquationCore weakSchemeBridge weakSchemeBridge_valid).2
        leftIndex PUnit.unit

/-- The concrete weak witness satisfies exact basic-open restriction compatibility. -/
theorem weakWitness_valid :
    IsClosedEquationalLawWitness rawSystem twoChartReferenceModel
      (weakReading.witness PUnit.unit weakReading_closed_unit) :=
  weakReading_witnessCompatible PUnit.unit weakReading_closed_unit

/-- Every required law is closed and selected by the weak reading. -/
theorem weakReading_requiredClosed :
    RequiredClosed rawSystem twoChartReferenceModel weakReading :=
  ClosedEquationalLawReading.ofSemanticCore_requiredClosed rawSystem
    twoChartReferenceModel weakLawEquationCore weakSchemeBridge

/-- Every required law is closed and selected by the strong reading. -/
theorem strongReading_requiredClosed :
    RequiredClosed rawSystem twoChartReferenceModel strongReading :=
  ClosedEquationalLawReading.ofSemanticCore_requiredClosed rawSystem
    twoChartReferenceModel strongLawEquationCore strongSchemeBridge

/-- The weak reading closes and selects every law index. -/
theorem weakReading_allLawsSelected :
    AllLawsSelected rawSystem twoChartReferenceModel weakReading :=
  ClosedEquationalLawReading.ofSemanticCore_allLawsSelected rawSystem
    twoChartReferenceModel weakLawEquationCore weakSchemeBridge

/-- The strong reading closes and selects every law index. -/
theorem strongReading_allLawsSelected :
    AllLawsSelected rawSystem twoChartReferenceModel strongReading :=
  ClosedEquationalLawReading.ofSemanticCore_allLawsSelected rawSystem
    twoChartReferenceModel strongLawEquationCore strongSchemeBridge

/-! ## Generator-level exactness -/

private theorem ofIdealTop_span_comap_eq_bot_iff
    (equation : carrier.Atom → Γ(twoChartReferenceModel.underlying, ⊤))
    {T : AlgebraicGeometry.Scheme}
    (s : T ⟶ twoChartReferenceModel.underlying) :
    (Scheme.IdealSheafData.ofIdealTop
        (X := twoChartReferenceModel.underlying)
        (Ideal.span (Set.range equation))).comap s = ⊥ ↔
      ∀ a, s.appTop (equation a) = 0 := by
  haveI : IsAffine twoChartReferenceModel.underlying := by
    rw [twoChart_underlying]
    infer_instance
  let e := Scheme.IdealSheafData.equivOfIsAffine
    (X := twoChartReferenceModel.underlying)
  constructor
  · intro h a
    have hcomap :
        (Scheme.IdealSheafData.ofIdealTop
            (X := twoChartReferenceModel.underlying)
            (Ideal.span (Set.range equation))).comap s ≤ ⊥ := h.le
    have hle := (Scheme.IdealSheafData.map_gc s _ _).mp hcomap
    change Scheme.IdealSheafData.ofIdealTop
      (Ideal.span (Set.range equation)) ≤
        (⊥ : T.IdealSheafData).map s at hle
    rw [Scheme.IdealSheafData.map_bot,
      Scheme.ker_of_isAffine] at hle
    have hideal :
        Ideal.span (Set.range equation) ≤ RingHom.ker s.appTop.hom := by
      simpa [e] using e.toOrderIso.monotone hle
    exact hideal (Ideal.subset_span ⟨a, rfl⟩)
  · intro h
    apply le_antisymm
    · apply (Scheme.IdealSheafData.map_gc s _ _).mpr
      change Scheme.IdealSheafData.ofIdealTop
        (Ideal.span (Set.range equation)) ≤
          (⊥ : T.IdealSheafData).map s
      rw [Scheme.IdealSheafData.map_bot,
        Scheme.ker_of_isAffine]
      have hideal :
          Ideal.span (Set.range equation) ≤ RingHom.ker s.appTop.hom := by
        apply Ideal.span_le.mpr
        rintro _ ⟨a, rfl⟩
        exact h a
      apply Scheme.IdealSheafData.le_of_isAffine
      simpa using hideal
    · exact bot_le

private theorem finiteCore_lawIdealExact
    (G : SemanticLawEquationWitnessIdealCore RingedSite.FiniteModel.site)
    (B : SemanticLawEquationSchemeBridge rawSystem G)
    (i : RingedSite.FiniteModel.site.equationSystem.Index) :
    LawIdealExact rawSystem twoChartReferenceModel
      (ClosedEquationalLawReading.ofSemanticCore rawSystem
        twoChartReferenceModel G B)
      (ClosedEquationalLawReading.ofSemanticCore_witnessCompatible rawSystem
        twoChartReferenceModel G B)
      i (Set.mem_univ i) := by
  intro T s
  change (GeometricLawReading.ofSemanticCore rawSystem twoChartReferenceModel
    G B).HoldsOn s i ↔ _
  rw [GeometricLawReading.ofSemanticCore_holdsOn]
  have hsheaf := lawWitnessIdealSheaf_ofGlobalSections rawSystem
    twoChartReferenceModel
    (ClosedEquationalLawReading.ofSemanticCore rawSystem
      twoChartReferenceModel G B)
    (ClosedEquationalLawReading.ofSemanticCore_witnessCompatible rawSystem
      twoChartReferenceModel G B)
    i (Set.mem_univ i)
    (semanticCoreGlobalEquation rawSystem twoChartReferenceModel G B i)
    (by
      exact ClosedEquationalLawReading.ofSemanticCore_witness rawSystem
        twoChartReferenceModel G B i (Set.mem_univ i))
  rw [hsheaf]
  exact (ofIdealTop_span_comap_eq_bot_iff
    (semanticCoreGlobalEquation rawSystem twoChartReferenceModel G B i) s).symm

private theorem weak_lawIdealExact_calculation :
    LawIdealExact rawSystem twoChartReferenceModel weakReading
      weakReading_witnessCompatible PUnit.unit
      (weakReading_requiredClosed.closed PUnit.unit
        (RingedSite.FiniteModel.site_equation_required PUnit.unit)) := by
  intro T s
  simpa only [weakReading] using
    finiteCore_lawIdealExact weakLawEquationCore weakSchemeBridge PUnit.unit
      (T := T) s

private theorem strong_lawIdealExact_calculation :
    LawIdealExact rawSystem twoChartReferenceModel strongReading
      strongReading_witnessCompatible PUnit.unit
      (strongReading_requiredClosed.closed PUnit.unit
        (RingedSite.FiniteModel.site_equation_required PUnit.unit)) := by
  intro T s
  simpa only [strongReading] using
    finiteCore_lawIdealExact strongLawEquationCore strongSchemeBridge PUnit.unit
      (T := T) s

/-- Required weak semantic truth is exactly weak ideal-sheaf vanishing. -/
theorem weakReading_requiredLawIdealExact :
    RequiredLawIdealExact rawSystem twoChartReferenceModel
      weakReading weakReading_valid weakReading_requiredClosed := by
  intro i hi
  cases i
  intro T s
  simpa only [twoChart_underlying] using
    weak_lawIdealExact_calculation (T := T) s

/-- Required strong semantic truth is exactly strong ideal-sheaf vanishing. -/
theorem strongReading_requiredLawIdealExact :
    RequiredLawIdealExact rawSystem twoChartReferenceModel
      strongReading strongReading_valid strongReading_requiredClosed := by
  intro i hi
  cases i
  intro T s
  simpa only [twoChart_underlying] using
    strong_lawIdealExact_calculation (T := T) s

/-- Weak semantic truth implies vanishing of the concrete weak witness ideal sheaf. -/
theorem weakReading_lawIdealSound :
    LawIdealSound rawSystem twoChartReferenceModel weakReading
      weakReading_witnessCompatible PUnit.unit
      (weakReading_requiredClosed.closed PUnit.unit
        (RingedSite.FiniteModel.site_equation_required PUnit.unit)) := by
  intro T s hs
  exact (weak_lawIdealExact_calculation s).mp hs

/-- Vanishing of the concrete weak witness ideal sheaf implies weak semantic truth. -/
theorem weakReading_lawIdealComplete :
    LawIdealComplete rawSystem twoChartReferenceModel weakReading
      weakReading_witnessCompatible PUnit.unit
      (weakReading_requiredClosed.closed PUnit.unit
        (RingedSite.FiniteModel.site_equation_required PUnit.unit)) := by
  intro T s hs
  exact (weak_lawIdealExact_calculation s).mpr hs

/-- Weak semantic truth is equivalent to concrete weak witness ideal-sheaf vanishing. -/
theorem weakReading_lawIdealExact :
    LawIdealExact rawSystem twoChartReferenceModel weakReading
      weakReading_witnessCompatible PUnit.unit
      (weakReading_requiredClosed.closed PUnit.unit
        (RingedSite.FiniteModel.site_equation_required PUnit.unit)) :=
  weak_lawIdealExact_calculation

/-- Weak semantic truth is exact for every law index. -/
theorem weakReading_allLawIdealExact :
    AllLawIdealExact rawSystem twoChartReferenceModel weakReading
      weakReading_valid weakReading_allLawsSelected := by
  intro i
  cases i
  intro T s
  simpa only [twoChart_underlying] using
    weak_lawIdealExact_calculation (T := T) s

/-- Strong semantic truth is exact for every law index. -/
theorem strongReading_allLawIdealExact :
    AllLawIdealExact rawSystem twoChartReferenceModel strongReading
      strongReading_valid strongReading_allLawsSelected := by
  intro i
  cases i
  intro T s
  simpa only [twoChart_underlying] using
    strong_lawIdealExact_calculation (T := T) s

/-- The weak law data embeds into the strong law data by preserving component A. -/
def weakToStrong :
    ClosedEquationalLawInclusion rawSystem twoChartReferenceModel
      weakReading strongReading where
  lawMap i := i
  atomMap _ a :=
    match a with
    | FiniteAtom.componentA => FiniteAtom.componentA
    | _ => FiniteAtom.componentC

private def polynomialEvalOne :
    FreeTypedCommAlg (rawSystem.coordFamily base) Int →+* Int :=
  MvPolynomial.eval₂Hom (RingHom.id Int) (fun _ => 1)

private theorem base_JStruct_le_ker_polynomialEvalOne :
    (rawSystem.relationFamily base).JStruct ≤
      RingHom.ker polynomialEvalOne := by
  rw [StructuralRelationFamily.JStruct]
  apply Ideal.span_le.mpr
  rintro p ⟨r, rfl⟩
  cases r
  simp [rawSystem, RawPresheaf.relationFamily, polynomialEvalOne]

private def rawEvalOne : rawSystem.rawAlgebra base →+* Int :=
  Ideal.Quotient.lift (rawSystem.relationFamily base).JStruct
    polynomialEvalOne (by
      intro p hp
      exact base_JStruct_le_ker_polynomialEvalOne hp)

private def polynomialEvalNegativeOne :
    FreeTypedCommAlg (rawSystem.coordFamily base) Int →+* Int :=
  MvPolynomial.eval₂Hom (RingHom.id Int) (fun _ => -1)

private theorem base_JStruct_le_ker_polynomialEvalNegativeOne :
    (rawSystem.relationFamily base).JStruct ≤
      RingHom.ker polynomialEvalNegativeOne := by
  rw [StructuralRelationFamily.JStruct]
  apply Ideal.span_le.mpr
  rintro p ⟨r, rfl⟩
  cases r
  simp [rawSystem, RawPresheaf.relationFamily, polynomialEvalNegativeOne]

private def rawEvalNegativeOne : rawSystem.rawAlgebra base →+* Int :=
  Ideal.Quotient.lift (rawSystem.relationFamily base).JStruct
    polynomialEvalNegativeOne (by
      intro p hp
      exact base_JStruct_le_ker_polynomialEvalNegativeOne hp)

private def polynomialEvalModTwo :
    FreeTypedCommAlg (rawSystem.coordFamily base) Int →+* ZMod 2 :=
  MvPolynomial.eval₂Hom (Int.castRingHom (ZMod 2)) (fun _ => 1)

private theorem base_JStruct_le_ker_polynomialEvalModTwo :
    (rawSystem.relationFamily base).JStruct ≤
      RingHom.ker polynomialEvalModTwo := by
  rw [StructuralRelationFamily.JStruct]
  apply Ideal.span_le.mpr
  rintro p ⟨r, rfl⟩
  cases r
  simp [rawSystem, RawPresheaf.relationFamily, polynomialEvalModTwo]

private def rawEvalModTwo : rawSystem.rawAlgebra base →+* ZMod 2 :=
  Ideal.Quotient.lift (rawSystem.relationFamily base).JStruct
    polynomialEvalModTwo (by
      intro p hp
      exact base_JStruct_le_ker_polynomialEvalModTwo hp)

private noncomputable def sheafifiedEvalOne :
    SheafifiedSectionRing rawSystem base →+* Int :=
  rawEvalOne.comp
    baseSheafifiedPresentation.comparison.toAlgHom.toRingHom

private noncomputable def sheafifiedEvalNegativeOne :
    SheafifiedSectionRing rawSystem base →+* Int :=
  rawEvalNegativeOne.comp
    baseSheafifiedPresentation.comparison.toAlgHom.toRingHom

private noncomputable def sheafifiedEvalModTwo :
    SheafifiedSectionRing rawSystem base →+* ZMod 2 :=
  rawEvalModTwo.comp
    baseSheafifiedPresentation.comparison.toAlgHom.toRingHom

private noncomputable def globalEvalOne :
    Γ(twoChartReferenceModel.underlying, ⊤) →+* Int :=
  sheafifiedEvalOne.comp
    (AlgebraicGeometry.Scheme.ΓSpecIso
      (SheafifiedSectionRing rawSystem base)).hom.hom

private noncomputable def globalEvalNegativeOne :
    Γ(twoChartReferenceModel.underlying, ⊤) →+* Int :=
  sheafifiedEvalNegativeOne.comp
    (AlgebraicGeometry.Scheme.ΓSpecIso
      (SheafifiedSectionRing rawSystem base)).hom.hom

private noncomputable def globalEvalModTwo :
    Γ(twoChartReferenceModel.underlying, ⊤) →+* ZMod 2 :=
  sheafifiedEvalModTwo.comp
    (AlgebraicGeometry.Scheme.ΓSpecIso
      (SheafifiedSectionRing rawSystem base)).hom.hom

private noncomputable def ambientTopAffineOpen :
    twoChartReferenceModel.underlying.affineOpens := by
  rw [twoChart_underlying]
  exact ⟨⊤, AlgebraicGeometry.isAffineOpen_top _⟩

private theorem baseGlobalCoordinate_eq_inv :
    baseGlobalCoordinate =
      (AlgebraicGeometry.Scheme.ΓSpecIso
        (SheafifiedSectionRing rawSystem base)).inv
        StandardArchitectureScheme.baseCoordinateSection := by
  rfl

private theorem globalEvalOne_baseGlobalCoordinate :
    globalEvalOne baseGlobalCoordinate = 1 := by
  simp only [globalEvalOne, sheafifiedEvalOne, RingHom.comp_apply,
    baseGlobalCoordinate_eq_inv]
  have hΓ :
      (AlgebraicGeometry.Scheme.ΓSpecIso
        (SheafifiedSectionRing rawSystem base)).hom.hom
          ((AlgebraicGeometry.Scheme.ΓSpecIso
            (SheafifiedSectionRing rawSystem base)).inv
            StandardArchitectureScheme.baseCoordinateSection) =
        StandardArchitectureScheme.baseCoordinateSection := by
    simpa only [CommRingCat.comp_apply] using congrArg
      (fun q => q StandardArchitectureScheme.baseCoordinateSection)
      (AlgebraicGeometry.Scheme.ΓSpecIso
        (SheafifiedSectionRing rawSystem base)).inv_hom_id
  erw [hΓ]
  change rawEvalOne
    (baseSheafifiedPresentation.comparison.toAlgHom
      StandardArchitectureScheme.baseCoordinateSection) = 1
  rw [StandardArchitectureScheme.baseCoordinateSection,
    StandardSchemeReading.baseCoordinateSection]
  change rawEvalOne
    (baseSheafifiedPresentation.comparison.toAlgHom
      ((sheafificationUnitAlgHom rawSystem base)
        ((rawSystem.relationFamily base).quotientMap
          (MvPolynomial.X ())))) = 1
  calc
    rawEvalOne
        (baseSheafifiedPresentation.comparison.toAlgHom
          ((sheafificationUnitAlgHom rawSystem base)
            ((rawSystem.relationFamily base).quotientMap
              (MvPolynomial.X ())))) =
      rawEvalOne
        (baseSheafifiedPresentation.comparison.toAlgHom
          (baseSheafifiedPresentation.comparison.symm.toAlgHom
            ((rawSystem.relationFamily base).quotientMap
              (MvPolynomial.X ())))) := by
        rw [basePresentation_comparison_symm_toAlgHom]
    _ = 1 := by
      have hcancel :
          baseSheafifiedPresentation.comparison.toAlgHom
              (baseSheafifiedPresentation.comparison.symm.toAlgHom
                ((rawSystem.relationFamily base).quotientMap
                  (MvPolynomial.X ()))) =
            (rawSystem.relationFamily base).quotientMap
              (MvPolynomial.X ()) := by
        exact baseSheafifiedPresentation.comparison.apply_symm_apply _
      rw [hcancel]
      rw [rawEvalOne,
        AAT.AG.LawAlgebra.StructuralRelationFamily.quotientMap,
        Ideal.Quotient.lift_mk]
      simp [polynomialEvalOne]

private theorem globalEvalNegativeOne_baseGlobalCoordinate :
    globalEvalNegativeOne baseGlobalCoordinate = -1 := by
  simp only [globalEvalNegativeOne, sheafifiedEvalNegativeOne, RingHom.comp_apply,
    baseGlobalCoordinate_eq_inv]
  have hΓ :
      (AlgebraicGeometry.Scheme.ΓSpecIso
        (SheafifiedSectionRing rawSystem base)).hom.hom
          ((AlgebraicGeometry.Scheme.ΓSpecIso
            (SheafifiedSectionRing rawSystem base)).inv
            StandardArchitectureScheme.baseCoordinateSection) =
        StandardArchitectureScheme.baseCoordinateSection := by
    simpa only [CommRingCat.comp_apply] using congrArg
      (fun q => q StandardArchitectureScheme.baseCoordinateSection)
      (AlgebraicGeometry.Scheme.ΓSpecIso
        (SheafifiedSectionRing rawSystem base)).inv_hom_id
  erw [hΓ]
  change rawEvalNegativeOne
    (baseSheafifiedPresentation.comparison.toAlgHom
      StandardArchitectureScheme.baseCoordinateSection) = -1
  rw [StandardArchitectureScheme.baseCoordinateSection,
    StandardSchemeReading.baseCoordinateSection]
  change rawEvalNegativeOne
    (baseSheafifiedPresentation.comparison.toAlgHom
      ((sheafificationUnitAlgHom rawSystem base)
        ((rawSystem.relationFamily base).quotientMap
          (MvPolynomial.X ())))) = -1
  calc
    rawEvalNegativeOne
        (baseSheafifiedPresentation.comparison.toAlgHom
          ((sheafificationUnitAlgHom rawSystem base)
            ((rawSystem.relationFamily base).quotientMap
              (MvPolynomial.X ())))) =
      rawEvalNegativeOne
        (baseSheafifiedPresentation.comparison.toAlgHom
          (baseSheafifiedPresentation.comparison.symm.toAlgHom
            ((rawSystem.relationFamily base).quotientMap
              (MvPolynomial.X ())))) := by
        rw [basePresentation_comparison_symm_toAlgHom]
    _ = -1 := by
      have hcancel :
          baseSheafifiedPresentation.comparison.toAlgHom
              (baseSheafifiedPresentation.comparison.symm.toAlgHom
                ((rawSystem.relationFamily base).quotientMap
                  (MvPolynomial.X ()))) =
            (rawSystem.relationFamily base).quotientMap
              (MvPolynomial.X ()) := by
        exact baseSheafifiedPresentation.comparison.apply_symm_apply _
      rw [hcancel]
      rw [rawEvalNegativeOne,
        AAT.AG.LawAlgebra.StructuralRelationFamily.quotientMap,
        Ideal.Quotient.lift_mk]
      simp [polynomialEvalNegativeOne]

private theorem globalEvalModTwo_baseGlobalCoordinate :
    globalEvalModTwo baseGlobalCoordinate = 1 := by
  simp only [globalEvalModTwo, sheafifiedEvalModTwo, RingHom.comp_apply,
    baseGlobalCoordinate_eq_inv]
  have hΓ :
      (AlgebraicGeometry.Scheme.ΓSpecIso
        (SheafifiedSectionRing rawSystem base)).hom.hom
          ((AlgebraicGeometry.Scheme.ΓSpecIso
            (SheafifiedSectionRing rawSystem base)).inv
            StandardArchitectureScheme.baseCoordinateSection) =
        StandardArchitectureScheme.baseCoordinateSection := by
    simpa only [CommRingCat.comp_apply] using congrArg
      (fun q => q StandardArchitectureScheme.baseCoordinateSection)
      (AlgebraicGeometry.Scheme.ΓSpecIso
        (SheafifiedSectionRing rawSystem base)).inv_hom_id
  erw [hΓ]
  change rawEvalModTwo
    (baseSheafifiedPresentation.comparison.toAlgHom
      StandardArchitectureScheme.baseCoordinateSection) = 1
  rw [StandardArchitectureScheme.baseCoordinateSection,
    StandardSchemeReading.baseCoordinateSection]
  change rawEvalModTwo
    (baseSheafifiedPresentation.comparison.toAlgHom
      ((sheafificationUnitAlgHom rawSystem base)
        ((rawSystem.relationFamily base).quotientMap
          (MvPolynomial.X ())))) = 1
  calc
    rawEvalModTwo
        (baseSheafifiedPresentation.comparison.toAlgHom
          ((sheafificationUnitAlgHom rawSystem base)
            ((rawSystem.relationFamily base).quotientMap
              (MvPolynomial.X ())))) =
      rawEvalModTwo
        (baseSheafifiedPresentation.comparison.toAlgHom
          (baseSheafifiedPresentation.comparison.symm.toAlgHom
            ((rawSystem.relationFamily base).quotientMap
              (MvPolynomial.X ())))) := by
        rw [basePresentation_comparison_symm_toAlgHom]
    _ = 1 := by
      have hcancel :
          baseSheafifiedPresentation.comparison.toAlgHom
              (baseSheafifiedPresentation.comparison.symm.toAlgHom
                ((rawSystem.relationFamily base).quotientMap
                  (MvPolynomial.X ()))) =
            (rawSystem.relationFamily base).quotientMap
              (MvPolynomial.X ()) := by
        exact baseSheafifiedPresentation.comparison.apply_symm_apply _
      rw [hcancel]
      rw [rawEvalModTwo,
        AAT.AG.LawAlgebra.StructuralRelationFamily.quotientMap,
        Ideal.Quotient.lift_mk]
      simp [polynomialEvalModTwo]

private theorem weak_local_top_eq_span
    (hi : weakReading.closed PUnit.unit) :
    localLawWitnessIdeal rawSystem twoChartReferenceModel
        (weakReading.witness PUnit.unit hi) ambientTopAffineOpen =
      Ideal.span (Set.range (semanticCoreGlobalEquation rawSystem
        twoChartReferenceModel weakLawEquationCore weakSchemeBridge PUnit.unit)) := by
  rw [← lawWitnessIdealSheaf_ideal rawSystem twoChartReferenceModel
    weakReading weakReading_valid.witness_compatible PUnit.unit hi
    ambientTopAffineOpen]
  rw [lawWitnessIdealSheaf_ofGlobalSections rawSystem twoChartReferenceModel
    weakReading weakReading_valid.witness_compatible PUnit.unit hi
    (semanticCoreGlobalEquation rawSystem twoChartReferenceModel
      weakLawEquationCore weakSchemeBridge PUnit.unit)]
  · rw [Scheme.IdealSheafData.ofIdealTop_ideal]
    simp [ambientTopAffineOpen]
  · simpa only [weakReading] using
      ClosedEquationalLawReading.ofSemanticCore_witness rawSystem
        twoChartReferenceModel weakLawEquationCore weakSchemeBridge PUnit.unit hi

private theorem weak_generated_top_eq_span :
    (lawGeneratedIdealSheaf rawSystem twoChartReferenceModel
      weakReading weakReading_valid weakReading_requiredClosed).ideal
        ambientTopAffineOpen =
      Ideal.span (Set.range (semanticCoreGlobalEquation rawSystem
        twoChartReferenceModel weakLawEquationCore weakSchemeBridge PUnit.unit)) := by
  rw [lawGeneratedIdealSheaf_ideal]
  apply le_antisymm
  · refine iSup_le fun i => ?_
    cases i.1
    exact (weak_local_top_eq_span _).le
  · let idx : {i : RingedSite.FiniteModel.site.equationSystem.Index //
        RingedSite.FiniteModel.site.equationSystem.Required i ∧ weakReading.selected ambientTopAffineOpen i} :=
      ⟨PUnit.unit, RingedSite.FiniteModel.site_equation_required PUnit.unit,
        weakReading_selected ambientTopAffineOpen PUnit.unit⟩
    have h := le_iSup (fun i : {i : RingedSite.FiniteModel.site.equationSystem.Index //
      RingedSite.FiniteModel.site.equationSystem.Required i ∧ weakReading.selected ambientTopAffineOpen i} =>
        localLawWitnessIdeal rawSystem twoChartReferenceModel
          (weakReading.witness i.1
            (weakReading_requiredClosed.closed i.1 i.2.1))
          ambientTopAffineOpen) idx
    rw [weak_local_top_eq_span] at h
    exact h

private theorem strong_local_top_eq_span
    (hi : strongReading.closed PUnit.unit) :
    localLawWitnessIdeal rawSystem twoChartReferenceModel
        (strongReading.witness PUnit.unit hi) ambientTopAffineOpen =
      Ideal.span (Set.range (semanticCoreGlobalEquation rawSystem
        twoChartReferenceModel strongLawEquationCore strongSchemeBridge PUnit.unit)) := by
  rw [← lawWitnessIdealSheaf_ideal rawSystem twoChartReferenceModel
    strongReading strongReading_valid.witness_compatible PUnit.unit hi
    ambientTopAffineOpen]
  rw [lawWitnessIdealSheaf_ofGlobalSections rawSystem twoChartReferenceModel
    strongReading strongReading_valid.witness_compatible PUnit.unit hi
    (semanticCoreGlobalEquation rawSystem twoChartReferenceModel
      strongLawEquationCore strongSchemeBridge PUnit.unit)]
  · rw [Scheme.IdealSheafData.ofIdealTop_ideal]
    simp [ambientTopAffineOpen]
  · simpa only [strongReading] using
      ClosedEquationalLawReading.ofSemanticCore_witness rawSystem
        twoChartReferenceModel strongLawEquationCore strongSchemeBridge PUnit.unit hi

private theorem strong_generated_top_eq_span :
    (lawGeneratedIdealSheaf rawSystem twoChartReferenceModel
      strongReading strongReading_valid strongReading_requiredClosed).ideal
        ambientTopAffineOpen =
      Ideal.span (Set.range (semanticCoreGlobalEquation rawSystem
        twoChartReferenceModel strongLawEquationCore strongSchemeBridge PUnit.unit)) := by
  rw [lawGeneratedIdealSheaf_ideal]
  apply le_antisymm
  · refine iSup_le fun i => ?_
    cases i.1
    exact (strong_local_top_eq_span _).le
  · let idx : {i : RingedSite.FiniteModel.site.equationSystem.Index //
        RingedSite.FiniteModel.site.equationSystem.Required i ∧ strongReading.selected ambientTopAffineOpen i} :=
      ⟨PUnit.unit, RingedSite.FiniteModel.site_equation_required PUnit.unit,
        strongReading_selected ambientTopAffineOpen PUnit.unit⟩
    have h := le_iSup (fun i : {i : RingedSite.FiniteModel.site.equationSystem.Index //
      RingedSite.FiniteModel.site.equationSystem.Required i ∧ strongReading.selected ambientTopAffineOpen i} =>
        localLawWitnessIdeal rawSystem twoChartReferenceModel
          (strongReading.witness i.1
            (strongReading_requiredClosed.closed i.1 i.2.1))
          ambientTopAffineOpen) idx
    rw [strong_local_top_eq_span] at h
    exact h

private theorem weak_span_le_ker_globalEvalOne :
    Ideal.span (Set.range (semanticCoreGlobalEquation rawSystem
      twoChartReferenceModel weakLawEquationCore weakSchemeBridge PUnit.unit)) ≤
      RingHom.ker globalEvalOne := by
  apply Ideal.span_le.mpr
  rintro _ ⟨a, rfl⟩
  cases a
  · rw [weakCore_componentA_equation]
    change globalEvalOne (baseGlobalCoordinate - 1) = 0
    rw [map_sub, map_one, globalEvalOne_baseGlobalCoordinate]
    simp
  all_goals
    rw [weakCore_other_equation _ (by simp)]
    simp

private theorem strong_span_le_ker_globalEvalModTwo :
    Ideal.span (Set.range (semanticCoreGlobalEquation rawSystem
      twoChartReferenceModel strongLawEquationCore strongSchemeBridge PUnit.unit)) ≤
      RingHom.ker globalEvalModTwo := by
  apply Ideal.span_le.mpr
  rintro _ ⟨a, rfl⟩
  cases a
  · rw [strongCore_componentA_equation]
    change globalEvalModTwo (baseGlobalCoordinate - 1) = 0
    rw [map_sub, map_one, globalEvalModTwo_baseGlobalCoordinate]
    simp
  · rw [strongCore_componentB_equation]
    change globalEvalModTwo (baseGlobalCoordinate + 1) = 0
    rw [map_add, map_one, globalEvalModTwo_baseGlobalCoordinate]
    decide
  all_goals
    rw [strongCore_other_equation _ (by simp) (by simp)]
    simp

/-- The weak-to-strong atom map preserves required laws, coordinates, and semantic truth. -/
theorem weakToStrong_valid :
    IsClosedEquationalLawInclusion rawSystem twoChartReferenceModel weakToStrong where
  required_map := fun i hi => by simpa [weakToStrong] using hi
  closed_map := fun i _ => by
    cases i
    change PUnit.unit ∈ (Set.univ : Set RingedSite.FiniteModel.site.equationSystem.Index)
    simp
  selected_map := fun V i _ => strongReading_selected V i
  coordinate_eq := by
    intro i hi V a
    cases i
    simp only [weakToStrong]
    rw [weakReading_witness_eq_ofSemanticCore,
      strongReading_witness_eq_ofSemanticCore]
    simp only [ClosedEquationalLawWitness.ofSemanticCore,
      ClosedEquationalLawWitness.ofGlobalSections]
    cases a
    · rw [weakCore_componentA_equation, strongCore_componentA_equation]
    all_goals
      rw [weakCore_other_equation _ (by simp),
        strongCore_other_equation _ (by simp) (by simp)]
  semantic_monotone := by
    intro T s i hs
    cases i
    simp only [weakToStrong] at hs
    rw [weakReading_holdsOn_iff]
    rw [strongReading_holdsOn_iff] at hs
    intro a
    cases a
    · simpa only [weakCore_componentA_equation,
        strongCore_componentA_equation] using hs FiniteAtom.componentA
    all_goals
      rw [weakCore_other_equation _ (by simp)]
      simp

/-- The strong reading adds the genuinely new equation `x + 1` to the weak ideal. -/
theorem weak_ideal_lt_strong :
    lawGeneratedIdealSheaf rawSystem twoChartReferenceModel
        weakReading weakReading_valid weakReading_requiredClosed <
      lawGeneratedIdealSheaf rawSystem twoChartReferenceModel
        strongReading strongReading_valid strongReading_requiredClosed := by
  refine lt_of_le_of_ne
    (lawGeneratedIdealSheaf_mono rawSystem twoChartReferenceModel
      weakReading_valid strongReading_valid
      weakReading_requiredClosed strongReading_requiredClosed
      weakToStrong weakToStrong_valid) ?_
  intro heq
  have htop := congrArg
    (fun I : twoChartReferenceModel.underlying.IdealSheafData =>
      I.ideal ambientTopAffineOpen) heq
  change
    (lawGeneratedIdealSheaf rawSystem twoChartReferenceModel
      weakReading weakReading_valid weakReading_requiredClosed).ideal
        ambientTopAffineOpen =
    (lawGeneratedIdealSheaf rawSystem twoChartReferenceModel
      strongReading strongReading_valid strongReading_requiredClosed).ideal
        ambientTopAffineOpen at htop
  rw [weak_generated_top_eq_span, strong_generated_top_eq_span] at htop
  have hmemStrong :
      semanticCoreGlobalEquation rawSystem twoChartReferenceModel
          strongLawEquationCore strongSchemeBridge PUnit.unit
          FiniteAtom.componentB ∈
        Ideal.span (Set.range (semanticCoreGlobalEquation rawSystem
          twoChartReferenceModel strongLawEquationCore strongSchemeBridge
          PUnit.unit)) :=
    Ideal.subset_span ⟨FiniteAtom.componentB, rfl⟩
  have hmemWeak :
      semanticCoreGlobalEquation rawSystem twoChartReferenceModel
          strongLawEquationCore strongSchemeBridge PUnit.unit
          FiniteAtom.componentB ∈
        Ideal.span (Set.range (semanticCoreGlobalEquation rawSystem
          twoChartReferenceModel weakLawEquationCore weakSchemeBridge
          PUnit.unit)) := by
    rw [htop]
    exact hmemStrong
  have hzero := weak_span_le_ker_globalEvalOne hmemWeak
  rw [strongCore_componentB_equation] at hzero
  norm_num [globalEvalOne_baseGlobalCoordinate] at hzero

private noncomputable def integerTestPoint :
    AlgebraicGeometry.Spec (CommRingCat.of Int) ⟶
      twoChartReferenceModel.underlying := by
  rw [twoChart_underlying]
  exact AlgebraicGeometry.Spec.map (CommRingCat.ofHom sheafifiedEvalOne)

private noncomputable def negativeOneTestPoint :
    AlgebraicGeometry.Spec (CommRingCat.of Int) ⟶
      twoChartReferenceModel.underlying := by
  rw [twoChart_underlying]
  exact AlgebraicGeometry.Spec.map
    (CommRingCat.ofHom sheafifiedEvalNegativeOne)

private noncomputable def modTwoTestPoint :
    AlgebraicGeometry.Spec (CommRingCat.of (ZMod 2)) ⟶
      twoChartReferenceModel.underlying := by
  rw [twoChart_underlying]
  exact AlgebraicGeometry.Spec.map (CommRingCat.ofHom sheafifiedEvalModTwo)

private theorem integerTestPoint_normalized_appTop :
    integerTestPoint.appTop ≫
        (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of Int)).hom =
      (AlgebraicGeometry.Scheme.ΓSpecIso
          (SheafifiedSectionRing rawSystem base)).hom ≫
        CommRingCat.ofHom sheafifiedEvalOne := by
  simpa only [integerTestPoint, twoChart_underlying] using
    AlgebraicGeometry.Scheme.ΓSpecIso_naturality
      (CommRingCat.ofHom sheafifiedEvalOne)

private theorem negativeOneTestPoint_normalized_appTop :
    negativeOneTestPoint.appTop ≫
        (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of Int)).hom =
      (AlgebraicGeometry.Scheme.ΓSpecIso
          (SheafifiedSectionRing rawSystem base)).hom ≫
        CommRingCat.ofHom sheafifiedEvalNegativeOne := by
  simpa only [negativeOneTestPoint, twoChart_underlying] using
    AlgebraicGeometry.Scheme.ΓSpecIso_naturality
      (CommRingCat.ofHom sheafifiedEvalNegativeOne)

private theorem modTwoTestPoint_normalized_appTop :
    modTwoTestPoint.appTop ≫
        (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of (ZMod 2))).hom =
      (AlgebraicGeometry.Scheme.ΓSpecIso
          (SheafifiedSectionRing rawSystem base)).hom ≫
        CommRingCat.ofHom sheafifiedEvalModTwo := by
  simpa only [modTwoTestPoint, twoChart_underlying] using
    AlgebraicGeometry.Scheme.ΓSpecIso_naturality
      (CommRingCat.ofHom sheafifiedEvalModTwo)

private theorem negativeOneTestPoint_not_weak_semanticLawful :
    ¬ SemanticLawfulAlong rawSystem twoChartReferenceModel weakReading
      negativeOneTestPoint := by
  intro h
  have hA := h PUnit.unit (RingedSite.FiniteModel.site_equation_required PUnit.unit)
  rw [weakReading_holdsOn_iff] at hA
  have hequation := hA FiniteAtom.componentA
  rw [weakCore_componentA_equation] at hequation
  have hnormalized := congrArg (fun q => q (baseGlobalCoordinate - 1))
    negativeOneTestPoint_normalized_appTop
  change
    (AlgebraicGeometry.Scheme.ΓSpecIso
      (CommRingCat.of Int)).hom.hom
        (negativeOneTestPoint.appTop.hom (baseGlobalCoordinate - 1)) =
      globalEvalNegativeOne (baseGlobalCoordinate - 1) at hnormalized
  rw [hequation, map_zero, map_sub, map_one,
    globalEvalNegativeOne_baseGlobalCoordinate] at hnormalized
  norm_num at hnormalized

private theorem integerTestPoint_not_strong_semanticLawful :
    ¬ SemanticLawfulAlong rawSystem twoChartReferenceModel strongReading
      integerTestPoint := by
  intro h
  have hrequired := h PUnit.unit (RingedSite.FiniteModel.site_equation_required PUnit.unit)
  rw [strongReading_holdsOn_iff] at hrequired
  have hequation := hrequired FiniteAtom.componentB
  rw [strongCore_componentB_equation] at hequation
  have hnormalized := congrArg (fun q => q (baseGlobalCoordinate + 1))
    integerTestPoint_normalized_appTop
  change
    (AlgebraicGeometry.Scheme.ΓSpecIso
      (CommRingCat.of Int)).hom.hom
        (integerTestPoint.appTop.hom (baseGlobalCoordinate + 1)) =
      globalEvalOne (baseGlobalCoordinate + 1) at hnormalized
  rw [hequation, map_zero, map_add, map_one,
    globalEvalOne_baseGlobalCoordinate] at hnormalized
  norm_num at hnormalized

private theorem integerTestPoint_semanticLawful :
    SemanticLawfulAlong rawSystem twoChartReferenceModel weakReading
      integerTestPoint := by
  intro i _
  cases i
  rw [weakReading_holdsOn_iff]
  intro a
  apply (ConcreteCategory.bijective_of_isIso
    (AlgebraicGeometry.Scheme.ΓSpecIso
      (CommRingCat.of Int)).hom).1
  have hnormalized := congrArg (fun q => q
    (semanticCoreGlobalEquation rawSystem twoChartReferenceModel
      weakLawEquationCore weakSchemeBridge PUnit.unit a))
    integerTestPoint_normalized_appTop
  change
    (AlgebraicGeometry.Scheme.ΓSpecIso
      (CommRingCat.of Int)).hom.hom
        (integerTestPoint.appTop.hom
          (semanticCoreGlobalEquation rawSystem twoChartReferenceModel
            weakLawEquationCore weakSchemeBridge PUnit.unit a)) =
      globalEvalOne
        (semanticCoreGlobalEquation rawSystem twoChartReferenceModel
          weakLawEquationCore weakSchemeBridge PUnit.unit a) at hnormalized
  rw [hnormalized]
  simpa only [map_zero] using weak_span_le_ker_globalEvalOne
    (Ideal.subset_span ⟨a, rfl⟩)

private theorem modTwoTestPoint_semanticLawful :
    SemanticLawfulAlong rawSystem twoChartReferenceModel strongReading
      modTwoTestPoint := by
  intro i _
  cases i
  rw [strongReading_holdsOn_iff]
  intro a
  apply (ConcreteCategory.bijective_of_isIso
    (AlgebraicGeometry.Scheme.ΓSpecIso
      (CommRingCat.of (ZMod 2))).hom).1
  have hnormalized := congrArg (fun q => q
    (semanticCoreGlobalEquation rawSystem twoChartReferenceModel
      strongLawEquationCore strongSchemeBridge PUnit.unit a))
    modTwoTestPoint_normalized_appTop
  change
    (AlgebraicGeometry.Scheme.ΓSpecIso
      (CommRingCat.of (ZMod 2))).hom.hom
        (modTwoTestPoint.appTop.hom
          (semanticCoreGlobalEquation rawSystem twoChartReferenceModel
            strongLawEquationCore strongSchemeBridge PUnit.unit a)) =
      globalEvalModTwo
        (semanticCoreGlobalEquation rawSystem twoChartReferenceModel
          strongLawEquationCore strongSchemeBridge PUnit.unit a) at hnormalized
  rw [hnormalized]
  simpa only [map_zero] using strong_span_le_ker_globalEvalModTwo
    (Ideal.subset_span ⟨a, rfl⟩)

private theorem integerTestPoint_idealLawful :
    IdealLawfulAlong rawSystem twoChartReferenceModel weakReading
      weakReading_valid weakReading_requiredClosed integerTestPoint :=
  (witnessVanishes_iff_idealLawfulAlong rawSystem twoChartReferenceModel
    weakReading weakReading_valid weakReading_requiredClosed integerTestPoint).mp
    ((semanticLawfulAlong_iff_witnessVanishes rawSystem
      twoChartReferenceModel weakReading weakReading_valid
      weakReading_requiredClosed weakReading_requiredLawIdealExact
      integerTestPoint).mp integerTestPoint_semanticLawful)

private theorem modTwoTestPoint_idealLawful :
    IdealLawfulAlong rawSystem twoChartReferenceModel strongReading
      strongReading_valid strongReading_requiredClosed modTwoTestPoint :=
  (witnessVanishes_iff_idealLawfulAlong rawSystem twoChartReferenceModel
    strongReading strongReading_valid strongReading_requiredClosed
    modTwoTestPoint).mp
    ((semanticLawfulAlong_iff_witnessVanishes rawSystem
      twoChartReferenceModel strongReading strongReading_valid
      strongReading_requiredClosed strongReading_requiredLawIdealExact
      modTwoTestPoint).mp modTwoTestPoint_semanticLawful)

/-- The concrete integer point lifts to a point of the weak closed subscheme. -/
theorem weakSubscheme_nonempty :
    Nonempty (lawfulClosedSubscheme rawSystem twoChartReferenceModel
      weakReading weakReading_valid weakReading_requiredClosed) := by
  let p : AlgebraicGeometry.Spec (CommRingCat.of Int) :=
    Classical.choice inferInstance
  exact ⟨(factorizationLift rawSystem twoChartReferenceModel weakReading
    weakReading_valid weakReading_requiredClosed integerTestPoint
    integerTestPoint_idealLawful).base p⟩

/-- The concrete characteristic-two point lifts to a point of the strong closed subscheme. -/
theorem strongSubscheme_nonempty :
    Nonempty (lawfulClosedSubscheme rawSystem twoChartReferenceModel
      strongReading strongReading_valid strongReading_requiredClosed) := by
  let p : AlgebraicGeometry.Spec (CommRingCat.of (ZMod 2)) :=
    Classical.choice inferInstance
  exact ⟨(factorizationLift rawSystem twoChartReferenceModel strongReading
    strongReading_valid strongReading_requiredClosed modTwoTestPoint
    modTwoTestPoint_idealLawful).base p⟩

private theorem negativeOneTestPoint_not_weak_factors :
    ¬ Nonempty (FactorsThroughLawfulClosedSubscheme rawSystem
      twoChartReferenceModel weakReading weakReading_valid
      weakReading_requiredClosed negativeOneTestPoint) := by
  intro hfactor
  apply negativeOneTestPoint_not_weak_semanticLawful
  exact (semanticLawfulAlong_iff_witnessVanishes rawSystem
    twoChartReferenceModel weakReading weakReading_valid
    weakReading_requiredClosed weakReading_requiredLawIdealExact
    negativeOneTestPoint).mpr
      ((witnessVanishes_iff_idealLawfulAlong rawSystem
        twoChartReferenceModel weakReading weakReading_valid
        weakReading_requiredClosed negativeOneTestPoint).mpr
          ((idealLawfulAlong_iff_nonempty_factorsThrough rawSystem
            twoChartReferenceModel weakReading weakReading_valid
            weakReading_requiredClosed negativeOneTestPoint).mpr hfactor))

private theorem integerTestPoint_not_strong_factors :
    ¬ Nonempty (FactorsThroughLawfulClosedSubscheme rawSystem
      twoChartReferenceModel strongReading strongReading_valid
      strongReading_requiredClosed integerTestPoint) := by
  intro hfactor
  apply integerTestPoint_not_strong_semanticLawful
  exact (semanticLawfulAlong_iff_witnessVanishes rawSystem
    twoChartReferenceModel strongReading strongReading_valid
    strongReading_requiredClosed strongReading_requiredLawIdealExact
    integerTestPoint).mpr
      ((witnessVanishes_iff_idealLawfulAlong rawSystem
        twoChartReferenceModel strongReading strongReading_valid
        strongReading_requiredClosed integerTestPoint).mpr
          ((idealLawfulAlong_iff_nonempty_factorsThrough rawSystem
            twoChartReferenceModel strongReading strongReading_valid
            strongReading_requiredClosed integerTestPoint).mpr hfactor))

/-- The weak closed immersion excludes the concrete coordinate-negative-one point. -/
theorem weakImmersion_not_isIso :
    ¬ IsIso (lawfulClosedImmersion rawSystem twoChartReferenceModel
      weakReading weakReading_valid weakReading_requiredClosed) := by
  intro hIso
  letI : IsIso (lawfulClosedImmersion rawSystem twoChartReferenceModel
      weakReading weakReading_valid weakReading_requiredClosed) := hIso
  apply negativeOneTestPoint_not_weak_factors
  exact ⟨⟨negativeOneTestPoint ≫
      inv (lawfulClosedImmersion rawSystem twoChartReferenceModel
        weakReading weakReading_valid weakReading_requiredClosed), by simp⟩⟩

/-- The strong closed immersion excludes the concrete integer coordinate-one point. -/
theorem strongImmersion_not_isIso :
    ¬ IsIso (lawfulClosedImmersion rawSystem twoChartReferenceModel
      strongReading strongReading_valid strongReading_requiredClosed) := by
  intro hIso
  letI : IsIso (lawfulClosedImmersion rawSystem twoChartReferenceModel
      strongReading strongReading_valid strongReading_requiredClosed) := hIso
  apply integerTestPoint_not_strong_factors
  exact ⟨⟨integerTestPoint ≫
      inv (lawfulClosedImmersion rawSystem twoChartReferenceModel
        strongReading strongReading_valid strongReading_requiredClosed), by simp⟩⟩

/-- The concrete integer point satisfies every weak law. -/
private theorem integerTestPoint_fullyWeakSemanticLawful :
    FullySemanticLawfulAlong rawSystem twoChartReferenceModel weakReading
      integerTestPoint := by
  intro i
  exact integerTestPoint_semanticLawful i (RingedSite.FiniteModel.site_equation_required i)

private theorem integerTestPoint_fullWeakIdealLawful :
    FullIdealLawfulAlong rawSystem twoChartReferenceModel weakReading
      weakReading_valid integerTestPoint :=
  (fullySemanticLawfulAlong_iff_fullIdealLawfulAlong rawSystem
    twoChartReferenceModel weakReading weakReading_valid
    weakReading_allLawsSelected weakReading_allLawIdealExact
    integerTestPoint).mp integerTestPoint_fullyWeakSemanticLawful

private theorem integerTestPoint_not_strong_all_factors :
    ¬ Nonempty (FactorsThroughAllLawfulClosedSubscheme rawSystem
      twoChartReferenceModel strongReading strongReading_valid
      integerTestPoint) := by
  intro hfactor
  apply integerTestPoint_not_strong_semanticLawful
  have hfull :
      FullySemanticLawfulAlong rawSystem twoChartReferenceModel strongReading
        integerTestPoint :=
    (fullySemanticLawfulAlong_iff_fullIdealLawfulAlong rawSystem
      twoChartReferenceModel strongReading strongReading_valid
      strongReading_allLawsSelected strongReading_allLawIdealExact
      integerTestPoint).mpr
        ((fullIdealLawfulAlong_iff_nonempty_factorsThrough rawSystem
          twoChartReferenceModel strongReading strongReading_valid
          integerTestPoint).mpr hfactor)
  intro i _
  exact hfull i

/-- The strict required-law comparison is not an isomorphism. -/
theorem weakToStrongMap_not_isIso :
    ¬ IsIso (lawfulClosedSubschemeMap rawSystem twoChartReferenceModel
      weakReading_valid strongReading_valid
      weakReading_requiredClosed strongReading_requiredClosed
      weakToStrong weakToStrong_valid) := by
  intro hIso
  let comparison := lawfulClosedSubschemeMap rawSystem twoChartReferenceModel
    weakReading_valid strongReading_valid
    weakReading_requiredClosed strongReading_requiredClosed
    weakToStrong weakToStrong_valid
  letI : IsIso comparison := hIso
  let weakLift := factorizationLift rawSystem twoChartReferenceModel weakReading
    weakReading_valid weakReading_requiredClosed integerTestPoint
    integerTestPoint_idealLawful
  apply integerTestPoint_not_strong_factors
  refine ⟨⟨weakLift ≫ inv comparison, ?_⟩⟩
  calc
    (weakLift ≫ inv comparison) ≫
        lawfulClosedImmersion rawSystem twoChartReferenceModel strongReading
          strongReading_valid strongReading_requiredClosed =
      (weakLift ≫ inv comparison) ≫
        (comparison ≫ lawfulClosedImmersion rawSystem
          twoChartReferenceModel weakReading weakReading_valid
          weakReading_requiredClosed) := by
            rw [lawfulClosedSubschemeMap_immersion rawSystem
              twoChartReferenceModel weakReading_valid strongReading_valid
              weakReading_requiredClosed strongReading_requiredClosed
              weakToStrong weakToStrong_valid]
    _ = weakLift ≫ lawfulClosedImmersion rawSystem
        twoChartReferenceModel weakReading weakReading_valid
        weakReading_requiredClosed := by simp
    _ = integerTestPoint := factorizationLift_fac rawSystem
      twoChartReferenceModel weakReading weakReading_valid
      weakReading_requiredClosed integerTestPoint integerTestPoint_idealLawful

/-- The strict all-law comparison is not an isomorphism. -/
theorem weakToStrongAllMap_not_isIso :
    ¬ IsIso (allLawfulClosedSubschemeMap rawSystem twoChartReferenceModel
      weakReading_valid strongReading_valid
      weakToStrong weakToStrong_valid) := by
  intro hIso
  let comparison := allLawfulClosedSubschemeMap rawSystem
    twoChartReferenceModel weakReading_valid strongReading_valid
    weakToStrong weakToStrong_valid
  letI : IsIso comparison := hIso
  let weakLift := allLawFactorizationLift rawSystem twoChartReferenceModel
    weakReading weakReading_valid integerTestPoint
    integerTestPoint_fullWeakIdealLawful
  apply integerTestPoint_not_strong_all_factors
  refine ⟨⟨weakLift ≫ inv comparison, ?_⟩⟩
  calc
    (weakLift ≫ inv comparison) ≫
        allLawfulClosedImmersion rawSystem twoChartReferenceModel
          strongReading strongReading_valid =
      (weakLift ≫ inv comparison) ≫
        (comparison ≫ allLawfulClosedImmersion rawSystem
          twoChartReferenceModel weakReading weakReading_valid) := by
            rw [allLawfulClosedSubschemeMap_immersion rawSystem
              twoChartReferenceModel weakReading_valid strongReading_valid
              weakToStrong weakToStrong_valid]
    _ = weakLift ≫ allLawfulClosedImmersion rawSystem
        twoChartReferenceModel weakReading weakReading_valid := by simp
    _ = integerTestPoint := allLawFactorizationLift_fac rawSystem
      twoChartReferenceModel weakReading weakReading_valid integerTestPoint
      integerTestPoint_fullWeakIdealLawful

/-- A two-law index separating required and all-law readings. -/
inductive RequiredAllLawIndex
  | base
  | strengthening
  deriving DecidableEq

/-- Residual value of the selected required/all equation family. -/
private noncomputable def requiredAllResidual
    (index : RequiredAllLawIndex) (A : ArchitectureObject carrier) : Int := by
  classical
  exact if match index with
    | .base => hasDependencyCycle A
    | .strengthening => hasSubstitutionConflict A
    then 1 else 0

/-- The base equation is required while the strengthening equation remains optional. -/
noncomputable def requiredAllEquationSystem : ArchitecturalEquationSystem
    RingedSite.FiniteModel.site.contextPreorder where
  Index := RequiredAllLawIndex
  role
    | .base => EquationRole.required
    | .strengthening => EquationRole.optional
  Observable := fun _ => Int
  observableCommRing := fun _ => inferInstance
  restrict := fun _ => RingHom.id Int
  restrict_id := by intros; rfl
  restrict_comp := by intros; rfl
  violationCoordinate := fun _ index _ => match index with
    | .base => 2
    | .strengthening => 3
  violationCoordinate_restrict := by intros; rfl
  equationResidual := fun _ A index _ => requiredAllResidual index A
  equationResidual_restrict := by intros; rfl

/-- One-way natural-language display generated from the required/all equation family. -/
noncomputable def requiredAllLawUniverse : LawUniverse carrier :=
  requiredAllEquationSystem.toLegacyLawUniverse

/-- Characterizes the unique required equation in the two-equation fixture. -/
theorem requiredAllEquationSystem_required_iff (i : RequiredAllLawIndex) :
    requiredAllEquationSystem.Required i ↔ i = .base := by
  cases i <;> simp [requiredAllEquationSystem,
    ArchitecturalEquationSystem.Required]

/-- Characterizes the unique required law in the two-law SD9 universe. -/
theorem requiredAllLawUniverse_required_iff (i : RequiredAllLawIndex) :
    requiredAllLawUniverse.Required i ↔ i = .base := by
  cases i <;> simp [requiredAllLawUniverse, requiredAllEquationSystem,
    ArchitecturalEquationSystem.Required,
    ArchitecturalEquationSystem.toLegacyLawUniverse_required_iff]

/-- Records that the strengthening law is optional in the required/all fixture. -/
theorem requiredAllLawUniverse_optional_strengthening :
    requiredAllLawUniverse.Optional .strengthening := by
  rfl

private def requiredAllCoverageRequirements :
    Site.CoverageRequirements corePackage.object requiredAllEquationSystem
      RingedSite.FiniteModel.site.signature where
  requiredSupport := coverageRequirements.requiredSupport
  requiredEquationCoordinate := fun _ => True
  selectedViolationWitness := fun _ => True
  requiredAxis := coverageRequirements.requiredAxis
  supportVisibleOn := coverageRequirements.supportVisibleOn
  equationCoordinateVisibleOn := fun W _ =>
    W = twoPatchContext TwoPatchContextIndex.left ∨
      W = twoPatchContext TwoPatchContextIndex.right
  violationWitnessVisibleOn := fun W _ =>
    W = twoPatchContext TwoPatchContextIndex.left ∨
      W = twoPatchContext TwoPatchContextIndex.right
  axisReadableOn := coverageRequirements.axisReadableOn
  boundaryVisibleOn := coverageRequirements.boundaryVisibleOn

/-- The existing finite context geometry retargeted to the two-law universe. -/
noncomputable def requiredAllSite : Site.AATSite corePackage.object where
  contextPreorder := RingedSite.FiniteModel.site.contextPreorder
  equationSystem := requiredAllEquationSystem
  signature := RingedSite.FiniteModel.site.signature
  requirements := requiredAllCoverageRequirements
  overlap := RingedSite.FiniteModel.site.overlap

/-- Identifies the retargeted site's law universe with the two-law SD9 universe. -/
@[simp] theorem requiredAllSite_lawUniverse :
    requiredAllSite.equationSystem.toLegacyLawUniverse = requiredAllLawUniverse :=
  rfl

/-- The existing coordinates, relations, and restrictions on the two-law site. -/
def requiredAllRawSystem : RawAmbientRestrictionSystem requiredAllSite Int :=
  { coordFamily := RawPresheaf.coordFamily
    relationFamily := RawPresheaf.relationFamily
    restrictionStable := RawPresheaf.restrictionStable
    identity_polynomialMap := RawPresheaf.system.identity_polynomialMap
    composition_polynomialMap := RawPresheaf.system.composition_polynomialMap }

private theorem requiredAll_admissible_base_eq
    {X : requiredAllSite.category}
    (F : Site.AATCoverageFamily requiredAllCoverageRequirements
      requiredAllSite.overlap X) :
    X.ctx = twoPatchContext TwoPatchContextIndex.base := by
  rcases F.admissible.signatureAxisCoverage PUnit.unit trivial with ⟨i, _⟩
  have hboundary := F.admissible.boundaryCoverage i i
  simpa [requiredAllCoverageRequirements] using hboundary

private theorem requiredAll_admissible_has_base_patch
    {X : requiredAllSite.category}
    (F : Site.AATCoverageFamily requiredAllCoverageRequirements
      requiredAllSite.overlap X) :
    ∃ i : F.Index, F.patch i =
      twoPatchContext TwoPatchContextIndex.base := by
  rcases F.admissible.signatureAxisCoverage PUnit.unit trivial with ⟨i, hi⟩
  exact ⟨i, by simpa [requiredAllCoverageRequirements,
    coverageRequirements] using hi⟩

private theorem requiredAll_admissible_presieve_identity
    {X : requiredAllSite.category}
    (F : Site.AATCoverageFamily requiredAllCoverageRequirements
      requiredAllSite.overlap X) :
    F.presieve (𝟙 X) := by
  rcases requiredAll_admissible_has_base_patch F with ⟨i, hi⟩
  have hctx : X.ctx = F.patch i :=
    (requiredAll_admissible_base_eq F).trans hi.symm
  have hobj : X = Site.ContextCategoryObject.of
      requiredAllSite.contextPreorder (F.patch i) := by
    cases X
    simp only [Site.ContextCategoryObject.of] at hctx ⊢
    congr
  exact Presieve.ofArrows.mk' i hobj (Subsingleton.elim _ _)

private theorem requiredAll_admissible_generate_eq_top
    {X : requiredAllSite.category}
    (F : Site.AATCoverageFamily requiredAllCoverageRequirements
      requiredAllSite.overlap X) :
    Sieve.generate F.presieve = ⊤ :=
  Sieve.generate_of_contains_isSplitEpi (𝟙 X)
    (requiredAll_admissible_presieve_identity F)

private theorem requiredAllSite_topology_eq_bot :
    requiredAllSite.topology = ⊥ := by
  rw [Site.AATSite.topology_eq, Site.AATGrothendieckTopology,
    Precoverage.toGrothendieck_eq_sInf]
  apply le_antisymm
  · apply sInf_le
    intro X S hS
    rw [GrothendieckTopology.bot_covering]
    rcases hS with ⟨F, rfl⟩
    exact requiredAll_admissible_generate_eq_top F
  · exact bot_le

/-- Bottom-topology sheafification on the retargeted finite site. -/
noncomputable instance requiredAllHasSheafify :
    HasSheafify requiredAllSite.topology (AATCommAlgCat Int) := by
  rw [requiredAllSite_topology_eq_bot]
  exact HasSheafify.mk' _ _
    (sheafBotEquivalence (AATCommAlgCat Int)).symm.toAdjunction

private theorem requiredAllCanonicalComponentIsIso
    (W : requiredAllSite.category) :
    IsIso (requiredAllRawSystem.toRingedSite.canonical.app (op W)) := by
  have hsheaf : Presheaf.IsSheaf requiredAllSite.topology
      requiredAllRawSystem.toPresheaf := by
    rw [requiredAllSite_topology_eq_bot]
    exact Presheaf.isSheaf_bot _
  haveI : IsIso (CategoryTheory.toSheafify requiredAllSite.topology
      requiredAllRawSystem.toPresheaf) :=
    CategoryTheory.isIso_toSheafify
      (J := requiredAllSite.topology) hsheaf
  change IsIso ((CategoryTheory.toSheafify requiredAllSite.topology
    requiredAllRawSystem.toPresheaf).app (op W))
  infer_instance

private noncomputable def oldToRequiredBaseSectionIso :
    SheafifiedSectionRing rawSystem base ≅
      SheafifiedSectionRing requiredAllRawSystem base := by
  letI := StandardSchemeReading.canonicalComponentIsIso base
  letI := requiredAllCanonicalComponentIsIso base
  exact asIso
    ((inv (rawSystem.toRingedSite.canonical.app (op base))).right ≫
      (requiredAllRawSystem.toRingedSite.canonical.app (op base)).right)

private noncomputable def requiredAllBaseSchemeIso :
    architectureChartSpec requiredAllRawSystem base ≅
      twoChartReferenceModel.underlying := by
  rw [twoChart_underlying]
  exact AlgebraicGeometry.Scheme.Spec.mapIso oldToRequiredBaseSectionIso.op

private noncomputable def requiredAllDecoration :
    AATReadingDecoration requiredAllRawSystem
      twoChartReferenceModel.underlying :=
  AATReadingDecoration.pullback requiredAllRawSystem
    requiredAllBaseSchemeIso.inv
    (AATReadingDecoration.ofContext requiredAllRawSystem base)

private theorem requiredAllCoordinateRestriction_comp_self
    {X Y : requiredAllSite.category} (f : X ⟶ Y) :
    (RawPresheaf.coordinateRestriction f).polynomialMap.comp
        (RawPresheaf.coordinateRestriction f).polynomialMap =
      RingHom.id _ := by
  have hsign :
      (RawPresheaf.gauge X * RawPresheaf.gauge Y) *
          (RawPresheaf.gauge X * RawPresheaf.gauge Y) = 1 := by
    calc
      (RawPresheaf.gauge X * RawPresheaf.gauge Y) *
          (RawPresheaf.gauge X * RawPresheaf.gauge Y) =
          (RawPresheaf.gauge X * RawPresheaf.gauge X) *
            (RawPresheaf.gauge Y * RawPresheaf.gauge Y) := by ring
      _ = 1 := by
        rw [RawPresheaf.gauge_sq, RawPresheaf.gauge_sq, one_mul]
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [TypedCoordinateRestriction.polynomialMap]
  · intro i
    cases i
    change
      (RawPresheaf.coordinateRestriction f).polynomialMap
          ((RawPresheaf.coordinateRestriction f).polynomialMap
            (MvPolynomial.X ())) =
        MvPolynomial.X ()
    rw [RawPresheaf.coordinateRestriction_polynomialMap_X, map_mul]
    erw [TypedCoordinateRestriction.polynomialMap_C]
    rw [RawPresheaf.coordinateRestriction_polynomialMap_X]
    rw [← mul_assoc]
    erw [← MvPolynomial.C.map_mul]
    rw [hsign, map_one, one_mul]

private theorem requiredAllRawRestriction_comp_self
    {X Y : requiredAllSite.category} (f : X ⟶ Y) :
    (requiredAllRawSystem.restrictionStable f).quotientDesc.comp
        (requiredAllRawSystem.restrictionStable f).quotientDesc =
      RingHom.id _ := by
  apply Ideal.Quotient.ringHom_ext
  apply RingHom.ext
  intro p
  simp only [RingHom.comp_apply]
  have h := congrArg (fun q => q p)
    (requiredAllCoordinateRestriction_comp_self f)
  simpa only [RawPresheaf.system_restriction, RingHom.comp_apply,
    RingHom.id_apply] using congrArg
      (requiredAllRawSystem.relationFamily X).quotientMap h

private theorem requiredAllRawRestriction_bijective
    {X Y : requiredAllSite.category} (f : X ⟶ Y) :
    Function.Bijective
      (requiredAllRawSystem.restrictionStable f).quotientDesc := by
  apply Function.bijective_iff_has_inverse.mpr
  refine ⟨(requiredAllRawSystem.restrictionStable f).quotientDesc, ?_, ?_⟩
  · intro q
    have h := congrArg (fun g => g q)
      (requiredAllRawRestriction_comp_self f)
    simpa only [RingHom.comp_apply, RingHom.id_apply] using h
  · intro q
    have h := congrArg (fun g => g q)
      (requiredAllRawRestriction_comp_self f)
    simpa only [RingHom.comp_apply, RingHom.id_apply] using h

private theorem requiredAllRawRestrictionCommRing_isIso
    {X Y : requiredAllSite.category} (f : X ⟶ Y) :
    IsIso (CommRingCat.ofHom
      (requiredAllRawSystem.restrictionStable f).quotientDesc) := by
  rw [CategoryTheory.ConcreteCategory.isIso_iff_bijective]
  exact requiredAllRawRestriction_bijective f

private instance requiredAllRawRestriction_isIso
    {X Y : requiredAllSite.category} (f : X ⟶ Y) :
    IsIso (requiredAllRawSystem.toRingedSite.raw.map f.op) := by
  letI : IsIso ((Under.forget _).map
      (requiredAllRawSystem.toRingedSite.raw.map f.op)) := by
    change IsIso (CommRingCat.ofHom
      (requiredAllRawSystem.restrictionStable f).quotientDesc)
    exact requiredAllRawRestrictionCommRing_isIso f
  exact isIso_of_reflects_iso _ (Under.forget _)

private instance requiredAllSheafifiedRestrictionObject_isIso
    {X Y : requiredAllSite.category} (f : X ⟶ Y) :
    IsIso (requiredAllRawSystem.toRingedSite.structureSheaf.val.map f.op) := by
  letI := requiredAllCanonicalComponentIsIso X
  letI := requiredAllCanonicalComponentIsIso Y
  haveI : IsIso
      (requiredAllRawSystem.toRingedSite.raw.map f.op ≫
        requiredAllRawSystem.toRingedSite.canonical.app (op X)) := inferInstance
  have hn := requiredAllRawSystem.toRingedSite.canonical.naturality f.op
  haveI : IsIso
      (requiredAllRawSystem.toRingedSite.canonical.app (op Y) ≫
        requiredAllRawSystem.toRingedSite.structureSheaf.val.map f.op) := by
    rw [← hn]
    infer_instance
  exact CategoryTheory.IsIso.of_isIso_comp_left
    (requiredAllRawSystem.toRingedSite.canonical.app (op Y))
    (requiredAllRawSystem.toRingedSite.structureSheaf.val.map f.op)

private instance requiredAllSheafifiedRestriction_isIso
    {X Y : requiredAllSite.category} (f : X ⟶ Y) :
    IsIso (sheafifiedRestriction requiredAllRawSystem f) := by
  letI := requiredAllSheafifiedRestrictionObject_isIso f
  change IsIso
    (requiredAllRawSystem.toRingedSite.structureSheaf.val.map f.op).right
  infer_instance

private instance requiredAllArchitectureChartRestriction_isIso
    {X Y : requiredAllSite.category} (f : X ⟶ Y) :
    IsIso (architectureChartRestriction requiredAllRawSystem f) := by
  change IsIso (AlgebraicGeometry.Scheme.Spec.map
    (sheafifiedRestriction requiredAllRawSystem f).op)
  infer_instance

private noncomputable def requiredAllRestrictionChart
    {W : requiredAllSite.category} (f : W ⟶ base) :
    ArchitectureAffineChart requiredAllRawSystem
      twoChartReferenceModel.underlying requiredAllDecoration where
  context := W
  contextHom := f
  map := architectureChartRestriction requiredAllRawSystem f ≫
    requiredAllBaseSchemeIso.hom

private theorem requiredAllRestrictionChart_valid
    {W : requiredAllSite.category} (f : W ⟶ base) :
    IsArchitectureAffineChart requiredAllRawSystem
      (requiredAllRestrictionChart f) := by
  constructor
  · letI := requiredAllArchitectureChartRestriction_isIso f
    change AlgebraicGeometry.IsOpenImmersion
      (architectureChartRestriction requiredAllRawSystem f ≫
        requiredAllBaseSchemeIso.hom)
    infer_instance
  · change sheafifiedRestriction requiredAllRawSystem f =
      (AlgebraicGeometry.Scheme.ΓSpecIso
          (SheafifiedSectionRing requiredAllRawSystem base)).inv ≫
        requiredAllBaseSchemeIso.inv.appTop ≫
        (architectureChartRestriction requiredAllRawSystem f ≫
          requiredAllBaseSchemeIso.hom).appTop ≫
        (AlgebraicGeometry.Scheme.ΓSpecIso
          (SheafifiedSectionRing requiredAllRawSystem W)).hom
    have hcancel :
        requiredAllBaseSchemeIso.inv.appTop ≫
            requiredAllBaseSchemeIso.hom.appTop = 𝟙 _ := by
      rw [← Scheme.Hom.comp_appTop,
        requiredAllBaseSchemeIso.hom_inv_id, Scheme.Hom.id_appTop]
    have hcancel_assoc :
        requiredAllBaseSchemeIso.inv.appTop ≫
            requiredAllBaseSchemeIso.hom.appTop ≫
              (architectureChartRestriction requiredAllRawSystem f).appTop ≫
                (AlgebraicGeometry.Scheme.ΓSpecIso
                  (SheafifiedSectionRing requiredAllRawSystem W)).hom =
          (architectureChartRestriction requiredAllRawSystem f).appTop ≫
            (AlgebraicGeometry.Scheme.ΓSpecIso
              (SheafifiedSectionRing requiredAllRawSystem W)).hom := by
      rw [← Category.assoc requiredAllBaseSchemeIso.inv.appTop
        requiredAllBaseSchemeIso.hom.appTop, hcancel, Category.id_comp]
    rw [Scheme.Hom.comp_appTop,
      Category.assoc requiredAllBaseSchemeIso.hom.appTop
        (architectureChartRestriction requiredAllRawSystem f).appTop
        (AlgebraicGeometry.Scheme.ΓSpecIso
          (SheafifiedSectionRing requiredAllRawSystem W)).hom,
      hcancel_assoc]
    symm
    rw [architectureChartRestriction_appTop]
    exact (AlgebraicGeometry.Scheme.ΓSpecIso
      (SheafifiedSectionRing requiredAllRawSystem base)).inv_hom_id_assoc _

private noncomputable def requiredAllTwoChartAtlas :
    ArchitectureAffineAtlas requiredAllRawSystem
      twoChartReferenceModel.underlying requiredAllDecoration where
  Index := Bool
  chart
    | false => requiredAllRestrictionChart RawPresheaf.leftToBase
    | true => requiredAllRestrictionChart rightToBase

private theorem requiredAllTwoChartAtlas_chart_map_eq
    (i : requiredAllTwoChartAtlas.Index) :
    (requiredAllTwoChartAtlas.chart i).map =
      architectureChartRestriction requiredAllRawSystem
          (requiredAllTwoChartAtlas.chart i).contextHom ≫
        requiredAllBaseSchemeIso.hom := by
  cases i <;> rfl

private theorem requiredAllTwoChartAtlas_chart_isIso
    (i : requiredAllTwoChartAtlas.Index) :
    IsIso (requiredAllTwoChartAtlas.chart i).map := by
  rw [requiredAllTwoChartAtlas_chart_map_eq]
  infer_instance

private theorem requiredAllTwoChartAtlas_valid :
    IsArchitectureAffineAtlas requiredAllRawSystem
      requiredAllTwoChartAtlas := by
  constructor
  · intro i
    cases i
    · exact requiredAllRestrictionChart_valid RawPresheaf.leftToBase
    · exact requiredAllRestrictionChart_valid rightToBase
  · intro x
    letI := requiredAllTwoChartAtlas_chart_isIso false
    refine ⟨false,
      (asIso (requiredAllTwoChartAtlas.chart false).map).inv x, ?_⟩
    exact AlgebraicGeometry.Scheme.inv_hom_apply
      (asIso (requiredAllTwoChartAtlas.chart false).map) x

private theorem requiredAllTwoChartPair_isPullback
    (i j : requiredAllTwoChartAtlas.Index) :
    IsPullback
      (architectureChartRestriction requiredAllRawSystem
        (requiredAllTwoChartAtlas.pairToLeft requiredAllRawSystem i j))
      (architectureChartRestriction requiredAllRawSystem
        (requiredAllTwoChartAtlas.pairToRight requiredAllRawSystem i j))
      (requiredAllTwoChartAtlas.chart i).map
      (requiredAllTwoChartAtlas.chart j).map := by
  letI := requiredAllArchitectureChartRestriction_isIso
    (requiredAllTwoChartAtlas.pairToLeft requiredAllRawSystem i j)
  letI := requiredAllTwoChartAtlas_chart_isIso j
  apply IsPullback.of_horiz_isIso
  constructor
  rw [requiredAllTwoChartAtlas_chart_map_eq,
    requiredAllTwoChartAtlas_chart_map_eq,
    ← Category.assoc, ← Category.assoc,
    ← architectureChartRestriction_comp,
    ← architectureChartRestriction_comp]
  exact congrArg
    (fun q => architectureChartRestriction requiredAllRawSystem q ≫
      requiredAllBaseSchemeIso.hom)
    (Subsingleton.elim _ _)

private noncomputable def requiredAllTwoChartOverlapPresentation :
    ArchitectureOverlapPresentation requiredAllRawSystem
      requiredAllTwoChartAtlas where
  comparison i j := (requiredAllTwoChartPair_isPullback i j).isoPullback

private theorem requiredAllTwoChartOverlapPresentation_valid :
    IsArchitectureOverlapPresentation requiredAllRawSystem
      requiredAllTwoChartOverlapPresentation := by
  constructor
  · intro i j
    exact IsPullback.isoPullback_hom_fst
      (requiredAllTwoChartPair_isPullback i j)
  · intro i j
    exact IsPullback.isoPullback_hom_snd
      (requiredAllTwoChartPair_isPullback i j)

/-- The two-law finite model on the existing two-chart underlying Scheme. -/
noncomputable def requiredAllReferenceModel :
    StandardArchitectureScheme requiredAllRawSystem :=
  StandardArchitectureScheme.ofPresentation requiredAllRawSystem
    twoChartReferenceModel.underlying requiredAllDecoration
    requiredAllTwoChartAtlas requiredAllTwoChartAtlas_valid
    requiredAllTwoChartOverlapPresentation
    requiredAllTwoChartOverlapPresentation_valid

/-- Identifies the retargeted reference model with the original underlying Scheme. -/
theorem requiredAllReferenceModel_underlying :
    requiredAllReferenceModel.underlying =
      twoChartReferenceModel.underlying :=
  rfl

private noncomputable def requiredAllOrientedRawCoordinate
    (W : requiredAllSite.category) :
    requiredAllRawSystem.rawAlgebra W :=
  (requiredAllRawSystem.relationFamily W).quotientMap
    (MvPolynomial.C (RawPresheaf.gauge W) * MvPolynomial.X ())

private theorem requiredAllRawSystem_restrictionStable
    {source target : requiredAllSite.category} (f : source ⟶ target) :
    requiredAllRawSystem.restrictionStable f =
      RawPresheaf.system.restrictionStable f :=
  rfl

private theorem requiredAllOrientedRawCoordinate_restrict
    {source target : requiredAllSite.category} (f : source ⟶ target) :
    (requiredAllRawSystem.restrictionStable f).quotientDesc
        (requiredAllOrientedRawCoordinate target) =
      requiredAllOrientedRawCoordinate source := by
  rw [requiredAllOrientedRawCoordinate, requiredAllOrientedRawCoordinate,
    RestrictionStableStructuralRelations.quotientDesc_mk,
    requiredAllRawSystem_restrictionStable,
    RawPresheaf.system_restriction, map_mul]
  erw [(RawPresheaf.coordinateRestriction f).polynomialMap_C]
  erw [(RawPresheaf.coordinateRestriction f).polynomialMap_X]
  have hcoeff :
      RawPresheaf.gauge target *
          (RawPresheaf.gauge source * RawPresheaf.gauge target) =
        RawPresheaf.gauge source := by
    calc
      RawPresheaf.gauge target *
          (RawPresheaf.gauge source * RawPresheaf.gauge target) =
          RawPresheaf.gauge source *
            (RawPresheaf.gauge target * RawPresheaf.gauge target) := by ring
      _ = RawPresheaf.gauge source := by
        rw [RawPresheaf.gauge_sq, mul_one]
  change
    (requiredAllRawSystem.relationFamily source).quotientMap
        (MvPolynomial.C (RawPresheaf.gauge target) *
          (MvPolynomial.C
            (RawPresheaf.gauge source * RawPresheaf.gauge target) *
              MvPolynomial.X ())) =
      (requiredAllRawSystem.relationFamily source).quotientMap
        (MvPolynomial.C (RawPresheaf.gauge source) * MvPolynomial.X ())
  calc
    (requiredAllRawSystem.relationFamily source).quotientMap
        (MvPolynomial.C (RawPresheaf.gauge target) *
          (MvPolynomial.C
            (RawPresheaf.gauge source * RawPresheaf.gauge target) *
              MvPolynomial.X ())) =
      (requiredAllRawSystem.relationFamily source).quotientMap
        (MvPolynomial.C
            (RawPresheaf.gauge target *
              (RawPresheaf.gauge source * RawPresheaf.gauge target)) *
          MvPolynomial.X ()) := by
        congr 1
        simp only [MvPolynomial.C_mul]
        ring
    _ = _ := by rw [hcoeff]

private theorem requiredAllRawRestriction_id
    (W : requiredAllSite.category)
    (x : requiredAllRawSystem.rawAlgebra W) :
    (requiredAllRawSystem.restrictionStable (𝟙 W)).quotientDesc x = x := by
  have h := congrArg (fun q => q x) (requiredAllRawSystem.quotientDesc_id W)
  simpa using h

private theorem requiredAllRawRestriction_comp
    {W₀ W₁ W₂ : requiredAllSite.category}
    (f : W₀ ⟶ W₁) (g : W₁ ⟶ W₂)
    (x : requiredAllRawSystem.rawAlgebra W₂) :
    (requiredAllRawSystem.restrictionStable (f ≫ g)).quotientDesc x =
      (requiredAllRawSystem.restrictionStable f).quotientDesc
        ((requiredAllRawSystem.restrictionStable g).quotientDesc x) := by
  have h := congrArg (fun q => q x)
    (requiredAllRawSystem.quotientDesc_comp f g)
  simpa [RingHom.comp_apply] using h

/-- The two-law semantic core carries `x - 1` on the base law and `x + 1` on its strengthening. -/
noncomputable def requiredAllLawEquationCore :
    SemanticLawEquationWitnessIdealCore requiredAllSite where
  Observable W := requiredAllRawSystem.rawAlgebra W
  observableCommRing W := inferInstance
  restrict f := (requiredAllRawSystem.restrictionStable f).quotientDesc
  restrict_id := requiredAllRawRestriction_id
  restrict_comp := requiredAllRawRestriction_comp
  violationWitness W i a :=
    match i with
    | .base =>
        match a with
        | FiniteAtom.componentA => requiredAllOrientedRawCoordinate W - 1
        | _ => 0
    | .strengthening =>
        match a with
        | FiniteAtom.componentB => requiredAllOrientedRawCoordinate W + 1
        | _ => 0
  violationWitness_restrict := by
    intro source target f lawIndex atom
    cases lawIndex <;> cases atom <;>
      simp only [map_sub, map_add, map_one, map_zero,
        requiredAllOrientedRawCoordinate_restrict]
  supportAtom := FiniteAtom.componentA
  supportLawIndex := .base
  supportLawIndex_required := by rfl

/-- The two-law core is identified objectwise with the retargeted raw quotient. -/
noncomputable def requiredAllSchemeBridge :
    SemanticLawEquationSchemeBridge requiredAllRawSystem
      requiredAllLawEquationCore where
  toRawPresentation W := RingEquiv.refl (requiredAllRawSystem.rawAlgebra W)

/-- Verifies restriction naturality and presentation stability for the required/all bridge. -/
theorem requiredAllSchemeBridge_valid :
    IsSemanticLawEquationSchemeBridge requiredAllRawSystem
      requiredAllLawEquationCore requiredAllSchemeBridge where
  restriction_natural := by
    intro source target f x
    have hn := requiredAllRawSystem.toRingedSite.canonical.naturality f.op
    have ha := congrArg (fun q => q.right x) hn
    change
      (requiredAllRawSystem.toRingedSite.canonical.app (op source)).right
          ((requiredAllRawSystem.restrictionStable f).quotientDesc x) =
        (requiredAllRawSystem.toRingedSite.structureSheaf.val.map f.op).right
          ((requiredAllRawSystem.toRingedSite.canonical.app (op target)).right x)
    simpa only [CommRingCat.comp_apply,
      RawAmbientRestrictionSystem.toRingedSite_raw] using ha
  presentation_stable W := {
    canonical_isIso := requiredAllCanonicalComponentIsIso W
  }

/-- The global coordinate whose two law equations generate the required/all comparison. -/
noncomputable def requiredAllBaseGlobalCoordinate :
    Γ(requiredAllReferenceModel.underlying, ⊤) :=
  requiredAllReferenceModel.decoration.coordinateSection
    requiredAllRawSystem ()

private theorem requiredLaw_componentA_raw_equation :
    requiredAllLawEquationCore.violationWitness base .base
        FiniteAtom.componentA =
      ((requiredAllRawSystem.relationFamily base).quotientMap
          (MvPolynomial.X ()) - 1 :
        requiredAllRawSystem.rawAlgebra base) := by
  simp only [requiredAllLawEquationCore]
  rw [requiredAllOrientedRawCoordinate, gauge_base]
  simp

private theorem strengtheningLaw_componentB_raw_equation :
    requiredAllLawEquationCore.violationWitness base .strengthening
        FiniteAtom.componentB =
      ((requiredAllRawSystem.relationFamily base).quotientMap
          (MvPolynomial.X ()) + 1 :
        requiredAllRawSystem.rawAlgebra base) := by
  simp only [requiredAllLawEquationCore]
  rw [requiredAllOrientedRawCoordinate, gauge_base]
  simp

/-- Computes the required law equation as `x - 1` on the component-A atom. -/
theorem requiredLaw_componentA_equation :
    semanticCoreGlobalEquation requiredAllRawSystem requiredAllReferenceModel
        requiredAllLawEquationCore requiredAllSchemeBridge
        .base FiniteAtom.componentA =
      requiredAllBaseGlobalCoordinate - 1 := by
  rw [semanticCoreGlobalEquation]
  change
    requiredAllDecoration.interpretation
      (requiredAllSchemeBridge.toSheafifiedSection base
        (requiredAllLawEquationCore.violationWitness base .base
          FiniteAtom.componentA)) =
      requiredAllDecoration.coordinateSection requiredAllRawSystem () - 1
  rw [requiredLaw_componentA_raw_equation]
  simp only [SemanticLawEquationSchemeBridge.toSheafifiedSection,
    requiredAllSchemeBridge, RingHom.comp_apply, map_sub, map_one,
    AATReadingDecoration.coordinateSection_apply]
  rfl

/-- Computes the optional strengthening equation as `x + 1` on component B. -/
theorem strengtheningLaw_componentB_equation :
    semanticCoreGlobalEquation requiredAllRawSystem requiredAllReferenceModel
        requiredAllLawEquationCore requiredAllSchemeBridge
        .strengthening FiniteAtom.componentB =
      requiredAllBaseGlobalCoordinate + 1 := by
  rw [semanticCoreGlobalEquation]
  change
    requiredAllDecoration.interpretation
      (requiredAllSchemeBridge.toSheafifiedSection base
        (requiredAllLawEquationCore.violationWitness base .strengthening
          FiniteAtom.componentB)) =
      requiredAllDecoration.coordinateSection requiredAllRawSystem () + 1
  rw [strengtheningLaw_componentB_raw_equation]
  simp only [SemanticLawEquationSchemeBridge.toSheafifiedSection,
    requiredAllSchemeBridge, RingHom.comp_apply, map_add, map_one,
    AATReadingDecoration.coordinateSection_apply]
  rfl

/-- The closed-equational reading that selects both laws while marking only the base law required. -/
noncomputable def requiredAllReading :
    ClosedEquationalLawReading requiredAllRawSystem requiredAllReferenceModel :=
  ClosedEquationalLawReading.ofSemanticCore requiredAllRawSystem
    requiredAllReferenceModel requiredAllLawEquationCore requiredAllSchemeBridge

/-- Verifies witness compatibility for the required/all reading. -/
theorem requiredAllReading_witnessCompatible :
    IsClosedEquationalWitnessReading requiredAllRawSystem
      requiredAllReferenceModel requiredAllReading :=
  ClosedEquationalLawReading.ofSemanticCore_witnessCompatible
    requiredAllRawSystem requiredAllReferenceModel requiredAllLawEquationCore
    requiredAllSchemeBridge

/-- Verifies the full closed-equational recognition predicate for the required/all reading. -/
theorem requiredAllReading_valid :
    IsClosedEquationalLawReading requiredAllRawSystem
      requiredAllReferenceModel requiredAllReading :=
  ClosedEquationalLawReading.ofSemanticCore_valid requiredAllRawSystem
    requiredAllReferenceModel requiredAllLawEquationCore requiredAllSchemeBridge

/-- Constructs required closedness from the canonical semantic core. -/
theorem requiredAllReading_requiredClosed :
    RequiredClosed requiredAllRawSystem requiredAllReferenceModel
      requiredAllReading :=
  ClosedEquationalLawReading.ofSemanticCore_requiredClosed
    requiredAllRawSystem requiredAllReferenceModel requiredAllLawEquationCore
    requiredAllSchemeBridge

/-- Shows that every law in the two-law fixture is selected and closed. -/
theorem requiredAllReading_allLawsSelected :
    AllLawsSelected requiredAllRawSystem requiredAllReferenceModel
      requiredAllReading :=
  ClosedEquationalLawReading.ofSemanticCore_allLawsSelected
    requiredAllRawSystem requiredAllReferenceModel requiredAllLawEquationCore
    requiredAllSchemeBridge

/-- Shows that required indices form a proper subset of the closed indices. -/
theorem required_indices_ssubset_closed :
    {i | requiredAllSite.equationSystem.toLegacyLawUniverse.Required i} ⊂
      requiredAllReading.closed := by
  rw [Set.ssubset_iff_exists]
  constructor
  · intro i _
    exact requiredAllReading_allLawsSelected.closed i
  · refine ⟨RequiredAllLawIndex.strengthening,
      requiredAllReading_allLawsSelected.closed
        RequiredAllLawIndex.strengthening, ?_⟩
    intro hrequired
    have hrequired' :
        requiredAllLawUniverse.Required RequiredAllLawIndex.strengthening := by
      simpa only [requiredAllSite_lawUniverse] using hrequired
    have heq := (requiredAllLawUniverse_required_iff
      RequiredAllLawIndex.strengthening).mp hrequired'
    exact RequiredAllLawIndex.noConfusion heq

/-- Characterizes selected laws at every named affine context in the two-law fixture. -/
theorem requiredAllReading_selected
    (V : requiredAllReferenceModel.underlying.affineOpens)
    (i : RequiredAllLawIndex) :
    requiredAllReading.selected V i :=
  ClosedEquationalLawReading.ofSemanticCore_selected requiredAllRawSystem
    requiredAllReferenceModel requiredAllLawEquationCore requiredAllSchemeBridge V i

/-- Shows that required indices form a proper subset of the context-selected indices. -/
theorem required_indices_ssubset_selected
    (V : requiredAllReferenceModel.underlying.affineOpens) :
    {i | requiredAllSite.equationSystem.toLegacyLawUniverse.Required i} ⊂
      {i | requiredAllReading.selected V i} := by
  rw [Set.ssubset_iff_exists]
  constructor
  · intro i _
    exact requiredAllReading_selected V i
  · refine ⟨RequiredAllLawIndex.strengthening,
      requiredAllReading_selected V RequiredAllLawIndex.strengthening, ?_⟩
    intro hrequired
    have hrequired' :
        requiredAllLawUniverse.Required RequiredAllLawIndex.strengthening := by
      simpa only [requiredAllSite_lawUniverse] using hrequired
    have heq := (requiredAllLawUniverse_required_iff
      RequiredAllLawIndex.strengthening).mp hrequired'
    exact RequiredAllLawIndex.noConfusion heq

private def requiredAllRawEvalOne :
    requiredAllRawSystem.rawAlgebra base →+* Int :=
  Ideal.Quotient.lift (requiredAllRawSystem.relationFamily base).JStruct
    polynomialEvalOne (by
      intro p hp
      exact base_JStruct_le_ker_polynomialEvalOne hp)

private noncomputable def requiredAllSheafifiedEvalOne :
    SheafifiedSectionRing requiredAllRawSystem base →+* Int := by
  letI := requiredAllCanonicalComponentIsIso base
  exact requiredAllRawEvalOne.comp
    (inv (requiredAllRawSystem.toRingedSite.canonical.app (op base))).right.hom

private noncomputable def requiredAllGlobalEvalOne :
    Γ(requiredAllReferenceModel.underlying, ⊤) →+* Int :=
  requiredAllSheafifiedEvalOne.comp
    ((AlgebraicGeometry.Scheme.ΓSpecIso
      (SheafifiedSectionRing requiredAllRawSystem base)).hom.hom.comp
        requiredAllBaseSchemeIso.hom.appTop.hom)

private theorem requiredAllBaseGlobalCoordinate_eq :
    requiredAllBaseGlobalCoordinate =
      requiredAllBaseSchemeIso.inv.appTop
        ((AlgebraicGeometry.Scheme.ΓSpecIso
          (SheafifiedSectionRing requiredAllRawSystem base)).inv
            ((requiredAllRawSystem.toRingedSite.canonical.app (op base)).right
              ((requiredAllRawSystem.relationFamily base).quotientMap
                (MvPolynomial.X ())))) := by
  rfl

private theorem requiredAllGlobalEvalOne_baseGlobalCoordinate :
    requiredAllGlobalEvalOne requiredAllBaseGlobalCoordinate = 1 := by
  letI := requiredAllCanonicalComponentIsIso base
  rw [requiredAllBaseGlobalCoordinate_eq]
  change requiredAllRawEvalOne
    ((inv (requiredAllRawSystem.toRingedSite.canonical.app (op base))).right
      ((AlgebraicGeometry.Scheme.ΓSpecIso
        (SheafifiedSectionRing requiredAllRawSystem base)).hom
        (requiredAllBaseSchemeIso.hom.appTop
          (requiredAllBaseSchemeIso.inv.appTop
            ((AlgebraicGeometry.Scheme.ΓSpecIso
              (SheafifiedSectionRing requiredAllRawSystem base)).inv
                ((requiredAllRawSystem.toRingedSite.canonical.app (op base)).right
                  ((requiredAllRawSystem.relationFamily base).quotientMap
                    (MvPolynomial.X ())))))))) = 1
  have hscheme (x : Γ(architectureChartSpec requiredAllRawSystem base, ⊤)) :
      requiredAllBaseSchemeIso.hom.appTop
          (requiredAllBaseSchemeIso.inv.appTop x) = x := by
    have hcancel :
        requiredAllBaseSchemeIso.inv.appTop ≫
            requiredAllBaseSchemeIso.hom.appTop = 𝟙 _ := by
      rw [← Scheme.Hom.comp_appTop,
        requiredAllBaseSchemeIso.hom_inv_id, Scheme.Hom.id_appTop]
    simpa only [CommRingCat.comp_apply, CommRingCat.id_apply] using
      congrArg (fun q => q x) hcancel
  rw [hscheme]
  rw [(AlgebraicGeometry.Scheme.ΓSpecIso
    (SheafifiedSectionRing requiredAllRawSystem base)).inv_hom_id_apply]
  have hcanonical :
      (requiredAllRawSystem.toRingedSite.canonical.app (op base)).right ≫
          (inv (requiredAllRawSystem.toRingedSite.canonical.app (op base))).right =
        𝟙 _ := by
    change
      (Under.forget _).map
          (requiredAllRawSystem.toRingedSite.canonical.app (op base)) ≫
        (Under.forget _).map
          (inv (requiredAllRawSystem.toRingedSite.canonical.app (op base))) = 𝟙 _
    rw [← CategoryTheory.Functor.map_comp, IsIso.hom_inv_id,
      CategoryTheory.Functor.map_id]
  change requiredAllRawEvalOne
    (((requiredAllRawSystem.toRingedSite.canonical.app (op base)).right ≫
      (inv (requiredAllRawSystem.toRingedSite.canonical.app (op base))).right)
        ((requiredAllRawSystem.relationFamily base).quotientMap
          (MvPolynomial.X ()))) = 1
  rw [hcanonical, CommRingCat.id_apply]
  rw [requiredAllRawEvalOne,
    AAT.AG.LawAlgebra.StructuralRelationFamily.quotientMap,
    Ideal.Quotient.lift_mk]
  rw [polynomialEvalOne]
  exact MvPolynomial.eval₂Hom_X' (RingHom.id Int) (fun _ => 1) ()

private def requiredAllRawEvalModTwo :
    requiredAllRawSystem.rawAlgebra base →+* ZMod 2 :=
  Ideal.Quotient.lift (requiredAllRawSystem.relationFamily base).JStruct
    polynomialEvalModTwo (by
      intro p hp
      exact base_JStruct_le_ker_polynomialEvalModTwo hp)

private noncomputable def requiredAllSheafifiedEvalModTwo :
    SheafifiedSectionRing requiredAllRawSystem base →+* ZMod 2 := by
  letI := requiredAllCanonicalComponentIsIso base
  exact requiredAllRawEvalModTwo.comp
    (inv (requiredAllRawSystem.toRingedSite.canonical.app (op base))).right.hom

private noncomputable def requiredAllGlobalEvalModTwo :
    Γ(requiredAllReferenceModel.underlying, ⊤) →+* ZMod 2 :=
  requiredAllSheafifiedEvalModTwo.comp
    ((AlgebraicGeometry.Scheme.ΓSpecIso
      (SheafifiedSectionRing requiredAllRawSystem base)).hom.hom.comp
        requiredAllBaseSchemeIso.hom.appTop.hom)

private theorem requiredAllGlobalEvalModTwo_baseGlobalCoordinate :
    requiredAllGlobalEvalModTwo requiredAllBaseGlobalCoordinate = 1 := by
  letI := requiredAllCanonicalComponentIsIso base
  rw [requiredAllBaseGlobalCoordinate_eq]
  change requiredAllRawEvalModTwo
    ((inv (requiredAllRawSystem.toRingedSite.canonical.app (op base))).right
      ((AlgebraicGeometry.Scheme.ΓSpecIso
        (SheafifiedSectionRing requiredAllRawSystem base)).hom
        (requiredAllBaseSchemeIso.hom.appTop
          (requiredAllBaseSchemeIso.inv.appTop
            ((AlgebraicGeometry.Scheme.ΓSpecIso
              (SheafifiedSectionRing requiredAllRawSystem base)).inv
                ((requiredAllRawSystem.toRingedSite.canonical.app (op base)).right
                  ((requiredAllRawSystem.relationFamily base).quotientMap
                    (MvPolynomial.X ())))))))) = 1
  have hscheme (x : Γ(architectureChartSpec requiredAllRawSystem base, ⊤)) :
      requiredAllBaseSchemeIso.hom.appTop
          (requiredAllBaseSchemeIso.inv.appTop x) = x := by
    have hcancel :
        requiredAllBaseSchemeIso.inv.appTop ≫
            requiredAllBaseSchemeIso.hom.appTop = 𝟙 _ := by
      rw [← Scheme.Hom.comp_appTop,
        requiredAllBaseSchemeIso.hom_inv_id, Scheme.Hom.id_appTop]
    simpa only [CommRingCat.comp_apply, CommRingCat.id_apply] using
      congrArg (fun q => q x) hcancel
  rw [hscheme]
  rw [(AlgebraicGeometry.Scheme.ΓSpecIso
    (SheafifiedSectionRing requiredAllRawSystem base)).inv_hom_id_apply]
  have hcanonical :
      (requiredAllRawSystem.toRingedSite.canonical.app (op base)).right ≫
          (inv (requiredAllRawSystem.toRingedSite.canonical.app (op base))).right =
        𝟙 _ := by
    change
      (Under.forget _).map
          (requiredAllRawSystem.toRingedSite.canonical.app (op base)) ≫
        (Under.forget _).map
          (inv (requiredAllRawSystem.toRingedSite.canonical.app (op base))) = 𝟙 _
    rw [← CategoryTheory.Functor.map_comp, IsIso.hom_inv_id,
      CategoryTheory.Functor.map_id]
  change requiredAllRawEvalModTwo
    (((requiredAllRawSystem.toRingedSite.canonical.app (op base)).right ≫
      (inv (requiredAllRawSystem.toRingedSite.canonical.app (op base))).right)
        ((requiredAllRawSystem.relationFamily base).quotientMap
          (MvPolynomial.X ()))) = 1
  rw [hcanonical, CommRingCat.id_apply]
  rw [requiredAllRawEvalModTwo,
    AAT.AG.LawAlgebra.StructuralRelationFamily.quotientMap,
    Ideal.Quotient.lift_mk]
  rw [polynomialEvalModTwo]
  exact MvPolynomial.eval₂Hom_X'
    (Int.castRingHom (ZMod 2)) (fun _ => 1) ()

private theorem requiredLaw_other_equation
    (a : carrier.Atom) (ha : a ≠ FiniteAtom.componentA) :
    semanticCoreGlobalEquation requiredAllRawSystem requiredAllReferenceModel
        requiredAllLawEquationCore requiredAllSchemeBridge .base a = 0 := by
  cases a <;> simp_all [semanticCoreGlobalEquation,
    requiredAllLawEquationCore, requiredAllSchemeBridge,
    SemanticLawEquationSchemeBridge.toSheafifiedSection]

private theorem requiredAll_local_top_eq_span
    (i : RequiredAllLawIndex) (hi : requiredAllReading.closed i) :
    localLawWitnessIdeal requiredAllRawSystem requiredAllReferenceModel
        (requiredAllReading.witness i hi) ambientTopAffineOpen =
      Ideal.span (Set.range (semanticCoreGlobalEquation requiredAllRawSystem
        requiredAllReferenceModel requiredAllLawEquationCore
        requiredAllSchemeBridge i)) := by
  rw [← lawWitnessIdealSheaf_ideal requiredAllRawSystem
    requiredAllReferenceModel requiredAllReading
    requiredAllReading_witnessCompatible i hi ambientTopAffineOpen]
  rw [lawWitnessIdealSheaf_ofGlobalSections requiredAllRawSystem
    requiredAllReferenceModel requiredAllReading
    requiredAllReading_witnessCompatible i hi
    (semanticCoreGlobalEquation requiredAllRawSystem requiredAllReferenceModel
      requiredAllLawEquationCore requiredAllSchemeBridge i)]
  · rw [Scheme.IdealSheafData.ofIdealTop_ideal]
    simp [ambientTopAffineOpen]
  · simpa only [requiredAllReading] using
      ClosedEquationalLawReading.ofSemanticCore_witness requiredAllRawSystem
        requiredAllReferenceModel requiredAllLawEquationCore
        requiredAllSchemeBridge i hi

private theorem required_base_span_le_ker_globalEvalOne :
    Ideal.span (Set.range (semanticCoreGlobalEquation requiredAllRawSystem
      requiredAllReferenceModel requiredAllLawEquationCore
      requiredAllSchemeBridge .base)) ≤
      RingHom.ker requiredAllGlobalEvalOne := by
  apply Ideal.span_le.mpr
  rintro _ ⟨a, rfl⟩
  cases a
  · rw [requiredLaw_componentA_equation]
    change requiredAllGlobalEvalOne
      (requiredAllBaseGlobalCoordinate - 1) = 0
    rw [map_sub, map_one, requiredAllGlobalEvalOne_baseGlobalCoordinate]
    simp
  all_goals
    rw [requiredLaw_other_equation _ (by simp)]
    simp

private theorem required_ideal_top_le_ker_globalEvalOne :
    (lawGeneratedIdealSheaf requiredAllRawSystem requiredAllReferenceModel
      requiredAllReading requiredAllReading_valid
      requiredAllReading_requiredClosed).ideal ambientTopAffineOpen ≤
        RingHom.ker requiredAllGlobalEvalOne := by
  rw [lawGeneratedIdealSheaf_ideal]
  refine iSup_le fun i => ?_
  rcases i with ⟨i, hrequired, hselected⟩
  have hi : i = RequiredAllLawIndex.base :=
    (requiredAllEquationSystem_required_iff i).mp hrequired
  subst i
  rw [requiredAll_local_top_eq_span]
  exact required_base_span_le_ker_globalEvalOne

/-- optional strengthening lawがall idealを真に強める。 -/
theorem required_ideal_lt_all_ideal :
    lawGeneratedIdealSheaf requiredAllRawSystem requiredAllReferenceModel
        requiredAllReading requiredAllReading_valid
        requiredAllReading_requiredClosed <
      allLawGeneratedIdealSheaf requiredAllRawSystem requiredAllReferenceModel
        requiredAllReading requiredAllReading_valid := by
  refine lt_of_le_of_ne
    (lawGeneratedIdealSheaf_le_all requiredAllRawSystem
      requiredAllReferenceModel requiredAllReading requiredAllReading_valid
      requiredAllReading_requiredClosed) ?_
  intro heq
  have hlocal :
      semanticCoreGlobalEquation requiredAllRawSystem requiredAllReferenceModel
          requiredAllLawEquationCore requiredAllSchemeBridge .strengthening
          FiniteAtom.componentB ∈
        localLawWitnessIdeal requiredAllRawSystem requiredAllReferenceModel
          (requiredAllReading.witness .strengthening
            (requiredAllReading_allLawsSelected.closed .strengthening))
          ambientTopAffineOpen := by
    rw [requiredAll_local_top_eq_span]
    exact Ideal.subset_span ⟨FiniteAtom.componentB, rfl⟩
  let idx : {i : RequiredAllLawIndex //
      requiredAllReading.selected ambientTopAffineOpen i} :=
    ⟨.strengthening, requiredAllReading_selected _ _⟩
  have hfull :
      semanticCoreGlobalEquation requiredAllRawSystem requiredAllReferenceModel
          requiredAllLawEquationCore requiredAllSchemeBridge .strengthening
          FiniteAtom.componentB ∈
        (allLawGeneratedIdealSheaf requiredAllRawSystem requiredAllReferenceModel
          requiredAllReading requiredAllReading_valid).ideal
            ambientTopAffineOpen := by
    rw [allLawGeneratedIdealSheaf_ideal]
    exact (le_iSup (fun i : {i : RequiredAllLawIndex //
      requiredAllReading.selected ambientTopAffineOpen i} =>
        localLawWitnessIdeal requiredAllRawSystem requiredAllReferenceModel
          (requiredAllReading.witness i.1
            (requiredAllReading_valid.selected_closed
              ambientTopAffineOpen i.1 i.2)) ambientTopAffineOpen) idx) hlocal
  have hrequired :
      semanticCoreGlobalEquation requiredAllRawSystem requiredAllReferenceModel
          requiredAllLawEquationCore requiredAllSchemeBridge .strengthening
          FiniteAtom.componentB ∈
        (lawGeneratedIdealSheaf requiredAllRawSystem requiredAllReferenceModel
          requiredAllReading requiredAllReading_valid
          requiredAllReading_requiredClosed).ideal ambientTopAffineOpen := by
    rw [heq]
    exact hfull
  have hzero := required_ideal_top_le_ker_globalEvalOne hrequired
  rw [strengtheningLaw_componentB_equation] at hzero
  change requiredAllGlobalEvalOne
    (requiredAllBaseGlobalCoordinate + 1) = 0 at hzero
  rw [map_add, map_one, requiredAllGlobalEvalOne_baseGlobalCoordinate] at hzero
  norm_num at hzero

/-- 同じreading内のall locusからrequired locusへのmapは同型ではない。 -/
theorem fullToRequiredLawfulMap_not_isIso :
    ¬ IsIso (fullToRequiredLawfulMap requiredAllRawSystem
      requiredAllReferenceModel requiredAllReading
      requiredAllReading_valid requiredAllReading_requiredClosed) := by
  intro hIso
  let comparison := fullToRequiredLawfulMap requiredAllRawSystem
    requiredAllReferenceModel requiredAllReading requiredAllReading_valid
    requiredAllReading_requiredClosed
  letI : IsIso comparison := hIso
  have hker := Scheme.Hom.ker_comp_of_isIso comparison
    (lawfulClosedImmersion requiredAllRawSystem requiredAllReferenceModel
      requiredAllReading requiredAllReading_valid
      requiredAllReading_requiredClosed)
  have heq :
      allLawGeneratedIdealSheaf requiredAllRawSystem requiredAllReferenceModel
          requiredAllReading requiredAllReading_valid =
        lawGeneratedIdealSheaf requiredAllRawSystem requiredAllReferenceModel
          requiredAllReading requiredAllReading_valid
          requiredAllReading_requiredClosed := by
    calc
      allLawGeneratedIdealSheaf requiredAllRawSystem requiredAllReferenceModel
          requiredAllReading requiredAllReading_valid =
        (allLawfulClosedImmersion requiredAllRawSystem requiredAllReferenceModel
          requiredAllReading requiredAllReading_valid).ker :=
            (Scheme.IdealSheafData.ker_subschemeι _).symm
      _ = (comparison ≫ lawfulClosedImmersion requiredAllRawSystem
          requiredAllReferenceModel requiredAllReading requiredAllReading_valid
          requiredAllReading_requiredClosed).ker := by
            rw [fullToRequiredLawfulMap_immersion]
      _ = (lawfulClosedImmersion requiredAllRawSystem requiredAllReferenceModel
          requiredAllReading requiredAllReading_valid
          requiredAllReading_requiredClosed).ker := hker
      _ = lawGeneratedIdealSheaf requiredAllRawSystem requiredAllReferenceModel
          requiredAllReading requiredAllReading_valid
          requiredAllReading_requiredClosed :=
            lawfulClosedImmersion_ker requiredAllRawSystem
              requiredAllReferenceModel requiredAllReading
              requiredAllReading_valid requiredAllReading_requiredClosed
  exact required_ideal_lt_all_ideal.ne heq.symm

/-- The integral point satisfying the required equation in the two-law fixture. -/
noncomputable def selectedRequiredPoint :
    AlgebraicGeometry.Scheme.Spec.obj (op (CommRingCat.of Int)) ⟶
      requiredAllReferenceModel.underlying :=
  AlgebraicGeometry.Spec.map
      (CommRingCat.ofHom requiredAllSheafifiedEvalOne) ≫
    requiredAllBaseSchemeIso.hom

/-- The mod-two point satisfying both equations in the two-law fixture. -/
noncomputable def selectedModTwoPoint :
    AlgebraicGeometry.Scheme.Spec.obj (op (CommRingCat.of (ZMod 2))) ⟶
      requiredAllReferenceModel.underlying :=
  AlgebraicGeometry.Spec.map
      (CommRingCat.ofHom requiredAllSheafifiedEvalModTwo) ≫
    requiredAllBaseSchemeIso.hom

private theorem selectedRequiredPoint_normalized_appTop :
    selectedRequiredPoint.appTop ≫
        (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of Int)).hom =
      CommRingCat.ofHom requiredAllGlobalEvalOne := by
  simpa only [selectedRequiredPoint, Scheme.Hom.comp_appTop,
    Category.assoc, requiredAllGlobalEvalOne, CommRingCat.hom_comp] using
    congrArg (fun q => requiredAllBaseSchemeIso.hom.appTop ≫ q)
      (AlgebraicGeometry.Scheme.ΓSpecIso_naturality
        (CommRingCat.ofHom requiredAllSheafifiedEvalOne))

private theorem selectedModTwoPoint_normalized_appTop :
    selectedModTwoPoint.appTop ≫
        (AlgebraicGeometry.Scheme.ΓSpecIso
          (CommRingCat.of (ZMod 2))).hom =
      CommRingCat.ofHom requiredAllGlobalEvalModTwo := by
  simpa only [selectedModTwoPoint, Scheme.Hom.comp_appTop,
    Category.assoc, requiredAllGlobalEvalModTwo, CommRingCat.hom_comp] using
    congrArg (fun q => requiredAllBaseSchemeIso.hom.appTop ≫ q)
      (AlgebraicGeometry.Scheme.ΓSpecIso_naturality
        (CommRingCat.ofHom requiredAllSheafifiedEvalModTwo))

private noncomputable instance requiredAllReferenceModel_isAffine :
    IsAffine requiredAllReferenceModel.underlying := by
  rw [requiredAllReferenceModel_underlying, twoChart_underlying]
  infer_instance

private theorem requiredAll_ambientTopAffineOpen_eq :
    ambientTopAffineOpen =
      (⟨⊤, AlgebraicGeometry.isAffineOpen_top
        requiredAllReferenceModel.underlying⟩ :
          requiredAllReferenceModel.underlying.affineOpens) := by
  apply Subtype.ext
  rfl

private theorem required_ideal_le_selectedRequiredPoint_ker :
    lawGeneratedIdealSheaf requiredAllRawSystem requiredAllReferenceModel
        requiredAllReading requiredAllReading_valid
        requiredAllReading_requiredClosed ≤ selectedRequiredPoint.ker := by
  haveI : IsAffine requiredAllReferenceModel.underlying := by
    rw [requiredAllReferenceModel_underlying, twoChart_underlying]
    infer_instance
  have hring :
      (lawGeneratedIdealSheaf requiredAllRawSystem requiredAllReferenceModel
        requiredAllReading requiredAllReading_valid
        requiredAllReading_requiredClosed).ideal ambientTopAffineOpen ≤
          RingHom.ker selectedRequiredPoint.appTop.hom := by
    intro x hx
    have heval := required_ideal_top_le_ker_globalEvalOne hx
    change requiredAllGlobalEvalOne x = 0 at heval
    change selectedRequiredPoint.appTop.hom x = 0
    apply (ConcreteCategory.bijective_of_isIso
      (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of Int)).hom).1
    have hnormalized := congrArg (fun q => q x)
      selectedRequiredPoint_normalized_appTop
    change
      (AlgebraicGeometry.Scheme.ΓSpecIso
        (CommRingCat.of Int)).hom.hom
          (selectedRequiredPoint.appTop.hom x) =
        requiredAllGlobalEvalOne x at hnormalized
    rw [hnormalized, heval, map_zero]
  have hring' :
      (lawGeneratedIdealSheaf requiredAllRawSystem requiredAllReferenceModel
        requiredAllReading requiredAllReading_valid
        requiredAllReading_requiredClosed).ideal
          ⟨⊤, AlgebraicGeometry.isAffineOpen_top
            requiredAllReferenceModel.underlying⟩ ≤
        RingHom.ker selectedRequiredPoint.appTop.hom := by
    simpa only [← requiredAll_ambientTopAffineOpen_eq] using hring
  let e := Scheme.IdealSheafData.equivOfIsAffine
    (X := requiredAllReferenceModel.underlying)
  apply e.toOrderIso.le_iff_le.mp
  rw [Scheme.ker_of_isAffine]
  simpa [e] using hring'

private theorem strengtheningLaw_other_equation
    (a : carrier.Atom) (ha : a ≠ FiniteAtom.componentB) :
    semanticCoreGlobalEquation requiredAllRawSystem requiredAllReferenceModel
        requiredAllLawEquationCore requiredAllSchemeBridge .strengthening a = 0 := by
  cases a <;> simp_all [semanticCoreGlobalEquation,
    requiredAllLawEquationCore, requiredAllSchemeBridge,
    SemanticLawEquationSchemeBridge.toSheafifiedSection]

private theorem requiredAll_span_le_ker_globalEvalModTwo
    (i : RequiredAllLawIndex) :
    Ideal.span (Set.range (semanticCoreGlobalEquation requiredAllRawSystem
      requiredAllReferenceModel requiredAllLawEquationCore
      requiredAllSchemeBridge i)) ≤
      RingHom.ker requiredAllGlobalEvalModTwo := by
  apply Ideal.span_le.mpr
  rintro _ ⟨a, rfl⟩
  cases i
  · cases a
    · rw [requiredLaw_componentA_equation]
      change requiredAllGlobalEvalModTwo
        (requiredAllBaseGlobalCoordinate - 1) = 0
      rw [map_sub, map_one, requiredAllGlobalEvalModTwo_baseGlobalCoordinate]
      simp
    all_goals
      rw [requiredLaw_other_equation _ (by simp)]
      simp
  · cases a
    · rw [strengtheningLaw_other_equation _ (by simp)]
      simp
    · rw [strengtheningLaw_componentB_equation]
      change requiredAllGlobalEvalModTwo
        (requiredAllBaseGlobalCoordinate + 1) = 0
      rw [map_add, map_one, requiredAllGlobalEvalModTwo_baseGlobalCoordinate]
      decide
    all_goals
      rw [strengtheningLaw_other_equation _ (by simp)]
      simp

private theorem all_ideal_top_le_ker_globalEvalModTwo :
    (allLawGeneratedIdealSheaf requiredAllRawSystem requiredAllReferenceModel
      requiredAllReading requiredAllReading_valid).ideal ambientTopAffineOpen ≤
        RingHom.ker requiredAllGlobalEvalModTwo := by
  rw [allLawGeneratedIdealSheaf_ideal]
  refine iSup_le fun i => ?_
  rw [requiredAll_local_top_eq_span]
  exact requiredAll_span_le_ker_globalEvalModTwo i.1

private theorem strengthening_equation_mem_all_top :
    semanticCoreGlobalEquation requiredAllRawSystem requiredAllReferenceModel
        requiredAllLawEquationCore requiredAllSchemeBridge .strengthening
        FiniteAtom.componentB ∈
      (allLawGeneratedIdealSheaf requiredAllRawSystem requiredAllReferenceModel
        requiredAllReading requiredAllReading_valid).ideal ambientTopAffineOpen := by
  have hlocal :
      semanticCoreGlobalEquation requiredAllRawSystem requiredAllReferenceModel
          requiredAllLawEquationCore requiredAllSchemeBridge .strengthening
          FiniteAtom.componentB ∈
        localLawWitnessIdeal requiredAllRawSystem requiredAllReferenceModel
          (requiredAllReading.witness .strengthening
            (requiredAllReading_allLawsSelected.closed .strengthening))
          ambientTopAffineOpen := by
    rw [requiredAll_local_top_eq_span]
    exact Ideal.subset_span ⟨FiniteAtom.componentB, rfl⟩
  let idx : {i : RequiredAllLawIndex //
      requiredAllReading.selected ambientTopAffineOpen i} :=
    ⟨.strengthening, requiredAllReading_selected _ _⟩
  rw [allLawGeneratedIdealSheaf_ideal]
  exact (le_iSup (fun i : {i : RequiredAllLawIndex //
    requiredAllReading.selected ambientTopAffineOpen i} =>
      localLawWitnessIdeal requiredAllRawSystem requiredAllReferenceModel
        (requiredAllReading.witness i.1
          (requiredAllReading_valid.selected_closed
            ambientTopAffineOpen i.1 i.2)) ambientTopAffineOpen) idx) hlocal

private theorem all_ideal_le_selectedModTwoPoint_ker :
    allLawGeneratedIdealSheaf requiredAllRawSystem requiredAllReferenceModel
        requiredAllReading requiredAllReading_valid ≤ selectedModTwoPoint.ker := by
  haveI : IsAffine requiredAllReferenceModel.underlying := by
    rw [requiredAllReferenceModel_underlying, twoChart_underlying]
    infer_instance
  have hring :
      (allLawGeneratedIdealSheaf requiredAllRawSystem requiredAllReferenceModel
        requiredAllReading requiredAllReading_valid).ideal
          ambientTopAffineOpen ≤ RingHom.ker selectedModTwoPoint.appTop.hom := by
    intro x hx
    have heval := all_ideal_top_le_ker_globalEvalModTwo hx
    change requiredAllGlobalEvalModTwo x = 0 at heval
    change selectedModTwoPoint.appTop.hom x = 0
    apply (ConcreteCategory.bijective_of_isIso
      (AlgebraicGeometry.Scheme.ΓSpecIso
        (CommRingCat.of (ZMod 2))).hom).1
    have hnormalized := congrArg (fun q => q x)
      selectedModTwoPoint_normalized_appTop
    change
      (AlgebraicGeometry.Scheme.ΓSpecIso
        (CommRingCat.of (ZMod 2))).hom.hom
          (selectedModTwoPoint.appTop.hom x) =
        requiredAllGlobalEvalModTwo x at hnormalized
    rw [hnormalized, heval, map_zero]
  have hring' :
      (allLawGeneratedIdealSheaf requiredAllRawSystem requiredAllReferenceModel
        requiredAllReading requiredAllReading_valid).ideal
          ⟨⊤, AlgebraicGeometry.isAffineOpen_top
            requiredAllReferenceModel.underlying⟩ ≤
        RingHom.ker selectedModTwoPoint.appTop.hom := by
    simpa only [← requiredAll_ambientTopAffineOpen_eq] using hring
  let e := Scheme.IdealSheafData.equivOfIsAffine
    (X := requiredAllReferenceModel.underlying)
  apply e.toOrderIso.le_iff_le.mp
  rw [Scheme.ker_of_isAffine]
  simpa [e] using hring'

/-- `x = 1`のpointはrequired equationを満たす。 -/
theorem selected_point_factors_required :
    Nonempty (FactorsThroughLawfulClosedSubscheme requiredAllRawSystem
      requiredAllReferenceModel requiredAllReading
      requiredAllReading_valid requiredAllReading_requiredClosed
      selectedRequiredPoint) := by
  apply (idealLawfulAlong_iff_nonempty_factorsThrough requiredAllRawSystem
    requiredAllReferenceModel requiredAllReading requiredAllReading_valid
    requiredAllReading_requiredClosed selectedRequiredPoint).mp
  apply (idealLawfulAlong_iff_le_ker requiredAllRawSystem
    requiredAllReferenceModel requiredAllReading requiredAllReading_valid
    requiredAllReading_requiredClosed selectedRequiredPoint).mpr
  exact required_ideal_le_selectedRequiredPoint_ker

/-- 同じpointではoptional equationの値が`2`となり、all locusへはfactorしない。 -/
theorem selected_point_not_factors_all :
    ¬ Nonempty (FactorsThroughAllLawfulClosedSubscheme requiredAllRawSystem
      requiredAllReferenceModel requiredAllReading
      requiredAllReading_valid selectedRequiredPoint) := by
  rintro ⟨t⟩
  have hle :
      allLawGeneratedIdealSheaf requiredAllRawSystem requiredAllReferenceModel
          requiredAllReading requiredAllReading_valid ≤ selectedRequiredPoint.ker := by
    rw [← t.2]
    calc
      allLawGeneratedIdealSheaf requiredAllRawSystem requiredAllReferenceModel
          requiredAllReading requiredAllReading_valid =
        (allLawfulClosedImmersion requiredAllRawSystem requiredAllReferenceModel
          requiredAllReading requiredAllReading_valid).ker :=
            (Scheme.IdealSheafData.ker_subschemeι _).symm
      _ ≤ (t.1 ≫ allLawfulClosedImmersion requiredAllRawSystem
          requiredAllReferenceModel requiredAllReading
          requiredAllReading_valid).ker := Scheme.Hom.le_ker_comp _ _
  let e := Scheme.IdealSheafData.equivOfIsAffine
    (X := requiredAllReferenceModel.underlying)
  have htop :
      (allLawGeneratedIdealSheaf requiredAllRawSystem requiredAllReferenceModel
        requiredAllReading requiredAllReading_valid).ideal
          ⟨⊤, AlgebraicGeometry.isAffineOpen_top
            requiredAllReferenceModel.underlying⟩ ≤
        RingHom.ker selectedRequiredPoint.appTop.hom := by
    have hmapped := e.toOrderIso.monotone hle
    rw [Scheme.ker_of_isAffine] at hmapped
    simpa [e] using hmapped
  have hmem :
      semanticCoreGlobalEquation requiredAllRawSystem requiredAllReferenceModel
          requiredAllLawEquationCore requiredAllSchemeBridge .strengthening
          FiniteAtom.componentB ∈
        (allLawGeneratedIdealSheaf requiredAllRawSystem requiredAllReferenceModel
          requiredAllReading requiredAllReading_valid).ideal
            ⟨⊤, AlgebraicGeometry.isAffineOpen_top
              requiredAllReferenceModel.underlying⟩ := by
    simpa only [← requiredAll_ambientTopAffineOpen_eq] using
      strengthening_equation_mem_all_top
  have hpzero := htop hmem
  rw [strengtheningLaw_componentB_equation] at hpzero
  change selectedRequiredPoint.appTop.hom
    (requiredAllBaseGlobalCoordinate + 1) = 0 at hpzero
  have hnormalized := congrArg
    (fun q => q (requiredAllBaseGlobalCoordinate + 1))
    selectedRequiredPoint_normalized_appTop
  change
    (AlgebraicGeometry.Scheme.ΓSpecIso
      (CommRingCat.of Int)).hom.hom
        (selectedRequiredPoint.appTop.hom
          (requiredAllBaseGlobalCoordinate + 1)) =
      requiredAllGlobalEvalOne
        (requiredAllBaseGlobalCoordinate + 1) at hnormalized
  rw [hpzero, map_zero, map_add, map_one,
    requiredAllGlobalEvalOne_baseGlobalCoordinate] at hnormalized
  norm_num at hnormalized

/-- characteristic twoのpointはrequired / optional双方を満たす。 -/
theorem selected_modTwo_point_factors_all :
    Nonempty (FactorsThroughAllLawfulClosedSubscheme requiredAllRawSystem
      requiredAllReferenceModel requiredAllReading
      requiredAllReading_valid selectedModTwoPoint) := by
  apply (fullIdealLawfulAlong_iff_nonempty_factorsThrough requiredAllRawSystem
    requiredAllReferenceModel requiredAllReading requiredAllReading_valid
    selectedModTwoPoint).mp
  change (allLawGeneratedIdealSheaf requiredAllRawSystem
    requiredAllReferenceModel requiredAllReading
    requiredAllReading_valid).comap selectedModTwoPoint = ⊥
  rw [eq_bot_iff]
  apply (Scheme.IdealSheafData.map_gc selectedModTwoPoint _ ⊥).mpr
  simpa only [Scheme.IdealSheafData.map_bot] using
    all_ideal_le_selectedModTwoPoint_ker

/-- The integral point used to separate the weak and strong law loci. -/
noncomputable def integerPoint :
    AlgebraicGeometry.Scheme.Spec.obj (op (CommRingCat.of Int)) ⟶
      twoChartReferenceModel.underlying :=
  integerTestPoint

/-- The mod-two point lying on both the weak and strong law loci. -/
noncomputable def modTwoPoint :
    AlgebraicGeometry.Scheme.Spec.obj (op (CommRingCat.of (ZMod 2))) ⟶
      twoChartReferenceModel.underlying :=
  modTwoTestPoint

/-- The finite object comparison witness for the integral point. -/
theorem integerPoint_objectComparison :
    RequiredObjectPointComparison rawSystem twoChartReferenceModel
      weakReading integerPoint
        AAT.AG.LawAlgebra.FiniteExamples.CycleCorrespondenceExample.acyclicObject := by
  intro i _
  cases i
  constructor
  · intro _
    exact (RingedSite.FiniteModel.site_equationHolds_iff_noCycleLaw _).mpr
      AAT.AG.LawAlgebra.FiniteExamples.CycleCorrespondenceExample.acyclic_noCycleLaw_holds
  · intro _
    simpa only [integerPoint] using
      integerTestPoint_semanticLawful PUnit.unit
        (RingedSite.FiniteModel.site_equation_required PUnit.unit)

/-- Shows that the same object comparison does not hold for the cyclic object. -/
theorem integerPoint_objectComparison_fails_for_cyclic :
    ¬ RequiredObjectPointComparison rawSystem twoChartReferenceModel
      weakReading integerPoint
        AAT.AG.LawAlgebra.FiniteExamples.CycleCorrespondenceExample.cyclicObject := by
  intro hcomparison
  have hweak : weakReading.geometric.HoldsOn integerPoint PUnit.unit := by
    simpa only [integerPoint] using
      integerTestPoint_semanticLawful PUnit.unit
        (RingedSite.FiniteModel.site_equation_required PUnit.unit)
  have hcyclic :=
    (hcomparison PUnit.unit (RingedSite.FiniteModel.site_equation_required PUnit.unit)).mp hweak
  exact
    AAT.AG.LawAlgebra.FiniteExamples.CycleCorrespondenceExample.cyclic_noCycleLaw_fails
      ((RingedSite.FiniteModel.site_equationHolds_iff_noCycleLaw _).mp hcyclic)

/-- Computes vanishing of the weak obstruction valuation at the integral point. -/
theorem integerPoint_omega_fires :
    SemanticLawfulAlong rawSystem twoChartReferenceModel weakReading integerPoint ↔
      omegaU noCycleValuation lawUniverse singletonRequiredAggregation
          AAT.AG.LawAlgebra.FiniteExamples.CycleCorrespondenceExample.acyclicObject =
        noCycleValuation.domain.zero := by
  exact semanticLawfulAlong_iff_omegaU_zero rawSystem twoChartReferenceModel
    weakReading integerPoint
    AAT.AG.LawAlgebra.FiniteExamples.CycleCorrespondenceExample.acyclicObject
    noCycleValuation singletonRequiredAggregation integerPoint_objectComparison
    (fun index => by
      cases index with
      | mk index _ =>
          cases index
          simpa only [RingedSite.FiniteModel.site_law_eq_noCycleLaw] using
            noCycleSound)
    (fun index => by
      cases index with
      | mk index _ =>
          cases index
          simpa only [RingedSite.FiniteModel.site_law_eq_noCycleLaw] using
            noCycleComplete)

/-- Computes the required signature-axis vanishing at the integral point. -/
theorem integerPoint_axis_fires :
    SemanticLawfulAlong rawSystem twoChartReferenceModel weakReading integerPoint ↔
      RequiredSignatureAxesZero
        AAT.AG.LawAlgebra.FiniteExamples.CycleCorrespondenceExample.acyclicObject
        AAT.AG.LawAlgebra.FiniteExamples.CycleCorrespondenceExample.signatureAxes := by
  exact semanticLawfulAlong_iff_requiredSignatureAxesZero rawSystem
    twoChartReferenceModel weakReading integerPoint
    AAT.AG.LawAlgebra.FiniteExamples.CycleCorrespondenceExample.acyclicObject
    AAT.AG.LawAlgebra.FiniteExamples.CycleCorrespondenceExample.signatureAxes
    integerPoint_objectComparison
    (by
      let A :=
        AAT.AG.LawAlgebra.FiniteExamples.CycleCorrespondenceExample.acyclicObject
      have hlegacy :=
        AAT.AG.LawAlgebra.FiniteExamples.CycleCorrespondenceExample.lawfulness_iff_signatureAxesZero A
      constructor
      · intro hsite
        apply hlegacy.mp
        intro index hrequired
        cases index
        have hholds := hsite PUnit.unit (by rfl)
        exact (RingedSite.FiniteModel.site_equationHolds_iff_noCycleLaw _).mp hholds
      · intro haxes index hrequired
        cases index
        have hholds := hlegacy.mpr haxes PUnit.unit
          (AAT.AG.FiniteModel.lawUniverse_required PUnit.unit)
        exact (RingedSite.FiniteModel.site_equationHolds_iff_noCycleLaw _).mpr hholds)

/-- Shows that the weak global equation vanishes at the integral point. -/
theorem integerPoint_globalEquationsVanish_weak :
    GlobalEquationsVanishAlong rawSystem twoChartReferenceModel
      (semanticCoreGlobalEquation rawSystem twoChartReferenceModel
        weakLawEquationCore weakSchemeBridge PUnit.unit) integerPoint := by
  change weakReading.geometric.HoldsOn integerPoint PUnit.unit
  simpa only [integerPoint] using
    integerTestPoint_semanticLawful PUnit.unit
      (RingedSite.FiniteModel.site_equation_required PUnit.unit)

/-- Detects the strong equation at the integral point by concrete evaluation. -/
theorem integerPoint_not_globalEquationsVanish_strong :
    ¬ GlobalEquationsVanishAlong rawSystem twoChartReferenceModel
      (semanticCoreGlobalEquation rawSystem twoChartReferenceModel
        strongLawEquationCore strongSchemeBridge PUnit.unit) integerPoint := by
  intro hvanish
  apply integerTestPoint_not_strong_semanticLawful
  intro i _
  cases i
  rw [strongReading_holdsOn_iff]
  simpa only [integerPoint] using hvanish

/-- Shows semantic lawfulness of the integral point for the weak reading. -/
theorem integerPoint_semanticLawful_weak :
    SemanticLawfulAlong rawSystem twoChartReferenceModel weakReading integerPoint := by
  simpa only [integerPoint] using integerTestPoint_semanticLawful

/-- Shows semantic non-lawfulness of the integral point for the strong reading. -/
theorem integerPoint_not_semanticLawful_strong :
    ¬ SemanticLawfulAlong rawSystem twoChartReferenceModel
      strongReading integerPoint := by
  simpa only [integerPoint] using integerTestPoint_not_strong_semanticLawful

/-- Shows full semantic lawfulness of the integral point for the weak reading. -/
theorem integerPoint_fullySemanticLawful_weak :
    FullySemanticLawfulAlong rawSystem twoChartReferenceModel
      weakReading integerPoint := by
  simpa only [integerPoint] using integerTestPoint_fullyWeakSemanticLawful

/-- Shows failure of full semantic lawfulness for the strong reading. -/
theorem integerPoint_not_fullySemanticLawful_strong :
    ¬ FullySemanticLawfulAlong rawSystem twoChartReferenceModel
      strongReading integerPoint := by
  intro hfull
  apply integerPoint_not_semanticLawful_strong
  intro i _
  exact hfull i

/-- Shows that every required weak witness vanishes at the integral point. -/
theorem integerPoint_witnessVanishes_weak :
    WitnessVanishes rawSystem twoChartReferenceModel weakReading
      weakReading_valid weakReading_requiredClosed integerPoint := by
  exact (semanticLawfulAlong_iff_witnessVanishes rawSystem
    twoChartReferenceModel weakReading weakReading_valid
    weakReading_requiredClosed weakReading_requiredLawIdealExact integerPoint).mp
      integerPoint_semanticLawful_weak

/-- Exhibits a strong witness that does not vanish at the integral point. -/
theorem integerPoint_not_witnessVanishes_strong :
    ¬ WitnessVanishes rawSystem twoChartReferenceModel strongReading
      strongReading_valid strongReading_requiredClosed integerPoint := by
  intro hwitness
  apply integerPoint_not_semanticLawful_strong
  exact (semanticLawfulAlong_iff_witnessVanishes rawSystem
    twoChartReferenceModel strongReading strongReading_valid
    strongReading_requiredClosed strongReading_requiredLawIdealExact integerPoint).mpr
      hwitness

/-- Shows required-ideal lawfulness of the integral point for the weak reading. -/
theorem integerPoint_idealLawful_weak :
    IdealLawfulAlong rawSystem twoChartReferenceModel weakReading
      weakReading_valid weakReading_requiredClosed integerPoint := by
  simpa only [integerPoint] using integerTestPoint_idealLawful

/-- Shows failure of required-ideal lawfulness for the strong reading. -/
theorem integerPoint_not_idealLawful_strong :
    ¬ IdealLawfulAlong rawSystem twoChartReferenceModel strongReading
      strongReading_valid strongReading_requiredClosed integerPoint := by
  intro hideal
  apply integerPoint_not_witnessVanishes_strong
  exact (witnessVanishes_iff_idealLawfulAlong rawSystem
    twoChartReferenceModel strongReading strongReading_valid
    strongReading_requiredClosed integerPoint).mpr hideal

/-- Shows all-law ideal lawfulness of the integral point for the weak reading. -/
theorem integerPoint_fullIdealLawful_weak :
    FullIdealLawfulAlong rawSystem twoChartReferenceModel weakReading
      weakReading_valid integerPoint := by
  simpa only [integerPoint] using integerTestPoint_fullWeakIdealLawful

/-- Shows failure of all-law ideal lawfulness for the strong reading. -/
theorem integerPoint_not_fullIdealLawful_strong :
    ¬ FullIdealLawfulAlong rawSystem twoChartReferenceModel strongReading
      strongReading_valid integerPoint := by
  intro hideal
  apply integerPoint_not_fullySemanticLawful_strong
  exact (fullySemanticLawfulAlong_iff_fullIdealLawfulAlong rawSystem
    twoChartReferenceModel strongReading strongReading_valid
    strongReading_allLawsSelected strongReading_allLawIdealExact integerPoint).mpr
      hideal

/-- Constructs the actual factorization of the integral point through the weak subscheme. -/
theorem integerPoint_factors_weak :
    Nonempty (FactorsThroughLawfulClosedSubscheme rawSystem
      twoChartReferenceModel weakReading weakReading_valid
      weakReading_requiredClosed integerPoint) := by
  exact (idealLawfulAlong_iff_nonempty_factorsThrough rawSystem
    twoChartReferenceModel weakReading weakReading_valid
    weakReading_requiredClosed integerPoint).mp integerPoint_idealLawful_weak

/-- Rules out factorization of the integral point through the strong subscheme. -/
theorem integerPoint_not_factors_strong :
    ¬ Nonempty (FactorsThroughLawfulClosedSubscheme rawSystem
      twoChartReferenceModel strongReading strongReading_valid
      strongReading_requiredClosed integerPoint) := by
  simpa only [integerPoint] using integerTestPoint_not_strong_factors

/-- Constructs the mod-two point's factorization through the weak subscheme. -/
theorem modTwoPoint_factors_weak :
    Nonempty (FactorsThroughLawfulClosedSubscheme rawSystem
      twoChartReferenceModel weakReading weakReading_valid
      weakReading_requiredClosed modTwoPoint) := by
  have hstrong :
      SemanticLawfulAlong rawSystem twoChartReferenceModel strongReading
        modTwoPoint := by
    simpa only [modTwoPoint] using modTwoTestPoint_semanticLawful
  have hweak :
      SemanticLawfulAlong rawSystem twoChartReferenceModel weakReading
        modTwoPoint :=
    semanticLawfulAlong_mono rawSystem twoChartReferenceModel
      weakToStrong weakToStrong_valid modTwoPoint hstrong
  exact (idealLawfulAlong_iff_nonempty_factorsThrough rawSystem
    twoChartReferenceModel weakReading weakReading_valid
    weakReading_requiredClosed modTwoPoint).mp
      ((witnessVanishes_iff_idealLawfulAlong rawSystem
        twoChartReferenceModel weakReading weakReading_valid
        weakReading_requiredClosed modTwoPoint).mp
          ((semanticLawfulAlong_iff_witnessVanishes rawSystem
            twoChartReferenceModel weakReading weakReading_valid
            weakReading_requiredClosed weakReading_requiredLawIdealExact
            modTwoPoint).mp hweak))

/-- Constructs the mod-two point's factorization through the strong subscheme. -/
theorem modTwoPoint_factors_strong :
    Nonempty (FactorsThroughLawfulClosedSubscheme rawSystem
      twoChartReferenceModel strongReading strongReading_valid
      strongReading_requiredClosed modTwoPoint) := by
  apply (idealLawfulAlong_iff_nonempty_factorsThrough rawSystem
    twoChartReferenceModel strongReading strongReading_valid
    strongReading_requiredClosed modTwoPoint).mp
  simpa only [modTwoPoint] using modTwoTestPoint_idealLawful

/-- Constructs the integral point's factorization through the weak all-law subscheme. -/
theorem integerPoint_factorsAll_weak :
    Nonempty (FactorsThroughAllLawfulClosedSubscheme rawSystem
      twoChartReferenceModel weakReading weakReading_valid integerPoint) := by
  exact (fullIdealLawfulAlong_iff_nonempty_factorsThrough rawSystem
    twoChartReferenceModel weakReading weakReading_valid integerPoint).mp
      integerPoint_fullIdealLawful_weak

/-- Rules out its factorization through the strong all-law subscheme. -/
theorem integerPoint_not_factorsAll_strong :
    ¬ Nonempty (FactorsThroughAllLawfulClosedSubscheme rawSystem
      twoChartReferenceModel strongReading strongReading_valid integerPoint) := by
  simpa only [integerPoint] using integerTestPoint_not_strong_all_factors

/-- Instantiates the generic required semantic–ideal–factorization correspondence. -/
theorem weak_correspondence_fires
    {T : AlgebraicGeometry.Scheme}
    (s : T ⟶ twoChartReferenceModel.underlying) :
    (SemanticLawfulAlong rawSystem twoChartReferenceModel weakReading s ↔
      WitnessVanishes rawSystem twoChartReferenceModel weakReading
        weakReading_valid weakReading_requiredClosed s) ∧
    (WitnessVanishes rawSystem twoChartReferenceModel weakReading
        weakReading_valid weakReading_requiredClosed s ↔
      IdealLawfulAlong rawSystem twoChartReferenceModel weakReading
        weakReading_valid weakReading_requiredClosed s) ∧
    (IdealLawfulAlong rawSystem twoChartReferenceModel weakReading
        weakReading_valid weakReading_requiredClosed s ↔
      Nonempty (FactorsThroughLawfulClosedSubscheme rawSystem
        twoChartReferenceModel weakReading weakReading_valid
        weakReading_requiredClosed s)) :=
  lawfulnessIdealFactorizationCorrespondence rawSystem twoChartReferenceModel
    weakReading weakReading_valid weakReading_requiredClosed
    weakReading_requiredLawIdealExact s

/-- Instantiates the existing-core correspondence using the verified weak bridge. -/
theorem weak_semanticCore_correspondence_fires
    {T : AlgebraicGeometry.Scheme}
    (s : T ⟶ twoChartReferenceModel.underlying) :
    SemanticCoreIdealSheafRealized rawSystem twoChartReferenceModel
      weakLawEquationCore weakSchemeBridge ∧
    (SemanticLawfulAlong rawSystem twoChartReferenceModel weakReading s ↔
      WitnessVanishes rawSystem twoChartReferenceModel weakReading
        weakReading_valid weakReading_requiredClosed s) ∧
    (WitnessVanishes rawSystem twoChartReferenceModel weakReading
        weakReading_valid weakReading_requiredClosed s ↔
      IdealLawfulAlong rawSystem twoChartReferenceModel weakReading
        weakReading_valid weakReading_requiredClosed s) ∧
    (IdealLawfulAlong rawSystem twoChartReferenceModel weakReading
        weakReading_valid weakReading_requiredClosed s ↔
      Nonempty (FactorsThroughLawfulClosedSubscheme rawSystem
        twoChartReferenceModel weakReading weakReading_valid
        weakReading_requiredClosed s)) := by
  simpa only [weakReading] using
    semanticCoreLawfulnessIdealFactorizationCorrespondence rawSystem
      twoChartReferenceModel weakLawEquationCore weakSchemeBridge
      weakSchemeBridge_valid weakReading_requiredLawIdealExact s

/-- Instantiates the full all-law correspondence for the weak reading. -/
theorem weak_full_correspondence_fires
    {T : AlgebraicGeometry.Scheme}
    (s : T ⟶ twoChartReferenceModel.underlying) :
    (FullySemanticLawfulAlong rawSystem twoChartReferenceModel weakReading s ↔
      FullIdealLawfulAlong rawSystem twoChartReferenceModel weakReading
        weakReading_valid s) ∧
    (FullIdealLawfulAlong rawSystem twoChartReferenceModel weakReading
        weakReading_valid s ↔
      Nonempty (FactorsThroughAllLawfulClosedSubscheme rawSystem
        twoChartReferenceModel weakReading weakReading_valid s)) :=
  fullLawfulnessIdealFactorizationCorrespondence rawSystem
    twoChartReferenceModel weakReading weakReading_valid
    weakReading_allLawsSelected weakReading_allLawIdealExact s

private theorem leftRawPolynomialSignFlip_involutive :
    (RawPresheaf.coordinateRestriction
        RawPresheaf.leftToBase).polynomialMap.comp
      (RawPresheaf.coordinateRestriction
        RawPresheaf.leftToBase).polynomialMap =
        RingHom.id _ := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [TypedCoordinateRestriction.polynomialMap]
  · intro i
    cases i
    change
      (RawPresheaf.coordinateRestriction RawPresheaf.leftToBase).polynomialMap
          ((RawPresheaf.coordinateRestriction RawPresheaf.leftToBase).polynomialMap
            (MvPolynomial.X ())) = MvPolynomial.X ()
    rw [RawPresheaf.coordinateRestriction_polynomialMap_X, map_mul]
    erw [TypedCoordinateRestriction.polynomialMap_C]
    rw [RawPresheaf.coordinateRestriction_polynomialMap_X]
    rw [← mul_assoc]
    erw [← MvPolynomial.C.map_mul]
    have hsign :
        (RawPresheaf.gauge RawPresheaf.left *
            RawPresheaf.gauge AAT.AG.FiniteModel.twoPatchBase) *
          (RawPresheaf.gauge RawPresheaf.left *
            RawPresheaf.gauge AAT.AG.FiniteModel.twoPatchBase) = 1 := by
      calc
        _ = (RawPresheaf.gauge RawPresheaf.left *
              RawPresheaf.gauge RawPresheaf.left) *
            (RawPresheaf.gauge AAT.AG.FiniteModel.twoPatchBase *
              RawPresheaf.gauge AAT.AG.FiniteModel.twoPatchBase) := by ring
        _ = 1 := by
          rw [RawPresheaf.gauge_sq, RawPresheaf.gauge_sq, one_mul]
    rw [hsign, map_one, one_mul]

private theorem leftRawSignFlip_involutive :
    (rawSystem.restrictionStable
        RawPresheaf.leftToBase).quotientDesc.comp
      (rawSystem.restrictionStable
        RawPresheaf.leftToBase).quotientDesc = RingHom.id _ := by
  apply Ideal.Quotient.ringHom_ext
  apply RingHom.ext
  intro p
  simp only [RingHom.comp_apply]
  have h := congrArg (fun q => q p) leftRawPolynomialSignFlip_involutive
  simpa only [RawPresheaf.system_restriction, RingHom.comp_apply,
    RingHom.id_apply] using congrArg
      (rawSystem.relationFamily RawPresheaf.left).quotientMap h

private noncomputable def leftRawSignFlip :
    rawSystem.rawAlgebra RawPresheaf.left ≃+*
      rawSystem.rawAlgebra RawPresheaf.left := by
  let f := (rawSystem.restrictionStable
    RawPresheaf.leftToBase).quotientDesc
  apply RingEquiv.ofBijective f
  apply Function.bijective_iff_has_inverse.mpr
  refine ⟨f, ?_, ?_⟩
  · intro q
    have h := congrArg (fun g => g q) leftRawSignFlip_involutive
    simpa only [f, RingHom.comp_apply, RingHom.id_apply] using h
  · intro q
    have h := congrArg (fun g => g q) leftRawSignFlip_involutive
    simpa only [f, RingHom.comp_apply, RingHom.id_apply] using h

private theorem leftRawSignFlip_coordinate :
    leftRawSignFlip
        ((rawSystem.relationFamily RawPresheaf.left).quotientMap
          (MvPolynomial.X ())) =
      (rawSystem.relationFamily RawPresheaf.left).quotientMap
        (-(MvPolynomial.X ())) := by
  simpa only [leftRawSignFlip, RingEquiv.ofBijective_apply] using
    RawPresheaf.leftToBase_quotientDesc_X

/-- A raw-presentation bridge whose left component applies the sign flip. -/
noncomputable def restrictionBrokenSchemeBridge :
    SemanticLawEquationSchemeBridge rawSystem weakLawEquationCore where
  toRawPresentation W := by
    classical
    by_cases hW : W = RawPresheaf.left
    · subst W
      exact leftRawSignFlip
    · exact RingEquiv.refl (rawSystem.rawAlgebra W)

private theorem restrictionBrokenSchemeBridge_base :
    restrictionBrokenSchemeBridge.toRawPresentation base =
      RingEquiv.refl (rawSystem.rawAlgebra base) := by
  simp only [restrictionBrokenSchemeBridge, dif_neg
    (Ne.symm
      AAT.AG.LawAlgebra.FiniteExamples.RingedSite.FiniteModel.left_ne_base)]

private theorem restrictionBrokenSchemeBridge_left :
    restrictionBrokenSchemeBridge.toRawPresentation RawPresheaf.left =
      leftRawSignFlip := by
  rw [restrictionBrokenSchemeBridge]
  simp

private theorem restrictionBrokenSchemeBridge_base_coordinate :
    restrictionBrokenSchemeBridge.toSheafifiedSection base
        ((rawSystem.relationFamily base).quotientMap (MvPolynomial.X ())) =
      baseCoordinateSection := by
  rw [SemanticLawEquationSchemeBridge.toSheafifiedSection,
    restrictionBrokenSchemeBridge_base]
  rfl

private theorem restrictionBrokenSchemeBridge_left_double_flip :
    restrictionBrokenSchemeBridge.toSheafifiedSection RawPresheaf.left
        (weakLawEquationCore.restrict RawPresheaf.leftToBase
          ((rawSystem.relationFamily base).quotientMap (MvPolynomial.X ()))) =
      leftCoordinateSection := by
  rw [SemanticLawEquationSchemeBridge.toSheafifiedSection,
    restrictionBrokenSchemeBridge_left]
  change
    (rawSystem.toRingedSite.canonical.app (op RawPresheaf.left)).right
      (leftRawSignFlip
        ((rawSystem.restrictionStable
          RawPresheaf.leftToBase).quotientDesc
            ((rawSystem.relationFamily base).quotientMap
              (MvPolynomial.X ())))) = leftCoordinateSection
  have hrestrict :
      (rawSystem.restrictionStable RawPresheaf.leftToBase).quotientDesc
          ((rawSystem.relationFamily base).quotientMap
            (MvPolynomial.X ())) =
        (rawSystem.relationFamily RawPresheaf.left).quotientMap
          (-(MvPolynomial.X ())) := by
    simpa only [rawSystem, base] using
      RawPresheaf.leftToBase_quotientDesc_X
  rw [hrestrict]
  let q := (rawSystem.relationFamily RawPresheaf.left).quotientMap
    (MvPolynomial.X ())
  change
    (rawSystem.toRingedSite.canonical.app (op RawPresheaf.left)).right
      (leftRawSignFlip (-q)) = leftCoordinateSection
  calc
    (rawSystem.toRingedSite.canonical.app (op RawPresheaf.left)).right
        (leftRawSignFlip (-q)) =
      (rawSystem.toRingedSite.canonical.app (op RawPresheaf.left)).right
        (-(leftRawSignFlip q)) := by rw [map_neg]
    _ = (rawSystem.toRingedSite.canonical.app (op RawPresheaf.left)).right q := by
      rw [leftRawSignFlip_coordinate]
      have hqneg :
          (rawSystem.relationFamily RawPresheaf.left).quotientMap
              (-(MvPolynomial.X ())) = -q := by
        rw [map_neg]
      rw [hqneg]
      have hcanneg :
          (rawSystem.toRingedSite.canonical.app (op RawPresheaf.left)).right
              (-q) =
            -(rawSystem.toRingedSite.canonical.app (op RawPresheaf.left)).right
              q := map_neg _ q
      simp only [neg_neg]
    _ = leftCoordinateSection := rfl

/-- Shows that the sign-flipped bridge violates restriction naturality. -/
theorem restrictionBrokenSchemeBridge_not_valid :
    ¬ IsSemanticLawEquationSchemeBridge rawSystem
      weakLawEquationCore restrictionBrokenSchemeBridge := by
  intro hvalid
  have hn := hvalid.restriction_natural RawPresheaf.leftToBase
    ((rawSystem.relationFamily base).quotientMap (MvPolynomial.X ()))
  rw [restrictionBrokenSchemeBridge_left_double_flip] at hn
  change leftCoordinateSection =
    sheafifiedRestriction rawSystem RawPresheaf.leftToBase
      (restrictionBrokenSchemeBridge.toSheafifiedSection base
        ((rawSystem.relationFamily base).quotientMap
          (MvPolynomial.X ()))) at hn
  rw [restrictionBrokenSchemeBridge_base_coordinate] at hn
  exact sheafified_leftToBase_changes_coordinate hn.symm

private theorem restrictionBroken_globalEquation_eq_weak :
    semanticCoreGlobalEquation rawSystem twoChartReferenceModel
        weakLawEquationCore restrictionBrokenSchemeBridge PUnit.unit =
      semanticCoreGlobalEquation rawSystem twoChartReferenceModel
        weakLawEquationCore weakSchemeBridge PUnit.unit := by
  funext a
  rw [semanticCoreGlobalEquation, semanticCoreGlobalEquation]
  change
    twoChartReferenceModel.decoration.interpretation
        (restrictionBrokenSchemeBridge.toSheafifiedSection base
          (weakLawEquationCore.violationWitness base PUnit.unit a)) =
      twoChartReferenceModel.decoration.interpretation
        (weakSchemeBridge.toSheafifiedSection base
          (weakLawEquationCore.violationWitness base PUnit.unit a))
  rw [SemanticLawEquationSchemeBridge.toSheafifiedSection,
    SemanticLawEquationSchemeBridge.toSheafifiedSection,
    restrictionBrokenSchemeBridge_base]
  rfl

private theorem restrictionBroken_left_rawIdeal_eq
    (hrealized : SemanticCoreIdealSheafRealized rawSystem
      twoChartReferenceModel weakLawEquationCore restrictionBrokenSchemeBridge) :
    weakLawEquationCore.lawWitnessIdeal RawPresheaf.left PUnit.unit =
      Ideal.map leftRawSignFlip
        (weakLawEquationCore.lawWitnessIdeal RawPresheaf.left PUnit.unit) := by
  let brokenReading : ClosedEquationalLawReading rawSystem
      twoChartReferenceModel :=
    ClosedEquationalLawReading.ofSemanticCore rawSystem
      twoChartReferenceModel weakLawEquationCore restrictionBrokenSchemeBridge
  let brokenCompatible : IsClosedEquationalWitnessReading rawSystem
      twoChartReferenceModel brokenReading := by
    dsimp only [brokenReading]
    exact ClosedEquationalLawReading.ofSemanticCore_witnessCompatible rawSystem
      twoChartReferenceModel weakLawEquationCore restrictionBrokenSchemeBridge
  have brokenClosed : brokenReading.closed PUnit.unit := by
    change PUnit.unit ∈ (Set.univ : Set RingedSite.FiniteModel.site.equationSystem.Index)
    exact Set.mem_univ PUnit.unit
  have hsheaf :
      lawWitnessIdealSheaf rawSystem twoChartReferenceModel brokenReading
          brokenCompatible PUnit.unit brokenClosed =
        lawWitnessIdealSheaf rawSystem twoChartReferenceModel weakReading
          weakReading_witnessCompatible PUnit.unit weakReading_closed_unit := by
    rw [lawWitnessIdealSheaf_ofGlobalSections rawSystem twoChartReferenceModel
      brokenReading brokenCompatible PUnit.unit brokenClosed
      (semanticCoreGlobalEquation rawSystem twoChartReferenceModel
        weakLawEquationCore restrictionBrokenSchemeBridge PUnit.unit)]
    · rw [lawWitnessIdealSheaf_ofGlobalSections rawSystem
        twoChartReferenceModel weakReading weakReading_witnessCompatible
        PUnit.unit weakReading_closed_unit
        (semanticCoreGlobalEquation rawSystem twoChartReferenceModel
          weakLawEquationCore weakSchemeBridge PUnit.unit)]
      · rw [restrictionBroken_globalEquation_eq_weak]
      · simpa only [weakReading] using
          ClosedEquationalLawReading.ofSemanticCore_witness rawSystem
            twoChartReferenceModel weakLawEquationCore weakSchemeBridge
            PUnit.unit weakReading_closed_unit
    · rfl
  have hbroken := hrealized.2 leftIndex PUnit.unit
  dsimp only at hbroken
  have hleft :
      Scheme.IdealSheafData.ofIdealTop
          (X := (twoChartReferenceModel.atlas.chart leftIndex).domain)
          (Ideal.map
            (AlgebraicGeometry.Scheme.ΓSpecIso
              (SheafifiedSectionRing rawSystem
                (twoChartReferenceModel.atlas.chart leftIndex).context)).inv.hom
            (Ideal.map
              (restrictionBrokenSchemeBridge.toSheafifiedSection
                (twoChartReferenceModel.atlas.chart leftIndex).context)
              (weakLawEquationCore.lawWitnessIdeal
                (twoChartReferenceModel.atlas.chart leftIndex).context
                PUnit.unit))) =
        Scheme.IdealSheafData.ofIdealTop
          (X := (twoChartReferenceModel.atlas.chart leftIndex).domain)
          (Ideal.map
            (AlgebraicGeometry.Scheme.ΓSpecIso
              (SheafifiedSectionRing rawSystem
                (twoChartReferenceModel.atlas.chart leftIndex).context)).inv.hom
            (Ideal.map
              (weakSchemeBridge.toSheafifiedSection
                (twoChartReferenceModel.atlas.chart leftIndex).context)
              (weakLawEquationCore.lawWitnessIdeal
                (twoChartReferenceModel.atlas.chart leftIndex).context
                PUnit.unit))) := by
    rw [← hbroken, ← weakCore_leftChart_idealSheaf_realization_fires]
    rw [hsheaf]
  letI : AlgebraicGeometry.IsAffine
      (twoChartReferenceModel.atlas.chart leftIndex).domain :=
    (twoChartReferenceModel.atlas.chart leftIndex).domain_isAffine
  have houter :=
    (Scheme.IdealSheafData.equivOfIsAffine
      (X := (twoChartReferenceModel.atlas.chart leftIndex).domain)).symm.injective
      (by simpa only [Scheme.IdealSheafData.equivOfIsAffine_symm_apply]
        using hleft)
  let gammaInv := (AlgebraicGeometry.Scheme.ΓSpecIso
    (SheafifiedSectionRing rawSystem RawPresheaf.left)).inv.hom
  have hgamma : Function.Bijective gammaInv :=
    ConcreteCategory.bijective_of_isIso
      (AlgebraicGeometry.Scheme.ΓSpecIso
        (SheafifiedSectionRing rawSystem RawPresheaf.left)).inv
  change
    Ideal.map gammaInv
        (Ideal.map
          (restrictionBrokenSchemeBridge.toSheafifiedSection RawPresheaf.left)
          (weakLawEquationCore.lawWitnessIdeal RawPresheaf.left PUnit.unit)) =
      Ideal.map gammaInv
        (Ideal.map (weakSchemeBridge.toSheafifiedSection RawPresheaf.left)
          (weakLawEquationCore.lawWitnessIdeal RawPresheaf.left PUnit.unit)) at houter
  have hinner := congrArg (Ideal.comap gammaInv) houter
  have hinner' := by
    simpa only [Ideal.comap_map_of_bijective gammaInv hgamma] using hinner
  rw [SemanticLawEquationSchemeBridge.toSheafifiedSection,
    restrictionBrokenSchemeBridge_left,
    SemanticLawEquationSchemeBridge.toSheafifiedSection, weakSchemeBridge] at hinner'
  let canonical :=
    (sheafificationUnitAlgHom rawSystem RawPresheaf.left).toRingHom
  have hcanonical : Function.Bijective canonical := by
    letI := StandardSchemeReading.canonicalComponentIsIso RawPresheaf.left
    exact ConcreteCategory.bijective_of_isIso
      (rawSystem.toRingedSite.canonical.app (op RawPresheaf.left)).right
  rw [← Ideal.map_map, ← Ideal.map_map] at hinner'
  change
    Ideal.map canonical
        (Ideal.map leftRawSignFlip.toRingHom
          (weakLawEquationCore.lawWitnessIdeal RawPresheaf.left PUnit.unit)) =
      Ideal.map canonical
        (Ideal.map (RingEquiv.refl _).toRingHom
          (weakLawEquationCore.lawWitnessIdeal RawPresheaf.left PUnit.unit)) at hinner'
  have hraw := congrArg
    (Ideal.comap canonical) hinner'
  have hraw' := by
    simpa only [Ideal.comap_map_of_bijective canonical hcanonical] using hraw
  simpa only [RingEquiv.toRingHom_refl, Ideal.map_id] using hraw'.symm

private theorem gauge_left : RawPresheaf.gauge RawPresheaf.left = -1 := by
  simp [RawPresheaf.gauge]

private theorem weak_componentA_left_raw_equation :
    weakLawEquationCore.violationWitness RawPresheaf.left PUnit.unit
        FiniteAtom.componentA =
      (-(rawSystem.relationFamily RawPresheaf.left).quotientMap
          (MvPolynomial.X ()) - 1 : rawSystem.rawAlgebra RawPresheaf.left) := by
  simp only [weakLawEquationCore]
  rw [orientedRawCoordinate, gauge_left]
  simp

private theorem leftRawSignFlip_weak_componentA :
    leftRawSignFlip
        (weakLawEquationCore.violationWitness RawPresheaf.left PUnit.unit
          FiniteAtom.componentA) =
      (rawSystem.relationFamily RawPresheaf.left).quotientMap
          (MvPolynomial.X ()) - 1 := by
  rw [weak_componentA_left_raw_equation, map_sub, map_neg, map_one,
    leftRawSignFlip_coordinate]
  rw [map_neg]
  ring

private theorem quotientOneEval_rawCoordinate :
    RawPresheaf.quotientOneEval
        ((rawSystem.relationFamily RawPresheaf.left).quotientMap
          (MvPolynomial.X ())) = 1 := by
  change RawPresheaf.quotientOneEval
      ((RawPresheaf.relationFamily RawPresheaf.left).quotientMap
        (MvPolynomial.X ())) = 1
  rw [RawPresheaf.quotientOneEval_mk]
  simp [RawPresheaf.oneEval]

private theorem restrictionBroken_left_mappedIdeal_le_evalKer :
    Ideal.map leftRawSignFlip
        (weakLawEquationCore.lawWitnessIdeal RawPresheaf.left PUnit.unit) ≤
      RingHom.ker RawPresheaf.quotientOneEval := by
  rw [SemanticLawEquationWitnessIdealCore.lawWitnessIdeal, Ideal.map_span]
  apply Ideal.span_le.mpr
  rintro y ⟨x, ⟨a, rfl⟩, rfl⟩
  change RawPresheaf.quotientOneEval
      (leftRawSignFlip
        (weakLawEquationCore.violationWitness RawPresheaf.left PUnit.unit a)) = 0
  cases a
  · rw [leftRawSignFlip_weak_componentA]
    rw [map_sub, quotientOneEval_rawCoordinate, map_one, sub_self]
  all_goals simp [weakLawEquationCore]

/-- Refutes actual chart-ideal realization for the sign-flipped bridge. -/
theorem restrictionBrokenSchemeBridge_not_realized :
    ¬ SemanticCoreIdealSheafRealized rawSystem twoChartReferenceModel
      weakLawEquationCore restrictionBrokenSchemeBridge := by
  intro hrealized
  have hideal := restrictionBroken_left_rawIdeal_eq hrealized
  let generator := weakLawEquationCore.violationWitness RawPresheaf.left
    PUnit.unit FiniteAtom.componentA
  have hgenerator : generator ∈
      weakLawEquationCore.lawWitnessIdeal RawPresheaf.left PUnit.unit := by
    exact Ideal.subset_span ⟨FiniteAtom.componentA, rfl⟩
  have hgeneratorMapped : generator ∈
      Ideal.map leftRawSignFlip
        (weakLawEquationCore.lawWitnessIdeal RawPresheaf.left PUnit.unit) := by
    rw [← hideal]
    exact hgenerator
  have hzero := restrictionBroken_left_mappedIdeal_le_evalKer hgeneratorMapped
  change RawPresheaf.quotientOneEval generator = 0 at hzero
  rw [show generator =
      (-(rawSystem.relationFamily RawPresheaf.left).quotientMap
          (MvPolynomial.X ()) - 1 : rawSystem.rawAlgebra RawPresheaf.left) by
        exact weak_componentA_left_raw_equation] at hzero
  rw [map_sub, map_neg, quotientOneEval_rawCoordinate, map_one] at hzero
  norm_num at hzero

/-- A geometric reading deliberately chosen to fail base-change stability. -/
noncomputable def baseChangeBrokenGeometricReading :
    GeometricLawReading rawSystem twoChartReferenceModel where
  HoldsOn s _ := IsIso s

/-- Exhibits the base-change failure of the broken geometric reading. -/
theorem baseChangeBrokenGeometricReading_not_valid :
    ¬ IsGeometricLawReading rawSystem twoChartReferenceModel
      baseChangeBrokenGeometricReading := by
  intro hvalid
  unfold IsGeometricLawReading at hvalid
  apply weakImmersion_not_isIso
  have hchanged : baseChangeBrokenGeometricReading.HoldsOn
      ((lawfulClosedImmersion rawSystem twoChartReferenceModel weakReading
          weakReading_valid weakReading_requiredClosed) ≫
        𝟙 twoChartReferenceModel.underlying) PUnit.unit := by
    apply hvalid
    change IsIso (𝟙 twoChartReferenceModel.underlying)
    infer_instance
  simpa only [baseChangeBrokenGeometricReading, Category.comp_id] using hchanged

/-- The closed-equational package built from the base-change-broken semantic reading. -/
noncomputable def baseChangeBrokenReading :
    ClosedEquationalLawReading rawSystem twoChartReferenceModel :=
  { weakReading with geometric := baseChangeBrokenGeometricReading }

/-- Shows that its witnesses remain compatible despite the semantic failure. -/
theorem baseChangeBrokenReading_witnessCompatible :
    IsClosedEquationalWitnessReading rawSystem twoChartReferenceModel
      baseChangeBrokenReading := by
  simpa only [baseChangeBrokenReading] using weakReading_witnessCompatible

/-- Shows that semantic base-change failure prevents recognition as a valid reading. -/
theorem baseChangeBrokenReading_not_valid :
    ¬ IsClosedEquationalLawReading rawSystem twoChartReferenceModel
      baseChangeBrokenReading := by
  intro hvalid
  apply baseChangeBrokenGeometricReading_not_valid
  exact hvalid.geometric_stable

/-- A reading that omits the required law from its closed selection. -/
noncomputable def missingRequiredReading :
    ClosedEquationalLawReading rawSystem twoChartReferenceModel where
  geometric := weakReading.geometric
  closed := ∅
  selected := fun _ => ∅
  witness i hi := False.elim (by simpa using hi)

/-- Verifies the remaining recognition data for the missing-required fixture. -/
theorem missingRequiredReading_valid :
    IsClosedEquationalLawReading rawSystem twoChartReferenceModel
      missingRequiredReading where
  geometric_stable := weakGeometricReading_valid
  witness_compatible := by
    intro i hi
    exact False.elim (by simpa using hi)
  selected_closed := by
    intro V i hi
    exact False.elim (by simpa using hi)
  selected_basicOpen := by
    intro V f i
    simp [missingRequiredReading]

/-- Shows that the missing-required fixture cannot discharge required closedness. -/
theorem missingRequiredReading_not_requiredClosed :
    ¬ RequiredClosed rawSystem twoChartReferenceModel missingRequiredReading := by
  intro hrequired
  have hclosed := hrequired.closed PUnit.unit
    (RingedSite.FiniteModel.site_equation_required PUnit.unit)
  simpa [missingRequiredReading] using hclosed

/-- Shows that the missing-required fixture does not select every law. -/
theorem missingRequiredReading_not_allLawsSelected :
    ¬ AllLawsSelected rawSystem twoChartReferenceModel
      missingRequiredReading := by
  intro hall
  simpa [missingRequiredReading] using hall.closed PUnit.unit

/-- A reading whose selected set fails basic-open restriction compatibility. -/
noncomputable def restrictionBrokenSelectionReading :
    ClosedEquationalLawReading rawSystem twoChartReferenceModel :=
  { weakReading with
    selected := fun V => { _i | V.1 = ⊤ } }

/-- Exhibits the selected-set restriction failure at a concrete basic open. -/
theorem restrictionBrokenSelectionReading_not_valid :
    ¬ IsClosedEquationalLawReading rawSystem twoChartReferenceModel
      restrictionBrokenSelectionReading := by
  intro hvalid
  have hselected : restrictionBrokenSelectionReading.selected
      ambientTopAffineOpen PUnit.unit := by
    change ambientTopAffineOpen.1 = ⊤
    simp [ambientTopAffineOpen]
  have hrestricted :=
    (hvalid.selected_basicOpen ambientTopAffineOpen
      (0 : Γ(twoChartReferenceModel.underlying, ambientTopAffineOpen))
      PUnit.unit).mp hselected
  change
    (twoChartReferenceModel.underlying.affineBasicOpen
      (0 : Γ(twoChartReferenceModel.underlying, ambientTopAffineOpen))).1 = ⊤ at hrestricted
  rw [AlgebraicGeometry.Scheme.affineBasicOpen_coe,
    AlgebraicGeometry.Scheme.basicOpen_zero] at hrestricted
  let x : twoChartReferenceModel.underlying := by
    rw [twoChart_underlying]
    exact Classical.choice StandardArchitectureScheme.baseSpec_nonempty
  have hxTop : x ∈ (⊤ : twoChartReferenceModel.underlying.Opens) := by simp
  have hxBot : x ∈ (⊥ : twoChartReferenceModel.underlying.Opens) := by
    rw [hrestricted]
    exact hxTop
  simp at hxBot

/-- A valid reading whose context selection omits the required law. -/
noncomputable def missingRequiredSelectionReading :
    ClosedEquationalLawReading rawSystem twoChartReferenceModel :=
  { weakReading with selected := fun _ => ∅ }

/-- Verifies closed-equational recognition for the missing-selection fixture. -/
theorem missingRequiredSelectionReading_valid :
    IsClosedEquationalLawReading rawSystem twoChartReferenceModel
      missingRequiredSelectionReading where
  geometric_stable := weakGeometricReading_valid
  witness_compatible := by
    simpa only [missingRequiredSelectionReading] using
      weakReading_witnessCompatible
  selected_closed := by
    intro V i hi
    exact False.elim (by simpa using hi)
  selected_basicOpen := by
    intro V f i
    simp [missingRequiredSelectionReading]

/-- Shows that its missing context selection prevents required closedness. -/
theorem missingRequiredSelectionReading_not_requiredClosed :
    ¬ RequiredClosed rawSystem twoChartReferenceModel
      missingRequiredSelectionReading := by
  intro hrequired
  have hselected := hrequired.selected ambientTopAffineOpen PUnit.unit
    (RingedSite.FiniteModel.site_equation_required PUnit.unit)
  simpa [missingRequiredSelectionReading] using hselected

/-- A valid reading whose semantic predicate disagrees with equation vanishing. -/
noncomputable def semanticMismatchReading :
    ClosedEquationalLawReading rawSystem twoChartReferenceModel :=
  { weakReading with geometric := { HoldsOn := fun _ _ => False } }

/-- Verifies closed-equational recognition for the semantic-mismatch fixture. -/
theorem semanticMismatchReading_valid :
    IsClosedEquationalLawReading rawSystem twoChartReferenceModel
      semanticMismatchReading where
  geometric_stable := by
    intro T T' s f i hs
    exact hs.elim
  witness_compatible := by
    simpa only [semanticMismatchReading] using weakReading_witnessCompatible
  selected_closed := by
    simpa only [semanticMismatchReading] using weakReading_valid.selected_closed
  selected_basicOpen := by
    simpa only [semanticMismatchReading] using weakReading_valid.selected_basicOpen

/-- Verifies witness compatibility for the semantic-mismatch fixture. -/
theorem semanticMismatchReading_witnessCompatible :
    IsClosedEquationalWitnessReading rawSystem twoChartReferenceModel
      semanticMismatchReading :=
  semanticMismatchReading_valid.witness_compatible

/-- Discharges required closedness for the semantic-mismatch fixture. -/
theorem semanticMismatchReading_requiredClosed :
    RequiredClosed rawSystem twoChartReferenceModel semanticMismatchReading where
  closed i hi := weakReading_requiredClosed.closed i hi
  selected V i hi := weakReading_requiredClosed.selected V i hi

/-- Shows that all laws are selected in the semantic-mismatch fixture. -/
theorem semanticMismatchReading_allLawsSelected :
    AllLawsSelected rawSystem twoChartReferenceModel
      semanticMismatchReading where
  closed i := weakReading_allLawsSelected.closed i
  selected V i := weakReading_allLawsSelected.selected V i

/-- Shows failure of required law-ideal exactness for the semantic mismatch. -/
theorem semanticMismatchReading_not_exact :
    ¬ RequiredLawIdealExact rawSystem twoChartReferenceModel
      semanticMismatchReading semanticMismatchReading_valid
      semanticMismatchReading_requiredClosed := by
  intro hexact
  have hideal :
      (lawWitnessIdealSheaf rawSystem twoChartReferenceModel
        semanticMismatchReading semanticMismatchReading_witnessCompatible
        PUnit.unit
        (semanticMismatchReading_requiredClosed.closed PUnit.unit
          (RingedSite.FiniteModel.site_equation_required PUnit.unit))).comap integerPoint = ⊥ := by
    simpa only [semanticMismatchReading] using
      (weakReading_lawIdealSound integerPoint
        (integerPoint_semanticLawful_weak PUnit.unit
          (RingedSite.FiniteModel.site_equation_required PUnit.unit)))
  have hsemantic :=
    (hexact PUnit.unit (RingedSite.FiniteModel.site_equation_required PUnit.unit) integerPoint).mpr hideal
  exact hsemantic

/-- Exhibits a law index at which exactness fails. -/
theorem semanticMismatchReading_not_lawIdealExact :
    ¬ LawIdealExact rawSystem twoChartReferenceModel
      semanticMismatchReading semanticMismatchReading_witnessCompatible
      PUnit.unit
      (semanticMismatchReading_requiredClosed.closed PUnit.unit
        (RingedSite.FiniteModel.site_equation_required PUnit.unit)) := by
  intro hexact
  have hideal :
      (lawWitnessIdealSheaf rawSystem twoChartReferenceModel
        semanticMismatchReading semanticMismatchReading_witnessCompatible
        PUnit.unit
        (semanticMismatchReading_requiredClosed.closed PUnit.unit
          (RingedSite.FiniteModel.site_equation_required PUnit.unit))).comap integerPoint = ⊥ := by
    simpa only [semanticMismatchReading] using
      (weakReading_lawIdealSound integerPoint
        (integerPoint_semanticLawful_weak PUnit.unit
          (RingedSite.FiniteModel.site_equation_required PUnit.unit)))
  exact (hexact integerPoint).mpr hideal

/-- Shows that ideal vanishing does not imply the chosen semantic predicate. -/
theorem semanticMismatchReading_not_complete :
    ¬ LawIdealComplete rawSystem twoChartReferenceModel
      semanticMismatchReading semanticMismatchReading_witnessCompatible
      PUnit.unit
      (semanticMismatchReading_requiredClosed.closed PUnit.unit
        (RingedSite.FiniteModel.site_equation_required PUnit.unit)) := by
  intro hcomplete
  have hideal :
      (lawWitnessIdealSheaf rawSystem twoChartReferenceModel
        semanticMismatchReading semanticMismatchReading_witnessCompatible
        PUnit.unit
        (semanticMismatchReading_requiredClosed.closed PUnit.unit
          (RingedSite.FiniteModel.site_equation_required PUnit.unit))).comap integerPoint = ⊥ := by
    simpa only [semanticMismatchReading] using
      (weakReading_lawIdealSound integerPoint
        (integerPoint_semanticLawful_weak PUnit.unit
          (RingedSite.FiniteModel.site_equation_required PUnit.unit)))
  exact hcomplete integerPoint hideal

/-- Shows failure of all-law exactness for the semantic mismatch. -/
theorem semanticMismatchReading_not_allLawIdealExact :
    ¬ AllLawIdealExact rawSystem twoChartReferenceModel semanticMismatchReading
      semanticMismatchReading_valid
      semanticMismatchReading_allLawsSelected := by
  intro hexact
  have hideal :
      (lawWitnessIdealSheaf rawSystem twoChartReferenceModel
        semanticMismatchReading semanticMismatchReading_witnessCompatible
        PUnit.unit
        (semanticMismatchReading_allLawsSelected.closed PUnit.unit)).comap
          integerPoint = ⊥ := by
    simpa only [semanticMismatchReading] using
      (weakReading_lawIdealSound integerPoint
        (integerPoint_semanticLawful_weak PUnit.unit
          (RingedSite.FiniteModel.site_equation_required PUnit.unit)))
  exact (hexact PUnit.unit integerPoint).mpr hideal

/-- Shows that the full semantic–ideal correspondence cannot fire under the mismatch. -/
theorem semanticMismatch_full_correspondence_fails :
    ¬ (FullySemanticLawfulAlong rawSystem twoChartReferenceModel
          semanticMismatchReading integerPoint ↔
        FullIdealLawfulAlong rawSystem twoChartReferenceModel
          semanticMismatchReading semanticMismatchReading_valid
          integerPoint) := by
  intro hcorrespondence
  have hideal : FullIdealLawfulAlong rawSystem twoChartReferenceModel
      semanticMismatchReading semanticMismatchReading_valid integerPoint := by
    simpa only [semanticMismatchReading] using integerPoint_fullIdealLawful_weak
  exact (hcorrespondence.mpr hideal) PUnit.unit

/-- A valid reading whose semantic predicate overclaims equation vanishing. -/
noncomputable def semanticOverclaimReading :
    ClosedEquationalLawReading rawSystem twoChartReferenceModel :=
  { weakReading with geometric := { HoldsOn := fun _ _ => True } }

/-- Verifies closed-equational recognition for the semantic-overclaim fixture. -/
theorem semanticOverclaimReading_valid :
    IsClosedEquationalLawReading rawSystem twoChartReferenceModel
      semanticOverclaimReading where
  geometric_stable := by
    intro T T' s f i hs
    trivial
  witness_compatible := by
    simpa only [semanticOverclaimReading] using weakReading_witnessCompatible
  selected_closed := by
    simpa only [semanticOverclaimReading] using weakReading_valid.selected_closed
  selected_basicOpen := by
    simpa only [semanticOverclaimReading] using weakReading_valid.selected_basicOpen

/-- Verifies witness compatibility for the semantic-overclaim fixture. -/
theorem semanticOverclaimReading_witnessCompatible :
    IsClosedEquationalWitnessReading rawSystem twoChartReferenceModel
      semanticOverclaimReading :=
  semanticOverclaimReading_valid.witness_compatible

/-- Discharges required closedness for the semantic-overclaim fixture. -/
theorem semanticOverclaimReading_requiredClosed :
    RequiredClosed rawSystem twoChartReferenceModel semanticOverclaimReading where
  closed i hi := weakReading_requiredClosed.closed i hi
  selected V i hi := weakReading_requiredClosed.selected V i hi

/-- Shows that the semantic overclaim violates law-ideal soundness. -/
theorem semanticOverclaimReading_not_sound :
    ¬ LawIdealSound rawSystem twoChartReferenceModel semanticOverclaimReading
      semanticOverclaimReading_witnessCompatible PUnit.unit
      (semanticOverclaimReading_requiredClosed.closed PUnit.unit
        (RingedSite.FiniteModel.site_equation_required PUnit.unit)) := by
  intro hsound
  have hideal := hsound negativeOneTestPoint (by trivial)
  have hweakIdeal :
      (lawWitnessIdealSheaf rawSystem twoChartReferenceModel weakReading
        weakReading_witnessCompatible PUnit.unit
        (weakReading_requiredClosed.closed PUnit.unit
          (RingedSite.FiniteModel.site_equation_required PUnit.unit))).comap negativeOneTestPoint = ⊥ := by
    simpa only [semanticOverclaimReading] using hideal
  apply negativeOneTestPoint_not_weak_semanticLawful
  intro i hi
  cases i
  exact (weak_lawIdealExact_calculation negativeOneTestPoint).mpr hweakIdeal

/-- A law witness whose coordinate fails exact basic-open restriction. -/
noncomputable def restrictionBrokenWitness :
    ClosedEquationalLawWitness rawSystem twoChartReferenceModel PUnit.unit where
  coordinate V _ := by
    classical
    exact if V.1 = ⊤ then 0 else 1

/-- Exhibits the concrete basic-open restriction failure of the broken witness. -/
theorem restrictionBrokenWitness_not_valid :
    ¬ IsClosedEquationalLawWitness rawSystem twoChartReferenceModel
      restrictionBrokenWitness := by
  intro hvalid
  let f : Γ(twoChartReferenceModel.underlying, ambientTopAffineOpen) := 2
  let fTop : Γ(twoChartReferenceModel.underlying, ⊤) := 2
  have hbasicOpen :
      (twoChartReferenceModel.underlying.affineBasicOpen f).1 =
        twoChartReferenceModel.underlying.basicOpen fTop := by
    rw [AlgebraicGeometry.Scheme.affineBasicOpen_coe]
  have hsourceTwoZero :
      (2 : Γ(AlgebraicGeometry.Spec (CommRingCat.of (ZMod 2)), ⊤)) = 0 := by
    let e := (AlgebraicGeometry.Scheme.ΓSpecIso
      (CommRingCat.of (ZMod 2))).commRingCatIsoToRingEquiv
    apply e.injective
    simp only [map_ofNat, map_zero]
    change (2 : ZMod 2) = 0
    decide
  have happTwoZero : modTwoTestPoint.appTop fTop = 0 := by
    change modTwoTestPoint.appTop
      (2 : Γ(twoChartReferenceModel.underlying, ⊤)) = 0
    rw [map_ofNat, hsourceTwoZero]
  have hproper :
      twoChartReferenceModel.underlying.basicOpen fTop ≠ ⊤ := by
    intro htop
    let z : AlgebraicGeometry.Spec (CommRingCat.of (ZMod 2)) :=
      Classical.choice inferInstance
    have hz : z ∈ modTwoTestPoint ⁻¹ᵁ
        twoChartReferenceModel.underlying.basicOpen fTop := by
      change modTwoTestPoint.base z ∈
        twoChartReferenceModel.underlying.basicOpen fTop
      rw [htop]
      trivial
    rw [AlgebraicGeometry.Scheme.preimage_basicOpen_top,
      happTwoZero, AlgebraicGeometry.Scheme.basicOpen_zero] at hz
    simp at hz
  let modThreeTestPoint :
      AlgebraicGeometry.Spec (CommRingCat.of (ZMod 3)) ⟶
        twoChartReferenceModel.underlying :=
    AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom (Int.castRingHom (ZMod 3))) ≫
      integerTestPoint
  have hsourceTwoUnit :
      IsUnit (2 :
        Γ(AlgebraicGeometry.Spec (CommRingCat.of (ZMod 3)), ⊤)) := by
    let e := (AlgebraicGeometry.Scheme.ΓSpecIso
      (CommRingCat.of (ZMod 3))).commRingCatIsoToRingEquiv
    refine ⟨⟨2, 2, ?_, ?_⟩, rfl⟩
    · apply e.injective
      simp only [map_mul, map_ofNat, map_one]
      decide
    · apply e.injective
      simp only [map_mul, map_ofNat, map_one]
      decide
  have happTwoUnit : IsUnit (modThreeTestPoint.appTop fTop) := by
    simpa only [fTop, map_ofNat] using hsourceTwoUnit
  let z : AlgebraicGeometry.Spec (CommRingCat.of (ZMod 3)) :=
    Classical.choice inferInstance
  have hzSource : z ∈
      (AlgebraicGeometry.Spec (CommRingCat.of (ZMod 3))).basicOpen
        (modThreeTestPoint.appTop fTop) := by
    rw [(AlgebraicGeometry.Spec
      (CommRingCat.of (ZMod 3))).basicOpen_of_isUnit happTwoUnit]
    trivial
  have hzPreimage : z ∈ modThreeTestPoint ⁻¹ᵁ
      twoChartReferenceModel.underlying.basicOpen fTop := by
    rw [AlgebraicGeometry.Scheme.preimage_basicOpen_top]
    exact hzSource
  have hzTarget : modThreeTestPoint.base z ∈
      twoChartReferenceModel.underlying.basicOpen fTop := hzPreimage
  have hnonempty : Nonempty
      (twoChartReferenceModel.underlying.affineBasicOpen f).1 := by
    rw [hbasicOpen]
    exact ⟨⟨modThreeTestPoint.base z, hzTarget⟩⟩
  letI : Nonempty
      (twoChartReferenceModel.underlying.affineBasicOpen f).1 := hnonempty
  letI : Nontrivial
      Γ(twoChartReferenceModel.underlying,
        twoChartReferenceModel.underlying.affineBasicOpen f) :=
    AlgebraicGeometry.Scheme.component_nontrivial _ _
  have hrestricted :=
    hvalid ambientTopAffineOpen f FiniteAtom.componentA
  have htop : ambientTopAffineOpen.1 = ⊤ := by
    simp [ambientTopAffineOpen]
  have hrestrictedProper :
      (twoChartReferenceModel.underlying.affineBasicOpen f).1 ≠ ⊤ := by
    rw [hbasicOpen]
    exact hproper
  simp only [restrictionBrokenWitness, htop, if_pos,
    hrestrictedProper, map_zero] at hrestricted
  exact (one_ne_zero :
    (1 : Γ(twoChartReferenceModel.underlying,
      twoChartReferenceModel.underlying.affineBasicOpen f)) ≠ 0)
    hrestricted.symm

/-- A closed-equational reading containing the restriction-broken witness. -/
noncomputable def restrictionBrokenReading :
    ClosedEquationalLawReading rawSystem twoChartReferenceModel where
  geometric := weakReading.geometric
  closed := Set.univ
  selected := weakReading.selected
  witness i _ := by
    cases i
    exact restrictionBrokenWitness

/-- Shows that the broken witness prevents witness compatibility. -/
theorem restrictionBrokenReading_not_witnessCompatible :
    ¬ IsClosedEquationalWitnessReading rawSystem twoChartReferenceModel
      restrictionBrokenReading := by
  intro hcompatible
  apply restrictionBrokenWitness_not_valid
  have hunit : restrictionBrokenReading.closed PUnit.unit := by
    change PUnit.unit ∈ (Set.univ : Set PUnit)
    trivial
  simpa only [restrictionBrokenReading] using
    hcompatible PUnit.unit hunit

/-- Shows that witness incompatibility prevents reading validity. -/
theorem restrictionBrokenReading_not_valid :
    ¬ IsClosedEquationalLawReading rawSystem twoChartReferenceModel
      restrictionBrokenReading := by
  intro hvalid
  exact restrictionBrokenReading_not_witnessCompatible
    hvalid.witness_compatible

/-- An inclusion whose atom map does not preserve the selected coordinate. -/
def coordinateBrokenInclusion :
    ClosedEquationalLawInclusion rawSystem twoChartReferenceModel
      weakReading strongReading where
  lawMap i := i
  atomMap _ a :=
    match a with
    | FiniteAtom.componentA => FiniteAtom.componentB
    | _ => FiniteAtom.componentC

/-- Exhibits the concrete coordinate-preservation failure of the broken inclusion. -/
theorem coordinateBrokenInclusion_not_valid :
    ¬ IsClosedEquationalLawInclusion rawSystem twoChartReferenceModel
      coordinateBrokenInclusion := by
  intro hvalid
  have hcoordinate := hvalid.coordinate_eq PUnit.unit
    (weakReading_requiredClosed.closed PUnit.unit
      (RingedSite.FiniteModel.site_equation_required PUnit.unit))
    ambientTopAffineOpen FiniteAtom.componentA
  rw [weakReading_witness_eq_ofSemanticCore,
    strongReading_witness_eq_ofSemanticCore] at hcoordinate
  simp only [coordinateBrokenInclusion,
    ClosedEquationalLawWitness.ofSemanticCore,
    ClosedEquationalLawWitness.ofGlobalSections] at hcoordinate
  rw [weakCore_componentA_equation,
    strongCore_componentB_equation] at hcoordinate
  have hequation : baseGlobalCoordinate - 1 = baseGlobalCoordinate + 1 := by
    simpa [ambientTopAffineOpen] using hcoordinate
  have heval := congrArg globalEvalOne hequation
  rw [map_sub, map_add, map_one,
    globalEvalOne_baseGlobalCoordinate] at heval
  norm_num at heval

end AAT.AG.LawAlgebra.FiniteExamples.ClosedEquationalGeometry
