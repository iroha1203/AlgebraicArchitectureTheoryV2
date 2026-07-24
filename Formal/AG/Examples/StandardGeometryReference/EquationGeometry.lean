import Formal.AG.Examples.StandardGeometryReference.Geometry
import Formal.AG.LawAlgebra.ClosedEquationalGeometry
import Formal.AG.LawAlgebra.Correspondence

/-!
# Standard geometry reference: equation geometry

This module owns SD2--SD4: the weak, strong, and rigid equation geometries,
their generated ideals and firing points, and the contravariant comparison
maps.

## Implementation notes — R3--R4 / SD2--SD3

These notes cover every nontrivial SD2--SD3 definition, including the weak,
strong, and rigid architectural equation systems and scheme bridges; their
readings, generated ideal sheaves, lawful closed subschemes, evaluation
morphisms, and 0/1/2 firing packages.

* The three equation systems share the fixed raw coordinate and differ by
  their concrete atom-indexed equations. Their scheme bridges are built from
  the actual raw presentation, and the readings, ideals, and closed
  subschemes are obtained through the generic closed-equational APIs.
  Supplying arbitrary ideals, exactness certificates, or closed subschemes
  was rejected because that would bypass generation by the selected laws.
* Evaluation points are actual `Scheme.Spec.map` morphisms induced by
  evaluation at `0`, `1`, and `2`. For the selected weak and strong readings,
  semantic lawfulness, witness vanishing, ideal lawfulness, and factorization
  are connected for the same evaluation morphism through the generic
  correspondence theorems. Encoding firing as a standalone predicate alias
  or as a conclusion-bearing certificate was rejected because it would not
  establish those four layers for the same morphism.

## Implementation notes — R5 / SD4

These notes cover every nontrivial SD4 definition, including
`weakToStrong`, `strongToRigid`, their validities, `lawComparison`,
`strongToRigidComparison`, `weakToRigidComparison`, and the composition
package.

* The inclusions use concrete total law and atom maps, and the scheme maps are
  built by `lawfulClosedSubschemeMap`; identity and composition laws come from
  the generic inclusion API. Comparing only the order of the resulting
  ideals was rejected because the required output is the actual
  contravariant morphism between closed subschemes.
* Strict kernel and ideal inclusions prove that the comparison maps are not
  isomorphisms. Replacing a comparison by an identity or taking a morphism as
  external fixture data was rejected because it would erase the strict
  weak/strong/rigid law hierarchy.
-/

set_option maxHeartbeats 4000000

namespace AAT.AG.Examples.StandardGeometryReferenceModels

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AAT.AG.LawAlgebra
open AlgebraicGeometry
open scoped AlgebraicGeometry Classical

noncomputable section

private theorem referenceRawRestriction_id
    (W : referenceSite.category) (x : referenceRaw.rawAlgebra W) :
    (referenceRaw.restrictionStable (𝟙 W)).quotientDesc x = x := by
  have h := congrArg (fun q => q x) (referenceRaw.quotientDesc_id W)
  simpa using h

private theorem referenceRawRestriction_comp
    {W₀ W₁ W₂ : referenceSite.category}
    (f : W₀ ⟶ W₁) (g : W₁ ⟶ W₂)
    (x : referenceRaw.rawAlgebra W₂) :
    (referenceRaw.restrictionStable (f ≫ g)).quotientDesc x =
      (referenceRaw.restrictionStable f).quotientDesc
        ((referenceRaw.restrictionStable g).quotientDesc x) := by
  have h := congrArg (fun q => q x) (referenceRaw.quotientDesc_comp f g)
  simpa [RingHom.comp_apply] using h

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
noncomputable def weakLawEquationCore :
    ArchitecturalEquationSystem referenceSite.contextPreorder where
  Index := referenceSite.equationSystem.Index
  role := referenceSite.equationSystem.role
  Observable W := referenceRaw.rawAlgebra W
  observableCommRing W := inferInstance
  restrict f := (referenceRaw.restrictionStable f).quotientDesc
  restrict_id := referenceRawRestriction_id
  restrict_comp := referenceRawRestriction_comp
  violationCoordinate W _ a :=
    match a with
    | AAT.AG.FiniteModel.FiniteAtom.componentA =>
        rawCoordinate W * (rawCoordinate W - 1)
    | _ => 0
  violationCoordinate_restrict := by
    intro source target f lawIndex atom
    cases atom <;> simp only [map_mul, map_sub, map_one, map_zero,
      rawCoordinate_restrict]
  equationResidual W object _index _atom :=
    (AAT.AG.FiniteModel.noCycleResidual object : referenceRaw.rawAlgebra W)
  equationResidual_restrict := by
    intro source target f object index atom
    rw [map_intCast]

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
noncomputable def strongLawEquationCore :
    ArchitecturalEquationSystem referenceSite.contextPreorder where
  Index := referenceSite.equationSystem.Index
  role := referenceSite.equationSystem.role
  Observable W := referenceRaw.rawAlgebra W
  observableCommRing W := inferInstance
  restrict f := (referenceRaw.restrictionStable f).quotientDesc
  restrict_id := referenceRawRestriction_id
  restrict_comp := referenceRawRestriction_comp
  violationCoordinate W _ a :=
    match a with
    | AAT.AG.FiniteModel.FiniteAtom.componentA =>
        rawCoordinate W * (rawCoordinate W - 1)
    | AAT.AG.FiniteModel.FiniteAtom.componentB => rawCoordinate W
    | _ => 0
  violationCoordinate_restrict := by
    intro source target f lawIndex atom
    cases atom <;> simp only [map_mul, map_sub, map_one, map_zero,
      rawCoordinate_restrict]
  equationResidual W object _index _atom :=
    (AAT.AG.FiniteModel.noCycleResidual object : referenceRaw.rawAlgebra W)
  equationResidual_restrict := by
    intro source target f object index atom
    rw [map_intCast]

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
noncomputable def rigidLawEquationCore :
    ArchitecturalEquationSystem referenceSite.contextPreorder where
  Index := referenceSite.equationSystem.Index
  role := referenceSite.equationSystem.role
  Observable W := referenceRaw.rawAlgebra W
  observableCommRing W := inferInstance
  restrict f := (referenceRaw.restrictionStable f).quotientDesc
  restrict_id := referenceRawRestriction_id
  restrict_comp := referenceRawRestriction_comp
  violationCoordinate W _ a :=
    match a with
    | AAT.AG.FiniteModel.FiniteAtom.componentA =>
        rawCoordinate W * (rawCoordinate W - 1)
    | AAT.AG.FiniteModel.FiniteAtom.componentB => rawCoordinate W
    | AAT.AG.FiniteModel.FiniteAtom.componentC =>
        algebraMap Int (referenceRaw.rawAlgebra W) 2
    | _ => 0
  violationCoordinate_restrict := by
    intro source target f lawIndex atom
    cases atom <;> simp only [map_mul, map_sub, map_one, map_zero,
      map_ofNat, rawCoordinate_restrict]
  equationResidual W object _index _atom :=
    (AAT.AG.FiniteModel.noCycleResidual object : referenceRaw.rawAlgebra W)
  equationResidual_restrict := by
    intro source target f object index atom
    rw [map_intCast]

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
@[simp] theorem weakLawEquationCore_observable
    (W : referenceSite.category) :
    weakLawEquationCore.Observable W = referenceRaw.rawAlgebra W :=
  rfl

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
@[simp] theorem strongLawEquationCore_observable
    (W : referenceSite.category) :
    strongLawEquationCore.Observable W = referenceRaw.rawAlgebra W :=
  rfl

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
@[simp] theorem rigidLawEquationCore_observable
    (W : referenceSite.category) :
    rigidLawEquationCore.Observable W = referenceRaw.rawAlgebra W :=
  rfl

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
@[simp] theorem weakLawEquationCore_observableCommRing
    (W : referenceSite.category) :
    weakLawEquationCore.observableCommRing W =
      inferInstanceAs (CommRing (referenceRaw.rawAlgebra W)) :=
  rfl

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
@[simp] theorem strongLawEquationCore_observableCommRing
    (W : referenceSite.category) :
    strongLawEquationCore.observableCommRing W =
      inferInstanceAs (CommRing (referenceRaw.rawAlgebra W)) :=
  rfl

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
@[simp] theorem rigidLawEquationCore_observableCommRing
    (W : referenceSite.category) :
    rigidLawEquationCore.observableCommRing W =
      inferInstanceAs (CommRing (referenceRaw.rawAlgebra W)) :=
  rfl

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
@[simp] theorem weakLawEquationCore_restrict
    {source target : referenceSite.category} (f : source ⟶ target) :
    weakLawEquationCore.restrict f =
      (referenceRaw.restrictionStable f).quotientDesc :=
  rfl

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
@[simp] theorem strongLawEquationCore_restrict
    {source target : referenceSite.category} (f : source ⟶ target) :
    strongLawEquationCore.restrict f =
      (referenceRaw.restrictionStable f).quotientDesc :=
  rfl

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
@[simp] theorem rigidLawEquationCore_restrict
    {source target : referenceSite.category} (f : source ⟶ target) :
    rigidLawEquationCore.restrict f =
      (referenceRaw.restrictionStable f).quotientDesc :=
  rfl

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
@[simp] theorem weakViolationWitness_eq
    (W : referenceSite.category)
    (a : AAT.AG.FiniteModel.carrier.Atom) :
    weakLawEquationCore.violationCoordinate W PUnit.unit a =
      if a = AAT.AG.FiniteModel.FiniteAtom.componentA then
        rawCoordinate W * (rawCoordinate W - 1)
      else 0 :=
  by
    cases a <;> simp [weakLawEquationCore]

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
@[simp] theorem strongViolationWitness_eq
    (W : referenceSite.category)
    (a : AAT.AG.FiniteModel.carrier.Atom) :
    strongLawEquationCore.violationCoordinate W PUnit.unit a =
      if a = AAT.AG.FiniteModel.FiniteAtom.componentA then
        rawCoordinate W * (rawCoordinate W - 1)
      else if a = AAT.AG.FiniteModel.FiniteAtom.componentB then
        rawCoordinate W
      else 0 :=
  by
    cases a <;> simp [strongLawEquationCore]

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
@[simp] theorem rigidViolationWitness_eq
    (W : referenceSite.category)
    (a : AAT.AG.FiniteModel.carrier.Atom) :
    rigidLawEquationCore.violationCoordinate W PUnit.unit a =
      if a = AAT.AG.FiniteModel.FiniteAtom.componentA then
        rawCoordinate W * (rawCoordinate W - 1)
      else if a = AAT.AG.FiniteModel.FiniteAtom.componentB then
        rawCoordinate W
      else if a = AAT.AG.FiniteModel.FiniteAtom.componentC then
        algebraMap Int (referenceRaw.rawAlgebra W) 2
      else 0 :=
  by
    cases a <;> simp [rigidLawEquationCore]

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
noncomputable def weakSchemeBridge :
    SemanticLawEquationSchemeBridge referenceRaw weakLawEquationCore where
  toRawPresentation W := RingEquiv.refl (referenceRaw.rawAlgebra W)

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
noncomputable def strongSchemeBridge :
    SemanticLawEquationSchemeBridge referenceRaw strongLawEquationCore where
  toRawPresentation W := RingEquiv.refl (referenceRaw.rawAlgebra W)

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
noncomputable def rigidSchemeBridge :
    SemanticLawEquationSchemeBridge referenceRaw rigidLawEquationCore where
  toRawPresentation W := RingEquiv.refl (referenceRaw.rawAlgebra W)

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
@[simp] theorem weakSchemeBridge_toRawPresentation
    (W : referenceSite.category) :
    weakSchemeBridge.toRawPresentation W =
      RingEquiv.refl (referenceRaw.rawAlgebra W) :=
  rfl

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
@[simp] theorem strongSchemeBridge_toRawPresentation
    (W : referenceSite.category) :
    strongSchemeBridge.toRawPresentation W =
      RingEquiv.refl (referenceRaw.rawAlgebra W) :=
  rfl

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
@[simp] theorem rigidSchemeBridge_toRawPresentation
    (W : referenceSite.category) :
    rigidSchemeBridge.toRawPresentation W =
      RingEquiv.refl (referenceRaw.rawAlgebra W) :=
  rfl

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
theorem weakSchemeBridge_valid :
    IsSemanticLawEquationSchemeBridge
      referenceRaw weakLawEquationCore weakSchemeBridge := by
  constructor
  · intro source target f x
    have hn := referenceRaw.toRingedSite.canonical.naturality f.op
    have ha := congrArg (fun q => q.right x) hn
    change
      (referenceRaw.toRingedSite.canonical.app (op source)).right
          ((referenceRaw.restrictionStable f).quotientDesc x) =
        (referenceRaw.toRingedSite.structureSheaf.val.map f.op).right
          ((referenceRaw.toRingedSite.canonical.app (op target)).right x)
    simpa only [CommRingCat.comp_apply,
      RawAmbientRestrictionSystem.toRingedSite_raw] using ha
  · intro W
    exact { canonical_isIso := canonical_component_isIso W }

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
theorem strongSchemeBridge_valid :
    IsSemanticLawEquationSchemeBridge
      referenceRaw strongLawEquationCore strongSchemeBridge := by
  constructor
  · intro source target f x
    have hn := referenceRaw.toRingedSite.canonical.naturality f.op
    have ha := congrArg (fun q => q.right x) hn
    change
      (referenceRaw.toRingedSite.canonical.app (op source)).right
          ((referenceRaw.restrictionStable f).quotientDesc x) =
        (referenceRaw.toRingedSite.structureSheaf.val.map f.op).right
          ((referenceRaw.toRingedSite.canonical.app (op target)).right x)
    simpa only [CommRingCat.comp_apply,
      RawAmbientRestrictionSystem.toRingedSite_raw] using ha
  · intro W
    exact { canonical_isIso := canonical_component_isIso W }

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
theorem rigidSchemeBridge_valid :
    IsSemanticLawEquationSchemeBridge
      referenceRaw rigidLawEquationCore rigidSchemeBridge := by
  constructor
  · intro source target f x
    have hn := referenceRaw.toRingedSite.canonical.naturality f.op
    have ha := congrArg (fun q => q.right x) hn
    change
      (referenceRaw.toRingedSite.canonical.app (op source)).right
          ((referenceRaw.restrictionStable f).quotientDesc x) =
        (referenceRaw.toRingedSite.structureSheaf.val.map f.op).right
          ((referenceRaw.toRingedSite.canonical.app (op target)).right x)
    simpa only [CommRingCat.comp_apply,
      RawAmbientRestrictionSystem.toRingedSite_raw] using ha
  · intro W
    exact { canonical_isIso := canonical_component_isIso W }

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
noncomputable def weakReading :
    ClosedEquationalLawReading referenceRaw referenceScheme
      weakLawEquationCore :=
  ClosedEquationalLawReading.ofSemanticCore
    referenceRaw referenceScheme weakLawEquationCore weakSchemeBridge

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
@[simp] theorem weakReading_eq :
    weakReading =
      ClosedEquationalLawReading.ofSemanticCore
        referenceRaw referenceScheme weakLawEquationCore weakSchemeBridge :=
  rfl

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
noncomputable def strongReading :
    ClosedEquationalLawReading referenceRaw referenceScheme
      strongLawEquationCore :=
  ClosedEquationalLawReading.ofSemanticCore
    referenceRaw referenceScheme strongLawEquationCore strongSchemeBridge

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
@[simp] theorem strongReading_eq :
    strongReading =
      ClosedEquationalLawReading.ofSemanticCore
        referenceRaw referenceScheme strongLawEquationCore strongSchemeBridge :=
  rfl

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
noncomputable def rigidReading :
    ClosedEquationalLawReading referenceRaw referenceScheme
      rigidLawEquationCore :=
  ClosedEquationalLawReading.ofSemanticCore
    referenceRaw referenceScheme rigidLawEquationCore rigidSchemeBridge

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
@[simp] theorem rigidReading_eq :
    rigidReading =
      ClosedEquationalLawReading.ofSemanticCore
        referenceRaw referenceScheme rigidLawEquationCore rigidSchemeBridge :=
  rfl

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
theorem weakReading_valid :
    IsClosedEquationalLawReading referenceRaw referenceScheme weakReading :=
  ClosedEquationalLawReading.ofSemanticCore_valid
    referenceRaw referenceScheme weakLawEquationCore weakSchemeBridge

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
theorem strongReading_valid :
    IsClosedEquationalLawReading referenceRaw referenceScheme strongReading :=
  ClosedEquationalLawReading.ofSemanticCore_valid
    referenceRaw referenceScheme strongLawEquationCore strongSchemeBridge

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
theorem rigidReading_valid :
    IsClosedEquationalLawReading referenceRaw referenceScheme rigidReading :=
  ClosedEquationalLawReading.ofSemanticCore_valid
    referenceRaw referenceScheme rigidLawEquationCore rigidSchemeBridge

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
theorem weakReading_requiredClosed :
    RequiredClosed referenceRaw referenceScheme weakReading :=
  ClosedEquationalLawReading.ofSemanticCore_requiredClosed
    referenceRaw referenceScheme weakLawEquationCore weakSchemeBridge

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
theorem strongReading_requiredClosed :
    RequiredClosed referenceRaw referenceScheme strongReading :=
  ClosedEquationalLawReading.ofSemanticCore_requiredClosed
    referenceRaw referenceScheme strongLawEquationCore strongSchemeBridge

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
theorem rigidReading_requiredClosed :
    RequiredClosed referenceRaw referenceScheme rigidReading :=
  ClosedEquationalLawReading.ofSemanticCore_requiredClosed
    referenceRaw referenceScheme rigidLawEquationCore rigidSchemeBridge

private theorem referenceCore_lawIdealExact
    (G : ArchitecturalEquationSystem referenceSite.contextPreorder)
    (B : SemanticLawEquationSchemeBridge referenceRaw G)
    (i : G.Index) :
    LawIdealExact referenceRaw referenceScheme
      (ClosedEquationalLawReading.ofSemanticCore referenceRaw
        referenceScheme G B)
      (ClosedEquationalLawReading.ofSemanticCore_witnessCompatible
        referenceRaw referenceScheme G B)
      i (Set.mem_univ i) := by
  intro T s
  change (GeometricLawReading.ofSemanticCore referenceRaw referenceScheme
    G B).HoldsOn s i ↔ _
  rw [GeometricLawReading.ofSemanticCore_holdsOn]
  have hsheaf := lawWitnessIdealSheaf_ofGlobalSections referenceRaw
    referenceScheme
    (ClosedEquationalLawReading.ofSemanticCore referenceRaw
      referenceScheme G B)
    (ClosedEquationalLawReading.ofSemanticCore_witnessCompatible
      referenceRaw referenceScheme G B)
    i (Set.mem_univ i)
    (semanticCoreGlobalEquation referenceRaw referenceScheme G B i)
    (by
      exact ClosedEquationalLawReading.ofSemanticCore_witness referenceRaw
        referenceScheme G B i (Set.mem_univ i))
  rw [hsheaf]
  exact globalEquationsVanishAlong_iff_ofIdealTop_span_comap_eq_bot
    referenceRaw referenceScheme
    (semanticCoreGlobalEquation referenceRaw referenceScheme G B i) s

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
theorem weakReading_requiredLawIdealExact :
    RequiredLawIdealExact referenceRaw referenceScheme
      weakReading weakReading_valid weakReading_requiredClosed :=
  by
    intro i hi
    cases i
    intro T s
    simpa only [weakReading] using
      referenceCore_lawIdealExact weakLawEquationCore weakSchemeBridge
        PUnit.unit (T := T) s

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
theorem strongReading_requiredLawIdealExact :
    RequiredLawIdealExact referenceRaw referenceScheme
      strongReading strongReading_valid strongReading_requiredClosed :=
  by
    intro i hi
    cases i
    intro T s
    simpa only [strongReading] using
      referenceCore_lawIdealExact strongLawEquationCore strongSchemeBridge
        PUnit.unit (T := T) s

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
theorem rigidReading_requiredLawIdealExact :
    RequiredLawIdealExact referenceRaw referenceScheme
      rigidReading rigidReading_valid rigidReading_requiredClosed :=
  by
    intro i hi
    cases i
    intro T s
    simpa only [rigidReading] using
      referenceCore_lawIdealExact rigidLawEquationCore rigidSchemeBridge
        PUnit.unit (T := T) s

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
noncomputable abbrev weakIdealSheaf :
    referenceScheme.underlying.IdealSheafData :=
  lawGeneratedIdealSheaf referenceRaw referenceScheme
    weakReading weakReading_valid weakReading_requiredClosed

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
@[simp] theorem weakIdealSheaf_eq :
    weakIdealSheaf =
      lawGeneratedIdealSheaf referenceRaw referenceScheme
        weakReading weakReading_valid weakReading_requiredClosed :=
  rfl

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
noncomputable abbrev strongIdealSheaf :
    referenceScheme.underlying.IdealSheafData :=
  lawGeneratedIdealSheaf referenceRaw referenceScheme
    strongReading strongReading_valid strongReading_requiredClosed

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
@[simp] theorem strongIdealSheaf_eq :
    strongIdealSheaf =
      lawGeneratedIdealSheaf referenceRaw referenceScheme
        strongReading strongReading_valid strongReading_requiredClosed :=
  rfl

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
noncomputable abbrev rigidIdealSheaf :
    referenceScheme.underlying.IdealSheafData :=
  lawGeneratedIdealSheaf referenceRaw referenceScheme
    rigidReading rigidReading_valid rigidReading_requiredClosed

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
@[simp] theorem rigidIdealSheaf_eq :
    rigidIdealSheaf =
      lawGeneratedIdealSheaf referenceRaw referenceScheme
        rigidReading rigidReading_valid rigidReading_requiredClosed :=
  rfl

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
noncomputable abbrev weakLocus : AlgebraicGeometry.Scheme :=
  lawfulClosedSubscheme referenceRaw referenceScheme
    weakReading weakReading_valid weakReading_requiredClosed

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
@[simp] theorem weakLocus_eq :
    weakLocus =
      lawfulClosedSubscheme referenceRaw referenceScheme
        weakReading weakReading_valid weakReading_requiredClosed :=
  rfl

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
noncomputable abbrev strongLocus : AlgebraicGeometry.Scheme :=
  lawfulClosedSubscheme referenceRaw referenceScheme
    strongReading strongReading_valid strongReading_requiredClosed

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
@[simp] theorem strongLocus_eq :
    strongLocus =
      lawfulClosedSubscheme referenceRaw referenceScheme
        strongReading strongReading_valid strongReading_requiredClosed :=
  rfl

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
noncomputable abbrev rigidLocus : AlgebraicGeometry.Scheme :=
  lawfulClosedSubscheme referenceRaw referenceScheme
    rigidReading rigidReading_valid rigidReading_requiredClosed

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
@[simp] theorem rigidLocus_eq :
    rigidLocus =
      lawfulClosedSubscheme referenceRaw referenceScheme
        rigidReading rigidReading_valid rigidReading_requiredClosed :=
  rfl

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
noncomputable abbrev weakImmersion :
    weakLocus ⟶ referenceScheme.underlying :=
  lawfulClosedImmersion referenceRaw referenceScheme
    weakReading weakReading_valid weakReading_requiredClosed

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
@[simp] theorem weakImmersion_eq :
    weakImmersion =
      lawfulClosedImmersion referenceRaw referenceScheme
        weakReading weakReading_valid weakReading_requiredClosed :=
  rfl

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
noncomputable abbrev strongImmersion :
    strongLocus ⟶ referenceScheme.underlying :=
  lawfulClosedImmersion referenceRaw referenceScheme
    strongReading strongReading_valid strongReading_requiredClosed

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
@[simp] theorem strongImmersion_eq :
    strongImmersion =
      lawfulClosedImmersion referenceRaw referenceScheme
        strongReading strongReading_valid strongReading_requiredClosed :=
  rfl

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
noncomputable abbrev rigidImmersion :
    rigidLocus ⟶ referenceScheme.underlying :=
  lawfulClosedImmersion referenceRaw referenceScheme
    rigidReading rigidReading_valid rigidReading_requiredClosed

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
@[simp] theorem rigidImmersion_eq :
    rigidImmersion =
      lawfulClosedImmersion referenceRaw referenceScheme
        rigidReading rigidReading_valid rigidReading_requiredClosed :=
  rfl

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
noncomputable def ambientGlobalSectionsIso :
  Γ(referenceScheme.underlying, ⊤) ≅
      CommRingCat.of AmbientRing :=
  AlgebraicGeometry.Scheme.ΓSpecIso
    (CommRingCat.of AmbientRing)

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
@[simp] theorem ambientGlobalSectionsIso_eq :
    ambientGlobalSectionsIso =
      AlgebraicGeometry.Scheme.ΓSpecIso
        (CommRingCat.of AmbientRing) :=
  rfl

private theorem ambientGlobalSectionsIso_unit
    (x : referenceRaw.rawAlgebra baseContext) :
    ambientGlobalSectionsIso.hom
        (ambientDecoration.interpretation
          ((sheafificationUnitAlgHom referenceRaw baseContext) x)) =
      baseRawAlgebraIso.hom x := by
  letI := canonical_component_isIso baseContext
  simp only [ambientGlobalSectionsIso, ambientDecoration,
    AATReadingDecoration.pullback_interpretation,
    AATReadingDecoration.ofContext_interpretation,
    baseChartDomainIso, AlgebraicGeometry.Scheme.Spec.mapIso_inv]
  change
    (AlgebraicGeometry.Scheme.ΓSpecIso
        (CommRingCat.of AmbientRing)).hom
        (((AlgebraicGeometry.Scheme.ΓSpecIso
            (SheafifiedSectionRing referenceRaw baseContext)).inv ≫
          (AlgebraicGeometry.Scheme.Spec.map
            baseSectionRingIso.hom.op).appTop)
          ((sheafificationUnitAlgHom referenceRaw baseContext) x)) =
      baseRawAlgebraIso.hom x
  rw [AlgebraicGeometry.Scheme.Spec_map]
  simp only [CommRingCat.comp_apply]
  have hΓ := congrArg
    (fun q => q.hom
      ((AlgebraicGeometry.Scheme.ΓSpecIso
        (SheafifiedSectionRing referenceRaw baseContext)).inv
          ((sheafificationUnitAlgHom referenceRaw baseContext) x)))
    (AlgebraicGeometry.Scheme.ΓSpecIso_naturality
      baseSectionRingIso.hom)
  change
    (AlgebraicGeometry.Scheme.ΓSpecIso
      (CommRingCat.of AmbientRing)).hom
        ((AlgebraicGeometry.Spec.map baseSectionRingIso.hom).appTop
          ((AlgebraicGeometry.Scheme.ΓSpecIso
            (SheafifiedSectionRing referenceRaw baseContext)).inv
            ((sheafificationUnitAlgHom referenceRaw baseContext) x))) =
      baseSectionRingIso.hom
        ((AlgebraicGeometry.Scheme.ΓSpecIso
          (SheafifiedSectionRing referenceRaw baseContext)).hom
          ((AlgebraicGeometry.Scheme.ΓSpecIso
            (SheafifiedSectionRing referenceRaw baseContext)).inv
            ((sheafificationUnitAlgHom referenceRaw baseContext) x))) at hΓ
  calc
    _ = baseSectionRingIso.hom
        ((sheafificationUnitAlgHom referenceRaw baseContext) x) := by
      simpa only [CommRingCat.comp_apply, Iso.inv_hom_id_apply,
        Quiver.Hom.unop_op] using hΓ
    _ = baseRawAlgebraIso.hom x := by
      change baseRawAlgebraIso.hom
          ((inv (referenceRaw.toRingedSite.canonical.app
            (op baseContext)).right)
            ((referenceRaw.toRingedSite.canonical.app
              (op baseContext)).right x)) = _
      have hcancel := congrArg
        (fun q => q x)
        (IsIso.hom_inv_id
          (referenceRaw.toRingedSite.canonical.app
            (op baseContext)).right)
      rw [show (inv (referenceRaw.toRingedSite.canonical.app
          (op baseContext)).right)
          ((referenceRaw.toRingedSite.canonical.app
            (op baseContext)).right x) = x by
        simpa only [CommRingCat.comp_apply, Category.id_comp] using hcancel]

/--
The reference equation system is realized by the canonical integer
coefficient inclusion into the global sections of `Spec ℤ[x]`.
-/
noncomputable def referenceEquationObservableRealization :
    EquationObservableRealization
      referenceRaw referenceScheme referenceSite.equationSystem where
  sectionMap := fun _ =>
    ambientGlobalSectionsIso.inv.hom.comp
      (algebraMap Int AmbientRing)
  naturality := by
    intro source target f x
    rfl

/-- One symbolic equation section in the generated reference realization. -/
noncomputable def referenceSiteGlobalEquation
    (W : referenceSite.category)
    (i : referenceSite.equationSystem.Index)
    (a : AAT.AG.FiniteModel.carrier.Atom) :
    Γ(referenceScheme.underlying, ⊤) :=
  referenceEquationObservableRealization.violationSection W i a

/-- One actual object-residual section in the generated reference realization. -/
noncomputable def referenceSiteResidualSection
    (Obj : ArchitectureObject AAT.AG.FiniteModel.carrier)
    (W : referenceSite.category)
    (i : referenceSite.equationSystem.Index)
    (a : AAT.AG.FiniteModel.carrier.Atom) :
    Γ(referenceScheme.underlying, ⊤) :=
  referenceEquationObservableRealization.residualSection Obj W i a

/-- The symbolic section is the canonical image of the selected coordinate. -/
theorem referenceSiteGlobalEquation_image
    (W : referenceSite.category)
    (i : referenceSite.equationSystem.Index)
    (a : AAT.AG.FiniteModel.carrier.Atom) :
    ambientGlobalSectionsIso.hom (referenceSiteGlobalEquation W i a) =
      algebraMap Int AmbientRing
        (referenceSite.equationSystem.violationCoordinate W i a) := by
  simp only [referenceSiteGlobalEquation,
    EquationObservableRealization.violationSection,
    referenceEquationObservableRealization, RingHom.comp_apply]
  exact ambientGlobalSectionsIso.commRingCatIsoToRingEquiv.apply_symm_apply _

/-- The residual section is the canonical image of the actual residual. -/
theorem referenceSiteResidualSection_image
    (Obj : ArchitectureObject AAT.AG.FiniteModel.carrier)
    (W : referenceSite.category)
    (i : referenceSite.equationSystem.Index)
    (a : AAT.AG.FiniteModel.carrier.Atom) :
    ambientGlobalSectionsIso.hom
        (referenceSiteResidualSection Obj W i a) =
      algebraMap Int AmbientRing
        (referenceSite.equationSystem.equationResidual W Obj i a) := by
  simp only [referenceSiteResidualSection,
    EquationObservableRealization.residualSection,
    referenceEquationObservableRealization, RingHom.comp_apply]
  exact ambientGlobalSectionsIso.commRingCatIsoToRingEquiv.apply_symm_apply _

/--
The required generated ideal sheaf is the pullback of the site equation
system's contextual obstruction ideal sheaf.
-/
theorem referenceSiteGeneratedIdealSheaf_eq_obstructionIdeal :
    referenceEquationObservableRealization.generatedIdealSheaf
        AAT.AG.FiniteModel.acyclicObject =
      referenceEquationObservableRealization.globalObstructionIdealSheaf.comap
        (referenceEquationObservableRealization.realizationImmersion
          AAT.AG.FiniteModel.acyclicObject) :=
  EquationObservableRealization.generatedIdealSheaf_eq_globalObstructionIdealSheaf
    referenceEquationObservableRealization
    AAT.AG.FiniteModel.acyclicObject

/--
Compatibility adapter for synthesis packages that still consume the generic
`ClosedEquationalLawReading` record.  The Issue 3733 standard route uses
`referenceEquationObservableRealization` and its actual residual predicates.
-/
noncomputable def referenceLegacySiteReading :
    ClosedEquationalLawReading referenceRaw referenceScheme
      referenceSite.equationSystem where
  geometric := {
    HoldsOn := fun s i =>
      GlobalEquationsVanishAlong referenceRaw referenceScheme
        (referenceSiteGlobalEquation baseContext i) s
  }
  closed := Set.univ
  selected := fun _ => Set.univ
  witness := fun i _ =>
    ClosedEquationalLawWitness.ofGlobalSections
      referenceRaw referenceScheme i
      (referenceSiteGlobalEquation baseContext i)

/-- The synthesis compatibility adapter satisfies the generic recognition laws. -/
theorem referenceLegacySiteReading_valid :
    IsClosedEquationalLawReading referenceRaw referenceScheme
      referenceLegacySiteReading where
  geometric_stable := by
    intro T T' s f i hs a
    rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, hs a, map_zero]
  witness_compatible := by
    intro i _
    exact ClosedEquationalLawWitness.ofGlobalSections_valid
      referenceRaw referenceScheme i _
  selected_closed := fun _ i _ => Set.mem_univ i
  selected_basicOpen := fun _ _ i =>
    iff_of_true (Set.mem_univ i) (Set.mem_univ i)

/-- Every required equation is selected by the synthesis compatibility adapter. -/
theorem referenceLegacySiteReading_requiredClosed :
    RequiredClosed referenceRaw referenceScheme
      referenceLegacySiteReading where
  closed := fun i _ => Set.mem_univ i
  selected := fun _ i _ => Set.mem_univ i

/-- The compatibility adapter's semantic predicate is exactly its witness ideal. -/
theorem referenceLegacySiteReading_requiredLawIdealExact :
    RequiredLawIdealExact referenceRaw referenceScheme
      referenceLegacySiteReading referenceLegacySiteReading_valid
      referenceLegacySiteReading_requiredClosed := by
  intro i _ T s
  change
    GlobalEquationsVanishAlong referenceRaw referenceScheme
        (referenceSiteGlobalEquation baseContext i) s ↔
      (lawWitnessIdealSheaf referenceRaw referenceScheme
        referenceLegacySiteReading
        referenceLegacySiteReading_valid.witness_compatible
        i (Set.mem_univ i)).comap s = ⊥
  rw [lawWitnessIdealSheaf_ofGlobalSections
    referenceRaw referenceScheme referenceLegacySiteReading
    referenceLegacySiteReading_valid.witness_compatible
    i (Set.mem_univ i)
    (referenceSiteGlobalEquation baseContext i) rfl]
  exact globalEquationsVanishAlong_iff_ofIdealTop_span_comap_eq_bot
    referenceRaw referenceScheme
    (referenceSiteGlobalEquation baseContext i) s

private theorem weakGlobalEquation_image
    (a : AAT.AG.FiniteModel.carrier.Atom) :
    ambientGlobalSectionsIso.hom
        (semanticCoreGlobalEquation referenceRaw referenceScheme
          weakLawEquationCore weakSchemeBridge PUnit.unit a) =
      baseRawAlgebraIso.hom
        (weakLawEquationCore.violationCoordinate baseContext PUnit.unit a) := by
  change ambientGlobalSectionsIso.hom
      (ambientDecoration.interpretation
        (weakSchemeBridge.toSheafifiedSection baseContext
          (weakLawEquationCore.violationCoordinate baseContext PUnit.unit a))) = _
  simpa [weakSchemeBridge,
    SemanticLawEquationSchemeBridge.toSheafifiedSection] using
      ambientGlobalSectionsIso_unit
        (weakLawEquationCore.violationCoordinate baseContext PUnit.unit a)

private theorem strongGlobalEquation_image
    (a : AAT.AG.FiniteModel.carrier.Atom) :
    ambientGlobalSectionsIso.hom
        (semanticCoreGlobalEquation referenceRaw referenceScheme
          strongLawEquationCore strongSchemeBridge PUnit.unit a) =
      baseRawAlgebraIso.hom
        (strongLawEquationCore.violationCoordinate baseContext PUnit.unit a) := by
  change ambientGlobalSectionsIso.hom
      (ambientDecoration.interpretation
        (strongSchemeBridge.toSheafifiedSection baseContext
          (strongLawEquationCore.violationCoordinate baseContext PUnit.unit a))) = _
  simpa [strongSchemeBridge,
    SemanticLawEquationSchemeBridge.toSheafifiedSection] using
      ambientGlobalSectionsIso_unit
        (strongLawEquationCore.violationCoordinate baseContext PUnit.unit a)

private theorem rigidGlobalEquation_image
    (a : AAT.AG.FiniteModel.carrier.Atom) :
    ambientGlobalSectionsIso.hom
        (semanticCoreGlobalEquation referenceRaw referenceScheme
          rigidLawEquationCore rigidSchemeBridge PUnit.unit a) =
      baseRawAlgebraIso.hom
        (rigidLawEquationCore.violationCoordinate baseContext PUnit.unit a) := by
  change ambientGlobalSectionsIso.hom
      (ambientDecoration.interpretation
        (rigidSchemeBridge.toSheafifiedSection baseContext
          (rigidLawEquationCore.violationCoordinate baseContext PUnit.unit a))) = _
  simpa [rigidSchemeBridge,
    SemanticLawEquationSchemeBridge.toSheafifiedSection] using
      ambientGlobalSectionsIso_unit
        (rigidLawEquationCore.violationCoordinate baseContext PUnit.unit a)

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
@[simp] theorem weakGlobalEquation_eq
    (a : AAT.AG.FiniteModel.carrier.Atom) :
    ambientGlobalSectionsIso.hom
        (semanticCoreGlobalEquation
          referenceRaw referenceScheme
          weakLawEquationCore weakSchemeBridge PUnit.unit a) =
      if a = AAT.AG.FiniteModel.FiniteAtom.componentA then
        coordinate * (coordinate - 1)
      else 0 := by
  rw [weakGlobalEquation_image]
  change baseRawAlgebraIso.hom
      (match a with
      | AAT.AG.FiniteModel.FiniteAtom.componentA =>
          rawCoordinate baseContext * (rawCoordinate baseContext - 1)
      | _ => 0) = _
  cases a
  case componentA =>
    simp only [↓reduceIte]
    change baseRawAlgebraIso.hom
        (rawCoordinate baseContext * (rawCoordinate baseContext - 1)) =
      coordinate * (coordinate - 1)
    rw [map_mul, map_sub, map_one, baseRawAlgebraIso_coordinate]
  all_goals simp

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
@[simp] theorem strongGlobalEquation_eq
    (a : AAT.AG.FiniteModel.carrier.Atom) :
    ambientGlobalSectionsIso.hom
        (semanticCoreGlobalEquation
          referenceRaw referenceScheme
          strongLawEquationCore strongSchemeBridge PUnit.unit a) =
      if a = AAT.AG.FiniteModel.FiniteAtom.componentA then
        coordinate * (coordinate - 1)
      else if a = AAT.AG.FiniteModel.FiniteAtom.componentB then
        coordinate
      else 0 := by
  rw [strongGlobalEquation_image]
  change baseRawAlgebraIso.hom
      (match a with
      | AAT.AG.FiniteModel.FiniteAtom.componentA =>
          rawCoordinate baseContext * (rawCoordinate baseContext - 1)
      | AAT.AG.FiniteModel.FiniteAtom.componentB => rawCoordinate baseContext
      | _ => 0) = _
  cases a
  case componentA =>
    simp only [↓reduceIte]
    change baseRawAlgebraIso.hom
        (rawCoordinate baseContext * (rawCoordinate baseContext - 1)) =
      coordinate * (coordinate - 1)
    rw [map_mul, map_sub, map_one, baseRawAlgebraIso_coordinate]
  case componentB =>
    rw [if_neg (by simp), if_pos rfl]
    exact baseRawAlgebraIso_coordinate
  all_goals simp

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
@[simp] theorem rigidGlobalEquation_eq
    (a : AAT.AG.FiniteModel.carrier.Atom) :
    ambientGlobalSectionsIso.hom
        (semanticCoreGlobalEquation
          referenceRaw referenceScheme
          rigidLawEquationCore rigidSchemeBridge PUnit.unit a) =
      if a = AAT.AG.FiniteModel.FiniteAtom.componentA then
        coordinate * (coordinate - 1)
      else if a = AAT.AG.FiniteModel.FiniteAtom.componentB then
        coordinate
      else if a = AAT.AG.FiniteModel.FiniteAtom.componentC then
        MvPolynomial.C 2
      else 0 := by
  rw [rigidGlobalEquation_image]
  change baseRawAlgebraIso.hom
      (match a with
      | AAT.AG.FiniteModel.FiniteAtom.componentA =>
          rawCoordinate baseContext * (rawCoordinate baseContext - 1)
      | AAT.AG.FiniteModel.FiniteAtom.componentB => rawCoordinate baseContext
      | AAT.AG.FiniteModel.FiniteAtom.componentC =>
          algebraMap Int (referenceRaw.rawAlgebra baseContext) 2
      | _ => 0) = _
  cases a
  case componentA =>
    simp only [↓reduceIte]
    change baseRawAlgebraIso.hom
        (rawCoordinate baseContext * (rawCoordinate baseContext - 1)) =
      coordinate * (coordinate - 1)
    rw [map_mul, map_sub, map_one, baseRawAlgebraIso_coordinate]
  case componentB =>
    rw [if_neg (by simp), if_pos rfl]
    exact baseRawAlgebraIso_coordinate
  case componentC =>
    rw [if_neg (by simp), if_neg (by simp), if_pos rfl]
    change baseRawAlgebraIso.hom
        (algebraMap Int (referenceRaw.rawAlgebra baseContext) 2) =
      algebraMap Int AmbientRing 2
    simp only [map_ofNat]
  all_goals simp


/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
def weakAmbientIdeal : Ideal AmbientRing :=
  Ideal.span {coordinate * (coordinate - 1)}

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
@[simp] theorem weakAmbientIdeal_eq :
    weakAmbientIdeal =
      Ideal.span {coordinate * (coordinate - 1)} :=
  rfl

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
def strongAmbientIdeal : Ideal AmbientRing :=
  Ideal.span {coordinate}

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
@[simp] theorem strongAmbientIdeal_eq :
    strongAmbientIdeal = Ideal.span {coordinate} :=
  rfl

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
def rigidAmbientIdeal : Ideal AmbientRing :=
  Ideal.span {coordinate, MvPolynomial.C 2}

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
@[simp] theorem rigidAmbientIdeal_eq :
    rigidAmbientIdeal =
      Ideal.span {coordinate, MvPolynomial.C 2} :=
  rfl

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
def weakLeftIdeal : Ideal (Localization.Away leftGenerator) :=
  Ideal.span
    {algebraMap AmbientRing (Localization.Away leftGenerator)
      (coordinate * (coordinate - 1))}

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
@[simp] theorem weakLeftIdeal_eq :
    weakLeftIdeal =
      Ideal.span
        {algebraMap AmbientRing (Localization.Away leftGenerator)
          (coordinate * (coordinate - 1))} :=
  rfl

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
def weakRightIdeal : Ideal (Localization.Away rightGenerator) :=
  Ideal.span
    {algebraMap AmbientRing (Localization.Away rightGenerator)
      (coordinate * (coordinate - 1))}

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
@[simp] theorem weakRightIdeal_eq :
    weakRightIdeal =
      Ideal.span
        {algebraMap AmbientRing (Localization.Away rightGenerator)
          (coordinate * (coordinate - 1))} :=
  rfl

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
def weakOverlapIdeal : Ideal (Localization.Away overlapGenerator) :=
  Ideal.span
    {algebraMap AmbientRing (Localization.Away overlapGenerator)
      (coordinate * (coordinate - 1))}

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
@[simp] theorem weakOverlapIdeal_eq :
    weakOverlapIdeal =
      Ideal.span
        {algebraMap AmbientRing (Localization.Away overlapGenerator)
          (coordinate * (coordinate - 1))} :=
  rfl

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
def strongLeftIdeal : Ideal (Localization.Away leftGenerator) :=
  Ideal.span
    {algebraMap AmbientRing (Localization.Away leftGenerator) coordinate}

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
@[simp] theorem strongLeftIdeal_eq :
    strongLeftIdeal =
      Ideal.span
        {algebraMap AmbientRing
          (Localization.Away leftGenerator) coordinate} :=
  rfl

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
def strongRightIdeal : Ideal (Localization.Away rightGenerator) :=
  Ideal.span
    {algebraMap AmbientRing (Localization.Away rightGenerator) coordinate}

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
@[simp] theorem strongRightIdeal_eq :
    strongRightIdeal =
      Ideal.span
        {algebraMap AmbientRing
          (Localization.Away rightGenerator) coordinate} :=
  rfl

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
def strongOverlapIdeal : Ideal (Localization.Away overlapGenerator) :=
  Ideal.span
    {algebraMap AmbientRing (Localization.Away overlapGenerator) coordinate}

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
@[simp] theorem strongOverlapIdeal_eq :
    strongOverlapIdeal =
      Ideal.span
        {algebraMap AmbientRing
          (Localization.Away overlapGenerator) coordinate} :=
  rfl

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
noncomputable def leftChartGlobalSectionsIso :
  Γ(leftChart.domain, ⊤) ≅
      CommRingCat.of (Localization.Away leftGenerator) :=
  AlgebraicGeometry.Scheme.ΓSpecIso
      (SheafifiedSectionRing referenceRaw leftContext) ≪≫
    leftSectionRingIso

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
@[simp] theorem leftChartGlobalSectionsIso_eq :
    leftChartGlobalSectionsIso =
      AlgebraicGeometry.Scheme.ΓSpecIso
          (SheafifiedSectionRing referenceRaw leftContext) ≪≫
        leftSectionRingIso :=
  rfl

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
noncomputable def rightChartGlobalSectionsIso :
  Γ(rightChart.domain, ⊤) ≅
      CommRingCat.of (Localization.Away rightGenerator) :=
  AlgebraicGeometry.Scheme.ΓSpecIso
      (SheafifiedSectionRing referenceRaw rightContext) ≪≫
    rightSectionRingIso

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
@[simp] theorem rightChartGlobalSectionsIso_eq :
    rightChartGlobalSectionsIso =
      AlgebraicGeometry.Scheme.ΓSpecIso
          (SheafifiedSectionRing referenceRaw rightContext) ≪≫
        rightSectionRingIso :=
  rfl

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
noncomputable def actualOverlapGlobalSectionsIso :
    Γ(referenceScheme.atlas.actualOverlap
        referenceRaw leftIndex rightIndex, ⊤) ≅
      CommRingCat.of (Localization.Away overlapGenerator) :=
  (asIso actualOverlapIso.inv.appTop) ≪≫
    AlgebraicGeometry.Scheme.ΓSpecIso
      (CommRingCat.of (Localization.Away overlapGenerator))

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
@[simp] theorem actualOverlapGlobalSectionsIso_eq :
    actualOverlapGlobalSectionsIso =
      (asIso actualOverlapIso.inv.appTop) ≪≫
        AlgebraicGeometry.Scheme.ΓSpecIso
          (CommRingCat.of (Localization.Away overlapGenerator)) :=
  rfl

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
noncomputable def ambientTopAffineOpen :
    referenceScheme.underlying.affineOpens := by
  letI : IsAffine referenceScheme.underlying := by
    rw [referenceScheme_underlying, ambientScheme_eq]
    infer_instance
  exact ⟨⊤, isAffineOpen_top _⟩

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
@[simp] theorem ambientTopAffineOpen_obj :
    ambientTopAffineOpen.1 = ⊤ :=
  rfl

private theorem reference_local_top_eq_span
    (G : ArchitecturalEquationSystem referenceSite.contextPreorder)
    (B : SemanticLawEquationSchemeBridge referenceRaw G)
    (i : G.Index)
    (hi : (ClosedEquationalLawReading.ofSemanticCore referenceRaw
      referenceScheme G B).closed i) :
    localLawWitnessIdeal referenceRaw referenceScheme
        ((ClosedEquationalLawReading.ofSemanticCore referenceRaw
          referenceScheme G B).witness i hi)
        ambientTopAffineOpen =
      Ideal.span (Set.range (semanticCoreGlobalEquation referenceRaw
        referenceScheme G B i)) := by
  let reading := ClosedEquationalLawReading.ofSemanticCore referenceRaw
    referenceScheme G B
  rw [← lawWitnessIdealSheaf_ideal referenceRaw referenceScheme
    reading
    (ClosedEquationalLawReading.ofSemanticCore_valid referenceRaw
      referenceScheme G B).witness_compatible i hi
    ambientTopAffineOpen]
  rw [lawWitnessIdealSheaf_ofGlobalSections referenceRaw referenceScheme
    reading
    (ClosedEquationalLawReading.ofSemanticCore_valid referenceRaw
      referenceScheme G B).witness_compatible i hi
    (semanticCoreGlobalEquation referenceRaw referenceScheme G B i)]
  · rw [Scheme.IdealSheafData.ofIdealTop_ideal]
    simp [ambientTopAffineOpen]
  · simpa only [reading] using
      ClosedEquationalLawReading.ofSemanticCore_witness referenceRaw
        referenceScheme G B i hi

private theorem reference_generated_top_eq_span
    (G : ArchitecturalEquationSystem referenceSite.contextPreorder)
    (B : SemanticLawEquationSchemeBridge referenceRaw G)
    (i₀ : G.Index) (hi₀ : G.Required i₀)
    (hunique : ∀ i, G.Required i → i = i₀) :
    (lawGeneratedIdealSheaf referenceRaw referenceScheme
      (ClosedEquationalLawReading.ofSemanticCore referenceRaw
        referenceScheme G B)
      (ClosedEquationalLawReading.ofSemanticCore_valid referenceRaw
        referenceScheme G B)
      (ClosedEquationalLawReading.ofSemanticCore_requiredClosed referenceRaw
        referenceScheme G B)).ideal ambientTopAffineOpen =
      Ideal.span (Set.range (semanticCoreGlobalEquation referenceRaw
        referenceScheme G B i₀)) := by
  let reading := ClosedEquationalLawReading.ofSemanticCore referenceRaw
    referenceScheme G B
  let valid := ClosedEquationalLawReading.ofSemanticCore_valid referenceRaw
    referenceScheme G B
  let required :=
    ClosedEquationalLawReading.ofSemanticCore_requiredClosed referenceRaw
      referenceScheme G B
  rw [lawGeneratedIdealSheaf_ideal]
  apply le_antisymm
  · refine iSup_le fun i => ?_
    have hi : i.1 = i₀ := hunique i.1 i.2.1
    subst i₀
    exact (reference_local_top_eq_span G B i.1 _).le
  · let idx : {i : G.Index //
        G.Required i ∧
          reading.selected ambientTopAffineOpen i} :=
      ⟨i₀, hi₀,
        ClosedEquationalLawReading.ofSemanticCore_selected referenceRaw
          referenceScheme G B ambientTopAffineOpen i₀⟩
    have h := le_iSup (fun i :
      {i : G.Index //
          G.Required i ∧
            reading.selected ambientTopAffineOpen i} =>
        localLawWitnessIdeal referenceRaw referenceScheme
          (reading.witness i.1 (required.closed i.1 i.2.1))
          ambientTopAffineOpen) idx
    rw [reference_local_top_eq_span G B i₀] at h
    exact h

private theorem weak_generated_top_eq_span :
    (lawGeneratedIdealSheaf referenceRaw referenceScheme
      weakReading weakReading_valid weakReading_requiredClosed).ideal
        ambientTopAffineOpen =
      Ideal.span (Set.range (semanticCoreGlobalEquation referenceRaw
        referenceScheme weakLawEquationCore weakSchemeBridge PUnit.unit)) := by
  simpa only [weakReading, weakReading_valid, weakReading_requiredClosed] using
    reference_generated_top_eq_span weakLawEquationCore weakSchemeBridge
      PUnit.unit
      (by
        change referenceSite.equationSystem.Required PUnit.unit
        exact referenceSite_equation_required PUnit.unit)
      (by intro i _hi; cases i; rfl)

private theorem strong_generated_top_eq_span :
    (lawGeneratedIdealSheaf referenceRaw referenceScheme
      strongReading strongReading_valid strongReading_requiredClosed).ideal
        ambientTopAffineOpen =
      Ideal.span (Set.range (semanticCoreGlobalEquation referenceRaw
        referenceScheme strongLawEquationCore strongSchemeBridge PUnit.unit)) := by
  simpa only [strongReading, strongReading_valid, strongReading_requiredClosed] using
    reference_generated_top_eq_span strongLawEquationCore strongSchemeBridge
      PUnit.unit
      (by
        change referenceSite.equationSystem.Required PUnit.unit
        exact referenceSite_equation_required PUnit.unit)
      (by intro i _hi; cases i; rfl)

private theorem rigid_generated_top_eq_span :
    (lawGeneratedIdealSheaf referenceRaw referenceScheme
      rigidReading rigidReading_valid rigidReading_requiredClosed).ideal
        ambientTopAffineOpen =
      Ideal.span (Set.range (semanticCoreGlobalEquation referenceRaw
        referenceScheme rigidLawEquationCore rigidSchemeBridge PUnit.unit)) := by
  simpa only [rigidReading, rigidReading_valid, rigidReading_requiredClosed] using
    reference_generated_top_eq_span rigidLawEquationCore rigidSchemeBridge
      PUnit.unit
      (by
        change referenceSite.equationSystem.Required PUnit.unit
        exact referenceSite_equation_required PUnit.unit)
      (by intro i _hi; cases i; rfl)

private theorem reference_generated_eq_witness
    (G : ArchitecturalEquationSystem referenceSite.contextPreorder)
    (B : SemanticLawEquationSchemeBridge referenceRaw G)
    (i₀ : G.Index) (hi₀ : G.Required i₀)
    (hunique : ∀ i, G.Required i → i = i₀) :
    lawGeneratedIdealSheaf referenceRaw referenceScheme
        (ClosedEquationalLawReading.ofSemanticCore referenceRaw
          referenceScheme G B)
        (ClosedEquationalLawReading.ofSemanticCore_valid referenceRaw
          referenceScheme G B)
        (ClosedEquationalLawReading.ofSemanticCore_requiredClosed referenceRaw
          referenceScheme G B) =
      lawWitnessIdealSheaf referenceRaw referenceScheme
        (ClosedEquationalLawReading.ofSemanticCore referenceRaw
          referenceScheme G B)
        (ClosedEquationalLawReading.ofSemanticCore_witnessCompatible referenceRaw
          referenceScheme G B)
        i₀ (show i₀ ∈ (Set.univ : Set G.Index) from Set.mem_univ i₀) := by
  letI : IsAffine referenceScheme.underlying := by
    rw [referenceScheme_underlying, ambientScheme_eq]
    infer_instance
  apply Scheme.IdealSheafData.ext_of_isAffine
  let hi : i₀ ∈ (Set.univ : Set G.Index) := Set.mem_univ i₀
  have hw := lawWitnessIdealSheaf_ofGlobalSections referenceRaw
    referenceScheme
    (ClosedEquationalLawReading.ofSemanticCore referenceRaw
      referenceScheme G B)
    (ClosedEquationalLawReading.ofSemanticCore_witnessCompatible referenceRaw
      referenceScheme G B)
    i₀ hi
    (semanticCoreGlobalEquation referenceRaw referenceScheme G B i₀)
    (ClosedEquationalLawReading.ofSemanticCore_witness referenceRaw
      referenceScheme G B i₀ hi)
  rw [hw, Scheme.IdealSheafData.ofIdealTop_ideal]
  simpa [ambientTopAffineOpen] using
    reference_generated_top_eq_span G B i₀ hi₀ hunique

private theorem reference_generated_comap_chart
    (G : ArchitecturalEquationSystem referenceSite.contextPreorder)
    (B : SemanticLawEquationSchemeBridge referenceRaw G)
    (hB : IsSemanticLawEquationSchemeBridge referenceRaw G B)
    (i₀ : G.Index) (hi₀ : G.Required i₀)
    (hunique : ∀ i, G.Required i → i = i₀)
    (j : referenceScheme.atlas.Index) :
    (lawGeneratedIdealSheaf referenceRaw referenceScheme
      (ClosedEquationalLawReading.ofSemanticCore referenceRaw
        referenceScheme G B)
      (ClosedEquationalLawReading.ofSemanticCore_valid referenceRaw
        referenceScheme G B)
      (ClosedEquationalLawReading.ofSemanticCore_requiredClosed referenceRaw
        referenceScheme G B)).comap
        (referenceScheme.atlas.chart j).map =
      Scheme.IdealSheafData.ofIdealTop
        (X := (referenceScheme.atlas.chart j).domain)
        (Ideal.map
          (AlgebraicGeometry.Scheme.ΓSpecIso
            (SheafifiedSectionRing referenceRaw
              (referenceScheme.atlas.chart j).context)).inv.hom
          (Ideal.map
            (B.toSheafifiedSection
              (referenceScheme.atlas.chart j).context)
            (G.witnessIdeal
              (referenceScheme.atlas.chart j).context i₀))) := by
  rw [reference_generated_eq_witness G B i₀ hi₀ hunique]
  exact (semanticCoreIdealSheaf_realized referenceRaw referenceScheme
    G B hB).2 j i₀

private theorem referenceIdeal_left_raw
    (G : ArchitecturalEquationSystem referenceSite.contextPreorder)
    (B : SemanticLawEquationSchemeBridge referenceRaw G)
    (hB : IsSemanticLawEquationSchemeBridge referenceRaw G B)
    (i₀ : G.Index) (hi₀ : G.Required i₀)
    (hunique : ∀ i, G.Required i → i = i₀) :
    Ideal.map leftChartGlobalSectionsIso.hom.hom
        (((lawGeneratedIdealSheaf referenceRaw referenceScheme
          (ClosedEquationalLawReading.ofSemanticCore referenceRaw
            referenceScheme G B)
          (ClosedEquationalLawReading.ofSemanticCore_valid referenceRaw
            referenceScheme G B)
          (ClosedEquationalLawReading.ofSemanticCore_requiredClosed referenceRaw
            referenceScheme G B)).comap leftChart.map).ideal
          ⟨⊤, @isAffineOpen_top leftChart.domain
            leftChart.domain_isAffine⟩) =
      Ideal.map (leftRawAlgebraIso.hom.hom.comp
        (B.toRawPresentation leftContext).toRingHom)
        (G.witnessIdeal leftContext i₀) := by
  letI := (hB.presentation_stable leftContext).canonical_isIso
  have hreal := congrArg
    (fun I : leftChart.domain.IdealSheafData =>
      I.ideal ⟨⊤, @isAffineOpen_top leftChart.domain
        leftChart.domain_isAffine⟩)
    (reference_generated_comap_chart G B hB i₀ hi₀ hunique leftIndex)
  change
    (((lawGeneratedIdealSheaf referenceRaw referenceScheme
      (ClosedEquationalLawReading.ofSemanticCore referenceRaw
        referenceScheme G B)
      (ClosedEquationalLawReading.ofSemanticCore_valid referenceRaw
        referenceScheme G B)
      (ClosedEquationalLawReading.ofSemanticCore_requiredClosed referenceRaw
        referenceScheme G B)).comap leftChart.map).ideal
      ⟨⊤, @isAffineOpen_top leftChart.domain leftChart.domain_isAffine⟩) =
    (Scheme.IdealSheafData.ofIdealTop
      (X := leftChart.domain)
      (Ideal.map
        (AlgebraicGeometry.Scheme.ΓSpecIso
          (SheafifiedSectionRing referenceRaw leftContext)).inv.hom
        (Ideal.map (B.toSheafifiedSection leftContext)
          (G.witnessIdeal leftContext i₀)))).ideal
      ⟨⊤, @isAffineOpen_top leftChart.domain leftChart.domain_isAffine⟩ at hreal
  change Ideal.map leftChartGlobalSectionsIso.hom.hom
      (((lawGeneratedIdealSheaf referenceRaw referenceScheme
        (ClosedEquationalLawReading.ofSemanticCore referenceRaw
          referenceScheme G B)
        (ClosedEquationalLawReading.ofSemanticCore_valid referenceRaw
          referenceScheme G B)
        (ClosedEquationalLawReading.ofSemanticCore_requiredClosed referenceRaw
          referenceScheme G B)).comap leftChart.map).ideal
        ⟨⊤, @isAffineOpen_top leftChart.domain
          leftChart.domain_isAffine⟩) = _
  rw [hreal, Scheme.IdealSheafData.ofIdealTop_ideal]
  simp [leftChartGlobalSectionsIso, leftSectionRingIso,
    Ideal.map_map, SemanticLawEquationSchemeBridge.toSheafifiedSection,
    sheafificationUnitAlgHom]
  congr 1
  ext x
  simp only [RingHom.comp_apply, Iso.inv_hom_id_apply]
  have hcancel := congrArg
    (fun q => q ((B.toRawPresentation leftContext) x))
    (IsIso.hom_inv_id
      (referenceRaw.toRingedSite.canonical.app (op leftContext)).right)
  apply congrArg leftRawAlgebraIso.hom.hom
  change (inv (referenceRaw.toRingedSite.canonical.app
      (op leftContext)).right)
      ((referenceRaw.toRingedSite.canonical.app (op leftContext)).right
        ((B.toRawPresentation leftContext) x)) =
    (B.toRawPresentation leftContext) x
  simpa only [CommRingCat.comp_apply, Category.id_comp] using hcancel

private theorem referenceIdeal_right_raw
    (G : ArchitecturalEquationSystem referenceSite.contextPreorder)
    (B : SemanticLawEquationSchemeBridge referenceRaw G)
    (hB : IsSemanticLawEquationSchemeBridge referenceRaw G B)
    (i₀ : G.Index) (hi₀ : G.Required i₀)
    (hunique : ∀ i, G.Required i → i = i₀) :
    Ideal.map rightChartGlobalSectionsIso.hom.hom
        (((lawGeneratedIdealSheaf referenceRaw referenceScheme
          (ClosedEquationalLawReading.ofSemanticCore referenceRaw
            referenceScheme G B)
          (ClosedEquationalLawReading.ofSemanticCore_valid referenceRaw
            referenceScheme G B)
          (ClosedEquationalLawReading.ofSemanticCore_requiredClosed referenceRaw
            referenceScheme G B)).comap rightChart.map).ideal
          ⟨⊤, @isAffineOpen_top rightChart.domain
            rightChart.domain_isAffine⟩) =
      Ideal.map (rightRawAlgebraIso.hom.hom.comp
        (B.toRawPresentation rightContext).toRingHom)
        (G.witnessIdeal rightContext i₀) := by
  letI := (hB.presentation_stable rightContext).canonical_isIso
  have hreal := congrArg
    (fun I : rightChart.domain.IdealSheafData =>
      I.ideal ⟨⊤, @isAffineOpen_top rightChart.domain
        rightChart.domain_isAffine⟩)
    (reference_generated_comap_chart G B hB i₀ hi₀ hunique rightIndex)
  change
    (((lawGeneratedIdealSheaf referenceRaw referenceScheme
      (ClosedEquationalLawReading.ofSemanticCore referenceRaw
        referenceScheme G B)
      (ClosedEquationalLawReading.ofSemanticCore_valid referenceRaw
        referenceScheme G B)
      (ClosedEquationalLawReading.ofSemanticCore_requiredClosed referenceRaw
        referenceScheme G B)).comap rightChart.map).ideal
      ⟨⊤, @isAffineOpen_top rightChart.domain rightChart.domain_isAffine⟩) =
    (Scheme.IdealSheafData.ofIdealTop
      (X := rightChart.domain)
      (Ideal.map
        (AlgebraicGeometry.Scheme.ΓSpecIso
          (SheafifiedSectionRing referenceRaw rightContext)).inv.hom
        (Ideal.map (B.toSheafifiedSection rightContext)
          (G.witnessIdeal rightContext i₀)))).ideal
      ⟨⊤, @isAffineOpen_top rightChart.domain rightChart.domain_isAffine⟩ at hreal
  change Ideal.map rightChartGlobalSectionsIso.hom.hom
      (((lawGeneratedIdealSheaf referenceRaw referenceScheme
        (ClosedEquationalLawReading.ofSemanticCore referenceRaw
          referenceScheme G B)
        (ClosedEquationalLawReading.ofSemanticCore_valid referenceRaw
          referenceScheme G B)
        (ClosedEquationalLawReading.ofSemanticCore_requiredClosed referenceRaw
          referenceScheme G B)).comap rightChart.map).ideal
        ⟨⊤, @isAffineOpen_top rightChart.domain
          rightChart.domain_isAffine⟩) = _
  rw [hreal, Scheme.IdealSheafData.ofIdealTop_ideal]
  simp [rightChartGlobalSectionsIso, rightSectionRingIso,
    Ideal.map_map, SemanticLawEquationSchemeBridge.toSheafifiedSection,
    sheafificationUnitAlgHom]
  congr 1
  ext x
  simp only [RingHom.comp_apply, Iso.inv_hom_id_apply]
  have hcancel := congrArg
    (fun q => q ((B.toRawPresentation rightContext) x))
    (IsIso.hom_inv_id
      (referenceRaw.toRingedSite.canonical.app (op rightContext)).right)
  apply congrArg rightRawAlgebraIso.hom.hom
  change (inv (referenceRaw.toRingedSite.canonical.app
      (op rightContext)).right)
      ((referenceRaw.toRingedSite.canonical.app (op rightContext)).right
        ((B.toRawPresentation rightContext) x)) =
    (B.toRawPresentation rightContext) x
  simpa only [CommRingCat.comp_apply, Category.id_comp] using hcancel

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
theorem weakIdeal_left_eq :
    Ideal.map leftChartGlobalSectionsIso.hom.hom
        ((weakIdealSheaf.comap leftChart.map).ideal
          ⟨⊤, @isAffineOpen_top leftChart.domain
            leftChart.domain_isAffine⟩) =
      weakLeftIdeal := by
  have hraw := referenceIdeal_left_raw weakLawEquationCore
    weakSchemeBridge weakSchemeBridge_valid PUnit.unit
      (by
        change referenceSite.equationSystem.Required PUnit.unit
        exact referenceSite_equation_required PUnit.unit)
      (by intro i _hi; cases i; rfl)
  have hsource :
      Ideal.map leftChartGlobalSectionsIso.hom.hom
          ((weakIdealSheaf.comap leftChart.map).ideal
            ⟨⊤, @isAffineOpen_top leftChart.domain
              leftChart.domain_isAffine⟩) =
        Ideal.map leftRawAlgebraIso.hom.hom
          (weakLawEquationCore.witnessIdeal leftContext PUnit.unit) := by
    simpa only [weakReading, weakReading_valid, weakReading_requiredClosed,
      weakSchemeBridge, RingHom.comp_id] using hraw
  rw [hsource, ArchitecturalEquationSystem.witnessIdeal,
    Ideal.map_span]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro y ⟨_, ⟨a, rfl⟩, rfl⟩
    change leftRawAlgebraIso.hom
      (weakLawEquationCore.violationCoordinate leftContext PUnit.unit a) ∈
        weakLeftIdeal
    rw [weakViolationWitness_eq]
    split
    · change leftRawAlgebraIso.hom
          (rawCoordinate leftContext * (rawCoordinate leftContext - 1)) ∈
        weakLeftIdeal
      rw [map_mul, map_sub, map_one, leftRawAlgebraIso_coordinate]
      rw [← map_one (algebraMap AmbientRing
          (Localization.Away leftGenerator)), ← map_sub, ← map_mul]
      exact Ideal.subset_span (Set.mem_singleton _)
    · exact map_zero leftRawAlgebraIso.hom.hom ▸ Ideal.zero_mem _
  · rw [weakLeftIdeal]
    apply Ideal.span_le.mpr
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    apply Ideal.subset_span
    refine ⟨weakLawEquationCore.violationCoordinate leftContext PUnit.unit
      AAT.AG.FiniteModel.FiniteAtom.componentA, ⟨?_, ?_⟩⟩
    · exact ⟨AAT.AG.FiniteModel.FiniteAtom.componentA, rfl⟩
    · rw [weakViolationWitness_eq, if_pos rfl]
      change leftRawAlgebraIso.hom
          (rawCoordinate leftContext * (rawCoordinate leftContext - 1)) = _
      rw [map_mul, map_sub, map_one, leftRawAlgebraIso_coordinate]
      rw [← map_one (algebraMap AmbientRing
          (Localization.Away leftGenerator)), ← map_sub, ← map_mul]

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
theorem weakIdeal_right_eq :
    Ideal.map rightChartGlobalSectionsIso.hom.hom
        ((weakIdealSheaf.comap rightChart.map).ideal
          ⟨⊤, @isAffineOpen_top rightChart.domain
            rightChart.domain_isAffine⟩) =
      weakRightIdeal := by
  have hraw := referenceIdeal_right_raw weakLawEquationCore
    weakSchemeBridge weakSchemeBridge_valid PUnit.unit
      (by
        change referenceSite.equationSystem.Required PUnit.unit
        exact referenceSite_equation_required PUnit.unit)
      (by intro i _hi; cases i; rfl)
  have hsource :
      Ideal.map rightChartGlobalSectionsIso.hom.hom
          ((weakIdealSheaf.comap rightChart.map).ideal
            ⟨⊤, @isAffineOpen_top rightChart.domain
              rightChart.domain_isAffine⟩) =
        Ideal.map rightRawAlgebraIso.hom.hom
          (weakLawEquationCore.witnessIdeal rightContext PUnit.unit) := by
    simpa only [weakReading, weakReading_valid, weakReading_requiredClosed,
      weakSchemeBridge, RingHom.comp_id] using hraw
  rw [hsource, ArchitecturalEquationSystem.witnessIdeal,
    Ideal.map_span]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro y ⟨_, ⟨a, rfl⟩, rfl⟩
    change rightRawAlgebraIso.hom
      (weakLawEquationCore.violationCoordinate rightContext PUnit.unit a) ∈
        weakRightIdeal
    rw [weakViolationWitness_eq]
    split
    · change rightRawAlgebraIso.hom
          (rawCoordinate rightContext * (rawCoordinate rightContext - 1)) ∈
        weakRightIdeal
      rw [map_mul, map_sub, map_one, rightRawAlgebraIso_coordinate]
      rw [← map_one (algebraMap AmbientRing
          (Localization.Away rightGenerator)), ← map_sub, ← map_mul]
      exact Ideal.subset_span (Set.mem_singleton _)
    · exact map_zero rightRawAlgebraIso.hom.hom ▸ Ideal.zero_mem _
  · rw [weakRightIdeal]
    apply Ideal.span_le.mpr
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    apply Ideal.subset_span
    refine ⟨weakLawEquationCore.violationCoordinate rightContext PUnit.unit
      AAT.AG.FiniteModel.FiniteAtom.componentA, ⟨?_, ?_⟩⟩
    · exact ⟨AAT.AG.FiniteModel.FiniteAtom.componentA, rfl⟩
    · rw [weakViolationWitness_eq, if_pos rfl]
      change rightRawAlgebraIso.hom
          (rawCoordinate rightContext * (rawCoordinate rightContext - 1)) = _
      rw [map_mul, map_sub, map_one, rightRawAlgebraIso_coordinate]
      rw [← map_one (algebraMap AmbientRing
          (Localization.Away rightGenerator)), ← map_sub, ← map_mul]

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
theorem strongIdeal_left_eq :
    Ideal.map leftChartGlobalSectionsIso.hom.hom
        ((strongIdealSheaf.comap leftChart.map).ideal
          ⟨⊤, @isAffineOpen_top leftChart.domain
            leftChart.domain_isAffine⟩) =
      strongLeftIdeal := by
  have hraw := referenceIdeal_left_raw strongLawEquationCore
    strongSchemeBridge strongSchemeBridge_valid PUnit.unit
      (by
        change referenceSite.equationSystem.Required PUnit.unit
        exact referenceSite_equation_required PUnit.unit)
      (by intro i _hi; cases i; rfl)
  have hsource :
      Ideal.map leftChartGlobalSectionsIso.hom.hom
          ((strongIdealSheaf.comap leftChart.map).ideal
            ⟨⊤, @isAffineOpen_top leftChart.domain
              leftChart.domain_isAffine⟩) =
        Ideal.map leftRawAlgebraIso.hom.hom
          (strongLawEquationCore.witnessIdeal leftContext PUnit.unit) := by
    simpa only [strongReading, strongReading_valid, strongReading_requiredClosed,
      strongSchemeBridge, RingHom.comp_id] using hraw
  rw [hsource, ArchitecturalEquationSystem.witnessIdeal,
    Ideal.map_span]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro y ⟨_, ⟨a, rfl⟩, rfl⟩
    change leftRawAlgebraIso.hom
      (strongLawEquationCore.violationCoordinate leftContext PUnit.unit a) ∈
        strongLeftIdeal
    rw [strongViolationWitness_eq]
    split
    · change leftRawAlgebraIso.hom
          (rawCoordinate leftContext * (rawCoordinate leftContext - 1)) ∈
        strongLeftIdeal
      rw [map_mul, map_sub, map_one, leftRawAlgebraIso_coordinate]
      exact strongLeftIdeal.mul_mem_right _
        (Ideal.subset_span (Set.mem_singleton _))
    · split
      · rw [leftRawAlgebraIso_coordinate]
        exact Ideal.subset_span (Set.mem_singleton _)
      · exact map_zero leftRawAlgebraIso.hom.hom ▸ Ideal.zero_mem _
  · rw [strongLeftIdeal]
    apply Ideal.span_le.mpr
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    apply Ideal.subset_span
    refine ⟨strongLawEquationCore.violationCoordinate leftContext PUnit.unit
      AAT.AG.FiniteModel.FiniteAtom.componentB, ⟨?_, ?_⟩⟩
    · exact ⟨AAT.AG.FiniteModel.FiniteAtom.componentB, rfl⟩
    · rw [strongViolationWitness_eq, if_neg (by simp), if_pos rfl]
      change leftRawAlgebraIso.hom (rawCoordinate leftContext) = _
      rw [leftRawAlgebraIso_coordinate]

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
theorem strongIdeal_right_eq :
    Ideal.map rightChartGlobalSectionsIso.hom.hom
        ((strongIdealSheaf.comap rightChart.map).ideal
          ⟨⊤, @isAffineOpen_top rightChart.domain
            rightChart.domain_isAffine⟩) =
      strongRightIdeal := by
  have hraw := referenceIdeal_right_raw strongLawEquationCore
    strongSchemeBridge strongSchemeBridge_valid PUnit.unit
      (by
        change referenceSite.equationSystem.Required PUnit.unit
        exact referenceSite_equation_required PUnit.unit)
      (by intro i _hi; cases i; rfl)
  have hsource :
      Ideal.map rightChartGlobalSectionsIso.hom.hom
          ((strongIdealSheaf.comap rightChart.map).ideal
            ⟨⊤, @isAffineOpen_top rightChart.domain
              rightChart.domain_isAffine⟩) =
        Ideal.map rightRawAlgebraIso.hom.hom
          (strongLawEquationCore.witnessIdeal rightContext PUnit.unit) := by
    simpa only [strongReading, strongReading_valid, strongReading_requiredClosed,
      strongSchemeBridge, RingHom.comp_id] using hraw
  rw [hsource, ArchitecturalEquationSystem.witnessIdeal,
    Ideal.map_span]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro y ⟨_, ⟨a, rfl⟩, rfl⟩
    change rightRawAlgebraIso.hom
      (strongLawEquationCore.violationCoordinate rightContext PUnit.unit a) ∈
        strongRightIdeal
    rw [strongViolationWitness_eq]
    split
    · change rightRawAlgebraIso.hom
          (rawCoordinate rightContext * (rawCoordinate rightContext - 1)) ∈
        strongRightIdeal
      rw [map_mul, map_sub, map_one, rightRawAlgebraIso_coordinate]
      exact strongRightIdeal.mul_mem_right _
        (Ideal.subset_span (Set.mem_singleton _))
    · split
      · rw [rightRawAlgebraIso_coordinate]
        exact Ideal.subset_span (Set.mem_singleton _)
      · exact map_zero rightRawAlgebraIso.hom.hom ▸ Ideal.zero_mem _
  · rw [strongRightIdeal]
    apply Ideal.span_le.mpr
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    apply Ideal.subset_span
    refine ⟨strongLawEquationCore.violationCoordinate rightContext PUnit.unit
      AAT.AG.FiniteModel.FiniteAtom.componentB, ⟨?_, ?_⟩⟩
    · exact ⟨AAT.AG.FiniteModel.FiniteAtom.componentB, rfl⟩
    · rw [strongViolationWitness_eq, if_neg (by simp), if_pos rfl]
      change rightRawAlgebraIso.hom (rawCoordinate rightContext) = _
      rw [rightRawAlgebraIso_coordinate]

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
theorem weakIdeal_top_eq :
    Ideal.map ambientGlobalSectionsIso.hom.hom
        (weakIdealSheaf.ideal ambientTopAffineOpen) =
      weakAmbientIdeal := by
  change Ideal.map ambientGlobalSectionsIso.hom.hom
      ((lawGeneratedIdealSheaf referenceRaw referenceScheme
        weakReading weakReading_valid weakReading_requiredClosed).ideal
        ambientTopAffineOpen) = weakAmbientIdeal
  rw [weak_generated_top_eq_span,
    Ideal.map_span]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro y ⟨_, ⟨a, rfl⟩, rfl⟩
    change ambientGlobalSectionsIso.hom
      (semanticCoreGlobalEquation referenceRaw referenceScheme
        weakLawEquationCore weakSchemeBridge PUnit.unit a) ∈ weakAmbientIdeal
    rw [weakGlobalEquation_eq]
    split
    · exact Ideal.subset_span (Set.mem_singleton _)
    · exact Ideal.zero_mem _
  · rw [weakAmbientIdeal]
    apply Ideal.span_le.mpr
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    apply Ideal.subset_span
    refine ⟨semanticCoreGlobalEquation referenceRaw referenceScheme
      weakLawEquationCore weakSchemeBridge PUnit.unit
      AAT.AG.FiniteModel.FiniteAtom.componentA, ⟨?_, ?_⟩⟩
    · exact ⟨AAT.AG.FiniteModel.FiniteAtom.componentA, rfl⟩
    · simpa using weakGlobalEquation_eq
        AAT.AG.FiniteModel.FiniteAtom.componentA

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
theorem strongIdeal_top_eq :
    Ideal.map ambientGlobalSectionsIso.hom.hom
        (strongIdealSheaf.ideal ambientTopAffineOpen) =
      strongAmbientIdeal := by
  change Ideal.map ambientGlobalSectionsIso.hom.hom
      ((lawGeneratedIdealSheaf referenceRaw referenceScheme
        strongReading strongReading_valid strongReading_requiredClosed).ideal
        ambientTopAffineOpen) = strongAmbientIdeal
  rw [strong_generated_top_eq_span,
    Ideal.map_span]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro y ⟨_, ⟨a, rfl⟩, rfl⟩
    change ambientGlobalSectionsIso.hom
      (semanticCoreGlobalEquation referenceRaw referenceScheme
        strongLawEquationCore strongSchemeBridge PUnit.unit a) ∈ strongAmbientIdeal
    rw [strongGlobalEquation_eq]
    split
    · exact (Ideal.span {coordinate}).mul_mem_right (coordinate - 1)
        (Ideal.subset_span (Set.mem_singleton coordinate))
    · split
      · exact Ideal.subset_span (Set.mem_singleton coordinate)
      · exact Ideal.zero_mem _
  · rw [strongAmbientIdeal]
    apply Ideal.span_le.mpr
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    apply Ideal.subset_span
    refine ⟨semanticCoreGlobalEquation referenceRaw referenceScheme
      strongLawEquationCore strongSchemeBridge PUnit.unit
      AAT.AG.FiniteModel.FiniteAtom.componentB, ⟨?_, ?_⟩⟩
    · exact ⟨AAT.AG.FiniteModel.FiniteAtom.componentB, rfl⟩
    · simpa using strongGlobalEquation_eq
        AAT.AG.FiniteModel.FiniteAtom.componentB

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
theorem rigidIdeal_top_eq :
    Ideal.map ambientGlobalSectionsIso.hom.hom
        (rigidIdealSheaf.ideal ambientTopAffineOpen) =
      rigidAmbientIdeal := by
  change Ideal.map ambientGlobalSectionsIso.hom.hom
      ((lawGeneratedIdealSheaf referenceRaw referenceScheme
        rigidReading rigidReading_valid rigidReading_requiredClosed).ideal
        ambientTopAffineOpen) = rigidAmbientIdeal
  rw [rigid_generated_top_eq_span,
    Ideal.map_span]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro y ⟨_, ⟨a, rfl⟩, rfl⟩
    change ambientGlobalSectionsIso.hom
      (semanticCoreGlobalEquation referenceRaw referenceScheme
        rigidLawEquationCore rigidSchemeBridge PUnit.unit a) ∈ rigidAmbientIdeal
    rw [rigidGlobalEquation_eq]
    split
    · exact (Ideal.span {coordinate, MvPolynomial.C 2}).mul_mem_right
        (coordinate - 1)
        (Ideal.subset_span (Set.mem_insert coordinate _))
    · split
      · exact Ideal.subset_span (Set.mem_insert coordinate _)
      · split
        · exact Ideal.subset_span
            (Set.mem_insert_of_mem coordinate (Set.mem_singleton _))
        · exact Ideal.zero_mem _
  · rw [rigidAmbientIdeal]
    apply Ideal.span_le.mpr
    intro y hy
    rcases (Set.mem_insert_iff.mp hy) with rfl | hy
    · apply Ideal.subset_span
      refine ⟨semanticCoreGlobalEquation referenceRaw referenceScheme
        rigidLawEquationCore rigidSchemeBridge PUnit.unit
        AAT.AG.FiniteModel.FiniteAtom.componentB, ⟨?_, ?_⟩⟩
      · exact ⟨AAT.AG.FiniteModel.FiniteAtom.componentB, rfl⟩
      · simpa using rigidGlobalEquation_eq
          AAT.AG.FiniteModel.FiniteAtom.componentB
    · rw [Set.mem_singleton_iff] at hy
      subst y
      apply Ideal.subset_span
      refine ⟨semanticCoreGlobalEquation referenceRaw referenceScheme
        rigidLawEquationCore rigidSchemeBridge PUnit.unit
        AAT.AG.FiniteModel.FiniteAtom.componentC, ⟨?_, ?_⟩⟩
      · exact ⟨AAT.AG.FiniteModel.FiniteAtom.componentC, rfl⟩
      · simpa using rigidGlobalEquation_eq
          AAT.AG.FiniteModel.FiniteAtom.componentC



/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
def evaluationRingHom (n : Int) :
    AmbientRing →+* Int :=
  MvPolynomial.eval₂Hom (RingHom.id Int) (fun _ => n)

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
@[simp] theorem evaluationRingHom_eq (n : Int) :
    evaluationRingHom n =
      MvPolynomial.eval₂Hom (RingHom.id Int) (fun _ => n) :=
  rfl

/-- Evaluation at `x = 0` after reducing coefficients modulo `2`. -/
def siteEquationModTwoRingHom : AmbientRing →+* ZMod 2 :=
  MvPolynomial.eval₂Hom (Int.castRingHom (ZMod 2)) (fun _ => 0)

/--
The reference point on which the site-selected constant coordinate `2`
vanishes.
-/
noncomputable def siteEquationModTwoPoint :
    AlgebraicGeometry.Spec (CommRingCat.of (ZMod 2)) ⟶
      referenceScheme.underlying :=
  AlgebraicGeometry.Scheme.Spec.map
    (CommRingCat.ofHom siteEquationModTwoRingHom).op

private theorem siteEquationModTwoPoint_normalized_appTop :
    siteEquationModTwoPoint.appTop ≫
        (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of (ZMod 2))).hom =
      ambientGlobalSectionsIso.hom ≫
        CommRingCat.ofHom siteEquationModTwoRingHom := by
  simpa only [siteEquationModTwoPoint, referenceScheme_underlying,
    ambientScheme_eq, ambientGlobalSectionsIso,
    AlgebraicGeometry.Scheme.Spec_map, Quiver.Hom.unop_op] using
      AlgebraicGeometry.Scheme.ΓSpecIso_naturality
        (CommRingCat.ofHom siteEquationModTwoRingHom)

private theorem siteEquationModTwoPoint_normalized_apply
    (x : Γ(referenceScheme.underlying, ⊤)) :
    (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of (ZMod 2))).hom
        (siteEquationModTwoPoint.appTop x) =
      siteEquationModTwoRingHom (ambientGlobalSectionsIso.hom x) := by
  simpa only [CommRingCat.comp_apply] using congrArg
    (fun q => q x) siteEquationModTwoPoint_normalized_appTop

/-- The acyclic fixture has zero actual residual in every context and Atom. -/
theorem referenceSite_acyclic_residual_zero
    (W : referenceSite.category)
    (i : referenceSite.equationSystem.Index)
    (a : AAT.AG.FiniteModel.carrier.Atom) :
    referenceSite.equationSystem.equationResidual W
      AAT.AG.FiniteModel.acyclicObject i a = 0 := by
  cases i
  simp [Site.SelectedGeometryReading.toAATSite,
    referenceCorePackage, AAT.AG.FiniteModel.corePackageFor,
    AATCorePackage.generate, AATCorePackage.equationSystem,
    AATCorePackage.algebra, ObjectAlgebra.equationSystem,
    AAT.AG.FiniteModel.coreReadingFor,
    AAT.AG.FiniteModel.equationReading,
    AAT.AG.FiniteModel.equationSystem,
    AAT.AG.FiniteModel.noCycleResidual,
    AAT.AG.FiniteModel.hasDependencyCycle,
    AAT.AG.FiniteModel.acyclicObject,
    AAT.AG.FiniteModel.acyclicConfiguration]

/-- The mod-two point kills every symbolic-residual equalizer relation. -/
theorem siteEquationModTwoPoint_realizationRelations
    (g : EquationObservableRealization.GeneratorIndex
      referenceSite.equationSystem) :
    siteEquationModTwoPoint.appTop
      (referenceEquationObservableRealization.realizationRelation
        AAT.AG.FiniteModel.acyclicObject g) = 0 := by
  rcases g with ⟨W, i, a⟩
  apply (ConcreteCategory.bijective_of_isIso
    (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of (ZMod 2))).hom).1
  rw [map_zero, siteEquationModTwoPoint_normalized_apply]
  change siteEquationModTwoRingHom
    (ambientGlobalSectionsIso.hom
      (referenceSiteGlobalEquation W i a -
        referenceSiteResidualSection
          AAT.AG.FiniteModel.acyclicObject W i a)) = 0
  rw [map_sub, referenceSiteGlobalEquation_image,
    referenceSiteResidualSection_image,
    referenceSite_violationCoordinate,
    referenceSite_acyclic_residual_zero, map_zero, sub_zero]
  change siteEquationModTwoRingHom (2 : AmbientRing) = 0
  rw [map_ofNat]
  decide

/-- The mod-two point factors through the generated symbolic-residual equalizer. -/
theorem siteEquationModTwoPoint_realizes :
    Nonempty
      (referenceEquationObservableRealization.FactorsThroughRealization
        AAT.AG.FiniteModel.acyclicObject siteEquationModTwoPoint) := by
  apply
    (referenceEquationObservableRealization.realizationIdeal_iff_nonempty_factorsThrough
        AAT.AG.FiniteModel.acyclicObject siteEquationModTwoPoint).mp
  apply
    (referenceEquationObservableRealization.realizationRelationsVanishAlong_iff_ideal
        AAT.AG.FiniteModel.acyclicObject siteEquationModTwoPoint).mp
  exact siteEquationModTwoPoint_realizationRelations

/-- The mod-two point as a point of the generated realization scheme. -/
noncomputable def siteEquationModTwoRealizationPoint :
    AlgebraicGeometry.Spec (CommRingCat.of (ZMod 2)) ⟶
      referenceEquationObservableRealization.realizationScheme
        AAT.AG.FiniteModel.acyclicObject :=
  (Classical.choice siteEquationModTwoPoint_realizes).1

/-- The generated realization point maps to the original mod-two point. -/
@[reassoc] theorem siteEquationModTwoRealizationPoint_immersion :
    siteEquationModTwoRealizationPoint ≫
        referenceEquationObservableRealization.realizationImmersion
          AAT.AG.FiniteModel.acyclicObject =
      siteEquationModTwoPoint :=
  (Classical.choice siteEquationModTwoPoint_realizes).2

/-- Residual representability fires on the nontrivial mod-two realization. -/
theorem siteEquationModTwoPoint_residualRepresentable
    (W : referenceSite.category)
    (i : referenceSite.equationSystem.Index)
    (a : AAT.AG.FiniteModel.carrier.Atom) :
    (siteEquationModTwoRealizationPoint ≫
      referenceEquationObservableRealization.realizationImmersion
        AAT.AG.FiniteModel.acyclicObject).appTop
        (referenceEquationObservableRealization.violationSection W i a) =
      (siteEquationModTwoRealizationPoint ≫
        referenceEquationObservableRealization.realizationImmersion
          AAT.AG.FiniteModel.acyclicObject).appTop
        (referenceEquationObservableRealization.residualSection
          AAT.AG.FiniteModel.acyclicObject W i a) :=
  referenceEquationObservableRealization.residualRepresentable
    AAT.AG.FiniteModel.acyclicObject
      siteEquationModTwoRealizationPoint W i a

/-- The realization point satisfies every required actual residual equation. -/
theorem siteEquationModTwoPoint_equationLawful :
    referenceEquationObservableRealization.EquationLawfulAlong
      AAT.AG.FiniteModel.acyclicObject
      siteEquationModTwoRealizationPoint := by
  apply
    referenceEquationObservableRealization.equationLawfulAlong_of_equationLawful
        AAT.AG.FiniteModel.acyclicObject
        siteEquationModTwoRealizationPoint
  intro i _ W a
  exact referenceSite_acyclic_residual_zero W i a

/--
The mod-two realization point factors through the lawful closed subscheme
generated from the site-owned witness ideals.
-/
theorem siteEquationModTwoPoint_factors_generated :
    Nonempty
      (referenceEquationObservableRealization.FactorsThroughLawfulClosedSubscheme
          AAT.AG.FiniteModel.acyclicObject
          siteEquationModTwoRealizationPoint) := by
  have h :=
    Correspondence.siteEquationLawfulnessIdealFactorizationCorrespondence
      referenceEquationObservableRealization
      AAT.AG.FiniteModel.acyclicObject
      siteEquationModTwoRealizationPoint
  exact h.2.mp (h.1.mp siteEquationModTwoPoint_equationLawful)

/-- The ambient mod-two point satisfies the synthesis compatibility adapter. -/
theorem siteEquationModTwoPoint_legacySemantic :
    SemanticLawfulAlong referenceRaw referenceScheme
      referenceLegacySiteReading siteEquationModTwoPoint := by
  intro i _
  change ∀ a, siteEquationModTwoPoint.appTop
    (referenceSiteGlobalEquation baseContext i a) = 0
  intro a
  apply (ConcreteCategory.bijective_of_isIso
    (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of (ZMod 2))).hom).1
  rw [map_zero, siteEquationModTwoPoint_normalized_apply,
    referenceSiteGlobalEquation_image, referenceSite_violationCoordinate]
  change siteEquationModTwoRingHom (2 : AmbientRing) = 0
  rw [map_ofNat]
  decide

/--
The ambient mod-two point factors through the lawful closed subscheme owned
by the synthesis compatibility adapter.
-/
theorem siteEquationModTwoPoint_factors_legacy :
    Nonempty (FactorsThroughLawfulClosedSubscheme
      referenceRaw referenceScheme referenceLegacySiteReading
      referenceLegacySiteReading_valid
      referenceLegacySiteReading_requiredClosed
      siteEquationModTwoPoint) := by
  apply (idealLawfulAlong_iff_nonempty_factorsThrough
    referenceRaw referenceScheme referenceLegacySiteReading
    referenceLegacySiteReading_valid
    referenceLegacySiteReading_requiredClosed
    siteEquationModTwoPoint).mp
  apply (witnessVanishes_iff_idealLawfulAlong
    referenceRaw referenceScheme referenceLegacySiteReading
    referenceLegacySiteReading_valid
    referenceLegacySiteReading_requiredClosed
    siteEquationModTwoPoint).mp
  apply (semanticLawfulAlong_iff_witnessVanishes
    referenceRaw referenceScheme referenceLegacySiteReading
    referenceLegacySiteReading_valid
    referenceLegacySiteReading_requiredClosed
    referenceLegacySiteReading_requiredLawIdealExact
    siteEquationModTwoPoint).mp
  exact siteEquationModTwoPoint_legacySemantic

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
noncomputable def evaluationPoint (n : Int) :
    AlgebraicGeometry.Spec (CommRingCat.of Int) ⟶
      referenceScheme.underlying :=
  AlgebraicGeometry.Scheme.Spec.map
    (CommRingCat.ofHom (evaluationRingHom n)).op

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
@[simp] theorem evaluationPoint_eq (n : Int) :
    evaluationPoint n =
      AlgebraicGeometry.Scheme.Spec.map
        (CommRingCat.ofHom (evaluationRingHom n)).op :=
  rfl

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
noncomputable def zeroPoint :
    AlgebraicGeometry.Spec (CommRingCat.of Int) ⟶
      referenceScheme.underlying :=
  evaluationPoint 0

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
@[simp] theorem zeroPoint_eq :
    zeroPoint = evaluationPoint 0 :=
  rfl

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
noncomputable def onePoint :
    AlgebraicGeometry.Spec (CommRingCat.of Int) ⟶
      referenceScheme.underlying :=
  evaluationPoint 1

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
@[simp] theorem onePoint_eq :
    onePoint = evaluationPoint 1 :=
  rfl

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
noncomputable def twoPoint :
    AlgebraicGeometry.Spec (CommRingCat.of Int) ⟶
      referenceScheme.underlying :=
  evaluationPoint 2

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
@[simp] theorem twoPoint_eq :
    twoPoint = evaluationPoint 2 :=
  rfl

private theorem evaluationPoint_normalized_appTop (n : Int) :
    (evaluationPoint n).appTop ≫
        (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of Int)).hom =
      ambientGlobalSectionsIso.hom ≫
        CommRingCat.ofHom (evaluationRingHom n) := by
  simpa only [evaluationPoint, referenceScheme_underlying, ambientScheme_eq,
    ambientGlobalSectionsIso, AlgebraicGeometry.Scheme.Spec_map,
    Quiver.Hom.unop_op] using
      AlgebraicGeometry.Scheme.ΓSpecIso_naturality
        (CommRingCat.ofHom (evaluationRingHom n))

private theorem evaluationPoint_normalized_apply (n : Int)
    (x : Γ(referenceScheme.underlying, ⊤)) :
    (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of Int)).hom
        ((evaluationPoint n).appTop x) =
      evaluationRingHom n (ambientGlobalSectionsIso.hom x) := by
  simpa only [CommRingCat.comp_apply] using congrArg
    (fun q => q x) (evaluationPoint_normalized_appTop n)

private theorem evaluationPoint_weak_semantic
    (n : Int) (hn : n * (n - 1) = 0) :
    SemanticLawfulAlong referenceRaw referenceScheme weakReading
      (evaluationPoint n) := by
  intro i _
  cases i
  change (GeometricLawReading.ofSemanticCore referenceRaw referenceScheme
    weakLawEquationCore weakSchemeBridge).HoldsOn (evaluationPoint n) PUnit.unit
  rw [GeometricLawReading.ofSemanticCore_holdsOn]
  intro a
  apply (ConcreteCategory.bijective_of_isIso
    (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of Int)).hom).1
  rw [map_zero, evaluationPoint_normalized_apply,
    weakGlobalEquation_eq]
  split
  · simpa [evaluationRingHom, coordinate] using hn
  · simp [evaluationRingHom]

private theorem evaluationPoint_strong_semantic
    (n : Int) (hn : n = 0) :
    SemanticLawfulAlong referenceRaw referenceScheme strongReading
      (evaluationPoint n) := by
  subst n
  intro i _
  cases i
  change (GeometricLawReading.ofSemanticCore referenceRaw referenceScheme
    strongLawEquationCore strongSchemeBridge).HoldsOn (evaluationPoint 0) PUnit.unit
  rw [GeometricLawReading.ofSemanticCore_holdsOn]
  intro a
  apply (ConcreteCategory.bijective_of_isIso
    (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of Int)).hom).1
  rw [map_zero, evaluationPoint_normalized_apply,
    strongGlobalEquation_eq]
  cases a <;> simp [evaluationRingHom, coordinate]

private theorem evaluationPoint_not_weak_semantic
    (n : Int) (hn : n * (n - 1) ≠ 0) :
    ¬ SemanticLawfulAlong referenceRaw referenceScheme weakReading
      (evaluationPoint n) := by
  intro h
  have hrequired := h PUnit.unit
    (referenceSite_equation_required PUnit.unit)
  change (GeometricLawReading.ofSemanticCore referenceRaw referenceScheme
    weakLawEquationCore weakSchemeBridge).HoldsOn (evaluationPoint n) PUnit.unit
      at hrequired
  rw [GeometricLawReading.ofSemanticCore_holdsOn] at hrequired
  have hA := hrequired AAT.AG.FiniteModel.FiniteAtom.componentA
  have hnorm := evaluationPoint_normalized_apply n
    (semanticCoreGlobalEquation referenceRaw referenceScheme
      weakLawEquationCore weakSchemeBridge PUnit.unit
      AAT.AG.FiniteModel.FiniteAtom.componentA)
  rw [hA, map_zero, weakGlobalEquation_eq] at hnorm
  apply hn
  simpa [evaluationRingHom, coordinate] using hnorm.symm

private theorem evaluationPoint_not_strong_semantic
    (n : Int) (hn : n ≠ 0) :
    ¬ SemanticLawfulAlong referenceRaw referenceScheme strongReading
      (evaluationPoint n) := by
  intro h
  have hrequired := h PUnit.unit
    (referenceSite_equation_required PUnit.unit)
  change (GeometricLawReading.ofSemanticCore referenceRaw referenceScheme
    strongLawEquationCore strongSchemeBridge).HoldsOn (evaluationPoint n) PUnit.unit
      at hrequired
  rw [GeometricLawReading.ofSemanticCore_holdsOn] at hrequired
  have hB := hrequired AAT.AG.FiniteModel.FiniteAtom.componentB
  have hnorm := evaluationPoint_normalized_apply n
    (semanticCoreGlobalEquation referenceRaw referenceScheme
      strongLawEquationCore strongSchemeBridge PUnit.unit
      AAT.AG.FiniteModel.FiniteAtom.componentB)
  rw [hB, map_zero, strongGlobalEquation_eq] at hnorm
  apply hn
  simpa [evaluationRingHom, coordinate] using hnorm.symm


/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
theorem weak_correspondence
    {T : AlgebraicGeometry.Scheme}
    (s : T ⟶ referenceScheme.underlying) :
    (SemanticLawfulAlong referenceRaw referenceScheme weakReading s ↔
      WitnessVanishes referenceRaw referenceScheme
        weakReading weakReading_valid weakReading_requiredClosed s) ∧
    (WitnessVanishes referenceRaw referenceScheme
        weakReading weakReading_valid weakReading_requiredClosed s ↔
      IdealLawfulAlong referenceRaw referenceScheme
        weakReading weakReading_valid weakReading_requiredClosed s) ∧
    (IdealLawfulAlong referenceRaw referenceScheme
        weakReading weakReading_valid weakReading_requiredClosed s ↔
      Nonempty
        (FactorsThroughLawfulClosedSubscheme referenceRaw referenceScheme
          weakReading weakReading_valid weakReading_requiredClosed s))
  := lawfulnessIdealFactorizationCorrespondence referenceRaw referenceScheme
    weakReading weakReading_valid weakReading_requiredClosed
    weakReading_requiredLawIdealExact s

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
theorem strong_correspondence
    {T : AlgebraicGeometry.Scheme}
    (s : T ⟶ referenceScheme.underlying) :
    (SemanticLawfulAlong referenceRaw referenceScheme strongReading s ↔
      WitnessVanishes referenceRaw referenceScheme
        strongReading strongReading_valid strongReading_requiredClosed s) ∧
    (WitnessVanishes referenceRaw referenceScheme
        strongReading strongReading_valid strongReading_requiredClosed s ↔
      IdealLawfulAlong referenceRaw referenceScheme
        strongReading strongReading_valid strongReading_requiredClosed s) ∧
    (IdealLawfulAlong referenceRaw referenceScheme
        strongReading strongReading_valid strongReading_requiredClosed s ↔
      Nonempty
        (FactorsThroughLawfulClosedSubscheme referenceRaw referenceScheme
          strongReading strongReading_valid strongReading_requiredClosed s)) := lawfulnessIdealFactorizationCorrespondence referenceRaw referenceScheme
    strongReading strongReading_valid strongReading_requiredClosed
    strongReading_requiredLawIdealExact s

private theorem weak_four_of_semantic
    {T : AlgebraicGeometry.Scheme}
    (s : T ⟶ referenceScheme.underlying)
    (hs : SemanticLawfulAlong referenceRaw referenceScheme weakReading s) :
    SemanticLawfulAlong referenceRaw referenceScheme weakReading s ∧
    WitnessVanishes referenceRaw referenceScheme
      weakReading weakReading_valid weakReading_requiredClosed s ∧
    IdealLawfulAlong referenceRaw referenceScheme
      weakReading weakReading_valid weakReading_requiredClosed s ∧
    Nonempty (FactorsThroughLawfulClosedSubscheme referenceRaw referenceScheme
      weakReading weakReading_valid weakReading_requiredClosed s) := by
  have h := weak_correspondence s
  exact ⟨hs, h.1.mp hs, h.2.1.mp (h.1.mp hs),
    h.2.2.mp (h.2.1.mp (h.1.mp hs))⟩

private theorem strong_four_of_semantic
    {T : AlgebraicGeometry.Scheme}
    (s : T ⟶ referenceScheme.underlying)
    (hs : SemanticLawfulAlong referenceRaw referenceScheme strongReading s) :
    SemanticLawfulAlong referenceRaw referenceScheme strongReading s ∧
    WitnessVanishes referenceRaw referenceScheme
      strongReading strongReading_valid strongReading_requiredClosed s ∧
    IdealLawfulAlong referenceRaw referenceScheme
      strongReading strongReading_valid strongReading_requiredClosed s ∧
    Nonempty (FactorsThroughLawfulClosedSubscheme referenceRaw referenceScheme
      strongReading strongReading_valid strongReading_requiredClosed s) := by
  have h := strong_correspondence s
  exact ⟨hs, h.1.mp hs, h.2.1.mp (h.1.mp hs),
    h.2.2.mp (h.2.1.mp (h.1.mp hs))⟩

private theorem weak_four_not_of_not_semantic
    {T : AlgebraicGeometry.Scheme}
    (s : T ⟶ referenceScheme.underlying)
    (hs : ¬ SemanticLawfulAlong referenceRaw referenceScheme weakReading s) :
    ¬ SemanticLawfulAlong referenceRaw referenceScheme weakReading s ∧
    ¬ WitnessVanishes referenceRaw referenceScheme
      weakReading weakReading_valid weakReading_requiredClosed s ∧
    ¬ IdealLawfulAlong referenceRaw referenceScheme
      weakReading weakReading_valid weakReading_requiredClosed s ∧
    ¬ Nonempty (FactorsThroughLawfulClosedSubscheme referenceRaw referenceScheme
      weakReading weakReading_valid weakReading_requiredClosed s) := by
  have h := weak_correspondence s
  exact ⟨hs, fun hw => hs (h.1.mpr hw),
    fun hi => hs (h.1.mpr (h.2.1.mpr hi)),
    fun hf => hs (h.1.mpr (h.2.1.mpr (h.2.2.mpr hf)))⟩

private theorem strong_four_not_of_not_semantic
    {T : AlgebraicGeometry.Scheme}
    (s : T ⟶ referenceScheme.underlying)
    (hs : ¬ SemanticLawfulAlong referenceRaw referenceScheme strongReading s) :
    ¬ SemanticLawfulAlong referenceRaw referenceScheme strongReading s ∧
    ¬ WitnessVanishes referenceRaw referenceScheme
      strongReading strongReading_valid strongReading_requiredClosed s ∧
    ¬ IdealLawfulAlong referenceRaw referenceScheme
      strongReading strongReading_valid strongReading_requiredClosed s ∧
    ¬ Nonempty (FactorsThroughLawfulClosedSubscheme referenceRaw referenceScheme
      strongReading strongReading_valid strongReading_requiredClosed s) := by
  have h := strong_correspondence s
  exact ⟨hs, fun hw => hs (h.1.mpr hw),
    fun hi => hs (h.1.mpr (h.2.1.mpr hi)),
    fun hf => hs (h.1.mpr (h.2.1.mpr (h.2.2.mpr hf)))⟩

private def rigidEvaluationRingHom : AmbientRing →+* ZMod 2 :=
  MvPolynomial.eval₂Hom (Int.castRingHom (ZMod 2)) (fun _ => 0)

private theorem weakAmbientIdeal_le_evalZero :
    weakAmbientIdeal ≤ RingHom.ker (evaluationRingHom 0) := by
  rw [weakAmbientIdeal]
  apply Ideal.span_le.mpr
  rintro _ (rfl : _ = coordinate * (coordinate - 1))
  simp [evaluationRingHom, coordinate]

private theorem weakAmbientIdeal_le_evalOne :
    weakAmbientIdeal ≤ RingHom.ker (evaluationRingHom 1) := by
  rw [weakAmbientIdeal]
  apply Ideal.span_le.mpr
  rintro _ (rfl : _ = coordinate * (coordinate - 1))
  simp [evaluationRingHom, coordinate]

private theorem strongAmbientIdeal_le_evalZero :
    strongAmbientIdeal ≤ RingHom.ker (evaluationRingHom 0) := by
  rw [strongAmbientIdeal]
  apply Ideal.span_le.mpr
  rintro _ (rfl : _ = coordinate)
  simp [evaluationRingHom, coordinate]

private theorem rigidAmbientIdeal_le_evalModTwo :
    rigidAmbientIdeal ≤ RingHom.ker rigidEvaluationRingHom := by
  rw [rigidAmbientIdeal]
  apply Ideal.span_le.mpr
  intro p hp
  rcases Set.mem_insert_iff.mp hp with rfl | hp
  · simp [rigidEvaluationRingHom, coordinate]
  · have hp' : p = MvPolynomial.C 2 := by
      simpa only [Set.mem_singleton_iff] using hp
    subst p
    change rigidEvaluationRingHom (MvPolynomial.C 2) = 0
    simp only [rigidEvaluationRingHom, MvPolynomial.eval₂Hom_C]
    decide

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
theorem weakAmbientIdeal_ne_bot :
    weakAmbientIdeal ≠ ⊥ := by
  intro h
  have hm : coordinate * (coordinate - 1) ∈ weakAmbientIdeal :=
    Ideal.subset_span (Set.mem_singleton _)
  rw [h] at hm
  have hz : coordinate * (coordinate - 1) = 0 := by simpa using hm
  have hev := congrArg (evaluationRingHom 2) hz
  norm_num [evaluationRingHom, coordinate] at hev

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
theorem weakAmbientIdeal_ne_top :
    weakAmbientIdeal ≠ ⊤ := by
  intro h
  have hone : (1 : AmbientRing) ∈ weakAmbientIdeal := by rw [h]; simp
  have hk := weakAmbientIdeal_le_evalZero hone
  norm_num [evaluationRingHom] at hk

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
theorem strongAmbientIdeal_ne_bot :
    strongAmbientIdeal ≠ ⊥ := by
  intro h
  have hm : coordinate ∈ strongAmbientIdeal :=
    Ideal.subset_span (Set.mem_singleton _)
  rw [h] at hm
  have hz : coordinate = 0 := by simpa using hm
  have hev := congrArg (evaluationRingHom 1) hz
  norm_num [evaluationRingHom, coordinate] at hev

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
theorem strongAmbientIdeal_ne_top :
    strongAmbientIdeal ≠ ⊤ := by
  intro h
  have hone : (1 : AmbientRing) ∈ strongAmbientIdeal := by rw [h]; simp
  have hk := strongAmbientIdeal_le_evalZero hone
  norm_num [evaluationRingHom] at hk

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
theorem rigidAmbientIdeal_ne_bot :
    rigidAmbientIdeal ≠ ⊥ := by
  intro h
  have hm : coordinate ∈ rigidAmbientIdeal :=
    Ideal.subset_span (Set.mem_insert coordinate _)
  rw [h] at hm
  have hz : coordinate = 0 := by simpa using hm
  have hev := congrArg (evaluationRingHom 1) hz
  norm_num [evaluationRingHom, coordinate] at hev

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
theorem rigidAmbientIdeal_ne_top :
    rigidAmbientIdeal ≠ ⊤ := by
  intro h
  have hone : (1 : AmbientRing) ∈ rigidAmbientIdeal := by rw [h]; simp
  have hk := rigidAmbientIdeal_le_evalModTwo hone
  have : (1 : ZMod 2) = 0 := by
    simpa [rigidEvaluationRingHom] using hk
  norm_num at this

private theorem ideal_le_of_map_le_of_bijective
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Bijective f)
    {I J : Ideal R} (h : Ideal.map f I ≤ Ideal.map f J) : I ≤ J := by
  intro x hx
  have hxmap : f x ∈ Ideal.map f I := Ideal.mem_map_of_mem f hx
  have hjmap := h hxmap
  rw [Ideal.mem_map_iff_of_surjective f hf.2] at hjmap
  obtain ⟨y, hy, hyx⟩ := hjmap
  have hxy : y = x := hf.1 hyx
  simpa [hxy] using hy

private theorem weakAmbientIdeal_le_strongAmbientIdeal :
    weakAmbientIdeal ≤ strongAmbientIdeal := by
  rw [weakAmbientIdeal, strongAmbientIdeal]
  apply Ideal.span_le.mpr
  rintro _ (rfl : _ = coordinate * (coordinate - 1))
  exact (Ideal.span {coordinate}).mul_mem_right (coordinate - 1)
    (Ideal.subset_span (Set.mem_singleton coordinate))

private theorem strongAmbientIdeal_le_rigidAmbientIdeal :
    strongAmbientIdeal ≤ rigidAmbientIdeal := by
  rw [strongAmbientIdeal, rigidAmbientIdeal]
  apply Ideal.span_le.mpr
  rintro _ (rfl : _ = coordinate)
  exact Ideal.subset_span (Set.mem_insert coordinate _)

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
theorem weakIdeal_lt_strongIdeal :
    weakIdealSheaf < strongIdealSheaf := by
  refine lt_of_le_of_ne ?_ ?_
  · letI : IsAffine referenceScheme.underlying := by
      rw [referenceScheme_underlying, ambientScheme_eq]
      infer_instance
    apply Scheme.IdealSheafData.le_of_isAffine
    have hmap :
        Ideal.map ambientGlobalSectionsIso.hom.hom
            (weakIdealSheaf.ideal ambientTopAffineOpen) ≤
          Ideal.map ambientGlobalSectionsIso.hom.hom
            (strongIdealSheaf.ideal ambientTopAffineOpen) := by
      rw [weakIdeal_top_eq, strongIdeal_top_eq]
      exact weakAmbientIdeal_le_strongAmbientIdeal
    have hsource := ideal_le_of_map_le_of_bijective
      ambientGlobalSectionsIso.hom.hom
      (ConcreteCategory.bijective_of_isIso ambientGlobalSectionsIso.hom) hmap
    simpa [ambientTopAffineOpen] using hsource
  · intro heq
    have htop := congrArg
      (fun I : referenceScheme.underlying.IdealSheafData =>
        Ideal.map ambientGlobalSectionsIso.hom.hom
          (I.ideal ambientTopAffineOpen)) heq
    change Ideal.map ambientGlobalSectionsIso.hom.hom
        (weakIdealSheaf.ideal ambientTopAffineOpen) =
      Ideal.map ambientGlobalSectionsIso.hom.hom
        (strongIdealSheaf.ideal ambientTopAffineOpen) at htop
    rw [weakIdeal_top_eq, strongIdeal_top_eq] at htop
    have hx : coordinate ∈ strongAmbientIdeal :=
      Ideal.subset_span (Set.mem_singleton coordinate)
    rw [← htop] at hx
    have hk := weakAmbientIdeal_le_evalOne hx
    norm_num [evaluationRingHom, coordinate] at hk

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
theorem strongIdeal_lt_rigidIdeal :
    strongIdealSheaf < rigidIdealSheaf := by
  refine lt_of_le_of_ne ?_ ?_
  · letI : IsAffine referenceScheme.underlying := by
      rw [referenceScheme_underlying, ambientScheme_eq]
      infer_instance
    apply Scheme.IdealSheafData.le_of_isAffine
    have hmap :
        Ideal.map ambientGlobalSectionsIso.hom.hom
            (strongIdealSheaf.ideal ambientTopAffineOpen) ≤
          Ideal.map ambientGlobalSectionsIso.hom.hom
            (rigidIdealSheaf.ideal ambientTopAffineOpen) := by
      rw [strongIdeal_top_eq, rigidIdeal_top_eq]
      exact strongAmbientIdeal_le_rigidAmbientIdeal
    have hsource := ideal_le_of_map_le_of_bijective
      ambientGlobalSectionsIso.hom.hom
      (ConcreteCategory.bijective_of_isIso ambientGlobalSectionsIso.hom) hmap
    simpa [ambientTopAffineOpen] using hsource
  · intro heq
    have htop := congrArg
      (fun I : referenceScheme.underlying.IdealSheafData =>
        Ideal.map ambientGlobalSectionsIso.hom.hom
          (I.ideal ambientTopAffineOpen)) heq
    change Ideal.map ambientGlobalSectionsIso.hom.hom
        (strongIdealSheaf.ideal ambientTopAffineOpen) =
      Ideal.map ambientGlobalSectionsIso.hom.hom
        (rigidIdealSheaf.ideal ambientTopAffineOpen) at htop
    rw [strongIdeal_top_eq, rigidIdeal_top_eq] at htop
    have htwo : MvPolynomial.C 2 ∈ rigidAmbientIdeal :=
      Ideal.subset_span
        (Set.mem_insert_of_mem coordinate (Set.mem_singleton _))
    rw [← htop] at htwo
    have hk := strongAmbientIdeal_le_evalZero htwo
    change evaluationRingHom 0 (MvPolynomial.C 2) = 0 at hk
    have : (2 : Int) = 0 := by
      simpa only [evaluationRingHom, MvPolynomial.eval₂Hom_C,
        RingHom.id_apply] using hk
    norm_num at this


/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
theorem zeroPoint_fires :
    SemanticLawfulAlong referenceRaw referenceScheme weakReading zeroPoint ∧
    WitnessVanishes referenceRaw referenceScheme
      weakReading weakReading_valid weakReading_requiredClosed zeroPoint ∧
    IdealLawfulAlong referenceRaw referenceScheme
      weakReading weakReading_valid weakReading_requiredClosed zeroPoint ∧
    Nonempty
      (FactorsThroughLawfulClosedSubscheme referenceRaw referenceScheme
        weakReading weakReading_valid weakReading_requiredClosed zeroPoint) ∧
    SemanticLawfulAlong referenceRaw referenceScheme strongReading zeroPoint ∧
    WitnessVanishes referenceRaw referenceScheme
      strongReading strongReading_valid strongReading_requiredClosed zeroPoint ∧
    IdealLawfulAlong referenceRaw referenceScheme
      strongReading strongReading_valid strongReading_requiredClosed zeroPoint ∧
    Nonempty
      (FactorsThroughLawfulClosedSubscheme referenceRaw referenceScheme
        strongReading strongReading_valid strongReading_requiredClosed zeroPoint) := by
  have hwsem : SemanticLawfulAlong referenceRaw referenceScheme weakReading
      zeroPoint := by
    simpa only [zeroPoint] using
      evaluationPoint_weak_semantic 0 (by norm_num)
  have hssem : SemanticLawfulAlong referenceRaw referenceScheme strongReading
      zeroPoint := by
    simpa only [zeroPoint] using
      evaluationPoint_strong_semantic 0 rfl
  rcases weak_four_of_semantic zeroPoint hwsem with ⟨hw₁, hw₂, hw₃, hw₄⟩
  rcases strong_four_of_semantic zeroPoint hssem with ⟨hs₁, hs₂, hs₃, hs₄⟩
  exact ⟨hw₁, hw₂, hw₃, hw₄, hs₁, hs₂, hs₃, hs₄⟩

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
theorem onePoint_fires :
    SemanticLawfulAlong referenceRaw referenceScheme weakReading onePoint ∧
    WitnessVanishes referenceRaw referenceScheme
      weakReading weakReading_valid weakReading_requiredClosed onePoint ∧
    IdealLawfulAlong referenceRaw referenceScheme
      weakReading weakReading_valid weakReading_requiredClosed onePoint ∧
    Nonempty
      (FactorsThroughLawfulClosedSubscheme referenceRaw referenceScheme
        weakReading weakReading_valid weakReading_requiredClosed onePoint) ∧
    ¬ SemanticLawfulAlong referenceRaw referenceScheme strongReading onePoint ∧
    ¬ WitnessVanishes referenceRaw referenceScheme
      strongReading strongReading_valid strongReading_requiredClosed onePoint ∧
    ¬ IdealLawfulAlong referenceRaw referenceScheme
      strongReading strongReading_valid strongReading_requiredClosed onePoint ∧
    ¬ Nonempty
      (FactorsThroughLawfulClosedSubscheme referenceRaw referenceScheme
        strongReading strongReading_valid strongReading_requiredClosed onePoint) := by
  have hwsem : SemanticLawfulAlong referenceRaw referenceScheme weakReading
      onePoint := by
    simpa only [onePoint] using
      evaluationPoint_weak_semantic 1 (by norm_num)
  have hssem : ¬ SemanticLawfulAlong referenceRaw referenceScheme strongReading
      onePoint := by
    simpa only [onePoint] using
      evaluationPoint_not_strong_semantic 1 (by norm_num)
  rcases weak_four_of_semantic onePoint hwsem with ⟨hw₁, hw₂, hw₃, hw₄⟩
  rcases strong_four_not_of_not_semantic onePoint hssem with ⟨hs₁, hs₂, hs₃, hs₄⟩
  exact ⟨hw₁, hw₂, hw₃, hw₄, hs₁, hs₂, hs₃, hs₄⟩

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
theorem twoPoint_fires :
    ¬ SemanticLawfulAlong referenceRaw referenceScheme weakReading twoPoint ∧
    ¬ WitnessVanishes referenceRaw referenceScheme
      weakReading weakReading_valid weakReading_requiredClosed twoPoint ∧
    ¬ IdealLawfulAlong referenceRaw referenceScheme
      weakReading weakReading_valid weakReading_requiredClosed twoPoint ∧
    ¬ Nonempty
      (FactorsThroughLawfulClosedSubscheme referenceRaw referenceScheme
        weakReading weakReading_valid weakReading_requiredClosed twoPoint) ∧
    ¬ SemanticLawfulAlong referenceRaw referenceScheme strongReading twoPoint ∧
    ¬ WitnessVanishes referenceRaw referenceScheme
      strongReading strongReading_valid strongReading_requiredClosed twoPoint ∧
    ¬ IdealLawfulAlong referenceRaw referenceScheme
      strongReading strongReading_valid strongReading_requiredClosed twoPoint ∧
    ¬ Nonempty
      (FactorsThroughLawfulClosedSubscheme referenceRaw referenceScheme
        strongReading strongReading_valid strongReading_requiredClosed twoPoint) := by
  have hwsem : ¬ SemanticLawfulAlong referenceRaw referenceScheme weakReading
      twoPoint := by
    simpa only [twoPoint] using
      evaluationPoint_not_weak_semantic 2 (by norm_num)
  have hssem : ¬ SemanticLawfulAlong referenceRaw referenceScheme strongReading
      twoPoint := by
    simpa only [twoPoint] using
      evaluationPoint_not_strong_semantic 2 (by norm_num)
  rcases weak_four_not_of_not_semantic twoPoint hwsem with ⟨hw₁, hw₂, hw₃, hw₄⟩
  rcases strong_four_not_of_not_semantic twoPoint hssem with ⟨hs₁, hs₂, hs₃, hs₄⟩
  exact ⟨hw₁, hw₂, hw₃, hw₄, hs₁, hs₂, hs₃, hs₄⟩

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
@[simp] theorem weakImmersion_ker :
    weakImmersion.ker = weakIdealSheaf := by
  exact lawfulClosedImmersion_ker referenceRaw referenceScheme weakReading
    weakReading_valid weakReading_requiredClosed

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
@[simp] theorem strongImmersion_ker :
    strongImmersion.ker = strongIdealSheaf := by
  exact lawfulClosedImmersion_ker referenceRaw referenceScheme strongReading
    strongReading_valid strongReading_requiredClosed

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
@[simp] theorem weakImmersion_zeroLocus :
    Set.range weakImmersion = weakIdealSheaf.support := by
  exact lawfulClosedImmersion_range referenceRaw referenceScheme weakReading
    weakReading_valid weakReading_requiredClosed

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
@[simp] theorem strongImmersion_zeroLocus :
    Set.range strongImmersion = strongIdealSheaf.support := by
  exact lawfulClosedImmersion_range referenceRaw referenceScheme strongReading
    strongReading_valid strongReading_requiredClosed

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
noncomputable def weakAffineQuotientChart :
    AlgebraicGeometry.Spec
        (CommRingCat.of
          (Γ(referenceScheme.underlying, ambientTopAffineOpen) ⧸
            weakIdealSheaf.ideal ambientTopAffineOpen)) ⟶
      weakLocus :=
  (lawfulClosedSubschemeCover
    referenceRaw referenceScheme weakReading weakReading_valid
    weakReading_requiredClosed).f ambientTopAffineOpen

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
noncomputable def strongAffineQuotientChart :
    AlgebraicGeometry.Spec
        (CommRingCat.of
          (Γ(referenceScheme.underlying, ambientTopAffineOpen) ⧸
            strongIdealSheaf.ideal ambientTopAffineOpen)) ⟶
      strongLocus :=
  (lawfulClosedSubschemeCover
    referenceRaw referenceScheme strongReading strongReading_valid
    strongReading_requiredClosed).f ambientTopAffineOpen

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
theorem weakAffineQuotientChart_isIso :
    IsIso weakAffineQuotientChart := by
  change IsIso (weakIdealSheaf.subschemeCover.f ambientTopAffineOpen)
  apply isIso_of_isOpenImmersion_of_opensRange_eq_top
  rw [Scheme.IdealSheafData.opensRange_subschemeCover_map]
  simp only [ambientTopAffineOpen_obj, Scheme.Hom.preimage_top]

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
theorem strongAffineQuotientChart_isIso :
    IsIso strongAffineQuotientChart := by
  change IsIso (strongIdealSheaf.subschemeCover.f ambientTopAffineOpen)
  apply isIso_of_isOpenImmersion_of_opensRange_eq_top
  rw [Scheme.IdealSheafData.opensRange_subschemeCover_map]
  simp only [ambientTopAffineOpen_obj, Scheme.Hom.preimage_top]

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
theorem weakLocus_nonempty : Nonempty weakLocus := by
  let p : AlgebraicGeometry.Spec (CommRingCat.of Int) :=
    Classical.choice inferInstance
  exact zeroPoint_fires.2.2.2.1.map (fun t => t.1.base p)

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
theorem strongLocus_nonempty : Nonempty strongLocus := by
  let p : AlgebraicGeometry.Spec (CommRingCat.of Int) :=
    Classical.choice inferInstance
  exact zeroPoint_fires.2.2.2.2.2.2.2.map (fun t => t.1.base p)

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
theorem weakIdeal_overlap_agrees :
    (weakIdealSheaf.comap leftChart.map).comap
        (pullback.fst leftChart.map rightChart.map) =
      (weakIdealSheaf.comap rightChart.map).comap
        (pullback.snd leftChart.map rightChart.map) := by
  rw [← Scheme.IdealSheafData.comap_comp,
    ← Scheme.IdealSheafData.comap_comp, pullback.condition]

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
theorem strongIdeal_overlap_agrees :
    (strongIdealSheaf.comap leftChart.map).comap
        (pullback.fst leftChart.map rightChart.map) =
      (strongIdealSheaf.comap rightChart.map).comap
        (pullback.snd leftChart.map rightChart.map) := by
  rw [← Scheme.IdealSheafData.comap_comp,
    ← Scheme.IdealSheafData.comap_comp, pullback.condition]

private theorem pairContext_cast_inv :
    (eqToIso (by rw [pair_context]) :
      architectureChartSpec referenceRaw
          (referenceScheme.atlas.pairContext
            referenceRaw leftIndex rightIndex) ≅
        architectureChartSpec referenceRaw overlapContext).inv =
      architectureChartRestriction referenceRaw
        (eqToHom pair_context.symm) := by
  change eqToHom
      (congrArg (architectureChartFunctor referenceRaw).obj
        pair_context.symm) =
    (architectureChartFunctor referenceRaw).map
      (eqToHom pair_context.symm)
  rw [CategoryTheory.eqToHom_map]

private theorem actualOverlapIso_inv_fst :
    actualOverlapIso.inv ≫ pullback.fst leftChart.map rightChart.map =
      overlapChartDomainIso.inv ≫
        architectureChartRestriction referenceRaw overlapToLeft := by
  rw [actualOverlapIso_eq]
  simp only [Iso.trans_inv, Iso.symm_inv,
    StandardArchitectureScheme.overlap_is_actual_pullback, Category.assoc]
  have hcmp :=
    referenceScheme.overlapsValid.comparison_fst leftIndex rightIndex
  change (referenceScheme.overlaps.comparison leftIndex rightIndex).hom ≫
      pullback.fst leftChart.map rightChart.map =
    architectureChartRestriction referenceRaw
      (referenceScheme.atlas.pairToLeft
        referenceRaw leftIndex rightIndex) at hcmp
  slice_lhs 3 4 =>
    rw [hcmp]
  rw [← cancel_epi overlapChartDomainIso.hom,
    Iso.hom_inv_id_assoc, Iso.hom_inv_id_assoc]
  rw [pairContext_cast_inv]
  rw [← architectureChartRestriction_comp]
  exact congrArg (architectureChartRestriction referenceRaw)
    (Subsingleton.elim _ _)

private theorem overlapChartDomainIso_inv_appTop :
    overlapChartDomainIso.inv.appTop ≫
        (AlgebraicGeometry.Scheme.ΓSpecIso
          (CommRingCat.of
            (Localization.Away overlapGenerator))).hom =
      (AlgebraicGeometry.Scheme.ΓSpecIso
        (SheafifiedSectionRing referenceRaw overlapContext)).hom ≫
        overlapSectionRingIso.hom := by
  simpa only [overlapChartDomainIso,
    AlgebraicGeometry.Scheme.Spec_map, Quiver.Hom.unop_op] using
    AlgebraicGeometry.Scheme.ΓSpecIso_naturality
      overlapSectionRingIso.hom

private theorem actualOverlap_left_appTop :
    leftChartGlobalSectionsIso.inv ≫
        (pullback.fst leftChart.map rightChart.map).appTop ≫
        actualOverlapGlobalSectionsIso.hom =
      CommRingCat.ofHom leftToOverlapRingHom := by
  have hfst := congrArg (fun q => q.appTop) actualOverlapIso_inv_fst
  simp only [AlgebraicGeometry.Scheme.Hom.comp_appTop] at hfst
  rw [leftChartGlobalSectionsIso, actualOverlapGlobalSectionsIso,
    Iso.trans_inv, Iso.trans_hom]
  simp only [Category.assoc, asIso_hom]
  slice_lhs 3 4 => rw [hfst]
  slice_lhs 4 5 => rw [overlapChartDomainIso_inv_appTop]
  slice_lhs 3 4 =>
    rw [architectureChartRestriction_appTop]
  slice_lhs 2 4 =>
    rw [Iso.inv_hom_id_assoc]
  exact overlap_left_restriction_is_localization

private theorem reference_ofIdealTop_comap_open
    {Y Z : Scheme} [IsAffine Y]
    (I : Ideal Γ(Z, ⊤)) (g : Y ⟶ Z) [IsOpenImmersion g] :
    (Scheme.IdealSheafData.ofIdealTop I).comap g =
      Scheme.IdealSheafData.ofIdealTop (Ideal.map g.appTop.hom I) := by
  apply Scheme.IdealSheafData.ext_of_isAffine
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]
  simp only [Scheme.IdealSheafData.ofIdealTop_ideal]
  let e := g.appIso ⊤
  have comap_inv (J : Ideal Γ(Z, g ''ᵁ (⊤ : Y.Opens))) :
      Ideal.comap e.inv.hom J = Ideal.map e.hom.hom J := by
    ext x
    constructor
    · intro hx
      change e.inv x ∈ J at hx
      simpa using Ideal.mem_map_of_mem e.hom.hom hx
    · intro hx
      rw [Ideal.mem_map_iff_of_surjective e.hom.hom
        e.commRingCatIsoToRingEquiv.surjective] at hx
      obtain ⟨y, hy, hxy⟩ := hx
      change e.inv x ∈ J
      rw [← hxy]
      simpa using hy
  rw [comap_inv, Ideal.map_map]
  have appTop_eq :
      e.hom.hom.comp
          (Z.presheaf.map (homOfLE le_top).op).hom =
        g.appTop.hom := by
    apply RingHom.ext
    intro z
    change ((Z.presheaf.map (homOfLE le_top).op) ≫ e.hom) z =
      g.appTop z
    simp only [e, Scheme.Hom.appIso_hom]
    rw [← Category.assoc, g.naturality, Category.assoc,
      ← Functor.map_comp]
    simp
  rw [appTop_eq]
  have top_res :
      (Y.presheaf.map (homOfLE le_top).op).hom =
        RingHom.id Γ(Y, ⊤) := by
    apply RingHom.ext
    intro z
    have h := Y.presheaf.map_id (Opposite.op (⊤ : Y.Opens))
    exact congrArg (fun q => q z) h
  rw [top_res, Ideal.map_id]

private theorem reference_ideal_top_comap_open
    {Y Z : Scheme} [IsAffine Y] [IsAffine Z]
    (J : Z.IdealSheafData) (g : Y ⟶ Z) [IsOpenImmersion g] :
    (J.comap g).ideal ⟨⊤, isAffineOpen_top Y⟩ =
      Ideal.map g.appTop.hom
        (J.ideal ⟨⊤, isAffineOpen_top Z⟩) := by
  have hJ : Scheme.IdealSheafData.ofIdealTop
      (J.ideal ⟨⊤, isAffineOpen_top Z⟩) = J :=
    Scheme.IdealSheafData.ext_of_isAffine (by simp)
  rw [← hJ, reference_ofIdealTop_comap_open]
  simp

private theorem left_span_map_overlap (a : AmbientRing) :
    Ideal.map leftToOverlapRingHom
        (Ideal.span {algebraMap AmbientRing
          (Localization.Away leftGenerator) a}) =
      Ideal.span {algebraMap AmbientRing
        (Localization.Away overlapGenerator) a} := by
  rw [Ideal.map_span, Set.image_singleton]
  exact congrArg (fun x => Ideal.span {x})
    (RingHom.congr_fun leftToOverlapRingHom_comp_algebraMap a)

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
theorem weakIdeal_overlap_eq :
    Ideal.map actualOverlapGlobalSectionsIso.hom.hom
        ((weakIdealSheaf.comap
          (referenceScheme.atlas.actualOverlapToUnderlying
            referenceRaw leftIndex rightIndex)).ideal
          ⟨⊤, @isAffineOpen_top
            (referenceScheme.atlas.actualOverlap
              referenceRaw leftIndex rightIndex)
            (IsAffine.of_isIso actualOverlapIso.hom)⟩) =
      weakOverlapIdeal := by
  letI : IsOpenImmersion
      (pullback.fst
        (referenceScheme.atlas.chart leftIndex).map
        (referenceScheme.atlas.chart rightIndex).map) :=
    referenceScheme.atlas.overlap_left_isOpenImmersion
      referenceRaw referenceScheme.atlasValid leftIndex rightIndex
  letI : IsAffine
      (referenceScheme.atlas.actualOverlap
        referenceRaw leftIndex rightIndex) :=
    IsAffine.of_isIso actualOverlapIso.hom
  have hleft' :
      (weakIdealSheaf.comap leftChart.map).ideal
          ⟨⊤, @isAffineOpen_top leftChart.domain
            leftChart.domain_isAffine⟩ =
        Ideal.map leftChartGlobalSectionsIso.inv.hom weakLeftIdeal := by
    have hcomp :
        leftChartGlobalSectionsIso.inv.hom.comp
            leftChartGlobalSectionsIso.hom.hom =
          RingHom.id _ := by
      change (leftChartGlobalSectionsIso.hom ≫
        leftChartGlobalSectionsIso.inv).hom = _
      rw [Iso.hom_inv_id]
      rfl
    rw [← weakIdeal_left_eq, Ideal.map_map, hcomp]
    exact (Ideal.map_id _).symm
  rw [referenceScheme.atlas.actualOverlapToUnderlying_eq_left,
    Scheme.IdealSheafData.comap_comp]
  rw [reference_ideal_top_comap_open]
  change Ideal.map actualOverlapGlobalSectionsIso.hom.hom
      (Ideal.map
        (pullback.fst leftChart.map rightChart.map).appTop.hom
        ((weakIdealSheaf.comap leftChart.map).ideal
          ⟨⊤, @isAffineOpen_top leftChart.domain
            leftChart.domain_isAffine⟩)) = weakOverlapIdeal
  rw [hleft', Ideal.map_map, Ideal.map_map]
  change Ideal.map
      (leftChartGlobalSectionsIso.inv ≫
        (pullback.fst leftChart.map rightChart.map).appTop ≫
        actualOverlapGlobalSectionsIso.hom).hom weakLeftIdeal =
    weakOverlapIdeal
  rw [actualOverlap_left_appTop]
  simpa only [weakLeftIdeal, weakOverlapIdeal] using
    left_span_map_overlap (coordinate * (coordinate - 1))

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
theorem strongIdeal_overlap_eq :
    Ideal.map actualOverlapGlobalSectionsIso.hom.hom
        ((strongIdealSheaf.comap
          (referenceScheme.atlas.actualOverlapToUnderlying
            referenceRaw leftIndex rightIndex)).ideal
          ⟨⊤, @isAffineOpen_top
            (referenceScheme.atlas.actualOverlap
              referenceRaw leftIndex rightIndex)
            (IsAffine.of_isIso actualOverlapIso.hom)⟩) =
      strongOverlapIdeal := by
  letI : IsOpenImmersion
      (pullback.fst
        (referenceScheme.atlas.chart leftIndex).map
        (referenceScheme.atlas.chart rightIndex).map) :=
    referenceScheme.atlas.overlap_left_isOpenImmersion
      referenceRaw referenceScheme.atlasValid leftIndex rightIndex
  letI : IsAffine
      (referenceScheme.atlas.actualOverlap
        referenceRaw leftIndex rightIndex) :=
    IsAffine.of_isIso actualOverlapIso.hom
  have hleft' :
      (strongIdealSheaf.comap leftChart.map).ideal
          ⟨⊤, @isAffineOpen_top leftChart.domain
            leftChart.domain_isAffine⟩ =
        Ideal.map leftChartGlobalSectionsIso.inv.hom strongLeftIdeal := by
    have hcomp :
        leftChartGlobalSectionsIso.inv.hom.comp
            leftChartGlobalSectionsIso.hom.hom =
          RingHom.id _ := by
      change (leftChartGlobalSectionsIso.hom ≫
        leftChartGlobalSectionsIso.inv).hom = _
      rw [Iso.hom_inv_id]
      rfl
    rw [← strongIdeal_left_eq, Ideal.map_map, hcomp]
    exact (Ideal.map_id _).symm
  rw [referenceScheme.atlas.actualOverlapToUnderlying_eq_left,
    Scheme.IdealSheafData.comap_comp]
  rw [reference_ideal_top_comap_open]
  change Ideal.map actualOverlapGlobalSectionsIso.hom.hom
      (Ideal.map
        (pullback.fst leftChart.map rightChart.map).appTop.hom
        ((strongIdealSheaf.comap leftChart.map).ideal
          ⟨⊤, @isAffineOpen_top leftChart.domain
            leftChart.domain_isAffine⟩)) = strongOverlapIdeal
  rw [hleft', Ideal.map_map, Ideal.map_map]
  change Ideal.map
      (leftChartGlobalSectionsIso.inv ≫
        (pullback.fst leftChart.map rightChart.map).appTop ≫
        actualOverlapGlobalSectionsIso.hom).hom strongLeftIdeal =
    strongOverlapIdeal
  rw [actualOverlap_left_appTop]
  simpa only [strongLeftIdeal, strongOverlapIdeal] using
    left_span_map_overlap coordinate

private theorem rigidTopIdeal_ne_top :
    rigidIdealSheaf.ideal ambientTopAffineOpen ≠ ⊤ := by
  intro htop
  apply rigidAmbientIdeal_ne_top
  have hmap := congrArg
    (Ideal.map ambientGlobalSectionsIso.hom.hom) htop
  rw [rigidIdeal_top_eq] at hmap
  simpa only [Ideal.map_top, eq_comm] using hmap

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
theorem rigidLocus_nonempty : Nonempty rigidLocus := by
  letI : Nontrivial
      (Γ(referenceScheme.underlying, ambientTopAffineOpen) ⧸
        rigidIdealSheaf.ideal ambientTopAffineOpen) :=
    Ideal.Quotient.nontrivial_iff.mpr rigidTopIdeal_ne_top
  let p : AlgebraicGeometry.Spec
      (CommRingCat.of
        (Γ(referenceScheme.underlying, ambientTopAffineOpen) ⧸
          rigidIdealSheaf.ideal ambientTopAffineOpen)) :=
    Classical.choice inferInstance
  exact ⟨((lawfulClosedSubschemeCover
    referenceRaw referenceScheme rigidReading rigidReading_valid
    rigidReading_requiredClosed).f ambientTopAffineOpen).base p⟩

private theorem rigidImmersion_ker :
    rigidImmersion.ker = rigidIdealSheaf := by
  exact lawfulClosedImmersion_ker referenceRaw referenceScheme rigidReading
    rigidReading_valid rigidReading_requiredClosed

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
theorem weakImmersion_not_isIso : ¬ IsIso weakImmersion := by
  intro hIso
  letI : IsIso weakImmersion := hIso
  have hk : weakIdealSheaf = ⊥ := by
    simpa only [weakImmersion_ker] using
      (Scheme.Hom.ker_eq_bot_of_isIso weakImmersion)
  apply weakAmbientIdeal_ne_bot
  rw [← weakIdeal_top_eq, hk]
  simp

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
theorem strongImmersion_not_isIso : ¬ IsIso strongImmersion := by
  intro hIso
  letI : IsIso strongImmersion := hIso
  have hk : strongIdealSheaf = ⊥ := by
    simpa only [strongImmersion_ker] using
      (Scheme.Hom.ker_eq_bot_of_isIso strongImmersion)
  apply strongAmbientIdeal_ne_bot
  rw [← strongIdeal_top_eq, hk]
  simp

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
theorem rigidImmersion_not_isIso : ¬ IsIso rigidImmersion := by
  intro hIso
  letI : IsIso rigidImmersion := hIso
  have hk : rigidIdealSheaf = ⊥ := by
    simpa only [rigidImmersion_ker] using
      (Scheme.Hom.ker_eq_bot_of_isIso rigidImmersion)
  apply rigidAmbientIdeal_ne_bot
  rw [← rigidIdeal_top_eq, hk]
  simp

/-! ## R5: law comparison -/

/-- The concrete atom map from the weak reading to the strong reading. -/
def weakToStrongAtomMap
    (a : AAT.AG.FiniteModel.carrier.Atom) :
    AAT.AG.FiniteModel.carrier.Atom :=
  if a = AAT.AG.FiniteModel.FiniteAtom.componentA then
    AAT.AG.FiniteModel.FiniteAtom.componentA
  else
    AAT.AG.FiniteModel.FiniteAtom.componentC

/-- The weak-to-strong atom map is fixed on every input. -/
@[simp] theorem weakToStrongAtomMap_eq
    (a : AAT.AG.FiniteModel.carrier.Atom) :
    weakToStrongAtomMap a =
      if a = AAT.AG.FiniteModel.FiniteAtom.componentA then
        AAT.AG.FiniteModel.FiniteAtom.componentA
      else
        AAT.AG.FiniteModel.FiniteAtom.componentC :=
  rfl

private theorem weakGlobalEquation_atomMap
    (a : AAT.AG.FiniteModel.carrier.Atom) :
    semanticCoreGlobalEquation referenceRaw referenceScheme
        weakLawEquationCore weakSchemeBridge PUnit.unit a =
      semanticCoreGlobalEquation referenceRaw referenceScheme
        strongLawEquationCore strongSchemeBridge PUnit.unit
          (weakToStrongAtomMap a) := by
  apply (ConcreteCategory.bijective_of_isIso
    ambientGlobalSectionsIso.hom).1
  rw [weakGlobalEquation_eq, strongGlobalEquation_eq]
  cases a <;> simp [weakToStrongAtomMap]

/-- The concrete primitive inclusion from weak laws to strong laws. -/
def weakToStrong :
    ClosedEquationalLawInclusion
      referenceRaw referenceScheme weakReading strongReading where
  lawMap := id
  atomMap := fun _ => weakToStrongAtomMap

/-- The weak-to-strong inclusion preserves the sole law index. -/
@[simp] theorem weakToStrong_lawMap :
    weakToStrong.lawMap = id :=
  rfl

/-- The weak-to-strong inclusion uses the concrete atom map. -/
@[simp] theorem weakToStrong_atomMap :
    weakToStrong.atomMap PUnit.unit = weakToStrongAtomMap :=
  rfl

/-- The weak-to-strong inclusion preserves required laws, witnesses, and semantics. -/
theorem weakToStrong_valid :
    IsClosedEquationalLawInclusion
      referenceRaw referenceScheme weakToStrong where
  required_map := fun i hi => by simpa [weakToStrong] using hi
  closed_map := by
    intro i _
    change weakToStrong.lawMap i ∈
      (Set.univ : Set strongLawEquationCore.Index)
    exact Set.mem_univ _
  selected_map := by
    intro _V i _
    change weakToStrong.lawMap i ∈
      (Set.univ : Set strongLawEquationCore.Index)
    exact Set.mem_univ _
  coordinate_eq := by
    intro i hi V a
    cases i
    simp only [weakReading, strongReading,
      ClosedEquationalLawReading.ofSemanticCore_witness,
      ClosedEquationalLawWitness.ofSemanticCore,
      ClosedEquationalLawWitness.ofGlobalSections_coordinate,
      weakToStrong]
    exact congrArg
      (referenceScheme.underlying.presheaf.map (homOfLE le_top).op)
      (weakGlobalEquation_atomMap a)
  semantic_monotone := by
    intro T s i hs
    cases i
    change (GeometricLawReading.ofSemanticCore referenceRaw referenceScheme
      weakLawEquationCore weakSchemeBridge).HoldsOn s PUnit.unit
    rw [GeometricLawReading.ofSemanticCore_holdsOn]
    change (GeometricLawReading.ofSemanticCore referenceRaw referenceScheme
      strongLawEquationCore strongSchemeBridge).HoldsOn s PUnit.unit at hs
    rw [GeometricLawReading.ofSemanticCore_holdsOn] at hs
    intro a
    rw [weakGlobalEquation_atomMap]
    exact hs (weakToStrongAtomMap a)

/-- The strong lawful locus maps contravariantly to the weak lawful locus. -/
noncomputable def lawComparison :
    strongLocus ⟶ weakLocus :=
  lawfulClosedSubschemeMap
    referenceRaw referenceScheme
    weakReading_valid strongReading_valid
    weakReading_requiredClosed strongReading_requiredClosed
    weakToStrong weakToStrong_valid

/-- The weak-to-strong comparison is the canonical law-inclusion map. -/
@[simp] theorem lawComparison_eq :
    lawComparison =
      lawfulClosedSubschemeMap
        referenceRaw referenceScheme
        weakReading_valid strongReading_valid
        weakReading_requiredClosed strongReading_requiredClosed
        weakToStrong weakToStrong_valid :=
  rfl

/-- The weak-to-strong law comparison is a closed immersion. -/
theorem lawComparison_isClosedImmersion :
    AlgebraicGeometry.IsClosedImmersion lawComparison :=
  lawfulClosedSubschemeMap_isClosedImmersion
    referenceRaw referenceScheme
    weakReading_valid strongReading_valid
    weakReading_requiredClosed strongReading_requiredClosed
    weakToStrong weakToStrong_valid

/-- The weak-to-strong law comparison commutes with the ambient immersions. -/
theorem lawComparison_immersion :
    lawComparison ≫ weakImmersion = strongImmersion :=
  lawfulClosedSubschemeMap_immersion
    referenceRaw referenceScheme
    weakReading_valid strongReading_valid
    weakReading_requiredClosed strongReading_requiredClosed
    weakToStrong weakToStrong_valid

/-- Strictness of the weak and strong ideals makes the comparison non-isomorphic. -/
theorem lawComparison_not_isIso :
    ¬ IsIso lawComparison := by
  intro hIso
  letI : IsIso lawComparison := hIso
  have hker := Scheme.Hom.ker_comp_of_isIso lawComparison weakImmersion
  have hsheaf : strongIdealSheaf = weakIdealSheaf := by
    calc
      strongIdealSheaf = strongImmersion.ker := strongImmersion_ker.symm
      _ = (lawComparison ≫ weakImmersion).ker := by rw [lawComparison_immersion]
      _ = weakImmersion.ker := hker
      _ = weakIdealSheaf := weakImmersion_ker
  exact (ne_of_lt weakIdeal_lt_strongIdeal) hsheaf.symm

/-- The concrete atom map from the strong reading to the rigid reading. -/
def strongToRigidAtomMap
    (a : AAT.AG.FiniteModel.carrier.Atom) :
    AAT.AG.FiniteModel.carrier.Atom :=
  if a = AAT.AG.FiniteModel.FiniteAtom.componentA then
    AAT.AG.FiniteModel.FiniteAtom.componentA
  else if a = AAT.AG.FiniteModel.FiniteAtom.componentB then
    AAT.AG.FiniteModel.FiniteAtom.componentB
  else
    AAT.AG.FiniteModel.FiniteAtom.dependsAB

/-- The strong-to-rigid atom map is fixed on every input. -/
@[simp] theorem strongToRigidAtomMap_eq
    (a : AAT.AG.FiniteModel.carrier.Atom) :
    strongToRigidAtomMap a =
      if a = AAT.AG.FiniteModel.FiniteAtom.componentA then
        AAT.AG.FiniteModel.FiniteAtom.componentA
      else if a = AAT.AG.FiniteModel.FiniteAtom.componentB then
        AAT.AG.FiniteModel.FiniteAtom.componentB
      else
        AAT.AG.FiniteModel.FiniteAtom.dependsAB :=
  rfl

private theorem strongGlobalEquation_atomMap
    (a : AAT.AG.FiniteModel.carrier.Atom) :
    semanticCoreGlobalEquation referenceRaw referenceScheme
        strongLawEquationCore strongSchemeBridge PUnit.unit a =
      semanticCoreGlobalEquation referenceRaw referenceScheme
        rigidLawEquationCore rigidSchemeBridge PUnit.unit
          (strongToRigidAtomMap a) := by
  apply (ConcreteCategory.bijective_of_isIso
    ambientGlobalSectionsIso.hom).1
  rw [strongGlobalEquation_eq, rigidGlobalEquation_eq]
  cases a <;> simp [strongToRigidAtomMap]

/-- The concrete primitive inclusion from strong laws to rigid laws. -/
def strongToRigid :
    ClosedEquationalLawInclusion
      referenceRaw referenceScheme strongReading rigidReading where
  lawMap := id
  atomMap := fun _ => strongToRigidAtomMap

/-- The strong-to-rigid inclusion preserves the sole law index. -/
@[simp] theorem strongToRigid_lawMap :
    strongToRigid.lawMap = id :=
  rfl

/-- The strong-to-rigid inclusion uses the concrete atom map. -/
@[simp] theorem strongToRigid_atomMap :
    strongToRigid.atomMap PUnit.unit = strongToRigidAtomMap :=
  rfl

/-- The strong-to-rigid inclusion preserves required laws, witnesses, and semantics. -/
theorem strongToRigid_valid :
    IsClosedEquationalLawInclusion
      referenceRaw referenceScheme strongToRigid where
  required_map := fun i hi => by simpa [strongToRigid] using hi
  closed_map := by
    intro i _
    change strongToRigid.lawMap i ∈
      (Set.univ : Set rigidLawEquationCore.Index)
    exact Set.mem_univ _
  selected_map := by
    intro _V i _
    change strongToRigid.lawMap i ∈
      (Set.univ : Set rigidLawEquationCore.Index)
    exact Set.mem_univ _
  coordinate_eq := by
    intro i hi V a
    cases i
    simp only [strongReading, rigidReading,
      ClosedEquationalLawReading.ofSemanticCore_witness,
      ClosedEquationalLawWitness.ofSemanticCore,
      ClosedEquationalLawWitness.ofGlobalSections_coordinate,
      strongToRigid]
    exact congrArg
      (referenceScheme.underlying.presheaf.map (homOfLE le_top).op)
      (strongGlobalEquation_atomMap a)
  semantic_monotone := by
    intro T s i hs
    cases i
    change (GeometricLawReading.ofSemanticCore referenceRaw referenceScheme
      strongLawEquationCore strongSchemeBridge).HoldsOn s PUnit.unit
    rw [GeometricLawReading.ofSemanticCore_holdsOn]
    change (GeometricLawReading.ofSemanticCore referenceRaw referenceScheme
      rigidLawEquationCore rigidSchemeBridge).HoldsOn s PUnit.unit at hs
    rw [GeometricLawReading.ofSemanticCore_holdsOn] at hs
    intro a
    rw [strongGlobalEquation_atomMap]
    exact hs (strongToRigidAtomMap a)

/-- The rigid lawful locus maps contravariantly to the strong lawful locus. -/
noncomputable def strongToRigidComparison :
    rigidLocus ⟶ strongLocus :=
  lawfulClosedSubschemeMap
    referenceRaw referenceScheme
    strongReading_valid rigidReading_valid
    strongReading_requiredClosed rigidReading_requiredClosed
    strongToRigid strongToRigid_valid

/-- The strong-to-rigid comparison is the canonical law-inclusion map. -/
@[simp] theorem strongToRigidComparison_eq :
    strongToRigidComparison =
      lawfulClosedSubschemeMap
        referenceRaw referenceScheme
        strongReading_valid rigidReading_valid
        strongReading_requiredClosed rigidReading_requiredClosed
        strongToRigid strongToRigid_valid :=
  rfl

/-- The strong-to-rigid law comparison is a closed immersion. -/
theorem strongToRigidComparison_isClosedImmersion :
    AlgebraicGeometry.IsClosedImmersion strongToRigidComparison :=
  lawfulClosedSubschemeMap_isClosedImmersion
    referenceRaw referenceScheme
    strongReading_valid rigidReading_valid
    strongReading_requiredClosed rigidReading_requiredClosed
    strongToRigid strongToRigid_valid

/-- The strong-to-rigid comparison commutes with the ambient immersions. -/
theorem strongToRigidComparison_immersion :
    strongToRigidComparison ≫ strongImmersion = rigidImmersion :=
  lawfulClosedSubschemeMap_immersion
    referenceRaw referenceScheme
    strongReading_valid rigidReading_valid
    strongReading_requiredClosed rigidReading_requiredClosed
    strongToRigid strongToRigid_valid

/-- Strictness of the strong and rigid ideals makes the comparison non-isomorphic. -/
theorem strongToRigidComparison_not_isIso :
    ¬ IsIso strongToRigidComparison := by
  intro hIso
  letI : IsIso strongToRigidComparison := hIso
  have hker := Scheme.Hom.ker_comp_of_isIso
    strongToRigidComparison strongImmersion
  have hsheaf : rigidIdealSheaf = strongIdealSheaf := by
    calc
      rigidIdealSheaf = rigidImmersion.ker := rigidImmersion_ker.symm
      _ = (strongToRigidComparison ≫ strongImmersion).ker := by
        rw [strongToRigidComparison_immersion]
      _ = strongImmersion.ker := hker
      _ = strongIdealSheaf := strongImmersion_ker
  exact (ne_of_lt strongIdeal_lt_rigidIdeal) hsheaf.symm

/-- The composite inclusion from weak laws to rigid laws. -/
def weakToRigid :
    ClosedEquationalLawInclusion
      referenceRaw referenceScheme weakReading rigidReading :=
  weakToStrong.comp referenceRaw referenceScheme strongToRigid

/-- The weak-to-rigid inclusion is the generic composite inclusion. -/
@[simp] theorem weakToRigid_eq :
    weakToRigid =
      weakToStrong.comp referenceRaw referenceScheme strongToRigid :=
  rfl

/-- Validity of the weak-to-rigid inclusion is inherited from generic composition. -/
theorem weakToRigid_valid :
    IsClosedEquationalLawInclusion
      referenceRaw referenceScheme weakToRigid :=
  ClosedEquationalLawInclusion.comp_valid
    referenceRaw referenceScheme weakToStrong strongToRigid
    weakToStrong_valid strongToRigid_valid

/-- The rigid lawful locus maps directly to the weak lawful locus. -/
noncomputable def weakToRigidComparison :
    rigidLocus ⟶ weakLocus :=
  lawfulClosedSubschemeMap
    referenceRaw referenceScheme
    weakReading_valid rigidReading_valid
    weakReading_requiredClosed rigidReading_requiredClosed
    weakToRigid weakToRigid_valid

/-- The weak-to-rigid comparison is the canonical composite-inclusion map. -/
@[simp] theorem weakToRigidComparison_eq :
    weakToRigidComparison =
      lawfulClosedSubschemeMap
        referenceRaw referenceScheme
        weakReading_valid rigidReading_valid
        weakReading_requiredClosed rigidReading_requiredClosed
        weakToRigid weakToRigid_valid :=
  rfl

/-- The identity law inclusion induces the identity map of the weak locus. -/
theorem lawComparison_id_fires :
    lawfulClosedSubschemeMap
        referenceRaw referenceScheme
        weakReading_valid weakReading_valid
        weakReading_requiredClosed weakReading_requiredClosed
        (ClosedEquationalLawInclusion.refl
          referenceRaw referenceScheme weakReading)
        (ClosedEquationalLawInclusion.refl_valid
          referenceRaw referenceScheme weakReading) =
      𝟙 weakLocus :=
  lawfulClosedSubschemeMap_id referenceRaw referenceScheme
    weakReading weakReading_valid weakReading_requiredClosed

/-- The two non-isomorphic comparison legs compose by the generic law-inclusion theorem. -/
theorem lawComparison_comp_fires :
    strongToRigidComparison ≫ lawComparison = weakToRigidComparison :=
  lawfulClosedSubschemeMap_comp
    referenceRaw referenceScheme
    weakReading_valid strongReading_valid rigidReading_valid
    weakReading_requiredClosed strongReading_requiredClosed
    rigidReading_requiredClosed
    weakToStrong strongToRigid weakToStrong_valid strongToRigid_valid


end
end AAT.AG.Examples.StandardGeometryReferenceModels
