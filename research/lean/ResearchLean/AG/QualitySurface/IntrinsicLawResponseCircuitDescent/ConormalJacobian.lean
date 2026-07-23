import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import ResearchLean.AG.QualitySurface.IntrinsicLawResponseCircuitDescent.OperationImageSheaf
import ResearchLean.AG.QualitySurface.LawGeneratedIdealPowerSequence

/-!
# Conormal Jacobian and law-generated labeled responses

This file constructs the J4 conormal response from quotient-valued derivations.
The response descends to `I / I²` by the Leibniz rule, and is linear over the
law quotient.  Evaluation at a required law/Atom class is performed before
tilde, producing a morphism from the allowed-operation image sheaf to the
structure module.  The objectwise duals are not asserted to form an internal
Hom sheaf.

The labeled conormal class is generated from the existing
`violationCoordinate`; neither a representative nor a response evaluator is
accepted as input.  Kernel characterization and labeled generation are later
J5 obligations.
-/

open CategoryTheory
open TopologicalSpace
open scoped AlgebraicGeometry

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000

namespace ResearchLean.AG.QualitySurface.IntrinsicLawResponseCircuitDescent

universe uk uA uOp uChart uState uBefore uAfter u

namespace QuotientValuedDerivation

variable {k : Type uk} {A : Type uA}
variable [Field k] [CommRing A] [Algebra k A]

/-- A quotient-valued derivation restricts to an ambient-linear map on the law ideal. -/
noncomputable def idealResponse (I : Ideal A)
    (d : Derivation k A (A ⧸ I)) : I →ₗ[A] A ⧸ I where
  toFun x := d x
  map_add' := fun x y ↦ d.map_add x y
  map_smul' := by
    intro a x
    change d (a * x) = Ideal.Quotient.mk I a • d x
    rw [Derivation.leibniz]
    have hx : (x : A) • d a = 0 := by
      rw [Algebra.smul_def]
      change Ideal.Quotient.mk I x * d a = 0
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr x.property, zero_mul]
    rw [hx, add_zero]
    rfl

/-- The ambient-linear conormal response before quotient scalar extension. -/
noncomputable def conormalResponseA (I : Ideal A)
    (d : Derivation k A (A ⧸ I)) : I.Cotangent →ₗ[A] A ⧸ I :=
  Submodule.liftQ (I • ⊤ : Submodule A I)
    (idealResponse I d) (by
      intro x hx
      rw [LinearMap.mem_ker]
      refine Submodule.smul_induction_on hx ?_ ?_
      · intro a ha y _hy
        change d (a * y) = 0
        rw [Derivation.leibniz]
        have ha0 : a • d y = 0 := by
          rw [Algebra.smul_def]
          change Ideal.Quotient.mk I a * d y = 0
          rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha, zero_mul]
        have hy0 : (y : A) • d a = 0 := by
          rw [Algebra.smul_def]
          change Ideal.Quotient.mk I y * d a = 0
          rw [Ideal.Quotient.eq_zero_iff_mem.mpr y.property, zero_mul]
        rw [ha0, hy0, zero_add]
      · intro x y hx hy
        change d (x + y) = 0
        rw [map_add]
        change d x + d y = 0
        rw [show d x = 0 from hx, show d y = 0 from hy, add_zero])

/-- The full conormal response `I / I² → (A / I)` of a quotient-valued derivation. -/
noncomputable def conormalResponse (I : Ideal A)
    (d : Derivation k A (A ⧸ I)) :
    I.Cotangent →ₗ[A ⧸ I] A ⧸ I :=
  (conormalResponseA I d).extendScalarsOfSurjective
    Ideal.Quotient.mk_surjective

@[simp] theorem conormalResponse_toCotangent (I : Ideal A)
    (d : Derivation k A (A ⧸ I)) (x : I) :
    conormalResponse I d (I.toCotangent x) = d x := rfl

/-- The full conormal Jacobian, linear in the quotient-valued derivation. -/
noncomputable def conormalResponseLinear (I : Ideal A) :
    Derivation k A (A ⧸ I) →ₗ[A ⧸ I]
      Module.Dual (A ⧸ I) I.Cotangent where
  toFun := conormalResponse I
  map_add' := fun d e ↦ by
    ext x
    obtain ⟨x, rfl⟩ := I.toCotangent_surjective x
    simp
  map_smul' := fun r d ↦ by
    ext x
    obtain ⟨x, rfl⟩ := I.toCotangent_surjective x
    simp

@[simp] theorem conormalResponseLinear_apply_toCotangent (I : Ideal A)
    (d : Derivation k A (A ⧸ I)) (x : I) :
    conormalResponseLinear (k := k) I d (I.toCotangent x) = d x := rfl

end QuotientValuedDerivation

namespace TypedLocalizationGeometry

variable {k : Type uk} {A : Type uA} {Chart : Type uChart}
variable [Field k] [CommRing A] [Algebra k A] [Fintype Chart]

/-- The ambient conormal-dual module. -/
abbrev ambientConormalDualModule (I : Ideal A) :=
  ModuleCat.of (ambientLawQuotient I)
    (Module.Dual (ambientLawQuotient I) I.Cotangent)

/-- The ambient full conormal Jacobian as a module morphism. -/
noncomputable def ambientConormalJacobian (I : Ideal A) :
    ambientDerivationModule (k := k) I ⟶ ambientConormalDualModule I :=
  ModuleCat.ofHom (QuotientValuedDerivation.conormalResponseLinear (k := k) I)

/-- Evaluation of the ambient conormal dual at one generated conormal class. -/
noncomputable def ambientConormalEvaluation (I : Ideal A) (c : I.Cotangent) :
    ambientConormalDualModule I ⟶
      ModuleCat.of (ambientLawQuotient I) (ambientLawQuotient I) :=
  ModuleCat.ofHom (LinearMap.applyₗ (R := ambientLawQuotient I) c)

/-- The ambient labeled response, factored through the full conormal Jacobian. -/
noncomputable def ambientLabeledResponse (I : Ideal A) (c : I.Cotangent) :
    ambientDerivationModule (k := k) I ⟶
      ModuleCat.of (ambientLawQuotient I) (ambientLawQuotient I) :=
  ambientConormalJacobian (k := k) I ≫ ambientConormalEvaluation I c

@[simp] theorem ambientLabeledResponse_toCotangent
    (I : Ideal A) (d : Derivation k A (ambientLawQuotient I)) (x : I) :
    (ambientLabeledResponse (k := k) I (I.toCotangent x)).hom d = d x := rfl

/-- The ambient labeled response after tilde. -/
noncomputable def ambientLabeledResponseSheaf (I : Ideal A) (c : I.Cotangent) :
    ambientDerivationSheaf (k := k) I ⟶
      SheafOfModules.unit ((ambientLawSpec I).ringCatSheaf) :=
  AlgebraicGeometry.tilde.map (ambientLabeledResponse (k := k) I c) ≫
    (AlgebraicGeometry.tildeSelf
      (R := CommRingCat.of (ambientLawQuotient I))).hom

/-- Transport restricted ambient structure sections to the lawful-space structure module. -/
noncomputable def restrictedStructureModuleMap
    (G : TypedLocalizationGeometry k A Chart) (I : Ideal A) :
    (AlgebraicGeometry.Scheme.Modules.restrictFunctor (G.lawfulOpen I).ι).obj
        (SheafOfModules.unit ((ambientLawSpec I).ringCatSheaf)) ⟶
      SheafOfModules.unit ((G.lawfulSpace I).ringCatSheaf) where
  val.app U := ModuleCat.homMk
    ((forget₂ RingCat AddCommGrpCat).map
      ((forget₂ CommRingCat RingCat).map
        ((G.lawfulOpen I).ι.appIso U.unop).hom)) (by
      intro r
      ext s
      change (show Γ(G.lawfulSpace I, U.unop) from r) *
          (show Γ(G.lawfulSpace I, U.unop) from
            ((G.lawfulOpen I).ι.appIso U.unop).hom s) =
        ((G.lawfulOpen I).ι.appIso U.unop).hom
          (((G.lawfulOpen I).ι.appIso U.unop).inv r *
            (show Γ(ambientLawSpec I,
              (G.lawfulOpen I).ι ''ᵁ U.unop) from s))
      rw [map_mul, Iso.inv_hom_id_apply])
  val.naturality f := by
    rename_i X Y
    ext s
    apply ((G.lawfulOpen I).ι.appIso Y.unop).commRingCatIsoToRingEquiv.symm.injective
    simpa using congr($((G.lawfulOpen I).ι.appIso_inv_naturality f).hom
      (((G.lawfulOpen I).ι.appIso X.unop).hom s))

@[simp] theorem restrictedStructureModuleMap_app
    (G : TypedLocalizationGeometry k A Chart) (I : Ideal A)
    (U : (G.lawfulSpace I).Opens)
    (s : Γ(SheafOfModules.unit ((ambientLawSpec I).ringCatSheaf),
      (G.lawfulOpen I).ι ''ᵁ U)) :
    (G.restrictedStructureModuleMap I).app U s =
      ((G.lawfulOpen I).ι.appIso U).hom s := rfl

/-- Restrict one ambient labeled response to the generated lawful space. -/
noncomputable def coefficientLabeledResponse
    (G : TypedLocalizationGeometry k A Chart) (I : Ideal A) (c : I.Cotangent) :
    G.derivationCoefficientSheaf I ⟶
      SheafOfModules.unit ((G.lawfulSpace I).ringCatSheaf) :=
  (AlgebraicGeometry.Scheme.Modules.restrictFunctor (G.lawfulOpen I).ι).map
      (ambientLabeledResponseSheaf (k := k) I c) ≫
    G.restrictedStructureModuleMap I

/-- The structure-module section map on a selected chart is localization. -/
noncomputable def chartStructureToOpenIsLocalized
    (G : TypedLocalizationGeometry k A Chart) (I : Ideal A) (i : Chart) :
    IsLocalizedModule
      (Submonoid.powers (Ideal.Quotient.mk I (G.denominator i)))
      (AlgebraicGeometry.tilde.toOpen
        (R := CommRingCat.of (ambientLawQuotient I))
        (ModuleCat.of (ambientLawQuotient I) (ambientLawQuotient I))
        (G.lawfulChartOpen I i)).hom := by
  letI : IsLocalizedModule
    (Submonoid.powers (Ideal.Quotient.mk I (G.denominator i)))
    (AlgebraicGeometry.StructureSheaf.toOpenₗ (ambientLawQuotient I)
      (ModuleCat.of (ambientLawQuotient I) (ambientLawQuotient I))
      (G.lawfulChartOpen I i)) := by
    change IsLocalizedModule
      (Submonoid.powers (Ideal.Quotient.mk I (G.denominator i)))
      (AlgebraicGeometry.StructureSheaf.toOpenₗ (ambientLawQuotient I)
        (ModuleCat.of (ambientLawQuotient I) (ambientLawQuotient I))
        (PrimeSpectrum.basicOpen
          (Ideal.Quotient.mk I (G.denominator i))))
    infer_instance
  exact IsLocalizedModule.of_linearEquiv
    (Submonoid.powers (Ideal.Quotient.mk I (G.denominator i)))
    (AlgebraicGeometry.StructureSheaf.toOpenₗ (ambientLawQuotient I)
      (ModuleCat.of (ambientLawQuotient I) (ambientLawQuotient I))
      (G.lawfulChartOpen I i))
    ((AlgebraicGeometry.tilde.modulesSpecToSheafIso
      (R := CommRingCat.of (ambientLawQuotient I))
      (ModuleCat.of (ambientLawQuotient I) (ambientLawQuotient I))).app
        (.op (G.lawfulChartOpen I i))).toLinearEquiv.symm

/-- Read a structure-module section on a selected chart in the canonical chart quotient. -/
noncomputable def chartStructureSectionToLawQuotient
    (G : TypedLocalizationGeometry k A Chart) (I : Ideal A) (i : Chart) :
    letI : Algebra (ambientLawQuotient I) (G.chartLawQuotient I i) :=
      (G.chartLawQuotientMap I i).toRingHom.toAlgebra
    (AlgebraicGeometry.modulesSpecToSheaf.obj
      (SheafOfModules.unit ((ambientLawSpec I).ringCatSheaf))).presheaf.obj
        (.op (G.lawfulChartOpen I i)) →ₗ[ambientLawQuotient I]
      G.chartLawQuotient I i := by
  letI : Algebra (ambientLawQuotient I) (G.chartLawQuotient I i) :=
    (G.chartLawQuotientMap I i).toRingHom.toAlgebra
  let source := AlgebraicGeometry.tilde.toOpen
    (R := CommRingCat.of (ambientLawQuotient I))
    (ModuleCat.of (ambientLawQuotient I) (ambientLawQuotient I))
    (G.lawfulChartOpen I i)
  letI : IsLocalizedModule
      (Submonoid.powers (Ideal.Quotient.mk I (G.denominator i))) source.hom :=
    G.chartStructureToOpenIsLocalized I i
  apply IsLocalizedModule.lift
    (Submonoid.powers (Ideal.Quotient.mk I (G.denominator i))) source.hom
    (Algebra.linearMap (ambientLawQuotient I) (G.chartLawQuotient I i))
  intro s
  rw [← (Algebra.lsmul (ambientLawQuotient I)
    (A := G.chartLawQuotient I i) (ambientLawQuotient I)
    (G.chartLawQuotient I i)).commutes]
  rcases s.2 with ⟨n, hn⟩
  rw [← hn, map_pow]
  exact (G.isUnit_chartLawQuotientMap_denominator I i).pow n |>.map _

@[simp] theorem chartStructureSectionToLawQuotient_toOpen
    (G : TypedLocalizationGeometry k A Chart) (I : Ideal A) (i : Chart)
    (r : ambientLawQuotient I) :
    G.chartStructureSectionToLawQuotient I i
        ((AlgebraicGeometry.tilde.toOpen
          (R := CommRingCat.of (ambientLawQuotient I))
          (ModuleCat.of (ambientLawQuotient I) (ambientLawQuotient I))
          (G.lawfulChartOpen I i)) r) =
      G.chartLawQuotientMap I i r := by
  letI : Algebra (ambientLawQuotient I) (G.chartLawQuotient I i) :=
    (G.chartLawQuotientMap I i).toRingHom.toAlgebra
  letI : IsLocalizedModule
      (Submonoid.powers (Ideal.Quotient.mk I (G.denominator i)))
      (AlgebraicGeometry.tilde.toOpen
        (R := CommRingCat.of (ambientLawQuotient I))
        (ModuleCat.of (ambientLawQuotient I) (ambientLawQuotient I))
        (G.lawfulChartOpen I i)).hom :=
    G.chartStructureToOpenIsLocalized I i
  unfold chartStructureSectionToLawQuotient
  apply IsLocalizedModule.lift_apply

/-- Read a lawful-space structure-module section on a selected chart in its quotient ring. -/
noncomputable def chartStructureSectionToLawQuotientOnSpace
    (G : TypedLocalizationGeometry k A Chart) (I : Ideal A) (i : Chart)
    (s : Γ(SheafOfModules.unit ((G.lawfulSpace I).ringCatSheaf),
      G.lawfulChartOpenOnSpace I i)) :
    G.chartLawQuotient I i :=
  G.chartStructureSectionToLawQuotient I i
    ((SheafOfModules.unit ((ambientLawSpec I).ringCatSheaf)).val.map
      (eqToHom (G.image_lawfulChartOpenOnSpace I i).symm).op
      (((G.lawfulOpen I).ι.appIso
        (G.lawfulChartOpenOnSpace I i)).inv s))

theorem chartStructureSectionToLawQuotientOnSpace_coefficientLabeledResponse
    (G : TypedLocalizationGeometry k A Chart) (I : Ideal A) (i : Chart)
    (c : I.Cotangent)
    (s : Γ(G.derivationCoefficientSheaf I, G.lawfulChartOpenOnSpace I i)) :
    G.chartStructureSectionToLawQuotientOnSpace I i
        ((G.coefficientLabeledResponse I c).app
          (G.lawfulChartOpenOnSpace I i) s) =
      G.chartStructureSectionToLawQuotient I i
        ((ambientLabeledResponseSheaf (k := k) I c).app (G.lawfulChartOpen I i)
          ((ambientDerivationSheaf (k := k) I).presheaf.map
            (eqToHom (G.image_lawfulChartOpenOnSpace I i).symm).op s)) := by
  unfold chartStructureSectionToLawQuotientOnSpace
  apply congrArg (G.chartStructureSectionToLawQuotient I i)
  simpa [coefficientLabeledResponse, restrictedStructureModuleMap] using
    (PresheafOfModules.naturality_apply
      (ambientLabeledResponseSheaf (k := k) I c).val
      (eqToHom (G.image_lawfulChartOpenOnSpace I i).symm).op s).symm

/-- On a selected chart, the sheafified evaluation is the localized full Jacobian evaluation. -/
theorem chartAmbientLabeledResponse_eq_conormalResponse
    (G : TypedLocalizationGeometry k A Chart) (I : Ideal A) (i : Chart)
    (x : I)
    (s : (AlgebraicGeometry.modulesSpecToSheaf.obj
      (ambientDerivationSheaf (k := k) I)).presheaf.obj
        (.op (G.lawfulChartOpen I i))) :
    G.chartStructureSectionToLawQuotient I i
        ((ambientLabeledResponseSheaf (k := k) I (I.toCotangent x)).app
          (G.lawfulChartOpen I i) s) =
      QuotientValuedDerivation.conormalResponse (G.chartLawIdeal I i)
        (G.chartSectionToDerivation I i s)
        ((G.chartLawIdeal I i).toCotangent
          ⟨algebraMap A (G.chartRing i) x,
            Ideal.mem_map_of_mem (algebraMap A (G.chartRing i)) x.property⟩) := by
  letI : Algebra (ambientLawQuotient I) (G.chartLawQuotient I i) :=
    (G.chartLawQuotientMap I i).toRingHom.toAlgebra
  let source := AlgebraicGeometry.tilde.toOpen
    (ambientDerivationModule (k := k) I) (G.lawfulChartOpen I i)
  letI : IsLocalizedModule
      (Submonoid.powers (Ideal.Quotient.mk I (G.denominator i))) source.hom :=
    G.chartToOpenIsLocalized I i
  let localClass : (G.chartLawIdeal I i).Cotangent :=
    (G.chartLawIdeal I i).toCotangent
      ⟨algebraMap A (G.chartRing i) x,
        Ideal.mem_map_of_mem (algebraMap A (G.chartRing i)) x.property⟩
  let responseMap :
      (AlgebraicGeometry.modulesSpecToSheaf.obj
        (ambientDerivationSheaf (k := k) I)).presheaf.obj
          (.op (G.lawfulChartOpen I i)) →ₗ[ambientLawQuotient I]
        G.chartLawQuotient I i :=
    (G.chartStructureSectionToLawQuotient I i).comp
      ((AlgebraicGeometry.modulesSpecToSheaf.map
        (ambientLabeledResponseSheaf (k := k) I (I.toCotangent x))).1.app
          (.op (G.lawfulChartOpen I i))).hom
  let jacobianMap :
      (AlgebraicGeometry.modulesSpecToSheaf.obj
        (ambientDerivationSheaf (k := k) I)).presheaf.obj
          (.op (G.lawfulChartOpen I i)) →ₗ[ambientLawQuotient I]
        G.chartLawQuotient I i :=
    (((LinearMap.applyₗ (R := G.chartLawQuotient I i) localClass).comp
      (QuotientValuedDerivation.conormalResponseLinear (k := k)
        (G.chartLawIdeal I i))).restrictScalars
          (ambientLawQuotient I)).comp (G.chartSectionToDerivation I i)
  change responseMap s = jacobianMap s
  apply LinearMap.congr_fun
  apply IsLocalizedModule.ext
    (Submonoid.powers (Ideal.Quotient.mk I (G.denominator i))) source.hom
  · intro denominator
    rw [← (Algebra.lsmul (ambientLawQuotient I)
      (A := G.chartLawQuotient I i) (ambientLawQuotient I)
      (G.chartLawQuotient I i)).commutes]
    rcases denominator.2 with ⟨n, hn⟩
    rw [← hn, map_pow]
    exact (G.isUnit_chartLawQuotientMap_denominator I i).pow n |>.map _
  · ext d
    simp [responseMap, jacobianMap, localClass, ambientLabeledResponseSheaf,
      ambientLabeledResponse, ambientConormalJacobian, ambientConormalEvaluation,
      AlgebraicGeometry.tildeSelf]
    have hmap := congr($(AlgebraicGeometry.tilde.toOpen_map_app
      (ModuleCat.ofHom (QuotientValuedDerivation.conormalResponseLinear
        (k := k) I) ≫
        ModuleCat.ofHom (LinearMap.applyₗ (R := ambientLawQuotient I)
          (I.toCotangent x))) (G.lawfulChartOpen I i)) d)
    rw [ModuleCat.comp_apply, ModuleCat.comp_apply] at hmap
    dsimp [source]
    refine (congrArg (G.chartStructureSectionToLawQuotient I i) hmap).trans ?_
    rw [G.chartStructureSectionToLawQuotient_toOpen]
    calc
      G.chartLawQuotientMap I i
          ((ModuleCat.ofHom (QuotientValuedDerivation.conormalResponseLinear
            (k := k) I) ≫
            ModuleCat.ofHom (LinearMap.applyₗ (R := ambientLawQuotient I)
              (I.toCotangent x))).hom d) =
        G.chartLawQuotientMap I i (d x) := rfl
      _ = G.chartAmbientComparison I i d
          (algebraMap A (G.chartRing i) x) :=
        (G.chartAmbientComparison_algebraMap I i d x).symm
      _ = G.chartSectionToDerivation I i
          ((AlgebraicGeometry.tilde.toOpen
            (ambientDerivationModule (k := k) I)
            (G.lawfulChartOpen I i)) d)
          (algebraMap A (G.chartRing i) x) :=
        congrArg (fun e ↦ e (algebraMap A (G.chartRing i) x))
          (G.chartSectionToDerivation_toOpen I i d).symm

/-- The structure-module section map on a selected overlap is localization. -/
noncomputable def overlapStructureToOpenIsLocalized
    (G : TypedLocalizationGeometry k A Chart) (I : Ideal A) (i j : Chart) :
    IsLocalizedModule
      (Submonoid.powers
        (Ideal.Quotient.mk I (G.denominator i * G.denominator j)))
      (AlgebraicGeometry.tilde.toOpen
        (R := CommRingCat.of (ambientLawQuotient I))
        (ModuleCat.of (ambientLawQuotient I) (ambientLawQuotient I))
        (G.lawfulOverlapOpen I i j)).hom := by
  letI : IsLocalizedModule
      (Submonoid.powers
        (Ideal.Quotient.mk I (G.denominator i * G.denominator j)))
      (AlgebraicGeometry.StructureSheaf.toOpenₗ (ambientLawQuotient I)
        (ModuleCat.of (ambientLawQuotient I) (ambientLawQuotient I))
        (G.lawfulOverlapOpen I i j)) := by
    change IsLocalizedModule
      (Submonoid.powers
        (Ideal.Quotient.mk I (G.denominator i * G.denominator j)))
      (AlgebraicGeometry.StructureSheaf.toOpenₗ (ambientLawQuotient I)
        (ModuleCat.of (ambientLawQuotient I) (ambientLawQuotient I))
        (PrimeSpectrum.basicOpen
          (Ideal.Quotient.mk I (G.denominator i * G.denominator j))))
    infer_instance
  exact IsLocalizedModule.of_linearEquiv
    (Submonoid.powers
      (Ideal.Quotient.mk I (G.denominator i * G.denominator j)))
    (AlgebraicGeometry.StructureSheaf.toOpenₗ (ambientLawQuotient I)
      (ModuleCat.of (ambientLawQuotient I) (ambientLawQuotient I))
      (G.lawfulOverlapOpen I i j))
    ((AlgebraicGeometry.tilde.modulesSpecToSheafIso
      (R := CommRingCat.of (ambientLawQuotient I))
      (ModuleCat.of (ambientLawQuotient I) (ambientLawQuotient I))).app
        (.op (G.lawfulOverlapOpen I i j))).toLinearEquiv.symm

/-- Read a structure-module section on an overlap in the canonical overlap quotient. -/
noncomputable def overlapStructureSectionToLawQuotient
    (G : TypedLocalizationGeometry k A Chart) (I : Ideal A) (i j : Chart) :
    letI : Algebra (ambientLawQuotient I) (G.overlapLawQuotient I i j) :=
      (G.overlapLawQuotientMap I i j).toRingHom.toAlgebra
    (AlgebraicGeometry.modulesSpecToSheaf.obj
      (SheafOfModules.unit ((ambientLawSpec I).ringCatSheaf))).presheaf.obj
        (.op (G.lawfulOverlapOpen I i j)) →ₗ[ambientLawQuotient I]
      G.overlapLawQuotient I i j := by
  letI : Algebra (ambientLawQuotient I) (G.overlapLawQuotient I i j) :=
    (G.overlapLawQuotientMap I i j).toRingHom.toAlgebra
  let source := AlgebraicGeometry.tilde.toOpen
    (R := CommRingCat.of (ambientLawQuotient I))
    (ModuleCat.of (ambientLawQuotient I) (ambientLawQuotient I))
    (G.lawfulOverlapOpen I i j)
  letI : IsLocalizedModule
      (Submonoid.powers
        (Ideal.Quotient.mk I (G.denominator i * G.denominator j))) source.hom :=
    G.overlapStructureToOpenIsLocalized I i j
  apply IsLocalizedModule.lift
    (Submonoid.powers
      (Ideal.Quotient.mk I (G.denominator i * G.denominator j))) source.hom
    (Algebra.linearMap (ambientLawQuotient I) (G.overlapLawQuotient I i j))
  intro s
  rw [← (Algebra.lsmul (ambientLawQuotient I)
    (A := G.overlapLawQuotient I i j) (ambientLawQuotient I)
    (G.overlapLawQuotient I i j)).commutes]
  rcases s.2 with ⟨n, hn⟩
  rw [← hn, map_pow]
  exact (G.isUnit_overlapLawQuotientMap_denominator I i j).pow n |>.map _

@[simp] theorem overlapStructureSectionToLawQuotient_toOpen
    (G : TypedLocalizationGeometry k A Chart) (I : Ideal A) (i j : Chart)
    (r : ambientLawQuotient I) :
    G.overlapStructureSectionToLawQuotient I i j
        ((AlgebraicGeometry.tilde.toOpen
          (R := CommRingCat.of (ambientLawQuotient I))
          (ModuleCat.of (ambientLawQuotient I) (ambientLawQuotient I))
          (G.lawfulOverlapOpen I i j)) r) =
      G.overlapLawQuotientMap I i j r := by
  letI : Algebra (ambientLawQuotient I) (G.overlapLawQuotient I i j) :=
    (G.overlapLawQuotientMap I i j).toRingHom.toAlgebra
  letI : IsLocalizedModule
      (Submonoid.powers
        (Ideal.Quotient.mk I (G.denominator i * G.denominator j)))
      (AlgebraicGeometry.tilde.toOpen
        (R := CommRingCat.of (ambientLawQuotient I))
        (ModuleCat.of (ambientLawQuotient I) (ambientLawQuotient I))
        (G.lawfulOverlapOpen I i j)).hom :=
    G.overlapStructureToOpenIsLocalized I i j
  unfold overlapStructureSectionToLawQuotient
  apply IsLocalizedModule.lift_apply

/-- Read a lawful-space structure-module section on an overlap in its quotient ring. -/
noncomputable def overlapStructureSectionToLawQuotientOnSpace
    (G : TypedLocalizationGeometry k A Chart) (I : Ideal A) (i j : Chart)
    (s : Γ(SheafOfModules.unit ((G.lawfulSpace I).ringCatSheaf),
      G.lawfulOverlapOpenOnSpace I i j)) :
    G.overlapLawQuotient I i j :=
  G.overlapStructureSectionToLawQuotient I i j
    ((SheafOfModules.unit ((ambientLawSpec I).ringCatSheaf)).val.map
      (eqToHom (G.image_lawfulOverlapOpenOnSpace I i j).symm).op
      (((G.lawfulOpen I).ι.appIso
        (G.lawfulOverlapOpenOnSpace I i j)).inv s))

theorem overlapStructureSectionToLawQuotientOnSpace_coefficientLabeledResponse
    (G : TypedLocalizationGeometry k A Chart) (I : Ideal A) (i j : Chart)
    (c : I.Cotangent)
    (s : Γ(G.derivationCoefficientSheaf I, G.lawfulOverlapOpenOnSpace I i j)) :
    G.overlapStructureSectionToLawQuotientOnSpace I i j
        ((G.coefficientLabeledResponse I c).app
          (G.lawfulOverlapOpenOnSpace I i j) s) =
      G.overlapStructureSectionToLawQuotient I i j
        ((ambientLabeledResponseSheaf (k := k) I c).app (G.lawfulOverlapOpen I i j)
          ((ambientDerivationSheaf (k := k) I).presheaf.map
            (eqToHom (G.image_lawfulOverlapOpenOnSpace I i j).symm).op s)) := by
  unfold overlapStructureSectionToLawQuotientOnSpace
  apply congrArg (G.overlapStructureSectionToLawQuotient I i j)
  simpa [coefficientLabeledResponse, restrictedStructureModuleMap] using
    (PresheafOfModules.naturality_apply
      (ambientLabeledResponseSheaf (k := k) I c).val
      (eqToHom (G.image_lawfulOverlapOpenOnSpace I i j).symm).op s).symm

/-- On an overlap, the sheafified evaluation is the localized full conormal response. -/
theorem overlapAmbientLabeledResponse_eq_conormalResponse
    (G : TypedLocalizationGeometry k A Chart) (I : Ideal A) (i j : Chart)
    (x : I)
    (s : (AlgebraicGeometry.modulesSpecToSheaf.obj
      (ambientDerivationSheaf (k := k) I)).presheaf.obj
        (.op (G.lawfulOverlapOpen I i j))) :
    G.overlapStructureSectionToLawQuotient I i j
        ((ambientLabeledResponseSheaf (k := k) I (I.toCotangent x)).app
          (G.lawfulOverlapOpen I i j) s) =
      QuotientValuedDerivation.conormalResponse (G.overlapLawIdeal I i j)
        (G.overlapSectionToDerivation I i j s)
        ((G.overlapLawIdeal I i j).toCotangent
          ⟨algebraMap A (G.overlapRing i j) x,
            Ideal.mem_map_of_mem (algebraMap A (G.overlapRing i j)) x.property⟩) := by
  letI : Algebra (ambientLawQuotient I) (G.overlapLawQuotient I i j) :=
    (G.overlapLawQuotientMap I i j).toRingHom.toAlgebra
  let source := AlgebraicGeometry.tilde.toOpen
    (ambientDerivationModule (k := k) I) (G.lawfulOverlapOpen I i j)
  letI : IsLocalizedModule
      (Submonoid.powers
        (Ideal.Quotient.mk I (G.denominator i * G.denominator j))) source.hom :=
    G.overlapToOpenIsLocalized I i j
  let localClass : (G.overlapLawIdeal I i j).Cotangent :=
    (G.overlapLawIdeal I i j).toCotangent
      ⟨algebraMap A (G.overlapRing i j) x,
        Ideal.mem_map_of_mem (algebraMap A (G.overlapRing i j)) x.property⟩
  let responseMap :
      (AlgebraicGeometry.modulesSpecToSheaf.obj
        (ambientDerivationSheaf (k := k) I)).presheaf.obj
          (.op (G.lawfulOverlapOpen I i j)) →ₗ[ambientLawQuotient I]
        G.overlapLawQuotient I i j :=
    (G.overlapStructureSectionToLawQuotient I i j).comp
      ((AlgebraicGeometry.modulesSpecToSheaf.map
        (ambientLabeledResponseSheaf (k := k) I (I.toCotangent x))).1.app
          (.op (G.lawfulOverlapOpen I i j))).hom
  let jacobianMap :
      (AlgebraicGeometry.modulesSpecToSheaf.obj
        (ambientDerivationSheaf (k := k) I)).presheaf.obj
          (.op (G.lawfulOverlapOpen I i j)) →ₗ[ambientLawQuotient I]
        G.overlapLawQuotient I i j :=
    (((LinearMap.applyₗ (R := G.overlapLawQuotient I i j) localClass).comp
      (QuotientValuedDerivation.conormalResponseLinear (k := k)
        (G.overlapLawIdeal I i j))).restrictScalars
          (ambientLawQuotient I)).comp (G.overlapSectionToDerivation I i j)
  change responseMap s = jacobianMap s
  apply LinearMap.congr_fun
  apply IsLocalizedModule.ext
    (Submonoid.powers
      (Ideal.Quotient.mk I (G.denominator i * G.denominator j))) source.hom
  · intro denominator
    rw [← (Algebra.lsmul (ambientLawQuotient I)
      (A := G.overlapLawQuotient I i j) (ambientLawQuotient I)
      (G.overlapLawQuotient I i j)).commutes]
    rcases denominator.2 with ⟨n, hn⟩
    rw [← hn, map_pow]
    exact (G.isUnit_overlapLawQuotientMap_denominator I i j).pow n |>.map _
  · ext d
    simp [responseMap, jacobianMap, localClass, ambientLabeledResponseSheaf,
      ambientLabeledResponse, ambientConormalJacobian, ambientConormalEvaluation,
      AlgebraicGeometry.tildeSelf]
    have hmap := congr($(AlgebraicGeometry.tilde.toOpen_map_app
      (ModuleCat.ofHom (QuotientValuedDerivation.conormalResponseLinear
        (k := k) I) ≫
        ModuleCat.ofHom (LinearMap.applyₗ (R := ambientLawQuotient I)
          (I.toCotangent x))) (G.lawfulOverlapOpen I i j)) d)
    rw [ModuleCat.comp_apply, ModuleCat.comp_apply] at hmap
    dsimp [source]
    refine (congrArg (G.overlapStructureSectionToLawQuotient I i j) hmap).trans ?_
    rw [G.overlapStructureSectionToLawQuotient_toOpen]
    calc
      G.overlapLawQuotientMap I i j
          ((ModuleCat.ofHom (QuotientValuedDerivation.conormalResponseLinear
            (k := k) I) ≫
            ModuleCat.ofHom (LinearMap.applyₗ (R := ambientLawQuotient I)
              (I.toCotangent x))).hom d) =
        G.overlapLawQuotientMap I i j (d x) := rfl
      _ = G.overlapAmbientComparison I i j d
          (algebraMap A (G.overlapRing i j) x) :=
        (G.overlapAmbientComparison_algebraMap I i j d x).symm
      _ = G.overlapSectionToDerivation I i j
          ((AlgebraicGeometry.tilde.toOpen
            (ambientDerivationModule (k := k) I)
            (G.lawfulOverlapOpen I i j)) d)
          (algebraMap A (G.overlapRing i j) x) :=
        congrArg (fun e ↦ e (algebraMap A (G.overlapRing i j) x))
          (G.overlapSectionToDerivation_toOpen I i j d).symm

/-- The full conormal Jacobian on one typed chart. -/
noncomputable def chartConormalJacobian
    (G : TypedLocalizationGeometry k A Chart) (I : Ideal A) (i : Chart) :
    Derivation k (G.chartRing i) (G.chartLawQuotient I i) →ₗ[
      G.chartLawQuotient I i]
      Module.Dual (G.chartLawQuotient I i) (G.chartLawIdeal I i).Cotangent :=
  QuotientValuedDerivation.conormalResponseLinear (k := k) (G.chartLawIdeal I i)

/-- The chart response sheaf agrees with evaluation of the objectwise full Jacobian. -/
theorem chartAmbientLabeledResponse_eq_conormalJacobian
    (G : TypedLocalizationGeometry k A Chart) (I : Ideal A) (i : Chart)
    (x : I)
    (s : (AlgebraicGeometry.modulesSpecToSheaf.obj
      (ambientDerivationSheaf (k := k) I)).presheaf.obj
        (.op (G.lawfulChartOpen I i))) :
    G.chartStructureSectionToLawQuotient I i
        ((ambientLabeledResponseSheaf (k := k) I (I.toCotangent x)).app
          (G.lawfulChartOpen I i) s) =
      G.chartConormalJacobian I i (G.chartSectionToDerivation I i s)
        ((G.chartLawIdeal I i).toCotangent
          ⟨algebraMap A (G.chartRing i) x,
            Ideal.mem_map_of_mem (algebraMap A (G.chartRing i)) x.property⟩) :=
  G.chartAmbientLabeledResponse_eq_conormalResponse I i x s

/-- The full conormal Jacobian on one typed overlap. -/
noncomputable def overlapConormalJacobian
    (G : TypedLocalizationGeometry k A Chart) (I : Ideal A) (i j : Chart) :
    Derivation k (G.overlapRing i j) (G.overlapLawQuotient I i j) →ₗ[
      G.overlapLawQuotient I i j]
      Module.Dual (G.overlapLawQuotient I i j)
        (G.overlapLawIdeal I i j).Cotangent :=
  QuotientValuedDerivation.conormalResponseLinear (k := k)
    (G.overlapLawIdeal I i j)

/-- The overlap response sheaf agrees with evaluation of the objectwise full Jacobian. -/
theorem overlapAmbientLabeledResponse_eq_conormalJacobian
    (G : TypedLocalizationGeometry k A Chart) (I : Ideal A) (i j : Chart)
    (x : I)
    (s : (AlgebraicGeometry.modulesSpecToSheaf.obj
      (ambientDerivationSheaf (k := k) I)).presheaf.obj
        (.op (G.lawfulOverlapOpen I i j))) :
    G.overlapStructureSectionToLawQuotient I i j
        ((ambientLabeledResponseSheaf (k := k) I (I.toCotangent x)).app
          (G.lawfulOverlapOpen I i j) s) =
      G.overlapConormalJacobian I i j (G.overlapSectionToDerivation I i j s)
        ((G.overlapLawIdeal I i j).toCotangent
          ⟨algebraMap A (G.overlapRing i j) x,
            Ideal.mem_map_of_mem (algebraMap A (G.overlapRing i j)) x.property⟩) :=
  G.overlapAmbientLabeledResponse_eq_conormalResponse I i j x s

theorem lawfulOverlapOpenOnSpace_le_left
    (G : TypedLocalizationGeometry k A Chart) (I : Ideal A) (i j : Chart) :
    G.lawfulOverlapOpenOnSpace I i j ≤ G.lawfulChartOpenOnSpace I i := by
  apply AlgebraicGeometry.Scheme.Hom.preimage_mono
  rw [G.lawfulOverlapOpen_eq_inf I i j]
  exact inf_le_left

theorem lawfulOverlapOpenOnSpace_le_right
    (G : TypedLocalizationGeometry k A Chart) (I : Ideal A) (i j : Chart) :
    G.lawfulOverlapOpenOnSpace I i j ≤ G.lawfulChartOpenOnSpace I j := by
  apply AlgebraicGeometry.Scheme.Hom.preimage_mono
  rw [G.lawfulOverlapOpen_eq_inf I i j]
  exact inf_le_right

end TypedLocalizationGeometry

open AAT.AG AAT.AG.LawAlgebra

namespace LawGeneratedLabeledConormal

variable {U : AtomCarrier.{u}} {Arch : ArchitectureObject U}
variable {S : Site.AATSite Arch}

/-- A required law together with one Atom generator. -/
abbrev RequiredGeneratorLabel
    (E : ArchitecturalEquationSystem S.contextPreorder) :=
  E.RequiredIndex × U.Atom

/-- The existing violation witness, certified as a member of the generated obstruction ideal. -/
def requiredGeneratorWitness
    (E : ArchitecturalEquationSystem S.contextPreorder) (W : S.category)
    (e : RequiredGeneratorLabel E) : E.obstructionIdeal W :=
  ⟨E.violationCoordinate W e.1.1 e.2,
    E.witnessIdeal_le_obstructionIdeal W e.1.2
      (Ideal.subset_span ⟨e.2, rfl⟩)⟩

/-- The G-07 conormal class generated by one required law/Atom label. -/
def requiredGeneratorConormal
    (E : ArchitecturalEquationSystem S.contextPreorder) (W : S.category)
    (e : RequiredGeneratorLabel E) :
    LawGeneratedIdealPowerSequence.Raw.Conormal E W :=
  (E.obstructionIdeal W).toCotangent
    (requiredGeneratorWitness E W e)

@[simp] theorem requiredGeneratorConormal_toCotangent
    (E : ArchitecturalEquationSystem S.contextPreorder) (W : S.category)
    (e : RequiredGeneratorLabel E) :
    requiredGeneratorConormal E W e =
      (E.obstructionIdeal W).toCotangent
        (requiredGeneratorWitness E W e) := rfl

/-- Required labeled conormal classes obey the existing G-07 restriction map. -/
theorem requiredGeneratorConormal_restrict
    (E : ArchitecturalEquationSystem S.contextPreorder)
    {source target : S.category} (f : source ⟶ target)
    (e : RequiredGeneratorLabel E) :
    LawGeneratedIdealPowerSequence.Raw.conormalRestrict E f
        (requiredGeneratorConormal E target e) =
      requiredGeneratorConormal E source e := by
  rw [requiredGeneratorConormal,
    LawGeneratedIdealPowerSequence.Raw.conormalRestrict_toCotangent]
  apply congrArg (E.obstructionIdeal source).toCotangent
  apply Subtype.ext
  exact E.violationCoordinate_restrict f e.1.1 e.2

section TypedLocalization

variable {k : Type uk} {Chart : Type uChart}
variable [Field k] [Fintype Chart]
variable (E : ArchitecturalEquationSystem S.contextPreorder) (W : S.category)
variable [Algebra k (E.Observable W)]

/-- The generated witness transported to one typed principal chart. -/
noncomputable def chartRequiredGeneratorWitness
    (G : TypedLocalizationGeometry k (E.Observable W) Chart)
    (e : RequiredGeneratorLabel E) (i : Chart) :
    G.chartLawIdeal (E.obstructionIdeal W) i :=
  ⟨algebraMap (E.Observable W) (G.chartRing i)
      (E.violationCoordinate W e.1.1 e.2),
    Ideal.mem_map_of_mem (algebraMap (E.Observable W) (G.chartRing i))
      (requiredGeneratorWitness E W e).property⟩

/-- The generated witness transported to one typed principal overlap. -/
noncomputable def overlapRequiredGeneratorWitness
    (G : TypedLocalizationGeometry k (E.Observable W) Chart)
    (e : RequiredGeneratorLabel E) (i j : Chart) :
    G.overlapLawIdeal (E.obstructionIdeal W) i j :=
  ⟨algebraMap (E.Observable W) (G.overlapRing i j)
      (E.violationCoordinate W e.1.1 e.2),
    Ideal.mem_map_of_mem (algebraMap (E.Observable W) (G.overlapRing i j))
      (requiredGeneratorWitness E W e).property⟩

/-- The labeled conormal class on one typed principal chart. -/
noncomputable def chartLabeledConormal
    (G : TypedLocalizationGeometry k (E.Observable W) Chart)
    (e : RequiredGeneratorLabel E) (i : Chart) :
    (G.chartLawIdeal (E.obstructionIdeal W) i).Cotangent :=
  (G.chartLawIdeal (E.obstructionIdeal W) i).toCotangent
    (chartRequiredGeneratorWitness E W G e i)

/-- The labeled conormal class on one typed principal overlap. -/
noncomputable def overlapLabeledConormal
    (G : TypedLocalizationGeometry k (E.Observable W) Chart)
    (e : RequiredGeneratorLabel E) (i j : Chart) :
    (G.overlapLawIdeal (E.obstructionIdeal W) i j).Cotangent :=
  (G.overlapLawIdeal (E.obstructionIdeal W) i j).toCotangent
    (overlapRequiredGeneratorWitness E W G e i j)

/-- Conormal transport from the left chart to the overlap. -/
noncomputable def leftConormalRestriction
    (G : TypedLocalizationGeometry k (E.Observable W) Chart)
    (i j : Chart) :
    (G.chartLawIdeal (E.obstructionIdeal W) i).Cotangent →ₗ[k]
      (G.overlapLawIdeal (E.obstructionIdeal W) i j).Cotangent :=
  Ideal.mapCotangent
    (G.chartLawIdeal (E.obstructionIdeal W) i)
    (G.overlapLawIdeal (E.obstructionIdeal W) i j)
    ((G.leftChartToOverlap i j).restrictScalars k)
    (G.chartLawIdeal_le_left_comap (E.obstructionIdeal W) i j)

/-- Conormal transport from the right chart to the overlap. -/
noncomputable def rightConormalRestriction
    (G : TypedLocalizationGeometry k (E.Observable W) Chart)
    (i j : Chart) :
    (G.chartLawIdeal (E.obstructionIdeal W) j).Cotangent →ₗ[k]
      (G.overlapLawIdeal (E.obstructionIdeal W) i j).Cotangent :=
  Ideal.mapCotangent
    (G.chartLawIdeal (E.obstructionIdeal W) j)
    (G.overlapLawIdeal (E.obstructionIdeal W) i j)
    ((G.rightChartToOverlap i j).restrictScalars k)
    (G.chartLawIdeal_le_right_comap (E.obstructionIdeal W) i j)

/-- The left chart class restricts to the overlap class. -/
theorem left_chartLabeledConormal_natural
    (G : TypedLocalizationGeometry k (E.Observable W) Chart)
    (e : RequiredGeneratorLabel E) (i j : Chart) :
    leftConormalRestriction E W G i j (chartLabeledConormal E W G e i) =
      overlapLabeledConormal E W G e i j := by
  rw [chartLabeledConormal, leftConormalRestriction,
    Ideal.mapCotangent_toCotangent]
  apply congrArg
    (G.overlapLawIdeal (E.obstructionIdeal W) i j).toCotangent
  apply Subtype.ext
  exact G.leftChartToOverlap_algebraMap i j _

/-- The right chart class restricts to the overlap class. -/
theorem right_chartLabeledConormal_natural
    (G : TypedLocalizationGeometry k (E.Observable W) Chart)
    (e : RequiredGeneratorLabel E) (i j : Chart) :
    rightConormalRestriction E W G i j (chartLabeledConormal E W G e j) =
      overlapLabeledConormal E W G e i j := by
  rw [chartLabeledConormal, rightConormalRestriction,
    Ideal.mapCotangent_toCotangent]
  apply congrArg
    (G.overlapLawIdeal (E.obstructionIdeal W) i j).toCotangent
  apply Subtype.ext
  exact G.rightChartToOverlap_algebraMap i j _

end TypedLocalization

end LawGeneratedLabeledConormal

namespace ArchitectureOperationPresentation

open LawGeneratedLabeledConormal

variable {U : AtomCarrier.{u}} {Arch : ArchitectureObject U}
variable {S : Site.AATSite Arch}
variable {k : Type uk} {Op : Type uOp} {Chart : Type uChart}
variable {State : Type uState} {BeforeWitness : Type uBefore}
variable {AfterWitness : Type uAfter}
variable [Field k] [Fintype Op] [Fintype Chart]
variable (E : ArchitecturalEquationSystem S.contextPreorder) (W : S.category)
variable [Algebra k (E.Observable W)]

/-- The full chartwise Jacobian read from an allowed-operation local section. -/
noncomputable def chartAllowedConormalJacobian
    (P : ArchitectureOperationPresentation k (E.Observable W) Op
      State BeforeWitness AfterWitness)
    (G : TypedLocalizationGeometry k (E.Observable W) Chart)
    (i : Chart)
    (s : Γ(P.allowedOperationSheaf G (E.obstructionIdeal W),
      G.lawfulChartOpenOnSpace (E.obstructionIdeal W) i)) :
    Module.Dual (G.chartLawQuotient (E.obstructionIdeal W) i)
      (G.chartLawIdeal (E.obstructionIdeal W) i).Cotangent :=
  G.chartConormalJacobian (E.obstructionIdeal W) i
    (G.chartSectionToDerivationOnSpace (E.obstructionIdeal W) i
      ((P.allowedOperationToCoefficient G (E.obstructionIdeal W)).app
        (G.lawfulChartOpenOnSpace (E.obstructionIdeal W) i) s))

/-- The full overlap Jacobian read from an allowed-operation local section. -/
noncomputable def overlapAllowedConormalJacobian
    (P : ArchitectureOperationPresentation k (E.Observable W) Op
      State BeforeWitness AfterWitness)
    (G : TypedLocalizationGeometry k (E.Observable W) Chart)
    (i j : Chart)
    (s : Γ(P.allowedOperationSheaf G (E.obstructionIdeal W),
      G.lawfulOverlapOpenOnSpace (E.obstructionIdeal W) i j)) :
    Module.Dual (G.overlapLawQuotient (E.obstructionIdeal W) i j)
      (G.overlapLawIdeal (E.obstructionIdeal W) i j).Cotangent :=
  G.overlapConormalJacobian (E.obstructionIdeal W) i j
    (G.overlapSectionToDerivationOnSpace (E.obstructionIdeal W) i j
      ((P.allowedOperationToCoefficient G (E.obstructionIdeal W)).app
        (G.lawfulOverlapOpenOnSpace (E.obstructionIdeal W) i j) s))

/-- A selected allowed-operation chart section recovers its J2 Jacobian. -/
theorem chartAllowedConormalJacobian_selected
    (P : ArchitectureOperationPresentation k (E.Observable W) Op
      State BeforeWitness AfterWitness)
    (G : TypedLocalizationGeometry k (E.Observable W) Chart)
    (op : Op) (i : Chart) :
    P.chartAllowedConormalJacobian E W G i
        (P.allowedOperationSectionOnChart G (E.obstructionIdeal W) op i) =
      G.chartConormalJacobian (E.obstructionIdeal W) i
        (P.chartQuotientDerivation G (E.obstructionIdeal W) op i) := by
  unfold chartAllowedConormalJacobian
  rw [P.allowedOperationSectionOnChart_recovers G
    (E.obstructionIdeal W) op i]

/-- A selected allowed-operation overlap section recovers its J2 Jacobian. -/
theorem overlapAllowedConormalJacobian_selected
    (P : ArchitectureOperationPresentation k (E.Observable W) Op
      State BeforeWitness AfterWitness)
    (G : TypedLocalizationGeometry k (E.Observable W) Chart)
    (op : Op) (i j : Chart) :
    P.overlapAllowedConormalJacobian E W G i j
        (P.allowedOperationSectionOnOverlap G (E.obstructionIdeal W) op i j) =
      G.overlapConormalJacobian (E.obstructionIdeal W) i j
        (P.overlapQuotientDerivation G (E.obstructionIdeal W) op i j) := by
  unfold overlapAllowedConormalJacobian
  rw [P.allowedOperationSectionOnOverlap_recovers G
    (E.obstructionIdeal W) op i j]

/-- The required-label response `alpha_e : E_A ⟶ O_Y`. -/
noncomputable def labeledResponse
    (P : ArchitectureOperationPresentation k (E.Observable W) Op
      State BeforeWitness AfterWitness)
    (G : TypedLocalizationGeometry k (E.Observable W) Chart)
    (e : RequiredGeneratorLabel E) :
    P.allowedOperationSheaf G (E.obstructionIdeal W) ⟶
      SheafOfModules.unit
        ((G.lawfulSpace (E.obstructionIdeal W)).ringCatSheaf) :=
  P.allowedOperationToCoefficient G (E.obstructionIdeal W) ≫
    G.coefficientLabeledResponse (E.obstructionIdeal W)
      (requiredGeneratorConormal E W e)

theorem labeledResponse_factorization
    (P : ArchitectureOperationPresentation k (E.Observable W) Op
      State BeforeWitness AfterWitness)
    (G : TypedLocalizationGeometry k (E.Observable W) Chart)
    (e : RequiredGeneratorLabel E) :
    P.labeledResponse E W G e =
      P.allowedOperationToCoefficient G (E.obstructionIdeal W) ≫
        G.coefficientLabeledResponse (E.obstructionIdeal W)
          (requiredGeneratorConormal E W e) := rfl

/-- On a selected chart, `alpha_e` is evaluation of the full Jacobian at `c_e`. -/
theorem chart_labeledResponse_eq_allowedConormalJacobian
    (P : ArchitectureOperationPresentation k (E.Observable W) Op
      State BeforeWitness AfterWitness)
    (G : TypedLocalizationGeometry k (E.Observable W) Chart)
    (e : RequiredGeneratorLabel E) (i : Chart)
    (s : Γ(P.allowedOperationSheaf G (E.obstructionIdeal W),
      G.lawfulChartOpenOnSpace (E.obstructionIdeal W) i)) :
    G.chartStructureSectionToLawQuotientOnSpace (E.obstructionIdeal W) i
        ((P.labeledResponse E W G e).app
          (G.lawfulChartOpenOnSpace (E.obstructionIdeal W) i) s) =
      P.chartAllowedConormalJacobian E W G i s
        (chartLabeledConormal E W G e i) := by
  change G.chartStructureSectionToLawQuotientOnSpace
      (E.obstructionIdeal W) i
      ((G.coefficientLabeledResponse (E.obstructionIdeal W)
        (requiredGeneratorConormal E W e)).app
        (G.lawfulChartOpenOnSpace (E.obstructionIdeal W) i)
        ((P.allowedOperationToCoefficient G (E.obstructionIdeal W)).app
          (G.lawfulChartOpenOnSpace (E.obstructionIdeal W) i) s)) = _
  rw [G.chartStructureSectionToLawQuotientOnSpace_coefficientLabeledResponse]
  rw [show requiredGeneratorConormal E W e =
    (E.obstructionIdeal W).toCotangent
      (requiredGeneratorWitness E W e) from rfl]
  rw [G.chartAmbientLabeledResponse_eq_conormalJacobian]
  rfl

/-- On an overlap, `alpha_e` is evaluation of the full Jacobian at `c_e`. -/
theorem overlap_labeledResponse_eq_allowedConormalJacobian
    (P : ArchitectureOperationPresentation k (E.Observable W) Op
      State BeforeWitness AfterWitness)
    (G : TypedLocalizationGeometry k (E.Observable W) Chart)
    (e : RequiredGeneratorLabel E) (i j : Chart)
    (s : Γ(P.allowedOperationSheaf G (E.obstructionIdeal W),
      G.lawfulOverlapOpenOnSpace (E.obstructionIdeal W) i j)) :
    G.overlapStructureSectionToLawQuotientOnSpace (E.obstructionIdeal W) i j
        ((P.labeledResponse E W G e).app
          (G.lawfulOverlapOpenOnSpace (E.obstructionIdeal W) i j) s) =
      P.overlapAllowedConormalJacobian E W G i j s
        (overlapLabeledConormal E W G e i j) := by
  change G.overlapStructureSectionToLawQuotientOnSpace
      (E.obstructionIdeal W) i j
      ((G.coefficientLabeledResponse (E.obstructionIdeal W)
        (requiredGeneratorConormal E W e)).app
        (G.lawfulOverlapOpenOnSpace (E.obstructionIdeal W) i j)
        ((P.allowedOperationToCoefficient G (E.obstructionIdeal W)).app
          (G.lawfulOverlapOpenOnSpace (E.obstructionIdeal W) i j) s)) = _
  rw [G.overlapStructureSectionToLawQuotientOnSpace_coefficientLabeledResponse]
  rw [show requiredGeneratorConormal E W e =
    (E.obstructionIdeal W).toCotangent
      (requiredGeneratorWitness E W e) from rfl]
  rw [G.overlapAmbientLabeledResponse_eq_conormalJacobian]
  rfl

/-- Naturality of `alpha_e` for every inclusion of lawful-space opens. -/
theorem labeledResponse_natural
    (P : ArchitectureOperationPresentation k (E.Observable W) Op
      State BeforeWitness AfterWitness)
    (G : TypedLocalizationGeometry k (E.Observable W) Chart)
    (e : RequiredGeneratorLabel E)
    {V U : (G.lawfulSpace (E.obstructionIdeal W)).Opens} (h : V ≤ U)
    (s : Γ(P.allowedOperationSheaf G (E.obstructionIdeal W), U)) :
    (P.labeledResponse E W G e).app V
        ((P.allowedOperationSheaf G (E.obstructionIdeal W)).presheaf.map
          (homOfLE h).op s) =
      (SheafOfModules.unit
        ((G.lawfulSpace (E.obstructionIdeal W)).ringCatSheaf)).val.map
          (homOfLE h).op
          ((P.labeledResponse E W G e).app U s) := by
  exact PresheafOfModules.naturality_apply
    (P.labeledResponse E W G e).val (homOfLE h).op s

/-- Left chart-to-overlap naturality of every required labeled response. -/
theorem left_labeledResponse_natural
    (P : ArchitectureOperationPresentation k (E.Observable W) Op
      State BeforeWitness AfterWitness)
    (G : TypedLocalizationGeometry k (E.Observable W) Chart)
    (e : RequiredGeneratorLabel E) (i j : Chart)
    (s : Γ(P.allowedOperationSheaf G (E.obstructionIdeal W),
      G.lawfulChartOpenOnSpace (E.obstructionIdeal W) i)) :
    (P.labeledResponse E W G e).app
        (G.lawfulOverlapOpenOnSpace (E.obstructionIdeal W) i j)
        ((P.allowedOperationSheaf G (E.obstructionIdeal W)).presheaf.map
          (homOfLE (G.lawfulOverlapOpenOnSpace_le_left
            (E.obstructionIdeal W) i j)).op s) =
      (SheafOfModules.unit
        ((G.lawfulSpace (E.obstructionIdeal W)).ringCatSheaf)).val.map
          (homOfLE (G.lawfulOverlapOpenOnSpace_le_left
            (E.obstructionIdeal W) i j)).op
          ((P.labeledResponse E W G e).app
            (G.lawfulChartOpenOnSpace (E.obstructionIdeal W) i) s) :=
  P.labeledResponse_natural E W G e
    (G.lawfulOverlapOpenOnSpace_le_left (E.obstructionIdeal W) i j) s

/-- Right chart-to-overlap naturality of every required labeled response. -/
theorem right_labeledResponse_natural
    (P : ArchitectureOperationPresentation k (E.Observable W) Op
      State BeforeWitness AfterWitness)
    (G : TypedLocalizationGeometry k (E.Observable W) Chart)
    (e : RequiredGeneratorLabel E) (i j : Chart)
    (s : Γ(P.allowedOperationSheaf G (E.obstructionIdeal W),
      G.lawfulChartOpenOnSpace (E.obstructionIdeal W) j)) :
    (P.labeledResponse E W G e).app
        (G.lawfulOverlapOpenOnSpace (E.obstructionIdeal W) i j)
        ((P.allowedOperationSheaf G (E.obstructionIdeal W)).presheaf.map
          (homOfLE (G.lawfulOverlapOpenOnSpace_le_right
            (E.obstructionIdeal W) i j)).op s) =
      (SheafOfModules.unit
        ((G.lawfulSpace (E.obstructionIdeal W)).ringCatSheaf)).val.map
          (homOfLE (G.lawfulOverlapOpenOnSpace_le_right
            (E.obstructionIdeal W) i j)).op
          ((P.labeledResponse E W G e).app
            (G.lawfulChartOpenOnSpace (E.obstructionIdeal W) j) s) :=
  P.labeledResponse_natural E W G e
    (G.lawfulOverlapOpenOnSpace_le_right (E.obstructionIdeal W) i j) s

/-- Left restriction compatibility, expressed through the canonical overlap readout of `alpha_e`. -/
theorem left_labeledConormalJacobian_natural
    (P : ArchitectureOperationPresentation k (E.Observable W) Op
      State BeforeWitness AfterWitness)
    (G : TypedLocalizationGeometry k (E.Observable W) Chart)
    (e : RequiredGeneratorLabel E) (i j : Chart)
    (s : Γ(P.allowedOperationSheaf G (E.obstructionIdeal W),
      G.lawfulChartOpenOnSpace (E.obstructionIdeal W) i)) :
    P.overlapAllowedConormalJacobian E W G i j
        ((P.allowedOperationSheaf G (E.obstructionIdeal W)).presheaf.map
          (homOfLE (G.lawfulOverlapOpenOnSpace_le_left
            (E.obstructionIdeal W) i j)).op s)
        (overlapLabeledConormal E W G e i j) =
      G.overlapStructureSectionToLawQuotientOnSpace
        (E.obstructionIdeal W) i j
        ((SheafOfModules.unit
          ((G.lawfulSpace (E.obstructionIdeal W)).ringCatSheaf)).val.map
            (homOfLE (G.lawfulOverlapOpenOnSpace_le_left
              (E.obstructionIdeal W) i j)).op
            ((P.labeledResponse E W G e).app
              (G.lawfulChartOpenOnSpace (E.obstructionIdeal W) i) s)) := by
  rw [← P.overlap_labeledResponse_eq_allowedConormalJacobian E W G e i j]
  exact congrArg
    (G.overlapStructureSectionToLawQuotientOnSpace
      (E.obstructionIdeal W) i j)
    (P.left_labeledResponse_natural E W G e i j s)

/-- Right restriction compatibility, expressed through the canonical overlap readout of `alpha_e`. -/
theorem right_labeledConormalJacobian_natural
    (P : ArchitectureOperationPresentation k (E.Observable W) Op
      State BeforeWitness AfterWitness)
    (G : TypedLocalizationGeometry k (E.Observable W) Chart)
    (e : RequiredGeneratorLabel E) (i j : Chart)
    (s : Γ(P.allowedOperationSheaf G (E.obstructionIdeal W),
      G.lawfulChartOpenOnSpace (E.obstructionIdeal W) j)) :
    P.overlapAllowedConormalJacobian E W G i j
        ((P.allowedOperationSheaf G (E.obstructionIdeal W)).presheaf.map
          (homOfLE (G.lawfulOverlapOpenOnSpace_le_right
            (E.obstructionIdeal W) i j)).op s)
        (overlapLabeledConormal E W G e i j) =
      G.overlapStructureSectionToLawQuotientOnSpace
        (E.obstructionIdeal W) i j
        ((SheafOfModules.unit
          ((G.lawfulSpace (E.obstructionIdeal W)).ringCatSheaf)).val.map
            (homOfLE (G.lawfulOverlapOpenOnSpace_le_right
              (E.obstructionIdeal W) i j)).op
            ((P.labeledResponse E W G e).app
              (G.lawfulChartOpenOnSpace (E.obstructionIdeal W) j) s)) := by
  rw [← P.overlap_labeledResponse_eq_allowedConormalJacobian E W G e i j]
  exact congrArg
    (G.overlapStructureSectionToLawQuotientOnSpace
      (E.obstructionIdeal W) i j)
    (P.right_labeledResponse_natural E W G e i j s)

/-- The chart Jacobian on a selected primitive operation evaluates its generated class. -/
@[simp] theorem chartConormalJacobian_selected
    (P : ArchitectureOperationPresentation k (E.Observable W) Op
      State BeforeWitness AfterWitness)
    (G : TypedLocalizationGeometry k (E.Observable W) Chart)
    (e : RequiredGeneratorLabel E) (op : Op) (i : Chart) :
    G.chartConormalJacobian (E.obstructionIdeal W) i
        (P.chartQuotientDerivation G (E.obstructionIdeal W) op i)
        (chartLabeledConormal E W G e i) =
      P.chartQuotientDerivation G (E.obstructionIdeal W) op i
        (chartRequiredGeneratorWitness E W G e i) := rfl

/-- The overlap Jacobian on a selected primitive operation evaluates its generated class. -/
@[simp] theorem overlapConormalJacobian_selected
    (P : ArchitectureOperationPresentation k (E.Observable W) Op
      State BeforeWitness AfterWitness)
    (G : TypedLocalizationGeometry k (E.Observable W) Chart)
    (e : RequiredGeneratorLabel E) (op : Op) (i j : Chart) :
    G.overlapConormalJacobian (E.obstructionIdeal W) i j
        (P.overlapQuotientDerivation G (E.obstructionIdeal W) op i j)
        (overlapLabeledConormal E W G e i j) =
      P.overlapQuotientDerivation G (E.obstructionIdeal W) op i j
        (overlapRequiredGeneratorWitness E W G e i j) := rfl

/-- Left restriction compatibility of the selected operation's labeled Jacobian value. -/
theorem left_selectedConormalJacobian_natural
    (P : ArchitectureOperationPresentation k (E.Observable W) Op
      State BeforeWitness AfterWitness)
    (G : TypedLocalizationGeometry k (E.Observable W) Chart)
    (e : RequiredGeneratorLabel E) (op : Op) (i j : Chart) :
    G.overlapConormalJacobian (E.obstructionIdeal W) i j
        (P.overlapQuotientDerivation G (E.obstructionIdeal W) op i j)
        (overlapLabeledConormal E W G e i j) =
      G.leftLawQuotientRestriction (E.obstructionIdeal W) i j
        (G.chartConormalJacobian (E.obstructionIdeal W) i
          (P.chartQuotientDerivation G (E.obstructionIdeal W) op i)
          (chartLabeledConormal E W G e i)) := by
  rw [P.overlapConormalJacobian_selected E W G e op i j,
    P.chartConormalJacobian_selected E W G e op i]
  simpa [overlapRequiredGeneratorWitness, chartRequiredGeneratorWitness] using
    P.leftQuotientDerivation_natural G (E.obstructionIdeal W) op i j
      (algebraMap (E.Observable W) (G.chartRing i)
        (E.violationCoordinate W e.1.1 e.2))

/-- Right restriction compatibility of the selected operation's labeled Jacobian value. -/
theorem right_selectedConormalJacobian_natural
    (P : ArchitectureOperationPresentation k (E.Observable W) Op
      State BeforeWitness AfterWitness)
    (G : TypedLocalizationGeometry k (E.Observable W) Chart)
    (e : RequiredGeneratorLabel E) (op : Op) (i j : Chart) :
    G.overlapConormalJacobian (E.obstructionIdeal W) i j
        (P.overlapQuotientDerivation G (E.obstructionIdeal W) op i j)
        (overlapLabeledConormal E W G e i j) =
      G.rightLawQuotientRestriction (E.obstructionIdeal W) i j
        (G.chartConormalJacobian (E.obstructionIdeal W) j
          (P.chartQuotientDerivation G (E.obstructionIdeal W) op j)
          (chartLabeledConormal E W G e j)) := by
  rw [P.overlapConormalJacobian_selected E W G e op i j,
    P.chartConormalJacobian_selected E W G e op j]
  simpa [overlapRequiredGeneratorWitness, chartRequiredGeneratorWitness] using
    P.rightQuotientDerivation_natural G (E.obstructionIdeal W) op i j
      (algebraMap (E.Observable W) (G.chartRing j)
        (E.violationCoordinate W e.1.1 e.2))

end ArchitectureOperationPresentation

end ResearchLean.AG.QualitySurface.IntrinsicLawResponseCircuitDescent

#assert_standard_axioms_only
  ResearchLean.AG.QualitySurface.IntrinsicLawResponseCircuitDescent.QuotientValuedDerivation

#assert_standard_axioms_only
  ResearchLean.AG.QualitySurface.IntrinsicLawResponseCircuitDescent.TypedLocalizationGeometry

#assert_standard_axioms_only
  ResearchLean.AG.QualitySurface.IntrinsicLawResponseCircuitDescent.LawGeneratedLabeledConormal

#assert_standard_axioms_only
  ResearchLean.AG.QualitySurface.IntrinsicLawResponseCircuitDescent.ArchitectureOperationPresentation
