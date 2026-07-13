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
`violationWitness`; neither a representative nor a response evaluator is
accepted as input.  Kernel characterization and labeled generation are later
J5 obligations.
-/

open CategoryTheory
open TopologicalSpace
open scoped AlgebraicGeometry

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

/-- Canonical map from the restricted ambient structure module to the lawful-space one. -/
noncomputable def restrictedStructureModuleMap
    (G : TypedLocalizationGeometry k A Chart) (I : Ideal A) :
    (AlgebraicGeometry.Scheme.Modules.restrictFunctor (G.lawfulOpen I).ι).obj
        (SheafOfModules.unit ((ambientLawSpec I).ringCatSheaf)) ⟶
      SheafOfModules.unit ((G.lawfulSpace I).ringCatSheaf) :=
  (AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback
      (G.lawfulOpen I).ι).hom.app
        (SheafOfModules.unit ((ambientLawSpec I).ringCatSheaf)) ≫
    SheafOfModules.pullbackObjUnitToUnit
      (G.lawfulOpen I).ι.toRingCatSheafHom

/-- Restrict one ambient labeled response to the generated lawful space. -/
noncomputable def coefficientLabeledResponse
    (G : TypedLocalizationGeometry k A Chart) (I : Ideal A) (c : I.Cotangent) :
    G.derivationCoefficientSheaf I ⟶
      SheafOfModules.unit ((G.lawfulSpace I).ringCatSheaf) :=
  (AlgebraicGeometry.Scheme.Modules.restrictFunctor (G.lawfulOpen I).ι).map
      (ambientLabeledResponseSheaf (k := k) I c) ≫
    G.restrictedStructureModuleMap I

/-- The full conormal Jacobian on one typed chart. -/
noncomputable def chartConormalJacobian
    (G : TypedLocalizationGeometry k A Chart) (I : Ideal A) (i : Chart) :
    Derivation k (G.chartRing i) (G.chartLawQuotient I i) →ₗ[
      G.chartLawQuotient I i]
      Module.Dual (G.chartLawQuotient I i) (G.chartLawIdeal I i).Cotangent :=
  QuotientValuedDerivation.conormalResponseLinear (k := k) (G.chartLawIdeal I i)

/-- The full conormal Jacobian on one typed overlap. -/
noncomputable def overlapConormalJacobian
    (G : TypedLocalizationGeometry k A Chart) (I : Ideal A) (i j : Chart) :
    Derivation k (G.overlapRing i j) (G.overlapLawQuotient I i j) →ₗ[
      G.overlapLawQuotient I i j]
      Module.Dual (G.overlapLawQuotient I i j)
        (G.overlapLawIdeal I i j).Cotangent :=
  QuotientValuedDerivation.conormalResponseLinear (k := k)
    (G.overlapLawIdeal I i j)

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
abbrev RequiredGeneratorLabel (S : Site.AATSite Arch) :=
  { lawIndex : S.lawUniverse.Index // S.lawUniverse.Required lawIndex } × U.Atom

/-- The existing violation witness, certified as a member of the generated obstruction ideal. -/
def requiredGeneratorWitness
    (Core : SemanticLawEquationWitnessIdealCore S) (W : S.category)
    (e : RequiredGeneratorLabel S) : Core.obstructionIdeal W :=
  ⟨Core.violationWitness W e.1.1 e.2,
    Core.lawWitnessIdeal_le_obstructionIdeal W e.1.2
      (Ideal.subset_span ⟨e.2, rfl⟩)⟩

/-- The G-07 conormal class generated by one required law/Atom label. -/
def requiredGeneratorConormal
    (Core : SemanticLawEquationWitnessIdealCore S) (W : S.category)
    (e : RequiredGeneratorLabel S) :
    LawGeneratedIdealPowerSequence.Raw.Conormal Core W :=
  (Core.obstructionIdeal W).toCotangent
    (requiredGeneratorWitness Core W e)

@[simp] theorem requiredGeneratorConormal_toCotangent
    (Core : SemanticLawEquationWitnessIdealCore S) (W : S.category)
    (e : RequiredGeneratorLabel S) :
    requiredGeneratorConormal Core W e =
      (Core.obstructionIdeal W).toCotangent
        (requiredGeneratorWitness Core W e) := rfl

/-- Required labeled conormal classes obey the existing G-07 restriction map. -/
theorem requiredGeneratorConormal_restrict
    (Core : SemanticLawEquationWitnessIdealCore S)
    {source target : S.category} (f : source ⟶ target)
    (e : RequiredGeneratorLabel S) :
    LawGeneratedIdealPowerSequence.Raw.conormalRestrict Core f
        (requiredGeneratorConormal Core target e) =
      requiredGeneratorConormal Core source e := by
  rw [requiredGeneratorConormal,
    LawGeneratedIdealPowerSequence.Raw.conormalRestrict_toCotangent]
  apply congrArg (Core.obstructionIdeal source).toCotangent
  apply Subtype.ext
  exact Core.violationWitness_restrict f e.1.1 e.2

section TypedLocalization

variable {k : Type uk} {Chart : Type uChart}
variable [Field k] [Fintype Chart]
variable (Core : SemanticLawEquationWitnessIdealCore S) (W : S.category)
variable [Algebra k (Core.Observable W)]

/-- The generated witness transported to one typed principal chart. -/
noncomputable def chartRequiredGeneratorWitness
    (G : TypedLocalizationGeometry k (Core.Observable W) Chart)
    (e : RequiredGeneratorLabel S) (i : Chart) :
    G.chartLawIdeal (Core.obstructionIdeal W) i :=
  ⟨algebraMap (Core.Observable W) (G.chartRing i)
      (Core.violationWitness W e.1.1 e.2),
    Ideal.mem_map_of_mem (algebraMap (Core.Observable W) (G.chartRing i))
      (requiredGeneratorWitness Core W e).property⟩

/-- The generated witness transported to one typed principal overlap. -/
noncomputable def overlapRequiredGeneratorWitness
    (G : TypedLocalizationGeometry k (Core.Observable W) Chart)
    (e : RequiredGeneratorLabel S) (i j : Chart) :
    G.overlapLawIdeal (Core.obstructionIdeal W) i j :=
  ⟨algebraMap (Core.Observable W) (G.overlapRing i j)
      (Core.violationWitness W e.1.1 e.2),
    Ideal.mem_map_of_mem (algebraMap (Core.Observable W) (G.overlapRing i j))
      (requiredGeneratorWitness Core W e).property⟩

/-- The labeled conormal class on one typed principal chart. -/
noncomputable def chartLabeledConormal
    (G : TypedLocalizationGeometry k (Core.Observable W) Chart)
    (e : RequiredGeneratorLabel S) (i : Chart) :
    (G.chartLawIdeal (Core.obstructionIdeal W) i).Cotangent :=
  (G.chartLawIdeal (Core.obstructionIdeal W) i).toCotangent
    (chartRequiredGeneratorWitness Core W G e i)

/-- The labeled conormal class on one typed principal overlap. -/
noncomputable def overlapLabeledConormal
    (G : TypedLocalizationGeometry k (Core.Observable W) Chart)
    (e : RequiredGeneratorLabel S) (i j : Chart) :
    (G.overlapLawIdeal (Core.obstructionIdeal W) i j).Cotangent :=
  (G.overlapLawIdeal (Core.obstructionIdeal W) i j).toCotangent
    (overlapRequiredGeneratorWitness Core W G e i j)

/-- Conormal transport from the left chart to the overlap. -/
noncomputable def leftConormalRestriction
    (G : TypedLocalizationGeometry k (Core.Observable W) Chart)
    (i j : Chart) :
    (G.chartLawIdeal (Core.obstructionIdeal W) i).Cotangent →ₗ[k]
      (G.overlapLawIdeal (Core.obstructionIdeal W) i j).Cotangent :=
  Ideal.mapCotangent
    (G.chartLawIdeal (Core.obstructionIdeal W) i)
    (G.overlapLawIdeal (Core.obstructionIdeal W) i j)
    ((G.leftChartToOverlap i j).restrictScalars k)
    (G.chartLawIdeal_le_left_comap (Core.obstructionIdeal W) i j)

/-- Conormal transport from the right chart to the overlap. -/
noncomputable def rightConormalRestriction
    (G : TypedLocalizationGeometry k (Core.Observable W) Chart)
    (i j : Chart) :
    (G.chartLawIdeal (Core.obstructionIdeal W) j).Cotangent →ₗ[k]
      (G.overlapLawIdeal (Core.obstructionIdeal W) i j).Cotangent :=
  Ideal.mapCotangent
    (G.chartLawIdeal (Core.obstructionIdeal W) j)
    (G.overlapLawIdeal (Core.obstructionIdeal W) i j)
    ((G.rightChartToOverlap i j).restrictScalars k)
    (G.chartLawIdeal_le_right_comap (Core.obstructionIdeal W) i j)

/-- The left chart class restricts to the overlap class. -/
theorem left_chartLabeledConormal_natural
    (G : TypedLocalizationGeometry k (Core.Observable W) Chart)
    (e : RequiredGeneratorLabel S) (i j : Chart) :
    leftConormalRestriction Core W G i j (chartLabeledConormal Core W G e i) =
      overlapLabeledConormal Core W G e i j := by
  rw [chartLabeledConormal, leftConormalRestriction,
    Ideal.mapCotangent_toCotangent]
  apply congrArg
    (G.overlapLawIdeal (Core.obstructionIdeal W) i j).toCotangent
  apply Subtype.ext
  exact G.leftChartToOverlap_algebraMap i j _

/-- The right chart class restricts to the overlap class. -/
theorem right_chartLabeledConormal_natural
    (G : TypedLocalizationGeometry k (Core.Observable W) Chart)
    (e : RequiredGeneratorLabel S) (i j : Chart) :
    rightConormalRestriction Core W G i j (chartLabeledConormal Core W G e j) =
      overlapLabeledConormal Core W G e i j := by
  rw [chartLabeledConormal, rightConormalRestriction,
    Ideal.mapCotangent_toCotangent]
  apply congrArg
    (G.overlapLawIdeal (Core.obstructionIdeal W) i j).toCotangent
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
variable (Core : SemanticLawEquationWitnessIdealCore S) (W : S.category)
variable [Algebra k (Core.Observable W)]

/-- The full chartwise Jacobian read from an allowed-operation local section. -/
noncomputable def chartAllowedConormalJacobian
    (P : ArchitectureOperationPresentation k (Core.Observable W) Op
      State BeforeWitness AfterWitness)
    (G : TypedLocalizationGeometry k (Core.Observable W) Chart)
    (i : Chart)
    (s : Γ(P.allowedOperationSheaf G (Core.obstructionIdeal W),
      G.lawfulChartOpenOnSpace (Core.obstructionIdeal W) i)) :
    Module.Dual (G.chartLawQuotient (Core.obstructionIdeal W) i)
      (G.chartLawIdeal (Core.obstructionIdeal W) i).Cotangent :=
  G.chartConormalJacobian (Core.obstructionIdeal W) i
    (G.chartSectionToDerivationOnSpace (Core.obstructionIdeal W) i
      ((P.allowedOperationToCoefficient G (Core.obstructionIdeal W)).app
        (G.lawfulChartOpenOnSpace (Core.obstructionIdeal W) i) s))

/-- The full overlap Jacobian read from an allowed-operation local section. -/
noncomputable def overlapAllowedConormalJacobian
    (P : ArchitectureOperationPresentation k (Core.Observable W) Op
      State BeforeWitness AfterWitness)
    (G : TypedLocalizationGeometry k (Core.Observable W) Chart)
    (i j : Chart)
    (s : Γ(P.allowedOperationSheaf G (Core.obstructionIdeal W),
      G.lawfulOverlapOpenOnSpace (Core.obstructionIdeal W) i j)) :
    Module.Dual (G.overlapLawQuotient (Core.obstructionIdeal W) i j)
      (G.overlapLawIdeal (Core.obstructionIdeal W) i j).Cotangent :=
  G.overlapConormalJacobian (Core.obstructionIdeal W) i j
    (G.overlapSectionToDerivationOnSpace (Core.obstructionIdeal W) i j
      ((P.allowedOperationToCoefficient G (Core.obstructionIdeal W)).app
        (G.lawfulOverlapOpenOnSpace (Core.obstructionIdeal W) i j) s))

/-- A selected allowed-operation chart section recovers its J2 Jacobian. -/
theorem chartAllowedConormalJacobian_selected
    (P : ArchitectureOperationPresentation k (Core.Observable W) Op
      State BeforeWitness AfterWitness)
    (G : TypedLocalizationGeometry k (Core.Observable W) Chart)
    (op : Op) (i : Chart) :
    P.chartAllowedConormalJacobian Core W G i
        (P.allowedOperationSectionOnChart G (Core.obstructionIdeal W) op i) =
      G.chartConormalJacobian (Core.obstructionIdeal W) i
        (P.chartQuotientDerivation G (Core.obstructionIdeal W) op i) := by
  unfold chartAllowedConormalJacobian
  rw [P.allowedOperationSectionOnChart_recovers G
    (Core.obstructionIdeal W) op i]

/-- A selected allowed-operation overlap section recovers its J2 Jacobian. -/
theorem overlapAllowedConormalJacobian_selected
    (P : ArchitectureOperationPresentation k (Core.Observable W) Op
      State BeforeWitness AfterWitness)
    (G : TypedLocalizationGeometry k (Core.Observable W) Chart)
    (op : Op) (i j : Chart) :
    P.overlapAllowedConormalJacobian Core W G i j
        (P.allowedOperationSectionOnOverlap G (Core.obstructionIdeal W) op i j) =
      G.overlapConormalJacobian (Core.obstructionIdeal W) i j
        (P.overlapQuotientDerivation G (Core.obstructionIdeal W) op i j) := by
  unfold overlapAllowedConormalJacobian
  rw [P.allowedOperationSectionOnOverlap_recovers G
    (Core.obstructionIdeal W) op i j]

/-- The required-label response `alpha_e : E_A ⟶ O_Y`. -/
noncomputable def labeledResponse
    (P : ArchitectureOperationPresentation k (Core.Observable W) Op
      State BeforeWitness AfterWitness)
    (G : TypedLocalizationGeometry k (Core.Observable W) Chart)
    (e : RequiredGeneratorLabel S) :
    P.allowedOperationSheaf G (Core.obstructionIdeal W) ⟶
      SheafOfModules.unit
        ((G.lawfulSpace (Core.obstructionIdeal W)).ringCatSheaf) :=
  P.allowedOperationToCoefficient G (Core.obstructionIdeal W) ≫
    G.coefficientLabeledResponse (Core.obstructionIdeal W)
      (requiredGeneratorConormal Core W e)

theorem labeledResponse_factorization
    (P : ArchitectureOperationPresentation k (Core.Observable W) Op
      State BeforeWitness AfterWitness)
    (G : TypedLocalizationGeometry k (Core.Observable W) Chart)
    (e : RequiredGeneratorLabel S) :
    P.labeledResponse Core W G e =
      P.allowedOperationToCoefficient G (Core.obstructionIdeal W) ≫
        G.coefficientLabeledResponse (Core.obstructionIdeal W)
          (requiredGeneratorConormal Core W e) := rfl

/-- Naturality of `alpha_e` for every inclusion of lawful-space opens. -/
theorem labeledResponse_natural
    (P : ArchitectureOperationPresentation k (Core.Observable W) Op
      State BeforeWitness AfterWitness)
    (G : TypedLocalizationGeometry k (Core.Observable W) Chart)
    (e : RequiredGeneratorLabel S)
    {V U : (G.lawfulSpace (Core.obstructionIdeal W)).Opens} (h : V ≤ U)
    (s : Γ(P.allowedOperationSheaf G (Core.obstructionIdeal W), U)) :
    (P.labeledResponse Core W G e).app V
        ((P.allowedOperationSheaf G (Core.obstructionIdeal W)).presheaf.map
          (homOfLE h).op s) =
      (SheafOfModules.unit
        ((G.lawfulSpace (Core.obstructionIdeal W)).ringCatSheaf)).val.map
          (homOfLE h).op
          ((P.labeledResponse Core W G e).app U s) := by
  exact PresheafOfModules.naturality_apply
    (P.labeledResponse Core W G e).val (homOfLE h).op s

/-- Left chart-to-overlap naturality of every required labeled response. -/
theorem left_labeledResponse_natural
    (P : ArchitectureOperationPresentation k (Core.Observable W) Op
      State BeforeWitness AfterWitness)
    (G : TypedLocalizationGeometry k (Core.Observable W) Chart)
    (e : RequiredGeneratorLabel S) (i j : Chart)
    (s : Γ(P.allowedOperationSheaf G (Core.obstructionIdeal W),
      G.lawfulChartOpenOnSpace (Core.obstructionIdeal W) i)) :
    (P.labeledResponse Core W G e).app
        (G.lawfulOverlapOpenOnSpace (Core.obstructionIdeal W) i j)
        ((P.allowedOperationSheaf G (Core.obstructionIdeal W)).presheaf.map
          (homOfLE (G.lawfulOverlapOpenOnSpace_le_left
            (Core.obstructionIdeal W) i j)).op s) =
      (SheafOfModules.unit
        ((G.lawfulSpace (Core.obstructionIdeal W)).ringCatSheaf)).val.map
          (homOfLE (G.lawfulOverlapOpenOnSpace_le_left
            (Core.obstructionIdeal W) i j)).op
          ((P.labeledResponse Core W G e).app
            (G.lawfulChartOpenOnSpace (Core.obstructionIdeal W) i) s) :=
  P.labeledResponse_natural Core W G e
    (G.lawfulOverlapOpenOnSpace_le_left (Core.obstructionIdeal W) i j) s

/-- Right chart-to-overlap naturality of every required labeled response. -/
theorem right_labeledResponse_natural
    (P : ArchitectureOperationPresentation k (Core.Observable W) Op
      State BeforeWitness AfterWitness)
    (G : TypedLocalizationGeometry k (Core.Observable W) Chart)
    (e : RequiredGeneratorLabel S) (i j : Chart)
    (s : Γ(P.allowedOperationSheaf G (Core.obstructionIdeal W),
      G.lawfulChartOpenOnSpace (Core.obstructionIdeal W) j)) :
    (P.labeledResponse Core W G e).app
        (G.lawfulOverlapOpenOnSpace (Core.obstructionIdeal W) i j)
        ((P.allowedOperationSheaf G (Core.obstructionIdeal W)).presheaf.map
          (homOfLE (G.lawfulOverlapOpenOnSpace_le_right
            (Core.obstructionIdeal W) i j)).op s) =
      (SheafOfModules.unit
        ((G.lawfulSpace (Core.obstructionIdeal W)).ringCatSheaf)).val.map
          (homOfLE (G.lawfulOverlapOpenOnSpace_le_right
            (Core.obstructionIdeal W) i j)).op
          ((P.labeledResponse Core W G e).app
            (G.lawfulChartOpenOnSpace (Core.obstructionIdeal W) j) s) :=
  P.labeledResponse_natural Core W G e
    (G.lawfulOverlapOpenOnSpace_le_right (Core.obstructionIdeal W) i j) s

/-- The chart Jacobian on a selected primitive operation evaluates its generated class. -/
@[simp] theorem chartConormalJacobian_selected
    (P : ArchitectureOperationPresentation k (Core.Observable W) Op
      State BeforeWitness AfterWitness)
    (G : TypedLocalizationGeometry k (Core.Observable W) Chart)
    (e : RequiredGeneratorLabel S) (op : Op) (i : Chart) :
    G.chartConormalJacobian (Core.obstructionIdeal W) i
        (P.chartQuotientDerivation G (Core.obstructionIdeal W) op i)
        (chartLabeledConormal Core W G e i) =
      P.chartQuotientDerivation G (Core.obstructionIdeal W) op i
        (chartRequiredGeneratorWitness Core W G e i) := rfl

/-- The overlap Jacobian on a selected primitive operation evaluates its generated class. -/
@[simp] theorem overlapConormalJacobian_selected
    (P : ArchitectureOperationPresentation k (Core.Observable W) Op
      State BeforeWitness AfterWitness)
    (G : TypedLocalizationGeometry k (Core.Observable W) Chart)
    (e : RequiredGeneratorLabel S) (op : Op) (i j : Chart) :
    G.overlapConormalJacobian (Core.obstructionIdeal W) i j
        (P.overlapQuotientDerivation G (Core.obstructionIdeal W) op i j)
        (overlapLabeledConormal Core W G e i j) =
      P.overlapQuotientDerivation G (Core.obstructionIdeal W) op i j
        (overlapRequiredGeneratorWitness Core W G e i j) := rfl

/-- Left restriction compatibility of the selected operation's labeled Jacobian value. -/
theorem left_selectedConormalJacobian_natural
    (P : ArchitectureOperationPresentation k (Core.Observable W) Op
      State BeforeWitness AfterWitness)
    (G : TypedLocalizationGeometry k (Core.Observable W) Chart)
    (e : RequiredGeneratorLabel S) (op : Op) (i j : Chart) :
    G.overlapConormalJacobian (Core.obstructionIdeal W) i j
        (P.overlapQuotientDerivation G (Core.obstructionIdeal W) op i j)
        (overlapLabeledConormal Core W G e i j) =
      G.leftLawQuotientRestriction (Core.obstructionIdeal W) i j
        (G.chartConormalJacobian (Core.obstructionIdeal W) i
          (P.chartQuotientDerivation G (Core.obstructionIdeal W) op i)
          (chartLabeledConormal Core W G e i)) := by
  rw [P.overlapConormalJacobian_selected Core W G e op i j,
    P.chartConormalJacobian_selected Core W G e op i]
  simpa [overlapRequiredGeneratorWitness, chartRequiredGeneratorWitness] using
    P.leftQuotientDerivation_natural G (Core.obstructionIdeal W) op i j
      (algebraMap (Core.Observable W) (G.chartRing i)
        (Core.violationWitness W e.1.1 e.2))

/-- Right restriction compatibility of the selected operation's labeled Jacobian value. -/
theorem right_selectedConormalJacobian_natural
    (P : ArchitectureOperationPresentation k (Core.Observable W) Op
      State BeforeWitness AfterWitness)
    (G : TypedLocalizationGeometry k (Core.Observable W) Chart)
    (e : RequiredGeneratorLabel S) (op : Op) (i j : Chart) :
    G.overlapConormalJacobian (Core.obstructionIdeal W) i j
        (P.overlapQuotientDerivation G (Core.obstructionIdeal W) op i j)
        (overlapLabeledConormal Core W G e i j) =
      G.rightLawQuotientRestriction (Core.obstructionIdeal W) i j
        (G.chartConormalJacobian (Core.obstructionIdeal W) j
          (P.chartQuotientDerivation G (Core.obstructionIdeal W) op j)
          (chartLabeledConormal Core W G e j)) := by
  rw [P.overlapConormalJacobian_selected Core W G e op i j,
    P.chartConormalJacobian_selected Core W G e op j]
  simpa [overlapRequiredGeneratorWitness, chartRequiredGeneratorWitness] using
    P.rightQuotientDerivation_natural G (Core.obstructionIdeal W) op i j
      (algebraMap (Core.Observable W) (G.chartRing j)
        (Core.violationWitness W e.1.1 e.2))

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
