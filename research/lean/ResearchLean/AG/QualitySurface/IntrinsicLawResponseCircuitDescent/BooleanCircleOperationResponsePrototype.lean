import ResearchLean.AG.QualitySurface.LawGeneratedBooleanCircleLawCore
import ResearchLean.AG.QualitySurface.IntrinsicLawResponseCircuitDescent.LabeledConormalGeneration
import ResearchLean.AG.QualitySurface.IntrinsicLawResponseCircuitDescent.DerivationCoefficientSheaf

/-!
# Boolean-circle operation response prototype

The existing three-patch Boolean-circle cover is paired with a G-08-specific
three-component principal-localization ring layer.  Its first component is a
dual-number factor carrying a square-zero law generator; the other two
components make the three principal chart opens genuinely distinct.  Their
pairwise intersections are nonempty and their triple intersection is empty.
A concrete operation derivation detects the selected required conormal class
on the AAT patch carrying its support Atom and on a matched overlap.
-/

noncomputable section

namespace ResearchLean.AG.QualitySurface
namespace IntrinsicLawResponseCircuitDescent
namespace BooleanCircleOperationResponsePrototype

open AAT.AG AAT.AG.LawAlgebra
open LawGeneratedBooleanCircleSite
open LawGeneratedBooleanCircleLawCore

abbrev ResponseField := ZMod 2
abbrev ResponseDual := TrivSqZeroExt ResponseField ResponseField
abbrev ResponseRing := ResponseDual × ResponseField × ResponseField

/-- The G-08 square-zero law generator in the first product component. -/
def responseGenerator : ResponseRing :=
  (TrivSqZeroExt.inr 1, 0, 0)

/-- The derivative value of the square-zero generator. -/
def responseValue : ResponseRing :=
  (TrivSqZeroExt.inl 1, 0, 0)

theorem responseGenerator_sq : responseGenerator ^ 2 = 0 := by
  ext <;> simp [pow_two, responseGenerator]

theorem responseGenerator_ne_zero : responseGenerator ≠ 0 := by
  intro h
  have hsnd := congrArg (fun x : ResponseRing ↦ x.1.snd) h
  norm_num [responseGenerator] at hsnd

/-- The derivative of the nilpotent coordinate, valued in the constant
coordinate of the same dual-number component. -/
def epsilonDerivative :
    Derivation ResponseField ResponseRing ResponseRing where
  toFun x := (TrivSqZeroExt.inl x.1.snd, 0, 0)
  map_add' x y := by ext <;> simp
  map_smul' c x := by ext <;> simp
  map_one_eq_zero' := by ext <;> simp
  leibniz' x y := by
    rcases x with ⟨⟨x₁, xε⟩, x₂, x₃⟩
    rcases y with ⟨⟨y₁, yε⟩, y₂, y₃⟩
    ext <;> simp
    · exact mul_comm _ _
    · rw [mul_comm yε xε]
      exact (CharTwo.add_self_eq_zero (xε * yε)).symm

@[simp] theorem epsilonDerivative_responseGenerator :
    epsilonDerivative responseGenerator = responseValue := by
  rfl

/-- The constant square-zero equation system on the three-patch Boolean-circle site. -/
noncomputable def responseCore :
    ArchitecturalEquationSystem site.contextPreorder where
  Index := site.equationSystem.Index
  role := site.equationSystem.role
  Observable _ := ResponseRing
  observableCommRing _ := inferInstance
  restrict _ := RingHom.id ResponseRing
  restrict_id _ _ := rfl
  restrict_comp _ _ _ := rfl
  violationCoordinate _ _ _ := responseGenerator
  violationCoordinate_restrict _ _ _ := rfl
  equationResidual _ object _ _ :=
    (FiniteModel.noCycleResidual object : ResponseRing)
  equationResidual_restrict := by
    intros
    rfl

/-- The required equation and Atom displayed by the operation response. -/
def selectedLabel :
    LawGeneratedLabeledConormal.RequiredGeneratorLabel responseCore :=
  (⟨PUnit.unit, by rfl⟩, FiniteModel.FiniteAtom.componentA)

local instance responseCoreAlgebra :
    Algebra ResponseField (responseCore.Observable base) :=
  inferInstanceAs (Algebra ResponseField ResponseRing)

theorem response_witnessIdeal (W : site.category)
    (equationIndex : responseCore.Index) :
    responseCore.witnessIdeal W equationIndex = Ideal.span {responseGenerator} := by
  rw [ArchitecturalEquationSystem.witnessIdeal_eq_span]
  change Ideal.span (Set.range (fun _ : FiniteModel.carrier.Atom ↦
    responseGenerator)) = _
  congr 1
  ext x
  constructor
  · rintro ⟨atom, rfl⟩
    rfl
  · intro hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact ⟨FiniteModel.FiniteAtom.componentA, rfl⟩

theorem response_obstructionIdeal (W : site.category) :
    responseCore.obstructionIdeal W = Ideal.span {responseGenerator} := by
  rw [obstructionIdeal_eq_witnessIdeal responseCore W
      selectedLabel.1.1 selectedLabel.1.2
      (fun other _ => by cases other; rfl),
    response_witnessIdeal]

theorem responseValue_not_mem_obstructionIdeal :
    responseValue ∉ responseCore.obstructionIdeal base := by
  rw [response_obstructionIdeal]
  intro h
  rw [Ideal.mem_span_singleton'] at h
  obtain ⟨r, hr⟩ := h
  have hconstant := congrArg (fun x : ResponseRing ↦ x.1.fst) hr
  norm_num [responseValue, responseGenerator] at hconstant

/-- A finite selected repair-operation schema.  Algebraic response data remain
in the external typed presentation below. -/
def prototypeProofObligation : Formal.Arch.ProofObligation Unit Unit where
  formalUniverse := True
  requiredLaws := True
  invariantFamily _ := True
  witnessUniverse _ := True
  coverageAssumptions := True
  exactnessAssumptions := True
  operationPreconditions := True
  conclusion := True
  nonConclusions := True

def prototypeOperation : Formal.Arch.ArchitectureOperation Unit Unit Unit where
  kind := .repair
  source := Unit.unit
  target := Unit.unit
  precondition := True
  generatedProofObligation :=
    Formal.Arch.OperationProofObligation.repair
      prototypeProofObligation True True
  generatedProofObligationKind := rfl
  sourceWitness _ := True
  targetWitness _ := True
  witnessMap _ := Unit.unit
  witnessMappingSound _ _ := trivial
  nonConclusion := True

def presentation : ArchitectureOperationPresentation ResponseField
    (responseCore.Observable base) Unit Unit Unit Unit where
  operation _ := prototypeOperation
  ambientDerivation _ := epsilonDerivative

theorem presentation_realizesFirstOrder :
    presentation.RealizesFirstOrder Unit.unit prototypeOperation
      epsilonDerivative :=
  presentation.realizesFirstOrder Unit.unit

/-- Three idempotents whose pairwise intersections form a Boolean-circle
nerve: each selects two of the three product components. -/
def denominator (i : Fin 3) : ResponseRing :=
  if i = 0 then (1, 1, 0) else if i = 1 then (1, 0, 1) else (0, 1, 1)

def geometry : TypedLocalizationGeometry ResponseField
    (responseCore.Observable base) (Fin 3) where
  denominator := denominator

@[simp] theorem denominator_zero : geometry.denominator 0 = (1, 1, 0) := by
  simp [geometry, denominator]

@[simp] theorem denominator_one : geometry.denominator 1 = (1, 0, 1) := by
  simp [geometry, denominator]

@[simp] theorem denominator_two : geometry.denominator 2 = (0, 1, 1) := by
  simp [geometry, denominator]

theorem denominator_injective : Function.Injective geometry.denominator := by
  intro i j h
  fin_cases i <;> fin_cases j
  all_goals try rfl
  · have hc := congrArg (fun x : ResponseRing ↦ x.2.1) h
    norm_num [geometry, denominator] at hc
  · have hc := congrArg (fun x : ResponseRing ↦ x.1.fst) h
    norm_num [geometry, denominator] at hc
  · have hc := congrArg (fun x : ResponseRing ↦ x.2.1) h
    norm_num [geometry, denominator] at hc
  · have hc := congrArg (fun x : ResponseRing ↦ x.1.fst) h
    norm_num [geometry, denominator] at hc
  · have hc := congrArg (fun x : ResponseRing ↦ x.1.fst) h
    norm_num [geometry, denominator] at hc
  · have hc := congrArg (fun x : ResponseRing ↦ x.1.fst) h
    norm_num [geometry, denominator] at hc

theorem denominator_span_eq_top :
    Ideal.span (Set.range geometry.denominator) =
      (⊤ : Ideal (responseCore.Observable base)) := by
  apply (Ideal.eq_top_iff_one _).mpr
  have h₀ : geometry.denominator 0 ∈ Ideal.span (Set.range geometry.denominator) :=
    Ideal.subset_span ⟨0, rfl⟩
  have h₁ : geometry.denominator 1 ∈ Ideal.span (Set.range geometry.denominator) :=
    Ideal.subset_span ⟨1, rfl⟩
  have h₂ : geometry.denominator 2 ∈ Ideal.span (Set.range geometry.denominator) :=
    Ideal.subset_span ⟨2, rfl⟩
  have h₀₁ : geometry.denominator 0 * geometry.denominator 1 ∈
      Ideal.span (Set.range geometry.denominator) :=
    Ideal.mul_mem_left _ _ h₁
  have h₀₂ : geometry.denominator 0 * geometry.denominator 2 ∈
      Ideal.span (Set.range geometry.denominator) :=
    Ideal.mul_mem_left _ _ h₂
  have h₁₂ : geometry.denominator 1 * geometry.denominator 2 ∈
      Ideal.span (Set.range geometry.denominator) :=
    Ideal.mul_mem_left _ _ h₂
  have hone : geometry.denominator 0 * geometry.denominator 1 +
      geometry.denominator 0 * geometry.denominator 2 +
      geometry.denominator 1 * geometry.denominator 2 = (1 : ResponseRing) := by
    change denominator 0 * denominator 1 + denominator 0 * denominator 2 +
      denominator 1 * denominator 2 = (1 : ResponseRing)
    ext <;> simp [denominator]
  rw [← hone]
  exact Ideal.add_mem _ (Ideal.add_mem _ h₀₁ h₀₂) h₁₂

theorem denominator_mul_self (i : Fin 3) :
    denominator i * denominator i = denominator i := by
  fin_cases i <;> ext <;> simp [denominator]

theorem denominator_mul_ne_zero {i j : Fin 3} (hij : i ≠ j) :
    denominator i * denominator j ≠ 0 := by
  fin_cases i <;> fin_cases j <;> simp_all [denominator]

theorem denominator_triple_mul_eq_zero :
    denominator 0 * denominator 1 * denominator 2 = 0 := by
  ext <;> simp [denominator]

theorem denominator_not_mem_obstructionIdeal (i : Fin 3) :
    denominator i ∉ responseCore.obstructionIdeal base := by
  rw [response_obstructionIdeal, Ideal.mem_span_singleton']
  rintro ⟨r, hr⟩
  fin_cases i
  · have hcoord := congrArg (fun x : ResponseRing ↦ x.2.1) hr
    norm_num [denominator, responseGenerator] at hcoord
  · have hcoord := congrArg (fun x : ResponseRing ↦ x.2.2) hr
    norm_num [denominator, responseGenerator] at hcoord
  · have hcoord := congrArg (fun x : ResponseRing ↦ x.2.1) hr
    norm_num [denominator, responseGenerator] at hcoord

theorem denominator_mul_not_mem_obstructionIdeal {i j : Fin 3} (hij : i ≠ j) :
    denominator i * denominator j ∉ responseCore.obstructionIdeal base := by
  rw [response_obstructionIdeal, Ideal.mem_span_singleton']
  rintro ⟨r, hr⟩
  fin_cases i <;> fin_cases j
  all_goals try { exact (hij rfl).elim }
  · have hcoord := congrArg (fun x : ResponseRing ↦ x.1.fst) hr
    norm_num [denominator, responseGenerator] at hcoord
  · have hcoord := congrArg (fun x : ResponseRing ↦ x.2.1) hr
    norm_num [denominator, responseGenerator] at hcoord
  · have hcoord := congrArg (fun x : ResponseRing ↦ x.1.fst) hr
    norm_num [denominator, responseGenerator] at hcoord
  · have hcoord := congrArg (fun x : ResponseRing ↦ x.2.2) hr
    norm_num [denominator, responseGenerator] at hcoord
  · have hcoord := congrArg (fun x : ResponseRing ↦ x.2.1) hr
    norm_num [denominator, responseGenerator] at hcoord
  · have hcoord := congrArg (fun x : ResponseRing ↦ x.2.2) hr
    norm_num [denominator, responseGenerator] at hcoord

abbrev quotientDenominator (i : Fin 3) :=
  Ideal.Quotient.mk (responseCore.obstructionIdeal base)
    (denominator i)

theorem quotientDenominator_isIdempotent (i : Fin 3) :
    IsIdempotentElem (quotientDenominator i) := by
  change quotientDenominator i * quotientDenominator i = quotientDenominator i
  change Ideal.Quotient.mk (responseCore.obstructionIdeal base)
      (denominator i * denominator i) =
    Ideal.Quotient.mk (responseCore.obstructionIdeal base) (denominator i)
  rw [denominator_mul_self]

theorem quotientDenominator_ne_zero (i : Fin 3) :
    quotientDenominator i ≠ 0 := by
  intro hz
  have hmem := Ideal.Quotient.eq_zero_iff_mem.mp hz
  exact denominator_not_mem_obstructionIdeal i hmem

theorem quotientDenominator_not_isNilpotent (i : Fin 3) :
    ¬ IsNilpotent (quotientDenominator i) := by
  intro hnil
  exact quotientDenominator_ne_zero i
    ((quotientDenominator_isIdempotent i).eq_zero_of_isNilpotent hnil)

theorem quotientDenominator_injective : Function.Injective quotientDenominator := by
  intro i j hq
  by_contra hij
  have hmem := (Ideal.Quotient.mk_eq_mk_iff_sub_mem
    (I := responseCore.obstructionIdeal base)
    (denominator i) (denominator j)).mp hq
  rw [response_obstructionIdeal, Ideal.mem_span_singleton'] at hmem
  obtain ⟨r, hr⟩ := hmem
  change ResponseRing at r
  fin_cases i <;> fin_cases j
  all_goals try { exact (hij rfl).elim }
  · have hcoord := congrArg (fun x : ResponseRing ↦ x.2.1) hr
    change r.2.1 * 0 = (1 : ResponseField) - 0 at hcoord
    norm_num at hcoord
  · have hcoord := congrArg (fun x : ResponseRing ↦ x.2.2) hr
    change r.2.2 * 0 = (0 : ResponseField) - 1 at hcoord
    norm_num at hcoord
  · have hcoord := congrArg (fun x : ResponseRing ↦ x.2.1) hr
    change r.2.1 * 0 = (0 : ResponseField) - 1 at hcoord
    norm_num at hcoord
  · have hcoord := congrArg (fun x : ResponseRing ↦ x.2.1) hr
    change r.2.1 * 0 = (0 : ResponseField) - 1 at hcoord
    norm_num at hcoord
  · have hcoord := congrArg (fun x : ResponseRing ↦ x.2.2) hr
    change r.2.2 * 0 = (1 : ResponseField) - 0 at hcoord
    norm_num at hcoord
  · have hcoord := congrArg (fun x : ResponseRing ↦ x.2.1) hr
    change r.2.1 * 0 = (1 : ResponseField) - 0 at hcoord
    norm_num at hcoord

theorem quotientDenominator_mul_ne_zero {i j : Fin 3} (hij : i ≠ j) :
    quotientDenominator i * quotientDenominator j ≠ 0 := by
  intro hz
  exact denominator_mul_not_mem_obstructionIdeal hij
    (Ideal.Quotient.eq_zero_iff_mem.mp hz)

theorem quotientDenominator_triple_mul_eq_zero :
    quotientDenominator 0 * quotientDenominator 1 * quotientDenominator 2 = 0 := by
  change Ideal.Quotient.mk (responseCore.obstructionIdeal base)
      (denominator 0 * denominator 1 * denominator 2) = 0
  rw [denominator_triple_mul_eq_zero, map_zero]

theorem lawfulChartOpen_ne_bot (i : Fin 3) :
    geometry.lawfulChartOpen (responseCore.obstructionIdeal base) i ≠ ⊥ := by
  change PrimeSpectrum.basicOpen (quotientDenominator i) ≠ ⊥
  intro hbot
  exact quotientDenominator_not_isNilpotent i
    ((PrimeSpectrum.basicOpen_eq_bot_iff _).mp hbot)

theorem lawfulChartOpen_inf_ne_bot {i j : Fin 3} (hij : i ≠ j) :
    geometry.lawfulChartOpen (responseCore.obstructionIdeal base) i ⊓
        geometry.lawfulChartOpen (responseCore.obstructionIdeal base) j ≠ ⊥ := by
  change PrimeSpectrum.basicOpen (quotientDenominator i) ⊓
      PrimeSpectrum.basicOpen (quotientDenominator j) ≠ ⊥
  rw [← PrimeSpectrum.basicOpen_mul]
  intro hbot
  have hnil := (PrimeSpectrum.basicOpen_eq_bot_iff _).mp hbot
  have hzero := ((quotientDenominator_isIdempotent i).mul
    (quotientDenominator_isIdempotent j)).eq_zero_of_isNilpotent hnil
  exact quotientDenominator_mul_ne_zero hij hzero

theorem lawfulChartOpen_triple_inf_eq_bot :
    geometry.lawfulChartOpen (responseCore.obstructionIdeal base) 0 ⊓
        geometry.lawfulChartOpen (responseCore.obstructionIdeal base) 1 ⊓
        geometry.lawfulChartOpen (responseCore.obstructionIdeal base) 2 = ⊥ := by
  change PrimeSpectrum.basicOpen (quotientDenominator 0) ⊓
      PrimeSpectrum.basicOpen (quotientDenominator 1) ⊓
      PrimeSpectrum.basicOpen (quotientDenominator 2) = ⊥
  rw [← PrimeSpectrum.basicOpen_mul, ← PrimeSpectrum.basicOpen_mul,
    quotientDenominator_triple_mul_eq_zero, PrimeSpectrum.basicOpen_zero]

theorem lawfulChartOpen_ne {i j : Fin 3} (hij : i ≠ j) :
    geometry.lawfulChartOpen (responseCore.obstructionIdeal base) i ≠
      geometry.lawfulChartOpen (responseCore.obstructionIdeal base) j := by
  change PrimeSpectrum.basicOpen (quotientDenominator i) ≠
    PrimeSpectrum.basicOpen (quotientDenominator j)
  intro hopen
  have hq := PrimeSpectrum.basicOpen_injOn_isIdempotentElem
    (quotientDenominator_isIdempotent i)
    (quotientDenominator_isIdempotent j) hopen
  exact hij (quotientDenominator_injective hq)

/-- Typed charts and the existing admissible AAT cover use the same index. -/
def chartEquivCoverIndex : Fin 3 ≃ cover.Index := Equiv.refl (Fin 3)

def aatPatch (i : Fin 3) : site.category :=
  Site.ContextCategoryObject.of contextPreorder
    (cover.patch (chartEquivCoverIndex i))

theorem aatPatch_injective : Function.Injective aatPatch := by
  intro i j hij
  apply chartEquivCoverIndex.injective
  apply cover_patch_injective
  exact Site.ContextCategoryObject.mk.inj hij

def aatPatchInclusion (i : Fin 3) : aatPatch i ⟶ base :=
  CategoryTheory.homOfLE (cover.inclusion (chartEquivCoverIndex i))

theorem aatCover_admissible :
    Site.AdmissibleCover coverageRequirements contextOverlap
      cover.toCoverageFamily :=
  cover.admissible

theorem selectedSupport_visibleOn_aatPatch :
    coverageRequirements.supportVisibleOn
      (cover.patch (chartEquivCoverIndex 0)) selectedLabel.2 := by
  apply Or.inl
  refine ⟨?_, rfl, PUnit.unit, ?_⟩
  · simp [cover, chartEquivCoverIndex, chartContextIndex]
  · exact FiniteModel.allFamily_mem _ (by simp [selectedLabel])

theorem aatPatch_pair_overlap (i j : Fin 3) :
    contextOverlap.overlap base.1
        (cover.patch (chartEquivCoverIndex i))
        (cover.patch (chartEquivCoverIndex j)) =
      context (chartContextIndex i ∪ chartContextIndex j) := by
  simp [contextOverlap, overlapContext, cover, chartEquivCoverIndex,
    recognized_context]

theorem aatPatch_zero_one_overlap :
    contextOverlap.overlap base.1
        (cover.patch (chartEquivCoverIndex 0))
        (cover.patch (chartEquivCoverIndex 1)) =
      context ({0, 1} : Finset (Fin 3)) := by
  simpa [chartContextIndex] using aatPatch_pair_overlap 0 1

/-- The three distinct principal opens cover the full lawful affine scheme. -/
theorem lawfulOpen_eq_top :
    geometry.lawfulOpen (responseCore.obstructionIdeal base) = ⊤ := by
  change (⨆ i, PrimeSpectrum.basicOpen
    (Ideal.Quotient.mk (responseCore.obstructionIdeal base)
      (geometry.denominator i))) = ⊤
  rw [PrimeSpectrum.iSup_basicOpen_eq_top_iff]
  apply (Ideal.eq_top_iff_one _).mpr
  have h₀ := Ideal.subset_span (show Ideal.Quotient.mk
    (responseCore.obstructionIdeal base) (geometry.denominator 0) ∈
      Set.range (fun i ↦ Ideal.Quotient.mk (responseCore.obstructionIdeal base)
        (geometry.denominator i)) from ⟨0, rfl⟩)
  have h₁ := Ideal.subset_span (show Ideal.Quotient.mk
    (responseCore.obstructionIdeal base) (geometry.denominator 1) ∈
      Set.range (fun i ↦ Ideal.Quotient.mk (responseCore.obstructionIdeal base)
        (geometry.denominator i)) from ⟨1, rfl⟩)
  have h₂ := Ideal.subset_span (show Ideal.Quotient.mk
    (responseCore.obstructionIdeal base) (geometry.denominator 2) ∈
      Set.range (fun i ↦ Ideal.Quotient.mk (responseCore.obstructionIdeal base)
        (geometry.denominator i)) from ⟨2, rfl⟩)
  have h₀₁ := Ideal.mul_mem_left _
    (Ideal.Quotient.mk (responseCore.obstructionIdeal base)
      (geometry.denominator 0)) h₁
  have h₀₂ := Ideal.mul_mem_left _
    (Ideal.Quotient.mk (responseCore.obstructionIdeal base)
      (geometry.denominator 0)) h₂
  have h₁₂ := Ideal.mul_mem_left _
    (Ideal.Quotient.mk (responseCore.obstructionIdeal base)
      (geometry.denominator 1)) h₂
  have hone : geometry.denominator 0 * geometry.denominator 1 +
      geometry.denominator 0 * geometry.denominator 2 +
      geometry.denominator 1 * geometry.denominator 2 = (1 : ResponseRing) := by
    change denominator 0 * denominator 1 + denominator 0 * denominator 2 +
      denominator 1 * denominator 2 = (1 : ResponseRing)
    ext <;> simp [denominator]
  rw [← map_one (Ideal.Quotient.mk (responseCore.obstructionIdeal base)),
    ← hone, map_add, map_add, map_mul, map_mul, map_mul]
  exact Ideal.add_mem _ (Ideal.add_mem _ h₀₁ h₀₂) h₁₂

/-- Localization of chart `0` maps canonically back to the dual-number factor. -/
noncomputable def chartZeroToDual : geometry.chartRing 0 →+* ResponseDual :=
  IsLocalization.Away.lift (S := geometry.chartRing 0) (P := ResponseDual)
    (geometry.denominator 0)
    (g := RingHom.fst ResponseDual (ResponseField × ResponseField)) (by
      change IsUnit (1 : ResponseDual)
      exact isUnit_one)

@[simp] theorem chartZeroToDual_algebraMap (a : ResponseRing) :
    chartZeroToDual
      (algebraMap (responseCore.Observable base) (geometry.chartRing 0) a) =
        a.1 := by
  rw [chartZeroToDual, IsLocalization.Away.lift_eq]
  rfl

/-- The `(0,1)` principal overlap maps canonically to the dual-number factor;
both chart denominators restrict to `1` there. -/
noncomputable def overlapZeroOneToDual : geometry.overlapRing 0 1 →+* ResponseDual :=
  IsLocalization.Away.lift (S := geometry.overlapRing 0 1) (P := ResponseDual)
    (geometry.denominator 0 * geometry.denominator 1)
    (g := RingHom.fst ResponseDual (ResponseField × ResponseField)) (by
      change IsUnit (1 : ResponseDual)
      exact isUnit_one)

@[simp] theorem overlapZeroOneToDual_algebraMap (a : ResponseRing) :
    overlapZeroOneToDual
      (algebraMap (responseCore.Observable base) (geometry.overlapRing 0 1) a) =
        a.1 := by
  rw [overlapZeroOneToDual, IsLocalization.Away.lift_eq]
  rfl

def dualSquareZeroIdeal : Ideal ResponseDual :=
  Ideal.span {TrivSqZeroExt.inr 1}

theorem dualConstant_not_mem_squareZeroIdeal :
    TrivSqZeroExt.inl (1 : ResponseField) ∉ dualSquareZeroIdeal := by
  intro h
  rw [dualSquareZeroIdeal, Ideal.mem_span_singleton'] at h
  obtain ⟨r, hr⟩ := h
  have hconstant := congrArg (fun x : ResponseDual ↦ x.fst) hr
  norm_num at hconstant

theorem map_fst_obstructionIdeal_le_dualSquareZeroIdeal :
    Ideal.map (RingHom.fst ResponseDual (ResponseField × ResponseField))
        (responseCore.obstructionIdeal base) ≤ dualSquareZeroIdeal := by
  rw [response_obstructionIdeal, Ideal.map_span]
  apply Ideal.span_le.mpr
  rintro x ⟨y, hy, rfl⟩
  simp only [Set.mem_singleton_iff] at hy
  subst y
  change TrivSqZeroExt.inr 1 ∈ dualSquareZeroIdeal
  exact Ideal.subset_span rfl

theorem responseValue_not_mem_chartZeroLawIdeal :
    algebraMap (responseCore.Observable base) (geometry.chartRing 0)
        responseValue ∉
      geometry.chartLawIdeal (responseCore.obstructionIdeal base) 0 := by
  intro h
  apply dualConstant_not_mem_squareZeroIdeal
  have hle : geometry.chartLawIdeal (responseCore.obstructionIdeal base) 0 ≤
      Ideal.comap chartZeroToDual dualSquareZeroIdeal := by
    change Ideal.map
      (algebraMap (responseCore.Observable base) (geometry.chartRing 0))
        (responseCore.obstructionIdeal base) ≤
          Ideal.comap chartZeroToDual dualSquareZeroIdeal
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    change chartZeroToDual
      (algebraMap (responseCore.Observable base) (geometry.chartRing 0) x) ∈
        dualSquareZeroIdeal
    rw [chartZeroToDual_algebraMap]
    exact map_fst_obstructionIdeal_le_dualSquareZeroIdeal
      (Ideal.mem_map_of_mem
        (RingHom.fst ResponseDual (ResponseField × ResponseField)) hx)
  have hh := hle h
  change chartZeroToDual
      (algebraMap (responseCore.Observable base) (geometry.chartRing 0)
        responseValue) ∈ dualSquareZeroIdeal at hh
  rw [chartZeroToDual_algebraMap] at hh
  exact hh

theorem responseValue_not_mem_overlapZeroOneLawIdeal :
    algebraMap (responseCore.Observable base) (geometry.overlapRing 0 1)
        responseValue ∉
      geometry.overlapLawIdeal (responseCore.obstructionIdeal base) 0 1 := by
  intro h
  apply dualConstant_not_mem_squareZeroIdeal
  have hle : geometry.overlapLawIdeal (responseCore.obstructionIdeal base) 0 1 ≤
      Ideal.comap overlapZeroOneToDual dualSquareZeroIdeal := by
    change Ideal.map
      (algebraMap (responseCore.Observable base) (geometry.overlapRing 0 1))
        (responseCore.obstructionIdeal base) ≤
          Ideal.comap overlapZeroOneToDual dualSquareZeroIdeal
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    change overlapZeroOneToDual
      (algebraMap (responseCore.Observable base) (geometry.overlapRing 0 1) x) ∈
        dualSquareZeroIdeal
    rw [overlapZeroOneToDual_algebraMap]
    exact map_fst_obstructionIdeal_le_dualSquareZeroIdeal
      (Ideal.mem_map_of_mem
        (RingHom.fst ResponseDual (ResponseField × ResponseField)) hx)
  have hh := hle h
  change overlapZeroOneToDual
      (algebraMap (responseCore.Observable base) (geometry.overlapRing 0 1)
        responseValue) ∈ dualSquareZeroIdeal at hh
  rw [overlapZeroOneToDual_algebraMap] at hh
  exact hh

@[simp] theorem selected_requiredGeneratorWitness_value :
    (LawGeneratedLabeledConormal.requiredGeneratorWitness
      responseCore base selectedLabel : responseCore.Observable base) =
      responseGenerator := by
  rfl

noncomputable def ambientQuotientDerivative :
    Derivation ResponseField ResponseRing
      (ResponseRing ⧸ responseCore.obstructionIdeal base) :=
  QuotientValuedDerivation.quotientDerivation
    (responseCore.obstructionIdeal base) epsilonDerivative

theorem ambient_selected_response_ne_zero :
    QuotientValuedDerivation.conormalResponse
        (responseCore.obstructionIdeal base) ambientQuotientDerivative
        (LawGeneratedLabeledConormal.requiredGeneratorConormal
          responseCore base selectedLabel) ≠ 0 := by
  rw [LawGeneratedLabeledConormal.requiredGeneratorConormal_toCotangent,
    QuotientValuedDerivation.conormalResponse_toCotangent,
    ambientQuotientDerivative,
    QuotientValuedDerivation.quotientDerivation_apply,
    selected_requiredGeneratorWitness_value]
  change Ideal.Quotient.mk (responseCore.obstructionIdeal base) responseValue ≠ 0
  intro hz
  exact responseValue_not_mem_obstructionIdeal
    (Ideal.Quotient.eq_zero_iff_mem.mp hz)

noncomputable def chartZeroDerivative :
    Derivation ResponseField (geometry.chartRing 0)
      (geometry.chartLawQuotient (responseCore.obstructionIdeal base) 0) :=
  presentation.chartQuotientDerivation geometry
    (responseCore.obstructionIdeal base) Unit.unit 0

noncomputable def overlapZeroOneDerivative :
    Derivation ResponseField (geometry.overlapRing 0 1)
      (geometry.overlapLawQuotient (responseCore.obstructionIdeal base) 0 1) :=
  presentation.overlapQuotientDerivation geometry
    (responseCore.obstructionIdeal base) Unit.unit 0 1

/-- The AAT patch carrying the selected support Atom detects a nonzero required
conormal response on its genuinely distinct principal chart. -/
theorem selectedSupportPatch_response_ne_zero :
    geometry.chartConormalJacobian (responseCore.obstructionIdeal base) 0
        chartZeroDerivative
        (LawGeneratedLabeledConormal.chartLabeledConormal
          responseCore base geometry selectedLabel 0) ≠ 0 := by
  change chartZeroDerivative
      (LawGeneratedLabeledConormal.chartRequiredGeneratorWitness
        responseCore base geometry selectedLabel 0 :
          geometry.chartLawIdeal (responseCore.obstructionIdeal base) 0).1 ≠ 0
  rw [show (LawGeneratedLabeledConormal.chartRequiredGeneratorWitness
      responseCore base geometry selectedLabel 0).1 =
        algebraMap (responseCore.Observable base) (geometry.chartRing 0)
          responseGenerator by rfl]
  rw [chartZeroDerivative,
    ArchitectureOperationPresentation.chartQuotientDerivation_algebraMap]
  change Ideal.Quotient.mk
      (geometry.chartLawIdeal (responseCore.obstructionIdeal base) 0)
      (algebraMap (responseCore.Observable base) (geometry.chartRing 0)
        responseValue) ≠ 0
  intro hz
  exact responseValue_not_mem_chartZeroLawIdeal
    ((Submodule.Quotient.mk_eq_zero _).mp hz)

theorem selectedSupportEdge_response_ne_zero :
    geometry.overlapConormalJacobian (responseCore.obstructionIdeal base) 0 1
        overlapZeroOneDerivative
        (LawGeneratedLabeledConormal.overlapLabeledConormal
          responseCore base geometry selectedLabel 0 1) ≠ 0 := by
  change overlapZeroOneDerivative
      (LawGeneratedLabeledConormal.overlapRequiredGeneratorWitness
        responseCore base geometry selectedLabel 0 1 :
          geometry.overlapLawIdeal (responseCore.obstructionIdeal base) 0 1).1 ≠ 0
  rw [show (LawGeneratedLabeledConormal.overlapRequiredGeneratorWitness
      responseCore base geometry selectedLabel 0 1).1 =
        algebraMap (responseCore.Observable base) (geometry.overlapRing 0 1)
          responseGenerator by rfl]
  rw [overlapZeroOneDerivative,
    ArchitectureOperationPresentation.overlapQuotientDerivation_algebraMap]
  change Ideal.Quotient.mk
      (geometry.overlapLawIdeal (responseCore.obstructionIdeal base) 0 1)
      (algebraMap (responseCore.Observable base) (geometry.overlapRing 0 1)
        responseValue) ≠ 0
  intro hz
  exact responseValue_not_mem_overlapZeroOneLawIdeal
    ((Submodule.Quotient.mk_eq_zero _).mp hz)

/-- The existing AAT patch visibility and the typed nonzero response are one
matched-index fact, rather than two independently named constructions. -/
theorem selectedSupportPatch_visible_and_response_ne_zero :
    coverageRequirements.supportVisibleOn
        (cover.patch (chartEquivCoverIndex 0)) selectedLabel.2 ∧
      geometry.chartConormalJacobian (responseCore.obstructionIdeal base) 0
          chartZeroDerivative
          (LawGeneratedLabeledConormal.chartLabeledConormal
            responseCore base geometry selectedLabel 0) ≠ 0 :=
  ⟨selectedSupport_visibleOn_aatPatch,
    selectedSupportPatch_response_ne_zero⟩

/-- The same selected support patch participates in an actual AAT overlap, and
the matched nonempty typed principal intersection carries the restricted
nonzero response. -/
theorem selectedSupportCircleEdge_visible_and_response_ne_zero :
    coverageRequirements.supportVisibleOn
        (cover.patch (chartEquivCoverIndex 0)) selectedLabel.2 ∧
      contextOverlap.overlap base.1
          (cover.patch (chartEquivCoverIndex 0))
          (cover.patch (chartEquivCoverIndex 1)) =
        context ({0, 1} : Finset (Fin 3)) ∧
      geometry.lawfulChartOpen (responseCore.obstructionIdeal base) 0 ⊓
          geometry.lawfulChartOpen (responseCore.obstructionIdeal base) 1 ≠ ⊥ ∧
      geometry.overlapConormalJacobian (responseCore.obstructionIdeal base) 0 1
          overlapZeroOneDerivative
          (LawGeneratedLabeledConormal.overlapLabeledConormal
            responseCore base geometry selectedLabel 0 1) ≠ 0 :=
  ⟨selectedSupport_visibleOn_aatPatch, aatPatch_zero_one_overlap,
    lawfulChartOpen_inf_ne_bot (by decide), selectedSupportEdge_response_ne_zero⟩

#assert_standard_axioms_only
  ResearchLean.AG.QualitySurface.IntrinsicLawResponseCircuitDescent.BooleanCircleOperationResponsePrototype

end BooleanCircleOperationResponsePrototype
end IntrinsicLawResponseCircuitDescent
end ResearchLean.AG.QualitySurface
