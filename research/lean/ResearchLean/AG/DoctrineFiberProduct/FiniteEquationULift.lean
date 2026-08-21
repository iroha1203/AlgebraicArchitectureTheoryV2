import ResearchLean.AG.DoctrineFiberProduct.FinitePackageULift

/-!
# Canonical finite-model equation universe lift

This module rebases the finite circuit syntax along the canonical equivalence
from `FiniteModel.carrier` to `finiteModelLiftCarrier`.  It then reconstructs
the selected finite-model NoCycle equation system directly on an arbitrary
lifted base object and context.  Residuals inspect every target object through
`finiteModelSemanticDescent`; no arbitrary equation reading, outside-image
default, package, reflection certificate, or cartesian conclusion is accepted
as input.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open AtomFoundation

/-! ## Cross-carrier circuit queries -/

/-- Rebase a finite-model circuit query along the canonical lifted Atom equivalence. -/
def finiteModelLiftCircuitQuery :
    CircuitQuery FiniteModel.carrier →
      CircuitQuery finiteModelLiftCarrier.{u}
  | .atomPresent atom =>
      .atomPresent (finiteModelLiftCarrierEquiv.atom atom)
  | .relationPresent first second =>
      .relationPresent (finiteModelLiftCarrierEquiv.atom first)
        (finiteModelLiftCarrierEquiv.atom second)
  | .identificationPresent first second =>
      .identificationPresent (finiteModelLiftCarrierEquiv.atom first)
        (finiteModelLiftCarrierEquiv.atom second)

/-- Reflect a lifted finite-model circuit query through the inverse Atom equivalence. -/
def finiteModelReflectCircuitQuery :
    CircuitQuery finiteModelLiftCarrier.{u} →
      CircuitQuery FiniteModel.carrier
  | .atomPresent atom =>
      .atomPresent (finiteModelLiftCarrierEquiv.atom.symm atom)
  | .relationPresent first second =>
      .relationPresent (finiteModelLiftCarrierEquiv.atom.symm first)
        (finiteModelLiftCarrierEquiv.atom.symm second)
  | .identificationPresent first second =>
      .identificationPresent (finiteModelLiftCarrierEquiv.atom.symm first)
        (finiteModelLiftCarrierEquiv.atom.symm second)

/-- Reflecting a canonically lifted source query recovers that query. -/
@[simp]
theorem finiteModelReflectCircuitQuery_lift
    (query : CircuitQuery FiniteModel.carrier) :
    finiteModelReflectCircuitQuery.{u}
        (finiteModelLiftCircuitQuery.{u} query) = query := by
  cases query <;> simp [finiteModelReflectCircuitQuery,
    finiteModelLiftCircuitQuery]

/-- Lifting a reflected target query recovers the original lifted query. -/
@[simp]
theorem finiteModelLiftCircuitQuery_reflect
    (query : CircuitQuery finiteModelLiftCarrier.{u}) :
    finiteModelLiftCircuitQuery.{u}
        (finiteModelReflectCircuitQuery.{u} query) = query := by
  cases query <;> simp [finiteModelReflectCircuitQuery,
    finiteModelLiftCircuitQuery]

/-- Canonical cross-carrier circuit-query rebasing is injective. -/
theorem finiteModelLiftCircuitQuery_injective :
    Function.Injective (finiteModelLiftCircuitQuery.{u}) :=
  Function.LeftInverse.injective finiteModelReflectCircuitQuery_lift.{u}

/--
A rebased query holds on an arbitrary lifted object exactly when the source
query holds on that object's finite-model semantic descent.
-/
@[simp]
theorem finiteModelLiftCircuitQuery_holds_iff
    (query : CircuitQuery FiniteModel.carrier)
    (object : ArchitectureObject finiteModelLiftCarrier.{u}) :
    (finiteModelLiftCircuitQuery.{u} query).Holds object ↔
      query.Holds (finiteModelSemanticDescent.{u} object) := by
  cases query <;>
    simp [finiteModelLiftCircuitQuery, CircuitQuery.Holds,
      finiteModelSemanticDescent, finiteModelReflectAtomConfiguration,
      finiteModelReflectAtomFamily, FiniteModel.objectOfConfiguration]

/--
An arbitrary lifted query has exactly the semantics of its reflected source
query on finite-model semantic descent.
-/
@[simp]
theorem finiteModelReflectCircuitQuery_holds_iff
    (query : CircuitQuery finiteModelLiftCarrier.{u})
    (object : ArchitectureObject finiteModelLiftCarrier.{u}) :
    query.Holds object ↔
      (finiteModelReflectCircuitQuery.{u} query).Holds
        (finiteModelSemanticDescent.{u} object) := by
  simpa using
    (finiteModelLiftCircuitQuery_holds_iff.{u}
      (finiteModelReflectCircuitQuery.{u} query) object)

/-! ## Cross-carrier finite circuit data -/

/-- Rebase every signed query in a finite-model circuit datum. -/
def finiteModelLiftFiniteCircuitDatum
    (datum : FiniteCircuitDatum FiniteModel.carrier) :
    FiniteCircuitDatum finiteModelLiftCarrier.{u} where
  queries := datum.queries.map fun pair =>
    (finiteModelLiftCircuitQuery.{u} pair.1, pair.2)

/-- Reflect every signed query in a lifted finite-model circuit datum. -/
def finiteModelReflectFiniteCircuitDatum
    (datum : FiniteCircuitDatum finiteModelLiftCarrier.{u}) :
    FiniteCircuitDatum FiniteModel.carrier where
  queries := datum.queries.map fun pair =>
    (finiteModelReflectCircuitQuery.{u} pair.1, pair.2)

/-- Reflecting a canonically lifted source datum recovers that datum. -/
@[simp]
theorem finiteModelReflectFiniteCircuitDatum_lift
    (datum : FiniteCircuitDatum FiniteModel.carrier) :
    finiteModelReflectFiniteCircuitDatum.{u}
        (finiteModelLiftFiniteCircuitDatum.{u} datum) = datum := by
  cases datum with
  | mk queries =>
      simp [finiteModelReflectFiniteCircuitDatum,
        finiteModelLiftFiniteCircuitDatum, Function.comp_def,
        finiteModelReflectCircuitQuery_lift]

/-- Lifting a reflected target datum recovers the original lifted datum. -/
@[simp]
theorem finiteModelLiftFiniteCircuitDatum_reflect
    (datum : FiniteCircuitDatum finiteModelLiftCarrier.{u}) :
    finiteModelLiftFiniteCircuitDatum.{u}
        (finiteModelReflectFiniteCircuitDatum.{u} datum) = datum := by
  cases datum with
  | mk queries =>
      simp [finiteModelReflectFiniteCircuitDatum,
        finiteModelLiftFiniteCircuitDatum, Function.comp_def,
        finiteModelLiftCircuitQuery_reflect]

/-- Canonical cross-carrier finite-datum rebasing is injective. -/
theorem finiteModelLiftFiniteCircuitDatum_injective :
    Function.Injective (finiteModelLiftFiniteCircuitDatum.{u}) :=
  Function.LeftInverse.injective finiteModelReflectFiniteCircuitDatum_lift.{u}

/--
A rebased signed datum matches an arbitrary lifted object exactly when the
source datum matches its finite-model semantic descent.
-/
@[simp]
theorem finiteModelLiftFiniteCircuitDatum_matches_iff
    (datum : FiniteCircuitDatum FiniteModel.carrier)
    (object : ArchitectureObject finiteModelLiftCarrier.{u}) :
    (finiteModelLiftFiniteCircuitDatum.{u} datum).Matches object ↔
      datum.Matches (finiteModelSemanticDescent.{u} object) := by
  constructor
  · intro hmatches query expected hmem
    have hmapped := hmatches (finiteModelLiftCircuitQuery.{u} query) expected
      (List.mem_map.mpr ⟨(query, expected), hmem, rfl⟩)
    exact (finiteModelLiftCircuitQuery_holds_iff.{u} query object).symm.trans
      hmapped
  · intro hmatches query expected hmem
    rcases List.mem_map.mp hmem with ⟨pair, hpair, hp⟩
    cases hp
    exact (finiteModelLiftCircuitQuery_holds_iff.{u} pair.1 object).trans
      (hmatches pair.1 pair.2 hpair)

/--
An arbitrary lifted signed datum matches exactly when its reflected source
datum matches the semantic descent of the same object.
-/
@[simp]
theorem finiteModelReflectFiniteCircuitDatum_matches_iff
    (datum : FiniteCircuitDatum finiteModelLiftCarrier.{u})
    (object : ArchitectureObject finiteModelLiftCarrier.{u}) :
    datum.Matches object ↔
      (finiteModelReflectFiniteCircuitDatum.{u} datum).Matches
        (finiteModelSemanticDescent.{u} object) := by
  simpa using
    (finiteModelLiftFiniteCircuitDatum_matches_iff.{u}
      (finiteModelReflectFiniteCircuitDatum.{u} datum) object)

/-! ## Cross-carrier detector syntax -/

/-- Recursively rebase finite-model detector syntax and every exact template. -/
def finiteModelLiftCircuitDetectorCode :
    CircuitDetectorCode FiniteModel.carrier →
      CircuitDetectorCode finiteModelLiftCarrier.{u}
  | .reject => .reject
  | .exact pattern => .exact (finiteModelLiftFiniteCircuitDatum.{u} pattern)
  | .any left right =>
      .any (finiteModelLiftCircuitDetectorCode left)
        (finiteModelLiftCircuitDetectorCode right)

/-- Recursively reflect lifted finite-model detector syntax and its templates. -/
def finiteModelReflectCircuitDetectorCode :
    CircuitDetectorCode finiteModelLiftCarrier.{u} →
      CircuitDetectorCode FiniteModel.carrier
  | .reject => .reject
  | .exact pattern => .exact (finiteModelReflectFiniteCircuitDatum.{u} pattern)
  | .any left right =>
      .any (finiteModelReflectCircuitDetectorCode left)
        (finiteModelReflectCircuitDetectorCode right)

/-- Reflecting canonically lifted detector syntax recovers the source code. -/
@[simp]
theorem finiteModelReflectCircuitDetectorCode_lift
    (code : CircuitDetectorCode FiniteModel.carrier) :
    finiteModelReflectCircuitDetectorCode.{u}
        (finiteModelLiftCircuitDetectorCode.{u} code) = code := by
  induction code with
  | reject => rfl
  | exact pattern =>
      simp [finiteModelReflectCircuitDetectorCode,
        finiteModelLiftCircuitDetectorCode,
        finiteModelReflectFiniteCircuitDatum_lift]
  | any left right hleft hright =>
      simp [finiteModelReflectCircuitDetectorCode,
        finiteModelLiftCircuitDetectorCode, hleft, hright]

/-- Lifting reflected target detector syntax recovers the original code. -/
@[simp]
theorem finiteModelLiftCircuitDetectorCode_reflect
    (code : CircuitDetectorCode finiteModelLiftCarrier.{u}) :
    finiteModelLiftCircuitDetectorCode.{u}
        (finiteModelReflectCircuitDetectorCode.{u} code) = code := by
  induction code with
  | reject => rfl
  | exact pattern =>
      simp [finiteModelReflectCircuitDetectorCode,
        finiteModelLiftCircuitDetectorCode,
        finiteModelLiftFiniteCircuitDatum_reflect]
  | any left right hleft hright =>
      simp [finiteModelReflectCircuitDetectorCode,
        finiteModelLiftCircuitDetectorCode, hleft, hright]

/-- Canonical recursive detector-code rebasing is injective. -/
theorem finiteModelLiftCircuitDetectorCode_injective :
    Function.Injective (finiteModelLiftCircuitDetectorCode.{u}) :=
  Function.LeftInverse.injective finiteModelReflectCircuitDetectorCode_lift.{u}

/--
Evaluating rebased detector syntax on rebased signed data gives the original
finite-model Boolean result.
-/
theorem finiteModelLiftCircuitDetectorCode_eval
    (code : CircuitDetectorCode FiniteModel.carrier)
    (datum : FiniteCircuitDatum FiniteModel.carrier) :
    (finiteModelLiftCircuitDetectorCode.{u} code).eval
        (finiteModelLiftFiniteCircuitDatum.{u} datum) = code.eval datum := by
  induction code with
  | reject =>
      simp [finiteModelLiftCircuitDetectorCode, CircuitDetectorCode.eval]
  | exact pattern =>
      by_cases hpattern : pattern = datum
      · subst datum
        simp [finiteModelLiftCircuitDetectorCode, CircuitDetectorCode.eval]
      · have hlift :
          finiteModelLiftFiniteCircuitDatum.{u} pattern ≠
            finiteModelLiftFiniteCircuitDatum.{u} datum :=
          fun heq => hpattern
            (finiteModelLiftFiniteCircuitDatum_injective.{u} heq)
        simp [finiteModelLiftCircuitDetectorCode, CircuitDetectorCode.eval,
          hpattern, hlift]
  | any left right hleft hright =>
      simp [finiteModelLiftCircuitDetectorCode, CircuitDetectorCode.eval,
        hleft, hright]

/--
A lifted source detector evaluated on an arbitrary lifted datum agrees with
the source detector evaluated on the reflected datum.
-/
theorem finiteModelLiftCircuitDetectorCode_eval_reflect
    (code : CircuitDetectorCode FiniteModel.carrier)
    (datum : FiniteCircuitDatum finiteModelLiftCarrier.{u}) :
    (finiteModelLiftCircuitDetectorCode.{u} code).eval datum =
      code.eval (finiteModelReflectFiniteCircuitDatum.{u} datum) := by
  simpa using
    (finiteModelLiftCircuitDetectorCode_eval.{u} code
      (finiteModelReflectFiniteCircuitDatum.{u} datum))

/--
Evaluation of arbitrary lifted detector syntax is completely reflected to the
base finite carrier.
-/
theorem finiteModelReflectCircuitDetectorCode_eval
    (code : CircuitDetectorCode finiteModelLiftCarrier.{u})
    (datum : FiniteCircuitDatum finiteModelLiftCarrier.{u}) :
    code.eval datum =
      (finiteModelReflectCircuitDetectorCode.{u} code).eval
        (finiteModelReflectFiniteCircuitDatum.{u} datum) := by
  simpa using
    (finiteModelLiftCircuitDetectorCode_eval_reflect.{u}
      (finiteModelReflectCircuitDetectorCode.{u} code) datum)

/-! ## Direct lifted finite-model equation system -/

/--
A canonical context used only to expose one residual coordinate when proving
NoCycle reflection for an arbitrary selected lifted base object.
-/
def finiteModelLiftEquationProbeContext
    (base : ArchitectureObject finiteModelLiftCarrier.{u}) :
    Site.ArchCtx base where
  minimal := {
    Support := ULift.{u} PUnit
    Axis := ULift.{u} PUnit
    Observable := ULift.{u} PUnit
    supportReads := fun _ atom => base.configuration.family.mem atom
    supportReads_objectFamily := fun hselected => hselected
    axisReads := fun _ => True
    observableReads := fun _ => True
  }
  Extension := ULift.{u} PUnit
  extension := ULift.up PUnit.unit

/--
The direct lifted finite-model equation system.  Its residual on every target
object is the lifted source NoCycle residual of that object's semantic descent.
-/
noncomputable def finiteModelLiftEquationSystem
    {base : ArchitectureObject finiteModelLiftCarrier.{u}}
    (context : Site.ContextPreorderCategory base) :
    ArchitecturalEquationSystem context where
  Index := ULift.{u} (FiniteModel.equationSystem
    (Site.contextMorphismPreorderCategory FiniteModel.object)).Index
  role _ := EquationRole.required
  Observable := fun _ => ULift.{u} Int
  observableCommRing := fun _ => inferInstance
  restrict := fun _ => RingHom.id (ULift.{u} Int)
  restrict_id := by intros; rfl
  restrict_comp := by intros; rfl
  violationCoordinate := fun _ _ _ => ULift.up 2
  violationCoordinate_restrict := by intros; rfl
  equationResidual := fun _ object _ _ =>
    ULift.up (FiniteModel.noCycleResidual
      (finiteModelSemanticDescent.{u} object))
  equationResidual_restrict := by intros; rfl

/--
The direct lifted equation holds exactly when semantic descent has no selected
finite-model dependency cycle.
-/
theorem finiteModelLiftEquationHolds_iff_noCycle
    {base : ArchitectureObject finiteModelLiftCarrier.{u}}
    (context : Site.ContextPreorderCategory base)
    (object : ArchitectureObject finiteModelLiftCarrier.{u}) :
    (finiteModelLiftEquationSystem.{u} context).EquationHolds
        (ULift.up PUnit.unit) object ↔
      ¬ FiniteModel.hasDependencyCycle
        (finiteModelSemanticDescent.{u} object) := by
  constructor
  · intro hequation hcycle
    have hzero := hequation
      (Site.ContextCategoryObject.of context
        (finiteModelLiftEquationProbeContext.{u} base))
      (finiteModelLiftCarrierEquiv.atom FiniteModel.FiniteAtom.componentA)
    have hzeroDown := congrArg ULift.down hzero
    simp [finiteModelLiftEquationSystem, FiniteModel.noCycleResidual,
      hcycle] at hzeroDown
  · intro hncycle contextObject atom
    apply ULift.ext
    simp [finiteModelLiftEquationSystem, FiniteModel.noCycleResidual,
      hncycle]

/--
Lifted equation fulfillment is exactly fulfillment of the reviewed source
NoCycle equation on the semantic descent of the same object.
-/
theorem finiteModelLiftEquationHolds_iff_source
    {base : ArchitectureObject finiteModelLiftCarrier.{u}}
    (context : Site.ContextPreorderCategory base)
    (object : ArchitectureObject finiteModelLiftCarrier.{u}) :
    (finiteModelLiftEquationSystem.{u} context).EquationHolds
        (ULift.up PUnit.unit) object ↔
      (FiniteModel.equationSystem
          (Site.contextMorphismPreorderCategory FiniteModel.object)).EquationHolds
        PUnit.unit (finiteModelSemanticDescent.{u} object) := by
  rw [finiteModelLiftEquationHolds_iff_noCycle,
    FiniteModel.equationHolds_iff_noCycle]

/-! ## Exact lifted cycle detector -/

/-- The lifted exact three-edge dependency-cycle query datum. -/
def finiteModelLiftCycleQueryDatum :
    FiniteCircuitDatum finiteModelLiftCarrier.{u} :=
  finiteModelLiftFiniteCircuitDatum.{u} FiniteModel.cycleQueryDatum

/--
The equation-indexed detector reading selecting exactly the lifted finite-model
three-edge cycle datum.
-/
noncomputable def finiteModelLiftEquationCircuitReading
    {base : ArchitectureObject finiteModelLiftCarrier.{u}}
    (context : Site.ContextPreorderCategory base) :
    EquationCircuitReading (finiteModelLiftEquationSystem.{u} context) where
  code _ := .exact finiteModelLiftCycleQueryDatum.{u}

/--
The lifted detector at the lifted singleton index is the canonical rebase of
the reviewed source detector.
-/
@[simp]
theorem finiteModelLiftEquationCircuitReading_code
    {base : ArchitectureObject finiteModelLiftCarrier.{u}}
    (context : Site.ContextPreorderCategory base)
    (index : (FiniteModel.equationSystem
      (Site.contextMorphismPreorderCategory FiniteModel.object)).Index) :
    (finiteModelLiftEquationCircuitReading.{u} context).code
        (ULift.up index) =
      finiteModelLiftCircuitDetectorCode.{u}
        ((FiniteModel.equationCircuitReading
          (Site.contextMorphismPreorderCategory FiniteModel.object)).code index) := by
  cases index
  rfl

/--
Detector evaluation at the lifted singleton index reflects every lifted datum
to the reviewed source detector evaluation.
-/
theorem finiteModelLiftEquationCircuitReading_eval_reflect
    {base : ArchitectureObject finiteModelLiftCarrier.{u}}
    (context : Site.ContextPreorderCategory base)
    (index : (FiniteModel.equationSystem
      (Site.contextMorphismPreorderCategory FiniteModel.object)).Index)
    (datum : FiniteCircuitDatum finiteModelLiftCarrier.{u}) :
    ((finiteModelLiftEquationCircuitReading.{u} context).code
        (ULift.up index)).eval datum =
      ((FiniteModel.equationCircuitReading
          (Site.contextMorphismPreorderCategory FiniteModel.object)).code index).eval
        (finiteModelReflectFiniteCircuitDatum.{u} datum) := by
  rw [finiteModelLiftEquationCircuitReading_code]
  exact finiteModelLiftCircuitDetectorCode_eval_reflect.{u} _ datum

/--
The exact lifted cycle detector is sound on every lifted architecture object,
including objects outside the canonical architecture-object image.
-/
theorem finiteModelLiftEquationCircuitReading_sound
    {base : ArchitectureObject finiteModelLiftCarrier.{u}}
    (context : Site.ContextPreorderCategory base) :
    (finiteModelLiftEquationCircuitReading.{u} context).Sound := by
  intro index object datum hmatches haccepts
  rcases index with ⟨index⟩
  cases index
  change (CircuitDetectorCode.exact finiteModelLiftCycleQueryDatum.{u}).eval
    datum = true at haccepts
  have hdatum : finiteModelLiftCycleQueryDatum.{u} = datum :=
    (CircuitDetectorCode.eval_exact_eq_true_iff
      finiteModelLiftCycleQueryDatum.{u} datum).mp haccepts
  subst datum
  have hbaseMatches :
      FiniteModel.cycleQueryDatum.Matches
        (finiteModelSemanticDescent.{u} object) :=
    (finiteModelLiftFiniteCircuitDatum_matches_iff.{u}
      FiniteModel.cycleQueryDatum object).mp hmatches
  have hab :
      (finiteModelSemanticDescent.{u} object).configuration.relation
        FiniteModel.FiniteAtom.dependsAB FiniteModel.FiniteAtom.dependsBC :=
    ((hbaseMatches
      (.relationPresent FiniteModel.FiniteAtom.dependsAB
        FiniteModel.FiniteAtom.dependsBC) true
      (by simp [FiniteModel.cycleQueryDatum])).mpr rfl).2.2
  have hbc :
      (finiteModelSemanticDescent.{u} object).configuration.relation
        FiniteModel.FiniteAtom.dependsBC FiniteModel.FiniteAtom.dependsCA :=
    ((hbaseMatches
      (.relationPresent FiniteModel.FiniteAtom.dependsBC
        FiniteModel.FiniteAtom.dependsCA) true
      (by simp [FiniteModel.cycleQueryDatum])).mpr rfl).2.2
  have hca :
      (finiteModelSemanticDescent.{u} object).configuration.relation
        FiniteModel.FiniteAtom.dependsCA FiniteModel.FiniteAtom.dependsAB :=
    ((hbaseMatches
      (.relationPresent FiniteModel.FiniteAtom.dependsCA
        FiniteModel.FiniteAtom.dependsAB) true
      (by simp [FiniteModel.cycleQueryDatum])).mpr rfl).2.2
  intro hequation
  exact (finiteModelLiftEquationHolds_iff_noCycle.{u} context object).mp
    hequation ⟨hab, hbc, hca⟩

/-! ## Canonical lifted finite-model equation reading -/

/--
Package the direct lifted NoCycle system and exact detector over any selected
lifted base object and context preorder.
-/
noncomputable def finiteModelLiftEquationReadingFor
    {base : ArchitectureObject finiteModelLiftCarrier.{u}}
    (context : Site.ContextPreorderCategory base) :
    EquationReading base where
  contextPreorder := context
  equationSystem := finiteModelLiftEquationSystem.{u} context
  circuits := finiteModelLiftEquationCircuitReading.{u} context
  circuitSound := finiteModelLiftEquationCircuitReading_sound.{u} context

/--
Package the direct lifted NoCycle system and exact detector over a selected
context preorder on the canonical lifted finite-model object.
-/
noncomputable def finiteModelLiftEquationReading
    (context : Site.ContextPreorderCategory
      (finiteModelLiftArchitectureObject.{u} FiniteModel.object)) :
    EquationReading
      (finiteModelLiftArchitectureObject.{u} FiniteModel.object) :=
  finiteModelLiftEquationReadingFor.{u} context

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
