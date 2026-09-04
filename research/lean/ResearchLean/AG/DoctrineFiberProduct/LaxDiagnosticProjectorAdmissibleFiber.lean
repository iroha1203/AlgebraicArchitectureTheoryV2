import ResearchLean.AG.DoctrineFiberProduct.BCAuthoredCanonicalObjectNormalization
import ResearchLean.AG.CrossStageCoherence.CorePseudofunctor

/-!
# Admissible core fibers for the lax diagnostic projector

Canonical object-normalization admissibility is preserved by every canonical
`transportAlong`.  Consequently the admissible packages in each core fiber form
a full subcategory, and core-fiber transport restricts to these subcategories.

## Implementation notes

The five admissibility fields are transported separately.  Equation residuals
use configuration invariance through equation-reading transport and its base
cast.  Operation types use inverse object transport; operation naturality also
records the required dependent-cast `HEq`.  Invariants are conjugated by inverse
object transport, while signature coordinates use the same object-transport
identity.  The restricted functor is the standard full-subcategory lift of the
existing `coreFiberTransportFunctor`.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation CrossStageCoherence

/-- G-117(a) object route: inverse Atom transport commutes with canonical
object normalization, using only the source package and exact doctrine map. -/
theorem transportArchitectureObject_symm_canonicalObjectNormalization
    {U : AtomCarrier.{u}} (P : AATCorePackage U)
    {E : ExtractionDoctrine U}
    (f : ExactDoctrineHom P.reading.doctrine E)
    (object : ArchitectureObject U) :
    transportArchitectureObject f.atomEquiv.symm
        (canonicalObjectNormalization (transportAlong P f) object) =
      canonicalObjectNormalization P
        (transportArchitectureObject f.atomEquiv.symm object) := by
  unfold canonicalObjectNormalization transportAlong transportCoreReading
    transportObjectReading
  simp [transportArchitectureObject]

/-- G-117(a) equation route: source configuration-only residual dependence
survives canonical package transport, including the equation-reading base cast. -/
theorem equationResidualConfigurationInvariant_transportAlong
    {U : AtomCarrier.{u}} (P : AATCorePackage U)
    (invariant : EquationResidualConfigurationInvariant
      P.algebra.equationSystem)
    {E : ExtractionDoctrine U}
    (f : ExactDoctrineHom P.reading.doctrine E) :
    EquationResidualConfigurationInvariant
      (transportAlong P f).algebra.equationSystem := by
  unfold transportAlong transportCoreReading
  apply castEquationResidual_configurationInvariant
  apply transportEquationResidual_configurationInvariant
  exact invariant

/-- G-117(a) invariant route: a supplied source self-naturality proof is
preserved after conjugating the invariant and normalization by Atom transport. -/
theorem transportedInvariant_self_naturality
    {U : AtomCarrier.{u}} (e : Equiv U.Atom U.Atom) (I : Invariant U)
    (normalization : ArchitectureObject U → ArchitectureObject U)
    (targetNormalization : ArchitectureObject U → ArchitectureObject U)
    (h : Invariant.TransportedAlong I I _root_.id normalization)
    (commutes : ∀ object,
      transportArchitectureObject e.symm (targetNormalization object) =
        normalization (transportArchitectureObject e.symm object)) :
    Invariant.TransportedAlong (transportInvariant e I)
      (transportInvariant e I) _root_.id targetNormalization := by
  cases I with
  | function I =>
      rcases h with ⟨valueEquiv, hvalue⟩
      refine ⟨valueEquiv, ?_⟩
      intro object
      change valueEquiv
          (I.evaluate (transportArchitectureObject e.symm object)) =
        I.evaluate
          (transportArchitectureObject e.symm (targetNormalization object))
      rw [commutes]
      exact hvalue (transportArchitectureObject e.symm object)
  | predicate I =>
      intro object
      change I.holds (transportArchitectureObject e.symm object) ↔
        I.holds
          (transportArchitectureObject e.symm (targetNormalization object))
      rw [commutes]
      exact h (transportArchitectureObject e.symm object)

/-- G-117(a) operation-cast route: dependently typed operations identified by
`HEq` have equal configuration atom maps after identifying both endpoints. -/
theorem operationConfigurationMap_atomMap_eq_of_heq
    {U : AtomCarrier.{u}} (R : OperationReading U)
    {first second first' second' : ArchitectureObject U}
    (first_eq : first = first') (second_eq : second = second')
    {operation : R.Op first second} {operation' : R.Op first' second'}
    (operation_heq : HEq operation operation') :
    (R.configurationMap operation).atomMap =
      (R.configurationMap operation').atomMap := by
  subst first'
  subst second'
  cases operation_heq
  rfl

/-- G-117(a): the supplied source normalization-admissibility direction
hypothesis is transported to the target of every exact canonical package map. -/
theorem canonicalObjectNormalizationAdmissible_transportAlong
    {U : AtomCarrier.{u}} (P : AATCorePackage U)
    (admissible : CanonicalObjectNormalizationAdmissible P)
    {E : ExtractionDoctrine U}
    (f : ExactDoctrineHom P.reading.doctrine E) :
    CanonicalObjectNormalizationAdmissible (transportAlong P f) := by
  let operationTypeEq : ∀ first second,
      (transportAlong P f).reading.operationReading.Op first second =
        (transportAlong P f).reading.operationReading.Op
          (canonicalObjectNormalization (transportAlong P f) first)
          (canonicalObjectNormalization (transportAlong P f) second) := by
    intro first second
    change P.reading.operationReading.Op
        (transportArchitectureObject f.atomEquiv.symm first)
        (transportArchitectureObject f.atomEquiv.symm second) =
      P.reading.operationReading.Op
        (transportArchitectureObject f.atomEquiv.symm
          (canonicalObjectNormalization (transportAlong P f) first))
        (transportArchitectureObject f.atomEquiv.symm
          (canonicalObjectNormalization (transportAlong P f) second))
    rw [transportArchitectureObject_symm_canonicalObjectNormalization,
      transportArchitectureObject_symm_canonicalObjectNormalization]
    exact admissible.operation_type_eq _ _
  refine {
    equationResidual_eq := ?_
    operation_type_eq := operationTypeEq
    operation_naturality := ?_
    invariant_transport := ?_
    coordinate_eq := ?_ }
  · intro W object index atom
    apply equationResidualConfigurationInvariant_transportAlong P
      admissible.equationResidual_configurationInvariant f
    exact (canonicalObjectNormalization_configuration
      (transportAlong P f) object).symm
  · intro first second operation
    have hnat := congrArg ConfigurationHom.atomMap
      (admissible.operation_naturality
        (transportArchitectureObject f.atomEquiv.symm first)
        (transportArchitectureObject f.atomEquiv.symm second)
        operation)
    apply ConfigurationHom.ext
    simp only [castConfigurationHom_atomMap,
      transportAlong, transportCoreReading, transportOperationReading,
      transportConfigurationHom_atomMap, ConfigurationHom.comp,
      canonicalObjectNormalizationConfigurationHom_atomMap] at hnat ⊢
    apply funext
    intro atom
    apply f.atomEquiv.injective
    simp only [Function.comp_apply]
    rw [operationConfigurationMap_atomMap_eq_of_heq
      P.reading.operationReading
      (transportArchitectureObject_symm_canonicalObjectNormalization P f first)
      (transportArchitectureObject_symm_canonicalObjectNormalization P f second)
      ((cast_heq (operationTypeEq first second) operation).trans
        (cast_heq
          (admissible.operation_type_eq
            (transportArchitectureObject f.atomEquiv.symm first)
            (transportArchitectureObject f.atomEquiv.symm second))
          operation).symm)]
    simpa [Function.comp_def] using congrFun hnat (f.atomEquiv.symm atom)
  · intro index
    apply transportedInvariant_self_naturality f.atomEquiv
      (P.reading.invariantReading.invariant index)
      (canonicalObjectNormalization P)
      (canonicalObjectNormalization (transportAlong P f))
      (admissible.invariant_transport index)
    exact transportArchitectureObject_symm_canonicalObjectNormalization P f
  · intro object axis
    change P.reading.signatureReading.coordinate
        (transportArchitectureObject f.atomEquiv.symm object) axis =
      P.reading.signatureReading.coordinate
        (transportArchitectureObject f.atomEquiv.symm
          (canonicalObjectNormalization (transportAlong P f) object)) axis
    rw [transportArchitectureObject_symm_canonicalObjectNormalization]
    exact admissible.coordinate_eq _ _

/-- G-117(b): the object property selecting packages carrying the source-side
normalization-admissibility direction hypothesis in one core fiber. -/
def admissibleCoreFiberObjectProperty
    {U : AtomCarrier.{u}} (X : ExtractionInstance U) :
    ObjectProperty (CoreFiber X) :=
  fun P ↦ CanonicalObjectNormalizationAdmissible P.1

/-- G-117(b): the full subcategory of a core fiber on packages carrying the
normalization-admissibility direction hypothesis. -/
abbrev AdmCoreFiber {U : AtomCarrier.{u}} (X : ExtractionInstance U) :=
  (admissibleCoreFiberObjectProperty X).FullSubcategory

/-- G-117(b): core-fiber transport restricted to the admissible full
subcategories; target membership is generated by G-117(a). -/
noncomputable def admissibleCoreFiberTransportFunctor
    {U : AtomCarrier.{u}} {X Y : ExtractionInstance U} (sigma : X ⟶ Y) :
    Functor (AdmCoreFiber X) (AdmCoreFiber Y) :=
  (admissibleCoreFiberObjectProperty Y).lift
    ((admissibleCoreFiberObjectProperty X).ι ⋙ coreFiberTransportFunctor sigma)
    (fun P ↦ canonicalObjectNormalizationAdmissible_transportAlong
      P.obj.1 P.property (coreFiberBaseHom sigma P.obj).doctrineHom)

/-- G-117(b) object API: forgetting target admissibility exposes exactly the
object selected by the existing core-fiber transport functor. -/
@[simp]
theorem admissibleCoreFiberTransportFunctor_obj_obj
    {U : AtomCarrier.{u}} {X Y : ExtractionInstance U} (sigma : X ⟶ Y)
    (P : AdmCoreFiber X) :
    ((admissibleCoreFiberTransportFunctor sigma).obj P).obj =
      (coreFiberTransportFunctor sigma).obj P.obj :=
  rfl

/-- G-117(b) morphism API: forgetting target admissibility exposes exactly the
map of the existing core-fiber transport functor. -/
@[simp]
theorem admissibleCoreFiberTransportFunctor_map_hom
    {U : AtomCarrier.{u}} {X Y : ExtractionInstance U} (sigma : X ⟶ Y)
    {P Q : AdmCoreFiber X} (f : P ⟶ Q) :
    ((admissibleCoreFiberTransportFunctor sigma).map f).hom =
      (coreFiberTransportFunctor sigma).map f.hom :=
  rfl

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
