import Formal.AG.Atom.Axioms
import Formal.AG.Atom.ObjectAlgebra

namespace AAT.AG

universe u

/-!
# AAT core generation

This module implements the Part I Definitions 10.1 and 10.4A admissible-reading
construction used by Theorem 10.5.  Its implementation declaration is compared
directly with the task's primary specification during review.  A core stores
only the Atom axioms and the reading rules.  Its family, configuration,
architecture object, and operation-closed algebra are derived definitions.

## Implementation notes

The earlier component-assembly package was not retained as the primary
constructor because it accepted the conclusions of the generation route as
inputs.  The reachable-object subtype is used for the object algebra so its
objects are exactly those generated from the base object by the selected
operation family.
-/

/-- Part I composition rule acting on every explicitly list-finite Atom family. -/
structure CompositionReading (U : AtomCarrier.{u}) where
  /-- Construct a configuration from any explicitly finite Atom family. -/
  compose : (F : AtomFamily U) -> F.ListFinite -> AtomConfiguration U
  family_eq : ∀ F hfinite, (compose F hfinite).family = F
  family_supported : ∀ F hfinite, (compose F hfinite).FamilySupported

/-- Part I object-formation rule acting on every Atom configuration. -/
structure ObjectReading (U : AtomCarrier.{u}) where
  /-- Construct an architecture object from any Atom configuration. -/
  object : AtomConfiguration U -> ArchitectureObject U
  configuration_eq : ∀ C, (object C).configuration = C

/-- The admissible Part I reading from which the complete core is generated. -/
structure CoreReading (U : AtomCarrier.{u}) where
  /-- Source extraction doctrine. -/
  doctrine : ExtractionDoctrine U
  /-- Source selected for canonical atomization. -/
  source : doctrine.Source
  family_listFinite : (doctrine.atomize source).ListFinite
  /-- Configuration composition rule. -/
  composition : CompositionReading U
  /-- Architecture-object formation rule. -/
  objectReading : ObjectReading U
  /-- Context, architectural equation, and equation-indexed circuit reading. -/
  equationReading : EquationReading
    (objectReading.object
      (composition.compose (doctrine.atomize source) family_listFinite))
  /-- Invariant reading. -/
  invariantReading : InvariantFamily U
  /-- Architecture signature reading. -/
  signatureReading : ArchitectureSignature U
  /-- Object-pair-indexed operation reading. -/
  operationReading : OperationReading U

/-- Part I theorem 10.5 input package: axioms together with an admissible reading. -/
structure AATCorePackage (U : AtomCarrier.{u}) where
  axioms : AtomAxiomSystem U
  /-- The admissible reading from which all core components are derived. -/
  reading : CoreReading U

namespace CompositionReading

/-- Composition readings are equal when their configuration constructors agree. -/
@[ext]
theorem ext {U : AtomCarrier.{u}} {R S : CompositionReading U}
    (hcompose : R.compose = S.compose) : R = S := by
  cases R
  cases S
  cases hcompose
  rfl

/-- The composition rule returns a configuration on exactly the supplied family. -/
theorem compose_family_eq {U : AtomCarrier.{u}} (R : CompositionReading U)
    (F : AtomFamily U) (hfinite : F.ListFinite) :
    (R.compose F hfinite).family = F :=
  R.family_eq F hfinite

/-- The composition rule returns a configuration supported by its supplied family. -/
theorem compose_familySupported {U : AtomCarrier.{u}} (R : CompositionReading U)
    (F : AtomFamily U) (hfinite : F.ListFinite) :
    (R.compose F hfinite).FamilySupported :=
  R.family_supported F hfinite

end CompositionReading

namespace ObjectReading

/-- Object readings are equal when their object constructors agree. -/
@[ext]
theorem ext {U : AtomCarrier.{u}} {R S : ObjectReading U}
    (hobject : R.object = S.object) : R = S := by
  cases R
  cases S
  cases hobject
  rfl

/-- The object-formation rule returns an object on exactly the supplied configuration. -/
theorem object_configuration_eq {U : AtomCarrier.{u}} (R : ObjectReading U)
    (C : AtomConfiguration U) : (R.object C).configuration = C :=
  R.configuration_eq C

end ObjectReading

namespace CoreReading

/--
Core readings are equal when their doctrine, dependent source, and all
semantic reading rules agree. The finite-family evidence is proof-irrelevant.
-/
@[ext]
theorem ext {U : AtomCarrier.{u}} {R S : CoreReading U}
    (hdoctrine : R.doctrine = S.doctrine)
    (hsource : HEq R.source S.source)
    (hcomposition : R.composition = S.composition)
    (hobjectReading : R.objectReading = S.objectReading)
    (hequationReading : HEq R.equationReading S.equationReading)
    (hinvariantReading : R.invariantReading = S.invariantReading)
    (hsignatureReading : R.signatureReading = S.signatureReading)
    (hoperationReading : R.operationReading = S.operationReading) : R = S := by
  cases R
  cases S
  cases hdoctrine
  cases hsource
  cases hcomposition
  cases hobjectReading
  cases hequationReading
  cases hinvariantReading
  cases hsignatureReading
  cases hoperationReading
  rfl

end CoreReading

namespace AATCorePackage

/-- Core packages are equal when their primitive systems and admissible readings agree. -/
@[ext]
theorem ext {U : AtomCarrier.{u}} {P Q : AATCorePackage U}
    (haxioms : P.axioms = Q.axioms) (hreading : P.reading = Q.reading) : P = Q := by
  cases P
  cases Q
  cases haxioms
  cases hreading
  rfl

/-- Construct the core input package from its two independent inputs. -/
def generate {U : AtomCarrier.{u}}
    (S : AtomAxiomSystem U) (r : CoreReading U) : AATCorePackage U where
  axioms := S
  reading := r

/-- The canonical Atom family extracted by the core reading. -/
def family {U : AtomCarrier.{u}} (core : AATCorePackage U) : AtomFamily U :=
  core.reading.doctrine.atomize core.reading.source

/-- The configuration obtained by applying the composition rule to the canonical family. -/
def configuration {U : AtomCarrier.{u}}
    (core : AATCorePackage U) : AtomConfiguration U :=
  core.reading.composition.compose core.family core.reading.family_listFinite

/-- The architecture object obtained from the generated configuration. -/
def object {U : AtomCarrier.{u}} (core : AATCorePackage U) : ArchitectureObject U :=
  core.reading.objectReading.object core.configuration

/-- The operation-closed object algebra generated from the base object. -/
def algebra {U : AtomCarrier.{u}} (core : AATCorePackage U) : ObjectAlgebra U where
  Obj := {A : ArchitectureObject U //
    core.reading.operationReading.Reachable core.object A}
  object A := A.1
  base := ⟨core.object, OperationReading.Reachable.base⟩
  equationReading := core.reading.equationReading
  Op A B := core.reading.operationReading.Op A.1 B.1
  configurationMap op := core.reading.operationReading.configurationMap op
  invariantReading := core.reading.invariantReading
  signatureReading := core.reading.signatureReading

/-- The generated object as the distinguished base member of the reachable algebra. -/
def baseObject {U : AtomCarrier.{u}}
    (core : AATCorePackage U) : core.algebra.Obj :=
  core.algebra.base

/-- The generated core's selected context preorder. -/
def contextPreorder {U : AtomCarrier.{u}} (core : AATCorePackage U) :
    Site.ContextPreorderCategory core.object :=
  core.algebra.contextPreorder

/-- The generated core's primary architectural equation system. -/
def equationSystem {U : AtomCarrier.{u}} (core : AATCorePackage U) :
    ArchitecturalEquationSystem core.contextPreorder :=
  core.algebra.equationSystem

/-- The generated core's equation-indexed circuit reading. -/
def circuitReading {U : AtomCarrier.{u}} (core : AATCorePackage U) :
    EquationCircuitReading core.equationSystem :=
  core.algebra.circuits

/-- The canonical family of any core satisfies its extraction doctrine. -/
theorem family_atomizes {U : AtomCarrier.{u}} (core : AATCorePackage U) :
    core.reading.doctrine.Atomizes core.reading.source core.family :=
  core.reading.doctrine.atomize_holds core.reading.source

/-- Membership in the generated family is exactly extraction from the core source. -/
theorem family_mem_iff_extracts {U : AtomCarrier.{u}}
    (core : AATCorePackage U) (atom : U.Atom) :
    core.family.mem atom ↔
      core.reading.doctrine.extracts core.reading.source atom :=
  core.family_atomizes atom

/-- The generated configuration is exactly the composition result selected by the reading. -/
theorem configuration_eq_compose {U : AtomCarrier.{u}}
    (core : AATCorePackage U) :
    core.configuration =
      core.reading.composition.compose core.family core.reading.family_listFinite :=
  rfl

/-- The configuration of any core has exactly its canonical family. -/
theorem configuration_family_eq {U : AtomCarrier.{u}}
    (core : AATCorePackage U) :
    core.configuration.family = core.family :=
  core.reading.composition.family_eq _ _

/-- Configuration-family membership is exactly extraction from the core source. -/
theorem configuration_family_mem_iff_extracts {U : AtomCarrier.{u}}
    (core : AATCorePackage U) (atom : U.Atom) :
    core.configuration.family.mem atom ↔
      core.reading.doctrine.extracts core.reading.source atom := by
  rw [core.configuration_family_eq]
  exact core.family_mem_iff_extracts atom

/-- The generated relation is exactly the relation returned by the composition rule. -/
theorem configuration_relation_iff_compose {U : AtomCarrier.{u}}
    (core : AATCorePackage U) (a b : U.Atom) :
    core.configuration.relation a b ↔
      (core.reading.composition.compose core.family
        core.reading.family_listFinite).relation a b :=
  Iff.rfl

/-- The generated identification is exactly the one returned by the composition rule. -/
theorem configuration_identification_iff_compose {U : AtomCarrier.{u}}
    (core : AATCorePackage U) (a b : U.Atom) :
    core.configuration.identification a b ↔
      (core.reading.composition.compose core.family
        core.reading.family_listFinite).identification a b :=
  Iff.rfl

/-- Relations and identifications of any generated configuration are family-supported. -/
theorem configuration_familySupported {U : AtomCarrier.{u}}
    (core : AATCorePackage U) : core.configuration.FamilySupported :=
  core.reading.composition.family_supported _ _

/-- The object-formation rule preserves the generated configuration. -/
theorem object_configuration_eq {U : AtomCarrier.{u}}
    (core : AATCorePackage U) :
    core.object.configuration = core.configuration :=
  core.reading.objectReading.configuration_eq _

/-- Membership in the generated object's family is exactly source extraction. -/
theorem object_family_mem_iff_extracts {U : AtomCarrier.{u}}
    (core : AATCorePackage U) (atom : U.Atom) :
    core.object.configuration.family.mem atom ↔
      core.reading.doctrine.extracts core.reading.source atom := by
  rw [core.object_configuration_eq]
  exact core.configuration_family_mem_iff_extracts atom

/-- The generated algebra retains the core reading's equation-indexed circuits. -/
theorem algebra_circuitReading_eq {U : AtomCarrier.{u}}
    (core : AATCorePackage U) :
    core.algebra.circuits = core.reading.equationReading.circuits :=
  rfl

/-- The generated algebra uses the detector code selected by the core reading. -/
theorem algebra_detectorCode_eq {U : AtomCarrier.{u}}
    (core : AATCorePackage U)
    (i : core.reading.equationReading.equationSystem.Index) :
    core.algebra.circuits.code i =
      core.reading.equationReading.circuits.code i :=
  rfl

/-- Generated circuit acceptance computes by the core reading's selected detector. -/
theorem algebra_accepts_eq_detector_eval {U : AtomCarrier.{u}}
    (core : AATCorePackage U)
    (i : core.reading.equationReading.equationSystem.Index)
    (Q : FiniteCircuitDatum U) :
    core.algebra.circuits.accepts i Q =
      (core.reading.equationReading.circuits.code i).eval Q :=
  rfl

/--
An architecture object occurs in the generated algebra exactly when it is
reachable from the generated base object by the selected operation reading.
-/
theorem algebra_object_nonempty_iff_reachable {U : AtomCarrier.{u}}
    (core : AATCorePackage U) (A : ArchitectureObject U) :
    Nonempty {a : core.algebra.Obj // core.algebra.object a = A} ↔
      core.reading.operationReading.Reachable core.object A := by
  constructor
  · rintro ⟨a, ha⟩
    rw [← ha]
    exact a.2
  · intro hreachable
    exact ⟨⟨⟨A, hreachable⟩, rfl⟩⟩

/--
The generated algebra's circuit fiber is inhabited exactly when its indexed
finite detector accepts a datum matching the selected generated object.
-/
theorem algebra_circuit_nonempty_iff {U : AtomCarrier.{u}}
    (core : AATCorePackage U) (A : core.algebra.Obj)
    (i : core.algebra.equationSystem.Index) :
    Nonempty (core.algebra.Circuit A i) ↔
      ∃ Q : FiniteCircuitDatum U,
        Q.Matches (core.algebra.object A) ∧
          core.algebra.circuits.accepts i Q = true := by
  constructor
  · rintro ⟨c⟩
    exact ⟨c.1, c.2⟩
  · rintro ⟨Q, hmatches, haccepts⟩
    exact ⟨⟨Q, hmatches, haccepts⟩⟩

/-- `generate` retains the supplied Atom axioms. -/
theorem generate_axioms {U : AtomCarrier.{u}}
    (S : AtomAxiomSystem U) (r : CoreReading U) :
    (AATCorePackage.generate S r).axioms = S :=
  rfl

/-- `generate` retains the supplied admissible reading. -/
theorem generate_reading {U : AtomCarrier.{u}}
    (S : AtomAxiomSystem U) (r : CoreReading U) :
    (AATCorePackage.generate S r).reading = r :=
  rfl

/-- The generated family is definitionally the doctrine's canonical atomization. -/
theorem generate_family_eq_atomize {U : AtomCarrier.{u}}
    (S : AtomAxiomSystem U) (r : CoreReading U) :
    (AATCorePackage.generate S r).family = r.doctrine.atomize r.source :=
  rfl

/-- The generated family satisfies the atom-level extraction characterization. -/
theorem generate_family_atomizes {U : AtomCarrier.{u}}
    (S : AtomAxiomSystem U) (r : CoreReading U) :
    r.doctrine.Atomizes r.source (AATCorePackage.generate S r).family :=
  r.doctrine.atomize_holds r.source

/-- The generated family carries the concrete finite-list evidence supplied by the reading. -/
theorem generate_family_listFinite {U : AtomCarrier.{u}}
    (S : AtomAxiomSystem U) (r : CoreReading U) :
    (AATCorePackage.generate S r).family.ListFinite :=
  r.family_listFinite

/-- Any family with the same doctrine/source characterization is the generated family. -/
theorem generate_family_unique {U : AtomCarrier.{u}}
    (S : AtomAxiomSystem U) (r : CoreReading U)
    {F : AtomFamily U} (hF : r.doctrine.Atomizes r.source F) :
    F = (AATCorePackage.generate S r).family :=
  r.doctrine.eq_atomize r.source hF

/-- The generated configuration is supported on exactly the generated family. -/
theorem generate_configuration_family_eq
    {U : AtomCarrier.{u}} (S : AtomAxiomSystem U) (r : CoreReading U) :
    (AATCorePackage.generate S r).configuration.family =
      (AATCorePackage.generate S r).family :=
  r.composition.family_eq _ _

/-- The composition rule supplies relation and identification support. -/
theorem generate_configuration_familySupported
    {U : AtomCarrier.{u}} (S : AtomAxiomSystem U) (r : CoreReading U) :
    (AATCorePackage.generate S r).configuration.FamilySupported :=
  r.composition.family_supported _ _

/-- Object formation preserves the generated configuration. -/
theorem generate_object_configuration_eq
    {U : AtomCarrier.{u}} (S : AtomAxiomSystem U) (r : CoreReading U) :
    (AATCorePackage.generate S r).object.configuration =
      (AATCorePackage.generate S r).configuration :=
  r.objectReading.configuration_eq _

/-- The distinguished algebra object is the generated architecture object. -/
theorem generate_algebra_base_object
    {U : AtomCarrier.{u}} (S : AtomAxiomSystem U) (r : CoreReading U) :
    (AATCorePackage.generate S r).algebra.object
      (AATCorePackage.generate S r).baseObject =
        (AATCorePackage.generate S r).object :=
  rfl

/-- An indexed algebra operation has the source encoded by its first index. -/
theorem generate_algebra_operation_source
    {U : AtomCarrier.{u}} (S : AtomAxiomSystem U) (r : CoreReading U)
    {A B : (AATCorePackage.generate S r).algebra.Obj}
    (op : (AATCorePackage.generate S r).algebra.Op A B) :
    ((AATCorePackage.generate S r).algebra.operation op).source =
      (AATCorePackage.generate S r).algebra.object A :=
  rfl

/-- An indexed algebra operation has the target encoded by its second index. -/
theorem generate_algebra_operation_target
    {U : AtomCarrier.{u}} (S : AtomAxiomSystem U) (r : CoreReading U)
    {A B : (AATCorePackage.generate S r).algebra.Obj}
    (op : (AATCorePackage.generate S r).algebra.Op A B) :
    ((AATCorePackage.generate S r).algebra.operation op).target =
      (AATCorePackage.generate S r).algebra.object B :=
  rfl

/--
Every generated circuit refutes its indexed equation by the admissibility
proof retained in the core reading.
-/
theorem generate_circuit_sound
    {U : AtomCarrier.{u}} (S : AtomAxiomSystem U) (r : CoreReading U)
    (A : (AATCorePackage.generate S r).algebra.Obj)
    (i : (AATCorePackage.generate S r).algebra.equationSystem.Index)
    (c : (AATCorePackage.generate S r).algebra.Circuit A i) :
    ¬ (AATCorePackage.generate S r).algebra.equationSystem.EquationHolds i
      ((AATCorePackage.generate S r).algebra.object A) :=
  r.equationReading.circuitSound i A.1 c.1 c.2.1 c.2.2

/-- Generated operations transport family membership through their actual atom map. -/
theorem generate_algebra_operation_maps_family
    {U : AtomCarrier.{u}} (S : AtomAxiomSystem U) (r : CoreReading U)
    {A B : (AATCorePackage.generate S r).algebra.Obj}
    (op : (AATCorePackage.generate S r).algebra.Op A B)
    {a : U.Atom}
    (ha : ((AATCorePackage.generate S r).algebra.object A).configuration.family.mem a) :
    ((AATCorePackage.generate S r).algebra.object B).configuration.family.mem
      (((AATCorePackage.generate S r).algebra.configurationMap op).atomMap a) :=
  ((AATCorePackage.generate S r).algebra.configurationMap op).maps_family ha

/-- Generated operations transport configuration relations. -/
theorem generate_algebra_operation_maps_relation
    {U : AtomCarrier.{u}} (S : AtomAxiomSystem U) (r : CoreReading U)
    {A B : (AATCorePackage.generate S r).algebra.Obj}
    (op : (AATCorePackage.generate S r).algebra.Op A B)
    {a b : U.Atom}
    (hab : ((AATCorePackage.generate S r).algebra.object A).configuration.relation a b) :
    ((AATCorePackage.generate S r).algebra.object B).configuration.relation
      (((AATCorePackage.generate S r).algebra.configurationMap op).atomMap a)
      (((AATCorePackage.generate S r).algebra.configurationMap op).atomMap b) :=
  ((AATCorePackage.generate S r).algebra.configurationMap op).maps_relation hab

/-- Generated operations transport configuration identifications. -/
theorem generate_algebra_operation_maps_identification
    {U : AtomCarrier.{u}} (S : AtomAxiomSystem U) (r : CoreReading U)
    {A B : (AATCorePackage.generate S r).algebra.Obj}
    (op : (AATCorePackage.generate S r).algebra.Op A B)
    {a b : U.Atom}
    (hab : ((AATCorePackage.generate S r).algebra.object A).configuration.identification a b) :
    ((AATCorePackage.generate S r).algebra.object B).configuration.identification
      (((AATCorePackage.generate S r).algebra.configurationMap op).atomMap a)
      (((AATCorePackage.generate S r).algebra.configurationMap op).atomMap b) :=
  ((AATCorePackage.generate S r).algebra.configurationMap op).maps_identification hab

end AATCorePackage

end AAT.AG
