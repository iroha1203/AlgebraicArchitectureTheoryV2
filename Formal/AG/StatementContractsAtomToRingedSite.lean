import Formal.AG.Examples.FiniteModel
import Formal.AG.LawAlgebra.RawPresheafFiniteExample

noncomputable section

/-!
Executable statement contracts for the Atom-to-ringed-site PRD.

The SD1 constructor and characterization surface remains fixed below. Later
sections extend the same executable contract through SD2--SD5.
-/

namespace AAT.AG

universe u v

open CategoryTheory

/-! SD1 fixed definition signatures. -/

example {U : AtomCarrier.{u}} :
    (Source Vocabulary SemanticReading Resolution : Type u) ->
    Vocabulary -> SemanticReading -> Resolution ->
    (Vocabulary -> U.Atom -> Prop) ->
    (SemanticReading -> Source -> U.Atom -> Prop) ->
    (Resolution -> Source -> U.Atom -> Prop) ->
    (Source -> U.Atom -> Prop) -> (Source -> Source) -> ExtractionDoctrine U :=
  @ExtractionDoctrine.mk U

example {U : AtomCarrier.{u}} :
    Nonempty U.Atom ->
    (∀ a b, SameCoordinates U a b ↔ a = b) -> AtomAxiomSystem U :=
  @AtomAxiomSystem.mk U

example {U : AtomCarrier.{u}} :
    (compose : (F : AtomFamily U) -> F.ListFinite -> AtomConfiguration U) ->
    (∀ F hfinite, (compose F hfinite).family = F) ->
    (∀ F hfinite, (compose F hfinite).FamilySupported) -> CompositionReading U :=
  @CompositionReading.mk U

example {U : AtomCarrier.{u}} :
    (object : AtomConfiguration U -> ArchitectureObject U) ->
    (∀ C, (object C).configuration = C) -> ObjectReading U :=
  @ObjectReading.mk U

example {U : AtomCarrier.{u}} :
    List (CircuitQuery U × Bool) -> FiniteCircuitDatum U :=
  @FiniteCircuitDatum.mk U

example {U : AtomCarrier.{u}} {LU : LawUniverse U} :
    (code : LU.Index -> CircuitDetectorCode U) ->
    (∀ (i : LU.Index) (A : ArchitectureObject U) (Q : FiniteCircuitDatum U),
      Q.Matches A -> (code i).eval Q = true -> ¬ (LU.law i).holds A) ->
    CircuitReading LU :=
  @CircuitReading.mk U LU

example {U : AtomCarrier.{u}} :
    (lawUniverse : LawUniverse U) -> CircuitReading lawUniverse -> LawReading U :=
  @LawReading.mk U

example {U : AtomCarrier.{u}} {C D : AtomConfiguration U} :
    (atomMap : U.Atom -> U.Atom) ->
    (∀ {a}, C.family.mem a -> D.family.mem (atomMap a)) ->
    (∀ {a b}, C.relation a b -> D.relation (atomMap a) (atomMap b)) ->
    (∀ {a b}, C.identification a b -> D.identification (atomMap a) (atomMap b)) ->
    ConfigurationHom C D :=
  @ConfigurationHom.mk U C D

example {U : AtomCarrier.{u}} :
    (source target : ArchitectureObject U) ->
    ConfigurationHom source.configuration target.configuration -> Operation U :=
  @Operation.mk U

example {U : AtomCarrier.{u}} :
    (Op : ArchitectureObject U -> ArchitectureObject U -> Type u) ->
    ({A B : ArchitectureObject U} -> Op A B ->
      ConfigurationHom A.configuration B.configuration) -> OperationReading U :=
  @OperationReading.mk U

example {U : AtomCarrier.{u}} :
    (doctrine : ExtractionDoctrine U) ->
    (source : doctrine.Source) ->
    (doctrine.atomize source).ListFinite -> CompositionReading U -> ObjectReading U ->
    LawReading U -> InvariantFamily U -> ArchitectureSignature U -> OperationReading U ->
    CoreReading U :=
  @CoreReading.mk U

example {U : AtomCarrier.{u}} :
    (Obj : Type (u + 1)) ->
    (object : Obj -> ArchitectureObject U) ->
    (Op : Obj -> Obj -> Type u) ->
    ({A B : Obj} -> Op A B ->
      ConfigurationHom (object A).configuration (object B).configuration) ->
    InvariantFamily U -> LawReading U -> ArchitectureSignature U -> ObjectAlgebra U :=
  @ObjectAlgebra.mk U

example {U : AtomCarrier.{u}} :
    AtomAxiomSystem U -> CoreReading U -> AATCorePackage U :=
  @AATCorePackage.mk U

example {U : AtomCarrier.{u}}
    {motive : CircuitQuery U -> Sort u}
    (atomPresent : (a : U.Atom) -> motive (.atomPresent a))
    (relationPresent : (a b : U.Atom) -> motive (.relationPresent a b))
    (identificationPresent : (a b : U.Atom) -> motive (.identificationPresent a b))
    (query : CircuitQuery U) : motive query :=
  CircuitQuery.rec atomPresent relationPresent identificationPresent query

example {U : AtomCarrier.{u}}
    {motive : CircuitDetectorCode U -> Sort u}
    (reject : motive .reject)
    (exact : (pattern : FiniteCircuitDatum U) -> motive (.exact pattern))
    (any : (left right : CircuitDetectorCode U) -> motive left -> motive right ->
      motive (.any left right))
    (code : CircuitDetectorCode U) : motive code :=
  CircuitDetectorCode.rec reject exact any code

example {U : AtomCarrier.{u}} {R : OperationReading U}
    {base : ArchitectureObject U}
    {motive : (A : ArchitectureObject U) -> R.Reachable base A -> Prop}
    (baseCase : motive base .base)
    (stepCase : ∀ {A B} (reachable : R.Reachable base A) (op : R.Op A B),
      motive A reachable -> motive B (.step reachable op))
    {A : ArchitectureObject U} (reachable : R.Reachable base A) :
    motive A reachable :=
  OperationReading.Reachable.rec baseCase stepCase reachable

/-! SD2 fixed geometry signatures. -/

example {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {LU : LawUniverse U} {Sig : ArchitectureSignature U} :
    (U.Atom -> Prop) ->
    (LU.witnessFamily.Witness -> Prop) ->
    (Sig.Axis -> Prop) ->
    (Site.ArchCtx A -> U.Atom -> Prop) ->
    (Site.ArchCtx A -> LU.witnessFamily.Witness -> Prop) ->
    (Site.ArchCtx A -> Sig.Axis -> Prop) ->
    (Site.ArchCtx A -> Site.ArchCtx A -> Prop) ->
    Site.CoverageRequirements A LU Sig :=
  @Site.CoverageRequirements.mk U A LU Sig

example {U : AtomCarrier.{u}} {core : AATCorePackage U} :
    (contextPreorder : Site.ContextPreorderCategory core.object) ->
    Site.CoverageRequirements core.object
      core.algebra.lawReading.lawUniverse core.algebra.signatureReading ->
    Site.ContextOverlapPullback contextPreorder ->
    Site.SelectedGeometryReading core :=
  @Site.SelectedGeometryReading.mk U core

example {U : AtomCarrier.{u}} {core : AATCorePackage U}
    {X Y : Site.SelectedGeometryReading core}
    (hcontext : X.contextPreorder = Y.contextPreorder)
    (hrequirements : X.requirements = Y.requirements)
    (hoverlap : HEq X.overlap Y.overlap) : X = Y :=
  Site.SelectedGeometryReading.ext hcontext hrequirements hoverlap

example {U : AtomCarrier.{u}} {core : AATCorePackage U}
    (reading : Site.SelectedGeometryReading core) : Site.AATSite core.object :=
  reading.toAATSite

example {U : AtomCarrier.{u}} {core : AATCorePackage U}
    (reading : Site.SelectedGeometryReading core) :
    reading.toAATSite.architectureObject = core.object :=
  reading.toAATSite_architectureObject

example {U : AtomCarrier.{u}} {core : AATCorePackage U}
    (reading : Site.SelectedGeometryReading core) :
    reading.toAATSite.contextPreorder = reading.contextPreorder :=
  reading.toAATSite_contextPreorder

example {U : AtomCarrier.{u}} {core : AATCorePackage U}
    (reading : Site.SelectedGeometryReading core) :
    reading.toAATSite.lawUniverse = core.algebra.lawReading.lawUniverse :=
  reading.toAATSite_lawUniverse

example {U : AtomCarrier.{u}} {core : AATCorePackage U}
    (reading : Site.SelectedGeometryReading core) :
    reading.toAATSite.signature = core.algebra.signatureReading :=
  reading.toAATSite_signature

example {U : AtomCarrier.{u}} {core : AATCorePackage U}
    (reading : Site.SelectedGeometryReading core) :
    reading.toAATSite.requirements = reading.requirements :=
  reading.toAATSite_requirements

example {U : AtomCarrier.{u}} {core : AATCorePackage U}
    (reading : Site.SelectedGeometryReading core) :
    reading.toAATSite.overlap = reading.overlap :=
  reading.toAATSite_overlap

example {U : AtomCarrier.{u}} {core : AATCorePackage U}
    (reading : Site.SelectedGeometryReading core) :
    reading.toAATSite.topology =
      Site.AATGrothendieckTopology reading.requirements reading.overlap :=
  reading.topology_eq_generated

example {U : AtomCarrier.{u}} (L : Law U) (A : ArchitectureObject U) : Prop :=
  SemanticObstruction L A

example {U : AtomCarrier.{u}} (L : Law U) (A : ArchitectureObject U) :
    SemanticObstruction L A ↔ ¬ L.holds A :=
  SemanticObstruction.iff_not_holds L A

example {U : AtomCarrier.{u}} (D : ExtractionDoctrine U) :
    D.Source -> U.Atom -> Prop :=
  D.extracts

example {U : AtomCarrier.{u}} (D : ExtractionDoctrine U)
    (source : D.Source) (atom : U.Atom) :
    D.extracts source atom ↔
      D.vocabularyAllows D.vocabulary atom ∧
        D.semanticAllows D.semanticReading (D.normalize source) atom ∧
        D.resolutionAllows D.resolution (D.normalize source) atom ∧
        D.sourceSemantics (D.normalize source) atom :=
  D.extracts_iff source atom

example {U : AtomCarrier.{u}} (D : ExtractionDoctrine U) :
    D.Source -> AtomFamily U :=
  D.atomize

example {U : AtomCarrier.{u}} (D : ExtractionDoctrine U) :
    D.Source -> AtomFamily U -> Prop :=
  D.Atomizes

example {U : AtomCarrier.{u}} (D : ExtractionDoctrine U) :
    D.Vocabulary -> U.Atom -> Prop :=
  D.vocabularyAllows

example {U : AtomCarrier.{u}} (D : ExtractionDoctrine U) :
    D.SemanticReading -> D.Source -> U.Atom -> Prop :=
  D.semanticAllows

example {U : AtomCarrier.{u}} (D : ExtractionDoctrine U) :
    D.Resolution -> D.Source -> U.Atom -> Prop :=
  D.resolutionAllows

example {U : AtomCarrier.{u}} (D : ExtractionDoctrine U) :
    D.Source -> U.Atom -> Prop :=
  D.sourceSemantics

example {U : AtomCarrier.{u}} (D : ExtractionDoctrine U) : D.Source -> D.Source :=
  D.normalize

example {U : AtomCarrier.{u}} (S : AtomAxiomSystem U) : Nonempty U.Atom :=
  S.primitiveExistence

example {U : AtomCarrier.{u}} (S : AtomAxiomSystem U) :
    ∀ a b, SameCoordinates U a b ↔ a = b :=
  S.predicateStability

example {U : AtomCarrier.{u}} (D : ExtractionDoctrine U)
    (source : D.Source) : D.Atomizes source (D.atomize source) :=
  D.atomize_holds source

example {U : AtomCarrier.{u}} (D : ExtractionDoctrine U)
    (source : D.Source) {F G : AtomFamily U}
    (hF : D.Atomizes source F) (hG : D.Atomizes source G) : F = G :=
  D.atomize_unique source hF hG

example {U : AtomCarrier.{u}} (D : ExtractionDoctrine U)
    (source : D.Source) {F : AtomFamily U} (hF : D.Atomizes source F) :
    F = D.atomize source :=
  D.eq_atomize source hF

example {U : AtomCarrier.{u}} (R : CompositionReading U) :
    (F : AtomFamily U) -> F.ListFinite -> AtomConfiguration U :=
  R.compose

example {U : AtomCarrier.{u}} (R : CompositionReading U) :
    ∀ F hfinite, (R.compose F hfinite).family = F :=
  R.family_eq

example {U : AtomCarrier.{u}} (R : CompositionReading U) :
    ∀ F hfinite, (R.compose F hfinite).FamilySupported :=
  R.family_supported

example {U : AtomCarrier.{u}} (R : ObjectReading U) :
    AtomConfiguration U -> ArchitectureObject U :=
  R.object

example {U : AtomCarrier.{u}} (R : ObjectReading U) :
    ∀ C, (R.object C).configuration = C :=
  R.configuration_eq

example {U : AtomCarrier.{u}} (q : CircuitQuery U) :
    ArchitectureObject U -> Prop :=
  q.Holds

example {U : AtomCarrier.{u}} (Q : FiniteCircuitDatum U) :
    ArchitectureObject U -> Prop :=
  Q.Matches

example {U : AtomCarrier.{u}} (code : CircuitDetectorCode U) :
    FiniteCircuitDatum U -> Bool :=
  code.eval

example {U : AtomCarrier.{u}} {LU : LawUniverse U} (R : CircuitReading LU) :
    LU.Index -> FiniteCircuitDatum U -> Bool :=
  R.accepts

example {U : AtomCarrier.{u}} {LU : LawUniverse U} (R : CircuitReading LU) :
    (i : LU.Index) -> CircuitDetectorCode U :=
  R.code

example {U : AtomCarrier.{u}} {LU : LawUniverse U} (R : CircuitReading LU) :
    ∀ (i : LU.Index) (A : ArchitectureObject U) (Q : FiniteCircuitDatum U),
      Q.Matches A -> (R.code i).eval Q = true -> ¬ (LU.law i).holds A :=
  R.sound

example {U : AtomCarrier.{u}} {LU : LawUniverse U} (R : CircuitReading LU)
    (A : ArchitectureObject U) (i : LU.Index) : Type u :=
  R.Circuit A i

example {U : AtomCarrier.{u}} {LU : LawUniverse U} (R : CircuitReading LU) : Prop :=
  R.RequiredComplete

example {U : AtomCarrier.{u}} (R : LawReading U) : LawUniverse U :=
  R.lawUniverse

example {U : AtomCarrier.{u}} (R : LawReading U) : CircuitReading R.lawUniverse :=
  R.circuits

example {U : AtomCarrier.{u}} (C : AtomConfiguration U) : ConfigurationHom C C :=
  ConfigurationHom.id C

example {U : AtomCarrier.{u}} {C D : AtomConfiguration U}
    (f : ConfigurationHom C D) : U.Atom -> U.Atom :=
  f.atomMap

example {U : AtomCarrier.{u}} {C D : AtomConfiguration U}
    (f : ConfigurationHom C D) :
    ∀ {a}, C.family.mem a -> D.family.mem (f.atomMap a) :=
  f.maps_family

example {U : AtomCarrier.{u}} {C D : AtomConfiguration U}
    (f : ConfigurationHom C D) :
    ∀ {a b}, C.relation a b -> D.relation (f.atomMap a) (f.atomMap b) :=
  f.maps_relation

example {U : AtomCarrier.{u}} {C D : AtomConfiguration U}
    (f : ConfigurationHom C D) :
    ∀ {a b}, C.identification a b ->
      D.identification (f.atomMap a) (f.atomMap b) :=
  f.maps_identification

example {U : AtomCarrier.{u}} {C D E : AtomConfiguration U}
    (g : ConfigurationHom D E) (f : ConfigurationHom C D) :
    ConfigurationHom C E :=
  ConfigurationHom.comp g f

example {U : AtomCarrier.{u}} (R : OperationReading U)
    {A B : ArchitectureObject U} (op : R.Op A B) : Operation U :=
  R.operation op

example {U : AtomCarrier.{u}} (R : OperationReading U) :
    (A B : ArchitectureObject U) -> Type u :=
  R.Op

example {U : AtomCarrier.{u}} (R : OperationReading U) :
    ∀ {A B}, R.Op A B -> ConfigurationHom A.configuration B.configuration :=
  R.configurationMap

example {U : AtomCarrier.{u}} (R : OperationReading U)
    (base : ArchitectureObject U) : ArchitectureObject U -> Prop :=
  R.Reachable base

example {U : AtomCarrier.{u}} (K : ObjectAlgebra U) (A : K.Obj)
    (i : K.lawReading.lawUniverse.Index) : Type u :=
  K.Circuit A i

example {U : AtomCarrier.{u}} (K : ObjectAlgebra U) {A B : K.Obj}
    (op : K.Op A B) : Operation U :=
  K.operation op

example {U : AtomCarrier.{u}} (r : CoreReading U) : ExtractionDoctrine U :=
  r.doctrine

example {U : AtomCarrier.{u}} (r : CoreReading U) : r.doctrine.Source :=
  r.source

example {U : AtomCarrier.{u}} (r : CoreReading U) :
    (r.doctrine.atomize r.source).ListFinite :=
  r.family_listFinite

example {U : AtomCarrier.{u}} (r : CoreReading U) : CompositionReading U :=
  r.composition

example {U : AtomCarrier.{u}} (r : CoreReading U) : ObjectReading U :=
  r.objectReading

example {U : AtomCarrier.{u}} (r : CoreReading U) : LawReading U :=
  r.lawReading

example {U : AtomCarrier.{u}} (r : CoreReading U) : InvariantFamily U :=
  r.invariantReading

example {U : AtomCarrier.{u}} (r : CoreReading U) : ArchitectureSignature U :=
  r.signatureReading

example {U : AtomCarrier.{u}} (r : CoreReading U) : OperationReading U :=
  r.operationReading

example {U : AtomCarrier.{u}} (K : ObjectAlgebra U) : K.Obj -> ArchitectureObject U :=
  K.object

example {U : AtomCarrier.{u}} (K : ObjectAlgebra U) : K.Obj -> K.Obj -> Type u :=
  K.Op

example {U : AtomCarrier.{u}} (K : ObjectAlgebra U) :
    ∀ {A B}, K.Op A B ->
      ConfigurationHom (K.object A).configuration (K.object B).configuration :=
  K.configurationMap

example {U : AtomCarrier.{u}} (K : ObjectAlgebra U) : InvariantFamily U :=
  K.invariantReading

example {U : AtomCarrier.{u}} (K : ObjectAlgebra U) : LawReading U :=
  K.lawReading

example {U : AtomCarrier.{u}} (K : ObjectAlgebra U) : ArchitectureSignature U :=
  K.signatureReading

example {U : AtomCarrier.{u}} (core : AATCorePackage U) : AtomAxiomSystem U :=
  core.axioms

example {U : AtomCarrier.{u}} (core : AATCorePackage U) : CoreReading U :=
  core.reading

example {U : AtomCarrier.{u}}
    (S : AtomAxiomSystem U) (r : CoreReading U) : AATCorePackage U :=
  AATCorePackage.generate S r

example {U : AtomCarrier.{u}}
    (core : AATCorePackage U) : AtomFamily U :=
  core.family

example {U : AtomCarrier.{u}}
    (core : AATCorePackage U) : AtomConfiguration U :=
  core.configuration

example {U : AtomCarrier.{u}}
    (core : AATCorePackage U) : ArchitectureObject U :=
  core.object

example {U : AtomCarrier.{u}}
    (core : AATCorePackage U) : ObjectAlgebra U :=
  core.algebra

example {U : AtomCarrier.{u}}
    (core : AATCorePackage U) : core.algebra.Obj :=
  core.baseObject

example {U : AtomCarrier.{u}}
    (S : AtomAxiomSystem U) (r : CoreReading U) :
    (AATCorePackage.generate S r).axioms = S :=
  AATCorePackage.generate_axioms S r

example {U : AtomCarrier.{u}}
    (S : AtomAxiomSystem U) (r : CoreReading U) :
    (AATCorePackage.generate S r).reading = r :=
  AATCorePackage.generate_reading S r

example {U : AtomCarrier.{u}}
    (S : AtomAxiomSystem U) (r : CoreReading U) :
    (AATCorePackage.generate S r).family = r.doctrine.atomize r.source :=
  AATCorePackage.generate_family_eq_atomize S r

example {U : AtomCarrier.{u}}
    (S : AtomAxiomSystem U) (r : CoreReading U) :
    r.doctrine.Atomizes r.source (AATCorePackage.generate S r).family :=
  AATCorePackage.generate_family_atomizes S r

example {U : AtomCarrier.{u}}
    (S : AtomAxiomSystem U) (r : CoreReading U) :
    (AATCorePackage.generate S r).family.ListFinite :=
  AATCorePackage.generate_family_listFinite S r

example {U : AtomCarrier.{u}}
    (S : AtomAxiomSystem U) (r : CoreReading U)
    {F : AtomFamily U} (hF : r.doctrine.Atomizes r.source F) :
    F = (AATCorePackage.generate S r).family :=
  AATCorePackage.generate_family_unique S r hF

example {U : AtomCarrier.{u}}
    (S : AtomAxiomSystem U) (r : CoreReading U) :
    (AATCorePackage.generate S r).configuration.family =
      (AATCorePackage.generate S r).family :=
  AATCorePackage.generate_configuration_family_eq S r

example {U : AtomCarrier.{u}}
    (S : AtomAxiomSystem U) (r : CoreReading U) :
    (AATCorePackage.generate S r).configuration.FamilySupported :=
  AATCorePackage.generate_configuration_familySupported S r

example {U : AtomCarrier.{u}}
    (S : AtomAxiomSystem U) (r : CoreReading U) :
    (AATCorePackage.generate S r).object.configuration =
      (AATCorePackage.generate S r).configuration :=
  AATCorePackage.generate_object_configuration_eq S r

example {U : AtomCarrier.{u}}
    (S : AtomAxiomSystem U) (r : CoreReading U) :
    (AATCorePackage.generate S r).algebra.lawReading = r.lawReading :=
  AATCorePackage.generate_lawReading_eq S r

example {U : AtomCarrier.{u}}
    (S : AtomAxiomSystem U) (r : CoreReading U) :
    (AATCorePackage.generate S r).algebra.object
      (AATCorePackage.generate S r).baseObject =
        (AATCorePackage.generate S r).object :=
  AATCorePackage.generate_algebra_base_object S r

example {U : AtomCarrier.{u}}
    (S : AtomAxiomSystem U) (r : CoreReading U)
    {A B : (AATCorePackage.generate S r).algebra.Obj}
    (op : (AATCorePackage.generate S r).algebra.Op A B) :
    ((AATCorePackage.generate S r).algebra.operation op).source =
      (AATCorePackage.generate S r).algebra.object A :=
  AATCorePackage.generate_algebra_operation_source S r op

example {U : AtomCarrier.{u}}
    (S : AtomAxiomSystem U) (r : CoreReading U)
    {A B : (AATCorePackage.generate S r).algebra.Obj}
    (op : (AATCorePackage.generate S r).algebra.Op A B) :
    ((AATCorePackage.generate S r).algebra.operation op).target =
      (AATCorePackage.generate S r).algebra.object B :=
  AATCorePackage.generate_algebra_operation_target S r op

example {U : AtomCarrier.{u}}
    (S : AtomAxiomSystem U) (r : CoreReading U)
    (A : (AATCorePackage.generate S r).algebra.Obj)
    (i : (AATCorePackage.generate S r).algebra.lawReading.lawUniverse.Index)
    (c : (AATCorePackage.generate S r).algebra.Circuit A i) :
    ¬ ((AATCorePackage.generate S r).algebra.lawReading.lawUniverse.law i).holds
      ((AATCorePackage.generate S r).algebra.object A) :=
  AATCorePackage.generate_circuit_sound S r A i c

example {U : AtomCarrier.{u}}
    (S : AtomAxiomSystem U) (r : CoreReading U)
    {A B : (AATCorePackage.generate S r).algebra.Obj}
    (op : (AATCorePackage.generate S r).algebra.Op A B)
    {a : U.Atom}
    (ha : ((AATCorePackage.generate S r).algebra.object A).configuration.family.mem a) :
    ((AATCorePackage.generate S r).algebra.object B).configuration.family.mem
      (((AATCorePackage.generate S r).algebra.configurationMap op).atomMap a) :=
  AATCorePackage.generate_algebra_operation_maps_family S r op ha

example {U : AtomCarrier.{u}}
    (S : AtomAxiomSystem U) (r : CoreReading U)
    {A B : (AATCorePackage.generate S r).algebra.Obj}
    (op : (AATCorePackage.generate S r).algebra.Op A B)
    {a b : U.Atom}
    (hab : ((AATCorePackage.generate S r).algebra.object A).configuration.relation a b) :
    ((AATCorePackage.generate S r).algebra.object B).configuration.relation
      (((AATCorePackage.generate S r).algebra.configurationMap op).atomMap a)
      (((AATCorePackage.generate S r).algebra.configurationMap op).atomMap b) :=
  AATCorePackage.generate_algebra_operation_maps_relation S r op hab

example {U : AtomCarrier.{u}}
    (S : AtomAxiomSystem U) (r : CoreReading U)
    {A B : (AATCorePackage.generate S r).algebra.Obj}
    (op : (AATCorePackage.generate S r).algebra.Op A B)
    {a b : U.Atom}
    (hab : ((AATCorePackage.generate S r).algebra.object A).configuration.identification a b) :
    ((AATCorePackage.generate S r).algebra.object B).configuration.identification
      (((AATCorePackage.generate S r).algebra.configurationMap op).atomMap a)
      (((AATCorePackage.generate S r).algebra.configurationMap op).atomMap b) :=
  AATCorePackage.generate_algebra_operation_maps_identification S r op hab

example :
    ∃ A B : FiniteModel.corePackage.algebra.Obj,
      A ≠ B ∧ Nonempty (FiniteModel.corePackage.algebra.Op A B) :=
  FiniteModel.nonidentity_reachable_operation_fires

example :
    ¬ FiniteModel.coreReading.operationReading.Reachable
      FiniteModel.corePackage.object FiniteModel.unreachableEmptyObject :=
  FiniteModel.unreachableEmptyObject_not_reachable

example : SemanticObstruction FiniteModel.noCycleLaw FiniteModel.object :=
  FiniteModel.object_semanticObstruction

example : ¬ SemanticObstruction FiniteModel.noCycleLaw FiniteModel.acyclicObject :=
  FiniteModel.acyclicObject_not_semanticObstruction

example : FiniteModel.corePackage.family.mem FiniteModel.FiniteAtom.componentA :=
  FiniteModel.corePackage_componentA_mem

example : ¬ FiniteModel.corePackage.family.mem FiniteModel.FiniteAtom.componentC :=
  FiniteModel.corePackage_componentC_not_mem

example :
    (FiniteModel.corePackage.algebra.configurationMap
      FiniteModel.collapseOperation).atomMap FiniteModel.FiniteAtom.componentA =
        FiniteModel.FiniteAtom.componentB ∧
      FiniteModel.FiniteAtom.componentA ≠ FiniteModel.FiniteAtom.componentB :=
  FiniteModel.collapseOperation_atomMap_nonidentity

example :
    FiniteModel.collapsedObject.configuration.family.mem
      ((FiniteModel.corePackage.algebra.configurationMap
        FiniteModel.collapseOperation).atomMap FiniteModel.FiniteAtom.componentA) :=
  FiniteModel.collapseOperation_transports_family

example :
    FiniteModel.collapsedObject.configuration.relation
      ((FiniteModel.corePackage.algebra.configurationMap
        FiniteModel.collapseOperation).atomMap FiniteModel.FiniteAtom.dependsAB)
      ((FiniteModel.corePackage.algebra.configurationMap
        FiniteModel.collapseOperation).atomMap FiniteModel.FiniteAtom.dependsBC) :=
  FiniteModel.collapseOperation_transports_relation

example :
    FiniteModel.collapsedObject.configuration.identification
      ((FiniteModel.corePackage.algebra.configurationMap
        FiniteModel.collapseOperation).atomMap FiniteModel.FiniteAtom.componentA)
      ((FiniteModel.corePackage.algebra.configurationMap
        FiniteModel.collapseOperation).atomMap FiniteModel.FiniteAtom.componentB) :=
  FiniteModel.collapseOperation_transports_identification

example :
    FiniteModel.coreReading.lawReading.circuits.accepts PUnit.unit
      FiniteModel.cycleQueryDatum = true :=
  FiniteModel.cycleQueryDatum_accepted

example : FiniteModel.cycleQueryDatum.Matches FiniteModel.corePackage.object :=
  FiniteModel.cycleQueryDatum_matches_core

example : ¬ FiniteModel.componentAAbsentDatum.Matches FiniteModel.corePackage.object :=
  FiniteModel.componentAAbsentDatum_not_matches_core

example :
    (CircuitQuery.atomPresent FiniteModel.FiniteAtom.componentA).Holds
      FiniteModel.corePackage.object :=
  FiniteModel.componentA_atomPresent_holds_core

example :
    ¬ (CircuitQuery.atomPresent FiniteModel.FiniteAtom.componentC).Holds
      FiniteModel.corePackage.object :=
  FiniteModel.componentC_atomPresent_not_holds_core

example : FiniteModel.completeCircuitReading.RequiredComplete :=
  FiniteModel.completeCircuitReading_requiredComplete

example :
    ¬ (FiniteModel.componentAAbsentLawUniverse.law PUnit.unit).holds
        FiniteModel.corePackage.object ∧
      Nonempty (FiniteModel.completeCircuitReading.Circuit
        FiniteModel.corePackage.object PUnit.unit) :=
  FiniteModel.completeCircuitReading_nonvacuous

example :
    FiniteModel.coreReading.lawReading.circuits.accepts PUnit.unit ⟨[]⟩ = false :=
  FiniteModel.emptyQueryDatum_rejected

example :
    ¬ (FiniteModel.corePackage.algebra.lawReading.lawUniverse.law PUnit.unit).holds
      (FiniteModel.corePackage.algebra.object FiniteModel.corePackage.baseObject) :=
  FiniteModel.generatedCycleCircuit_sound

example :
    FiniteModel.site.lawUniverse =
      FiniteModel.corePackage.algebra.lawReading.lawUniverse :=
  FiniteModel.site_lawUniverse_eq_core

example :
    FiniteModel.site.signature = FiniteModel.corePackage.algebra.signatureReading :=
  FiniteModel.site_signature_eq_core

example :
    FiniteModel.site.topology =
      Site.AATGrothendieckTopology
        FiniteModel.siteSelectedGeometryReading.requirements
        FiniteModel.siteSelectedGeometryReading.overlap :=
  FiniteModel.site_topology_eq_generated

example :
    CategoryTheory.Sieve.generate FiniteModel.siteSingletonCover.presieve ∈
      FiniteModel.site.topology FiniteModel.siteBase :=
  FiniteModel.siteSingletonCover_topologyCover

example :
    CategoryTheory.Sieve.generate FiniteModel.twoPatchCover.presieve ∈
      FiniteModel.twoPatchSite.topology FiniteModel.twoPatchBase :=
  FiniteModel.twoPatchCover_topologyCover

/-! SD3 fixed typed raw presheaf signatures. -/

example {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k] :
    ((coordFamily : (W : S.category) -> LawAlgebra.CoordinateFamily W.ctx) ->
      (relationFamily : (W : S.category) ->
        LawAlgebra.StructuralRelationFamily (coordFamily W) k) ->
      (restrictionStable : ∀ {X Y : S.category} (f : X ⟶ Y),
        LawAlgebra.RestrictionStableStructuralRelations
          (relationFamily X) (relationFamily Y)
          (S.contextPreorder.morphism (CategoryTheory.leOfHom f))) ->
      (∀ X : S.category,
        (restrictionStable (𝟙 X)).restriction.polynomialMap =
          RingHom.id (LawAlgebra.FreeTypedCommAlg (coordFamily X) k)) ->
      (∀ {X Y Z : S.category} (f : X ⟶ Y) (g : Y ⟶ Z),
        (restrictionStable (f ≫ g)).restriction.polynomialMap =
          ((restrictionStable f).restriction.polynomialMap).comp
            ((restrictionStable g).restriction.polynomialMap)) ->
      LawAlgebra.RawAmbientRestrictionSystem S k) :=
  @LawAlgebra.RawAmbientRestrictionSystem.mk U A S k _

example {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (B : LawAlgebra.RawAmbientRestrictionSystem S k) (W : S.category) :
    Type (max u v) :=
  B.rawAlgebra W

example {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {source target : Site.ArchitectureContext A}
    {sourceFamily : LawAlgebra.CoordinateFamily source}
    {targetFamily : LawAlgebra.CoordinateFamily target}
    {k : Type v} [CommRing k]
    {f : Site.ContextMorphism source target}
    (rho : LawAlgebra.TypedCoordinateRestriction sourceFamily targetFamily k f)
    (x : k) :
    rho.polynomialMap (MvPolynomial.C x) = MvPolynomial.C x :=
  rho.polynomialMap_C x

example {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {source target : Site.ArchitectureContext A}
    {sourceFamily : LawAlgebra.CoordinateFamily source}
    {targetFamily : LawAlgebra.CoordinateFamily target}
    {k : Type v} [CommRing k]
    {sourceRelations : LawAlgebra.StructuralRelationFamily sourceFamily k}
    {targetRelations : LawAlgebra.StructuralRelationFamily targetFamily k}
    {f : Site.ContextMorphism source target}
    (h : LawAlgebra.RestrictionStableStructuralRelations
      sourceRelations targetRelations f) (x : k) :
    h.quotientDesc (targetRelations.quotientMap (MvPolynomial.C x)) =
      sourceRelations.quotientMap (MvPolynomial.C x) :=
  h.quotientDesc_C x

example {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (B : LawAlgebra.RawAmbientRestrictionSystem S k) :
    LawAlgebra.AlgebraValuedAATPresheaf S k :=
  B.toPresheaf

example {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (B : LawAlgebra.RawAmbientRestrictionSystem S k) (W : S.category) :
    B.rawAlgebra W ≃+* (B.toPresheaf.obj (Opposite.op W)).right :=
  B.toPresheafObjectIso W

example {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (B : LawAlgebra.RawAmbientRestrictionSystem S k) (X : S.category) :
    (B.restrictionStable (𝟙 X)).quotientDesc =
      RingHom.id (B.rawAlgebra X) :=
  B.quotientDesc_id X

example {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (B : LawAlgebra.RawAmbientRestrictionSystem S k)
    {X Y Z : S.category} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (B.restrictionStable (f ≫ g)).quotientDesc =
      ((B.restrictionStable f).quotientDesc).comp
        ((B.restrictionStable g).quotientDesc) :=
  B.quotientDesc_comp f g

example {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (B : LawAlgebra.RawAmbientRestrictionSystem S k)
    {X Y : S.category} (f : X ⟶ Y) (x : B.rawAlgebra Y) :
    B.toPresheafObjectIso X ((B.restrictionStable f).quotientDesc x) =
      (B.toPresheaf.map f.op).right (B.toPresheafObjectIso Y x) :=
  B.toPresheaf_map f x

example :
    (LawAlgebra.FiniteExamples.RawPresheaf.system.relationFamily
      LawAlgebra.FiniteExamples.RawPresheaf.left).quotientMap
        (MvPolynomial.X () ^ 2 - 1) = 0 :=
  LawAlgebra.FiniteExamples.RawPresheaf.relation_vanishes

example :
    ¬ Function.Injective
      (LawAlgebra.FiniteExamples.RawPresheaf.system.relationFamily
        LawAlgebra.FiniteExamples.RawPresheaf.left).quotientMap :=
  LawAlgebra.FiniteExamples.RawPresheaf.quotientMap_not_injective

example :
    (LawAlgebra.FiniteExamples.RawPresheaf.system.restrictionStable
      LawAlgebra.FiniteExamples.RawPresheaf.leftToBase).quotientDesc
        ((LawAlgebra.FiniteExamples.RawPresheaf.system.relationFamily
          FiniteModel.twoPatchBase).quotientMap (MvPolynomial.X ())) ≠
      (LawAlgebra.FiniteExamples.RawPresheaf.system.relationFamily
        LawAlgebra.FiniteExamples.RawPresheaf.left).quotientMap
          (MvPolynomial.X ()) :=
  LawAlgebra.FiniteExamples.RawPresheaf.leftToBase_quotientDesc_X_ne_X

example :
    (LawAlgebra.FiniteExamples.RawPresheaf.system.restrictionStable
      LawAlgebra.FiniteExamples.RawPresheaf.leftToBase).quotientDesc
        ((LawAlgebra.FiniteExamples.RawPresheaf.system.relationFamily
          FiniteModel.twoPatchBase).quotientMap (MvPolynomial.C (2 : Int))) =
      (LawAlgebra.FiniteExamples.RawPresheaf.system.relationFamily
        LawAlgebra.FiniteExamples.RawPresheaf.left).quotientMap
          (MvPolynomial.C (2 : Int)) :=
  LawAlgebra.FiniteExamples.RawPresheaf.leftToBase_quotientDesc_C

/-! SD4 fixed ringed AAT site signatures. -/

example {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k] :
    LawAlgebra.AlgebraValuedAATPresheaf S k ->
      LawAlgebra.RingedAATSite S k :=
  @LawAlgebra.RingedAATSite.mk U A S k _

example {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (R : LawAlgebra.RingedAATSite S k) : Site.AATSite A :=
  R.site

example {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (R : LawAlgebra.RingedAATSite S k) : ArchitectureObject U :=
  R.architectureObject

example {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (R T : LawAlgebra.RingedAATSite S k) (hraw : R.raw = T.raw) : R = T :=
  LawAlgebra.RingedAATSite.ext R T hraw

example {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    [CategoryTheory.HasSheafify S.topology (LawAlgebra.AATCommAlgCat k)]
    (raw : LawAlgebra.AlgebraValuedAATPresheaf S k) :
    LawAlgebra.RingedAATSite S k :=
  LawAlgebra.RingedAATSite.ofMathlibSheafification raw

example {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (R : LawAlgebra.RingedAATSite S k)
    [CategoryTheory.HasSheafify S.topology (LawAlgebra.AATCommAlgCat k)] :
    LawAlgebra.LawAlgebraSheafificationBridge S k :=
  R.sheafificationBridge

example {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (R : LawAlgebra.RingedAATSite S k)
    [CategoryTheory.HasSheafify S.topology (LawAlgebra.AATCommAlgCat k)] :
    R.sheafificationBridge.raw = R.raw :=
  R.sheafificationBridge_raw

example {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (R : LawAlgebra.RingedAATSite S k)
    [CategoryTheory.HasSheafify S.topology (LawAlgebra.AATCommAlgCat k)] :
    LawAlgebra.LawAlgebraSheaf S k :=
  R.structureSheaf

example {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (R : LawAlgebra.RingedAATSite S k)
    [CategoryTheory.HasSheafify S.topology (LawAlgebra.AATCommAlgCat k)] :
    R.raw ⟶ R.structureSheaf.val :=
  R.canonical

example {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (R : LawAlgebra.RingedAATSite S k)
    [CategoryTheory.HasSheafify S.topology (LawAlgebra.AATCommAlgCat k)] :
    R.structureSheaf =
      (CategoryTheory.presheafToSheaf
        S.topology (LawAlgebra.AATCommAlgCat k)).obj R.raw :=
  R.structureSheaf_eq_sheafify

example {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (R : LawAlgebra.RingedAATSite S k)
    [CategoryTheory.HasSheafify S.topology (LawAlgebra.AATCommAlgCat k)] :
    R.canonical = CategoryTheory.toSheafify S.topology R.raw :=
  R.canonical_eq_toSheafify

example {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (R : LawAlgebra.RingedAATSite S k)
    [CategoryTheory.HasSheafify S.topology (LawAlgebra.AATCommAlgCat k)]
    (F : LawAlgebra.LawAlgebraSheaf S k) (eta : R.raw ⟶ F.val) :
    ∃! lift : R.structureSheaf.val ⟶ F.val, R.canonical ≫ lift = eta :=
  R.lift_unique F eta

example (k : Type v) [CommRing k] :
    LawAlgebra.AATCommAlgCat.{u, v} k ⥤ Type (max u v) :=
  LawAlgebra.AATCommAlgToType k

example {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (R : LawAlgebra.RingedAATSite S k)
    [CategoryTheory.HasSheafify S.topology (LawAlgebra.AATCommAlgCat k)]
    [S.topology.HasSheafCompose (LawAlgebra.AATCommAlgToType k)] :
    CategoryTheory.Sheaf S.topology (Type (max u v)) :=
  R.underlyingTypeSheaf

example {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (R : LawAlgebra.RingedAATSite S k)
    [CategoryTheory.HasSheafify S.topology (LawAlgebra.AATCommAlgCat k)]
    [S.topology.HasSheafCompose (LawAlgebra.AATCommAlgToType k)] :
    R.underlyingTypeSheaf.val =
      R.structureSheaf.val ⋙ LawAlgebra.AATCommAlgToType k :=
  R.underlyingTypeSheaf_val

/-! SD5 fixed end-to-end constructor signatures. -/

example {U : AtomCarrier.{u}}
    (S : AtomAxiomSystem U)
    (coreReading : CoreReading U)
    (reading : Site.SelectedGeometryReading
      (AATCorePackage.generate S coreReading))
    (k : Type v) [CommRing k]
    (raw : LawAlgebra.RawAmbientRestrictionSystem reading.toAATSite k)
    [CategoryTheory.HasSheafify
      reading.toAATSite.topology (LawAlgebra.AATCommAlgCat k)] :
    LawAlgebra.RingedAATSite reading.toAATSite k :=
  LawAlgebra.generateRingedAATSite S coreReading reading k raw

example {U : AtomCarrier.{u}}
    (S : AtomAxiomSystem U) (coreReading : CoreReading U)
    (reading : Site.SelectedGeometryReading
      (AATCorePackage.generate S coreReading))
    (k : Type v) [CommRing k]
    (raw : LawAlgebra.RawAmbientRestrictionSystem reading.toAATSite k)
    [CategoryTheory.HasSheafify
      reading.toAATSite.topology (LawAlgebra.AATCommAlgCat k)] :
    (LawAlgebra.generateRingedAATSite S coreReading reading k raw).site =
      reading.toAATSite :=
  LawAlgebra.generateRingedAATSite_site S coreReading reading k raw

example {U : AtomCarrier.{u}}
    (S : AtomAxiomSystem U) (coreReading : CoreReading U)
    (reading : Site.SelectedGeometryReading
      (AATCorePackage.generate S coreReading))
    (k : Type v) [CommRing k]
    (raw : LawAlgebra.RawAmbientRestrictionSystem reading.toAATSite k)
    [CategoryTheory.HasSheafify
      reading.toAATSite.topology (LawAlgebra.AATCommAlgCat k)] :
    (LawAlgebra.generateRingedAATSite S coreReading reading k raw).raw =
      raw.toPresheaf :=
  LawAlgebra.generateRingedAATSite_raw S coreReading reading k raw

example {U : AtomCarrier.{u}}
    (S : AtomAxiomSystem U) (coreReading : CoreReading U)
    (reading : Site.SelectedGeometryReading
      (AATCorePackage.generate S coreReading))
    (k : Type v) [CommRing k]
    (raw : LawAlgebra.RawAmbientRestrictionSystem reading.toAATSite k)
    [CategoryTheory.HasSheafify
      reading.toAATSite.topology (LawAlgebra.AATCommAlgCat k)] :
    (LawAlgebra.generateRingedAATSite S coreReading reading k raw).structureSheaf =
      (CategoryTheory.presheafToSheaf
        reading.toAATSite.topology
        (LawAlgebra.AATCommAlgCat k)).obj raw.toPresheaf :=
  LawAlgebra.generateRingedAATSite_structureSheaf S coreReading reading k raw

example {U : AtomCarrier.{u}}
    (S : AtomAxiomSystem U) (coreReading : CoreReading U)
    (reading : Site.SelectedGeometryReading
      (AATCorePackage.generate S coreReading))
    (k : Type v) [CommRing k]
    (raw : LawAlgebra.RawAmbientRestrictionSystem reading.toAATSite k)
    [CategoryTheory.HasSheafify
      reading.toAATSite.topology (LawAlgebra.AATCommAlgCat k)] :
    (LawAlgebra.generateRingedAATSite S coreReading reading k raw).canonical =
      CategoryTheory.toSheafify
        reading.toAATSite.topology raw.toPresheaf :=
  LawAlgebra.generateRingedAATSite_canonical S coreReading reading k raw

example {U : AtomCarrier.{u}}
    (S : AtomAxiomSystem U) (coreReading : CoreReading U)
    (reading : Site.SelectedGeometryReading
      (AATCorePackage.generate S coreReading))
    (k : Type v) [CommRing k]
    (raw : LawAlgebra.RawAmbientRestrictionSystem reading.toAATSite k)
    [CategoryTheory.HasSheafify
      reading.toAATSite.topology (LawAlgebra.AATCommAlgCat k)] :
    (LawAlgebra.generateRingedAATSite S coreReading reading k raw).architectureObject =
      (AATCorePackage.generate S coreReading).object :=
  LawAlgebra.generateRingedAATSite_architectureObject
    S coreReading reading k raw

end AAT.AG
