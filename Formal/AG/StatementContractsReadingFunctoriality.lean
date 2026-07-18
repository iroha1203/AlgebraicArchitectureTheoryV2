import Formal.AG.ReadingFunctoriality
import Formal.AG.ReadingFunctoriality.FiniteExamples
import Formal.AG.ReadingFunctoriality.ModTwoTorFiring
import Formal.AG.ReadingFunctoriality.TopologyChangeFiring
import Formal.AG.ReadingFunctoriality.LinearLerayComparison

/-!
# Reading-functoriality statement contracts

Executable exact-signature contracts for Part 4 SD0–SD9 live in this module.
-/

namespace AAT.AG.StatementContractsReadingFunctoriality

open AAT.AG
open CategoryTheory CategoryTheory.Limits

universe u v w w'

variable {U : AtomCarrier.{u}}

example : Type (max (u + 1) (v + 1)) := ReadingCore.{u, v} U
example (p : ReadingCore.{u, v} U) : Type u := ReadingSelection p
example (K L : ObjectAlgebra U) : Type (u + 1) := ObjectAlgebraHom K L
example (P Q : AATCorePackage U) : Type (u + 1) := SignedExactCoreReadingHom P Q
example (P : AATCorePackage U) (A : P.algebra.Obj)
    (i : P.algebra.lawReading.lawUniverse.Index) : Type u :=
  PositiveCircuitDatum P A i
example (P Q : AATCorePackage U) : Type (u + 1) := PositiveCoreReadingHom P Q

example
    (core : AATCorePackage U)
    (geometry : Site.SelectedGeometryReading core)
    (Coefficient : Type v)
    (coefficientCommRing : CommRing Coefficient)
    (raw :
      let _ := coefficientCommRing
      LawAlgebra.RawAmbientRestrictionSystem geometry.toAATSite Coefficient) :
    ReadingCore U :=
  ⟨core, geometry, Coefficient, coefficientCommRing, raw⟩

example
    (p : ReadingCore.{u, v} U)
    (selectedWitness : p.lawUniverse.witnessFamily.Witness → Prop)
    (selectedCircuit : FiniteCircuitDatum U → Prop)
    (selectedAxis : p.signature.Axis → Prop) :
    ReadingSelection p :=
  ⟨selectedWitness, selectedCircuit, selectedAxis⟩

example
    (K L : ObjectAlgebra U)
    (objMap : K.Obj → L.Obj)
    (configurationMap :
      ∀ A, ConfigurationHom (K.object A).configuration
        (L.object (objMap A)).configuration)
    (lawMap :
      K.lawReading.lawUniverse.Index →
        L.lawReading.lawUniverse.Index)
    (required_iff :
      ∀ i,
        K.lawReading.lawUniverse.Required i ↔
          L.lawReading.lawUniverse.Required (lawMap i))
    (law_holds_iff :
      ∀ i A,
        (K.lawReading.lawUniverse.law i).holds (K.object A) ↔
          (L.lawReading.lawUniverse.law (lawMap i)).holds
            (L.object (objMap A)))
    (circuitMap :
      ∀ A i, K.Circuit A i → L.Circuit (objMap A) (lawMap i))
    (operationMap :
      ∀ {A B}, K.Op A B → L.Op (objMap A) (objMap B))
    (operation_naturality :
      ∀ {A B} (op : K.Op A B),
        ConfigurationHom.comp
            (L.configurationMap (operationMap op))
            (configurationMap A) =
          ConfigurationHom.comp
            (configurationMap B)
            (K.configurationMap op))
    (invariantMap :
      K.invariantReading.Index → L.invariantReading.Index)
    (invariant_transport :
      ∀ i,
        Invariant.TransportedAlong
          (K.invariantReading.invariant i)
          (L.invariantReading.invariant (invariantMap i))
          K.object (fun A => L.object (objMap A)))
    (axisMap : K.signatureReading.Axis → L.signatureReading.Axis)
    (coordinateEquiv :
      ∀ i,
        K.signatureReading.Coordinate i ≃
          L.signatureReading.Coordinate (axisMap i))
    (axis_selected_iff :
      ∀ i,
        K.signatureReading.selected i ↔
          L.signatureReading.selected (axisMap i))
    (coordinate_eq :
      ∀ A i,
        coordinateEquiv i
            (K.signatureReading.coordinate (K.object A) i) =
          L.signatureReading.coordinate
            (L.object (objMap A)) (axisMap i)) :
    ObjectAlgebraHom K L :=
  ⟨objMap, configurationMap, lawMap, required_iff, law_holds_iff,
    circuitMap, operationMap, operation_naturality, invariantMap,
    invariant_transport, axisMap, coordinateEquiv, axis_selected_iff,
    coordinate_eq⟩

example
    (P Q : AATCorePackage U)
    (atomMap : U.Atom → U.Atom)
    (extraction_eq : Q.family = P.family.transport atomMap)
    (composition_eq :
      ∀ (F : AtomFamily U) (hF : F.ListFinite),
        Q.reading.composition.compose
            (F.transport atomMap) (hF.transport atomMap) =
          (P.reading.composition.compose F hF).transport atomMap)
    (objectMap : ArchitectureObject U → ArchitectureObject U)
    (object_formation_eq :
      ∀ C,
        objectMap (P.reading.objectReading.object C) =
          Q.reading.objectReading.object (C.transport atomMap))
    (configurationMap :
      ∀ A, ConfigurationHom A.configuration (objectMap A).configuration)
    (configurationMap_atomMap :
      ∀ A, (configurationMap A).atomMap = atomMap)
    (lawMap :
      P.algebra.lawReading.lawUniverse.Index →
        Q.algebra.lawReading.lawUniverse.Index)
    (required_iff :
      ∀ i,
        P.algebra.lawReading.lawUniverse.Required i ↔
          Q.algebra.lawReading.lawUniverse.Required (lawMap i))
    (law_holds_iff :
      ∀ i A,
        (P.algebra.lawReading.lawUniverse.law i).holds A ↔
          (Q.algebra.lawReading.lawUniverse.law (lawMap i)).holds
            (objectMap A))
    (queryMap : FiniteCircuitDatum U → FiniteCircuitDatum U)
    (matches_iff :
      ∀ Qry A, Qry.Matches A ↔ (queryMap Qry).Matches (objectMap A))
    (accepts_iff :
      ∀ i Qry,
        P.algebra.lawReading.circuits.accepts i Qry = true ↔
          Q.algebra.lawReading.circuits.accepts
            (lawMap i) (queryMap Qry) = true)
    (operationMap :
      ∀ {A B},
        P.reading.operationReading.Op A B →
          Q.reading.operationReading.Op (objectMap A) (objectMap B))
    (operation_naturality :
      ∀ {A B} (op : P.reading.operationReading.Op A B),
        ConfigurationHom.comp
            (Q.reading.operationReading.configurationMap (operationMap op))
            (configurationMap A) =
          ConfigurationHom.comp
            (configurationMap B)
            (P.reading.operationReading.configurationMap op))
    (invariantMap :
      P.reading.invariantReading.Index → Q.reading.invariantReading.Index)
    (invariant_transport :
      ∀ i,
        Invariant.TransportedAlong
          (P.reading.invariantReading.invariant i)
          (Q.reading.invariantReading.invariant (invariantMap i))
          _root_.id objectMap)
    (axisMap :
      P.reading.signatureReading.Axis → Q.reading.signatureReading.Axis)
    (coordinateEquiv :
      ∀ i,
        P.reading.signatureReading.Coordinate i ≃
          Q.reading.signatureReading.Coordinate (axisMap i))
    (axis_selected_iff :
      ∀ i,
        P.reading.signatureReading.selected i ↔
          Q.reading.signatureReading.selected (axisMap i))
    (coordinate_eq :
      ∀ A i,
        coordinateEquiv i (P.reading.signatureReading.coordinate A i) =
          Q.reading.signatureReading.coordinate (objectMap A) (axisMap i)) :
    SignedExactCoreReadingHom P Q :=
  ⟨atomMap, extraction_eq, composition_eq, objectMap, object_formation_eq,
    configurationMap, configurationMap_atomMap, lawMap, required_iff,
    law_holds_iff, queryMap, matches_iff, accepts_iff, operationMap,
    operation_naturality, invariantMap, invariant_transport, axisMap,
    coordinateEquiv, axis_selected_iff, coordinate_eq⟩

example
    (P Q : AATCorePackage U)
    (atomMap : U.Atom → U.Atom)
    (extraction_mono : (P.family.transport atomMap).Subset Q.family)
    (compositionMap :
      ∀ (F : AtomFamily U) (hF : F.ListFinite),
        ConfigurationHom
          (P.reading.composition.compose F hF)
          (Q.reading.composition.compose
            (F.transport atomMap) (hF.transport atomMap)))
    (compositionMap_atomMap :
      ∀ F hF, (compositionMap F hF).atomMap = atomMap)
    (objectMap : ArchitectureObject U → ArchitectureObject U)
    (object_formation_eq :
      ∀ C,
        objectMap (P.reading.objectReading.object C) =
          Q.reading.objectReading.object (C.transport atomMap))
    (base_reachable :
      Q.reading.operationReading.Reachable Q.object (objectMap P.object))
    (configurationMap :
      ∀ A, ConfigurationHom A.configuration (objectMap A).configuration)
    (configurationMap_atomMap :
      ∀ A, (configurationMap A).atomMap = atomMap)
    (operationMap :
      ∀ {A B},
        P.reading.operationReading.Op A B →
          Q.reading.operationReading.Op (objectMap A) (objectMap B))
    (operation_naturality :
      ∀ {A B} (op : P.reading.operationReading.Op A B),
        ConfigurationHom.comp
            (Q.reading.operationReading.configurationMap (operationMap op))
            (configurationMap A) =
          ConfigurationHom.comp
            (configurationMap B)
            (P.reading.operationReading.configurationMap op))
    (lawMap :
      P.algebra.lawReading.lawUniverse.Index →
        Q.algebra.lawReading.lawUniverse.Index)
    (queryMap : FiniteCircuitDatum U → FiniteCircuitDatum U)
    (positive_preserved :
      ∀ Qry, Qry.Positive → (queryMap Qry).Positive)
    (matches_of_positive :
      ∀ Qry A, Qry.Positive → Qry.Matches A →
        (queryMap Qry).Matches (objectMap A))
    (accepts_mono :
      ∀ i Qry, Qry.Positive →
        P.algebra.lawReading.circuits.accepts i Qry = true →
          Q.algebra.lawReading.circuits.accepts
            (lawMap i) (queryMap Qry) = true) :
    PositiveCoreReadingHom P Q :=
  ⟨atomMap, extraction_mono, compositionMap, compositionMap_atomMap,
    objectMap, object_formation_eq, base_reachable, configurationMap,
    configurationMap_atomMap, operationMap, operation_naturality, lawMap,
    queryMap, positive_preserved, matches_of_positive, accepts_mono⟩

example (p : ReadingCore.{u, v} U) : Site.AATSite p.core.object := p.site
example (p : ReadingCore.{u, v} U) : LawUniverse U := p.lawUniverse
example (p : ReadingCore.{u, v} U) : ArchitectureSignature U := p.signature

example
    {p q : ReadingCore.{u, v} U}
    (hcore : p.core = q.core)
    (hgeometry : HEq p.geometry q.geometry)
    (hCoefficient : p.Coefficient = q.Coefficient)
    (hcoefficientCommRing :
      HEq p.coefficientCommRing q.coefficientCommRing)
    (hraw : HEq p.raw q.raw) : p = q :=
  ReadingCore.ext hcore hgeometry hCoefficient hcoefficientCommRing hraw

example
    {p : ReadingCore.{u, v} U} {s t : ReadingSelection p}
    (hwitness : s.selectedWitness = t.selectedWitness)
    (hcircuit : s.selectedCircuit = t.selectedCircuit)
    (haxis : s.selectedAxis = t.selectedAxis) : s = t :=
  ReadingSelection.ext hwitness hcircuit haxis

example : (U.Atom → U.Atom) → AtomFamily U → AtomFamily U :=
  AtomFamily.transport

example {F : AtomFamily U} (hF : F.ListFinite)
    (f : U.Atom → U.Atom) : (F.transport f).ListFinite :=
  hF.transport f

example : (U.Atom → U.Atom) → AtomConfiguration U → AtomConfiguration U :=
  AtomConfiguration.transport

example (f : U.Atom → U.Atom) (C : AtomConfiguration U) :
    ConfigurationHom C (C.transport f) :=
  AtomConfiguration.transportHom f C

example (f : U.Atom → U.Atom) (C : AtomConfiguration U) :
    (AtomConfiguration.transportHom f C).atomMap = f :=
  AtomConfiguration.transportHom_atomMap f C

example (I J : Invariant U) {ι : Type w}
    (source target : ι → ArchitectureObject U) : Prop :=
  Invariant.TransportedAlong I J source target

example (I : FunctionInvariant U) (J : PredicateInvariant U)
    {ι : Type w} (source target : ι → ArchitectureObject U) :
    ¬ Invariant.TransportedAlong (.function I) (.predicate J) source target :=
  Invariant.function_predicate_not_transportedAlong I J source target

example (I : Invariant U) {ι : Type w}
    (source : ι → ArchitectureObject U) :
    Invariant.TransportedAlong I I source source :=
  Invariant.transportedAlong_refl I source

example
    {K L : ObjectAlgebra U} {f g : ObjectAlgebraHom K L}
    (hobj : f.objMap = g.objMap)
    (hconfiguration : HEq f.configurationMap g.configurationMap)
    (hlaw : HEq f.lawMap g.lawMap)
    (hcircuit : HEq f.circuitMap g.circuitMap)
    (hoperation : HEq
      (@ObjectAlgebraHom.operationMap U K L f)
      (@ObjectAlgebraHom.operationMap U K L g))
    (hinvariant : HEq f.invariantMap g.invariantMap)
    (haxis : HEq f.axisMap g.axisMap)
    (hcoordinate : HEq f.coordinateEquiv g.coordinateEquiv) : f = g :=
  ObjectAlgebraHom.ext hobj hconfiguration hlaw hcircuit hoperation
    hinvariant haxis hcoordinate

example (K : ObjectAlgebra U) : ObjectAlgebraHom K K := ObjectAlgebraHom.id K
example {K L M : ObjectAlgebra U} (f : ObjectAlgebraHom K L)
    (g : ObjectAlgebraHom L M) : ObjectAlgebraHom K M := f.comp g
example (K : ObjectAlgebra U) : (ObjectAlgebraHom.id K).objMap = _root_.id :=
  ObjectAlgebraHom.id_objMap K
example {K L M : ObjectAlgebra U} (f : ObjectAlgebraHom K L)
    (g : ObjectAlgebraHom L M) :
    (f.comp g).objMap = g.objMap ∘ f.objMap :=
  ObjectAlgebraHom.comp_objMap f g

example
    {P Q : AATCorePackage U} {f g : SignedExactCoreReadingHom P Q}
    (hatom : f.atomMap = g.atomMap)
    (hobject : f.objectMap = g.objectMap)
    (hlaw : HEq f.lawMap g.lawMap)
    (hquery : HEq f.queryMap g.queryMap)
    (hoperation : HEq
      (@SignedExactCoreReadingHom.operationMap U P Q f)
      (@SignedExactCoreReadingHom.operationMap U P Q g))
    (hinvariant : HEq f.invariantMap g.invariantMap)
    (haxis : HEq f.axisMap g.axisMap)
    (hcoordinate : HEq f.coordinateEquiv g.coordinateEquiv) : f = g :=
  SignedExactCoreReadingHom.ext hatom hobject hlaw hquery hoperation
    hinvariant haxis hcoordinate

example (P : AATCorePackage U) : SignedExactCoreReadingHom P P :=
  SignedExactCoreReadingHom.refl P
example {P Q R : AATCorePackage U} (f : SignedExactCoreReadingHom P Q)
    (g : SignedExactCoreReadingHom Q R) : SignedExactCoreReadingHom P R :=
  f.comp g
noncomputable example {P Q : AATCorePackage U} (f : SignedExactCoreReadingHom P Q) :
    Q.configuration = P.configuration.transport f.atomMap :=
  f.generatedConfiguration_eq
example {P Q : AATCorePackage U} (f : SignedExactCoreReadingHom P Q) :
    f.objectMap P.object = Q.object := f.base_eq
noncomputable example {P Q : AATCorePackage U} (f : SignedExactCoreReadingHom P Q) :
    ObjectAlgebraHom P.algebra Q.algebra := f.toObjectAlgebraHom
example (P : AATCorePackage U) :
    (SignedExactCoreReadingHom.refl P).toObjectAlgebraHom =
      ObjectAlgebraHom.id P.algebra :=
  SignedExactCoreReadingHom.toObjectAlgebraHom_refl P
example {P Q R : AATCorePackage U} (f : SignedExactCoreReadingHom P Q)
    (g : SignedExactCoreReadingHom Q R) :
    (f.comp g).toObjectAlgebraHom =
      f.toObjectAlgebraHom.comp g.toObjectAlgebraHom :=
  SignedExactCoreReadingHom.toObjectAlgebraHom_comp f g

example (Qry : FiniteCircuitDatum U) : Prop := Qry.Positive
example (query : CircuitQuery U) :
    (⟨[(query, true)]⟩ : FiniteCircuitDatum U).Positive :=
  FiniteCircuitDatum.positive_singleton query
example (query : CircuitQuery U) :
    ¬ (⟨[(query, false)]⟩ : FiniteCircuitDatum U).Positive :=
  FiniteCircuitDatum.not_positive_singleton_false query

example
    {P Q : AATCorePackage U} {f g : PositiveCoreReadingHom P Q}
    (hatom : f.atomMap = g.atomMap)
    (hobject : f.objectMap = g.objectMap)
    (hoperation : HEq
      (@PositiveCoreReadingHom.operationMap U P Q f)
      (@PositiveCoreReadingHom.operationMap U P Q g))
    (hlaw : HEq f.lawMap g.lawMap)
    (hquery : f.queryMap = g.queryMap) : f = g :=
  PositiveCoreReadingHom.ext hatom hobject hoperation hlaw hquery

example (P : AATCorePackage U) : PositiveCoreReadingHom P P :=
  PositiveCoreReadingHom.refl P
example {P Q R : AATCorePackage U} (f : PositiveCoreReadingHom P Q)
    (g : PositiveCoreReadingHom Q R) : PositiveCoreReadingHom P R :=
  f.comp g
example {P Q : AATCorePackage U} (f : PositiveCoreReadingHom P Q)
    {A : ArchitectureObject U}
    (hA : P.reading.operationReading.Reachable P.object A) :
    Q.reading.operationReading.Reachable Q.object (f.objectMap A) :=
  f.mapReachable hA
example {P Q : AATCorePackage U} (f : PositiveCoreReadingHom P Q) :
    P.algebra.Obj → Q.algebra.Obj := f.objMap
example {P Q : AATCorePackage U} (f : PositiveCoreReadingHom P Q)
    {A : P.algebra.Obj} {i : P.algebra.lawReading.lawUniverse.Index}
    (c : PositiveCircuitDatum P A i) :
    PositiveCircuitDatum Q (f.objMap A) (f.lawMap i) :=
  f.mapPositiveCircuit c

example (p q : ReadingCore.{u, v} U) : Type (u + 1) := p.ExactCoreChange q
example (p q : ReadingCore.{u, v} U) : Type (u + 1) := p.PositiveCoreChange q
example (p : ReadingCore.{u, v} U) (base : p.site.category) : Type (u + 1) :=
  p.SelectedCover base

/-! Part 4 R2: direct reuse of closed-equational law comparison. -/

section ClosedEquationalDirectReuse

variable {A : ArchitectureObject U}
variable {S : Site.AATSite A} {k : Type v} [CommRing k]
variable (raw : LawAlgebra.RawAmbientRestrictionSystem S k)
variable [CategoryTheory.HasSheafify S.topology (LawAlgebra.AATCommAlgCat k)]
variable (X : LawAlgebra.StandardArchitectureScheme raw)

noncomputable example
    {R Q : LawAlgebra.ClosedEquationalLawReading raw X}
    (hR : LawAlgebra.IsClosedEquationalLawReading raw X R)
    (hQ : LawAlgebra.IsClosedEquationalLawReading raw X Q)
    (hRclosed : LawAlgebra.RequiredClosed raw X R)
    (hQclosed : LawAlgebra.RequiredClosed raw X Q)
    (e : LawAlgebra.ClosedEquationalLawInclusion raw X R Q)
    (he : LawAlgebra.IsClosedEquationalLawInclusion raw X e) :
    LawAlgebra.lawGeneratedIdealSheaf raw X R hR hRclosed ≤
      LawAlgebra.lawGeneratedIdealSheaf raw X Q hQ hQclosed :=
  LawAlgebra.lawGeneratedIdealSheaf_mono
    raw X hR hQ hRclosed hQclosed e he

noncomputable example
    {R Q : LawAlgebra.ClosedEquationalLawReading raw X}
    (hR : LawAlgebra.IsClosedEquationalLawReading raw X R)
    (hQ : LawAlgebra.IsClosedEquationalLawReading raw X Q)
    (e : LawAlgebra.ClosedEquationalLawInclusion raw X R Q)
    (he : LawAlgebra.IsClosedEquationalLawInclusion raw X e) :
    LawAlgebra.allLawGeneratedIdealSheaf raw X R hR ≤
      LawAlgebra.allLawGeneratedIdealSheaf raw X Q hQ :=
  LawAlgebra.allLawGeneratedIdealSheaf_mono raw X hR hQ e he

noncomputable example
    {R Q : LawAlgebra.ClosedEquationalLawReading raw X}
    (hR : LawAlgebra.IsClosedEquationalLawReading raw X R)
    (hQ : LawAlgebra.IsClosedEquationalLawReading raw X Q)
    (hRclosed : LawAlgebra.RequiredClosed raw X R)
    (hQclosed : LawAlgebra.RequiredClosed raw X Q)
    (e : LawAlgebra.ClosedEquationalLawInclusion raw X R Q)
    (he : LawAlgebra.IsClosedEquationalLawInclusion raw X e) :
    LawAlgebra.lawfulClosedSubscheme raw X Q hQ hQclosed ⟶
      LawAlgebra.lawfulClosedSubscheme raw X R hR hRclosed :=
  LawAlgebra.lawfulClosedSubschemeMap
    raw X hR hQ hRclosed hQclosed e he

noncomputable example
    {R Q : LawAlgebra.ClosedEquationalLawReading raw X}
    (hR : LawAlgebra.IsClosedEquationalLawReading raw X R)
    (hQ : LawAlgebra.IsClosedEquationalLawReading raw X Q)
    (e : LawAlgebra.ClosedEquationalLawInclusion raw X R Q)
    (he : LawAlgebra.IsClosedEquationalLawInclusion raw X e) :
    LawAlgebra.allLawfulClosedSubscheme raw X Q hQ ⟶
      LawAlgebra.allLawfulClosedSubscheme raw X R hR :=
  LawAlgebra.allLawfulClosedSubschemeMap raw X hR hQ e he

example
    {R Q : LawAlgebra.ClosedEquationalLawReading raw X}
    (e : LawAlgebra.ClosedEquationalLawInclusion raw X R Q)
    (he : LawAlgebra.IsClosedEquationalLawInclusion raw X e)
    {T : AlgebraicGeometry.Scheme}
    (s : T ⟶ X.underlying) :
    LawAlgebra.SemanticLawfulAlong raw X Q s →
      LawAlgebra.SemanticLawfulAlong raw X R s :=
  LawAlgebra.semanticLawfulAlong_mono raw X e he s

example
    {R Q : LawAlgebra.ClosedEquationalLawReading raw X}
    (e : LawAlgebra.ClosedEquationalLawInclusion raw X R Q)
    (he : LawAlgebra.IsClosedEquationalLawInclusion raw X e)
    {T : AlgebraicGeometry.Scheme}
    (s : T ⟶ X.underlying) :
    LawAlgebra.FullySemanticLawfulAlong raw X Q s →
      LawAlgebra.FullySemanticLawfulAlong raw X R s :=
  LawAlgebra.fullySemanticLawfulAlong_mono raw X e he s

end ClosedEquationalDirectReuse

namespace ClosedEquationalFiniteDirectReuse

open LawAlgebra.FiniteExamples.ClosedEquationalGeometry
open LawAlgebra.FiniteExamples.RingedSite.FiniteModel
open LawAlgebra.FiniteExamples.StandardArchitectureScheme

example :
    LawAlgebra.ClosedEquationalLawInclusion rawSystem twoChartReferenceModel
      weakReading strongReading :=
  weakToStrong

example :
    LawAlgebra.IsClosedEquationalLawInclusion rawSystem twoChartReferenceModel
      weakToStrong :=
  weakToStrong_valid

example :
    LawAlgebra.lawGeneratedIdealSheaf rawSystem twoChartReferenceModel
        weakReading weakReading_valid weakReading_requiredClosed <
      LawAlgebra.lawGeneratedIdealSheaf rawSystem twoChartReferenceModel
        strongReading strongReading_valid strongReading_requiredClosed :=
  weak_ideal_lt_strong

example :
    ¬ CategoryTheory.IsIso (LawAlgebra.lawfulClosedSubschemeMap rawSystem
      twoChartReferenceModel
      weakReading_valid strongReading_valid
      weakReading_requiredClosed strongReading_requiredClosed
      weakToStrong weakToStrong_valid) :=
  weakToStrongMap_not_isIso

example :
    ¬ CategoryTheory.IsIso (LawAlgebra.allLawfulClosedSubschemeMap rawSystem
      twoChartReferenceModel weakReading_valid strongReading_valid
      weakToStrong weakToStrong_valid) :=
  weakToStrongAllMap_not_isIso

example :
    ¬ LawAlgebra.IsClosedEquationalLawInclusion rawSystem
      twoChartReferenceModel coordinateBrokenInclusion :=
  coordinateBrokenInclusion_not_valid

end ClosedEquationalFiniteDirectReuse

namespace CoverageRefinementSD3

open CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- Fixed constructor contract for topology refinement. -/
example (J J' : GrothendieckTopology C)
    (refineCover : ∀ (X : C) (R : Sieve X), R ∈ J X →
      {R' : Sieve X // R' ∈ J' X ∧ R' ≤ R}) :
    CoverageTopologyRefinement J J' :=
  ⟨refineCover⟩

/-- Fixed topology-order contract induced by refinement. -/
example {J J' : GrothendieckTopology C}
    (r : CoverageTopologyRefinement J J') : J ≤ J' :=
  CoverageTopologyRefinement.le r

/-- Fixed identity topology-refinement contract. -/
example (J : GrothendieckTopology C) : CoverageTopologyRefinement J J :=
  CoverageTopologyRefinement.refl J

/-- Fixed composite topology-refinement contract. -/
example {J₁ J₂ J₃ : GrothendieckTopology C}
    (f : CoverageTopologyRefinement J₁ J₂)
    (g : CoverageTopologyRefinement J₂ J₃) :
    CoverageTopologyRefinement J₁ J₃ :=
  CoverageTopologyRefinement.comp f g

variable {A : ArchitectureObject U}
variable {S : Site.AATSite A} {base : S.category}

/-- Fixed constructor contract for selected-cover refinement. -/
example
    (coarse fine : Site.AATCoverageFamily S.requirements S.overlap base)
    (indexMap : fine.Index → coarse.Index)
    (factor : ∀ i, S.contextPreorder.le (fine.patch i) (coarse.patch (indexMap i)))
    (factor_triangle : ∀ i,
      S.contextPreorder.trans (factor i) (coarse.inclusion (indexMap i)) =
        fine.inclusion i) :
    Site.AATCoverageFamily.Refinement coarse fine :=
  ⟨indexMap, factor, factor_triangle⟩

/-- Fixed identity selected-cover refinement contract. -/
example (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base) :
    Site.AATCoverageFamily.Refinement 𝒰 𝒰 :=
  Site.AATCoverageFamily.Refinement.refl 𝒰

/-- Fixed composite selected-cover refinement contract. -/
example {𝒰 𝒱 𝒲 : Site.AATCoverageFamily S.requirements S.overlap base}
    (r : Site.AATCoverageFamily.Refinement 𝒰 𝒱)
    (s : Site.AATCoverageFamily.Refinement 𝒱 𝒲) :
    Site.AATCoverageFamily.Refinement 𝒰 𝒲 :=
  r.comp s

/-- Fixed generated-sieve inclusion contract. -/
example {𝒰 𝒱 : Site.AATCoverageFamily S.requirements S.overlap base}
    (r : Site.AATCoverageFamily.Refinement 𝒰 𝒱) :
    Sieve.generate 𝒱.presieve ≤ Sieve.generate 𝒰.presieve :=
  r.presieve_le

/-- Fixed selected-cover membership contract. -/
example (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base) :
    Sieve.generate 𝒰.presieve ∈ S.topology base :=
  𝒰.mem_topology

/-- Fixed canonical tuple-overlap constructor contract. -/
noncomputable example
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base) :
    ∀ n, Site.FinitePosetCechCanonicalTupleSimplex 𝒰.Index n → S.category :=
  Cohomology.canonicalTupleOverlap 𝒰

/-- Fixed degree-zero tuple-overlap contract. -/
example (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (σ : Fin 1 → 𝒰.Index) :
    Cohomology.canonicalTupleOverlap 𝒰 0 σ =
      Site.ContextCategoryObject.of S.contextPreorder (𝒰.patch (σ 0)) :=
  Cohomology.canonicalTupleOverlap_zero 𝒰 σ

/-- Fixed successor tuple-overlap contract. -/
example (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (n : Nat) (σ : Fin (n + 2) → 𝒰.Index) :
    (Cohomology.canonicalTupleOverlap 𝒰 (n + 1) σ).ctx =
      S.overlap.overlap base.ctx
        (Cohomology.canonicalTupleOverlap 𝒰 n (fun i => σ i.castSucc)).ctx
        (𝒰.patch (σ (Fin.last (n + 1)))) :=
  Cohomology.canonicalTupleOverlap_succ 𝒰 n σ

/-- Fixed projection from a tuple overlap to any selected chart. -/
noncomputable example
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    {n : Nat} (σ : Fin (n + 1) → 𝒰.Index) (k : Fin (n + 1)) :
    Cohomology.canonicalTupleOverlap 𝒰 n σ ⟶
      Site.ContextCategoryObject.of S.contextPreorder (𝒰.patch (σ k)) :=
  Cohomology.canonicalTupleOverlapProjection 𝒰 σ k

/-- Fixed universal lift into a tuple overlap. -/
noncomputable example
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    {n : Nat} (σ : Fin (n + 1) → 𝒰.Index) {X : S.category}
    (h : ∀ k, X ⟶
      Site.ContextCategoryObject.of S.contextPreorder (𝒰.patch (σ k))) :
    X ⟶ Cohomology.canonicalTupleOverlap 𝒰 n σ :=
  Cohomology.canonicalTupleOverlapLift 𝒰 σ h

/-- Fixed component equation for the tuple-overlap lift. -/
example
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    {n : Nat} (σ : Fin (n + 1) → 𝒰.Index) {X : S.category}
    (h : ∀ k, X ⟶
      Site.ContextCategoryObject.of S.contextPreorder (𝒰.patch (σ k)))
    (k : Fin (n + 1)) :
    Cohomology.canonicalTupleOverlapLift 𝒰 σ h ≫
        Cohomology.canonicalTupleOverlapProjection 𝒰 σ k = h k :=
  Cohomology.canonicalTupleOverlapLift_comp_chart 𝒰 σ h k

/-- Fixed overlap morphism induced contravariantly by a simplex morphism. -/
noncomputable example
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    {x y : SimplexCategory} (f : x ⟶ y)
    (σ : Fin (y.len + 1) → 𝒰.Index) :
    Cohomology.canonicalTupleOverlap 𝒰 y.len σ ⟶
      Cohomology.canonicalTupleOverlap 𝒰 x.len
        (fun i ↦ σ (f.toOrderHom i)) :=
  Cohomology.canonicalTupleOverlapMap 𝒰 f σ

/-- Fixed identity law for tuple-overlap maps. -/
example
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (x : SimplexCategory) (σ : Fin (x.len + 1) → 𝒰.Index) :
    Cohomology.canonicalTupleOverlapMap 𝒰 (𝟙 x) σ = 𝟙 _ :=
  Cohomology.canonicalTupleOverlapMap_id 𝒰 x σ

/-- Fixed composition law for tuple-overlap maps. -/
example
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    {x y z : SimplexCategory} (f : x ⟶ y) (g : y ⟶ z)
    (σ : Fin (z.len + 1) → 𝒰.Index) :
    Cohomology.canonicalTupleOverlapMap 𝒰 (f ≫ g) σ =
      Cohomology.canonicalTupleOverlapMap 𝒰 g σ ≫
        Cohomology.canonicalTupleOverlapMap 𝒰 f
          (fun i ↦ σ (g.toOrderHom i)) :=
  Cohomology.canonicalTupleOverlapMap_comp 𝒰 f g σ

/-- Fixed canonical face-order contract. -/
example (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (n : Nat) (i : Fin (n + 2)) (σ : Fin (n + 2) → 𝒰.Index) :
    S.contextPreorder.le
      (Cohomology.canonicalTupleOverlap 𝒰 (n + 1) σ).ctx
      (Cohomology.canonicalTupleOverlap 𝒰 n
        (Site.FinitePosetCechCanonicalTupleSimplex.simplexMap
          (SimplexCategory.δ i) σ)).ctx :=
  Cohomology.canonicalTupleOverlap_face_le 𝒰 n i σ

/-- Fixed canonical cover-relative constructor contract. -/
noncomputable example
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base) :
    Cohomology.CoverRelativeCechCover S :=
  Cohomology.canonicalCoverRelative 𝒰

/-- Fixed canonical base characterization contract. -/
example (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base) :
    (Cohomology.canonicalCoverRelative 𝒰).base = base :=
  Cohomology.canonicalCoverRelative_base 𝒰

/-- Fixed canonical simplex characterization contract. -/
example (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base) (n : Nat) :
    (Cohomology.canonicalCoverRelative 𝒰).simplex n =
      Site.FinitePosetCechCanonicalTupleSimplex 𝒰.Index n :=
  Cohomology.canonicalCoverRelative_simplex 𝒰 n

/-- Fixed canonical overlap characterization contract. -/
example (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (n : Nat) (σ : Fin (n + 1) → 𝒰.Index) :
    (Cohomology.canonicalCoverRelative 𝒰).overlap n σ =
      Cohomology.canonicalTupleOverlap 𝒰 n σ :=
  Cohomology.canonicalCoverRelative_overlap 𝒰 n σ

/-- Fixed canonical face characterization contract. -/
example (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (n : Nat) (i : Fin (n + 2)) (σ : Fin (n + 2) → 𝒰.Index) :
    (Cohomology.canonicalCoverRelative 𝒰).face n i σ =
      Site.FinitePosetCechCanonicalTupleSimplex.simplexMap
        (SimplexCategory.δ i) σ :=
  Cohomology.canonicalCoverRelative_face 𝒰 n i σ

/-- Fixed canonical two-face contract. -/
example (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (n : Nat) (σ : (Cohomology.canonicalCoverRelative 𝒰).simplex (n + 2))
    (i j : Fin (n + 2)) (hij : i ≤ j) :
    (Cohomology.canonicalCoverRelative 𝒰).face n i
        ((Cohomology.canonicalCoverRelative 𝒰).face (n + 1) j.succ σ) =
      (Cohomology.canonicalCoverRelative 𝒰).face n j
        ((Cohomology.canonicalCoverRelative 𝒰).face (n + 1) i.castSucc σ) :=
  Cohomology.canonicalCoverRelative_twoFace 𝒰 n σ i j hij

/-- Fixed canonical two-face restriction contract. -/
example (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (n : Nat) (σ : (Cohomology.canonicalCoverRelative 𝒰).simplex (n + 2))
    (i j : Fin (n + 2)) (hij : i ≤ j) :
    (Cohomology.canonicalCoverRelative 𝒰).faceRestriction (n + 1) j.succ σ ≫
        (Cohomology.canonicalCoverRelative 𝒰).faceRestriction n i
          ((Cohomology.canonicalCoverRelative 𝒰).face (n + 1) j.succ σ) =
      (Cohomology.canonicalCoverRelative 𝒰).faceRestriction (n + 1) i.castSucc σ ≫
        (Cohomology.canonicalCoverRelative 𝒰).faceRestriction n j
          ((Cohomology.canonicalCoverRelative 𝒰).face (n + 1) i.castSucc σ) ≫
        eqToHom (congrArg ((Cohomology.canonicalCoverRelative 𝒰).overlap n)
          (Cohomology.canonicalCoverRelative_twoFace 𝒰 n σ i j hij).symm) :=
  Cohomology.canonicalCoverRelative_faceRestriction_twoFace 𝒰 n σ i j hij

/-- Fixed refinement-induced simplex map contract. -/
example {𝒰 𝒱 : Site.AATCoverageFamily S.requirements S.overlap base}
    (r : Site.AATCoverageFamily.Refinement 𝒰 𝒱) (n : Nat) :
    (Cohomology.canonicalCoverRelative 𝒱).simplex n →
      (Cohomology.canonicalCoverRelative 𝒰).simplex n :=
  r.simplexMap n

/-- Fixed refinement-induced overlap map contract. -/
noncomputable example
    {𝒰 𝒱 : Site.AATCoverageFamily S.requirements S.overlap base}
    (r : Site.AATCoverageFamily.Refinement 𝒰 𝒱) (n : Nat)
    (σ : (Cohomology.canonicalCoverRelative 𝒱).simplex n) :
    (Cohomology.canonicalCoverRelative 𝒱).overlap n σ ⟶
      (Cohomology.canonicalCoverRelative 𝒰).overlap n (r.simplexMap n σ) :=
  r.overlapMap n σ

/-- Fixed refinement face-naturality contract. -/
example {𝒰 𝒱 : Site.AATCoverageFamily S.requirements S.overlap base}
    (r : Site.AATCoverageFamily.Refinement 𝒰 𝒱)
    (n : Nat) (i : Fin (n + 2))
    (σ : (Cohomology.canonicalCoverRelative 𝒱).simplex (n + 1)) :
    (Cohomology.canonicalCoverRelative 𝒱).faceRestriction n i σ ≫
        r.overlapMap n ((Cohomology.canonicalCoverRelative 𝒱).face n i σ) =
      r.overlapMap (n + 1) σ ≫
        (Cohomology.canonicalCoverRelative 𝒰).faceRestriction n i
          (r.simplexMap (n + 1) σ) :=
  r.overlapMap_face_naturality n i σ

open AAT.AG.ReadingFunctorialityFinite

/-- Fixed finite-site contract for the R3 reference model. -/
noncomputable example : Site.AATSite FiniteModel.corePackage.object :=
  finiteSite

/-- Fixed finite-base contract for the R3 reference model. -/
noncomputable example : finiteSite.category :=
  finiteBase

/-- Fixed coarse selected-cover contract for the R3 reference model. -/
noncomputable example :
    Site.AATCoverageFamily finiteSite.requirements finiteSite.overlap finiteBase :=
  coarseCover

/-- Fixed fine selected-cover contract for the R3 reference model. -/
noncomputable example :
    Site.AATCoverageFamily finiteSite.requirements finiteSite.overlap finiteBase :=
  fineCover

/-- Fixed actual finite selected-cover refinement contract. -/
noncomputable example : Site.AATCoverageFamily.Refinement coarseCover fineCover :=
  coarseToFineCover

/-- Fixed non-bijective finite refinement contract. -/
example : ¬ Function.Bijective coarseToFineCover.indexMap :=
  coarseToFineCover_not_bijective

end CoverageRefinementSD3

namespace CanonicalCechFunctorialitySD4

open CategoryTheory Opposite

variable {A : ArchitectureObject U}
variable {S : Site.AATSite A} {base : S.category}
variable {𝒰 𝒱 𝒲 : Site.AATCoverageFamily S.requirements S.overlap base}
variable (Ob : Cohomology.ObstructionSheaf S)

/-- Fixed additive restriction-map contract. -/
example {X Y : S.category} (f : X ⟶ Y) :
    Ob.carrier.toPresheaf.obj (op Y) →+
      Ob.carrier.toPresheaf.obj (op X) :=
  Ob.mapAddMonoidHom f

/-- Fixed canonical Čech complex contract. -/
noncomputable example :
    Cohomology.CoverRelativeCechComplex
      (Cohomology.canonicalCoverRelative 𝒰) Ob :=
  Cohomology.canonicalCechComplex 𝒰 Ob

/-- Fixed explicit canonical-differential contract. -/
example (n : Nat)
    (c : (Cohomology.canonicalCechComplex 𝒰 Ob).AdditiveCochain n)
    (σ : (Cohomology.canonicalCoverRelative 𝒰).simplex (n + 1)) :
    (Cohomology.canonicalCechComplex 𝒰 Ob).d n c σ =
      ∑ i : Fin (n + 2), ((-1 : ℤ) ^ i.1) •
        Ob.mapAddMonoidHom
          ((Cohomology.canonicalCoverRelative 𝒰).faceRestriction n i σ)
          (c ((Cohomology.canonicalCoverRelative 𝒰).face n i σ)) :=
  Cohomology.canonicalCechComplex_d_apply 𝒰 Ob n c σ

/-- Fixed derived square-zero contract. -/
example (n : Nat)
    (c : (Cohomology.canonicalCechComplex 𝒰 Ob).AdditiveCochain n) :
    (Cohomology.canonicalCechComplex 𝒰 Ob).d (n + 1)
        ((Cohomology.canonicalCechComplex 𝒰 Ob).d n c) =
      (0 : (Cohomology.canonicalCechComplex 𝒰 Ob).AdditiveCochain (n + 2)) :=
  Cohomology.canonicalCechComplex_d_comp_d 𝒰 Ob n c

variable {K : Cohomology.CoverRelativeCechComplex
  (Cohomology.canonicalCoverRelative 𝒰) Ob}
variable {L : Cohomology.CoverRelativeCechComplex
  (Cohomology.canonicalCoverRelative 𝒱) Ob}
variable {M : Cohomology.CoverRelativeCechComplex
  (Cohomology.canonicalCoverRelative 𝒲) Ob}

/-- Fixed arbitrary-degree additive Čech cohomology contract. -/
example (n : Nat) : Type u := K.AdditiveCechHn n

/-- Fixed additive-group instance contract in every cohomological degree. -/
noncomputable example (n : Nat) : AddCommGroup (K.AdditiveCechHn n) :=
  inferInstance

/-- Fixed cocycle-class contract. -/
noncomputable example (n : Nat) : K.CechCocycle n → K.AdditiveCechHn n :=
  K.additiveCohomologyClass n

/-- Fixed cochain-map constructor contract. -/
example
    (app : ∀ n, K.AdditiveCochain n →+ L.AdditiveCochain n)
    (commutes : ∀ n c, app (n + 1) (K.d n c) = L.d n (app n c)) :
    Cohomology.CoverRelativeCechComplex.Hom K L :=
  ⟨app, commutes⟩

/-- Fixed cocycle-map contract. -/
noncomputable example (f : Cohomology.CoverRelativeCechComplex.Hom K L) (n : Nat) :
    K.CechCocycle n → L.CechCocycle n :=
  f.mapCocycle n

/-- Fixed identity cochain-map contract. -/
noncomputable example : Cohomology.CoverRelativeCechComplex.Hom K K :=
  Cohomology.CoverRelativeCechComplex.Hom.id K

/-- Fixed composite cochain-map contract. -/
noncomputable example (f : Cohomology.CoverRelativeCechComplex.Hom K L)
    (g : Cohomology.CoverRelativeCechComplex.Hom L M) :
    Cohomology.CoverRelativeCechComplex.Hom K M :=
  f.comp g

/-- Fixed arbitrary-degree induced cohomology-map contract. -/
noncomputable example (f : Cohomology.CoverRelativeCechComplex.Hom K L) (n : Nat) :
    K.AdditiveCechHn n →+ L.AdditiveCechHn n :=
  f.mapAdditiveCechHn n

/-- Fixed identity law for induced cohomology maps. -/
example (n : Nat) :
    (Cohomology.CoverRelativeCechComplex.Hom.id K).mapAdditiveCechHn n =
      AddMonoidHom.id _ :=
  Cohomology.CoverRelativeCechComplex.Hom.mapAdditiveCechHn_id K n

/-- Fixed composition law for induced cohomology maps. -/
example (f : Cohomology.CoverRelativeCechComplex.Hom K L)
    (g : Cohomology.CoverRelativeCechComplex.Hom L M) (n : Nat) :
    (f.comp g).mapAdditiveCechHn n =
      (g.mapAdditiveCechHn n).comp (f.mapAdditiveCechHn n) :=
  Cohomology.CoverRelativeCechComplex.Hom.mapAdditiveCechHn_comp f g n

/-- Fixed refinement-induced canonical cochain-map contract. -/
noncomputable example (r : Site.AATCoverageFamily.Refinement 𝒰 𝒱) :
    Cohomology.CoverRelativeCechComplex.Hom
      (Cohomology.canonicalCechComplex 𝒰 Ob)
      (Cohomology.canonicalCechComplex 𝒱 Ob) :=
  r.canonicalCechHom Ob

/-- Fixed pointwise refinement-map formula contract. -/
example (r : Site.AATCoverageFamily.Refinement 𝒰 𝒱) (n : Nat)
    (c : (Cohomology.canonicalCechComplex 𝒰 Ob).AdditiveCochain n)
    (σ : (Cohomology.canonicalCoverRelative 𝒱).simplex n) :
    (r.canonicalCechHom Ob).app n c σ =
      Ob.mapAddMonoidHom (r.overlapMap n σ) (c (r.simplexMap n σ)) :=
  r.canonicalCechHom_app_apply Ob n c σ

/-- Fixed identity law for canonical refinement maps. -/
example :
    (Site.AATCoverageFamily.Refinement.refl 𝒰).canonicalCechHom Ob =
      Cohomology.CoverRelativeCechComplex.Hom.id
        (Cohomology.canonicalCechComplex 𝒰 Ob) :=
  Site.AATCoverageFamily.Refinement.canonicalCechHom_refl 𝒰 Ob

/-- Fixed composition law for canonical refinement maps. -/
example (r : Site.AATCoverageFamily.Refinement 𝒰 𝒱)
    (s : Site.AATCoverageFamily.Refinement 𝒱 𝒲) :
    (r.comp s).canonicalCechHom Ob =
      (r.canonicalCechHom Ob).comp (s.canonicalCechHom Ob) :=
  r.canonicalCechHom_comp s Ob

/-- Fixed obstruction-class naturality contract. -/
example (r : Site.AATCoverageFamily.Refinement 𝒰 𝒱) (n : Nat)
    (c : (Cohomology.canonicalCechComplex 𝒰 Ob).CechCocycle n) :
    (r.canonicalCechHom Ob).mapAdditiveCechHn n
        ((Cohomology.canonicalCechComplex 𝒰 Ob).additiveCohomologyClass n c) =
      (Cohomology.canonicalCechComplex 𝒱 Ob).additiveCohomologyClass n
        ((r.canonicalCechHom Ob).mapCocycle n c) :=
  Cohomology.obstructionClass_naturality r Ob n c

end CanonicalCechFunctorialitySD4

namespace SheafCohomologyFoundationSD5

open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]
variable {J J' : GrothendieckTopology C}

/-- Fixed standard Ext-universe contract for additive sheaves. -/
noncomputable example [HasSheafify J AddCommGrpCat.{w}] :
    HasExt.{max (max u v) (w + 1)}
      (Sheaf J AddCommGrpCat.{w}) :=
  Cohomology.standardAddCommGrpSheafHasExt

variable {A : ArchitectureObject U}
variable {S : Site.AATSite A} {base : S.category}
variable (Ob : Cohomology.ObstructionSheaf S)

/-- Fixed actual additive obstruction-sheaf contract. -/
noncomputable example :
    Sheaf S.topology AddCommGrpCat.{u + 1} :=
  Ob.toAddCommGrpSheaf

/-- Fixed AAT sheaf Ext-instance contract. -/
noncomputable example [HasSheafify S.topology AddCommGrpCat.{u + 1}] :
    HasExt.{u + 2} (Sheaf S.topology AddCommGrpCat.{u + 1}) :=
  Cohomology.aatSheafHasExt

/-- Fixed terminal local-to-global cohomology comparison contract. -/
noncomputable example
    (F : Sheaf J AddCommGrpCat.{v})
    [HasSheafify J AddCommGrpCat.{v}]
    [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]
    (X : C) (hX : IsTerminal X) (n : Nat) :
    F.H' n X ≃+ F.H n :=
  Cohomology.terminalHComparison F X hX n

variable (P : Cᵒᵖ ⥤ AddCommGrpCat.{w})
variable (hJ : Presheaf.IsSheaf J P) (hJ' : Presheaf.IsSheaf J' P)

/-- Fixed common-coefficient package contract. -/
example : CommonCoefficientSheaf J J' :=
  ⟨P, hJ, hJ'⟩

variable (F : CommonCoefficientSheaf J J')

/-- Fixed coarse coefficient-sheaf contract. -/
example : Sheaf J AddCommGrpCat.{w} := F.coarse

/-- Fixed fine coefficient-sheaf contract. -/
example : Sheaf J' AddCommGrpCat.{w} := F.fine

/-- Fixed same-topology coefficient iso contract. -/
noncomputable example (G : CommonCoefficientSheaf J J) :
    G.coarse ≅ G.fine :=
  G.sameTopologyIso

/-- Fixed same-topology cohomology map contract. -/
noncomputable example
    (G : CommonCoefficientSheaf J J)
    [HasSheafify J AddCommGrpCat.{w}]
    [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]
    (n : Nat) :
    G.coarse.H n →+ G.fine.H n :=
  G.sameTopologyHMap n

variable (r : CoverageTopologyRefinement J J')

/-- Fixed fine-sheafification functor contract. -/
noncomputable example [HasSheafify J' AddCommGrpCat.{w}] :
    Sheaf J AddCommGrpCat.{w} ⥤ Sheaf J' AddCommGrpCat.{w} :=
  r.fineSheafification

/-- Fixed coarse sheaf-condition transport contract. -/
example (h : Presheaf.IsSheaf J' P) : Presheaf.IsSheaf J P :=
  r.isSheaf_coarse P h

/-- Fixed coarse-restriction functor contract. -/
example : Sheaf J' AddCommGrpCat.{w} ⥤ Sheaf J AddCommGrpCat.{w} :=
  r.coarseRestriction

/-- Fixed fine-sheafification adjunction contract. -/
noncomputable example [HasSheafify J' AddCommGrpCat.{w}] :
    r.fineSheafification ⊣ r.coarseRestriction :=
  r.fineSheafificationAdjunction

/-- Fixed additive fine-sheafification contract. -/
noncomputable example [HasSheafify J' AddCommGrpCat.{w}] :
    r.fineSheafification.Additive :=
  CoverageTopologyRefinement.fineSheafification_additive r

/-- Fixed finite-limit preservation contract. -/
noncomputable example [HasSheafify J' AddCommGrpCat.{w}] :
    PreservesFiniteLimits r.fineSheafification :=
  CoverageTopologyRefinement.fineSheafification_preservesFiniteLimits r

/-- Fixed finite-colimit preservation contract. -/
noncomputable example [HasSheafify J' AddCommGrpCat.{w}] :
    PreservesFiniteColimits r.fineSheafification :=
  CoverageTopologyRefinement.fineSheafification_preservesFiniteColimits r

/-- Fixed constant-sheaf comparison contract. -/
noncomputable example
    [HasSheafify J AddCommGrpCat.{w}]
    [HasSheafify J' AddCommGrpCat.{w}] :
    r.fineSheafification.obj
        ((constantSheaf J AddCommGrpCat.{w}).obj
          (AddCommGrpCat.of (ULift ℤ))) ≅
      (constantSheaf J' AddCommGrpCat.{w}).obj
        (AddCommGrpCat.of (ULift ℤ)) :=
  r.constantSheafIso

/-- Fixed common-coefficient comparison contract. -/
noncomputable example [HasSheafify J' AddCommGrpCat.{w}] :
    r.fineSheafification.obj F.coarse ≅ F.fine :=
  r.commonCoefficientIso F

/-- Fixed concrete Ext topology-change map contract. -/
noncomputable example
    [HasSheafify J AddCommGrpCat.{w}]
    [HasSheafify J' AddCommGrpCat.{w}]
    [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]
    [HasExt.{w'} (Sheaf J' AddCommGrpCat.{w})]
    (n : Nat) :
    F.coarse.H n →+ F.fine.H n :=
  r.sheafHExtMap F n

/-- Fixed public topology-change map contract. -/
noncomputable example
    [HasSheafify J AddCommGrpCat.{w}]
    [HasSheafify J' AddCommGrpCat.{w}]
    [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]
    [HasExt.{w'} (Sheaf J' AddCommGrpCat.{w})]
    (n : Nat) :
    F.coarse.H n →+ F.fine.H n :=
  r.sheafHMap F n

/-- Fixed identification with the concrete Ext composite. -/
example
    [HasSheafify J AddCommGrpCat.{w}]
    [HasSheafify J' AddCommGrpCat.{w}]
    [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]
    [HasExt.{w'} (Sheaf J' AddCommGrpCat.{w})]
    (n : Nat) :
    r.sheafHMap F n = r.sheafHExtMap F n :=
  r.sheafHMap_eq_ext F n

/-- Fixed identity law for topology-change sheaf-cohomology maps. -/
example
    (G : CommonCoefficientSheaf J J)
    [HasSheafify J AddCommGrpCat.{w}]
    [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]
    (n : Nat) :
    (CoverageTopologyRefinement.refl J).sheafHMap G n =
      G.sameTopologyHMap n :=
  CoverageTopologyRefinement.sheafHMap_refl G n

/-- Fixed composition law for topology-change sheaf-cohomology maps. -/
example
    {J₁ J₂ J₃ : GrothendieckTopology C}
    (r₁₂ : CoverageTopologyRefinement J₁ J₂)
    (r₂₃ : CoverageTopologyRefinement J₂ J₃)
    (Q : Cᵒᵖ ⥤ AddCommGrpCat.{w})
    (h₁ : Presheaf.IsSheaf J₁ Q)
    (h₂ : Presheaf.IsSheaf J₂ Q)
    (h₃ : Presheaf.IsSheaf J₃ Q)
    [HasSheafify J₁ AddCommGrpCat.{w}]
    [HasSheafify J₂ AddCommGrpCat.{w}]
    [HasSheafify J₃ AddCommGrpCat.{w}]
    [HasExt.{w'} (Sheaf J₁ AddCommGrpCat.{w})]
    [HasExt.{w'} (Sheaf J₂ AddCommGrpCat.{w})]
    [HasExt.{w'} (Sheaf J₃ AddCommGrpCat.{w})]
    (n : Nat) :
    (r₁₂.comp r₂₃).sheafHMap ⟨Q, h₁, h₃⟩ n =
      (r₂₃.sheafHMap ⟨Q, h₂, h₃⟩ n).comp
        (r₁₂.sheafHMap ⟨Q, h₁, h₂⟩ n) :=
  CoverageTopologyRefinement.sheafHMap_comp r₁₂ r₂₃ Q h₁ h₂ h₃ n

end SheafCohomologyFoundationSD5

namespace LerayComparisonFoundationSD5

open CategoryTheory

variable {A : ArchitectureObject U}
variable {S : Site.AATSite A}
variable (Ob : Cohomology.ObstructionSheaf S)

/-- Fixed derived enough-injectives contract for additive AAT sheaves. -/
noncomputable example
    [HasSheafify S.topology AddCommGrpCat.{u + 1}] :
    EnoughInjectives (Sheaf S.topology AddCommGrpCat.{u + 1}) :=
  Cohomology.standardAddCommGrpSheafEnoughInjectives

/-- Fixed obstruction-sheaf injective-resolution contract. -/
noncomputable example
    [HasSheafify S.topology AddCommGrpCat.{u + 1}] :
    InjectiveResolution Ob.toAddCommGrpSheaf :=
  Cohomology.obstructionInjectiveResolution Ob

/-- Fixed `H'` computation by the obstruction injective resolution. -/
noncomputable example
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 2} (Sheaf S.topology AddCommGrpCat.{u + 1})]
    (X : S.category) (n : Nat) :
    (Ob.toAddCommGrpSheaf).H' n X ≃+
      CochainComplex.HomComplex.CohomologyClass
        ((CochainComplex.singleFunctor
          (Sheaf S.topology AddCommGrpCat.{u + 1}) 0).obj
            ((presheafToSheaf S.topology AddCommGrpCat.{u + 1}).obj
              (yoneda.obj X ⋙ AddCommGrpCat.free)))
        (Cohomology.obstructionInjectiveResolution Ob).cochainComplex n :=
  Cohomology.obstructionHPrimeInjectiveEquiv Ob X n

variable {𝒰 𝒱 : Cohomology.CoverRelativeCechCover S}
variable {K : Cohomology.CoverRelativeCechComplex 𝒰 Ob}
variable {L : Cohomology.CoverRelativeCechComplex 𝒱 Ob}

/-- Fixed actual cochain-complex contract for a cover-relative Čech complex. -/
noncomputable example : CochainComplex AddCommGrpCat.{u} ℕ :=
  K.toCochainComplex

/-- Fixed degreewise cochain-object characterization. -/
example (n : ℕ) :
    (K.toCochainComplex.X n : Type u) = K.AdditiveCochain n :=
  K.toCochainComplex_X n

/-- Fixed differential characterization. -/
example (n : ℕ) :
    letI := K.cochainAddCommGroup n
    letI := K.cochainAddCommGroup (n + 1)
    K.toCochainComplex.d n (n + 1) = AddCommGrpCat.ofHom (K.d n) :=
  K.toCochainComplex_d n

/-- Fixed Mathlib cochain-map contract. -/
noncomputable example
    (f : Cohomology.CoverRelativeCechComplex.Hom K L) :
    K.toCochainComplex ⟶ L.toCochainComplex :=
  f.toCochainMap

/-- Fixed degreewise cochain-map characterization. -/
example (f : Cohomology.CoverRelativeCechComplex.Hom K L) (n : ℕ) :
    (f.toCochainMap.f n).hom = f.app n :=
  f.toCochainMap_f n

/-- Fixed cocycle-to-cycle map contract. -/
noncomputable example (n : ℕ) :
    AddCommGrpCat.of (K.CechCocycleSubgroup n) ⟶
      K.toCochainComplex.cycles n :=
  K.cocycleToCycles n

/-- Fixed underlying-cocycle characterization. -/
example (n : ℕ) (z : K.CechCocycleSubgroup n) :
    (K.toCochainComplex.iCycles n).hom ((K.cocycleToCycles n).hom z) = z.1 :=
  K.cocycleToCycles_i n z

/-- Fixed arbitrary-degree comparison with actual Mathlib homology. -/
noncomputable example (n : ℕ) :
    K.AdditiveCechHn n ≃+ K.toCochainComplex.homology n :=
  K.additiveCechHnEquivHomology n

/-- Fixed representative formula for the actual homology class. -/
example (n : ℕ) (c : K.CechCocycle n) :
    K.additiveCechHnEquivHomology n (K.additiveCohomologyClass n c) =
      (K.toCochainComplex.homologyπ n).hom
        ((K.cocycleToCycles n).hom ⟨c.1, c.2⟩) :=
  K.additiveCechHnEquivHomology_additiveCohomologyClass n c

/-- Fixed naturality against Mathlib's actual homology map. -/
example (f : Cohomology.CoverRelativeCechComplex.Hom K L)
    (n : ℕ) (x : K.AdditiveCechHn n) :
    (HomologicalComplex.homologyMap f.toCochainMap n).hom
        (K.additiveCechHnEquivHomology n x) =
      L.additiveCechHnEquivHomology n (f.mapAdditiveCechHn n x) :=
  f.additiveCechHnEquivHomology_naturality n x

end LerayComparisonFoundationSD5

namespace ActualSelectedCechBridgeSD5

open CategoryTheory

variable {A : ArchitectureObject U}
variable {S : Site.AATSite A} {base : S.category}
variable (Ob : Cohomology.ObstructionSheaf S)
variable (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)

/-- Fixed actual large selected-cochain carrier. -/
example (F : S.categoryᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (n : ℕ) :
    Type (u + 1) :=
  Cohomology.SelectedCechCochain 𝒰 F n

/-- Fixed actual large selected Čech-complex functor. -/
noncomputable example :
    (S.categoryᵒᵖ ⥤ AddCommGrpCat.{u + 1}) ⥤
      CochainComplex AddCommGrpCat.{u + 1} ℕ :=
  Cohomology.selectedCechComplexFunctor 𝒰

/-- Fixed selected-cochain object formula. -/
example (F : S.categoryᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (n : ℕ) :
    (((Cohomology.selectedCechComplexFunctor 𝒰).obj F).X n : Type (u + 1)) =
      Cohomology.SelectedCechCochain 𝒰 F n :=
  Cohomology.selectedCechComplexFunctor_obj_X 𝒰 F n

/-- Fixed alternating-restriction differential formula. -/
example (F : S.categoryᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (n : ℕ)
    (c : Cohomology.SelectedCechCochain 𝒰 F n)
    (σ : (Cohomology.canonicalCoverRelative 𝒰).simplex (n + 1)) :
    (((Cohomology.selectedCechComplexFunctor 𝒰).obj F).d n (n + 1)).hom c σ =
      ∑ i : Fin (n + 2), ((-1 : ℤ) ^ i.1) •
        F.map ((Cohomology.canonicalCoverRelative 𝒰).faceRestriction n i σ).op
          (c ((Cohomology.canonicalCoverRelative 𝒰).face n i σ)) :=
  Cohomology.selectedCechComplexFunctor_obj_d_apply 𝒰 F n c σ

/-- Fixed coefficient-map formula. -/
example {F G : S.categoryᵒᵖ ⥤ AddCommGrpCat.{u + 1}} (η : F ⟶ G)
    (n : ℕ) (c : Cohomology.SelectedCechCochain 𝒰 F n)
    (σ : (Cohomology.canonicalCoverRelative 𝒰).simplex n) :
    (((Cohomology.selectedCechComplexFunctor 𝒰).map η).f n).hom c σ =
      η.app _ (c σ) :=
  Cohomology.selectedCechComplexFunctor_map_f_apply 𝒰 η n c σ

/-- Fixed zero-morphism preservation for the selected Čech functor. -/
example :
    (Cohomology.selectedCechComplexFunctor 𝒰).PreservesZeroMorphisms :=
  Cohomology.selectedCechComplexFunctor_preservesZeroMorphisms 𝒰

variable {𝒰}
variable {𝒱 𝒲 : Site.AATCoverageFamily S.requirements S.overlap base}

/-- Fixed large selected refinement cochain map. -/
noncomputable example (r : Site.AATCoverageFamily.Refinement 𝒰 𝒱) :
    Cohomology.selectedCechComplexFunctor 𝒰 ⟶
      Cohomology.selectedCechComplexFunctor 𝒱 :=
  r.selectedCechMap

/-- Fixed pointwise large selected refinement formula. -/
example (r : Site.AATCoverageFamily.Refinement 𝒰 𝒱)
    (F : S.categoryᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (n : ℕ) (c : Cohomology.SelectedCechCochain 𝒰 F n)
    (σ : (Cohomology.canonicalCoverRelative 𝒱).simplex n) :
    (((r.selectedCechMap).app F).f n).hom c σ =
      F.map (r.overlapMap n σ).op (c (r.simplexMap n σ)) :=
  r.selectedCechMap_app_f_apply F n c σ

/-- Fixed coefficient naturality of the large selected refinement map. -/
example (r : Site.AATCoverageFamily.Refinement 𝒰 𝒱)
    {F G : S.categoryᵒᵖ ⥤ AddCommGrpCat.{u + 1}} (η : F ⟶ G) :
    (Cohomology.selectedCechComplexFunctor 𝒰).map η ≫
        r.selectedCechMap.app G =
      r.selectedCechMap.app F ≫
        (Cohomology.selectedCechComplexFunctor 𝒱).map η :=
  r.selectedCechMap_coefficient_naturality η

/-- Fixed identity law for large selected refinement. -/
example (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base) :
    (Site.AATCoverageFamily.Refinement.refl 𝒰).selectedCechMap = 𝟙 _ :=
  Site.AATCoverageFamily.Refinement.selectedCechMap_refl 𝒰

/-- Fixed composition law for large selected refinement. -/
example (r : Site.AATCoverageFamily.Refinement 𝒰 𝒱)
    (s : Site.AATCoverageFamily.Refinement 𝒱 𝒲) :
    (r.comp s).selectedCechMap = r.selectedCechMap ≫ s.selectedCechMap :=
  r.selectedCechMap_comp s

/-- Fixed objectwise universe lift into the actual additive sheaf. -/
noncomputable example (X : S.category) :
    Ob.carrier.toPresheaf.obj (Opposite.op X) ≃+
      Ob.toAddCommGrpSheaf.val.obj (Opposite.op X) :=
  Ob.toAddCommGrpSheafObjAddEquiv X

/-- Fixed restriction naturality of the objectwise universe lift. -/
example {X Y : S.category} (f : X ⟶ Y)
    (x : Ob.carrier.toPresheaf.obj (Opposite.op Y)) :
    Ob.toAddCommGrpSheafObjAddEquiv X (Ob.mapAddMonoidHom f x) =
      Ob.toAddCommGrpSheaf.val.map f.op
        (Ob.toAddCommGrpSheafObjAddEquiv Y x) :=
  Ob.toAddCommGrpSheafObjAddEquiv_naturality f x

/-- Fixed lifted R5c2 complex. -/
noncomputable example (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base) :
    CochainComplex AddCommGrpCat.{u + 1} ℕ :=
  Cohomology.liftedCanonicalCechComplex 𝒰 Ob

/-- Fixed complex isomorphism to the actual selected complex. -/
noncomputable example
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base) :
    Cohomology.liftedCanonicalCechComplex 𝒰 Ob ≅
      (Cohomology.selectedCechComplexFunctor 𝒰).obj
        Ob.toAddCommGrpSheaf.val :=
  Cohomology.obstructionSelectedCechComplexIso 𝒰 Ob

/-- Fixed degreewise formula for the complex isomorphism. -/
example (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (n : ℕ) (c : (Cohomology.liftedCanonicalCechComplex 𝒰 Ob).X n)
    (σ : (Cohomology.canonicalCoverRelative 𝒰).simplex n) :
    ((Cohomology.obstructionSelectedCechComplexIso 𝒰 Ob).hom.f n).hom c σ =
      Ob.toAddCommGrpSheafObjAddEquiv _ (c.down σ) :=
  Cohomology.obstructionSelectedCechComplexIso_hom_f_apply 𝒰 Ob n c σ

/-- Fixed lifted refinement cochain map. -/
noncomputable example (r : Site.AATCoverageFamily.Refinement 𝒰 𝒱) :
    Cohomology.liftedCanonicalCechComplex 𝒰 Ob ⟶
      Cohomology.liftedCanonicalCechComplex 𝒱 Ob :=
  Cohomology.liftedCanonicalCechMap r Ob

/-- Fixed refinement naturality of the complex isomorphism. -/
example (r : Site.AATCoverageFamily.Refinement 𝒰 𝒱) :
    Cohomology.liftedCanonicalCechMap r Ob ≫
        (Cohomology.obstructionSelectedCechComplexIso 𝒱 Ob).hom =
      (Cohomology.obstructionSelectedCechComplexIso 𝒰 Ob).hom ≫
        r.selectedCechMap.app Ob.toAddCommGrpSheaf.val :=
  Cohomology.obstructionSelectedCechComplexIso_refinement_naturality r Ob

/-- Fixed homology preservation under the universe lift. -/
noncomputable example (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (n : ℕ) :
    (Cohomology.liftedCanonicalCechComplex 𝒰 Ob).homology n ≅
      AddCommGrpCat.uliftFunctor.{u + 1, u}.obj
        ((Cohomology.canonicalCechComplex 𝒰 Ob).toCochainComplex.homology n) :=
  Cohomology.liftedCanonicalCechHomologyIso 𝒰 Ob n

/-- Fixed refinement naturality of lifted homology. -/
example (r : Site.AATCoverageFamily.Refinement 𝒰 𝒱) (n : ℕ) :
    AddCommGrpCat.uliftFunctor.{u + 1, u}.map
          (HomologicalComplex.homologyMap
            (r.canonicalCechHom Ob).toCochainMap n) ≫
        (Cohomology.liftedCanonicalCechHomologyIso 𝒱 Ob n).inv =
      (Cohomology.liftedCanonicalCechHomologyIso 𝒰 Ob n).inv ≫
        HomologicalComplex.homologyMap
          (Cohomology.liftedCanonicalCechMap r Ob) n :=
  Cohomology.liftedCanonicalCechHomologyIso_inv_refinement_naturality r Ob n

/-- Fixed lifted-cocycle map into actual selected cycles. -/
noncomputable example
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base) (n : ℕ) :
    AddCommGrpCat.uliftFunctor.{u + 1, u}.obj
        (AddCommGrpCat.of
          ((Cohomology.canonicalCechComplex 𝒰 Ob).CechCocycleSubgroup n)) ⟶
      ((Cohomology.selectedCechComplexFunctor 𝒰).obj
        Ob.toAddCommGrpSheaf.val).cycles n :=
  Cohomology.obstructionCocycleToSelectedCycles 𝒰 Ob n

/-- Fixed underlying-cochain formula for the actual selected cycle. -/
example (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (n : ℕ) (z : (Cohomology.canonicalCechComplex 𝒰 Ob).CechCocycleSubgroup n)
    (σ : (Cohomology.canonicalCoverRelative 𝒰).simplex n) :
    (((Cohomology.selectedCechComplexFunctor 𝒰).obj
        Ob.toAddCommGrpSheaf.val).iCycles n).hom
        ((Cohomology.obstructionCocycleToSelectedCycles 𝒰 Ob n).hom
          (ULift.up z)) σ =
      Ob.toAddCommGrpSheafObjAddEquiv _ (z.1 σ) :=
  Cohomology.obstructionCocycleToSelectedCycles_i_apply 𝒰 Ob n z σ

/-- Fixed compatibility of the lifted homology isomorphism with `homologyπ`. -/
example (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base) (n : ℕ) :
    AddCommGrpCat.uliftFunctor.{u + 1, u}.map
          ((Cohomology.canonicalCechComplex 𝒰 Ob).toCochainComplex.homologyπ n) ≫
        (Cohomology.liftedCanonicalCechHomologyIso 𝒰 Ob n).inv =
      (((Cohomology.canonicalCechComplex 𝒰 Ob).toCochainComplex.sc n).mapCyclesIso
          AddCommGrpCat.uliftFunctor.{u + 1, u}).inv ≫
        (Cohomology.liftedCanonicalCechComplex 𝒰 Ob).homologyπ n :=
  Cohomology.liftedCanonicalCechHomologyIso_inv_homologyπ 𝒰 Ob n

/-- Fixed equivalence from the custom quotient to actual selected homology. -/
noncomputable example
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base) (n : ℕ) :
    (Cohomology.canonicalCechComplex 𝒰 Ob).AdditiveCechHn n ≃+
      ((Cohomology.selectedCechComplexFunctor 𝒰).obj
        Ob.toAddCommGrpSheaf.val).homology n :=
  Cohomology.additiveCechHnEquivSelectedHomology 𝒰 Ob n

/-- Fixed canonical additive map to actual selected homology. -/
noncomputable example
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base) (n : ℕ) :
    (Cohomology.canonicalCechComplex 𝒰 Ob).AdditiveCechHn n →+
      ((Cohomology.selectedCechComplexFunctor 𝒰).obj
        Ob.toAddCommGrpSheaf.val).homology n :=
  Cohomology.additiveCechHnToSelectedHomology 𝒰 Ob n

/-- Fixed arbitrary-degree bijectivity of the canonical additive map. -/
example (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base) (n : ℕ) :
    Function.Bijective
      (Cohomology.additiveCechHnToSelectedHomology 𝒰 Ob n) :=
  Cohomology.additiveCechHnToSelectedHomology_bijective 𝒰 Ob n

/-- Fixed representative formula in actual selected homology. -/
example (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (n : ℕ) (c : (Cohomology.canonicalCechComplex 𝒰 Ob).CechCocycle n) :
    Cohomology.additiveCechHnEquivSelectedHomology 𝒰 Ob n
        ((Cohomology.canonicalCechComplex 𝒰 Ob).additiveCohomologyClass n c) =
      (HomologicalComplex.homologyMapIso
          (Cohomology.obstructionSelectedCechComplexIso 𝒰 Ob) n).hom.hom
        ((Cohomology.liftedCanonicalCechHomologyIso 𝒰 Ob n).inv.hom
          (ULift.up
            (((Cohomology.canonicalCechComplex 𝒰 Ob).toCochainComplex.homologyπ n).hom
              (((Cohomology.canonicalCechComplex 𝒰 Ob).cocycleToCycles n).hom
                ⟨c.1, c.2⟩)))) :=
  Cohomology.additiveCechHnEquivSelectedHomology_additiveCohomologyClass
    𝒰 Ob n c

/-- Fixed representative formula for the canonical additive map. -/
example (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (n : ℕ) (c : (Cohomology.canonicalCechComplex 𝒰 Ob).CechCocycle n) :
    Cohomology.additiveCechHnToSelectedHomology 𝒰 Ob n
        ((Cohomology.canonicalCechComplex 𝒰 Ob).additiveCohomologyClass n c) =
      (HomologicalComplex.homologyMapIso
          (Cohomology.obstructionSelectedCechComplexIso 𝒰 Ob) n).hom.hom
        ((Cohomology.liftedCanonicalCechHomologyIso 𝒰 Ob n).inv.hom
          (ULift.up
            (((Cohomology.canonicalCechComplex 𝒰 Ob).toCochainComplex.homologyπ n).hom
              (((Cohomology.canonicalCechComplex 𝒰 Ob).cocycleToCycles n).hom
                ⟨c.1, c.2⟩)))) :=
  Cohomology.additiveCechHnToSelectedHomology_additiveCohomologyClass
    𝒰 Ob n c

/-- Fixed direct `homologyπ` representative formula in the actual selected complex. -/
example (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (n : ℕ) (c : (Cohomology.canonicalCechComplex 𝒰 Ob).CechCocycle n) :
    Cohomology.additiveCechHnToSelectedHomology 𝒰 Ob n
        ((Cohomology.canonicalCechComplex 𝒰 Ob).additiveCohomologyClass n c) =
      (((Cohomology.selectedCechComplexFunctor 𝒰).obj
          Ob.toAddCommGrpSheaf.val).homologyπ n).hom
        ((Cohomology.obstructionCocycleToSelectedCycles 𝒰 Ob n).hom
          (ULift.up ⟨c.1, c.2⟩)) :=
  Cohomology.additiveCechHnToSelectedHomology_additiveCohomologyClass_eq_homologyπ
    𝒰 Ob n c

/-- Fixed refinement naturality in actual selected homology. -/
example (r : Site.AATCoverageFamily.Refinement 𝒰 𝒱) (n : ℕ)
    (x : (Cohomology.canonicalCechComplex 𝒰 Ob).AdditiveCechHn n) :
    (HomologicalComplex.homologyMap
        (r.selectedCechMap.app Ob.toAddCommGrpSheaf.val) n).hom
        (Cohomology.additiveCechHnEquivSelectedHomology 𝒰 Ob n x) =
      Cohomology.additiveCechHnEquivSelectedHomology 𝒱 Ob n
        ((r.canonicalCechHom Ob).mapAdditiveCechHn n x) :=
  Cohomology.additiveCechHnEquivSelectedHomology_refinement_naturality
    r Ob n x

/-- Fixed refinement naturality of the canonical additive map. -/
example (r : Site.AATCoverageFamily.Refinement 𝒰 𝒱) (n : ℕ)
    (x : (Cohomology.canonicalCechComplex 𝒰 Ob).AdditiveCechHn n) :
    (HomologicalComplex.homologyMap
        (r.selectedCechMap.app Ob.toAddCommGrpSheaf.val) n).hom
        (Cohomology.additiveCechHnToSelectedHomology 𝒰 Ob n x) =
      Cohomology.additiveCechHnToSelectedHomology 𝒱 Ob n
        ((r.canonicalCechHom Ob).mapAdditiveCechHn n x) :=
  Cohomology.additiveCechHnToSelectedHomology_refinement_naturality
    r Ob n x

end ActualSelectedCechBridgeSD5

namespace SelectedCechResolutionBicomplexSD5

open CategoryTheory

variable {A : ArchitectureObject U}
variable {S : Site.AATSite A} {base : S.category}
variable (Ob : Cohomology.ObstructionSheaf S)
variable (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
variable [HasSheafify S.topology AddCommGrpCat.{u + 1}]

/-- Fixed first-quadrant selected Čech injective-resolution bicomplex. -/
noncomputable example :
    HomologicalComplex₂ AddCommGrpCat.{u + 1}
      (ComplexShape.up ℕ) (ComplexShape.up ℕ) :=
  Cohomology.selectedCechResolutionBicomplex 𝒰 Ob

/-- Fixed object formula in each bidegree. -/
example (q p : ℕ) :
    (((Cohomology.selectedCechResolutionBicomplex 𝒰 Ob).X q).X p :
        Type (u + 1)) =
      Cohomology.SelectedCechCochain 𝒰
        ((Cohomology.obstructionInjectiveResolution Ob).cocomplex.X q).val p :=
  Cohomology.selectedCechResolutionBicomplex_obj 𝒰 Ob q p

/-- Fixed selected Čech differential formula. -/
example (q p : ℕ)
    (c : Cohomology.SelectedCechCochain 𝒰
      ((Cohomology.obstructionInjectiveResolution Ob).cocomplex.X q).val p)
    (σ : (Cohomology.canonicalCoverRelative 𝒰).simplex (p + 1)) :
    (((Cohomology.selectedCechResolutionBicomplex 𝒰 Ob).X q).d
        p (p + 1)).hom c σ =
      ∑ i : Fin (p + 2), ((-1 : ℤ) ^ i.1) •
        ((Cohomology.obstructionInjectiveResolution Ob).cocomplex.X q).val.map
          ((Cohomology.canonicalCoverRelative 𝒰).faceRestriction p i σ).op
          (c ((Cohomology.canonicalCoverRelative 𝒰).face p i σ)) :=
  Cohomology.selectedCechResolutionBicomplex_cech_d_apply 𝒰 Ob q p c σ

/-- Fixed resolution differential formula. -/
example (q p : ℕ)
    (c : Cohomology.SelectedCechCochain 𝒰
      ((Cohomology.obstructionInjectiveResolution Ob).cocomplex.X q).val p)
    (σ : (Cohomology.canonicalCoverRelative 𝒰).simplex p) :
    (((Cohomology.selectedCechResolutionBicomplex 𝒰 Ob).d
        q (q + 1)).f p).hom c σ =
      ((Cohomology.obstructionInjectiveResolution Ob).cocomplex.d
        q (q + 1)).val.app _ (c σ) :=
  Cohomology.selectedCechResolutionBicomplex_resolution_d_apply 𝒰 Ob q p c σ

/-- Fixed commutation of the two bicomplex differentials. -/
example (q q' p p' : ℕ) :
    ((Cohomology.selectedCechResolutionBicomplex 𝒰 Ob).d q q').f p ≫
        ((Cohomology.selectedCechResolutionBicomplex 𝒰 Ob).X q').d p p' =
      ((Cohomology.selectedCechResolutionBicomplex 𝒰 Ob).X q).d p p' ≫
        ((Cohomology.selectedCechResolutionBicomplex 𝒰 Ob).d q q').f p' :=
  Cohomology.selectedCechResolutionBicomplex_d_comm 𝒰 Ob q q' p p'

/-- Fixed resolution-unit augmentation. -/
noncomputable example :
    (Cohomology.selectedCechComplexFunctor 𝒰).obj
        Ob.toAddCommGrpSheaf.val ⟶
      (Cohomology.selectedCechResolutionBicomplex 𝒰 Ob).X 0 :=
  Cohomology.selectedCechResolutionAugmentation 𝒰 Ob

/-- Fixed pointwise resolution-unit formula. -/
example (p : ℕ)
    (c : Cohomology.SelectedCechCochain 𝒰 Ob.toAddCommGrpSheaf.val p)
    (σ : (Cohomology.canonicalCoverRelative 𝒰).simplex p) :
    ((Cohomology.selectedCechResolutionAugmentation 𝒰 Ob).f p).hom c σ =
      ((Cohomology.obstructionInjectiveResolution Ob).ι.f 0).val.app _ (c σ) :=
  Cohomology.selectedCechResolutionAugmentation_f_apply 𝒰 Ob p c σ

/-- Fixed natural transformation from base sections to selected degree zero. -/
noncomputable example :
    (evaluation S.categoryᵒᵖ AddCommGrpCat.{u + 1}).obj
        (Opposite.op base) ⟶
      Cohomology.selectedCechComplexFunctor 𝒰 ⋙
        HomologicalComplex.eval AddCommGrpCat.{u + 1}
          (ComplexShape.up ℕ) 0 :=
  Cohomology.baseToSelectedCechZero 𝒰

/-- Fixed chart-restriction formula for selected degree zero. -/
example (F : S.categoryᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (x : F.obj (Opposite.op base))
    (σ : (Cohomology.canonicalCoverRelative 𝒰).simplex 0) :
    ((Cohomology.baseToSelectedCechZero 𝒰).app F).hom x σ =
      F.map ((Cohomology.canonicalCoverRelative 𝒰).inclusion (σ 0)).op x :=
  Cohomology.baseToSelectedCechZero_app_apply 𝒰 F x σ

/-- Fixed injective-resolution complex evaluated at the base. -/
noncomputable example : CochainComplex AddCommGrpCat.{u + 1} ℕ :=
  Cohomology.baseResolutionComplex (base := base) Ob

/-- Fixed object formula for the base-resolution complex. -/
example (q : ℕ) :
    ((Cohomology.baseResolutionComplex (base := base) Ob).X q :
        Type (u + 1)) =
      ((Cohomology.obstructionInjectiveResolution Ob).cocomplex.X q).val.obj
        (Opposite.op base) :=
  Cohomology.baseResolutionComplex_X Ob q

/-- Fixed differential formula for the base-resolution complex. -/
example (q : ℕ)
    (x : ((Cohomology.obstructionInjectiveResolution Ob).cocomplex.X q).val.obj
      (Opposite.op base)) :
    ((Cohomology.baseResolutionComplex (base := base) Ob).d
        q (q + 1)).hom x =
      ((Cohomology.obstructionInjectiveResolution Ob).cocomplex.d
        q (q + 1)).val.app _ x :=
  Cohomology.baseResolutionComplex_d_apply Ob q x

/-- Fixed additive Yoneda bridge from sheafified free representables to sections. -/
noncomputable example (X : S.category)
    (F : Sheaf S.topology AddCommGrpCat.{u + 1}) :
    (((presheafToSheaf S.topology AddCommGrpCat.{u + 1}).obj
      (yoneda.obj X ⋙ AddCommGrpCat.free) ⟶ F) : Type (u + 1)) ≃+
      (F.val.obj (Opposite.op X) : Type (u + 1)) :=
  Cohomology.sheafifiedFreeYonedaHomAddEquiv X F

/-- Fixed postcomposition law for the additive Yoneda bridge. -/
example (X : S.category)
    {F G : Sheaf S.topology AddCommGrpCat.{u + 1}}
    (f : ((presheafToSheaf S.topology AddCommGrpCat.{u + 1}).obj
      (yoneda.obj X ⋙ AddCommGrpCat.free)) ⟶ F)
    (g : F ⟶ G) :
    Cohomology.sheafifiedFreeYonedaHomAddEquiv X G (f ≫ g) =
      g.val.app (Opposite.op X)
        (Cohomology.sheafifiedFreeYonedaHomAddEquiv X F f) :=
  Cohomology.sheafifiedFreeYonedaHomAddEquiv_comp X f g

/-- Fixed source-object naturality law for the additive Yoneda bridge. -/
example {X Y : S.category}
    (a : X ⟶ Y)
    (F : Sheaf S.topology AddCommGrpCat.{u + 1})
    (f : ((presheafToSheaf S.topology AddCommGrpCat.{u + 1}).obj
      (yoneda.obj Y ⋙ AddCommGrpCat.free)) ⟶ F) :
    Cohomology.sheafifiedFreeYonedaHomAddEquiv X F
        ((presheafToSheaf S.topology AddCommGrpCat.{u + 1}).map
          (Functor.whiskerRight (yoneda.map a) AddCommGrpCat.free) ≫ f) =
      F.val.map a.op
        (Cohomology.sheafifiedFreeYonedaHomAddEquiv Y F f) :=
  Cohomology.sheafifiedFreeYonedaHomAddEquiv_precomp a F f

/-- Fixed universe lift of the base-resolution complex. -/
noncomputable example : CochainComplex AddCommGrpCat.{u + 2} ℕ :=
  Cohomology.liftedBaseResolutionComplex (base := base) Ob

/-- Fixed object formula for the universe-lifted base-resolution complex. -/
example (q : ℕ) :
    ((Cohomology.liftedBaseResolutionComplex (base := base) Ob).X q :
        Type (u + 2)) =
      ULift.{u + 2, u + 1}
        (((Cohomology.obstructionInjectiveResolution Ob).cocomplex.X q).val.obj
          (Opposite.op base)) :=
  Cohomology.liftedBaseResolutionComplex_X Ob q

/-- Fixed differential formula for the universe-lifted base-resolution complex. -/
example (q : ℕ)
    (x : ULift.{u + 2, u + 1}
      (((Cohomology.obstructionInjectiveResolution Ob).cocomplex.X q).val.obj
        (Opposite.op base))) :
    ((Cohomology.liftedBaseResolutionComplex (base := base) Ob).d
        q (q + 1)).hom x =
      ULift.up
        (((Cohomology.obstructionInjectiveResolution Ob).cocomplex.d
          q (q + 1)).val.app _ x.down) :=
  Cohomology.liftedBaseResolutionComplex_d_apply Ob q x

/-- Fixed cycle morphism from the free representable into the injective resolution. -/
noncomputable example (n : ℕ)
    (z : (Cohomology.liftedBaseResolutionComplex (base := base) Ob).cycles n) :
    ((presheafToSheaf S.topology AddCommGrpCat.{u + 1}).obj
      (yoneda.obj base ⋙ AddCommGrpCat.free)) ⟶
        (Cohomology.obstructionInjectiveResolution Ob).cocomplex.X n :=
  Cohomology.baseResolutionLiftedCycleMorphism Ob n z

/-- Fixed section formula for a lifted base-resolution cycle morphism. -/
example (n : ℕ)
    (z : (Cohomology.liftedBaseResolutionComplex (base := base) Ob).cycles n) :
    Cohomology.sheafifiedFreeYonedaHomAddEquiv base
        ((Cohomology.obstructionInjectiveResolution Ob).cocomplex.X n)
        (Cohomology.baseResolutionLiftedCycleMorphism Ob n z) =
      (((Cohomology.liftedBaseResolutionComplex
        (base := base) Ob).iCycles n).hom z).down :=
  Cohomology.baseResolutionLiftedCycleMorphism_section Ob n z

/-- Fixed cocycle equation for the base-resolution cycle morphism. -/
example (n : ℕ)
    (z : (Cohomology.liftedBaseResolutionComplex (base := base) Ob).cycles n) :
    Cohomology.baseResolutionLiftedCycleMorphism Ob n z ≫
        (Cohomology.obstructionInjectiveResolution Ob).cocomplex.d n (n + 1) = 0 :=
  Cohomology.baseResolutionLiftedCycleMorphism_comp_d Ob n z

section BaseResolutionHPrimeBridge

variable [HasExt.{u + 2} (Sheaf S.topology AddCommGrpCat.{u + 1})]

/-- Fixed cycle map into actual `Sheaf.H'`. -/
noncomputable example (n : ℕ) :
    (Cohomology.liftedBaseResolutionComplex (base := base) Ob).cycles n ⟶
      (Ob.toAddCommGrpSheaf).H' n base :=
  Cohomology.baseResolutionLiftedCyclesToHPrime Ob n

/-- Fixed representative formula using Mathlib's Ext cocycle constructor. -/
example (n : ℕ)
    (z : (Cohomology.liftedBaseResolutionComplex (base := base) Ob).cycles n) :
    (Cohomology.baseResolutionLiftedCyclesToHPrime Ob n).hom z =
      (Cohomology.obstructionInjectiveResolution Ob).extMk
        (Cohomology.baseResolutionLiftedCycleMorphism Ob n z) (n + 1) rfl
        (Cohomology.baseResolutionLiftedCycleMorphism_comp_d Ob n z) :=
  Cohomology.baseResolutionLiftedCyclesToHPrime_apply Ob n z

/-- Fixed homology isomorphism for the structural universe lift. -/
noncomputable example (n : ℕ) :
    (Cohomology.liftedBaseResolutionComplex (base := base) Ob).homology n ≅
      AddCommGrpCat.uliftFunctor.{u + 2, u + 1}.obj
        ((Cohomology.baseResolutionComplex (base := base) Ob).homology n) :=
  Cohomology.liftedBaseResolutionHomologyIso Ob n

/-- Fixed canonical equivalence from base-resolution homology to actual `Sheaf.H'`. -/
noncomputable example (n : ℕ) :
    ((Cohomology.baseResolutionComplex (base := base) Ob).homology n :
        Type (u + 1)) ≃+
      ((Ob.toAddCommGrpSheaf).H' n base : Type (u + 2)) :=
  Cohomology.baseResolutionHomologyEquivHPrime Ob n

/-- Fixed representative formula for the base-resolution homology comparison. -/
example (n : ℕ)
    (z : (Cohomology.baseResolutionComplex (base := base) Ob).cycles n) :
    Cohomology.baseResolutionHomologyEquivHPrime Ob n
        (((Cohomology.baseResolutionComplex (base := base) Ob).homologyπ n).hom z) =
      (Cohomology.baseResolutionLiftedCyclesToHPrime Ob n).hom
        (((((Cohomology.baseResolutionComplex (base := base) Ob).sc n).mapCyclesIso
          AddCommGrpCat.uliftFunctor.{u + 2, u + 1}).inv).hom (ULift.up z)) :=
  Cohomology.baseResolutionHomologyEquivHPrime_homologyπ Ob n z

end BaseResolutionHPrimeBridge

/-- Fixed map from the base resolution to the selected degree-zero column. -/
noncomputable example :
    Cohomology.baseResolutionComplex (base := base) Ob ⟶
      (Cohomology.selectedCechResolutionBicomplex 𝒰 Ob).flip.X 0 :=
  Cohomology.baseResolutionToSelectedCechZero 𝒰 Ob

/-- Fixed pointwise base-edge formula. -/
example (q : ℕ)
    (x : ((Cohomology.obstructionInjectiveResolution Ob).cocomplex.X q).val.obj
      (Opposite.op base))
    (σ : (Cohomology.canonicalCoverRelative 𝒰).simplex 0) :
    ((Cohomology.baseResolutionToSelectedCechZero 𝒰 Ob).f q).hom x σ =
      ((Cohomology.obstructionInjectiveResolution Ob).cocomplex.X q).val.map
        ((Cohomology.canonicalCoverRelative 𝒰).inclusion (σ 0)).op x :=
  Cohomology.baseResolutionToSelectedCechZero_f_apply 𝒰 Ob q x σ

variable {𝒰}
variable {𝒱 𝒲 : Site.AATCoverageFamily S.requirements S.overlap base}

/-- Fixed bicomplex map induced by selected-cover refinement. -/
noncomputable example (r : Site.AATCoverageFamily.Refinement 𝒰 𝒱) :
    Cohomology.selectedCechResolutionBicomplex 𝒰 Ob ⟶
      Cohomology.selectedCechResolutionBicomplex 𝒱 Ob :=
  Cohomology.selectedCechResolutionBicomplexMap r Ob

/-- Fixed pointwise formula for the refinement bicomplex map. -/
example (r : Site.AATCoverageFamily.Refinement 𝒰 𝒱) (q p : ℕ)
    (c : Cohomology.SelectedCechCochain 𝒰
      ((Cohomology.obstructionInjectiveResolution Ob).cocomplex.X q).val p)
    (σ : (Cohomology.canonicalCoverRelative 𝒱).simplex p) :
    ((((Cohomology.selectedCechResolutionBicomplexMap r Ob).f q).f p).hom c) σ =
      ((Cohomology.obstructionInjectiveResolution Ob).cocomplex.X q).val.map
        (r.overlapMap p σ).op (c (r.simplexMap p σ)) :=
  Cohomology.selectedCechResolutionBicomplexMap_f_f_apply r Ob q p c σ

/-- Fixed identity law for refinement bicomplex maps. -/
example (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base) :
    Cohomology.selectedCechResolutionBicomplexMap
        (Site.AATCoverageFamily.Refinement.refl 𝒰) Ob =
      𝟙 (Cohomology.selectedCechResolutionBicomplex 𝒰 Ob) :=
  Cohomology.selectedCechResolutionBicomplexMap_refl 𝒰 Ob

/-- Fixed composition law for refinement bicomplex maps. -/
example (r : Site.AATCoverageFamily.Refinement 𝒰 𝒱)
    (s : Site.AATCoverageFamily.Refinement 𝒱 𝒲) :
    Cohomology.selectedCechResolutionBicomplexMap (r.comp s) Ob =
      Cohomology.selectedCechResolutionBicomplexMap r Ob ≫
        Cohomology.selectedCechResolutionBicomplexMap s Ob :=
  Cohomology.selectedCechResolutionBicomplexMap_comp r s Ob

/-- Fixed refinement naturality of the resolution augmentation. -/
example (r : Site.AATCoverageFamily.Refinement 𝒰 𝒱) :
    Cohomology.selectedCechResolutionAugmentation 𝒰 Ob ≫
        (Cohomology.selectedCechResolutionBicomplexMap r Ob).f 0 =
      r.selectedCechMap.app Ob.toAddCommGrpSheaf.val ≫
        Cohomology.selectedCechResolutionAugmentation 𝒱 Ob :=
  Cohomology.selectedCechResolutionAugmentation_refinement_naturality r Ob

/-- Fixed refinement naturality of the base-resolution edge. -/
example (r : Site.AATCoverageFamily.Refinement 𝒰 𝒱) :
    Cohomology.baseResolutionToSelectedCechZero 𝒰 Ob ≫
        ((HomologicalComplex₂.flipFunctor AddCommGrpCat.{u + 1}
          (ComplexShape.up ℕ) (ComplexShape.up ℕ)).map
            (Cohomology.selectedCechResolutionBicomplexMap r Ob)).f 0 =
      Cohomology.baseResolutionToSelectedCechZero 𝒱 Ob :=
  Cohomology.baseResolutionToSelectedCechZero_refinement_naturality r Ob

/-! Part 4 R5c6: actual total complex, canonical edges, and refinement. -/

/-- Fixed vanishing of the augmentation followed by the resolution differential. -/
example (p : ℕ) :
    (Cohomology.selectedCechResolutionAugmentation 𝒰 Ob).f p ≫
        ((Cohomology.selectedCechResolutionBicomplex 𝒰 Ob).d 0 1).f p = 0 :=
  Cohomology.selectedCechResolutionAugmentation_comp_resolution_d 𝒰 Ob p

/-- Fixed zero-cocycle equation for base restriction. -/
example (q : ℕ) :
    (Cohomology.baseResolutionToSelectedCechZero 𝒰 Ob).f q ≫
        ((Cohomology.selectedCechResolutionBicomplex 𝒰 Ob).X q).d 0 1 = 0 :=
  Cohomology.baseResolutionToSelectedCechZero_comp_cech_d 𝒰 Ob q

/-- Fixed actual total complex. -/
noncomputable example : CochainComplex AddCommGrpCat.{u + 1} ℕ :=
  Cohomology.selectedCechResolutionTotalComplex 𝒰 Ob

/-- Fixed signed total differential formula on every summand. -/
example (q p n n' : ℕ) (h : q + p = n) :
    (Cohomology.selectedCechResolutionBicomplex 𝒰 Ob).ιTotal
          (ComplexShape.up ℕ) q p n h ≫
        (Cohomology.selectedCechResolutionTotalComplex 𝒰 Ob).d n n' =
      (Cohomology.selectedCechResolutionBicomplex 𝒰 Ob).d₁
          (ComplexShape.up ℕ) q p n' +
        (Cohomology.selectedCechResolutionBicomplex 𝒰 Ob).d₂
          (ComplexShape.up ℕ) q p n' :=
  Cohomology.selectedCechResolutionTotalComplex_ι_d 𝒰 Ob q p n n' h

/-- Fixed selected Čech edge into the total complex. -/
noncomputable example :
    (Cohomology.selectedCechComplexFunctor 𝒰).obj
        Ob.toAddCommGrpSheaf.val ⟶
      Cohomology.selectedCechResolutionTotalComplex 𝒰 Ob :=
  Cohomology.selectedCechToResolutionTotal 𝒰 Ob

/-- Fixed component formula for the selected Čech edge. -/
example (p : ℕ) :
    (Cohomology.selectedCechToResolutionTotal 𝒰 Ob).f p =
      (Cohomology.selectedCechResolutionAugmentation 𝒰 Ob).f p ≫
        (Cohomology.selectedCechResolutionBicomplex 𝒰 Ob).ιTotal
          (ComplexShape.up ℕ) 0 p p (by simp) :=
  Cohomology.selectedCechToResolutionTotal_f 𝒰 Ob p

/-- Fixed base-resolution edge into the total complex. -/
noncomputable example :
    Cohomology.baseResolutionComplex (base := base) Ob ⟶
      Cohomology.selectedCechResolutionTotalComplex 𝒰 Ob :=
  Cohomology.baseResolutionToSelectedCechTotal 𝒰 Ob

/-- Fixed component formula for the base-resolution edge. -/
example (q : ℕ) :
    (Cohomology.baseResolutionToSelectedCechTotal 𝒰 Ob).f q =
      (Cohomology.baseResolutionToSelectedCechZero 𝒰 Ob).f q ≫
        (Cohomology.selectedCechResolutionBicomplex 𝒰 Ob).ιTotal
          (ComplexShape.up ℕ) q 0 q (by simp) :=
  Cohomology.baseResolutionToSelectedCechTotal_f 𝒰 Ob q

/-- Fixed total map induced by refinement. -/
noncomputable example (r : Site.AATCoverageFamily.Refinement 𝒰 𝒱) :
    Cohomology.selectedCechResolutionTotalComplex 𝒰 Ob ⟶
      Cohomology.selectedCechResolutionTotalComplex 𝒱 Ob :=
  Cohomology.selectedCechResolutionTotalMap r Ob

/-- Fixed summand formula for the total refinement map. -/
example (r : Site.AATCoverageFamily.Refinement 𝒰 𝒱)
    (q p n : ℕ) (h : q + p = n) :
    (Cohomology.selectedCechResolutionBicomplex 𝒰 Ob).ιTotal
          (ComplexShape.up ℕ) q p n h ≫
        (Cohomology.selectedCechResolutionTotalMap r Ob).f n =
      ((Cohomology.selectedCechResolutionBicomplexMap r Ob).f q).f p ≫
        (Cohomology.selectedCechResolutionBicomplex 𝒱 Ob).ιTotal
          (ComplexShape.up ℕ) q p n h :=
  Cohomology.selectedCechResolutionTotalMap_ιTotal r Ob q p n h

/-- Fixed identity law for total refinement maps. -/
example (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base) :
    Cohomology.selectedCechResolutionTotalMap
        (Site.AATCoverageFamily.Refinement.refl 𝒰) Ob =
      𝟙 (Cohomology.selectedCechResolutionTotalComplex 𝒰 Ob) :=
  Cohomology.selectedCechResolutionTotalMap_refl 𝒰 Ob

/-- Fixed composition law for total refinement maps. -/
example (r : Site.AATCoverageFamily.Refinement 𝒰 𝒱)
    (s : Site.AATCoverageFamily.Refinement 𝒱 𝒲) :
    Cohomology.selectedCechResolutionTotalMap (r.comp s) Ob =
      Cohomology.selectedCechResolutionTotalMap r Ob ≫
        Cohomology.selectedCechResolutionTotalMap s Ob :=
  Cohomology.selectedCechResolutionTotalMap_comp r s Ob

/-- Fixed refinement naturality for the selected Čech edge. -/
example (r : Site.AATCoverageFamily.Refinement 𝒰 𝒱) :
    Cohomology.selectedCechToResolutionTotal 𝒰 Ob ≫
        Cohomology.selectedCechResolutionTotalMap r Ob =
      r.selectedCechMap.app Ob.toAddCommGrpSheaf.val ≫
        Cohomology.selectedCechToResolutionTotal 𝒱 Ob :=
  Cohomology.selectedCechToResolutionTotal_refinement_naturality r Ob

/-- Fixed refinement naturality for the base-resolution edge. -/
example (r : Site.AATCoverageFamily.Refinement 𝒰 𝒱) :
    Cohomology.baseResolutionToSelectedCechTotal 𝒰 Ob ≫
        Cohomology.selectedCechResolutionTotalMap r Ob =
      Cohomology.baseResolutionToSelectedCechTotal 𝒱 Ob :=
  Cohomology.baseResolutionToSelectedCechTotal_refinement_naturality r Ob

/-! Part 4 R5c7: Leray vanishing and actual resolution columns. -/

section LerayColumns

variable [HasExt.{u + 2} (Sheaf S.topology AddCommGrpCat.{u + 1})]

/-- Fixed Leray condition as positive-degree actual local `Sheaf.H'` vanishing. -/
example : Prop := Cohomology.IsLerayFor 𝒰 Ob

/-- Fixed zero obstruction coefficient used by the satisfying Leray instance. -/
example : Cohomology.ObstructionSheaf S :=
  Cohomology.zeroObstructionSheaf S

/-- Fixed zero-object property of the actual additive zero coefficient. -/
example : Limits.IsZero
    (Cohomology.zeroObstructionSheaf S).toAddCommGrpSheaf :=
  Cohomology.zeroObstructionSheaf_toAddCommGrpSheaf_isZero

/-- Fixed satisfying `IsLerayFor` instance for the zero coefficient. -/
example : Cohomology.IsLerayFor 𝒰 (Cohomology.zeroObstructionSheaf S) :=
  Cohomology.zeroObstructionSheaf_isLerayFor 𝒰

/-- Fixed rejection of Leray vanishing by a nontrivial actual local `Sheaf.H'`. -/
example {q p : ℕ} (hq : 0 < q)
    (σ : (Cohomology.canonicalCoverRelative 𝒰).simplex p)
    [Nontrivial
      ((Ob.toAddCommGrpSheaf).H' q
        ((Cohomology.canonicalCoverRelative 𝒰).overlap p σ))] :
    ¬ Cohomology.IsLerayFor 𝒰 Ob :=
  Cohomology.not_isLerayFor_of_nontrivialHPrime hq σ

/-- Fixed actual resolution column at selected Čech degree `p`. -/
noncomputable example (p : ℕ) : CochainComplex AddCommGrpCat.{u + 1} ℕ :=
  Cohomology.selectedCechResolutionColumn 𝒰 Ob p

/-- Fixed column-object formula. -/
example (p q : ℕ) :
    ((Cohomology.selectedCechResolutionColumn 𝒰 Ob p).X q : Type (u + 1)) =
      Cohomology.SelectedCechCochain 𝒰
        ((Cohomology.obstructionInjectiveResolution Ob).cocomplex.X q).val p :=
  Cohomology.selectedCechResolutionColumn_X 𝒰 Ob p q

/-- Fixed pointwise column-differential formula. -/
example (p q : ℕ)
    (c : Cohomology.SelectedCechCochain 𝒰
      ((Cohomology.obstructionInjectiveResolution Ob).cocomplex.X q).val p)
    (σ : (Cohomology.canonicalCoverRelative 𝒰).simplex p) :
    ((Cohomology.selectedCechResolutionColumn 𝒰 Ob p).d q (q + 1)).hom c σ =
      ((Cohomology.obstructionInjectiveResolution Ob).cocomplex.d
        q (q + 1)).val.app _ (c σ) :=
  Cohomology.selectedCechResolutionColumn_d_apply 𝒰 Ob p q c σ

variable (hLeray : Cohomology.IsLerayFor 𝒰 Ob)

/-- Fixed local-resolution homology vanishing derived from Leray vanishing. -/
example (q : ℕ) (hq : 0 < q) (p : ℕ)
    (σ : (Cohomology.canonicalCoverRelative 𝒰).simplex p) :
    Subsingleton
      ((Cohomology.baseResolutionComplex
        (base := (Cohomology.canonicalCoverRelative 𝒰).overlap p σ) Ob).homology q :
          Type (u + 1)) :=
  hLeray.overlapBaseResolutionHomology_subsingleton q hq p σ

/-- Fixed local-resolution exactness derived from Leray vanishing. -/
example (q : ℕ) (hq : 0 < q) (p : ℕ)
    (σ : (Cohomology.canonicalCoverRelative 𝒰).simplex p) :
    (Cohomology.baseResolutionComplex
      (base := (Cohomology.canonicalCoverRelative 𝒰).overlap p σ) Ob).ExactAt q :=
  hLeray.overlapBaseResolution_exactAt q hq p σ

/-- Fixed positive-degree exactness of the actual resolution column. -/
example (q : ℕ) (hq : 0 < q) (p : ℕ) :
    (Cohomology.selectedCechResolutionColumn 𝒰 Ob p).ExactAt q :=
  hLeray.selectedCechResolutionColumn_exactAt q hq p

/-- Fixed positive-degree homology vanishing of the actual resolution column. -/
example (q : ℕ) (hq : 0 < q) (p : ℕ) :
    Subsingleton
      ((Cohomology.selectedCechResolutionColumn 𝒰 Ob p).homology q :
        Type (u + 1)) :=
  hLeray.selectedCechResolutionColumn_homology_subsingleton q hq p

end LerayColumns

/-! Part 4 R5c8: augmentation exactness used by the selected total edge. -/

/-- Fixed degree-zero exactness of the actual resolution augmentation. -/
example (p : ℕ) :
    Function.Exact
      ((Cohomology.selectedCechResolutionAugmentation 𝒰 Ob).f p).hom
      (((Cohomology.selectedCechResolutionBicomplex 𝒰 Ob).d 0 1).f p).hom :=
  Cohomology.selectedCechResolutionAugmentation_exactAtZero 𝒰 Ob p

/-- Fixed surjectivity of restriction maps for actual injective sheaves. -/
example (I : Sheaf S.topology AddCommGrpCat.{u + 1})
    [Injective I] {X Y : S.category} (f : X ⟶ Y) :
    Function.Surjective (I.val.map f.op) :=
  Cohomology.injectiveSheaf_restriction_surjective I f

/-- Fixed degree-zero selected Čech exactness for every actual sheaf. -/
example (I : Sheaf S.topology AddCommGrpCat.{u + 1}) :
    Function.Exact
      ((Cohomology.baseToSelectedCechZero 𝒰).app I.val).hom
      (((Cohomology.selectedCechComplexFunctor 𝒰).obj I.val).d 0 1).hom :=
  Cohomology.sheaf_selectedCechAugmentation_exactAtZero 𝒰 I

/-- Fixed free Čech chain built from selected simplices and overlap arrows. -/
noncomputable example :
    ChainComplex (S.categoryᵒᵖ ⥤ AddCommGrpCat.{u + 1}) ℕ :=
  Cohomology.selectedCechFreeChain 𝒰

/-- Fixed local surjectivity onto positive-degree cycles before sheafification. -/
example (n : ℕ) :
    Presheaf.IsLocallySurjective S.topology
      ((Cohomology.selectedCechFreeChain 𝒰).sc' (n + 2) (n + 1) n).toCycles :=
  Cohomology.selectedCechFreeBoundaryToCycles_isLocallySurjective 𝒰 n

/-- Fixed sheafified free Čech chain. -/
noncomputable example :
    ChainComplex (Sheaf S.topology AddCommGrpCat.{u + 1}) ℕ :=
  Cohomology.selectedCechFreeSheafChain 𝒰

/-- Fixed positive-degree exactness of the sheafified free Čech chain. -/
example (n : ℕ) :
    (Cohomology.selectedCechFreeSheafChain 𝒰).ExactAt (n + 1) :=
  Cohomology.selectedCechFreeSheafChain_exactAt_succ 𝒰 n

/-- Fixed positive-degree selected Čech exactness for an injective sheaf. -/
example (I : Sheaf S.topology AddCommGrpCat.{u + 1})
    [Injective I] (p : ℕ) (hp : 0 < p) :
    ((Cohomology.selectedCechComplexFunctor 𝒰).obj I.val).ExactAt p :=
  Cohomology.injectiveSheaf_selectedCech_exactAt 𝒰 I p hp

section LerayTotalElimination

variable [HasExt.{u + 2} (Sheaf S.topology AddCommGrpCat.{u + 1})]

/-- Fixed selected Čech edge quasi-isomorphism derived from Leray vanishing. -/
example (hLeray : Cohomology.IsLerayFor 𝒰 Ob) :
    QuasiIso (Cohomology.selectedCechToResolutionTotal 𝒰 Ob) :=
  hLeray.selectedCechToResolutionTotal_quasiIso

/-- Fixed homology equivalence induced by the actual selected Čech edge. -/
noncomputable example (hLeray : Cohomology.IsLerayFor 𝒰 Ob) (n : ℕ) :
    (((Cohomology.selectedCechComplexFunctor 𝒰).obj
      Ob.toAddCommGrpSheaf.val).homology n : Type (u + 1)) ≃+
      ((Cohomology.selectedCechResolutionTotalComplex 𝒰 Ob).homology n :
        Type (u + 1)) :=
  Cohomology.selectedCechToResolutionTotalHomologyEquiv 𝒰 Ob hLeray n

/-- Fixed base-resolution edge quasi-isomorphism from actual sheaf gluing. -/
example : QuasiIso (Cohomology.baseResolutionToSelectedCechTotal 𝒰 Ob) :=
  Cohomology.baseResolutionToSelectedCechTotal_quasiIso 𝒰 Ob

/-- Fixed homology equivalence induced by the actual base-resolution edge. -/
noncomputable example (n : ℕ) :
    ((Cohomology.baseResolutionComplex (base := base) Ob).homology n :
        Type (u + 1)) ≃+
      ((Cohomology.selectedCechResolutionTotalComplex 𝒰 Ob).homology n :
        Type (u + 1)) :=
  Cohomology.baseResolutionToSelectedCechTotalHomologyEquiv 𝒰 Ob n

/-- Fixed canonical selected Čech-to-local-sheaf-cohomology equivalence. -/
noncomputable example (hLeray : Cohomology.IsLerayFor 𝒰 Ob) (n : ℕ) :
    (Cohomology.canonicalCechComplex 𝒰 Ob).AdditiveCechHn n ≃+
      (Ob.toAddCommGrpSheaf).H' n base :=
  Cohomology.cechToSheafHAtBaseEquiv 𝒰 Ob hLeray n

/-- Fixed canonical selected Čech-to-local-sheaf-cohomology map. -/
noncomputable example (hLeray : Cohomology.IsLerayFor 𝒰 Ob) (n : ℕ) :
    (Cohomology.canonicalCechComplex 𝒰 Ob).AdditiveCechHn n →+
      (Ob.toAddCommGrpSheaf).H' n base :=
  Cohomology.cechToSheafHAtBase 𝒰 Ob hLeray n

/-- Fixed bijectivity of the canonical local comparison. -/
example (hLeray : Cohomology.IsLerayFor 𝒰 Ob) (n : ℕ) :
    Function.Bijective (Cohomology.cechToSheafHAtBase 𝒰 Ob hLeray n) :=
  Cohomology.cechToSheafHAtBase_bijective 𝒰 Ob hLeray n

/-- Fixed refinement naturality of the canonical local comparison. -/
example {𝒱 : Site.AATCoverageFamily S.requirements S.overlap base}
    (r : Site.AATCoverageFamily.Refinement 𝒰 𝒱)
    (h𝒰 : Cohomology.IsLerayFor 𝒰 Ob)
    (h𝒱 : Cohomology.IsLerayFor 𝒱 Ob) (n : ℕ) :
    (Cohomology.cechToSheafHAtBase 𝒱 Ob h𝒱 n).comp
        ((r.canonicalCechHom Ob).mapAdditiveCechHn n) =
      Cohomology.cechToSheafHAtBase 𝒰 Ob h𝒰 n :=
  Cohomology.cechToSheafHAtBase_refinement_naturality r Ob h𝒰 h𝒱 n

/-- Fixed terminal-base Čech-to-global-sheaf-cohomology map. -/
noncomputable example (hbase : Limits.IsTerminal base)
    (hLeray : Cohomology.IsLerayFor 𝒰 Ob) (n : ℕ) :
    (Cohomology.canonicalCechComplex 𝒰 Ob).AdditiveCechHn n →+
      (Ob.toAddCommGrpSheaf).H n :=
  Cohomology.cechToSheafH 𝒰 Ob hbase hLeray n

/-- Fixed bijectivity of the canonical terminal-base comparison. -/
example (hbase : Limits.IsTerminal base)
    (hLeray : Cohomology.IsLerayFor 𝒰 Ob) (n : ℕ) :
    Function.Bijective (Cohomology.cechToSheafH 𝒰 Ob hbase hLeray n) :=
  Cohomology.cechToSheafH_bijective 𝒰 Ob hbase hLeray n

/-- Fixed refinement naturality of the terminal-base comparison. -/
example {𝒱 : Site.AATCoverageFamily S.requirements S.overlap base}
    (r : Site.AATCoverageFamily.Refinement 𝒰 𝒱)
    (hbase : Limits.IsTerminal base)
    (h𝒰 : Cohomology.IsLerayFor 𝒰 Ob)
    (h𝒱 : Cohomology.IsLerayFor 𝒱 Ob) (n : ℕ) :
    (Cohomology.cechToSheafH 𝒱 Ob hbase h𝒱 n).comp
        ((r.canonicalCechHom Ob).mapAdditiveCechHn n) =
      Cohomology.cechToSheafH 𝒰 Ob hbase h𝒰 n :=
  Cohomology.cechToSheafH_refinement_naturality r Ob hbase h𝒰 h𝒱 n

end LerayTotalElimination

end SelectedCechResolutionBicomplexSD5

namespace LargeLerayComparisonSD8d

open CategoryTheory

variable {A : ArchitectureObject U}
variable {S : Site.AATSite A} {base : S.category}

/-- Fixed generic Leray predicate for an arbitrary large additive sheaf. -/
example
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (F : Sheaf S.topology AddCommGrpCat.{u + 1})
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 2} (Sheaf S.topology AddCommGrpCat.{u + 1})] : Prop :=
  Cohomology.IsLerayForSheaf 𝒰 F

/-- Fixed satisfying instance supplied by the actual zero obstruction sheaf. -/
example
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 2} (Sheaf S.topology AddCommGrpCat.{u + 1})]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base) :
    Cohomology.IsLerayForSheaf
      𝒰 (Cohomology.zeroObstructionSheaf S).toAddCommGrpSheaf :=
  Cohomology.zeroObstructionSheaf_isLerayForSheaf 𝒰

/-- Fixed rejection from nontrivial actual local positive-degree cohomology. -/
example
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 2} (Sheaf S.topology AddCommGrpCat.{u + 1})]
    {𝒰 : Site.AATCoverageFamily S.requirements S.overlap base}
    {F : Sheaf S.topology AddCommGrpCat.{u + 1}}
    {q p : ℕ} (hq : 0 < q)
    (σ : (Cohomology.canonicalCoverRelative 𝒰).simplex p)
    [Nontrivial
      (F.H' q ((Cohomology.canonicalCoverRelative 𝒰).overlap p σ))] :
    ¬ Cohomology.IsLerayForSheaf 𝒰 F :=
  Cohomology.not_isLerayForSheaf_of_nontrivialHPrime hq σ

/-- Fixed cross-universe selected Čech comparison for a large additive sheaf. -/
noncomputable example
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (F : Sheaf S.topology AddCommGrpCat.{u + 1})
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 2} (Sheaf S.topology AddCommGrpCat.{u + 1})]
    (hLeray : Cohomology.IsLerayForSheaf 𝒰 F)
    (n : Nat) :
    (((Cohomology.selectedCechComplexFunctor 𝒰).obj F.val).homology n :
        Type (u + 1)) ≃+
      (F.H' n base : Type (u + 2)) :=
  Cohomology.selectedCechToSheafHAtBaseEquivForSheaf 𝒰 F hLeray n

/-- Fixed concrete rejection firing for the identity-containing finite cover. -/
example :
    ¬ Cohomology.IsLerayForSheaf
      ReadingFunctorialityFinite.nonLerayCover
      ReadingFunctorialityFinite.nonLerayObstructionSheaf.toAddCommGrpSheaf :=
  ReadingFunctorialityFinite.nonLerayCover_not_isLerayForSheaf

end LargeLerayComparisonSD8d

namespace FiniteSheafHFiringSD9

open CategoryTheory ReadingFunctorialityFinite

/-- Fixed terminal base used by the finite actual-`Sheaf.H` firing. -/
noncomputable example : Limits.IsTerminal finiteBase :=
  finiteBaseIsTerminal

/-- Fixed named additive sheafification instance for the finite site. -/
noncomputable example :
    HasSheafify finiteSite.topology AddCommGrpCat.{1} :=
  finiteAddCommGrpHasSheafify

/-- Fixed nonzero additive obstruction coefficient on the finite site. -/
noncomputable example : Cohomology.ObstructionSheaf finiteSite :=
  finiteObstructionSheaf

/-- Fixed nonzero canonical cochain-map firing for the duplicated cover. -/
example :
    ∃ (n : Nat)
      (c : (Cohomology.canonicalCechComplex
        coarseCover finiteObstructionSheaf).AdditiveCochain n)
      (σ : (Cohomology.canonicalCoverRelative fineCover).simplex n),
      (coarseToFineCover.canonicalCechHom finiteObstructionSheaf).app n c σ ≠ 0 :=
  coarseToFineCechHom_nonzero

/-- Fixed positive Leray firing for the actual finite coefficient. -/
example : Cohomology.IsLerayFor coarseCover finiteObstructionSheaf :=
  finiteLerayCover

/-- Fixed terminal comparison firing in every cohomological degree. -/
example (n : Nat) :
    Function.Bijective
      (Cohomology.cechToSheafH coarseCover finiteObstructionSheaf
        finiteBaseIsTerminal finiteLerayCover n) :=
  finite_cechToSheafH_bijective n

/-- Fixed independent strict-diamond AAT site. -/
noncomputable example : Site.AATSite FiniteModel.corePackage.object :=
  nonLeraySite

/-- Fixed base of the strict-diamond model. -/
noncomputable example : nonLeraySite.category :=
  nonLerayBase

/-- Fixed left branch of the selected strict-diamond configuration. -/
example : nonLeraySite.category :=
  nonLerayLeftObject

/-- Fixed right branch of the selected strict-diamond configuration. -/
example : nonLeraySite.category :=
  nonLerayRightObject

/-- Fixed two-branch structure of the comparison cover. -/
example :
    ∃ i j : nonLerayComparisonCover.Index,
      i ≠ j ∧
        nonLerayComparisonCover.patch i = nonLerayLeftObject.ctx ∧
        nonLerayComparisonCover.patch j = nonLerayRightObject.ctx :=
  nonLerayComparisonCover_twoBranches

/-- Fixed bottom object given by the actual pair overlap. -/
noncomputable example : nonLeraySite.category :=
  nonLerayOverlapObject

/-- Fixed identification of the selected bottom with the actual pair overlap. -/
example :
    nonLeraySite.overlap.overlap nonLerayBase.ctx
        nonLerayLeftObject.ctx nonLerayRightObject.ctx =
      nonLerayOverlapObject.ctx :=
  nonLerayPairOverlap_eq

/-- Fixed strict-diamond order certificate on the four selected objects. -/
example :
    nonLeraySite.contextPreorder.le
        nonLerayOverlapObject.ctx nonLerayLeftObject.ctx ∧
      nonLeraySite.contextPreorder.le
        nonLerayOverlapObject.ctx nonLerayRightObject.ctx ∧
      nonLeraySite.contextPreorder.le nonLerayLeftObject.ctx nonLerayBase.ctx ∧
      nonLeraySite.contextPreorder.le nonLerayRightObject.ctx nonLerayBase.ctx ∧
      ¬ nonLeraySite.contextPreorder.le
        nonLerayLeftObject.ctx nonLerayRightObject.ctx ∧
      ¬ nonLeraySite.contextPreorder.le
        nonLerayRightObject.ctx nonLerayLeftObject.ctx ∧
      ¬ nonLeraySite.contextPreorder.le nonLerayBase.ctx nonLerayLeftObject.ctx ∧
      ¬ nonLeraySite.contextPreorder.le nonLerayBase.ctx nonLerayRightObject.ctx ∧
      ¬ nonLeraySite.contextPreorder.le
        nonLerayLeftObject.ctx nonLerayOverlapObject.ctx ∧
      ¬ nonLeraySite.contextPreorder.le
        nonLerayRightObject.ctx nonLerayOverlapObject.ctx :=
  nonLerayStrictDiamond

/-- Fixed admissible-cover classification on the four selected objects. -/
example :
    Nonempty
        (Site.AATCoverageFamily nonLeraySite.requirements
          nonLeraySite.overlap nonLerayBase) ∧
      ¬ Nonempty
        (Site.AATCoverageFamily nonLeraySite.requirements
          nonLeraySite.overlap nonLerayLeftObject) ∧
      ¬ Nonempty
        (Site.AATCoverageFamily nonLeraySite.requirements
          nonLeraySite.overlap nonLerayRightObject) ∧
      ¬ Nonempty
        (Site.AATCoverageFamily nonLeraySite.requirements
          nonLeraySite.overlap nonLerayOverlapObject) :=
  nonLeraySelectedCoverClassification

/-- Fixed Leray two-branch comparison cover of the strict-diamond model. -/
noncomputable example :
    Site.AATCoverageFamily nonLeraySite.requirements
      nonLeraySite.overlap nonLerayBase :=
  nonLerayComparisonCover

/-- Fixed exact two-point index of the comparison cover. -/
example : nonLerayComparisonCover.Index ≃ Bool :=
  nonLerayComparisonCoverIndexEquiv

/-- Fixed small additive coefficient on the strict-diamond model. -/
noncomputable example : Cohomology.ObstructionSheaf nonLeraySite :=
  nonLerayObstructionSheaf

/-- Fixed zero value at the strict-diamond base. -/
example :
    Subsingleton
      ((nonLerayObstructionSheaf.toAddCommGrpSheaf.val.obj
        (Opposite.op nonLerayBase) : Type 1)) :=
  nonLerayBaseCoefficient_subsingleton

/-- Fixed zero value at the strict-diamond left branch. -/
example :
    Subsingleton
      ((nonLerayObstructionSheaf.toAddCommGrpSheaf.val.obj
        (Opposite.op nonLerayLeftObject) : Type 1)) :=
  nonLerayLeftCoefficient_subsingleton

/-- Fixed zero value at the strict-diamond right branch. -/
example :
    Subsingleton
      ((nonLerayObstructionSheaf.toAddCommGrpSheaf.val.obj
        (Opposite.op nonLerayRightObject) : Type 1)) :=
  nonLerayRightCoefficient_subsingleton

/-- Fixed `ZMod 2` value at the actual pair overlap. -/
noncomputable example :
    ((nonLerayObstructionSheaf.toAddCommGrpSheaf.val.obj
      (Opposite.op nonLerayOverlapObject) : Type 1)) ≃+ ZMod 2 :=
  nonLerayOverlapCoefficientEquiv

/-- Fixed positive Leray proof for the two-branch comparison cover. -/
example :
    Cohomology.IsLerayFor
      nonLerayComparisonCover nonLerayObstructionSheaf :=
  nonLerayComparisonCover_isLeray

/-- Fixed nontrivial degree-one Čech class. -/
example :
    Nontrivial
      ((Cohomology.canonicalCechComplex
        nonLerayComparisonCover nonLerayObstructionSheaf).AdditiveCechHn 1) :=
  nonLerayCechHOne_nontrivial

/-- Fixed actual local `Sheaf.H'` nontriviality. -/
example :
    Nontrivial
      ((nonLerayObstructionSheaf.toAddCommGrpSheaf).H' 1 nonLerayBase) :=
  nonLerayHPrimeOne_nontrivial

/-- Fixed selected cover containing the identity chart. -/
noncomputable example :
    Site.AATCoverageFamily nonLeraySite.requirements
      nonLeraySite.overlap nonLerayBase :=
  nonLerayCover

/-- Fixed identity chart contained in the negative selected cover. -/
example :
    ∃ i : nonLerayCover.Index,
      nonLerayCover.patch i = nonLerayBase.ctx :=
  nonLerayCover_containsIdentity

/-- Fixed premise-free negative Leray firing. -/
example :
    ¬ Cohomology.IsLerayFor nonLerayCover nonLerayObstructionSheaf :=
  nonLerayCover_not_completionEvidence

end FiniteSheafHFiringSD9

namespace CoefficientChangeSD6

open CategoryTheory CategoryTheory.Limits

universe x

/-- Fixed primitive data for a flat coefficient change. -/
example
    {k : Type v} {k' : Type w}
    [CommRing k] [CommRing k']
    (hom : k →+* k') (flat : hom.Flat) :
    FlatCoefficientChange k k' :=
  ⟨hom, flat⟩

/-- Fixed identity flat coefficient change. -/
example (k : Type v) [CommRing k] :
    FlatCoefficientChange k k :=
  FlatCoefficientChange.refl k

/-- Fixed composition of flat coefficient changes. -/
example
    {k : Type v} {k' : Type w} {k'' : Type x}
    [CommRing k] [CommRing k'] [CommRing k'']
    (f : FlatCoefficientChange k k')
    (g : FlatCoefficientChange k' k'') :
    FlatCoefficientChange k k'' :=
  f.comp g

/-- Fixed universe-lifted ring homomorphism. -/
noncomputable example
    {k k' : Type v} [CommRing k] [CommRing k']
    (f : FlatCoefficientChange k k') :
    ULift.{max u v, v} k →+* ULift.{max u v, v} k' :=
  f.liftedHom

/-- Fixed Mathlib under-category coefficient extension. -/
noncomputable example
    {k k' : Type v} [CommRing k] [CommRing k']
    (f : FlatCoefficientChange k k') :
    LawAlgebra.AATCommAlgCat.{u, v} k ⥤
      LawAlgebra.AATCommAlgCat.{u, v} k' :=
  f.coefficientExtension

/-- Fixed finite-limit preservation from flatness. -/
noncomputable example
    {k k' : Type v} [CommRing k] [CommRing k']
    (f : FlatCoefficientChange k k') :
    PreservesFiniteLimits
      (f.coefficientExtension :
        LawAlgebra.AATCommAlgCat.{u, v} k ⥤
          LawAlgebra.AATCommAlgCat.{u, v} k') :=
  FlatCoefficientChange.coefficientExtension_preservesFiniteLimits f

/-- Fixed sheafification preservation from the pushout adjunction. -/
noncomputable example
    {A : ArchitectureObject U}
    (S : Site.AATSite A)
    {k k' : Type v} [CommRing k] [CommRing k']
    (f : FlatCoefficientChange k k') :
    S.topology.PreservesSheafification
      (f.coefficientExtension :
        LawAlgebra.AATCommAlgCat.{u, v} k ⥤
          LawAlgebra.AATCommAlgCat.{u, v} k') :=
  FlatCoefficientChange.coefficientExtension_preservesSheafification S f

/-- Fixed identity coherence for coefficient extension. -/
noncomputable example
    (k : Type v) [CommRing k] :
    ((FlatCoefficientChange.refl k).coefficientExtension :
      LawAlgebra.AATCommAlgCat.{u, v} k ⥤
        LawAlgebra.AATCommAlgCat.{u, v} k) ≅ 𝟭 _ :=
  FlatCoefficientChange.coefficientExtensionReflIso k

/-- Fixed composition coherence for coefficient extension. -/
noncomputable example
    {k k' k'' : Type v}
    [CommRing k] [CommRing k'] [CommRing k'']
    (f : FlatCoefficientChange k k')
    (g : FlatCoefficientChange k' k'') :
    ((f.comp g).coefficientExtension :
      LawAlgebra.AATCommAlgCat.{u, v} k ⥤
        LawAlgebra.AATCommAlgCat.{u, v} k'') ≅
      (f.coefficientExtension :
        LawAlgebra.AATCommAlgCat.{u, v} k ⥤
          LawAlgebra.AATCommAlgCat.{u, v} k') ⋙
      (g.coefficientExtension :
        LawAlgebra.AATCommAlgCat.{u, v} k' ⥤
          LawAlgebra.AATCommAlgCat.{u, v} k'') :=
  FlatCoefficientChange.coefficientExtensionCompIso f g

/-- Fixed identity sheaf-composition instance. -/
noncomputable example
    {A : ArchitectureObject U}
    (S : Site.AATSite A)
    (k : Type v) [CommRing k] :
    S.topology.HasSheafCompose
      ((FlatCoefficientChange.refl k).coefficientExtension :
        LawAlgebra.AATCommAlgCat.{u, v} k ⥤
          LawAlgebra.AATCommAlgCat.{u, v} k) :=
  FlatCoefficientChange.coefficientExtension_hasSheafCompose_refl S k

/-- Fixed composition theorem for sheaf-preserving coefficient changes. -/
example
    {A : ArchitectureObject U}
    {S : Site.AATSite A}
    {k k' k'' : Type v}
    [CommRing k] [CommRing k'] [CommRing k'']
    (f : FlatCoefficientChange k k')
    (g : FlatCoefficientChange k' k'')
    (hf : S.topology.HasSheafCompose
      (f.coefficientExtension :
        LawAlgebra.AATCommAlgCat.{u, v} k ⥤
          LawAlgebra.AATCommAlgCat.{u, v} k'))
    (hg : S.topology.HasSheafCompose
      (g.coefficientExtension :
        LawAlgebra.AATCommAlgCat.{u, v} k' ⥤
          LawAlgebra.AATCommAlgCat.{u, v} k'')) :
    S.topology.HasSheafCompose
      ((f.comp g).coefficientExtension :
        LawAlgebra.AATCommAlgCat.{u, v} k ⥤
          LawAlgebra.AATCommAlgCat.{u, v} k'') :=
  FlatCoefficientChange.coefficientExtension_hasSheafCompose_comp
    f g hf hg

/-! Part 4 SD6 / AC28: raw structural coefficient change. -/

/-- Fixed objectwise change of structural relation coefficients. -/
noncomputable example
    {A : ArchitectureObject U}
    {W : Site.ArchitectureContext A}
    {k k' : Type v} [CommRing k] [CommRing k']
    {F : LawAlgebra.CoordinateFamily W}
    (R : LawAlgebra.StructuralRelationFamily F k)
    (f : k →+* k') :
    LawAlgebra.StructuralRelationFamily F k' :=
  R.baseChange f

/-- Fixed transport of restriction-stable structural relations. -/
noncomputable example
    {A : ArchitectureObject U}
    {source target : Site.ArchitectureContext A}
    {sourceFamily : LawAlgebra.CoordinateFamily source}
    {targetFamily : LawAlgebra.CoordinateFamily target}
    {k k' : Type v} [CommRing k] [CommRing k']
    {sourceRelations :
      LawAlgebra.StructuralRelationFamily sourceFamily k}
    {targetRelations :
      LawAlgebra.StructuralRelationFamily targetFamily k}
    {g : Site.ContextMorphism source target}
    (h : LawAlgebra.RestrictionStableStructuralRelations
      sourceRelations targetRelations g)
    (f : k →+* k') :
    LawAlgebra.RestrictionStableStructuralRelations
      (sourceRelations.baseChange f) (targetRelations.baseChange f) g :=
  h.baseChange f

/-- Fixed raw restriction-system coefficient change. -/
noncomputable example
    {A : ArchitectureObject U} {S : Site.AATSite A}
    {k k' : Type v} [CommRing k] [CommRing k']
    (raw : LawAlgebra.RawAmbientRestrictionSystem S k)
    (f : k →+* k') :
    LawAlgebra.RawAmbientRestrictionSystem S k' :=
  raw.baseChange f

/-- Fixed preservation of raw coordinate families. -/
example
    {A : ArchitectureObject U} {S : Site.AATSite A}
    {k k' : Type v} [CommRing k] [CommRing k']
    (raw : LawAlgebra.RawAmbientRestrictionSystem S k)
    (f : k →+* k') :
    (raw.baseChange f).coordFamily = raw.coordFamily :=
  LawAlgebra.RawAmbientRestrictionSystem.baseChange_coordFamily raw f

/-- Fixed objectwise characterization of changed structural relations. -/
example
    {A : ArchitectureObject U} {S : Site.AATSite A}
    {k k' : Type v} [CommRing k] [CommRing k']
    (raw : LawAlgebra.RawAmbientRestrictionSystem S k)
    (f : k →+* k') (W : S.category) :
    (raw.baseChange f).relationFamily W =
      (raw.relationFamily W).baseChange f :=
  LawAlgebra.RawAmbientRestrictionSystem.baseChange_relationFamily raw f W

/-- Fixed characterization of changed restriction-stability data. -/
example
    {A : ArchitectureObject U} {S : Site.AATSite A}
    {k k' : Type v} [CommRing k] [CommRing k']
    (raw : LawAlgebra.RawAmbientRestrictionSystem S k)
    (f : k →+* k') {W V : S.category} (g : W ⟶ V) :
    HEq ((raw.baseChange f).restrictionStable g)
      ((raw.restrictionStable g).baseChange f) :=
  LawAlgebra.RawAmbientRestrictionSystem.baseChange_restrictionStable raw f g

/-- Fixed identity coherence of raw coefficient change. -/
example
    {A : ArchitectureObject U} {S : Site.AATSite A}
    {k : Type v} [CommRing k]
    (raw : LawAlgebra.RawAmbientRestrictionSystem S k) :
    raw.baseChange (RingHom.id k) = raw :=
  LawAlgebra.RawAmbientRestrictionSystem.baseChange_id raw

/-- Fixed composition coherence of raw coefficient change. -/
example
    {A : ArchitectureObject U} {S : Site.AATSite A}
    {k k' k'' : Type v} [CommRing k] [CommRing k'] [CommRing k'']
    (raw : LawAlgebra.RawAmbientRestrictionSystem S k)
    (f : k →+* k') (g : k' →+* k'') :
    raw.baseChange (g.comp f) = (raw.baseChange f).baseChange g :=
  LawAlgebra.RawAmbientRestrictionSystem.baseChange_comp raw f g

/-- Fixed natural structural-quotient comparison with coefficient extension. -/
noncomputable example
    {A : ArchitectureObject U} {S : Site.AATSite A}
    {k k' : Type v} [CommRing k] [CommRing k']
    (raw : LawAlgebra.RawAmbientRestrictionSystem S k)
    (f : FlatCoefficientChange k k') :
    (raw.baseChange f.hom).toPresheaf ≅
      raw.toPresheaf ⋙ f.coefficientExtension :=
  LawAlgebra.RawAmbientRestrictionSystem.baseChangePresheafIso raw f

/-! Part 4 SD6 / AC29: sheafified section and affine Spec comparisons. -/

/-- Fixed section-object comparison obtained from sheafification and raw base change. -/
noncomputable example
    {A : ArchitectureObject U} {S : Site.AATSite A}
    {k k' : Type v} [CommRing k] [CommRing k']
    (raw : LawAlgebra.RawAmbientRestrictionSystem S k)
    [HasSheafify S.topology (LawAlgebra.AATCommAlgCat k)]
    [HasSheafify S.topology (LawAlgebra.AATCommAlgCat k')]
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        LawAlgebra.AATCommAlgCat.{u, v} k ⥤
          LawAlgebra.AATCommAlgCat.{u, v} k')]
    (W : S.category) :
    (f.coefficientExtension.obj
        (raw.toRingedSite.structureSheaf.val.obj (Opposite.op W)) :
      LawAlgebra.AATCommAlgCat.{u, v} k') ≅
      (raw.baseChange f.hom).toRingedSite.structureSheaf.val.obj
        (Opposite.op W) :=
  LawAlgebra.RawAmbientRestrictionSystem.sheafifiedSectionObjectBaseChangeIso
    raw f W

/-- Fixed actual affine pullback comparison for changed section spectra. -/
noncomputable example
    {A : ArchitectureObject U} {S : Site.AATSite A}
    {k k' : Type v} [CommRing k] [CommRing k']
    (raw : LawAlgebra.RawAmbientRestrictionSystem S k)
    [HasSheafify S.topology (LawAlgebra.AATCommAlgCat k)]
    [HasSheafify S.topology (LawAlgebra.AATCommAlgCat k')]
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        LawAlgebra.AATCommAlgCat.{u, v} k ⥤
          LawAlgebra.AATCommAlgCat.{u, v} k')]
    (W : S.category) :
    LawAlgebra.architectureChartSpec (raw.baseChange f.hom) W ≅
      pullback
        (AlgebraicGeometry.Scheme.Spec.map
          (raw.toRingedSite.structureSheaf.val.obj (Opposite.op W)).hom.op)
        (AlgebraicGeometry.Scheme.Spec.map
          (CommRingCat.ofHom f.liftedHom).op) :=
  LawAlgebra.RawAmbientRestrictionSystem.sheafifiedSectionSpecBaseChangeIso
    raw f W

/-- Fixed canonical map on sheafified sections. -/
noncomputable example
    {A : ArchitectureObject U} {S : Site.AATSite A}
    {k k' : Type v} [CommRing k] [CommRing k']
    (raw : LawAlgebra.RawAmbientRestrictionSystem S k)
    [HasSheafify S.topology (LawAlgebra.AATCommAlgCat k)]
    [HasSheafify S.topology (LawAlgebra.AATCommAlgCat k')]
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        LawAlgebra.AATCommAlgCat.{u, v} k ⥤
          LawAlgebra.AATCommAlgCat.{u, v} k')]
    (W : S.category) :
    LawAlgebra.SheafifiedSectionRing raw W ⟶
      LawAlgebra.SheafifiedSectionRing (raw.baseChange f.hom) W :=
  LawAlgebra.RawAmbientRestrictionSystem.sheafifiedSectionBaseChangeMap
    raw f W

/-- Fixed characterization of the canonical sheafified-section map. -/
example
    {A : ArchitectureObject U} {S : Site.AATSite A}
    {k k' : Type v} [CommRing k] [CommRing k']
    (raw : LawAlgebra.RawAmbientRestrictionSystem S k)
    [HasSheafify S.topology (LawAlgebra.AATCommAlgCat k)]
    [HasSheafify S.topology (LawAlgebra.AATCommAlgCat k')]
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        LawAlgebra.AATCommAlgCat.{u, v} k ⥤
          LawAlgebra.AATCommAlgCat.{u, v} k')]
    (W : S.category) :
    LawAlgebra.RawAmbientRestrictionSystem.sheafifiedSectionBaseChangeMap
        raw f W =
      Limits.pushout.inl
          (raw.toRingedSite.structureSheaf.val.obj (Opposite.op W)).hom
          (CommRingCat.ofHom f.liftedHom) ≫
        (LawAlgebra.RawAmbientRestrictionSystem.sheafifiedSectionObjectBaseChangeIso
          raw f W).hom.right :=
  LawAlgebra.RawAmbientRestrictionSystem.sheafifiedSectionBaseChangeMap_eq
    raw f W

/-- Supporting contract for the source projection of the canonical affine
base-change comparison. -/
example
    {A : ArchitectureObject U} {S : Site.AATSite A}
    {k k' : Type v} [CommRing k] [CommRing k']
    (raw : LawAlgebra.RawAmbientRestrictionSystem S k)
    [HasSheafify S.topology (LawAlgebra.AATCommAlgCat k)]
    [HasSheafify S.topology (LawAlgebra.AATCommAlgCat k')]
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        LawAlgebra.AATCommAlgCat.{u, v} k ⥤
          LawAlgebra.AATCommAlgCat.{u, v} k')]
    (W : S.category) :
    (LawAlgebra.RawAmbientRestrictionSystem.sheafifiedSectionSpecBaseChangeIso
        raw f W).hom ≫
        pullback.fst
          (AlgebraicGeometry.Scheme.Spec.map
            (raw.toRingedSite.structureSheaf.val.obj
              (Opposite.op W)).hom.op)
          (AlgebraicGeometry.Scheme.Spec.map
            (CommRingCat.ofHom f.liftedHom).op) =
      AlgebraicGeometry.Scheme.Spec.map
        (LawAlgebra.RawAmbientRestrictionSystem.sheafifiedSectionBaseChangeMap
          raw f W).op :=
  LawAlgebra.RawAmbientRestrictionSystem.sheafifiedSectionSpecBaseChangeIso_hom_fst
    raw f W

/-- Supporting contract for the coefficient projection of the canonical
affine base-change comparison. -/
example
    {A : ArchitectureObject U} {S : Site.AATSite A}
    {k k' : Type v} [CommRing k] [CommRing k']
    (raw : LawAlgebra.RawAmbientRestrictionSystem S k)
    [HasSheafify S.topology (LawAlgebra.AATCommAlgCat k)]
    [HasSheafify S.topology (LawAlgebra.AATCommAlgCat k')]
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        LawAlgebra.AATCommAlgCat.{u, v} k ⥤
          LawAlgebra.AATCommAlgCat.{u, v} k')]
    (W : S.category) :
    (LawAlgebra.RawAmbientRestrictionSystem.sheafifiedSectionSpecBaseChangeIso
        raw f W).hom ≫
        pullback.snd
          (AlgebraicGeometry.Scheme.Spec.map
            (raw.toRingedSite.structureSheaf.val.obj
              (Opposite.op W)).hom.op)
          (AlgebraicGeometry.Scheme.Spec.map
            (CommRingCat.ofHom f.liftedHom).op) =
      AlgebraicGeometry.Scheme.Spec.map
        ((raw.baseChange f.hom).toRingedSite.structureSheaf.val.obj
          (Opposite.op W)).hom.op :=
  LawAlgebra.RawAmbientRestrictionSystem.sheafifiedSectionSpecBaseChangeIso_hom_snd
    raw f W

/-! Standard-scheme coefficient pullback contracts. -/

section StandardSchemeCoefficientChange

variable {A : ArchitectureObject U} {S : Site.AATSite A}
variable {k k' : Type v} [CommRing k] [CommRing k']
variable (raw : LawAlgebra.RawAmbientRestrictionSystem S k)
variable [HasSheafify S.topology (LawAlgebra.AATCommAlgCat k)]
variable [HasSheafify S.topology (LawAlgebra.AATCommAlgCat k')]
variable (X : LawAlgebra.StandardArchitectureScheme raw)
variable (f : FlatCoefficientChange k k')
variable [S.topology.HasSheafCompose
  (f.coefficientExtension :
    LawAlgebra.AATCommAlgCat.{u, v} k ⥤
      LawAlgebra.AATCommAlgCat.{u, v} k')]

/-- Fixed coefficient structure morphism obtained from the global reading. -/
noncomputable example :
    X.underlying ⟶ AlgebraicGeometry.Scheme.Spec.obj
      (Opposite.op (CommRingCat.of (ULift.{max u v, v} k))) :=
  X.coefficientStructureMap raw

/-- Fixed standard-scheme change over the changed raw system. -/
noncomputable example :
    LawAlgebra.StandardArchitectureScheme (raw.baseChange f.hom) :=
  X.baseChange raw f

/-- Fixed projection from the changed scheme to its source. -/
noncomputable example :
    (X.baseChange raw f).underlying ⟶ X.underlying :=
  X.baseChangeMap raw f

/-- Fixed identification of the changed underlying scheme with the actual pullback. -/
noncomputable example :
    (X.baseChange raw f).underlying ≅
      pullback (X.coefficientStructureMap raw)
        (AlgebraicGeometry.Scheme.Spec.map
          (CommRingCat.ofHom f.liftedHom).op) :=
  X.baseChangeUnderlyingIso raw f

/-- Fixed pullback-projection formula for the change map. -/
example :
    X.baseChangeMap raw f =
      (X.baseChangeUnderlyingIso raw f).hom ≫
        pullback.fst (X.coefficientStructureMap raw)
          (AlgebraicGeometry.Scheme.Spec.map
            (CommRingCat.ofHom f.liftedHom).op) :=
  X.baseChangeMap_eq_pullback_fst raw f

/-- Fixed changed reading decoration. -/
noncomputable example :
    LawAlgebra.AATReadingDecoration (raw.baseChange f.hom)
      (X.baseChange raw f).underlying :=
  X.baseChangedDecoration raw f

/-- Fixed preservation of the selected reading context. -/
example :
    (X.baseChangedDecoration raw f).context = X.decoration.context :=
  X.baseChangedDecoration_context raw f

/-- Fixed compatibility of changed interpretation with the projection. -/
example :
    LawAlgebra.RawAmbientRestrictionSystem.sheafifiedSectionBaseChangeMap
          raw f X.decoration.context ≫
        (X.baseChangedDecoration raw f).interpretation =
      X.decoration.interpretation ≫ (X.baseChangeMap raw f).appTop :=
  X.baseChangedDecoration_interpretation raw f

/-- Fixed identification of the stored changed decoration. -/
example :
    (X.baseChange raw f).decoration = X.baseChangedDecoration raw f :=
  X.baseChange_decoration raw f

/-- Fixed affine atlas on the changed scheme. -/
noncomputable example :
    LawAlgebra.ArchitectureAffineAtlas (raw.baseChange f.hom)
      (X.baseChange raw f).underlying (X.baseChange raw f).decoration :=
  X.baseChangedAtlas raw f

/-- Fixed preservation of the atlas index type. -/
example :
    (X.baseChangedAtlas raw f).Index = X.atlas.Index :=
  X.baseChangedAtlas_Index raw f

/-- Fixed map from a changed chart to its source chart. -/
noncomputable example (i : X.atlas.Index) :
    ((X.baseChangedAtlas raw f).chart
      (cast (X.baseChangedAtlas_Index raw f).symm i)).domain ⟶
      (X.atlas.chart i).domain :=
  X.baseChangedChartMap raw f i

/-- Fixed pullback square for each changed chart. -/
example (i : X.atlas.Index) :
    IsPullback
      ((X.baseChangedAtlas raw f).chart
        (cast (X.baseChangedAtlas_Index raw f).symm i)).map
      (X.baseChangedChartMap raw f i)
      (X.baseChangeMap raw f)
      (X.atlas.chart i).map :=
  X.baseChangedChart_isPullback raw f i

/-- Fixed identification of the stored changed atlas. -/
example :
    (X.baseChange raw f).atlas = X.baseChangedAtlas raw f :=
  X.baseChange_atlas raw f

/-- Fixed overlap presentation for the changed atlas. -/
noncomputable example :
    LawAlgebra.ArchitectureOverlapPresentation
      (raw.baseChange f.hom) (X.baseChangedAtlas raw f) :=
  X.baseChangedOverlaps raw f

/-- Fixed validity proof for the changed overlap presentation. -/
example :
    LawAlgebra.IsArchitectureOverlapPresentation
      (raw.baseChange f.hom) (X.baseChangedOverlaps raw f) :=
  X.baseChangedOverlaps_valid raw f

/-- Fixed identification of the stored overlap presentation. -/
example :
    HEq (X.baseChange raw f).overlaps (X.baseChangedOverlaps raw f) :=
  X.baseChange_overlaps raw f

end StandardSchemeCoefficientChange

/-! Standard-scheme coefficient-change coherence contracts. -/

section StandardSchemeCoefficientCoherence

variable {A : ArchitectureObject U} {S : Site.AATSite A}
variable {k k' k'' : Type v}
variable [CommRing k] [CommRing k'] [CommRing k'']
variable (raw : LawAlgebra.RawAmbientRestrictionSystem S k)
variable [HasSheafify S.topology (LawAlgebra.AATCommAlgCat k)]
variable [HasSheafify S.topology (LawAlgebra.AATCommAlgCat k')]
variable [HasSheafify S.topology (LawAlgebra.AATCommAlgCat k'')]
variable (X : LawAlgebra.StandardArchitectureScheme raw)
variable (f : FlatCoefficientChange k k')
variable (g : FlatCoefficientChange k' k'')
variable [hf : S.topology.HasSheafCompose
  (f.coefficientExtension :
    LawAlgebra.AATCommAlgCat.{u, v} k ⥤
      LawAlgebra.AATCommAlgCat.{u, v} k')]
variable [hg : S.topology.HasSheafCompose
  (g.coefficientExtension :
    LawAlgebra.AATCommAlgCat.{u, v} k' ⥤
      LawAlgebra.AATCommAlgCat.{u, v} k'')]

/-- Fixed unit isomorphism for identity coefficient change. -/
noncomputable example :
    (X.baseChange raw (FlatCoefficientChange.refl k)).underlying ≅
      X.underlying :=
  X.baseChangeIdIso raw

/-- Fixed actual projection formula for identity coefficient change. -/
example :
    X.baseChangeMap raw (FlatCoefficientChange.refl k) =
      (X.baseChangeIdIso raw).hom :=
  X.baseChangeMap_id raw

/-- Fixed compositor between successive and composite coefficient change. -/
noncomputable example :
    letI : S.topology.HasSheafCompose
        ((f.comp g).coefficientExtension :
          LawAlgebra.AATCommAlgCat.{u, v} k ⥤
            LawAlgebra.AATCommAlgCat.{u, v} k'') :=
      FlatCoefficientChange.coefficientExtension_hasSheafCompose_comp
        f g hf hg
    ((X.baseChange raw f).baseChange
        (raw.baseChange f.hom) g).underlying ≅
      (X.baseChange raw (f.comp g)).underlying :=
  X.baseChangeCompIso raw f g

/-- Fixed actual morphism equality for composite coefficient change. -/
example :
    letI : S.topology.HasSheafCompose
        ((f.comp g).coefficientExtension :
          LawAlgebra.AATCommAlgCat.{u, v} k ⥤
            LawAlgebra.AATCommAlgCat.{u, v} k'') :=
      FlatCoefficientChange.coefficientExtension_hasSheafCompose_comp
        f g hf hg
    (X.baseChangeCompIso raw f g).hom ≫
        X.baseChangeMap raw (f.comp g) =
      (X.baseChange raw f).baseChangeMap
          (raw.baseChange f.hom) g ≫
        X.baseChangeMap raw f :=
  X.baseChangeMap_comp raw f g

end StandardSchemeCoefficientCoherence

/-! Semantic-core coefficient-change reading contracts. -/

section SemanticCoreCoefficientGeometry

open AlgebraicGeometry

variable {A : ArchitectureObject U} {S : Site.AATSite A}
variable {k k' : Type v} [CommRing k] [CommRing k']
variable (raw : LawAlgebra.RawAmbientRestrictionSystem S k)
variable [HasSheafify S.topology (LawAlgebra.AATCommAlgCat k)]
variable [HasSheafify S.topology (LawAlgebra.AATCommAlgCat k')]
variable (X : LawAlgebra.StandardArchitectureScheme raw)
variable (G : LawAlgebra.SemanticLawEquationWitnessIdealCore S)
variable (B : LawAlgebra.SemanticLawEquationSchemeBridge raw G)
variable (f : FlatCoefficientChange k k')
variable [S.topology.HasSheafCompose
  (f.coefficientExtension :
    LawAlgebra.AATCommAlgCat.{u, v} k ⥤
      LawAlgebra.AATCommAlgCat.{u, v} k')]

/-- Fixed transport of one source semantic-core equation by the actual change map. -/
noncomputable example
    (i : S.lawUniverse.Index) (a : U.Atom) :
    Γ((X.baseChange raw f).underlying, ⊤) :=
  LawAlgebra.baseChangedSemanticCoreGlobalEquation raw X G B f i a

/-- Fixed target closed-equational reading generated by the transported equations. -/
noncomputable example :
    LawAlgebra.ClosedEquationalLawReading
      (raw.baseChange f.hom) (X.baseChange raw f) :=
  LawAlgebra.ClosedEquationalLawReading.baseChangeOfSemanticCore
    raw X G B f

/-- Fixed comparison of target vanishing with source vanishing after projection. -/
example
    {T : AlgebraicGeometry.Scheme}
    (s : T ⟶ (X.baseChange raw f).underlying)
    (i : S.lawUniverse.Index) :
    (LawAlgebra.ClosedEquationalLawReading.baseChangeOfSemanticCore
      raw X G B f).geometric.HoldsOn s i ↔
      (LawAlgebra.ClosedEquationalLawReading.ofSemanticCore
        raw X G B).geometric.HoldsOn
          (s ≫ X.baseChangeMap raw f) i :=
  LawAlgebra.ClosedEquationalLawReading.baseChangeOfSemanticCore_geometric_iff
    raw X G B f s i

/-- Fixed validity of the target reading and its canonical witnesses. -/
example :
    LawAlgebra.IsClosedEquationalLawReading
      (raw.baseChange f.hom) (X.baseChange raw f)
      (LawAlgebra.ClosedEquationalLawReading.baseChangeOfSemanticCore
        raw X G B f) :=
  LawAlgebra.ClosedEquationalLawReading.baseChangeOfSemanticCore_valid
    raw X G B f

/-- Fixed required-law closure and selection of the target reading. -/
example :
    LawAlgebra.RequiredClosed
      (raw.baseChange f.hom) (X.baseChange raw f)
      (LawAlgebra.ClosedEquationalLawReading.baseChangeOfSemanticCore
        raw X G B f) :=
  LawAlgebra.ClosedEquationalLawReading.baseChangeOfSemanticCore_requiredClosed
    raw X G B f

/-- Fixed all-law closure and selection of the target reading. -/
example :
    LawAlgebra.AllLawsSelected
      (raw.baseChange f.hom) (X.baseChange raw f)
      (LawAlgebra.ClosedEquationalLawReading.baseChangeOfSemanticCore
        raw X G B f) :=
  LawAlgebra.ClosedEquationalLawReading.baseChangeOfSemanticCore_allLawsSelected
    raw X G B f

/-! Fixed per-law chart ideal comparison after coefficient change. -/

example
    (hB : LawAlgebra.IsSemanticLawEquationSchemeBridge raw G B)
    (j : X.atlas.Index)
    (i : S.lawUniverse.Index) :
    let R' := LawAlgebra.ClosedEquationalLawReading.baseChangeOfSemanticCore
      raw X G B f
    let hR' :=
      (LawAlgebra.ClosedEquationalLawReading.baseChangeOfSemanticCore_valid
        raw X G B f).witness_compatible
    let j' := cast (X.baseChangedAtlas_Index raw f).symm j
    Scheme.IdealSheafData.comap
        (Scheme.IdealSheafData.ofIdealTop
          (X := (X.atlas.chart j).domain)
          (Ideal.map
            (AlgebraicGeometry.Scheme.ΓSpecIso
              (LawAlgebra.SheafifiedSectionRing raw
                (X.atlas.chart j).context)).inv.hom
            (Ideal.map
              (B.toSheafifiedSection (X.atlas.chart j).context)
              (G.lawWitnessIdeal (X.atlas.chart j).context i))))
        (X.baseChangedChartMap raw f j) =
      Scheme.IdealSheafData.comap
        (LawAlgebra.lawWitnessIdealSheaf
          (raw.baseChange f.hom) (X.baseChange raw f)
          R' hR' i (Set.mem_univ i))
        ((X.baseChangedAtlas raw f).chart j').map :=
  LawAlgebra.semanticCoreLawWitnessIdeal_baseChangedChart
    raw X G B hB f j i

/-! Fixed AC33 aggregate ideal and lawful closed-geometry contracts. -/

example :
    Scheme.IdealSheafData.comap
        (LawAlgebra.lawGeneratedIdealSheaf raw X
          (LawAlgebra.ClosedEquationalLawReading.ofSemanticCore raw X G B)
          (LawAlgebra.ClosedEquationalLawReading.ofSemanticCore_valid raw X G B)
          (LawAlgebra.ClosedEquationalLawReading.ofSemanticCore_requiredClosed raw X G B))
        (X.baseChangeMap raw f) =
      LawAlgebra.lawGeneratedIdealSheaf
        (raw.baseChange f.hom) (X.baseChange raw f)
        (LawAlgebra.ClosedEquationalLawReading.baseChangeOfSemanticCore raw X G B f)
        (LawAlgebra.ClosedEquationalLawReading.baseChangeOfSemanticCore_valid raw X G B f)
        (LawAlgebra.ClosedEquationalLawReading.baseChangeOfSemanticCore_requiredClosed
          raw X G B f) :=
  LawAlgebra.lawGeneratedIdealSheaf_baseChange_ofSemanticCore raw X G B f

example :
    Scheme.IdealSheafData.comap
        (LawAlgebra.allLawGeneratedIdealSheaf raw X
          (LawAlgebra.ClosedEquationalLawReading.ofSemanticCore raw X G B)
          (LawAlgebra.ClosedEquationalLawReading.ofSemanticCore_valid raw X G B))
        (X.baseChangeMap raw f) =
      LawAlgebra.allLawGeneratedIdealSheaf
        (raw.baseChange f.hom) (X.baseChange raw f)
        (LawAlgebra.ClosedEquationalLawReading.baseChangeOfSemanticCore raw X G B f)
        (LawAlgebra.ClosedEquationalLawReading.baseChangeOfSemanticCore_valid raw X G B f) :=
  LawAlgebra.allSelectedLawGeneratedIdealSheaf_baseChange_ofSemanticCore raw X G B f

noncomputable example :
    LawAlgebra.lawfulClosedSubscheme
        (raw.baseChange f.hom) (X.baseChange raw f)
        (LawAlgebra.ClosedEquationalLawReading.baseChangeOfSemanticCore raw X G B f)
        (LawAlgebra.ClosedEquationalLawReading.baseChangeOfSemanticCore_valid raw X G B f)
        (LawAlgebra.ClosedEquationalLawReading.baseChangeOfSemanticCore_requiredClosed
          raw X G B f) ⟶
      LawAlgebra.lawfulClosedSubscheme raw X
        (LawAlgebra.ClosedEquationalLawReading.ofSemanticCore raw X G B)
        (LawAlgebra.ClosedEquationalLawReading.ofSemanticCore_valid raw X G B)
        (LawAlgebra.ClosedEquationalLawReading.ofSemanticCore_requiredClosed raw X G B) :=
  LawAlgebra.lawfulClosedSubschemeBaseChangeMap raw X G B f

example :
    LawAlgebra.lawfulClosedSubschemeBaseChangeMap raw X G B f ≫
        LawAlgebra.lawfulClosedImmersion raw X
          (LawAlgebra.ClosedEquationalLawReading.ofSemanticCore raw X G B)
          (LawAlgebra.ClosedEquationalLawReading.ofSemanticCore_valid raw X G B)
          (LawAlgebra.ClosedEquationalLawReading.ofSemanticCore_requiredClosed raw X G B) =
      LawAlgebra.lawfulClosedImmersion
        (raw.baseChange f.hom) (X.baseChange raw f)
        (LawAlgebra.ClosedEquationalLawReading.baseChangeOfSemanticCore raw X G B f)
        (LawAlgebra.ClosedEquationalLawReading.baseChangeOfSemanticCore_valid raw X G B f)
        (LawAlgebra.ClosedEquationalLawReading.baseChangeOfSemanticCore_requiredClosed
          raw X G B f) ≫ X.baseChangeMap raw f :=
  LawAlgebra.lawfulClosedSubschemeBaseChangeMap_immersion raw X G B f

noncomputable example :
    LawAlgebra.allLawfulClosedSubscheme
        (raw.baseChange f.hom) (X.baseChange raw f)
        (LawAlgebra.ClosedEquationalLawReading.baseChangeOfSemanticCore raw X G B f)
        (LawAlgebra.ClosedEquationalLawReading.baseChangeOfSemanticCore_valid raw X G B f) ⟶
      LawAlgebra.allLawfulClosedSubscheme raw X
        (LawAlgebra.ClosedEquationalLawReading.ofSemanticCore raw X G B)
        (LawAlgebra.ClosedEquationalLawReading.ofSemanticCore_valid raw X G B) :=
  LawAlgebra.allLawfulClosedSubschemeBaseChangeMap raw X G B f

example :
    LawAlgebra.allLawfulClosedSubschemeBaseChangeMap raw X G B f ≫
        LawAlgebra.allLawfulClosedImmersion raw X
          (LawAlgebra.ClosedEquationalLawReading.ofSemanticCore raw X G B)
          (LawAlgebra.ClosedEquationalLawReading.ofSemanticCore_valid raw X G B) =
      LawAlgebra.allLawfulClosedImmersion
        (raw.baseChange f.hom) (X.baseChange raw f)
        (LawAlgebra.ClosedEquationalLawReading.baseChangeOfSemanticCore raw X G B f)
        (LawAlgebra.ClosedEquationalLawReading.baseChangeOfSemanticCore_valid raw X G B f) ≫
        X.baseChangeMap raw f :=
  LawAlgebra.allLawfulClosedSubschemeBaseChangeMap_immersion raw X G B f

end SemanticCoreCoefficientGeometry

end CoefficientChangeSD6

namespace CoefficientChangeSD7

open scoped ChangeOfRings

/-! Fixed AC34 generic affine Tor base-change contracts. -/

noncomputable example
    {R R' : Type u}
    [CommRing R] [CommRing R']
    (f : FlatCoefficientChange R R')
    (M : ModuleCat.{max u v} R) :
    ModuleCat.{max u v} R' :=
  Derived.Intersection.moduleScalarExtension f M

noncomputable example
    {R R' : Type u}
    [CommRing R] [CommRing R']
    (f : FlatCoefficientChange R R')
    (M : ModuleCat.{max u v} R) :
    M ⟶ (ModuleCat.restrictScalars f.hom).obj
      (Derived.Intersection.moduleScalarExtension f M) :=
  Derived.Intersection.moduleScalarExtensionUnit f M

example
    {R R' : Type u}
    [CommRing R] [CommRing R']
    (f : FlatCoefficientChange R R')
    (M : ModuleCat.{max u v} R) (m : M) :
    Derived.Intersection.moduleScalarExtensionUnit f M m =
      (1 : R') ⊗ₜ[R, f.hom] m :=
  Derived.Intersection.moduleScalarExtensionUnit_apply f M m

noncomputable example
    {R : Type u} [CommRing R]
    (M : ModuleCat.{max u v} R) :
    Derived.Intersection.moduleScalarExtension
        (FlatCoefficientChange.refl R) M ≅ M :=
  Derived.Intersection.moduleScalarExtensionIdIso M

noncomputable example
    {R R' R'' : Type u}
    [CommRing R] [CommRing R'] [CommRing R'']
    (f : FlatCoefficientChange R R')
    (g : FlatCoefficientChange R' R'')
    (M : ModuleCat.{max u v} R) :
    Derived.Intersection.moduleScalarExtension g
        (Derived.Intersection.moduleScalarExtension f M) ≅
      Derived.Intersection.moduleScalarExtension (f.comp g) M :=
  Derived.Intersection.moduleScalarExtensionCompIso f g M

noncomputable example
    {R R' : Type v}
    [CommRing R] [CommRing R']
    (f : FlatCoefficientChange R R')
    (I J : Ideal R) (n : Nat) :
    Derived.Intersection.moduleScalarExtension f
        (Derived.Intersection.mathlibTor R I J n) ≅
      Derived.Intersection.mathlibTor R'
        (I.map f.hom) (J.map f.hom) n :=
  Derived.Intersection.mathlibTorFlatBaseChangeIso f I J n

end CoefficientChangeSD7

namespace CoefficientChangeSD8

open CategoryTheory Opposite
open scoped ChangeOfRings

variable {A : ArchitectureObject U}
variable {S : Site.AATSite A}

/-! Fixed AC37 canonical linear-coefficient base-change contracts. -/

example
    {R : Type u} [CommRing R]
    (P : S.categoryᵒᵖ ⥤ ModuleCat.{u + 1} R)
    (hP : Presheaf.IsSheaf S.topology
      (P ⋙ forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1})) :
    Cohomology.LinearCoefficientSheaf R S :=
  ⟨P, hP⟩

noncomputable example
    {R : Type u} [CommRing R]
    (Ob : Cohomology.LinearCoefficientSheaf R S) :
    Sheaf S.topology AddCommGrpCat.{u + 1} :=
  Ob.toAddCommGrpSheaf

noncomputable example
    {R : Type u} [CommRing R]
    (P : S.categoryᵒᵖ ⥤ ModuleCat.{u + 1} R)
    [HasSheafify S.topology AddCommGrpCat.{u + 1}] :
    Cohomology.LinearCoefficientSheaf R S :=
  Cohomology.LinearCoefficientSheaf.moduleSheafification P

noncomputable example
    {R R' : Type u} [CommRing R] [CommRing R']
    (Ob : Cohomology.LinearCoefficientSheaf R S)
    (f : FlatCoefficientChange R R') :
    S.categoryᵒᵖ ⥤ ModuleCat.{u + 1} R' :=
  Ob.rawBaseChangePresheaf f

noncomputable example
    {R R' : Type u} [CommRing R] [CommRing R']
    (Ob : Cohomology.LinearCoefficientSheaf R S)
    (f : FlatCoefficientChange R R')
    [HasSheafify S.topology AddCommGrpCat.{u + 1}] :
    Cohomology.LinearCoefficientSheaf R' S :=
  Ob.baseChange f

noncomputable example
    {R : Type u} [CommRing R]
    (Ob : Cohomology.LinearCoefficientSheaf R S)
    [HasSheafify S.topology AddCommGrpCat.{u + 1}] :
    (Ob.baseChange (FlatCoefficientChange.refl R)).modulePresheaf ≅
      Ob.modulePresheaf :=
  Ob.baseChangeIdIso

noncomputable example
    {R R' R'' : Type u}
    [CommRing R] [CommRing R'] [CommRing R'']
    (Ob : Cohomology.LinearCoefficientSheaf R S)
    (f : FlatCoefficientChange R R')
    (g : FlatCoefficientChange R' R'')
    [HasSheafify S.topology AddCommGrpCat.{u + 1}] :
    ((Ob.baseChange f).baseChange g).modulePresheaf ≅
      (Ob.baseChange (f.comp g)).modulePresheaf :=
  Ob.baseChangeCompIso f g

noncomputable example
    {R R' : Type u} [CommRing R] [CommRing R']
    (f : FlatCoefficientChange R R')
    (M : ModuleCat.{u + 1} R) :
    ModuleCat.{u + 1} R' :=
  Cohomology.LinearCoefficientSheaf.moduleScalarExtension f M

noncomputable example
    {R R' : Type u} [CommRing R] [CommRing R']
    (Ob : Cohomology.LinearCoefficientSheaf R S)
    (f : FlatCoefficientChange R R')
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (W : S.category) :
    Cohomology.LinearCoefficientSheaf.moduleScalarExtension f
        (Ob.modulePresheaf.obj (op W)) ⟶
      (Ob.baseChange f).modulePresheaf.obj (op W) :=
  Ob.baseChangeSectionMap f W

example
    {R R' : Type u} [CommRing R] [CommRing R']
    (Ob : Cohomology.LinearCoefficientSheaf R S)
    (f : FlatCoefficientChange R R')
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    {source target : S.category} (g : source ⟶ target) :
    (ModuleCat.extendScalars f.hom).map
          (Ob.modulePresheaf.map g.op) ≫
        Ob.baseChangeSectionMap f source =
      Ob.baseChangeSectionMap f target ≫
        (Ob.baseChange f).modulePresheaf.map g.op :=
  Ob.baseChangeSectionMap_naturality f g

/-- Fixed identity coherence for the canonical section map. -/
example
    {R : Type u} [CommRing R]
    (Ob : Cohomology.LinearCoefficientSheaf R S)
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (W : S.category) :
    Ob.baseChangeSectionMap (FlatCoefficientChange.refl R) W ≫
        (Ob.baseChangeIdIso).hom.app (op W) =
      (ModuleCat.extendScalarsId.{u, u + 1} R).hom.app
        (Ob.modulePresheaf.obj (op W)) :=
  Ob.baseChangeSectionMap_id W

/-- Fixed composition coherence for the canonical section map. -/
example
    {R R' R'' : Type u}
    [CommRing R] [CommRing R'] [CommRing R'']
    (Ob : Cohomology.LinearCoefficientSheaf R S)
    (f : FlatCoefficientChange R R')
    (g : FlatCoefficientChange R' R'')
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (W : S.category) :
    (ModuleCat.extendScalars g.hom).map
          (Ob.baseChangeSectionMap f W) ≫
        (Ob.baseChange f).baseChangeSectionMap g W ≫
        (Ob.baseChangeCompIso f g).hom.app (op W) =
      (ModuleCat.extendScalarsComp.{u, u + 1}
          f.hom g.hom).symm.hom.app
          (Ob.modulePresheaf.obj (op W)) ≫
        Ob.baseChangeSectionMap (f.comp g) W :=
  Ob.baseChangeSectionMap_comp f g W

/-! Fixed AC36 canonical linear Čech and flat homology contracts. -/

example
    {R : Type u} [CommRing R]
    {base : S.category}
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (Ob : Cohomology.LinearCoefficientSheaf R S)
    (K : CochainComplex (ModuleCat.{u + 1} R) Nat)
    (e : ∀ n, K.X n ≅
      ModuleCat.of R
        (∀ σ : (Cohomology.canonicalCoverRelative 𝒰).simplex n,
          Ob.modulePresheaf.obj
            (op ((Cohomology.canonicalCoverRelative 𝒰).overlap n σ)))) :
    Cohomology.LinearCoverRelativeCechComplex R 𝒰 Ob :=
  ⟨K, e⟩

noncomputable example
    {R : Type u} [CommRing R]
    {base : S.category}
    (Ob : Cohomology.LinearCoefficientSheaf R S)
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (n : Nat) :
    ModuleCat.of R
        (∀ σ : (Cohomology.canonicalCoverRelative 𝒰).simplex n,
          Ob.modulePresheaf.obj
            (op ((Cohomology.canonicalCoverRelative 𝒰).overlap n σ))) ⟶
      ModuleCat.of R
        (∀ σ : (Cohomology.canonicalCoverRelative 𝒰).simplex (n + 1),
          Ob.modulePresheaf.obj
            (op ((Cohomology.canonicalCoverRelative 𝒰).overlap (n + 1) σ))) :=
  Cohomology.linearCechDifferential Ob 𝒰 n

noncomputable example
    {R : Type u} [CommRing R]
    {base : S.category}
    (Ob : Cohomology.LinearCoefficientSheaf R S)
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base) :
    Cohomology.LinearCoverRelativeCechComplex R 𝒰 Ob :=
  Ob.canonicalLinearCech 𝒰

example
    {R : Type u} [CommRing R]
    {base : S.category}
    (Ob : Cohomology.LinearCoefficientSheaf R S)
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (n : Nat) :
    (Ob.canonicalLinearCech 𝒰).complex.d n (n + 1) =
      ((Ob.canonicalLinearCech 𝒰).cochainIso n).hom ≫
        Cohomology.linearCechDifferential Ob 𝒰 n ≫
        ((Ob.canonicalLinearCech 𝒰).cochainIso (n + 1)).inv :=
  Ob.canonicalLinearCech_d 𝒰 n

noncomputable example
    {R R' : Type u} [CommRing R] [CommRing R']
    {base : S.category}
    {𝒰 : Site.AATCoverageFamily S.requirements S.overlap base}
    {Ob : Cohomology.LinearCoefficientSheaf R S}
    (K : Cohomology.LinearCoverRelativeCechComplex R 𝒰 Ob)
    (f : FlatCoefficientChange R R') :
    CochainComplex (ModuleCat.{u + 1} R') Nat :=
  K.scalarExtension f

noncomputable example
    {R R' : Type u} [CommRing R] [CommRing R']
    {base : S.category}
    {𝒰 : Site.AATCoverageFamily S.requirements S.overlap base}
    {Ob : Cohomology.LinearCoefficientSheaf R S}
    (K : Cohomology.LinearCoverRelativeCechComplex R 𝒰 Ob)
    (f : FlatCoefficientChange R R')
    (n : Nat) :
    (K.scalarExtension f).X n ≅
      Cohomology.LinearCoefficientSheaf.moduleScalarExtension f
        (K.complex.X n) :=
  K.scalarExtensionObjIso f n

noncomputable example
    {R R' : Type u} [CommRing R] [CommRing R']
    {base : S.category}
    {𝒰 : Site.AATCoverageFamily S.requirements S.overlap base}
    {Ob : Cohomology.LinearCoefficientSheaf R S}
    (K : Cohomology.LinearCoverRelativeCechComplex R 𝒰 Ob)
    (f : FlatCoefficientChange R R')
    (n : Nat) :
    K.complex.X n ⟶
      (ModuleCat.restrictScalars f.hom).obj ((K.scalarExtension f).X n) :=
  K.scalarExtensionCochain f n

example
    {R R' : Type u} [CommRing R] [CommRing R']
    {base : S.category}
    {𝒰 : Site.AATCoverageFamily S.requirements S.overlap base}
    {Ob : Cohomology.LinearCoefficientSheaf R S}
    (K : Cohomology.LinearCoverRelativeCechComplex R 𝒰 Ob)
    (f : FlatCoefficientChange R R')
    (n : Nat) :
    K.scalarExtensionCochain f n ≫
        (ModuleCat.restrictScalars f.hom).map
          (K.scalarExtensionObjIso f n).hom =
      Derived.Intersection.moduleScalarExtensionUnit.{u, u + 1}
        f (K.complex.X n) :=
  K.scalarExtensionCochain_objIso f n

example
    {R R' : Type u} [CommRing R] [CommRing R']
    {base : S.category}
    {𝒰 : Site.AATCoverageFamily S.requirements S.overlap base}
    {Ob : Cohomology.LinearCoefficientSheaf R S}
    (K : Cohomology.LinearCoverRelativeCechComplex R 𝒰 Ob)
    (f : FlatCoefficientChange R R')
    (n : Nat) :
    (K.scalarExtension f).d n (n + 1) ≫
        (K.scalarExtensionObjIso f (n + 1)).hom =
      (K.scalarExtensionObjIso f n).hom ≫
        (ModuleCat.extendScalars f.hom).map
          (K.complex.d n (n + 1)) :=
  K.scalarExtension_d f n

noncomputable example
    {R R' : Type u} [CommRing R] [CommRing R']
    {base : S.category}
    {𝒰 : Site.AATCoverageFamily S.requirements S.overlap base}
    {Ob : Cohomology.LinearCoefficientSheaf R S}
    (K : Cohomology.LinearCoverRelativeCechComplex R 𝒰 Ob)
    (f : FlatCoefficientChange R R')
    (n : Nat) :
    Cohomology.LinearCoefficientSheaf.moduleScalarExtension f
        (K.complex.homology n) ≅
      (K.scalarExtension f).homology n :=
  K.hnFlatBaseChangeIso f n

noncomputable example
    {R R' : Type u} [CommRing R] [CommRing R']
    {base : S.category}
    {𝒰 : Site.AATCoverageFamily S.requirements S.overlap base}
    {Ob : Cohomology.LinearCoefficientSheaf R S}
    (K : Cohomology.LinearCoverRelativeCechComplex R 𝒰 Ob)
    (f : FlatCoefficientChange R R')
    (n : Nat) :
    K.complex.cycles n →
      (K.scalarExtension f).homology n :=
  K.classBaseChange f n

example
    {R R' : Type u} [CommRing R] [CommRing R']
    {base : S.category}
    {𝒰 : Site.AATCoverageFamily S.requirements S.overlap base}
    {Ob : Cohomology.LinearCoefficientSheaf R S}
    (K : Cohomology.LinearCoverRelativeCechComplex R 𝒰 Ob)
    (f : FlatCoefficientChange R R')
    (n : Nat)
    (c : K.complex.cycles n) :
    (K.hnFlatBaseChangeIso f n).hom
        (Derived.Intersection.moduleScalarExtensionUnit.{u, u + 1} f
          (K.complex.homology n) (K.complex.homologyπ n c)) =
      K.classBaseChange f n c :=
  K.class_baseChange_naturality f n c

/-! Fixed AC37 canonical coefficient Čech comparison contracts. -/

noncomputable example
    {R R' : Type u} [CommRing R] [CommRing R']
    (Ob : Cohomology.LinearCoefficientSheaf R S)
    (f : FlatCoefficientChange R R')
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    {base : S.category}
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (n : Nat) :
    ((Ob.canonicalLinearCech 𝒰).scalarExtension f).X n ⟶
      ((Ob.baseChange f).canonicalLinearCech 𝒰).complex.X n :=
  Ob.canonicalBaseChangeCochain f 𝒰 n

noncomputable example
    {R R' : Type u} [CommRing R] [CommRing R']
    (Ob : Cohomology.LinearCoefficientSheaf R S)
    (f : FlatCoefficientChange R R')
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    {base : S.category}
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base) :
    (Ob.canonicalLinearCech 𝒰).scalarExtension f ⟶
      ((Ob.baseChange f).canonicalLinearCech 𝒰).complex :=
  Ob.canonicalCechBaseChangeHom f 𝒰

example
    {R R' : Type u} [CommRing R] [CommRing R']
    (Ob : Cohomology.LinearCoefficientSheaf R S)
    (f : FlatCoefficientChange R R')
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    {base : S.category}
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (n : Nat) :
    (Ob.canonicalCechBaseChangeHom f 𝒰).f n =
      Ob.canonicalBaseChangeCochain f 𝒰 n :=
  Ob.canonicalCechBaseChangeHom_f f 𝒰 n

example
    {R R' : Type u} [CommRing R] [CommRing R']
    (Ob : Cohomology.LinearCoefficientSheaf R S)
    (f : FlatCoefficientChange R R')
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    {base : S.category}
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base) : Prop :=
  Ob.CechCoefficientBaseChangeCompatible f 𝒰

noncomputable example
    {R R' : Type u} [CommRing R] [CommRing R']
    (Ob : Cohomology.LinearCoefficientSheaf R S)
    (f : FlatCoefficientChange R R')
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    {base : S.category}
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (n : Nat) :
    Cohomology.LinearCoefficientSheaf.moduleScalarExtension f
        ((Ob.canonicalLinearCech 𝒰).complex.homology n) ⟶
      ((Ob.baseChange f).canonicalLinearCech 𝒰).complex.homology n :=
  Ob.canonicalCechHnBaseChangeMap f 𝒰 n

noncomputable example
    {R R' : Type u} [CommRing R] [CommRing R']
    (Ob : Cohomology.LinearCoefficientSheaf R S)
    (f : FlatCoefficientChange R R')
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    {base : S.category}
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (n : Nat) :
    (Ob.canonicalLinearCech 𝒰).complex.cycles n →
      ((Ob.baseChange f).canonicalLinearCech 𝒰).complex.cycles n :=
  Ob.canonicalCocycleBaseChange f 𝒰 n

example
    {R R' : Type u} [CommRing R] [CommRing R']
    (Ob : Cohomology.LinearCoefficientSheaf R S)
    (f : FlatCoefficientChange R R')
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    {base : S.category}
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (n : Nat)
    (c : (Ob.canonicalLinearCech 𝒰).complex.cycles n) :
    ((Ob.baseChange f).canonicalLinearCech 𝒰).complex.homologyπ n
        (Ob.canonicalCocycleBaseChange f 𝒰 n c) =
      Ob.canonicalCechHnBaseChangeMap f 𝒰 n
        (Derived.Intersection.moduleScalarExtensionUnit.{u, u + 1} f
          ((Ob.canonicalLinearCech 𝒰).complex.homology n)
          ((Ob.canonicalLinearCech 𝒰).complex.homologyπ n c)) :=
  Ob.canonicalCocycleBaseChange_class f 𝒰 n c

example
    {R R' : Type u} [CommRing R] [CommRing R']
    (Ob : Cohomology.LinearCoefficientSheaf R S)
    (f : FlatCoefficientChange R R')
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    {base : S.category}
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (hcompat : Ob.CechCoefficientBaseChangeCompatible f 𝒰)
    (n : Nat) :
    IsIso (Ob.canonicalCechHnBaseChangeMap f 𝒰 n) :=
  Ob.canonicalCechHnBaseChangeMap_isIso f 𝒰 hcompat n

noncomputable example
    {R R' : Type u} [CommRing R] [CommRing R']
    (Ob : Cohomology.LinearCoefficientSheaf R S)
    (f : FlatCoefficientChange R R')
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    {base : S.category}
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (hcompat : Ob.CechCoefficientBaseChangeCompatible f 𝒰)
    (n : Nat) :
    Cohomology.LinearCoefficientSheaf.moduleScalarExtension f
        ((Ob.canonicalLinearCech 𝒰).complex.homology n) ≅
      ((Ob.baseChange f).canonicalLinearCech 𝒰).complex.homology n :=
  Ob.canonicalCechHnFlatBaseChangeIso f 𝒰 hcompat n

end CoefficientChangeSD8

namespace LinearLerayComparisonSD8d

open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings

variable {A : ArchitectureObject U}
variable {S : Site.AATSite A} {base : S.category}

/-- Fixed generic Leray predicate specialized to a linear coefficient sheaf. -/
example
    {R : Type u} [CommRing R]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (Ob : Cohomology.LinearCoefficientSheaf R S)
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 2} (Sheaf S.topology AddCommGrpCat.{u + 1})] : Prop :=
  Ob.IsLinearLerayFor 𝒰

/-- Fixed transported module structure on actual terminal sheaf cohomology. -/
noncomputable example
    {R : Type u} [CommRing R]
    (Ob : Cohomology.LinearCoefficientSheaf R S)
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 2} (Sheaf S.topology AddCommGrpCat.{u + 1})]
    (hbase : IsTerminal base)
    (hLeray : Ob.IsLinearLerayFor 𝒰)
    (n : Nat) : ModuleCat.{u + 2} R :=
  Ob.terminalLerayHModule 𝒰 hbase hLeray n

/-- Fixed carrier identity for the transported terminal cohomology module. -/
example
    {R : Type u} [CommRing R]
    (Ob : Cohomology.LinearCoefficientSheaf R S)
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 2} (Sheaf S.topology AddCommGrpCat.{u + 1})]
    (hbase : IsTerminal base)
    (hLeray : Ob.IsLinearLerayFor 𝒰)
    (n : Nat) :
    (Ob.terminalLerayHModule 𝒰 hbase hLeray n : Type (u + 2)) =
      (Ob.toAddCommGrpSheaf).H n :=
  Ob.terminalLerayHModule_carrier 𝒰 hbase hLeray n

/-- Fixed linear Čech-to-actual-terminal-cohomology equivalence. -/
noncomputable example
    {R : Type u} [CommRing R]
    (Ob : Cohomology.LinearCoefficientSheaf R S)
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 2} (Sheaf S.topology AddCommGrpCat.{u + 1})]
    (hbase : IsTerminal base)
    (hLeray : Ob.IsLinearLerayFor 𝒰)
    (n : Nat) :
    (Ob.canonicalLinearCech 𝒰).complex.homology n ≃ₗ[R]
      Ob.terminalLerayHModule 𝒰 hbase hLeray n :=
  Ob.cechToSheafHLinearIso 𝒰 hbase hLeray n

/-- Fixed actual-`Sheaf.H` flat base-change map. -/
noncomputable example
    {R R' : Type u} [CommRing R] [CommRing R']
    (Ob : Cohomology.LinearCoefficientSheaf R S)
    (f : FlatCoefficientChange R R')
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 2} (Sheaf S.topology AddCommGrpCat.{u + 1})]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (hbase : IsTerminal base)
    (hsource : Ob.IsLinearLerayFor 𝒰)
    (htarget : (Ob.baseChange f).IsLinearLerayFor 𝒰)
    (n : Nat) :
    Derived.Intersection.moduleScalarExtension.{u, u + 2} f
        (Ob.terminalLerayHModule 𝒰 hbase hsource n) ⟶
      (Ob.baseChange f).terminalLerayHModule 𝒰 hbase htarget n :=
  Ob.sheafHFlatBaseChangeMap f 𝒰 hbase hsource htarget n

/-- Fixed pure-tensor formula for the actual-`Sheaf.H` base-change map. -/
example
    {R R' : Type u} [CommRing R] [CommRing R']
    (Ob : Cohomology.LinearCoefficientSheaf R S)
    (f : FlatCoefficientChange R R')
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 2} (Sheaf S.topology AddCommGrpCat.{u + 1})]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (hbase : IsTerminal base)
    (hsource : Ob.IsLinearLerayFor 𝒰)
    (htarget : (Ob.baseChange f).IsLinearLerayFor 𝒰)
    (n : Nat) (r' : R')
    (x : Ob.terminalLerayHModule 𝒰 hbase hsource n) :
    Ob.sheafHFlatBaseChangeMap f 𝒰 hbase hsource htarget n
        (r' ⊗ₜ[R, f.hom] x) =
      (Ob.baseChange f).cechToSheafHLinearIso 𝒰 hbase htarget n
        (Ob.canonicalCechHnBaseChangeMap f 𝒰 n
          (r' ⊗ₜ[R, f.hom]
            (Ob.cechToSheafHLinearIso 𝒰 hbase hsource n).symm x)) :=
  Ob.sheafHFlatBaseChangeMap_formula f 𝒰 hbase hsource htarget n r' x

/-- Fixed cohomology-class formula for the actual-`Sheaf.H` base-change map. -/
example
    {R R' : Type u} [CommRing R] [CommRing R']
    (Ob : Cohomology.LinearCoefficientSheaf R S)
    (f : FlatCoefficientChange R R')
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 2} (Sheaf S.topology AddCommGrpCat.{u + 1})]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (hbase : IsTerminal base)
    (hsource : Ob.IsLinearLerayFor 𝒰)
    (htarget : (Ob.baseChange f).IsLinearLerayFor 𝒰)
    (n : Nat)
    (c : (Ob.canonicalLinearCech 𝒰).complex.cycles n) :
    Ob.sheafHFlatBaseChangeMap f 𝒰 hbase hsource htarget n
        (Derived.Intersection.moduleScalarExtensionUnit.{u, u + 2} f
          (Ob.terminalLerayHModule 𝒰 hbase hsource n)
          (Ob.cechToSheafHLinearIso 𝒰 hbase hsource n
            ((Ob.canonicalLinearCech 𝒰).complex.homologyπ n c))) =
      (Ob.baseChange f).cechToSheafHLinearIso 𝒰 hbase htarget n
        (((Ob.baseChange f).canonicalLinearCech 𝒰).complex.homologyπ n
          (Ob.canonicalCocycleBaseChange f 𝒰 n c)) :=
  Ob.sheafHFlatBaseChangeMap_on_class f 𝒰 hbase hsource htarget n c

/-- Fixed isomorphism witness under Čech coefficient compatibility. -/
example
    {R R' : Type u} [CommRing R] [CommRing R']
    (Ob : Cohomology.LinearCoefficientSheaf R S)
    (f : FlatCoefficientChange R R')
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 2} (Sheaf S.topology AddCommGrpCat.{u + 1})]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (hbase : IsTerminal base)
    (hcompat : Ob.CechCoefficientBaseChangeCompatible f 𝒰)
    (hsource : Ob.IsLinearLerayFor 𝒰)
    (htarget : (Ob.baseChange f).IsLinearLerayFor 𝒰)
    (n : Nat) :
    IsIso (Ob.sheafHFlatBaseChangeMap f 𝒰 hbase hsource htarget n) :=
  Ob.sheafHFlatBaseChangeMap_isIso f 𝒰 hbase hcompat hsource htarget n

/-- Fixed actual-`Sheaf.H` flat base-change isomorphism. -/
noncomputable example
    {R R' : Type u} [CommRing R] [CommRing R']
    (Ob : Cohomology.LinearCoefficientSheaf R S)
    (f : FlatCoefficientChange R R')
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 2} (Sheaf S.topology AddCommGrpCat.{u + 1})]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (hbase : IsTerminal base)
    (hcompat : Ob.CechCoefficientBaseChangeCompatible f 𝒰)
    (hsource : Ob.IsLinearLerayFor 𝒰)
    (htarget : (Ob.baseChange f).IsLinearLerayFor 𝒰)
    (n : Nat) :
    Derived.Intersection.moduleScalarExtension.{u, u + 2} f
        (Ob.terminalLerayHModule 𝒰 hbase hsource n) ≅
      (Ob.baseChange f).terminalLerayHModule 𝒰 hbase htarget n :=
  Ob.sheafHFlatBaseChangeIso f 𝒰 hbase hcompat hsource htarget n

/-- Fixed identification of the base-change isomorphism's hom. -/
example
    {R R' : Type u} [CommRing R] [CommRing R']
    (Ob : Cohomology.LinearCoefficientSheaf R S)
    (f : FlatCoefficientChange R R')
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 2} (Sheaf S.topology AddCommGrpCat.{u + 1})]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (hbase : IsTerminal base)
    (hcompat : Ob.CechCoefficientBaseChangeCompatible f 𝒰)
    (hsource : Ob.IsLinearLerayFor 𝒰)
    (htarget : (Ob.baseChange f).IsLinearLerayFor 𝒰)
    (n : Nat) :
    (Ob.sheafHFlatBaseChangeIso f 𝒰 hbase hcompat hsource htarget n).hom =
      Ob.sheafHFlatBaseChangeMap f 𝒰 hbase hsource htarget n :=
  Ob.sheafHFlatBaseChangeIso_hom f 𝒰 hbase hcompat hsource htarget n

/-- Fixed identity comparison on transported terminal Leray cohomology. -/
noncomputable example
    {R : Type u} [CommRing R]
    (Ob : Cohomology.LinearCoefficientSheaf R S)
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 2} (Sheaf S.topology AddCommGrpCat.{u + 1})]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (hbase : IsTerminal base)
    (hsource : Ob.IsLinearLerayFor 𝒰)
    (htarget : (Ob.baseChange
      (FlatCoefficientChange.refl R)).IsLinearLerayFor 𝒰)
    (n : Nat) :
    (Ob.baseChange (FlatCoefficientChange.refl R)).terminalLerayHModule
        𝒰 hbase htarget n ≅
      Ob.terminalLerayHModule 𝒰 hbase hsource n :=
  Ob.baseChangeIdTerminalLerayHModuleIso
    𝒰 hbase hsource htarget n

/-- Fixed composition comparison on transported terminal Leray cohomology. -/
noncomputable example
    {R R' R'' : Type u}
    [CommRing R] [CommRing R'] [CommRing R'']
    (Ob : Cohomology.LinearCoefficientSheaf R S)
    (f : FlatCoefficientChange R R')
    (g : FlatCoefficientChange R' R'')
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 2} (Sheaf S.topology AddCommGrpCat.{u + 1})]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (hbase : IsTerminal base)
    (hiterated : ((Ob.baseChange f).baseChange g).IsLinearLerayFor 𝒰)
    (hcomposite : (Ob.baseChange (f.comp g)).IsLinearLerayFor 𝒰)
    (n : Nat) :
    ((Ob.baseChange f).baseChange g).terminalLerayHModule
        𝒰 hbase hiterated n ≅
      (Ob.baseChange (f.comp g)).terminalLerayHModule
        𝒰 hbase hcomposite n :=
  Ob.baseChangeCompTerminalLerayHModuleIso f g
    𝒰 hbase hiterated hcomposite n

/-- Fixed identity coherence of the actual-`Sheaf.H` base-change map. -/
example
    {R : Type u} [CommRing R]
    (Ob : Cohomology.LinearCoefficientSheaf R S)
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 2} (Sheaf S.topology AddCommGrpCat.{u + 1})]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (hbase : IsTerminal base)
    (hsource : Ob.IsLinearLerayFor 𝒰)
    (htarget : (Ob.baseChange
      (FlatCoefficientChange.refl R)).IsLinearLerayFor 𝒰)
    (n : Nat) :
    Ob.sheafHFlatBaseChangeMap (FlatCoefficientChange.refl R)
          𝒰 hbase hsource htarget n ≫
        (Ob.baseChangeIdTerminalLerayHModuleIso
          𝒰 hbase hsource htarget n).hom =
      (Derived.Intersection.moduleScalarExtensionIdIso.{u, u + 2}
        (Ob.terminalLerayHModule 𝒰 hbase hsource n)).hom :=
  Ob.sheafHFlatBaseChangeMap_id 𝒰 hbase hsource htarget n

/-- Fixed composition coherence of the actual-`Sheaf.H` base-change map. -/
example
    {R R' R'' : Type u}
    [CommRing R] [CommRing R'] [CommRing R'']
    (Ob : Cohomology.LinearCoefficientSheaf R S)
    (f : FlatCoefficientChange R R')
    (g : FlatCoefficientChange R' R'')
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 2} (Sheaf S.topology AddCommGrpCat.{u + 1})]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (hbase : IsTerminal base)
    (hsource : Ob.IsLinearLerayFor 𝒰)
    (hmiddle : (Ob.baseChange f).IsLinearLerayFor 𝒰)
    (hiterated : ((Ob.baseChange f).baseChange g).IsLinearLerayFor 𝒰)
    (hcomposite : (Ob.baseChange (f.comp g)).IsLinearLerayFor 𝒰)
    (n : Nat) :
    (ModuleCat.extendScalars g.hom).map
          (Ob.sheafHFlatBaseChangeMap f
            𝒰 hbase hsource hmiddle n) ≫
        (Ob.baseChange f).sheafHFlatBaseChangeMap g
          𝒰 hbase hmiddle hiterated n ≫
        (Ob.baseChangeCompTerminalLerayHModuleIso f g
          𝒰 hbase hiterated hcomposite n).hom =
      (Derived.Intersection.moduleScalarExtensionCompIso.{u, u + 2} f g
          (Ob.terminalLerayHModule 𝒰 hbase hsource n)).hom ≫
        Ob.sheafHFlatBaseChangeMap (f.comp g)
          𝒰 hbase hsource hcomposite n :=
  Ob.sheafHFlatBaseChangeMap_comp f g 𝒰 hbase hsource hmiddle
    hiterated hcomposite n

end LinearLerayComparisonSD8d

/-! ## SD9a: nonidentity exact finite core change -/

noncomputable example : AATCorePackage FiniteModel.carrier :=
  ReadingFunctorialityFinite.exactSourceCore

noncomputable example : AATCorePackage FiniteModel.carrier :=
  ReadingFunctorialityFinite.exactTargetCore

noncomputable example :
    SignedExactCoreReadingHom
      ReadingFunctorialityFinite.exactSourceCore
      ReadingFunctorialityFinite.exactTargetCore :=
  ReadingFunctorialityFinite.nonidentityExactCoreChange

example : ReadingFunctorialityFinite.nonidentityExactCoreChange.atomMap ≠ id :=
  ReadingFunctorialityFinite.nonidentityExactCoreChange_fires

/-! ## SD9b: positive-only finite core change -/

noncomputable example : AATCorePackage FiniteModel.carrier :=
  ReadingFunctorialityFinite.positiveSourceCore

noncomputable example : AATCorePackage FiniteModel.carrier :=
  ReadingFunctorialityFinite.positiveTargetCore

noncomputable example :
    PositiveCoreReadingHom
      ReadingFunctorialityFinite.positiveSourceCore
      ReadingFunctorialityFinite.positiveTargetCore :=
  ReadingFunctorialityFinite.positiveCoreChange

noncomputable example :
    ReadingFunctorialityFinite.positiveSourceCore.algebra.lawReading.lawUniverse.Index :=
  ReadingFunctorialityFinite.positiveLawIndex

noncomputable example :
    PositiveCircuitDatum ReadingFunctorialityFinite.positiveSourceCore
      ReadingFunctorialityFinite.positiveSourceCore.baseObject
      ReadingFunctorialityFinite.positiveLawIndex :=
  ReadingFunctorialityFinite.positiveCircuit

noncomputable example : CircuitQuery FiniteModel.carrier :=
  ReadingFunctorialityFinite.positiveQuery

example :
    (ReadingFunctorialityFinite.positiveQuery, true) ∈
      ReadingFunctorialityFinite.positiveCircuit.1.queries :=
  ReadingFunctorialityFinite.positiveQuery_mem

example : ReadingFunctorialityFinite.positiveCircuit.1.queries ≠ [] :=
  ReadingFunctorialityFinite.positiveCircuit_queries_nonempty

noncomputable example :
    PositiveCircuitDatum ReadingFunctorialityFinite.positiveTargetCore
      (ReadingFunctorialityFinite.positiveCoreChange.objMap
        ReadingFunctorialityFinite.positiveSourceCore.baseObject)
      (ReadingFunctorialityFinite.positiveCoreChange.lawMap
        ReadingFunctorialityFinite.positiveLawIndex) :=
  ReadingFunctorialityFinite.positiveCircuit_transport

example :
    ReadingFunctorialityFinite.positiveTargetCore.reading.operationReading.Reachable
      ReadingFunctorialityFinite.positiveTargetCore.object
      (ReadingFunctorialityFinite.positiveCoreChange.objectMap
        ReadingFunctorialityFinite.positiveSourceCore.object) :=
  ReadingFunctorialityFinite.positiveBase_target_reachable

example :
    ¬ Nonempty
      (SignedExactCoreReadingHom
        ReadingFunctorialityFinite.positiveSourceCore
        ReadingFunctorialityFinite.positiveTargetCore) :=
  ReadingFunctorialityFinite.positiveOnly_not_signedExact

noncomputable example : FiniteCircuitDatum FiniteModel.carrier :=
  ReadingFunctorialityFinite.negativeCircuit

example : ¬ ReadingFunctorialityFinite.negativeCircuit.Positive :=
  ReadingFunctorialityFinite.negativeCircuit_not_positive

example :
    ¬ ∃ target : FiniteCircuitDatum FiniteModel.carrier,
      ∀ A,
        ReadingFunctorialityFinite.negativeCircuit.Matches A ↔
          target.Matches
            (ReadingFunctorialityFinite.positiveCoreChange.objectMap A) :=
  ReadingFunctorialityFinite.negativeCircuit_not_transportable

/-! ## SD9e: coefficient arithmetic, raw data, and negative primitives -/

/-- Fixed positive coefficient change from integers to polynomials. -/
noncomputable example : FlatCoefficientChange Int (Polynomial Int) :=
  ReadingFunctorialityFinite.intPolynomialFlatChange

/-- Fixed identification of the positive coefficient homomorphism. -/
example :
    ReadingFunctorialityFinite.intPolynomialFlatChange.hom = Polynomial.C :=
  ReadingFunctorialityFinite.intPolynomialFlatChange_hom

/-- Fixed non-surjectivity firing for the positive coefficient change. -/
example :
    ¬ Function.Surjective
      ReadingFunctorialityFinite.intPolynomialFlatChange.hom :=
  ReadingFunctorialityFinite.intPolynomialFlatChange_nonidentity

/-- Fixed proper source ideal `(2)`. -/
noncomputable example : Ideal Int :=
  ReadingFunctorialityFinite.properIdeal

/-- Fixed characterization of the proper source ideal. -/
example :
    ReadingFunctorialityFinite.properIdeal = Ideal.span {2} :=
  ReadingFunctorialityFinite.properIdeal_eq

/-- Fixed properness of the source ideal. -/
example : ReadingFunctorialityFinite.properIdeal ≠ ⊤ :=
  ReadingFunctorialityFinite.properIdeal_ne_top

/-- Fixed properness after polynomial coefficient extension. -/
example :
    ReadingFunctorialityFinite.properIdeal.map
      ReadingFunctorialityFinite.intPolynomialFlatChange.hom ≠ ⊤ :=
  ReadingFunctorialityFinite.properIdeal_baseChange

/-- Fixed finite raw restriction system used by coefficient firing. -/
noncomputable example :
    LawAlgebra.RawAmbientRestrictionSystem
      ReadingFunctorialityFinite.finiteSite Int :=
  ReadingFunctorialityFinite.coefficientRaw

/-- Fixed non-flat quotient homomorphism to `ZMod 2`. -/
noncomputable example : Int →+* ZMod 2 :=
  ReadingFunctorialityFinite.intZModTwo

/-- Fixed non-flatness firing for the quotient to `ZMod 2`. -/
example : ¬ ReadingFunctorialityFinite.intZModTwo.Flat :=
  ReadingFunctorialityFinite.intZModTwo_not_flat

/-- Fixed coherent relation change that is not canonical coefficient transport. -/
noncomputable example :
    LawAlgebra.RawAmbientRestrictionSystem
      ReadingFunctorialityFinite.finiteSite (Polynomial Int) :=
  ReadingFunctorialityFinite.brokenRelationChange

/-- Fixed rejection of the noncanonical relation change. -/
example :
    ReadingFunctorialityFinite.brokenRelationChange ≠
      ReadingFunctorialityFinite.coefficientRaw.baseChange
        ReadingFunctorialityFinite.intPolynomialFlatChange.hom :=
  ReadingFunctorialityFinite.brokenRelationChange_not_rawBaseChange

example {A : ArchitectureObject U} {S : Site.AATSite A}
    {base : S.category} {R : Type u} [CommRing R]
    (Ob : Cohomology.LinearCoefficientSheaf R S)
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (n : Nat) (c : (Ob.canonicalLinearCech 𝒰).complex.X n)
    (σ : (Cohomology.canonicalCoverRelative 𝒰).simplex (n + 1)) :
    ((Ob.canonicalLinearCech 𝒰).complex.d n (n + 1)).hom c σ =
      ∑ i : Fin (n + 2), ((-1 : Int) ^ i.1) •
        Ob.modulePresheaf.map
          (Cohomology.canonicalTupleOverlapMap 𝒰
            (SimplexCategory.δ i) σ).op
          (c (fun j => σ ((SimplexCategory.δ i).toOrderHom j))) :=
  Ob.canonicalLinearCech_d_apply 𝒰 n c σ

example {A : ArchitectureObject U} {S : Site.AATSite A}
    {base : S.category} {R R' : Type u}
    [CommRing R] [CommRing R']
    (Ob : Cohomology.LinearCoefficientSheaf R S)
    (f : FlatCoefficientChange R R')
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    [Fintype 𝒰.Index]
    (hraw : Presheaf.IsSheaf S.topology
      (Ob.rawBaseChangePresheaf f ⋙
        forget₂ (ModuleCat.{u + 1} R') AddCommGrpCat.{u + 1})) :
    Cohomology.LinearCoefficientSheaf.CechCoefficientBaseChangeCompatible
      Ob f 𝒰 :=
  Cohomology.LinearCoefficientSheaf.cechCoefficientBaseChangeCompatible_of_finite_raw_isSheaf
      Ob f 𝒰 hraw

/-! ## SD9h: finite linear Čech and actual `Sheaf.H` firing -/

noncomputable example : Site.AATSite FiniteModel.corePackage.object :=
  ReadingFunctorialityFinite.finiteLinearSite

noncomputable example :
    HasSheafify ReadingFunctorialityFinite.finiteLinearSite.topology
      AddCommGrpCat.{1} :=
  ReadingFunctorialityFinite.finiteLinearAddCommGrpHasSheafify

noncomputable example : ReadingFunctorialityFinite.finiteLinearSite.category :=
  ReadingFunctorialityFinite.finiteLinearBase

noncomputable example :
    IsTerminal ReadingFunctorialityFinite.finiteLinearBase :=
  ReadingFunctorialityFinite.finiteLinearBaseIsTerminal

noncomputable example : ReadingFunctorialityFinite.finiteLinearSite.category :=
  ReadingFunctorialityFinite.finiteLinearLeftObject

noncomputable example : ReadingFunctorialityFinite.finiteLinearSite.category :=
  ReadingFunctorialityFinite.finiteLinearRightObject

noncomputable example : ReadingFunctorialityFinite.finiteLinearSite.category :=
  ReadingFunctorialityFinite.finiteLinearOverlapObject

example :
    ReadingFunctorialityFinite.finiteLinearSite.overlap.overlap
        ReadingFunctorialityFinite.finiteLinearBase.ctx
        ReadingFunctorialityFinite.finiteLinearLeftObject.ctx
        ReadingFunctorialityFinite.finiteLinearRightObject.ctx =
      ReadingFunctorialityFinite.finiteLinearOverlapObject.ctx :=
  ReadingFunctorialityFinite.finiteLinearPairOverlap_eq

example :
    ReadingFunctorialityFinite.finiteLinearSite.contextPreorder.le
        ReadingFunctorialityFinite.finiteLinearOverlapObject.ctx
          ReadingFunctorialityFinite.finiteLinearLeftObject.ctx ∧
      ReadingFunctorialityFinite.finiteLinearSite.contextPreorder.le
        ReadingFunctorialityFinite.finiteLinearOverlapObject.ctx
          ReadingFunctorialityFinite.finiteLinearRightObject.ctx ∧
      ReadingFunctorialityFinite.finiteLinearSite.contextPreorder.le
        ReadingFunctorialityFinite.finiteLinearLeftObject.ctx
          ReadingFunctorialityFinite.finiteLinearBase.ctx ∧
      ReadingFunctorialityFinite.finiteLinearSite.contextPreorder.le
        ReadingFunctorialityFinite.finiteLinearRightObject.ctx
          ReadingFunctorialityFinite.finiteLinearBase.ctx ∧
      (¬ ReadingFunctorialityFinite.finiteLinearSite.contextPreorder.le
        ReadingFunctorialityFinite.finiteLinearLeftObject.ctx
          ReadingFunctorialityFinite.finiteLinearRightObject.ctx) ∧
      (¬ ReadingFunctorialityFinite.finiteLinearSite.contextPreorder.le
        ReadingFunctorialityFinite.finiteLinearRightObject.ctx
          ReadingFunctorialityFinite.finiteLinearLeftObject.ctx) ∧
      (¬ ReadingFunctorialityFinite.finiteLinearSite.contextPreorder.le
        ReadingFunctorialityFinite.finiteLinearBase.ctx
          ReadingFunctorialityFinite.finiteLinearLeftObject.ctx) ∧
      (¬ ReadingFunctorialityFinite.finiteLinearSite.contextPreorder.le
        ReadingFunctorialityFinite.finiteLinearBase.ctx
          ReadingFunctorialityFinite.finiteLinearRightObject.ctx) ∧
      (¬ ReadingFunctorialityFinite.finiteLinearSite.contextPreorder.le
        ReadingFunctorialityFinite.finiteLinearLeftObject.ctx
          ReadingFunctorialityFinite.finiteLinearOverlapObject.ctx) ∧
      (¬ ReadingFunctorialityFinite.finiteLinearSite.contextPreorder.le
        ReadingFunctorialityFinite.finiteLinearRightObject.ctx
          ReadingFunctorialityFinite.finiteLinearOverlapObject.ctx) :=
  ReadingFunctorialityFinite.finiteLinearStrictDiamond

noncomputable example :
    Site.AATCoverageFamily
      ReadingFunctorialityFinite.finiteLinearSite.requirements
      ReadingFunctorialityFinite.finiteLinearSite.overlap
      ReadingFunctorialityFinite.finiteLinearBase :=
  ReadingFunctorialityFinite.finiteLinearCover

example : ReadingFunctorialityFinite.finiteLinearCover.Index ≃ Bool :=
  ReadingFunctorialityFinite.finiteLinearCoverIndexEquiv

example :
    ∃ i j : ReadingFunctorialityFinite.finiteLinearCover.Index,
      i ≠ j ∧
        ReadingFunctorialityFinite.finiteLinearCover.patch i =
          ReadingFunctorialityFinite.finiteLinearLeftObject.ctx ∧
        ReadingFunctorialityFinite.finiteLinearCover.patch j =
          ReadingFunctorialityFinite.finiteLinearRightObject.ctx :=
  ReadingFunctorialityFinite.finiteLinearCover_twoBranches

noncomputable example :
    Cohomology.LinearCoefficientSheaf Int
      ReadingFunctorialityFinite.finiteLinearSite :=
  ReadingFunctorialityFinite.finiteLinearCoefficientSheaf

noncomputable example : Fintype ReadingFunctorialityFinite.finiteLinearCover.Index :=
  ReadingFunctorialityFinite.finiteLinearCoverIndexFintype

noncomputable example :
    Cohomology.LinearCoefficientSheaf (Polynomial Int)
      ReadingFunctorialityFinite.finiteLinearSite :=
  ReadingFunctorialityFinite.finiteBaseChangedLinearCoefficientSheaf

example :
    Cohomology.LinearCoefficientSheaf.CechCoefficientBaseChangeCompatible
      ReadingFunctorialityFinite.finiteLinearCoefficientSheaf
      ReadingFunctorialityFinite.intPolynomialFlatChange
      ReadingFunctorialityFinite.finiteLinearCover :=
  ReadingFunctorialityFinite.finiteCechCoefficientCompatible

example :
    Cohomology.LinearCoefficientSheaf.IsLinearLerayFor
      ReadingFunctorialityFinite.finiteLinearCover
      ReadingFunctorialityFinite.finiteLinearCoefficientSheaf :=
  ReadingFunctorialityFinite.finiteLinearLerayCover

example :
    Cohomology.LinearCoefficientSheaf.IsLinearLerayFor
      ReadingFunctorialityFinite.finiteLinearCover
      ReadingFunctorialityFinite.finiteBaseChangedLinearCoefficientSheaf :=
  ReadingFunctorialityFinite.finiteTargetLinearLerayCover

noncomputable example :
    Cohomology.LinearCoverRelativeCechComplex Int
      ReadingFunctorialityFinite.finiteLinearCover
      ReadingFunctorialityFinite.finiteLinearCoefficientSheaf :=
  ReadingFunctorialityFinite.finiteLinearCech

example : Nat := ReadingFunctorialityFinite.finiteDegree

noncomputable example :
    ReadingFunctorialityFinite.finiteLinearCech.complex.cycles
      ReadingFunctorialityFinite.finiteDegree :=
  ReadingFunctorialityFinite.finiteCocycle

noncomputable example :
    ReadingFunctorialityFinite.finiteLinearCoefficientSheaf.terminalLerayHModule
      ReadingFunctorialityFinite.finiteLinearCover
      ReadingFunctorialityFinite.finiteLinearBaseIsTerminal
      ReadingFunctorialityFinite.finiteLinearLerayCover
      ReadingFunctorialityFinite.finiteDegree :=
  ReadingFunctorialityFinite.finiteActualSourceClass

noncomputable example :
    Derived.Intersection.moduleScalarExtension.{0, 2}
        ReadingFunctorialityFinite.intPolynomialFlatChange
        (ReadingFunctorialityFinite.finiteLinearCoefficientSheaf.terminalLerayHModule
            ReadingFunctorialityFinite.finiteLinearCover
            ReadingFunctorialityFinite.finiteLinearBaseIsTerminal
            ReadingFunctorialityFinite.finiteLinearLerayCover
            ReadingFunctorialityFinite.finiteDegree) ⟶
      ReadingFunctorialityFinite.finiteBaseChangedLinearCoefficientSheaf.terminalLerayHModule
          ReadingFunctorialityFinite.finiteLinearCover
          ReadingFunctorialityFinite.finiteLinearBaseIsTerminal
          ReadingFunctorialityFinite.finiteTargetLinearLerayCover
          ReadingFunctorialityFinite.finiteDegree :=
  ReadingFunctorialityFinite.finiteSheafHBaseChangeMap

noncomputable example :
    Derived.Intersection.moduleScalarExtension.{0, 2}
        ReadingFunctorialityFinite.intPolynomialFlatChange
        (ReadingFunctorialityFinite.finiteLinearCoefficientSheaf.terminalLerayHModule
            ReadingFunctorialityFinite.finiteLinearCover
            ReadingFunctorialityFinite.finiteLinearBaseIsTerminal
            ReadingFunctorialityFinite.finiteLinearLerayCover
            ReadingFunctorialityFinite.finiteDegree) ≅
      ReadingFunctorialityFinite.finiteBaseChangedLinearCoefficientSheaf.terminalLerayHModule
          ReadingFunctorialityFinite.finiteLinearCover
          ReadingFunctorialityFinite.finiteLinearBaseIsTerminal
          ReadingFunctorialityFinite.finiteTargetLinearLerayCover
          ReadingFunctorialityFinite.finiteDegree :=
  ReadingFunctorialityFinite.finiteSheafHBaseChangeIso

example :
    ReadingFunctorialityFinite.finiteSheafHBaseChangeIso.hom =
      ReadingFunctorialityFinite.finiteSheafHBaseChangeMap :=
  ReadingFunctorialityFinite.finiteSheafHBaseChangeIso_hom

example :
    ReadingFunctorialityFinite.finiteLinearCech.classBaseChange
      ReadingFunctorialityFinite.intPolynomialFlatChange
      ReadingFunctorialityFinite.finiteDegree
      ReadingFunctorialityFinite.finiteCocycle ≠ 0 :=
  ReadingFunctorialityFinite.finiteClass_baseChange_nonzero

example :
    ReadingFunctorialityFinite.finiteSheafHBaseChangeMap
      (Derived.Intersection.moduleScalarExtensionUnit.{0, 2}
        ReadingFunctorialityFinite.intPolynomialFlatChange
        (ReadingFunctorialityFinite.finiteLinearCoefficientSheaf.terminalLerayHModule
            ReadingFunctorialityFinite.finiteLinearCover
            ReadingFunctorialityFinite.finiteLinearBaseIsTerminal
            ReadingFunctorialityFinite.finiteLinearLerayCover
            ReadingFunctorialityFinite.finiteDegree)
        ReadingFunctorialityFinite.finiteActualSourceClass) ≠ 0 :=
  ReadingFunctorialityFinite.finiteSheafHClass_baseChange_nonzero

example :
    ReadingFunctorialityFinite.finiteLinearCech.classBaseChange
      ReadingFunctorialityFinite.intPolynomialFlatChange
      ReadingFunctorialityFinite.finiteDegree 0 = 0 :=
  ReadingFunctorialityFinite.zeroClass_not_firing

/-! R9c: independent topology and selected-cover firing. -/

namespace R9c

open ReadingFunctorialityFinite

noncomputable example : Site.AATSite FiniteModel.corePackage.object := topologySite
noncomputable example : topologySite.category := topologyBase
noncomputable example : IsTerminal topologyBase := topologyBaseIsTerminal
example : topologySite.category := topologyLeftObject
example : topologySite.category := topologyRightObject
noncomputable example : topologySite.category := topologyOverlapObject
example :
    topologySite.overlap.overlap topologyBase.ctx
        topologyLeftObject.ctx topologyRightObject.ctx = topologyOverlapObject.ctx :=
  topologyPairOverlap_eq
example :
    topologySite.contextPreorder.le topologyOverlapObject.ctx topologyLeftObject.ctx ∧
      topologySite.contextPreorder.le topologyOverlapObject.ctx topologyRightObject.ctx ∧
      topologySite.contextPreorder.le topologyLeftObject.ctx topologyBase.ctx ∧
      topologySite.contextPreorder.le topologyRightObject.ctx topologyBase.ctx ∧
      ¬ topologySite.contextPreorder.le topologyLeftObject.ctx topologyRightObject.ctx ∧
      ¬ topologySite.contextPreorder.le topologyRightObject.ctx topologyLeftObject.ctx ∧
      ¬ topologySite.contextPreorder.le topologyBase.ctx topologyLeftObject.ctx ∧
      ¬ topologySite.contextPreorder.le topologyBase.ctx topologyRightObject.ctx ∧
      ¬ topologySite.contextPreorder.le topologyLeftObject.ctx topologyOverlapObject.ctx ∧
      ¬ topologySite.contextPreorder.le topologyRightObject.ctx topologyOverlapObject.ctx :=
  topologyStrictDiamond

example : topologySite.category := topologyAuxBase
example : topologySite.category := topologyAuxPatch
noncomputable example : topologyAuxPatch ⟶ topologyAuxBase := topologyAuxInclusion
noncomputable example : topologySite.category := topologyLeftAuxOverlap
noncomputable example : topologySite.category := topologyRightAuxOverlap
example :
    topologySite.overlap.overlap topologyBase.ctx
        topologyLeftObject.ctx topologyAuxBase.ctx = topologyLeftAuxOverlap.ctx :=
  topologyLeftAuxOverlap_eq
example :
    topologySite.overlap.overlap topologyBase.ctx
        topologyRightObject.ctx topologyAuxBase.ctx = topologyRightAuxOverlap.ctx :=
  topologyRightAuxOverlap_eq
example :
    (¬ topologySite.contextPreorder.le topologyLeftObject.ctx topologyAuxBase.ctx) ∧
      (¬ topologySite.contextPreorder.le topologyRightObject.ctx topologyAuxBase.ctx) ∧
      (¬ topologySite.contextPreorder.le topologyAuxBase.ctx topologyLeftObject.ctx) ∧
      (¬ topologySite.contextPreorder.le topologyAuxBase.ctx topologyRightObject.ctx) ∧
      (¬ topologySite.contextPreorder.le topologyLeftObject.ctx topologyAuxPatch.ctx) ∧
      (¬ topologySite.contextPreorder.le topologyRightObject.ctx topologyAuxPatch.ctx) ∧
      (¬ topologySite.contextPreorder.le topologyAuxPatch.ctx topologyLeftObject.ctx) ∧
      (¬ topologySite.contextPreorder.le topologyAuxPatch.ctx topologyRightObject.ctx) ∧
      (¬ topologySite.contextPreorder.le topologyOverlapObject.ctx topologyAuxBase.ctx) ∧
      (¬ topologySite.contextPreorder.le topologyAuxBase.ctx topologyOverlapObject.ctx) ∧
      (¬ topologySite.contextPreorder.le topologyOverlapObject.ctx topologyAuxPatch.ctx) ∧
      (¬ topologySite.contextPreorder.le topologyAuxPatch.ctx topologyOverlapObject.ctx) :=
  topologyAuxOffDiamond
example : ¬ topologySite.contextPreorder.le
    topologyLeftAuxOverlap.ctx topologyAuxPatch.ctx :=
  topologyLeftAuxOverlap_not_le_auxPatch
example : ¬ topologySite.contextPreorder.le
    topologyRightAuxOverlap.ctx topologyAuxPatch.ctx :=
  topologyRightAuxOverlap_not_le_auxPatch

noncomputable example : Sieve topologyAuxBase := topologyAuxSieve
example : topologyAuxSieve =
    Sieve.generate (Presieve.singleton topologyAuxInclusion) :=
  topologyAuxSieve_eq_generateSingleton
noncomputable example : Precoverage topologySite.category := topologyAuxPrecoverage
example {X : topologySite.category} {R : Presieve X} :
    R ∈ topologyAuxPrecoverage X ↔
      ∃ _h : X = topologyAuxBase,
        HEq R (Presieve.singleton topologyAuxInclusion) :=
  topologyAuxPrecoverage_mem_iff

noncomputable example : Site.AATCoverageFamily topologySite.requirements
    topologySite.overlap topologyBase := topologyCoarseCover
noncomputable example : Site.AATCoverageFamily topologySite.requirements
    topologySite.overlap topologyBase := topologyFineCover
example : topologyCoarseCover.Index ≃ Bool := topologyCoarseCoverIndexEquiv
example : topologyFineCover.Index ≃ Bool × Bool := topologyFineCoverIndexEquiv
example : ∃ i j : topologyCoarseCover.Index,
    i ≠ j ∧ topologyCoarseCover.patch i = topologyLeftObject.ctx ∧
      topologyCoarseCover.patch j = topologyRightObject.ctx :=
  topologyCoarseCover_twoBranches
example : topologyCoarseCover.presieve = topologyFineCover.presieve :=
  topologyCoarseCover_presieve_eq_fineCover
noncomputable example : Precoverage topologySite.category := topologyCoarsePrecoverage
example {X : topologySite.category} {R : Presieve X} :
    R ∈ topologyCoarsePrecoverage X ↔
      ∃ _h : X = topologyBase, HEq R topologyCoarseCover.presieve :=
  topologyCoarsePrecoverage_mem_iff
example : topologySite.topology = topologyCoarsePrecoverage.toGrothendieck :=
  topologySite_topology_eq_coarseGenerated

noncomputable example : Site.AATCoverageFamily.Refinement
    topologyCoarseCover topologyFineCover := topologyCoarseToFineCover
example : ¬ Function.Bijective topologyCoarseToFineCover.indexMap :=
  topologyCoarseToFineCover_not_bijective
noncomputable example : Cohomology.ObstructionSheaf topologySite :=
  topologyObstructionSheaf
example : Subsingleton
    ((topologyObstructionSheaf.toAddCommGrpSheaf.val.obj
      (Opposite.op topologyBase) : Type 1)) := topologyBaseCoefficient_subsingleton
example : Subsingleton
    ((topologyObstructionSheaf.toAddCommGrpSheaf.val.obj
      (Opposite.op topologyLeftObject) : Type 1)) := topologyLeftCoefficient_subsingleton
example : Subsingleton
    ((topologyObstructionSheaf.toAddCommGrpSheaf.val.obj
      (Opposite.op topologyRightObject) : Type 1)) := topologyRightCoefficient_subsingleton
noncomputable example :
    ((topologyObstructionSheaf.toAddCommGrpSheaf.val.obj
      (Opposite.op topologyOverlapObject) : Type 1)) ≃+ ZMod 2 :=
  topologyOverlapCoefficientEquiv
example : Subsingleton
    ((topologyObstructionSheaf.toAddCommGrpSheaf.val.obj
      (Opposite.op topologyAuxBase) : Type 1)) := topologyAuxBaseCoefficient_subsingleton
example : Subsingleton
    ((topologyObstructionSheaf.toAddCommGrpSheaf.val.obj
      (Opposite.op topologyAuxPatch) : Type 1)) := topologyAuxPatchCoefficient_subsingleton
example : Subsingleton
    ((topologyObstructionSheaf.toAddCommGrpSheaf.val.obj
      (Opposite.op topologyLeftAuxOverlap) : Type 1)) :=
  topologyLeftAuxOverlapCoefficient_subsingleton
example : Subsingleton
    ((topologyObstructionSheaf.toAddCommGrpSheaf.val.obj
      (Opposite.op topologyRightAuxOverlap) : Type 1)) :=
  topologyRightAuxOverlapCoefficient_subsingleton
example :
    ∃ (c : (Cohomology.canonicalCechComplex topologyCoarseCover
          topologyObstructionSheaf).AdditiveCochain 1)
      (σ : (Cohomology.canonicalCoverRelative topologyFineCover).simplex 1),
      (topologyCoarseToFineCover.canonicalCechHom
        topologyObstructionSheaf).app 1 c σ ≠ 0 :=
  topologyCoarseToFineCechHom_nonzero

noncomputable example : ∀ n,
    (Cohomology.canonicalCoverRelative topologyFineCover).simplex n →
      (Cohomology.canonicalCoverRelative topologyCoarseCover).simplex n :=
  topologyBrokenFaceMap
example : ¬ ∃ r : Site.AATCoverageFamily.Refinement
      topologyCoarseCover topologyFineCover,
    r.simplexMap = topologyBrokenFaceMap := topologyBrokenFaceMap_not_refinement

noncomputable example : GrothendieckTopology topologySite.category := coarseTopology
example : coarseTopology = topologySite.topology := coarseTopology_eq_site
noncomputable example : topologyAuxBase ⟶ topologyBase := topologyAuxBaseToBase
noncomputable example : Sieve topologyAuxBase := topologyCoarsePullbackAtAuxBase
example : topologyCoarsePullbackAtAuxBase ∈ coarseTopology topologyAuxBase :=
  topologyCoarsePullbackAtAuxBase_mem
example : ¬ topologyCoarsePullbackAtAuxBase ≤ topologyAuxSieve :=
  topologyCoarsePullbackAtAuxBase_not_le_auxSieve
noncomputable example : GrothendieckTopology topologySite.category := fineTopology
example : fineTopology =
    coarseTopology ⊔ topologyAuxPrecoverage.toGrothendieck :=
  fineTopology_eq_coarse_sup_aux
example : fineTopology ≠ ⊤ := fineTopology_ne_top
example : Nat := nonzeroDegree
noncomputable example : HasSheafify coarseTopology AddCommGrpCat.{1} :=
  topologyCoarseAddCommGrpHasSheafify
noncomputable example : HasSheafify fineTopology AddCommGrpCat.{1} :=
  topologyFineAddCommGrpHasSheafify
noncomputable example : HasExt.{2} (Sheaf coarseTopology AddCommGrpCat.{1}) :=
  topologyCoarseAddCommGrpHasExt
noncomputable example : HasExt.{2} (Sheaf fineTopology AddCommGrpCat.{1}) :=
  topologyFineAddCommGrpHasExt
example : topologyAuxSieve ∈ fineTopology topologyAuxBase :=
  topologyAuxSieve_mem_fineTopology
example : topologyAuxSieve ∉ coarseTopology topologyAuxBase :=
  topologyAuxSieve_not_mem_coarseTopology
noncomputable example : CoverageTopologyRefinement coarseTopology fineTopology :=
  coarseFineTopologyRefinement
example : coarseTopology ≠ fineTopology := coarseFineTopology_strict
example : Sieve.generate topologyCoarseCover.presieve ∈
    coarseTopology topologyBase := topologyCoarseCover_mem_coarseTopology
example :
    (coarseFineTopologyRefinement.refineCover topologyBase
      (Sieve.generate topologyCoarseCover.presieve)
      topologyCoarseCover_mem_coarseTopology).1 =
        Sieve.generate topologyFineCover.presieve :=
  coarseFineTopologyRefinement_selects_fineCover
example : Sieve.generate topologyFineCover.presieve ∈ fineTopology topologyBase :=
  topologyFineCover_mem_fineTopology

end R9c

/-! R9d: actual topology-change firing on `Sheaf.H`. -/

namespace R9d

open ReadingFunctorialityFinite

example : Cohomology.IsLerayFor topologyCoarseCover topologyObstructionSheaf :=
  topologyCoarseLerayCover

noncomputable example :
    (Cohomology.canonicalCechComplex topologyCoarseCover
      topologyObstructionSheaf).CechCocycle 1 :=
  topologyCechOneCocycle

noncomputable example :
    (Cohomology.canonicalCechComplex topologyCoarseCover
      topologyObstructionSheaf).AdditiveCechHn 1 :=
  topologyCechOneClass

example : topologyCechOneClass ≠ 0 := topologyCechOneClass_ne_zero

example
    (x : (Cohomology.canonicalCechComplex topologyCoarseCover
      topologyObstructionSheaf).AdditiveCechHn 1) :
    x = 0 ∨ x = topologyCechOneClass :=
  topologyCechHOne_eq_zero_or_eq_one x

noncomputable example : CommonCoefficientSheaf coarseTopology fineTopology :=
  topologyCoefficient

example : topologyCoefficient.presheaf =
    topologyObstructionSheaf.toAddCommGrpSheaf.val :=
  topologyCoefficient_presheaf

noncomputable example : topologyCoefficient.coarse.H nonzeroDegree :=
  topologySourceHOneClass

example : topologySourceHOneClass =
    Cohomology.cechToSheafH topologyCoarseCover topologyObstructionSheaf
      topologyBaseIsTerminal topologyCoarseLerayCover nonzeroDegree
      topologyCechOneClass :=
  topologySourceHOneClass_eq_cech

noncomputable example :
    (Cohomology.canonicalCechComplex topologyCoarseCover
      topologyObstructionSheaf).AdditiveCechHn 1 ≃+
        topologyCoefficient.fine.H nonzeroDegree :=
  topologyCechToFineHOneEquiv

noncomputable example : topologyCoefficient.fine.H nonzeroDegree :=
  topologyTargetHOneClass

example :
    topologyCechToFineHOneEquiv.toAddMonoidHom =
      (coarseFineTopologyRefinement.sheafHMap
        topologyCoefficient nonzeroDegree).comp
        (Cohomology.cechToSheafH topologyCoarseCover
          topologyObstructionSheaf topologyBaseIsTerminal
          topologyCoarseLerayCover nonzeroDegree) :=
  topologyCechToFineHOneEquiv_eq_sheafHMap_comp_cech

example :
    coarseFineTopologyRefinement.sheafHMap
        topologyCoefficient nonzeroDegree topologySourceHOneClass =
      topologyTargetHOneClass :=
  topologySheafHMap_on_sourceClass

example : topologyTargetHOneClass ≠ 0 := topologyTargetHOneClass_ne_zero

example :
    coarseFineTopologyRefinement.sheafHMap
      topologyCoefficient nonzeroDegree ≠ 0 :=
  coarseFineSheafHMap_nonzero

example :
    coarseTopology ≠ fineTopology ∧
      fineTopology ≠ ⊤ ∧
      topologyTargetHOneClass ≠ 0 ∧
      coarseFineTopologyRefinement.sheafHMap
        topologyCoefficient nonzeroDegree ≠ 0 :=
  topologyActualHOneFiring

end R9d

/-! R9g: concrete `Tor₁` flat-base-change firing. -/

namespace R9g

open ReadingFunctorialityFinite

noncomputable example :
    Derived.Intersection.moduleScalarExtension intPolynomialFlatChange
        (Derived.Intersection.mathlibTor Int properIdeal properIdeal 1) ≅
      Derived.Intersection.mathlibTor (Polynomial Int)
        (properIdeal.map intPolynomialFlatChange.hom)
        (properIdeal.map intPolynomialFlatChange.hom) 1 :=
  modTwoTorOneBaseChangeIso

noncomputable example :
    Derived.Intersection.mathlibTor Int properIdeal properIdeal 1 :=
  modTwoTorOneSourceWitness

example : modTwoTorOneSourceWitness ≠ 0 :=
  modTwoTorOneSourceWitness_ne_zero

noncomputable example :
    Derived.Intersection.mathlibTor (Polynomial Int)
      (properIdeal.map intPolynomialFlatChange.hom)
      (properIdeal.map intPolynomialFlatChange.hom) 1 :=
  modTwoTorOneTargetWitness

example : modTwoTorOneTargetWitness ≠ 0 :=
  modTwoTorOneTargetWitness_ne_zero

example :
    Nontrivial
      (Derived.Intersection.mathlibTor (Polynomial Int)
        (properIdeal.map intPolynomialFlatChange.hom)
        (properIdeal.map intPolynomialFlatChange.hom) 1) :=
  modTwoTorOne_baseChange_nonzero

end R9g

end AAT.AG.StatementContractsReadingFunctoriality
