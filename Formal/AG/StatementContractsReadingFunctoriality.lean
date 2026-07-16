import Formal.AG.ReadingFunctoriality
import Formal.AG.ReadingFunctoriality.FiniteExamples

/-!
# Reading-functoriality statement contracts

Executable exact-signature contracts for Part 4 SD0–SD9 live in this module.
-/

namespace AAT.AG.StatementContractsReadingFunctoriality

open AAT.AG

universe u v w

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

end AAT.AG.StatementContractsReadingFunctoriality
