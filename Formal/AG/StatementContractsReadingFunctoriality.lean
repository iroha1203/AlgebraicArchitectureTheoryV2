import Formal.AG.ReadingFunctoriality
import Formal.AG.ReadingFunctoriality.FiniteExamples

/-!
# Reading-functoriality statement contracts

Executable exact-signature contracts for Part 4 SD0–SD9 live in this module.
-/

namespace AAT.AG.StatementContractsReadingFunctoriality

open AAT.AG

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

open ReadingFunctorialityFinite

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

end AAT.AG.StatementContractsReadingFunctoriality
