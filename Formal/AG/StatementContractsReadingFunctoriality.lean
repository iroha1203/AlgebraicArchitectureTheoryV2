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

end AAT.AG.StatementContractsReadingFunctoriality
