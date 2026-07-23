import Formal.AG.Atom.AATCore
import Formal.AG.Site.Geometry
import Formal.AG.LawAlgebra.StructureSheaf
import Mathlib.Logic.Equiv.Defs

/-!
# Reading functoriality core

This module owns the typed reading package and exact / positive core-change API
fixed by Part 4 SD0–SD1.
-/

namespace AAT.AG

universe u v w

/--
The typed reading parameter `p = (r, J, k)` from Part 4 SD0, retaining one
generated core, its selected geometry, and the coefficient-dependent raw system.

Implementation notes: the dependent fields enforce common provenance.  Scheme,
ideal, class, and comparison data are deliberately left to later layers rather
than stored in the core package.
-/
structure ReadingCore (U : AtomCarrier.{u}) where
  /-- The generated AAT core that supplies the site object and readings. -/
  core : AATCorePackage U
  /-- The selected geometry on the generated core. -/
  geometry : Site.SelectedGeometryReading core
  /-- The coefficient type used by the raw restriction system. -/
  Coefficient : Type v
  /-- The commutative-ring structure on the chosen coefficients. -/
  coefficientCommRing : CommRing Coefficient
  /-- The ambient restriction system on the geometry with the chosen coefficients. -/
  raw :
    let _ := coefficientCommRing
    LawAlgebra.RawAmbientRestrictionSystem geometry.toAATSite Coefficient

attribute [instance] ReadingCore.coefficientCommRing

namespace ReadingCore

/-- The AAT site determined by a reading core. -/
abbrev site (p : ReadingCore.{u, v} U) : Site.AATSite p.core.object :=
  p.geometry.toAATSite

/-- The architecture signature carried by the reading core's site. -/
abbrev signature (p : ReadingCore.{u, v} U) : ArchitectureSignature U :=
  p.site.signature

/-- Extensionality for the dependent data of a reading core. -/
@[ext] theorem ext
    {p q : ReadingCore.{u, v} U}
    (hcore : p.core = q.core)
    (hgeometry : HEq p.geometry q.geometry)
    (hCoefficient : p.Coefficient = q.Coefficient)
    (hcoefficientCommRing :
      HEq p.coefficientCommRing q.coefficientCommRing)
    (hraw : HEq p.raw q.raw) :
    p = q := by
  rcases p with ⟨pcore, pgeometry, pCoefficient, pRing, praw⟩
  rcases q with ⟨qcore, qgeometry, qCoefficient, qRing, qraw⟩
  cases hcore
  cases hgeometry
  cases hCoefficient
  cases hcoefficientCommRing
  cases hraw
  rfl

end ReadingCore

/--
Optional witness, circuit, and axis selectors over a reading core (Part 4 SD0).
Geometric and cohomological comparison data are intentionally not stored here.
-/
structure ReadingSelection (p : ReadingCore.{u, v} U) where
  /-- The selected symbolic equation/Atom witness coordinates. -/
  selectedWitness : p.site.equationSystem.Coordinate → Prop
  /-- The selected finite circuit data. -/
  selectedCircuit : FiniteCircuitDatum U → Prop
  /-- The selected signature axes. -/
  selectedAxis : p.signature.Axis → Prop

/-- Extensionality for optional reading selections. -/
@[ext] theorem ReadingSelection.ext
    {p : ReadingCore.{u, v} U}
    {s t : ReadingSelection p}
    (hwitness : s.selectedWitness = t.selectedWitness)
    (hcircuit : s.selectedCircuit = t.selectedCircuit)
    (haxis : s.selectedAxis = t.selectedAxis) :
    s = t := by
  cases s
  cases t
  cases hwitness
  cases hcircuit
  cases haxis
  rfl

/--
Direct-image transport of an atom family along an atom map (Part 4 SD1).

Implementation notes: the existential direct image retains every source atom
and supports composition; replacing it by an arbitrary target family would lose
the extraction provenance required by exact and positive core changes.
-/
def AtomFamily.transport
    (f : U.Atom → U.Atom)
    (F : AtomFamily U) :
    AtomFamily U where
  mem target := ∃ source, F.mem source ∧ f source = target

/-- A finite atom-family listing transports by mapping its listing. -/
theorem AtomFamily.ListFinite.transport
    {F : AtomFamily U}
    (hF : F.ListFinite)
    (f : U.Atom → U.Atom) :
    (F.transport f).ListFinite := by
  rcases hF with ⟨atoms, hatoms⟩
  refine ⟨atoms.map f, ?_⟩
  intro target htarget
  rcases htarget with ⟨source, hsource, rfl⟩
  exact List.mem_map.mpr ⟨source, hatoms source hsource, rfl⟩

/--
Direct-image transport of a configuration's family, relations, and identifications.

Implementation notes: relation and identification witnesses retain their source
atoms.  Merely mapping the family would not construct the configuration hom used
by the core-change APIs.
-/
def AtomConfiguration.transport
    (f : U.Atom → U.Atom)
    (C : AtomConfiguration U) :
    AtomConfiguration U where
  family := C.family.transport f
  relation target₁ target₂ :=
    ∃ source₁ source₂,
      C.relation source₁ source₂ ∧
        f source₁ = target₁ ∧ f source₂ = target₂
  identification target₁ target₂ :=
    ∃ source₁ source₂,
      C.identification source₁ source₂ ∧
        f source₁ = target₁ ∧ f source₂ = target₂

/-- The canonical configuration hom into the direct-image transport. -/
def AtomConfiguration.transportHom
    (f : U.Atom → U.Atom)
    (C : AtomConfiguration U) :
    ConfigurationHom C (C.transport f) where
  atomMap := f
  maps_family h := ⟨_, h, rfl⟩
  maps_relation h := ⟨_, _, h, rfl, rfl⟩
  maps_identification h := ⟨_, _, h, rfl, rfl⟩

/--
The canonical transport hom uses the supplied atom map.
This is the simplifier normal form for its computational component.
-/
@[simp] theorem AtomConfiguration.transportHom_atomMap
    (f : U.Atom → U.Atom)
    (C : AtomConfiguration U) :
    (AtomConfiguration.transportHom f C).atomMap = f :=
  rfl

/--
Transport compatibility for like-kind function or predicate invariants (Part 4 SD1).

Implementation notes: function invariants use an equivalence of value types and
predicate invariants use pointwise logical equivalence.  Cross-kind transport is
rejected rather than encoded by an unrelated certificate.
-/
def Invariant.TransportedAlong
    (I J : Invariant U)
    {ι : Type w}
    (source target : ι → ArchitectureObject U) : Prop :=
  match I, J with
  | .function I, .function J =>
      ∃ e : I.Value ≃ J.Value,
        ∀ A, e (I.evaluate (source A)) = J.evaluate (target A)
  | .predicate I, .predicate J =>
      ∀ A, I.holds (source A) ↔ J.holds (target A)
  | _, _ => False

/-- A function invariant cannot be transported to a predicate invariant. -/
theorem Invariant.function_predicate_not_transportedAlong
    (I : FunctionInvariant U) (J : PredicateInvariant U)
    {ι : Type w}
    (source target : ι → ArchitectureObject U) :
    ¬ Invariant.TransportedAlong (.function I) (.predicate J) source target :=
  fun h => h

/-- Every invariant transports along the identity object family. -/
theorem Invariant.transportedAlong_refl
    (I : Invariant U)
    {ι : Type w}
    (source : ι → ArchitectureObject U) :
    Invariant.TransportedAlong I I source source := by
  cases I with
  | function I =>
      exact ⟨Equiv.refl I.Value, fun _ => rfl⟩
  | predicate I =>
      exact fun _ => Iff.rfl

private theorem invariantTransportedAlong_comp
    (I J K : Invariant U)
    {ι : Type w}
    (source middle target : ι → ArchitectureObject U)
    (h₁ : Invariant.TransportedAlong I J source middle)
    (h₂ : Invariant.TransportedAlong J K middle target) :
    Invariant.TransportedAlong I K source target := by
  cases I <;> cases J <;> cases K
  · rcases h₁ with ⟨e₁, he₁⟩
    rcases h₂ with ⟨e₂, he₂⟩
    exact ⟨e₁.trans e₂, fun A => by simp only [Equiv.trans_apply, he₁, he₂]⟩
  · exact False.elim h₂
  · exact False.elim h₁
  · exact False.elim h₁
  · exact False.elim h₁
  · exact False.elim h₁
  · exact False.elim h₂
  · exact fun A => (h₁ A).trans (h₂ A)

private theorem invariantTransportedAlong_precomp
    (I J : Invariant U)
    {ι : Type v} {κ : Type w}
    (source target : ι → ArchitectureObject U)
    (e : κ → ι)
    (h : Invariant.TransportedAlong I J source target) :
    Invariant.TransportedAlong I J (source ∘ e) (target ∘ e) := by
  cases I <;> cases J
  · rcases h with ⟨equiv, hequiv⟩
    exact ⟨equiv, fun A => hequiv (e A)⟩
  · exact False.elim h
  · exact False.elim h
  · exact fun A => h (e A)

/--
A morphism between object algebras (Part 4 SD1).

Its fields transport objects, configurations, laws, signed circuits,
operations, invariants, and signature coordinates.

Implementation notes: this generic notion is the completed output type used by
an exact core change.  It is kept separate from `SignedExactCoreReadingHom`,
whose primitive data must construct this morphism instead of storing it as a
conclusion-equivalent field.
-/
structure ObjectAlgebraHom
    (K L : ObjectAlgebra U) where
  /-- Map between the source and target object types. -/
  objMap : K.Obj → L.Obj
  /-- Configuration hom on each actual object. -/
  configurationMap :
    ∀ A, ConfigurationHom (K.object A).configuration
      (L.object (objMap A)).configuration
  /-- Map between law indices. -/
  lawMap :
    K.equationSystem.Index → L.equationSystem.Index
  /-- Preservation and reflection of required-law status. -/
  required_iff :
    ∀ i,
      K.equationSystem.Required i ↔
        L.equationSystem.Required (lawMap i)
  /-- Preservation and reflection of law satisfaction. -/
  law_holds_iff :
    ∀ i A,
      K.equationSystem.EquationHolds i (K.object A) ↔
        L.equationSystem.EquationHolds (lawMap i) (L.object (objMap A))
  /-- Transport of signed circuit certificates. -/
  circuitMap :
    ∀ A i, K.Circuit A i →
      L.Circuit (objMap A) (lawMap i)
  /-- Transport of operations between actual objects. -/
  operationMap :
    ∀ {A B}, K.Op A B → L.Op (objMap A) (objMap B)
  /-- Naturality of configuration transport with respect to operations. -/
  operation_naturality :
    ∀ {A B} (op : K.Op A B),
      ConfigurationHom.comp
          (L.configurationMap (operationMap op))
          (configurationMap A) =
        ConfigurationHom.comp
          (configurationMap B)
          (K.configurationMap op)
  /-- Map between invariant indices. -/
  invariantMap :
    K.invariantReading.Index → L.invariantReading.Index
  /-- Transport compatibility for every indexed invariant. -/
  invariant_transport :
    ∀ i,
      Invariant.TransportedAlong
        (K.invariantReading.invariant i)
        (L.invariantReading.invariant (invariantMap i))
        K.object (fun A => L.object (objMap A))
  /-- Map between signature axes. -/
  axisMap :
    K.signatureReading.Axis → L.signatureReading.Axis
  /-- Equivalence of the coordinate types on corresponding axes. -/
  coordinateEquiv :
    ∀ i,
      K.signatureReading.Coordinate i ≃
        L.signatureReading.Coordinate (axisMap i)
  /-- Preservation and reflection of selected-axis status. -/
  axis_selected_iff :
    ∀ i,
      K.signatureReading.selected i ↔
        L.signatureReading.selected (axisMap i)
  /-- Compatibility of the coordinate equivalences with object coordinates. -/
  coordinate_eq :
    ∀ A i,
      coordinateEquiv i
          (K.signatureReading.coordinate (K.object A) i) =
        L.signatureReading.coordinate
          (L.object (objMap A)) (axisMap i)

namespace ObjectAlgebraHom

/-- Extensionality for the computational data of object-algebra morphisms. -/
@[ext (iff := false)] theorem ext
    {K L : ObjectAlgebra U}
    {f g : ObjectAlgebraHom K L}
    (hobj : f.objMap = g.objMap)
    (hconfiguration : HEq f.configurationMap g.configurationMap)
    (hlaw : HEq f.lawMap g.lawMap)
    (hcircuit : HEq f.circuitMap g.circuitMap)
    (hoperation : HEq
      (@ObjectAlgebraHom.operationMap U K L f)
      (@ObjectAlgebraHom.operationMap U K L g))
    (hinvariant : HEq f.invariantMap g.invariantMap)
    (haxis : HEq f.axisMap g.axisMap)
    (hcoordinate : HEq f.coordinateEquiv g.coordinateEquiv) :
    f = g := by
  cases f
  cases g
  cases hobj
  cases hconfiguration
  cases hlaw
  cases hcircuit
  cases hoperation
  cases hinvariant
  cases haxis
  cases hcoordinate
  rfl

/-- The identity object-algebra morphism. -/
def id (K : ObjectAlgebra U) : ObjectAlgebraHom K K where
  objMap := _root_.id
  configurationMap A := ConfigurationHom.id (K.object A).configuration
  lawMap := _root_.id
  required_iff _ := Iff.rfl
  law_holds_iff _ _ := Iff.rfl
  circuitMap _ _ := _root_.id
  operationMap := _root_.id
  operation_naturality _ := by
    apply ConfigurationHom.ext
    rfl
  invariantMap := _root_.id
  invariant_transport i :=
    Invariant.transportedAlong_refl (K.invariantReading.invariant i) K.object
  axisMap := _root_.id
  coordinateEquiv _ := Equiv.refl _
  axis_selected_iff _ := Iff.rfl
  coordinate_eq _ _ := rfl

/-- Composition of object-algebra morphisms. -/
def comp
    {K L M : ObjectAlgebra U}
    (f : ObjectAlgebraHom K L)
    (g : ObjectAlgebraHom L M) :
    ObjectAlgebraHom K M where
  objMap := g.objMap ∘ f.objMap
  configurationMap A :=
    ConfigurationHom.comp (g.configurationMap (f.objMap A))
      (f.configurationMap A)
  lawMap := g.lawMap ∘ f.lawMap
  required_iff i := (f.required_iff i).trans (g.required_iff (f.lawMap i))
  law_holds_iff i A :=
    (f.law_holds_iff i A).trans (g.law_holds_iff (f.lawMap i) (f.objMap A))
  circuitMap A i c := g.circuitMap (f.objMap A) (f.lawMap i) (f.circuitMap A i c)
  operationMap op := g.operationMap (f.operationMap op)
  operation_naturality op := by
    apply ConfigurationHom.ext
    have hf := congrArg ConfigurationHom.atomMap (f.operation_naturality op)
    have hg := congrArg ConfigurationHom.atomMap
      (g.operation_naturality (f.operationMap op))
    simp only [ConfigurationHom.comp] at hf hg ⊢
    rw [← Function.comp_assoc, hg, Function.comp_assoc, hf, ← Function.comp_assoc]
  invariantMap := g.invariantMap ∘ f.invariantMap
  invariant_transport i := by
    simpa only [Function.comp_apply] using
      invariantTransportedAlong_comp _ _ _ _ _ _
        (f.invariant_transport i)
        (invariantTransportedAlong_precomp _ _ _ _ f.objMap
          (g.invariant_transport (f.invariantMap i)))
  axisMap := g.axisMap ∘ f.axisMap
  coordinateEquiv i := (f.coordinateEquiv i).trans (g.coordinateEquiv (f.axisMap i))
  axis_selected_iff i :=
    (f.axis_selected_iff i).trans (g.axis_selected_iff (f.axisMap i))
  coordinate_eq A i := by
    simp only [Equiv.trans_apply]
    rw [f.coordinate_eq A i]
    simpa only [Function.comp_apply] using
      g.coordinate_eq (f.objMap A) (f.axisMap i)

/--
The object map of the identity morphism reduces to the identity function.
This is the simplifier normal form for identity object maps.
-/
@[simp] theorem id_objMap (K : ObjectAlgebra U) :
    (id K).objMap = _root_.id :=
  rfl

/--
The object map of a composite reduces to function composition.
This is the simplifier normal form for composite object maps.
-/
@[simp] theorem comp_objMap
    {K L M : ObjectAlgebra U}
    (f : ObjectAlgebraHom K L)
    (g : ObjectAlgebraHom L M) :
    (f.comp g).objMap = g.objMap ∘ f.objMap :=
  rfl

end ObjectAlgebraHom

@[simp] private theorem AtomFamily.transport_id
    (F : AtomFamily U) : F.transport _root_.id = F := by
  ext target
  constructor
  · rintro ⟨source, hsource, rfl⟩
    exact hsource
  · intro htarget
    exact ⟨target, htarget, rfl⟩

private theorem AtomFamily.transport_comp
    (F : AtomFamily U) (f g : U.Atom → U.Atom) :
    (F.transport f).transport g = F.transport (g ∘ f) := by
  ext target
  constructor
  · rintro ⟨middle, ⟨source, hsource, rfl⟩, rfl⟩
    exact ⟨source, hsource, rfl⟩
  · rintro ⟨source, hsource, rfl⟩
    exact ⟨f source, ⟨source, hsource, rfl⟩, rfl⟩

private theorem AtomFamily.transport_subset
    {F G : AtomFamily U} (h : F.Subset G)
    (f : U.Atom → U.Atom) :
    (F.transport f).Subset (G.transport f) := by
  rintro target ⟨source, hsource, rfl⟩
  exact ⟨source, h hsource, rfl⟩

@[simp] private theorem AtomConfiguration.transport_id
    (C : AtomConfiguration U) : C.transport _root_.id = C := by
  ext
  · constructor
    · rintro ⟨source, hsource, rfl⟩
      exact hsource
    · intro htarget
      exact ⟨_, htarget, rfl⟩
  · constructor
    · rintro ⟨source₁, source₂, h, rfl, rfl⟩
      exact h
    · intro h
      exact ⟨_, _, h, rfl, rfl⟩
  · constructor
    · rintro ⟨source₁, source₂, h, rfl, rfl⟩
      exact h
    · intro h
      exact ⟨_, _, h, rfl, rfl⟩

private theorem AtomConfiguration.transport_comp
    (C : AtomConfiguration U) (f g : U.Atom → U.Atom) :
    (C.transport f).transport g = C.transport (g ∘ f) := by
  ext
  · constructor
    · rintro ⟨middle, ⟨source, hsource, rfl⟩, rfl⟩
      exact ⟨source, hsource, rfl⟩
    · rintro ⟨source, hsource, rfl⟩
      exact ⟨f source, ⟨source, hsource, rfl⟩, rfl⟩
  · constructor
    · rintro ⟨middle₁, middle₂,
        ⟨source₁, source₂, h, rfl, rfl⟩, rfl, rfl⟩
      exact ⟨source₁, source₂, h, rfl, rfl⟩
    · rintro ⟨source₁, source₂, h, rfl, rfl⟩
      exact ⟨f source₁, f source₂,
        ⟨source₁, source₂, h, rfl, rfl⟩, rfl, rfl⟩
  · constructor
    · rintro ⟨middle₁, middle₂,
        ⟨source₁, source₂, h, rfl, rfl⟩, rfl, rfl⟩
      exact ⟨source₁, source₂, h, rfl, rfl⟩
    · rintro ⟨source₁, source₂, h, rfl, rfl⟩
      exact ⟨f source₁, f source₂,
        ⟨source₁, source₂, h, rfl, rfl⟩, rfl, rfl⟩

/--
Primitive data for an exact signed change between generated AAT cores (Part 4 SD1).

The data preserve and reflect laws and signed queries while transporting objects,
operations, invariants, and signature coordinates.

Implementation notes: the completed `ObjectAlgebraHom` is deliberately absent.
`toObjectAlgebraHom` constructs its reachable-object and circuit components from
these primitive maps.  Storing the completed morphism here would bypass the main
construction required by SD1.
-/
structure SignedExactCoreReadingHom
    (P Q : AATCorePackage U) where
  /-- Map on primitive atoms. -/
  atomMap : U.Atom → U.Atom
  /-- Exact identification of the target extracted family with the direct image. -/
  extraction_eq :
    Q.family = P.family.transport atomMap
  /-- Compatibility of generated composition with direct-image transport. -/
  composition_eq :
    ∀ (F : AtomFamily U) (hF : F.ListFinite),
      Q.reading.composition.compose
          (F.transport atomMap) (hF.transport atomMap) =
        (P.reading.composition.compose F hF).transport atomMap
  /-- Map on architecture objects. -/
  objectMap : ArchitectureObject U → ArchitectureObject U
  /-- Compatibility of object formation with configuration transport. -/
  object_formation_eq :
    ∀ C,
      objectMap (P.reading.objectReading.object C) =
        Q.reading.objectReading.object (C.transport atomMap)
  /-- Configuration hom attached to every object. -/
  configurationMap :
    ∀ A, ConfigurationHom A.configuration (objectMap A).configuration
  /-- Every configuration hom uses the primitive atom map. -/
  configurationMap_atomMap :
    ∀ A, (configurationMap A).atomMap = atomMap
  /-- Map between generated law indices. -/
  lawMap :
    P.algebra.equationSystem.Index → Q.algebra.equationSystem.Index
  /-- Preservation and reflection of required-law status. -/
  required_iff :
    ∀ i,
      P.algebra.equationSystem.Required i ↔
        Q.algebra.equationSystem.Required (lawMap i)
  /-- Preservation and reflection of law satisfaction on mapped objects. -/
  law_holds_iff :
    ∀ i A,
      P.algebra.equationSystem.EquationHolds i A ↔
        Q.algebra.equationSystem.EquationHolds (lawMap i) (objectMap A)
  /-- Map on signed finite circuit queries. -/
  queryMap : FiniteCircuitDatum U → FiniteCircuitDatum U
  /-- Preservation and reflection of signed query matching. -/
  matches_iff :
    ∀ Qry A, Qry.Matches A ↔ (queryMap Qry).Matches (objectMap A)
  /-- Preservation and reflection of circuit acceptance. -/
  accepts_iff :
    ∀ i Qry,
      P.algebra.circuits.accepts i Qry = true ↔
        Q.algebra.circuits.accepts
          (lawMap i) (queryMap Qry) = true
  /-- Map on operations between architecture objects. -/
  operationMap :
    ∀ {A B},
      P.reading.operationReading.Op A B →
        Q.reading.operationReading.Op (objectMap A) (objectMap B)
  /-- Naturality of configuration transport with respect to operations. -/
  operation_naturality :
    ∀ {A B} (op : P.reading.operationReading.Op A B),
      ConfigurationHom.comp
          (Q.reading.operationReading.configurationMap (operationMap op))
          (configurationMap A) =
        ConfigurationHom.comp
          (configurationMap B)
          (P.reading.operationReading.configurationMap op)
  /-- Map between invariant indices. -/
  invariantMap :
    P.reading.invariantReading.Index →
      Q.reading.invariantReading.Index
  /-- Compatibility of indexed invariants with the object map. -/
  invariant_transport :
    ∀ i,
      Invariant.TransportedAlong
        (P.reading.invariantReading.invariant i)
        (Q.reading.invariantReading.invariant (invariantMap i))
        _root_.id objectMap
  /-- Map between signature axes. -/
  axisMap :
    P.reading.signatureReading.Axis →
      Q.reading.signatureReading.Axis
  /-- Equivalence of coordinate types on corresponding axes. -/
  coordinateEquiv :
    ∀ i,
      P.reading.signatureReading.Coordinate i ≃
        Q.reading.signatureReading.Coordinate (axisMap i)
  /-- Preservation and reflection of selected-axis status. -/
  axis_selected_iff :
    ∀ i,
      P.reading.signatureReading.selected i ↔
        Q.reading.signatureReading.selected (axisMap i)
  /-- Compatibility of coordinate equivalences with mapped objects. -/
  coordinate_eq :
    ∀ A i,
      coordinateEquiv i
          (P.reading.signatureReading.coordinate A i) =
        Q.reading.signatureReading.coordinate
          (objectMap A) (axisMap i)

namespace SignedExactCoreReadingHom

private theorem configurationHom_heq
    {C D E : AtomConfiguration U}
    (f : ConfigurationHom C D) (g : ConfigurationHom C E)
    (htarget : D = E) (hatom : f.atomMap = g.atomMap) :
    HEq f g := by
  cases htarget
  exact heq_of_eq (ConfigurationHom.ext hatom)

/-- Extensionality for the computational data of exact core changes. -/
@[ext (iff := false)] theorem ext
    {P Q : AATCorePackage U}
    {f g : SignedExactCoreReadingHom P Q}
    (hatom : f.atomMap = g.atomMap)
    (hobject : f.objectMap = g.objectMap)
    (hlaw : HEq f.lawMap g.lawMap)
    (hquery : HEq f.queryMap g.queryMap)
    (hoperation : HEq
      (@SignedExactCoreReadingHom.operationMap U P Q f)
      (@SignedExactCoreReadingHom.operationMap U P Q g))
    (hinvariant : HEq f.invariantMap g.invariantMap)
    (haxis : HEq f.axisMap g.axisMap)
    (hcoordinate : HEq f.coordinateEquiv g.coordinateEquiv) :
    f = g := by
  have hconfiguration : HEq f.configurationMap g.configurationMap := by
    apply Function.hfunext rfl
    intro A A' hA
    cases hA
    apply configurationHom_heq
    · exact congrArg ArchitectureObject.configuration (congrFun hobject A)
    · rw [f.configurationMap_atomMap A, g.configurationMap_atomMap A, hatom]
  cases f
  cases g
  cases hatom
  cases hobject
  cases hconfiguration
  cases hlaw
  cases hquery
  cases hoperation
  cases hinvariant
  cases haxis
  cases hcoordinate
  rfl

/-- The identity exact core change. -/
def refl (P : AATCorePackage U) :
    SignedExactCoreReadingHom P P where
  atomMap := _root_.id
  extraction_eq := (AtomFamily.transport_id P.family).symm
  composition_eq F hF := by simp
  objectMap := _root_.id
  object_formation_eq C := by simp
  configurationMap A := ConfigurationHom.id A.configuration
  configurationMap_atomMap _ := rfl
  lawMap := _root_.id
  required_iff _ := Iff.rfl
  law_holds_iff _ _ := Iff.rfl
  queryMap := _root_.id
  matches_iff _ _ := Iff.rfl
  accepts_iff _ _ := Iff.rfl
  operationMap := _root_.id
  operation_naturality _ := by
    apply ConfigurationHom.ext
    rfl
  invariantMap := _root_.id
  invariant_transport i :=
    Invariant.transportedAlong_refl (P.reading.invariantReading.invariant i)
      _root_.id
  axisMap := _root_.id
  coordinateEquiv _ := Equiv.refl _
  axis_selected_iff _ := Iff.rfl
  coordinate_eq _ _ := rfl

/-- Composition of exact core changes. -/
def comp
    {P Q R : AATCorePackage U}
    (f : SignedExactCoreReadingHom P Q)
    (g : SignedExactCoreReadingHom Q R) :
    SignedExactCoreReadingHom P R where
  atomMap := g.atomMap ∘ f.atomMap
  extraction_eq := by
    rw [g.extraction_eq, f.extraction_eq, AtomFamily.transport_comp]
  composition_eq F hF := by
    have hg := g.composition_eq
      (F.transport f.atomMap) (hF.transport f.atomMap)
    have hg' :
        R.reading.composition.compose
            (F.transport (g.atomMap ∘ f.atomMap))
            (hF.transport (g.atomMap ∘ f.atomMap)) =
          (Q.reading.composition.compose
            (F.transport f.atomMap) (hF.transport f.atomMap)).transport g.atomMap := by
      simpa only [AtomFamily.transport_comp] using hg
    calc
      _ = (Q.reading.composition.compose
            (F.transport f.atomMap) (hF.transport f.atomMap)).transport g.atomMap := hg'
      _ = ((P.reading.composition.compose F hF).transport f.atomMap).transport
            g.atomMap := congrArg (fun C => C.transport g.atomMap)
              (f.composition_eq F hF)
      _ = _ := AtomConfiguration.transport_comp _ _ _
  objectMap := g.objectMap ∘ f.objectMap
  object_formation_eq C := by
    simp only [Function.comp_apply]
    rw [f.object_formation_eq C, g.object_formation_eq]
    exact congrArg R.reading.objectReading.object
      (AtomConfiguration.transport_comp C f.atomMap g.atomMap)
  configurationMap A :=
    ConfigurationHom.comp (g.configurationMap (f.objectMap A))
      (f.configurationMap A)
  configurationMap_atomMap A := by
    simp only [ConfigurationHom.comp]
    rw [f.configurationMap_atomMap A, g.configurationMap_atomMap]
  lawMap := g.lawMap ∘ f.lawMap
  required_iff i := (f.required_iff i).trans (g.required_iff (f.lawMap i))
  law_holds_iff i A :=
    (f.law_holds_iff i A).trans (g.law_holds_iff (f.lawMap i) (f.objectMap A))
  queryMap := g.queryMap ∘ f.queryMap
  matches_iff Qry A :=
    (f.matches_iff Qry A).trans (g.matches_iff (f.queryMap Qry) (f.objectMap A))
  accepts_iff i Qry :=
    (f.accepts_iff i Qry).trans (g.accepts_iff (f.lawMap i) (f.queryMap Qry))
  operationMap op := g.operationMap (f.operationMap op)
  operation_naturality op := by
    apply ConfigurationHom.ext
    have hf := congrArg ConfigurationHom.atomMap (f.operation_naturality op)
    have hg := congrArg ConfigurationHom.atomMap
      (g.operation_naturality (f.operationMap op))
    simp only [ConfigurationHom.comp] at hf hg ⊢
    rw [← Function.comp_assoc, hg, Function.comp_assoc, hf, ← Function.comp_assoc]
  invariantMap := g.invariantMap ∘ f.invariantMap
  invariant_transport i := by
    simpa only [Function.comp_apply] using
      invariantTransportedAlong_comp _ _ _ _ _ _
        (f.invariant_transport i)
        (invariantTransportedAlong_precomp _ _ _ _ f.objectMap
          (g.invariant_transport (f.invariantMap i)))
  axisMap := g.axisMap ∘ f.axisMap
  coordinateEquiv i := (f.coordinateEquiv i).trans (g.coordinateEquiv (f.axisMap i))
  axis_selected_iff i :=
    (f.axis_selected_iff i).trans (g.axis_selected_iff (f.axisMap i))
  coordinate_eq A i := by
    simp only [Equiv.trans_apply]
    rw [f.coordinate_eq A i]
    simpa only [Function.comp_apply] using
      g.coordinate_eq (f.objectMap A) (f.axisMap i)

/-- An exact change identifies the generated target configuration with the direct image. -/
theorem generatedConfiguration_eq
    {P Q : AATCorePackage U}
    (f : SignedExactCoreReadingHom P Q) :
    Q.configuration = P.configuration.transport f.atomMap := by
  unfold AATCorePackage.configuration
  simpa only [f.extraction_eq] using
    f.composition_eq P.family P.reading.family_listFinite

/-- The exact object map sends the generated source object to the generated target object. -/
theorem base_eq
    {P Q : AATCorePackage U}
    (f : SignedExactCoreReadingHom P Q) :
    f.objectMap P.object = Q.object := by
  unfold AATCorePackage.object
  rw [f.object_formation_eq]
  rw [← f.generatedConfiguration_eq]

private theorem mapReachable
    {P Q : AATCorePackage U}
    (f : SignedExactCoreReadingHom P Q)
    {A : ArchitectureObject U}
    (hA : P.reading.operationReading.Reachable P.object A) :
    Q.reading.operationReading.Reachable Q.object (f.objectMap A) := by
  induction hA with
  | base =>
      rw [f.base_eq]
      exact OperationReading.Reachable.base
  | step hA op ih =>
      exact OperationReading.Reachable.step ih (f.operationMap op)

/--
Construct the actual object-algebra morphism carried by an exact core change.

Implementation notes: reachable target objects are produced by induction on the
source operation closure, and signed circuits are built using `matches_iff` and
`accepts_iff`.  No completed morphism or reachable-object map is accepted as an
input field.
-/
noncomputable def toObjectAlgebraHom
    {P Q : AATCorePackage U}
    (f : SignedExactCoreReadingHom P Q) :
    ObjectAlgebraHom P.algebra Q.algebra where
  objMap A := ⟨f.objectMap A.1, f.mapReachable A.2⟩
  configurationMap A := f.configurationMap A.1
  lawMap := f.lawMap
  required_iff := f.required_iff
  law_holds_iff i A := f.law_holds_iff i A.1
  circuitMap A i c :=
    ⟨f.queryMap c.1, (f.matches_iff c.1 A.1).mp c.2.1,
      (f.accepts_iff i c.1).mp c.2.2⟩
  operationMap := f.operationMap
  operation_naturality := f.operation_naturality
  invariantMap := f.invariantMap
  invariant_transport i := by
    simpa only [Function.comp_apply] using
      invariantTransportedAlong_precomp _ _ _ _
        (fun A : P.algebra.Obj => A.1) (f.invariant_transport i)
  axisMap := f.axisMap
  coordinateEquiv := f.coordinateEquiv
  axis_selected_iff := f.axis_selected_iff
  coordinate_eq A := f.coordinate_eq A.1

/--
The actual morphism constructed from the identity exact change is the identity.
This is the simplifier normal form for exact identity changes.
-/
@[simp] theorem toObjectAlgebraHom_refl
    (P : AATCorePackage U) :
    (refl P).toObjectAlgebraHom = ObjectAlgebraHom.id P.algebra := by
  apply ObjectAlgebraHom.ext
  · funext A
    apply Subtype.ext
    rfl
  all_goals rfl

/--
Construction of the actual morphism commutes with composition of exact changes.
This is the simplifier normal form for exact composite changes.
-/
@[simp] theorem toObjectAlgebraHom_comp
    {P Q R : AATCorePackage U}
    (f : SignedExactCoreReadingHom P Q)
    (g : SignedExactCoreReadingHom Q R) :
    (f.comp g).toObjectAlgebraHom =
      f.toObjectAlgebraHom.comp g.toObjectAlgebraHom := by
  apply ObjectAlgebraHom.ext
  · funext A
    apply Subtype.ext
    rfl
  all_goals rfl

end SignedExactCoreReadingHom

/-- A finite circuit datum is positive when every recorded expected polarity is true. -/
def FiniteCircuitDatum.Positive
    (Qry : FiniteCircuitDatum U) : Prop :=
  ∀ query expected,
    (query, expected) ∈ Qry.queries → expected = true

/-- A singleton query with expected polarity `true` is positive. -/
theorem FiniteCircuitDatum.positive_singleton
    (query : CircuitQuery U) :
    (⟨[(query, true)]⟩ : FiniteCircuitDatum U).Positive := by
  intro actual expected hmem
  have hpair : (actual, expected) = (query, true) := by
    simpa only [List.mem_singleton] using hmem
  exact congrArg Prod.snd hpair

/-- A singleton query with expected polarity `false` is not positive. -/
theorem FiniteCircuitDatum.not_positive_singleton_false
    (query : CircuitQuery U) :
    ¬ (⟨[(query, false)]⟩ : FiniteCircuitDatum U).Positive := by
  intro hpositive
  have := hpositive query false (by simp)
  simp at this

/--
A positive circuit certificate on an actual object and law index.
The concrete nonidentity finite-model firing required by AC9 is supplied in R9.
-/
def PositiveCircuitDatum
    (P : AATCorePackage U)
    (A : P.algebra.Obj)
    (i : P.algebra.equationSystem.Index) : Type u :=
  {Qry : FiniteCircuitDatum U //
    Qry.Positive ∧
      Qry.Matches (P.algebra.object A) ∧
        P.algebra.circuits.accepts i Qry = true}

/--
Primitive data for a positive-only change between generated AAT cores (Part 4 SD1).

The change transports reachable objects and circuit data whose expected polarities
are all positive.

Implementation notes: matching and acceptance are one-way implications and no
negative circuit transport or completed `ObjectAlgebraHom` is stored.  Their
reflection is only one of the additional conditions required by the exact signed
notion, which also fixes extraction, composition, law, invariant, and signature
compatibilities.
-/
structure PositiveCoreReadingHom
    (P Q : AATCorePackage U) where
  /-- Map on primitive atoms. -/
  atomMap : U.Atom → U.Atom
  /-- The transported source family is contained in the target family. -/
  extraction_mono :
    (P.family.transport atomMap).Subset Q.family
  /-- Configuration hom from each source composite into its target composite. -/
  compositionMap :
    ∀ (F : AtomFamily U) (hF : F.ListFinite),
      ConfigurationHom
        (P.reading.composition.compose F hF)
        (Q.reading.composition.compose
          (F.transport atomMap) (hF.transport atomMap))
  /-- Every composition map uses the primitive atom map. -/
  compositionMap_atomMap :
    ∀ F hF, (compositionMap F hF).atomMap = atomMap
  /-- Map on architecture objects. -/
  objectMap : ArchitectureObject U → ArchitectureObject U
  /-- Compatibility of object formation with configuration transport. -/
  object_formation_eq :
    ∀ C,
      objectMap (P.reading.objectReading.object C) =
        Q.reading.objectReading.object (C.transport atomMap)
  /-- Reachability of the mapped generated source object in the target core. -/
  base_reachable :
    Q.reading.operationReading.Reachable Q.object (objectMap P.object)
  /-- Configuration hom attached to every object. -/
  configurationMap :
    ∀ A, ConfigurationHom A.configuration (objectMap A).configuration
  /-- Every configuration hom uses the primitive atom map. -/
  configurationMap_atomMap :
    ∀ A, (configurationMap A).atomMap = atomMap
  /-- Map on operations between architecture objects. -/
  operationMap :
    ∀ {A B},
      P.reading.operationReading.Op A B →
        Q.reading.operationReading.Op (objectMap A) (objectMap B)
  /-- Naturality of configuration transport with respect to operations. -/
  operation_naturality :
    ∀ {A B} (op : P.reading.operationReading.Op A B),
      ConfigurationHom.comp
          (Q.reading.operationReading.configurationMap (operationMap op))
          (configurationMap A) =
        ConfigurationHom.comp
          (configurationMap B)
          (P.reading.operationReading.configurationMap op)
  /-- Map between generated law indices. -/
  lawMap :
    P.algebra.equationSystem.Index → Q.algebra.equationSystem.Index
  /-- Map on finite circuit data. -/
  queryMap : FiniteCircuitDatum U → FiniteCircuitDatum U
  /-- Preservation of positive polarity. -/
  positive_preserved :
    ∀ Qry, Qry.Positive → (queryMap Qry).Positive
  /-- One-way preservation of matching for positive circuit data. -/
  matches_of_positive :
    ∀ Qry A, Qry.Positive → Qry.Matches A →
      (queryMap Qry).Matches (objectMap A)
  /-- One-way preservation of acceptance for positive circuit data. -/
  accepts_mono :
    ∀ i Qry, Qry.Positive →
      P.algebra.circuits.accepts i Qry = true →
        Q.algebra.circuits.accepts
          (lawMap i) (queryMap Qry) = true

namespace PositiveCoreReadingHom

private theorem configurationHom_heq_positive
    {C D E : AtomConfiguration U}
    (f : ConfigurationHom C D) (g : ConfigurationHom C E)
    (htarget : D = E) (hatom : f.atomMap = g.atomMap) :
    HEq f g := by
  cases htarget
  exact heq_of_eq (ConfigurationHom.ext hatom)

private def castTarget
    {C D E : AtomConfiguration U}
    (h : D = E) (f : ConfigurationHom C D) :
    ConfigurationHom C E := by
  cases h
  exact f

@[simp] private theorem castTarget_atomMap
    {C D E : AtomConfiguration U}
    (h : D = E) (f : ConfigurationHom C D) :
    (castTarget h f).atomMap = f.atomMap := by
  cases h
  rfl

private theorem mapReachableAux
    {P Q : AATCorePackage U}
    (f : PositiveCoreReadingHom P Q)
    {A : ArchitectureObject U}
    (hA : P.reading.operationReading.Reachable P.object A) :
    Q.reading.operationReading.Reachable Q.object (f.objectMap A) := by
  induction hA with
  | base => exact f.base_reachable
  | step hA op ih =>
      exact OperationReading.Reachable.step ih (f.operationMap op)

/-- Extensionality for the computational data of positive core changes. -/
@[ext (iff := false)] theorem ext
    {P Q : AATCorePackage U}
    {f g : PositiveCoreReadingHom P Q}
    (hatom : f.atomMap = g.atomMap)
    (hobject : f.objectMap = g.objectMap)
    (hoperation : HEq
      (@PositiveCoreReadingHom.operationMap U P Q f)
      (@PositiveCoreReadingHom.operationMap U P Q g))
    (hlaw : HEq f.lawMap g.lawMap)
    (hquery : f.queryMap = g.queryMap) :
    f = g := by
  have hcomposition : HEq f.compositionMap g.compositionMap := by
    apply Function.hfunext rfl
    intro F G hFG
    cases hFG
    apply Function.hfunext rfl
    intro hF hG hh
    cases hh
    apply configurationHom_heq_positive
    · exact congrArg
        (fun atomMap => Q.reading.composition.compose
          (F.transport atomMap) (hF.transport atomMap)) hatom
    · rw [f.compositionMap_atomMap F hF,
        g.compositionMap_atomMap F hF, hatom]
  have hconfiguration : HEq f.configurationMap g.configurationMap := by
    apply Function.hfunext rfl
    intro A B hAB
    cases hAB
    apply configurationHom_heq_positive
    · exact congrArg ArchitectureObject.configuration (congrFun hobject A)
    · rw [f.configurationMap_atomMap A, g.configurationMap_atomMap A, hatom]
  cases f
  cases g
  cases hatom
  cases hcomposition
  cases hobject
  cases hconfiguration
  cases hoperation
  cases hlaw
  cases hquery
  rfl

/-- The identity positive core change. -/
def refl (P : AATCorePackage U) :
    PositiveCoreReadingHom P P where
  atomMap := _root_.id
  extraction_mono := by
    rintro target ⟨source, hsource, rfl⟩
    exact hsource
  compositionMap F hF :=
    castTarget (by simp) (ConfigurationHom.id
      (P.reading.composition.compose F hF))
  compositionMap_atomMap F hF := by
    simp only [castTarget_atomMap]
    rfl
  objectMap := _root_.id
  object_formation_eq C := by simp
  base_reachable := OperationReading.Reachable.base
  configurationMap A := ConfigurationHom.id A.configuration
  configurationMap_atomMap _ := rfl
  operationMap := _root_.id
  operation_naturality _ := by
    apply ConfigurationHom.ext
    rfl
  lawMap := _root_.id
  queryMap := _root_.id
  positive_preserved _ h := h
  matches_of_positive _ _ _ h := h
  accepts_mono _ _ _ h := h

/-- Composition of positive core changes. -/
def comp
    {P Q R : AATCorePackage U}
    (f : PositiveCoreReadingHom P Q)
    (g : PositiveCoreReadingHom Q R) :
    PositiveCoreReadingHom P R where
  atomMap := g.atomMap ∘ f.atomMap
  extraction_mono := by
    intro target htarget
    have hnested : ((P.family.transport f.atomMap).transport g.atomMap).mem target := by
      simpa only [AtomFamily.transport_comp] using htarget
    exact g.extraction_mono
      (AtomFamily.transport_subset f.extraction_mono g.atomMap hnested)
  compositionMap F hF := by
    let map := ConfigurationHom.comp
      (g.compositionMap (F.transport f.atomMap) (hF.transport f.atomMap))
      (f.compositionMap F hF)
    have htarget :
        R.reading.composition.compose
            ((F.transport f.atomMap).transport g.atomMap)
            ((hF.transport f.atomMap).transport g.atomMap) =
          R.reading.composition.compose
            (F.transport (g.atomMap ∘ f.atomMap))
            (hF.transport (g.atomMap ∘ f.atomMap)) := by
      simp only [AtomFamily.transport_comp]
    exact castTarget htarget map
  compositionMap_atomMap F hF := by
    simp only [castTarget_atomMap, ConfigurationHom.comp]
    rw [f.compositionMap_atomMap F hF,
      g.compositionMap_atomMap (F.transport f.atomMap) (hF.transport f.atomMap)]
  objectMap := g.objectMap ∘ f.objectMap
  object_formation_eq C := by
    simp only [Function.comp_apply]
    rw [f.object_formation_eq C, g.object_formation_eq]
    exact congrArg R.reading.objectReading.object
      (AtomConfiguration.transport_comp C f.atomMap g.atomMap)
  base_reachable := mapReachableAux g f.base_reachable
  configurationMap A :=
    ConfigurationHom.comp (g.configurationMap (f.objectMap A))
      (f.configurationMap A)
  configurationMap_atomMap A := by
    simp only [ConfigurationHom.comp]
    rw [f.configurationMap_atomMap A, g.configurationMap_atomMap]
  operationMap op := g.operationMap (f.operationMap op)
  operation_naturality op := by
    apply ConfigurationHom.ext
    have hf := congrArg ConfigurationHom.atomMap (f.operation_naturality op)
    have hg := congrArg ConfigurationHom.atomMap
      (g.operation_naturality (f.operationMap op))
    simp only [ConfigurationHom.comp] at hf hg ⊢
    rw [← Function.comp_assoc, hg, Function.comp_assoc, hf, ← Function.comp_assoc]
  lawMap := g.lawMap ∘ f.lawMap
  queryMap := g.queryMap ∘ f.queryMap
  positive_preserved Qry h := g.positive_preserved _ (f.positive_preserved Qry h)
  matches_of_positive Qry A hpositive hmatches :=
    g.matches_of_positive _ _ (f.positive_preserved Qry hpositive)
      (f.matches_of_positive Qry A hpositive hmatches)
  accepts_mono i Qry hpositive haccepts :=
    g.accepts_mono _ _ (f.positive_preserved Qry hpositive)
      (f.accepts_mono i Qry hpositive haccepts)

/-- A positive change maps every source reachable object to a target reachable object. -/
theorem mapReachable
    {P Q : AATCorePackage U}
    (f : PositiveCoreReadingHom P Q)
    {A : ArchitectureObject U}
    (hA : P.reading.operationReading.Reachable P.object A) :
    Q.reading.operationReading.Reachable Q.object (f.objectMap A) :=
  mapReachableAux f hA

/-- The induced map between actual reachable object types. -/
def objMap
    {P Q : AATCorePackage U}
    (f : PositiveCoreReadingHom P Q) :
    P.algebra.Obj → Q.algebra.Obj :=
  fun A => ⟨f.objectMap A.1, f.mapReachable A.2⟩

/-- Transport a positive circuit certificate to the mapped object and law. -/
def mapPositiveCircuit
    {P Q : AATCorePackage U}
    (f : PositiveCoreReadingHom P Q)
    {A : P.algebra.Obj}
    {i : P.algebra.equationSystem.Index}
    (c : PositiveCircuitDatum P A i) :
    PositiveCircuitDatum Q (f.objMap A) (f.lawMap i) :=
  ⟨f.queryMap c.1,
    f.positive_preserved c.1 c.2.1,
    f.matches_of_positive c.1 A.1 c.2.1 c.2.2.1,
    f.accepts_mono i c.1 c.2.1 c.2.2.2⟩

end PositiveCoreReadingHom

namespace ReadingCore

/-- Exact core changes between two typed reading cores. -/
abbrev ExactCoreChange
    (p q : ReadingCore.{u, v} U) :=
  SignedExactCoreReadingHom p.core q.core

/-- Positive-only core changes between two typed reading cores. -/
abbrev PositiveCoreChange
    (p q : ReadingCore.{u, v} U) :=
  PositiveCoreReadingHom p.core q.core

/-- A selected AAT coverage family on a base object of the reading core's site. -/
abbrev SelectedCover
    (p : ReadingCore.{u, v} U)
    (base : p.site.category) :=
  Site.AATCoverageFamily p.site.requirements p.site.overlap base

end ReadingCore

end AAT.AG
