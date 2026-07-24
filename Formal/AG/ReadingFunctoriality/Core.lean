import Formal.AG.Atom.AATCore
import Formal.AG.Site.Geometry
import Formal.AG.LawAlgebra.StructureSheaf
import Mathlib.CategoryTheory.Equivalence
import Mathlib.Logic.Equiv.Defs

/-!
# Reading functoriality core

This module owns the typed reading package and exact / positive core-change API
fixed by Part 4 SD0–SD1.
-/

namespace AAT.AG

universe u v w

open CategoryTheory

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

/-- Transport an Atom-level circuit query along an Atom equivalence. -/
def CircuitQuery.transport
    (e : U.Atom ≃ U.Atom) :
    CircuitQuery U → CircuitQuery U
  | .atomPresent atom => .atomPresent (e atom)
  | .relationPresent atom₁ atom₂ =>
      .relationPresent (e atom₁) (e atom₂)
  | .identificationPresent atom₁ atom₂ =>
      .identificationPresent (e atom₁) (e atom₂)

/-- Transport every signed query component along an Atom equivalence. -/
def FiniteCircuitDatum.transport
    (e : U.Atom ≃ U.Atom)
    (datum : FiniteCircuitDatum U) :
    FiniteCircuitDatum U where
  queries := datum.queries.map fun pair => (pair.1.transport e, pair.2)

/-- Transport finite detector syntax together with its signed query templates. -/
def CircuitDetectorCode.transport
    (e : U.Atom ≃ U.Atom) :
    CircuitDetectorCode U → CircuitDetectorCode U
  | .reject => .reject
  | .exact pattern => .exact (pattern.transport e)
  | .any left right => .any (left.transport e) (right.transport e)

/-- Query transport commutes with composition of Atom equivalences. -/
@[simp] theorem CircuitQuery.transport_trans
    (e₁ e₂ : U.Atom ≃ U.Atom) (query : CircuitQuery U) :
    (query.transport e₁).transport e₂ = query.transport (e₁.trans e₂) := by
  cases query <;> rfl

/-- Signed finite-circuit transport commutes with composition. -/
@[simp] theorem FiniteCircuitDatum.transport_trans
    (e₁ e₂ : U.Atom ≃ U.Atom) (datum : FiniteCircuitDatum U) :
    (datum.transport e₁).transport e₂ = datum.transport (e₁.trans e₂) := by
  cases datum with
  | mk queries =>
      simp [FiniteCircuitDatum.transport, Function.comp_def]

/-- Identity Atom transport leaves each circuit query unchanged. -/
@[simp] theorem CircuitQuery.transport_refl
    (query : CircuitQuery U) :
    query.transport (Equiv.refl U.Atom) = query := by
  cases query <;> rfl

/-- Identity Atom transport leaves signed finite-circuit data unchanged. -/
@[simp] theorem FiniteCircuitDatum.transport_refl
    (datum : FiniteCircuitDatum U) :
    datum.transport (Equiv.refl U.Atom) = datum := by
  cases datum with
  | mk queries =>
      simp [FiniteCircuitDatum.transport]

/-- Signed finite-circuit transport along an Atom equivalence is injective. -/
theorem FiniteCircuitDatum.transport_injective
    {U : AtomCarrier.{u}}
    (e : U.Atom ≃ U.Atom) :
    Function.Injective (FiniteCircuitDatum.transport e) := by
  intro source target heq
  have hback := congrArg
    (FiniteCircuitDatum.transport e.symm) heq
  simpa using hback

/-- Detector syntax transport commutes with composition of Atom equivalences. -/
@[simp] theorem CircuitDetectorCode.transport_trans
    {U : AtomCarrier.{u}}
    (e₁ e₂ : U.Atom ≃ U.Atom) (code : CircuitDetectorCode U) :
    (code.transport e₁).transport e₂ =
      code.transport (e₁.trans e₂) := by
  induction code with
  | reject => rfl
  | exact pattern =>
      simp [CircuitDetectorCode.transport]
  | any left right hleft hright =>
      simp [CircuitDetectorCode.transport, hleft, hright]

/-- Identity Atom transport leaves finite detector syntax unchanged. -/
@[simp] theorem CircuitDetectorCode.transport_refl
    {U : AtomCarrier.{u}}
    (code : CircuitDetectorCode U) :
    code.transport (Equiv.refl U.Atom) = code := by
  induction code with
  | reject => rfl
  | exact pattern =>
      simp [CircuitDetectorCode.transport]
  | any left right hleft hright =>
      simp [CircuitDetectorCode.transport, hleft, hright]

/--
Evaluation of transported detector syntax on transported signed data is the
original evaluation.
-/
theorem CircuitDetectorCode.eval_transport
    {U : AtomCarrier.{u}}
    (e : U.Atom ≃ U.Atom)
    (code : CircuitDetectorCode U)
    (datum : FiniteCircuitDatum U) :
    (code.transport e).eval (datum.transport e) = code.eval datum := by
  induction code with
  | reject =>
      simp [CircuitDetectorCode.transport, CircuitDetectorCode.eval]
  | exact pattern =>
      by_cases hpattern : pattern = datum
      · subst datum
        simp [CircuitDetectorCode.transport, CircuitDetectorCode.eval]
      · have htransport :
          pattern.transport e ≠ datum.transport e :=
            fun heq => hpattern
              (FiniteCircuitDatum.transport_injective e heq)
        simp [CircuitDetectorCode.transport, CircuitDetectorCode.eval,
          hpattern, htransport]
  | any left right hleft hright =>
      simp [CircuitDetectorCode.transport, CircuitDetectorCode.eval,
        hleft, hright]

/--
An Atom query is preserved and reflected by direct-image configuration
transport along an Atom equivalence.
-/
theorem CircuitQuery.transport_holds_iff
    (e : U.Atom ≃ U.Atom) (query : CircuitQuery U)
    (A : ArchitectureObject U) :
    (query.transport e).Holds
        { A with configuration := A.configuration.transport e } ↔
      query.Holds A := by
  cases query with
  | atomPresent atom =>
      constructor
      · rintro ⟨source, hsource, heq⟩
        simpa only [e.injective heq] using hsource
      · intro h
        exact ⟨atom, h, rfl⟩
  | relationPresent atom₁ atom₂ =>
      constructor
      · rintro ⟨⟨source₁, hsource₁, heq₁⟩,
          ⟨⟨source₂, hsource₂, heq₂⟩,
            ⟨relationSource₁, relationSource₂, hrelation,
              hrelation₁, hrelation₂⟩⟩⟩
        have hs₁ : source₁ = atom₁ := e.injective heq₁
        have hs₂ : source₂ = atom₂ := e.injective heq₂
        have hr₁ : relationSource₁ = atom₁ := e.injective hrelation₁
        have hr₂ : relationSource₂ = atom₂ := e.injective hrelation₂
        subst source₁
        subst source₂
        subst relationSource₁
        subst relationSource₂
        exact ⟨hsource₁, hsource₂, hrelation⟩
      · rintro ⟨h₁, h₂, hrelation⟩
        exact ⟨⟨atom₁, h₁, rfl⟩, ⟨⟨atom₂, h₂, rfl⟩,
          ⟨atom₁, atom₂, hrelation, rfl, rfl⟩⟩⟩
  | identificationPresent atom₁ atom₂ =>
      constructor
      · rintro ⟨⟨source₁, hsource₁, heq₁⟩,
          ⟨⟨source₂, hsource₂, heq₂⟩,
            ⟨identificationSource₁, identificationSource₂, hidentification,
              hidentification₁, hidentification₂⟩⟩⟩
        have hs₁ : source₁ = atom₁ := e.injective heq₁
        have hs₂ : source₂ = atom₂ := e.injective heq₂
        have hi₁ : identificationSource₁ = atom₁ :=
          e.injective hidentification₁
        have hi₂ : identificationSource₂ = atom₂ :=
          e.injective hidentification₂
        subst source₁
        subst source₂
        subst identificationSource₁
        subst identificationSource₂
        exact ⟨hsource₁, hsource₂, hidentification⟩
      · rintro ⟨h₁, h₂, hidentification⟩
        exact ⟨⟨atom₁, h₁, rfl⟩, ⟨⟨atom₂, h₂, rfl⟩,
          ⟨atom₁, atom₂, hidentification, rfl, rfl⟩⟩⟩

/--
Signed query matching is preserved and reflected by exact configuration
transport.
-/
theorem FiniteCircuitDatum.transport_matches_iff
    (e : U.Atom ≃ U.Atom) (datum : FiniteCircuitDatum U)
    (A B : ArchitectureObject U)
    (hconfiguration :
      B.configuration = A.configuration.transport e) :
    datum.Matches A ↔ (datum.transport e).Matches B := by
  have holds_iff (query : CircuitQuery U) :
      query.Holds B ↔
        query.Holds { A with configuration := A.configuration.transport e } := by
    cases query <;> simp [CircuitQuery.Holds, hconfiguration]
  have query_iff (query : CircuitQuery U) :
      (query.transport e).Holds B ↔ query.Holds A := by
    exact (holds_iff (query.transport e)).trans
      (CircuitQuery.transport_holds_iff e query A)
  constructor
  · intro hmatches query expected hmem
    rcases List.mem_map.mp hmem with ⟨pair, hpair, hp⟩
    cases hp
    exact (query_iff pair.1).trans
      (hmatches pair.1 pair.2 hpair)
  · intro hmatches query expected hmem
    have hmapped := hmatches (query.transport e) expected
      (List.mem_map.mpr ⟨(query, expected), hmem, rfl⟩)
    exact (query_iff query).symm.trans hmapped

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

Its fields transport objects, configurations, equations, signed circuits,
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
  /-- Map between equation indices. -/
  equationMap :
    K.equationSystem.Index → L.equationSystem.Index
  /-- Preservation and reflection of required-equation status. -/
  required_iff :
    ∀ i,
      K.equationSystem.Required i ↔
        L.equationSystem.Required (equationMap i)
  /-- Preservation and reflection of equation fulfillment. -/
  equation_holds_iff :
    ∀ i A,
      K.equationSystem.EquationHolds i (K.object A) ↔
        L.equationSystem.EquationHolds (equationMap i) (L.object (objMap A))
  /-- Transport of signed circuit certificates. -/
  circuitMap :
    ∀ A i, K.Circuit A i →
      L.Circuit (objMap A) (equationMap i)
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
    (hequation : HEq f.equationMap g.equationMap)
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
  cases hequation
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
  equationMap := _root_.id
  required_iff _ := Iff.rfl
  equation_holds_iff _ _ := Iff.rfl
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
  equationMap := g.equationMap ∘ f.equationMap
  required_iff i :=
    (f.required_iff i).trans (g.required_iff (f.equationMap i))
  equation_holds_iff i A :=
    (f.equation_holds_iff i A).trans
      (g.equation_holds_iff (f.equationMap i) (f.objMap A))
  circuitMap A i c :=
    g.circuitMap (f.objMap A) (f.equationMap i) (f.circuitMap A i c)
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
Primitive exact transport between two architectural equation systems.

The context maps form an equivalence of the selected thin categories.
`observableEquiv` and `observable_naturality` are the component and naturality
data of the induced observable-presheaf isomorphism.  Equation fulfillment is
not stored: it is derived below from role equality and compatibility of the
violation and residual generators.
-/
structure EquationSystemExactTransport
    {A₀ B₀ : ArchitectureObject U}
    {C : Site.ContextPreorderCategory A₀}
    {D : Site.ContextPreorderCategory B₀}
    (E : ArchitecturalEquationSystem C)
    (F : ArchitecturalEquationSystem D)
    (atomEquiv : U.Atom ≃ U.Atom)
    (objectMap : ArchitectureObject U → ArchitectureObject U) where
  /-- Forward object map of the context-category equivalence. -/
  contextForward :
    Site.ContextCategoryObject C → Site.ContextCategoryObject D
  /-- Inverse object map of the context-category equivalence. -/
  contextBackward :
    Site.ContextCategoryObject D → Site.ContextCategoryObject C
  /-- Forward map on readable context morphisms. -/
  contextForward_map :
    ∀ {W V}, (W ⟶ V) → (contextForward W ⟶ contextForward V)
  /-- Inverse map on readable context morphisms. -/
  contextBackward_map :
    ∀ {W V}, (W ⟶ V) → (contextBackward W ⟶ contextBackward V)
  /-- Forward after inverse is strictly the selected target context. -/
  contextForward_backward :
    ∀ W, contextForward (contextBackward W) = W
  /-- Inverse after forward is strictly the selected source context. -/
  contextBackward_forward :
    ∀ W, contextBackward (contextForward W) = W
  /-- Map between equation indices. -/
  equationMap : E.Index → F.Index
  /-- Required, optional, and derived roles are all preserved exactly. -/
  role_eq : ∀ i, F.role (equationMap i) = E.role i
  /-- Observable-ring equivalence at every source context. -/
  observableEquiv :
    ∀ W, E.Observable W ≃+* F.Observable (contextForward W)
  /-- Observable-ring equivalences commute with restriction. -/
  observable_naturality :
    ∀ {W V} (f : W ⟶ V) (x : E.Observable V),
      observableEquiv W (E.restrict f x) =
        F.restrict (contextForward_map f) (observableEquiv V x)
  /-- Symbolic violation generators commute with exact transport. -/
  violationCoordinate_eq :
    ∀ W i atom,
      observableEquiv W (E.violationCoordinate W i atom) =
        F.violationCoordinate (contextForward W) (equationMap i)
          (atomEquiv atom)
  /-- Object-dependent residual generators commute with exact transport. -/
  equationResidual_eq :
    ∀ W A i atom,
      observableEquiv W (E.equationResidual W A i atom) =
        F.equationResidual (contextForward W) (objectMap A)
          (equationMap i) (atomEquiv atom)

namespace EquationSystemExactTransport

variable
    {A₀ B₀ : ArchitectureObject U}
    {C : Site.ContextPreorderCategory A₀}
    {D : Site.ContextPreorderCategory B₀}
    {E : ArchitecturalEquationSystem C}
    {F : ArchitecturalEquationSystem D}
    {atomEquiv : U.Atom ≃ U.Atom}
    {objectMap : ArchitectureObject U → ArchitectureObject U}

/-- The forward context data define an actual functor. -/
def contextFunctor
    (T : EquationSystemExactTransport E F atomEquiv objectMap) :
    (Site.ContextCategoryObject C) ⥤ (Site.ContextCategoryObject D) where
  obj := T.contextForward
  map := T.contextForward_map
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- The inverse context data define an actual functor. -/
def contextInverse
    (T : EquationSystemExactTransport E F atomEquiv objectMap) :
    (Site.ContextCategoryObject D) ⥤ (Site.ContextCategoryObject C) where
  obj := T.contextBackward
  map := T.contextBackward_map
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- The two strict context maps determine a category equivalence. -/
noncomputable def contextEquivalence
    (T : EquationSystemExactTransport E F atomEquiv objectMap) :
    (Site.ContextCategoryObject C) ≌ (Site.ContextCategoryObject D) where
  functor := T.contextFunctor
  inverse := T.contextInverse
  unitIso := NatIso.ofComponents fun W =>
    eqToIso (T.contextBackward_forward W).symm
  counitIso := NatIso.ofComponents fun W =>
    eqToIso (T.contextForward_backward W)
  functor_unitIso_comp _ := Subsingleton.elim _ _

/--
The observable-ring components and restriction compatibility assemble into a
natural isomorphism of `CommRingCat`-valued presheaves.
-/
noncomputable def observablePresheafIso
    (T : EquationSystemExactTransport E F atomEquiv objectMap) :
    E.observablePresheaf ≅
      T.contextFunctor.op ⋙ F.observablePresheaf :=
  NatIso.ofComponents
    (fun W => (T.observableEquiv W.unop).toCommRingCatIso)
    (by
      intro X Y f
      apply CommRingCat.hom_ext
      ext x
      exact T.observable_naturality f.unop x)

/-- Full role equality yields required-role preservation and reflection. -/
theorem required_iff
    (T : EquationSystemExactTransport E F atomEquiv objectMap)
    (i : E.Index) :
    E.Required i ↔ F.Required (T.equationMap i) := by
  unfold ArchitecturalEquationSystem.Required
  rw [T.role_eq]

/--
Equation fulfillment is derived from context equivalence, observable-ring
equivalence, and residual-generator compatibility.
-/
theorem equationHolds_iff
    (T : EquationSystemExactTransport E F atomEquiv objectMap)
    (i : E.Index) (A : ArchitectureObject U) :
    E.EquationHolds i A ↔
      F.EquationHolds (T.equationMap i) (objectMap A) := by
  constructor
  · intro hsource W atom
    let sourceContext := T.contextBackward W
    let sourceAtom := atomEquiv.symm atom
    have hzero := hsource sourceContext sourceAtom
    have hmapped :
        T.observableEquiv sourceContext
            (E.equationResidual sourceContext A i sourceAtom) = 0 := by
      rw [hzero]
      exact map_zero _
    rw [T.equationResidual_eq] at hmapped
    dsimp [sourceContext, sourceAtom] at hmapped
    rw [T.contextForward_backward W] at hmapped
    simpa using hmapped
  · intro htarget W atom
    apply (T.observableEquiv W).injective
    rw [T.equationResidual_eq]
    simpa using htarget (T.contextForward W) (atomEquiv atom)

/-- Identity transport of an equation system. -/
def refl
    {A₀ : ArchitectureObject U}
    {C : Site.ContextPreorderCategory A₀}
    (E : ArchitecturalEquationSystem C) :
    EquationSystemExactTransport E E (Equiv.refl U.Atom) _root_.id where
  contextForward := _root_.id
  contextBackward := _root_.id
  contextForward_map := _root_.id
  contextBackward_map := _root_.id
  contextForward_backward _ := rfl
  contextBackward_forward _ := rfl
  equationMap := _root_.id
  role_eq _ := rfl
  observableEquiv _ := RingEquiv.refl _
  observable_naturality := by intros; rfl
  violationCoordinate_eq := by intros; rfl
  equationResidual_eq := by intros; rfl

/-- Composition of primitive exact equation-system transports. -/
def comp
    {A₀ B₀ D₀ : ArchitectureObject U}
    {C : Site.ContextPreorderCategory A₀}
    {D : Site.ContextPreorderCategory B₀}
    {G : Site.ContextPreorderCategory D₀}
    {E : ArchitecturalEquationSystem C}
    {F : ArchitecturalEquationSystem D}
    {H : ArchitecturalEquationSystem G}
    {atomEquiv₁ atomEquiv₂ : U.Atom ≃ U.Atom}
    {objectMap₁ objectMap₂ : ArchitectureObject U → ArchitectureObject U}
    (T : EquationSystemExactTransport E F atomEquiv₁ objectMap₁)
    (S : EquationSystemExactTransport F H atomEquiv₂ objectMap₂) :
    EquationSystemExactTransport E H (atomEquiv₁.trans atomEquiv₂)
      (objectMap₂ ∘ objectMap₁) where
  contextForward := S.contextForward ∘ T.contextForward
  contextBackward := T.contextBackward ∘ S.contextBackward
  contextForward_map f := S.contextForward_map (T.contextForward_map f)
  contextBackward_map f := T.contextBackward_map (S.contextBackward_map f)
  contextForward_backward W := by
    change S.contextForward
        (T.contextForward (T.contextBackward (S.contextBackward W))) = W
    rw [T.contextForward_backward, S.contextForward_backward]
  contextBackward_forward W := by
    change T.contextBackward
        (S.contextBackward (S.contextForward (T.contextForward W))) = W
    rw [S.contextBackward_forward, T.contextBackward_forward]
  equationMap := S.equationMap ∘ T.equationMap
  role_eq i := by
    change H.role (S.equationMap (T.equationMap i)) = E.role i
    exact (S.role_eq (T.equationMap i)).trans (T.role_eq i)
  observableEquiv W :=
    (T.observableEquiv W).trans (S.observableEquiv (T.contextForward W))
  observable_naturality f x := by
    simp only [RingEquiv.trans_apply]
    calc
      S.observableEquiv (T.contextForward _)
          (T.observableEquiv _ (E.restrict f x)) =
          S.observableEquiv (T.contextForward _)
            (F.restrict (T.contextForward_map f)
              (T.observableEquiv _ x)) := by
            rw [T.observable_naturality]
      _ = H.restrict
          (S.contextForward_map (T.contextForward_map f))
          (S.observableEquiv (T.contextForward _) (T.observableEquiv _ x)) :=
        S.observable_naturality (T.contextForward_map f)
          (T.observableEquiv _ x)
  violationCoordinate_eq W i atom := by
    simp only [RingEquiv.trans_apply]
    calc
      S.observableEquiv (T.contextForward W)
          (T.observableEquiv W (E.violationCoordinate W i atom)) =
          S.observableEquiv (T.contextForward W)
            (F.violationCoordinate (T.contextForward W)
              (T.equationMap i) (atomEquiv₁ atom)) := by
            rw [T.violationCoordinate_eq]
      _ = H.violationCoordinate
          (S.contextForward (T.contextForward W))
          (S.equationMap (T.equationMap i))
          (atomEquiv₂ (atomEquiv₁ atom)) :=
        S.violationCoordinate_eq (T.contextForward W)
          (T.equationMap i) (atomEquiv₁ atom)
  equationResidual_eq W A i atom := by
    simp only [RingEquiv.trans_apply]
    calc
      S.observableEquiv (T.contextForward W)
          (T.observableEquiv W (E.equationResidual W A i atom)) =
          S.observableEquiv (T.contextForward W)
            (F.equationResidual (T.contextForward W)
              (objectMap₁ A) (T.equationMap i) (atomEquiv₁ atom)) := by
            rw [T.equationResidual_eq]
      _ = H.equationResidual
          (S.contextForward (T.contextForward W))
          (objectMap₂ (objectMap₁ A))
          (S.equationMap (T.equationMap i))
          (atomEquiv₂ (atomEquiv₁ atom)) :=
        S.equationResidual_eq (T.contextForward W)
          (objectMap₁ A) (T.equationMap i) (atomEquiv₁ atom)

end EquationSystemExactTransport

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
  /-- Equivalence on primitive atoms. -/
  atomEquiv : U.Atom ≃ U.Atom
  /-- Exact identification of the target extracted family with the direct image. -/
  extraction_eq :
    Q.family = P.family.transport atomEquiv
  /-- Compatibility of generated composition with direct-image transport. -/
  composition_eq :
    ∀ (F : AtomFamily U) (hF : F.ListFinite),
      Q.reading.composition.compose
          (F.transport atomEquiv) (hF.transport atomEquiv) =
        (P.reading.composition.compose F hF).transport atomEquiv
  /-- Map on architecture objects. -/
  objectMap : ArchitectureObject U → ArchitectureObject U
  /-- Compatibility of object formation with configuration transport. -/
  object_formation_eq :
    ∀ C,
      objectMap (P.reading.objectReading.object C) =
        Q.reading.objectReading.object (C.transport atomEquiv)
  /-- Configuration hom attached to every object. -/
  configurationMap :
    ∀ A, ConfigurationHom A.configuration (objectMap A).configuration
  /-- Every configuration hom uses the primitive Atom equivalence. -/
  configurationMap_atomMap :
    ∀ A, (configurationMap A).atomMap = atomEquiv
  /-- Exact identification of target configuration data with direct image. -/
  configuration_eq :
    ∀ A,
      (objectMap A).configuration =
        A.configuration.transport atomEquiv
  /--
  Context equivalence, observable-presheaf equivalence, role equality, and
  violation/residual generator compatibility.
  -/
  equationTransport :
    EquationSystemExactTransport
      P.algebra.equationSystem Q.algebra.equationSystem atomEquiv objectMap
  /--
  The target finite detector code is the structural transport of the source
  detector code and its signed templates.
  -/
  detectorCode_eq :
    ∀ i,
      Q.algebra.circuits.code (equationTransport.equationMap i) =
        (P.algebra.circuits.code i).transport atomEquiv
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

/-- Underlying function of the exact Atom equivalence. -/
def atomMap
    {P Q : AATCorePackage U}
    (f : SignedExactCoreReadingHom P Q) :
    U.Atom → U.Atom :=
  f.atomEquiv

/-- Equation-index map supplied by the primitive equation transport. -/
def equationMap
    {P Q : AATCorePackage U}
    (f : SignedExactCoreReadingHom P Q) :
    P.algebra.equationSystem.Index →
      Q.algebra.equationSystem.Index :=
  f.equationTransport.equationMap

/-- Canonical signed-query transport induced by the Atom equivalence. -/
def queryMap
    {P Q : AATCorePackage U}
    (f : SignedExactCoreReadingHom P Q) :
    FiniteCircuitDatum U → FiniteCircuitDatum U :=
  fun datum => datum.transport f.atomEquiv

/-- Required-role preservation is derived from full role equality. -/
theorem required_iff
    {P Q : AATCorePackage U}
    (f : SignedExactCoreReadingHom P Q)
    (i : P.algebra.equationSystem.Index) :
    P.algebra.equationSystem.Required i ↔
      Q.algebra.equationSystem.Required (f.equationMap i) :=
  f.equationTransport.required_iff i

/--
Equation fulfillment is derived from context, observable, and residual
transport.
-/
theorem equation_holds_iff
    {P Q : AATCorePackage U}
    (f : SignedExactCoreReadingHom P Q)
    (i : P.algebra.equationSystem.Index)
    (A : ArchitectureObject U) :
    P.algebra.equationSystem.EquationHolds i A ↔
      Q.algebra.equationSystem.EquationHolds
        (f.equationMap i) (f.objectMap A) :=
  f.equationTransport.equationHolds_iff i A

/-- Signed query matching is derived componentwise from configuration transport. -/
theorem matches_iff
    {P Q : AATCorePackage U}
    (f : SignedExactCoreReadingHom P Q)
    (datum : FiniteCircuitDatum U)
    (A : ArchitectureObject U) :
    datum.Matches A ↔ (f.queryMap datum).Matches (f.objectMap A) :=
  FiniteCircuitDatum.transport_matches_iff f.atomEquiv datum A
    (f.objectMap A) (f.configuration_eq A)

/-- Circuit acceptance is derived from detector evaluation compatibility. -/
theorem accepts_iff
    {P Q : AATCorePackage U}
    (f : SignedExactCoreReadingHom P Q)
    (i : P.algebra.equationSystem.Index)
    (datum : FiniteCircuitDatum U) :
    P.algebra.circuits.accepts i datum = true ↔
      Q.algebra.circuits.accepts
        (f.equationMap i) (f.queryMap datum) = true := by
  unfold EquationCircuitReading.accepts
  change
    (P.algebra.circuits.code i).eval datum = true ↔
      (Q.algebra.circuits.code
        (f.equationTransport.equationMap i)).eval
          (datum.transport f.atomEquiv) = true
  rw [f.detectorCode_eq]
  rw [CircuitDetectorCode.eval_transport]

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
    (hatom : f.atomEquiv = g.atomEquiv)
    (hobject : f.objectMap = g.objectMap)
    (hequation : HEq f.equationTransport g.equationTransport)
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
  cases hequation
  cases hoperation
  cases hinvariant
  cases haxis
  cases hcoordinate
  rfl

/-- The identity exact core change. -/
def refl (P : AATCorePackage U) :
    SignedExactCoreReadingHom P P where
  atomEquiv := Equiv.refl U.Atom
  extraction_eq := by
    simpa using (AtomFamily.transport_id P.family).symm
  composition_eq F hF := by simp
  objectMap := _root_.id
  object_formation_eq C := by simp
  configurationMap A := ConfigurationHom.id A.configuration
  configurationMap_atomMap _ := rfl
  configuration_eq A := by
    simpa using (AtomConfiguration.transport_id A.configuration).symm
  equationTransport :=
    EquationSystemExactTransport.refl P.algebra.equationSystem
  detectorCode_eq i := by
    simp [EquationSystemExactTransport.refl]
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
  atomEquiv := f.atomEquiv.trans g.atomEquiv
  extraction_eq := by
    rw [g.extraction_eq, f.extraction_eq, AtomFamily.transport_comp]
    rfl
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
      _ = _ := by
        simpa only [Equiv.trans_apply] using
          AtomConfiguration.transport_comp
            (P.reading.composition.compose F hF) f.atomMap g.atomMap
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
    apply funext
    intro atom
    rfl
  configuration_eq A := by
    change (g.objectMap (f.objectMap A)).configuration =
      A.configuration.transport (f.atomEquiv.trans g.atomEquiv)
    rw [g.configuration_eq, f.configuration_eq]
    simpa only [Equiv.trans_apply] using
      AtomConfiguration.transport_comp A.configuration f.atomMap g.atomMap
  equationTransport :=
    f.equationTransport.comp g.equationTransport
  detectorCode_eq i := by
    calc
      R.algebra.circuits.code
          ((f.equationTransport.comp g.equationTransport).equationMap i) =
          (Q.algebra.circuits.code (f.equationMap i)).transport
            g.atomEquiv := by
              simpa [equationMap, EquationSystemExactTransport.comp] using
                g.detectorCode_eq (f.equationMap i)
      _ = ((P.algebra.circuits.code i).transport f.atomEquiv).transport
            g.atomEquiv := by
              exact congrArg (CircuitDetectorCode.transport g.atomEquiv)
                (f.detectorCode_eq i)
      _ = (P.algebra.circuits.code i).transport
            (f.atomEquiv.trans g.atomEquiv) :=
        CircuitDetectorCode.transport_trans _ _ _
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
  have hconfiguration := f.generatedConfiguration_eq
  change Q.configuration =
    P.configuration.transport f.atomEquiv at hconfiguration
  rw [← hconfiguration]

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
  equationMap := f.equationMap
  required_iff := f.required_iff
  equation_holds_iff i A := f.equation_holds_iff i A.1
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
  · rfl
  · rfl
  · apply heq_of_eq
    funext A i circuit
    apply Subtype.ext
    simp [toObjectAlgebraHom, queryMap, refl, ObjectAlgebraHom.id]
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
  · rfl
  · rfl
  · apply heq_of_eq
    funext A i circuit
    apply Subtype.ext
    simp [toObjectAlgebraHom, queryMap, comp, ObjectAlgebraHom.comp]
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
  /-- Map between generated equation indices. -/
  equationMap :
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
          (equationMap i) (queryMap Qry) = true

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
    (hequation : HEq f.equationMap g.equationMap)
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
  cases hequation
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
  equationMap := _root_.id
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
  equationMap := g.equationMap ∘ f.equationMap
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

/-- Transport a positive circuit certificate to the mapped object and equation. -/
def mapPositiveCircuit
    {P Q : AATCorePackage U}
    (f : PositiveCoreReadingHom P Q)
    {A : P.algebra.Obj}
    {i : P.algebra.equationSystem.Index}
    (c : PositiveCircuitDatum P A i) :
    PositiveCircuitDatum Q (f.objMap A) (f.equationMap i) :=
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
