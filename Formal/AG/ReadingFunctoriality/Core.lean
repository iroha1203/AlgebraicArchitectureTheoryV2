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

structure ReadingCore (U : AtomCarrier.{u}) where
  core : AATCorePackage U
  geometry : Site.SelectedGeometryReading core
  Coefficient : Type v
  coefficientCommRing : CommRing Coefficient
  raw :
    let _ := coefficientCommRing
    LawAlgebra.RawAmbientRestrictionSystem geometry.toAATSite Coefficient

attribute [instance] ReadingCore.coefficientCommRing

namespace ReadingCore

abbrev site (p : ReadingCore.{u, v} U) : Site.AATSite p.core.object :=
  p.geometry.toAATSite

abbrev lawUniverse (p : ReadingCore.{u, v} U) : LawUniverse U :=
  p.site.lawUniverse

abbrev signature (p : ReadingCore.{u, v} U) : ArchitectureSignature U :=
  p.site.signature

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

structure ReadingSelection (p : ReadingCore.{u, v} U) where
  selectedWitness : p.lawUniverse.witnessFamily.Witness → Prop
  selectedCircuit : FiniteCircuitDatum U → Prop
  selectedAxis : p.signature.Axis → Prop

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

def AtomFamily.transport
    (f : U.Atom → U.Atom)
    (F : AtomFamily U) :
    AtomFamily U where
  mem target := ∃ source, F.mem source ∧ f source = target

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

def AtomConfiguration.transportHom
    (f : U.Atom → U.Atom)
    (C : AtomConfiguration U) :
    ConfigurationHom C (C.transport f) where
  atomMap := f
  maps_family h := ⟨_, h, rfl⟩
  maps_relation h := ⟨_, _, h, rfl, rfl⟩
  maps_identification h := ⟨_, _, h, rfl, rfl⟩

@[simp] theorem AtomConfiguration.transportHom_atomMap
    (f : U.Atom → U.Atom)
    (C : AtomConfiguration U) :
    (AtomConfiguration.transportHom f C).atomMap = f :=
  rfl

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

theorem Invariant.function_predicate_not_transportedAlong
    (I : FunctionInvariant U) (J : PredicateInvariant U)
    {ι : Type w}
    (source target : ι → ArchitectureObject U) :
    ¬ Invariant.TransportedAlong (.function I) (.predicate J) source target :=
  fun h => h

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

structure ObjectAlgebraHom
    (K L : ObjectAlgebra U) where
  objMap : K.Obj → L.Obj
  configurationMap :
    ∀ A, ConfigurationHom (K.object A).configuration
      (L.object (objMap A)).configuration
  lawMap :
    K.lawReading.lawUniverse.Index →
      L.lawReading.lawUniverse.Index
  required_iff :
    ∀ i,
      K.lawReading.lawUniverse.Required i ↔
        L.lawReading.lawUniverse.Required (lawMap i)
  law_holds_iff :
    ∀ i A,
      (K.lawReading.lawUniverse.law i).holds (K.object A) ↔
        (L.lawReading.lawUniverse.law (lawMap i)).holds
          (L.object (objMap A))
  circuitMap :
    ∀ A i, K.Circuit A i →
      L.Circuit (objMap A) (lawMap i)
  operationMap :
    ∀ {A B}, K.Op A B → L.Op (objMap A) (objMap B)
  operation_naturality :
    ∀ {A B} (op : K.Op A B),
      ConfigurationHom.comp
          (L.configurationMap (operationMap op))
          (configurationMap A) =
        ConfigurationHom.comp
          (configurationMap B)
          (K.configurationMap op)
  invariantMap :
    K.invariantReading.Index → L.invariantReading.Index
  invariant_transport :
    ∀ i,
      Invariant.TransportedAlong
        (K.invariantReading.invariant i)
        (L.invariantReading.invariant (invariantMap i))
        K.object (fun A => L.object (objMap A))
  axisMap :
    K.signatureReading.Axis → L.signatureReading.Axis
  coordinateEquiv :
    ∀ i,
      K.signatureReading.Coordinate i ≃
        L.signatureReading.Coordinate (axisMap i)
  axis_selected_iff :
    ∀ i,
      K.signatureReading.selected i ↔
        L.signatureReading.selected (axisMap i)
  coordinate_eq :
    ∀ A i,
      coordinateEquiv i
          (K.signatureReading.coordinate (K.object A) i) =
        L.signatureReading.coordinate
          (L.object (objMap A)) (axisMap i)

namespace ObjectAlgebraHom

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

@[simp] theorem id_objMap (K : ObjectAlgebra U) :
    (id K).objMap = _root_.id :=
  rfl

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

structure SignedExactCoreReadingHom
    (P Q : AATCorePackage U) where
  atomMap : U.Atom → U.Atom
  extraction_eq :
    Q.family = P.family.transport atomMap
  composition_eq :
    ∀ (F : AtomFamily U) (hF : F.ListFinite),
      Q.reading.composition.compose
          (F.transport atomMap) (hF.transport atomMap) =
        (P.reading.composition.compose F hF).transport atomMap
  objectMap : ArchitectureObject U → ArchitectureObject U
  object_formation_eq :
    ∀ C,
      objectMap (P.reading.objectReading.object C) =
        Q.reading.objectReading.object (C.transport atomMap)
  configurationMap :
    ∀ A, ConfigurationHom A.configuration (objectMap A).configuration
  configurationMap_atomMap :
    ∀ A, (configurationMap A).atomMap = atomMap
  lawMap :
    P.algebra.lawReading.lawUniverse.Index →
      Q.algebra.lawReading.lawUniverse.Index
  required_iff :
    ∀ i,
      P.algebra.lawReading.lawUniverse.Required i ↔
        Q.algebra.lawReading.lawUniverse.Required (lawMap i)
  law_holds_iff :
    ∀ i A,
      (P.algebra.lawReading.lawUniverse.law i).holds A ↔
        (Q.algebra.lawReading.lawUniverse.law (lawMap i)).holds
          (objectMap A)
  queryMap : FiniteCircuitDatum U → FiniteCircuitDatum U
  matches_iff :
    ∀ Qry A, Qry.Matches A ↔ (queryMap Qry).Matches (objectMap A)
  accepts_iff :
    ∀ i Qry,
      P.algebra.lawReading.circuits.accepts i Qry = true ↔
        Q.algebra.lawReading.circuits.accepts
          (lawMap i) (queryMap Qry) = true
  operationMap :
    ∀ {A B},
      P.reading.operationReading.Op A B →
        Q.reading.operationReading.Op (objectMap A) (objectMap B)
  operation_naturality :
    ∀ {A B} (op : P.reading.operationReading.Op A B),
      ConfigurationHom.comp
          (Q.reading.operationReading.configurationMap (operationMap op))
          (configurationMap A) =
        ConfigurationHom.comp
          (configurationMap B)
          (P.reading.operationReading.configurationMap op)
  invariantMap :
    P.reading.invariantReading.Index →
      Q.reading.invariantReading.Index
  invariant_transport :
    ∀ i,
      Invariant.TransportedAlong
        (P.reading.invariantReading.invariant i)
        (Q.reading.invariantReading.invariant (invariantMap i))
        _root_.id objectMap
  axisMap :
    P.reading.signatureReading.Axis →
      Q.reading.signatureReading.Axis
  coordinateEquiv :
    ∀ i,
      P.reading.signatureReading.Coordinate i ≃
        Q.reading.signatureReading.Coordinate (axisMap i)
  axis_selected_iff :
    ∀ i,
      P.reading.signatureReading.selected i ↔
        Q.reading.signatureReading.selected (axisMap i)
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

theorem generatedConfiguration_eq
    {P Q : AATCorePackage U}
    (f : SignedExactCoreReadingHom P Q) :
    Q.configuration = P.configuration.transport f.atomMap := by
  unfold AATCorePackage.configuration
  simpa only [f.extraction_eq] using
    f.composition_eq P.family P.reading.family_listFinite

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

@[simp] theorem toObjectAlgebraHom_refl
    (P : AATCorePackage U) :
    (refl P).toObjectAlgebraHom = ObjectAlgebraHom.id P.algebra := by
  apply ObjectAlgebraHom.ext
  · funext A
    apply Subtype.ext
    rfl
  all_goals rfl

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

def FiniteCircuitDatum.Positive
    (Qry : FiniteCircuitDatum U) : Prop :=
  ∀ query expected,
    (query, expected) ∈ Qry.queries → expected = true

def PositiveCircuitDatum
    (P : AATCorePackage U)
    (A : P.algebra.Obj)
    (i : P.algebra.lawReading.lawUniverse.Index) : Type u :=
  {Qry : FiniteCircuitDatum U //
    Qry.Positive ∧
      Qry.Matches (P.algebra.object A) ∧
        P.algebra.lawReading.circuits.accepts i Qry = true}

structure PositiveCoreReadingHom
    (P Q : AATCorePackage U) where
  atomMap : U.Atom → U.Atom
  extraction_mono :
    (P.family.transport atomMap).Subset Q.family
  compositionMap :
    ∀ (F : AtomFamily U) (hF : F.ListFinite),
      ConfigurationHom
        (P.reading.composition.compose F hF)
        (Q.reading.composition.compose
          (F.transport atomMap) (hF.transport atomMap))
  compositionMap_atomMap :
    ∀ F hF, (compositionMap F hF).atomMap = atomMap
  objectMap : ArchitectureObject U → ArchitectureObject U
  object_formation_eq :
    ∀ C,
      objectMap (P.reading.objectReading.object C) =
        Q.reading.objectReading.object (C.transport atomMap)
  base_reachable :
    Q.reading.operationReading.Reachable Q.object (objectMap P.object)
  configurationMap :
    ∀ A, ConfigurationHom A.configuration (objectMap A).configuration
  configurationMap_atomMap :
    ∀ A, (configurationMap A).atomMap = atomMap
  operationMap :
    ∀ {A B},
      P.reading.operationReading.Op A B →
        Q.reading.operationReading.Op (objectMap A) (objectMap B)
  operation_naturality :
    ∀ {A B} (op : P.reading.operationReading.Op A B),
      ConfigurationHom.comp
          (Q.reading.operationReading.configurationMap (operationMap op))
          (configurationMap A) =
        ConfigurationHom.comp
          (configurationMap B)
          (P.reading.operationReading.configurationMap op)
  lawMap :
    P.algebra.lawReading.lawUniverse.Index →
      Q.algebra.lawReading.lawUniverse.Index
  queryMap : FiniteCircuitDatum U → FiniteCircuitDatum U
  positive_preserved :
    ∀ Qry, Qry.Positive → (queryMap Qry).Positive
  matches_of_positive :
    ∀ Qry A, Qry.Positive → Qry.Matches A →
      (queryMap Qry).Matches (objectMap A)
  accepts_mono :
    ∀ i Qry, Qry.Positive →
      P.algebra.lawReading.circuits.accepts i Qry = true →
        Q.algebra.lawReading.circuits.accepts
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

theorem mapReachable
    {P Q : AATCorePackage U}
    (f : PositiveCoreReadingHom P Q)
    {A : ArchitectureObject U}
    (hA : P.reading.operationReading.Reachable P.object A) :
    Q.reading.operationReading.Reachable Q.object (f.objectMap A) :=
  mapReachableAux f hA

def objMap
    {P Q : AATCorePackage U}
    (f : PositiveCoreReadingHom P Q) :
    P.algebra.Obj → Q.algebra.Obj :=
  fun A => ⟨f.objectMap A.1, f.mapReachable A.2⟩

def mapPositiveCircuit
    {P Q : AATCorePackage U}
    (f : PositiveCoreReadingHom P Q)
    {A : P.algebra.Obj}
    {i : P.algebra.lawReading.lawUniverse.Index}
    (c : PositiveCircuitDatum P A i) :
    PositiveCircuitDatum Q (f.objMap A) (f.lawMap i) :=
  ⟨f.queryMap c.1,
    f.positive_preserved c.1 c.2.1,
    f.matches_of_positive c.1 A.1 c.2.1 c.2.2.1,
    f.accepts_mono i c.1 c.2.1 c.2.2.2⟩

end PositiveCoreReadingHom

namespace ReadingCore

abbrev ExactCoreChange
    (p q : ReadingCore.{u, v} U) :=
  SignedExactCoreReadingHom p.core q.core

abbrev PositiveCoreChange
    (p q : ReadingCore.{u, v} U) :=
  PositiveCoreReadingHom p.core q.core

abbrev SelectedCover
    (p : ReadingCore.{u, v} U)
    (base : p.site.category) :=
  Site.AATCoverageFamily p.site.requirements p.site.overlap base

end ReadingCore

end AAT.AG
