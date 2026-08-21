import ResearchLean.AG.DoctrineFiberProduct.CartesianTransport
import ResearchLean.AG.DoctrineFiberProduct.CartesianRegimeSchema

/-!
# Cartesian transport to an arbitrary target package

This module constructs the object-level inverse reindexing needed to turn the
canonical-codomain cartesian theorem into a cartesian lift ending at an
arbitrary package in the target fiber.  Only the upper Atom equivalence is
inverted; the lower source map is never assumed invertible.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u v

open CategoryTheory
open AtomFoundation
open CrossStageCoherence

/-! ## Round trips for primitive reading transport -/

/-- Inverse conjugation of a composition reading is undone by forward conjugation. -/
theorem transportCompositionReading_symm_roundtrip {U : AtomCarrier.{u}}
    (e : U.Atom ≃ U.Atom) (R : CompositionReading U) :
    transportCompositionReading e
        (transportCompositionReading e.symm R) = R := by
  apply CompositionReading.ext
  funext F hF
  simp only [transportCompositionReading]
  rw [atomConfiguration_transport_symm_equiv]
  have hinput :
      (⟨(F.transport e.symm).transport e,
          (hF.transport e.symm).transport e⟩ :
        {G : AtomFamily U // G.ListFinite}) = ⟨F, hF⟩ := by
    apply Subtype.ext
    exact atomFamily_transport_symm_equiv F e
  exact congrArg
    (fun input : {G : AtomFamily U // G.ListFinite} =>
      R.compose input.1 input.2) hinput

/-- Inverse conjugation of an object reading is undone by forward conjugation. -/
theorem transportObjectReading_symm_roundtrip {U : AtomCarrier.{u}}
    (e : U.Atom ≃ U.Atom) (R : ObjectReading U) :
    transportObjectReading e (transportObjectReading e.symm R) = R := by
  apply ObjectReading.ext
  funext C
  simp [transportObjectReading]

/-- Inverse conjugation of one invariant is undone by forward conjugation. -/
theorem transportInvariant_symm_roundtrip {U : AtomCarrier.{u}}
    (e : U.Atom ≃ U.Atom) (I : Invariant U) :
    transportInvariant e (transportInvariant e.symm I) = I := by
  cases I with
  | function I =>
      apply congrArg Invariant.function
      cases I with
      | mk Value evaluate =>
          congr
          funext A
          simp
  | predicate I =>
      apply congrArg Invariant.predicate
      cases I with
      | mk holds =>
          congr
          funext A
          simp

/-- Inverse conjugation of an invariant family is undone by forward conjugation. -/
theorem transportInvariantFamily_symm_roundtrip {U : AtomCarrier.{u}}
    (e : U.Atom ≃ U.Atom) (R : InvariantFamily U) :
    transportInvariantFamily e (transportInvariantFamily e.symm R) = R := by
  cases R with
  | mk Index invariant =>
      change InvariantFamily.mk Index
          (fun i => transportInvariant e (transportInvariant e.symm (invariant i))) =
        InvariantFamily.mk Index invariant
      congr
      funext i
      exact transportInvariant_symm_roundtrip e (invariant i)

/-- Inverse conjugation of a signature is undone by forward conjugation. -/
theorem transportArchitectureSignature_symm_roundtrip {U : AtomCarrier.{u}}
    (e : U.Atom ≃ U.Atom) (S : ArchitectureSignature U) :
    transportArchitectureSignature e
        (transportArchitectureSignature e.symm S) = S := by
  cases S with
  | mk Axis Coordinate selected coordinate =>
      change ArchitectureSignature.mk Axis Coordinate selected
          (fun A i => coordinate
            (transportArchitectureObject e
              (transportArchitectureObject e.symm A)) i) =
        ArchitectureSignature.mk Axis Coordinate selected coordinate
      congr
      funext A i
      simp

/-- Atom maps agree after transporting the dependent endpoints of an operation. -/
private theorem operationConfigurationMap_atomMap_eq {U : AtomCarrier.{u}}
    (R : OperationReading U) {A A' B B' : ArchitectureObject U}
    (hA : A = A') (hB : B = B')
    {op : R.Op A B} {op' : R.Op A' B'} (hop : HEq op op') :
    (R.configurationMap op).atomMap =
      (R.configurationMap op').atomMap := by
  cases hA
  cases hB
  have hop' : op = op' := eq_of_heq hop
  cases hop'
  rfl

/-- Reindexing operation endpoints changes no underlying operation datum. -/
private theorem castOperation_heq {U : AtomCarrier.{u}}
    (R : OperationReading U) {A A' B B' : ArchitectureObject U}
    (hA : A = A') (hB : B = B') (op : R.Op A B) :
    HEq (castOperation R hA hB op) op := by
  cases hA
  cases hB
  rfl

/-- Inverse transport of an operation is its underlying operation up to endpoint casts. -/
private theorem transportOperation_symm_heq {U : AtomCarrier.{u}}
    (e : U.Atom ≃ U.Atom) (R : OperationReading U)
    {A B : ArchitectureObject U} (op : R.Op A B) :
    HEq (transportOperation e.symm R op) op := by
  unfold transportOperation
  exact castOperation_heq R
    (transportArchitectureObject_equiv_symm e.symm A).symm
    (transportArchitectureObject_equiv_symm e.symm B).symm op

/-- Inverse conjugation of an operation reading is undone by forward conjugation. -/
theorem transportOperationReading_symm_roundtrip {U : AtomCarrier.{u}}
    (e : U.Atom ≃ U.Atom) (R : OperationReading U) :
    transportOperationReading e (transportOperationReading e.symm R) = R := by
  let hOp :
      (transportOperationReading e
          (transportOperationReading e.symm R)).Op = R.Op := by
    funext A B
    exact congrArg₂ R.Op
      (transportArchitectureObject_symm_equiv e A)
      (transportArchitectureObject_symm_equiv e B)
  apply OperationReading.ext hOp
  apply Function.hfunext rfl
  intro A A' hA
  cases hA
  apply Function.hfunext rfl
  intro B B' hB
  cases hB
  apply Function.hfunext (congrFun (congrFun hOp A) B)
  intro op op' hop
  have hAeq := transportArchitectureObject_symm_equiv e A
  have hBeq := transportArchitectureObject_symm_equiv e B
  apply heq_of_eq
  apply ConfigurationHom.ext
  funext atom
  simp only [transportOperationReading, castConfigurationHom_atomMap,
    transportConfigurationHom_atomMap]
  rw [operationConfigurationMap_atomMap_eq R hAeq hBeq hop]
  simp [Function.comp_def]

/-! ## Canonical inverse reindexing of a target package -/

/--
The selected source family in the source pointed doctrine is list-finite.

The proof transports the target package's finiteness witness through the inverse
Atom equivalence.  It uses `f.source_eq` only at the selected source and never
constructs an inverse to `f.doctrineHom.sourceMap`.
-/
noncomputable def inverseFamilyListFinite {U : AtomCarrier.{u}}
    {X : ExtractionInstance U} (Q : AATCorePackage U)
    (f : X ⟶ packagePoint Q) :
    (X.doctrine.atomize X.source).ListFinite := by
  let e := f.doctrineHom.atomEquiv
  have hsource :
      f.doctrineHom.sourceMap X.source = Q.reading.source :=
    f.source_eq
  have hfamily :
      Q.family = (X.doctrine.atomize X.source).transport e := by
    calc
      Q.family = Q.reading.doctrine.atomize
          (f.doctrineHom.sourceMap X.source) := by
        exact congrArg Q.reading.doctrine.atomize hsource.symm
      _ = (X.doctrine.atomize X.source).transport e :=
        f.doctrineHom.atomize_naturality X.source
  have hfinite := Q.reading.family_listFinite.transport e.symm
  change (Q.family.transport e.symm).ListFinite at hfinite
  rw [hfamily] at hfinite
  simpa [e] using hfinite

/-- The base object generated by inverse-reindexing the target lower readings. -/
noncomputable def inverseBaseObject {U : AtomCarrier.{u}}
    {X : ExtractionInstance U} (Q : AATCorePackage U)
    (f : X ⟶ packagePoint Q) : ArchitectureObject U :=
  let e := f.doctrineHom.atomEquiv
  let hfinite := inverseFamilyListFinite Q f
  (transportObjectReading e.symm Q.reading.objectReading).object
    ((transportCompositionReading e.symm Q.reading.composition).compose
      (X.doctrine.atomize X.source) hfinite)

/--
The inverse-reindexed lower readings generate exactly the inverse direct image
of the target package's base object.
-/
theorem inverseBaseObject_eq {U : AtomCarrier.{u}}
    {X : ExtractionInstance U} (Q : AATCorePackage U)
    (f : X ⟶ packagePoint Q) :
    inverseBaseObject Q f =
      transportArchitectureObject f.doctrineHom.atomEquiv.symm Q.object := by
  let e := f.doctrineHom.atomEquiv
  let hfinite := inverseFamilyListFinite Q f
  have hsource :
      f.doctrineHom.sourceMap X.source = Q.reading.source :=
    f.source_eq
  have hfamily :
      Q.family = (X.doctrine.atomize X.source).transport e := by
    calc
      Q.family = Q.reading.doctrine.atomize
          (f.doctrineHom.sourceMap X.source) := by
        exact congrArg Q.reading.doctrine.atomize hsource.symm
      _ = (X.doctrine.atomize X.source).transport e :=
        f.doctrineHom.atomize_naturality X.source
  let sourceInput : {F : AtomFamily U // F.ListFinite} :=
    ⟨X.doctrine.atomize X.source, hfinite⟩
  let inverseInput : {F : AtomFamily U // F.ListFinite} :=
    ⟨Q.family.transport e.symm,
      Q.reading.family_listFinite.transport e.symm⟩
  have hinput : sourceInput = inverseInput := by
    apply Subtype.ext
    change X.doctrine.atomize X.source = Q.family.transport e.symm
    calc
      X.doctrine.atomize X.source =
          ((X.doctrine.atomize X.source).transport e).transport e.symm :=
        (atomFamily_transport_equiv_symm
          (X.doctrine.atomize X.source) e).symm
      _ = Q.family.transport e.symm :=
        congrArg (fun F : AtomFamily U => F.transport e.symm) hfamily.symm
  have hcomposition :
      (transportCompositionReading e.symm Q.reading.composition).compose
          sourceInput.1 sourceInput.2 =
        (Q.reading.composition.compose Q.family
          Q.reading.family_listFinite).transport e.symm := by
    calc
      _ = (transportCompositionReading e.symm Q.reading.composition).compose
          inverseInput.1 inverseInput.2 :=
        congrArg
          (fun input : {F : AtomFamily U // F.ListFinite} =>
            (transportCompositionReading e.symm Q.reading.composition).compose
              input.1 input.2) hinput
      _ = _ := transportCompositionReading_compose_transport
        e.symm Q.reading.composition Q.family
          Q.reading.family_listFinite
  change
    (transportObjectReading e.symm Q.reading.objectReading).object
        ((transportCompositionReading e.symm Q.reading.composition).compose
          sourceInput.1 sourceInput.2) = _
  rw [hcomposition]
  exact (transportObjectReading_object_transport e.symm
    Q.reading.objectReading _).symm

/--
Canonical inverse reindexing of every primitive field of a target core reading.
The equation reading is reindexed along the equality of the generated base
object proved above; no equation comparison is accepted as input.
-/
noncomputable def inverseCoreReading {U : AtomCarrier.{u}}
    {X : ExtractionInstance U} (Q : AATCorePackage U)
    (f : X ⟶ packagePoint Q) : CoreReading U :=
  let e := f.doctrineHom.atomEquiv
  let hfinite := inverseFamilyListFinite Q f
  {
    doctrine := X.doctrine
    source := X.source
    family_listFinite := hfinite
    composition := transportCompositionReading e.symm Q.reading.composition
    objectReading := transportObjectReading e.symm Q.reading.objectReading
    equationReading :=
      castEquationReading (inverseBaseObject_eq Q f).symm
        (transportEquationReading e.symm Q.object Q.reading.equationReading)
    invariantReading :=
      transportInvariantFamily e.symm Q.reading.invariantReading
    signatureReading :=
      transportArchitectureSignature e.symm Q.reading.signatureReading
    operationReading :=
      transportOperationReading e.symm Q.reading.operationReading
  }

/-- The target axioms together with its canonically inverse-reindexed reading. -/
noncomputable def inverseCorePackage {U : AtomCarrier.{u}}
    {X : ExtractionInstance U} (Q : AATCorePackage U)
    (f : X ⟶ packagePoint Q) : AATCorePackage U where
  axioms := Q.axioms
  reading := inverseCoreReading Q f

/-- The inverse-reindexed package lies over the source pointed doctrine. -/
@[simp]
theorem inverseCorePackage_point {U : AtomCarrier.{u}}
    {X : ExtractionInstance U} (Q : AATCorePackage U)
    (f : X ⟶ packagePoint Q) :
    packagePoint (inverseCorePackage Q f) = X := by
  cases X
  rfl

/-! ## The generated upper equivalence -/

/-- Reindex the target equation reading of an exact equation transport. -/
private def castTargetEquationExact {U : AtomCarrier.{u}}
    {A₀ A A' : ArchitectureObject U}
    {C₀ : Site.ContextPreorderCategory A₀}
    {E₀ : ArchitecturalEquationSystem C₀}
    (S : EquationReading A) (h : A = A')
    (e : U.Atom ≃ U.Atom)
    (objectMap : ArchitectureObject U → ArchitectureObject U)
    (T : EquationSystemExactTransport E₀ S.equationSystem e objectMap) :
    EquationSystemExactTransport E₀
      (castEquationReading h S).equationSystem e objectMap := by
  cases h
  exact T

/-- Detector compatibility is unchanged by reindexing the target base object. -/
private theorem castTargetEquationExact_detectorCode {U : AtomCarrier.{u}}
    {A₀ A A' : ArchitectureObject U}
    {C₀ : Site.ContextPreorderCategory A₀}
    {E₀ : ArchitecturalEquationSystem C₀}
    (S : EquationReading A) (h : A = A')
    (e : U.Atom ≃ U.Atom)
    (objectMap : ArchitectureObject U → ArchitectureObject U)
    (T : EquationSystemExactTransport E₀ S.equationSystem e objectMap)
    (sourceCode : E₀.Index → CircuitDetectorCode U)
    (hcode : ∀ i,
      S.circuits.code (T.equationMap i) = (sourceCode i).transport e)
    (i : E₀.Index) :
    (castEquationReading h S).circuits.code
        ((castTargetEquationExact S h e objectMap T).equationMap i) =
      (sourceCode i).transport e := by
  cases h
  exact hcode i

/--
The backward upper map from the target package to its inverse reindexing.

Every field is the canonical inverse Atom transport.  In particular, this map
is generated from `Q` and `f`; no upper comparison is accepted as input.
-/
noncomputable def inverseCorePackageBackwardUpper {U : AtomCarrier.{u}}
    {X : ExtractionInstance U} (Q : AATCorePackage U)
    (f : X ⟶ packagePoint Q) :
    SignedExactCoreReadingHom Q (inverseCorePackage Q f) where
  atomEquiv := f.doctrineHom.atomEquiv.symm
  extraction_eq := by
    let e := f.doctrineHom.atomEquiv
    have hsource :
        f.doctrineHom.sourceMap X.source = Q.reading.source :=
      f.source_eq
    have hfamily :
        Q.family = (X.doctrine.atomize X.source).transport e := by
      calc
        Q.family = Q.reading.doctrine.atomize
            (f.doctrineHom.sourceMap X.source) := by
          exact congrArg Q.reading.doctrine.atomize hsource.symm
        _ = (X.doctrine.atomize X.source).transport e :=
          f.doctrineHom.atomize_naturality X.source
    change X.doctrine.atomize X.source = Q.family.transport e.symm
    rw [hfamily]
    exact (atomFamily_transport_equiv_symm
      (X.doctrine.atomize X.source) e).symm
  composition_eq F hF :=
    transportCompositionReading_compose_transport
      f.doctrineHom.atomEquiv.symm Q.reading.composition F hF
  objectMap := transportArchitectureObject f.doctrineHom.atomEquiv.symm
  object_formation_eq C :=
    transportObjectReading_object_transport
      f.doctrineHom.atomEquiv.symm Q.reading.objectReading C
  configurationMap A :=
    AtomConfiguration.transportHom f.doctrineHom.atomEquiv.symm A.configuration
  configurationMap_atomMap _ := rfl
  configuration_eq _ := rfl
  equationTransport :=
    castTargetEquationExact
      (transportEquationReading f.doctrineHom.atomEquiv.symm
        Q.object Q.reading.equationReading)
      (inverseBaseObject_eq Q f).symm
      f.doctrineHom.atomEquiv.symm
      (transportArchitectureObject f.doctrineHom.atomEquiv.symm)
      (transportEquationSystemExact f.doctrineHom.atomEquiv.symm
        Q.object Q.reading.equationReading.contextPreorder
        Q.reading.equationReading.equationSystem)
  detectorCode_eq i := by
    apply castTargetEquationExact_detectorCode
      (transportEquationReading f.doctrineHom.atomEquiv.symm
        Q.object Q.reading.equationReading)
      (inverseBaseObject_eq Q f).symm
      f.doctrineHom.atomEquiv.symm
      (transportArchitectureObject f.doctrineHom.atomEquiv.symm)
      (transportEquationSystemExact f.doctrineHom.atomEquiv.symm
        Q.object Q.reading.equationReading.contextPreorder
        Q.reading.equationReading.equationSystem)
      Q.reading.equationReading.circuits.code
    intro j
    rfl
  operationMap op :=
    transportOperation f.doctrineHom.atomEquiv.symm
      Q.reading.operationReading op
  operation_naturality op :=
    transportOperation_naturality f.doctrineHom.atomEquiv.symm
      Q.reading.operationReading op
  invariantMap := _root_.id
  invariant_transport i :=
    invariant_transportAlong f.doctrineHom.atomEquiv.symm
      (Q.reading.invariantReading.invariant i)
  axisMap := _root_.id
  coordinateEquiv _ := Equiv.refl _
  axis_selected_iff _ := Iff.rfl
  coordinate_eq A i :=
    (transportArchitectureSignature_coordinate
      f.doctrineHom.atomEquiv.symm Q.reading.signatureReading A i).symm

/-- Reindex the source equation reading of an exact equation transport. -/
private def castSourceEquationExact {U : AtomCarrier.{u}}
    {A A' B : ArchitectureObject U}
    {D : Site.ContextPreorderCategory B}
    {G : ArchitecturalEquationSystem D}
    (h : A = A') (S : EquationReading A)
    (e : U.Atom ≃ U.Atom)
    (objectMap : ArchitectureObject U → ArchitectureObject U)
    (T : EquationSystemExactTransport S.equationSystem G e objectMap) :
    EquationSystemExactTransport
      (castEquationReading h S).equationSystem G e objectMap := by
  cases h
  exact T

/-- Target and source base reindexing cancel around equation composition. -/
private theorem castTargetEquationExact_comp_castSource
    {U : AtomCarrier.{u}}
    {A₀ A A' B : ArchitectureObject U}
    {C₀ : Site.ContextPreorderCategory A₀}
    {E₀ : ArchitecturalEquationSystem C₀}
    {D : Site.ContextPreorderCategory B}
    {G : ArchitecturalEquationSystem D}
    (S : EquationReading A) (h : A = A')
    (e t : U.Atom ≃ U.Atom)
    (objectMap₁ objectMap₂ : ArchitectureObject U → ArchitectureObject U)
    (T : EquationSystemExactTransport E₀ S.equationSystem e objectMap₁)
    (K : EquationSystemExactTransport S.equationSystem G t objectMap₂) :
    HEq
      ((castTargetEquationExact S h e objectMap₁ T).comp
        (castSourceEquationExact h S t objectMap₂ K))
      (T.comp K) := by
  cases h
  rfl

/-- Source and target base reindexing also cancel in the reverse composition. -/
private theorem castSourceEquationExact_comp_castTarget
    {U : AtomCarrier.{u}}
    {A A' B : ArchitectureObject U}
    {D : Site.ContextPreorderCategory B}
    {G : ArchitecturalEquationSystem D}
    (S : EquationReading A) (h : A = A')
    (e t : U.Atom ≃ U.Atom)
    (objectMap₁ objectMap₂ : ArchitectureObject U → ArchitectureObject U)
    (K : EquationSystemExactTransport S.equationSystem G e objectMap₁)
    (T : EquationSystemExactTransport G S.equationSystem t objectMap₂) :
    HEq
      ((castSourceEquationExact h S e objectMap₁ K).comp
        (castTargetEquationExact S h t objectMap₂ T))
      (K.comp T) := by
  cases h
  rfl

/-- Identity equation transport is unchanged by reindexing its base object. -/
private theorem equationExact_refl_cast_heq {U : AtomCarrier.{u}}
    {A A' : ArchitectureObject U} (S : EquationReading A)
    (h : A = A') :
    HEq (EquationSystemExactTransport.refl S.equationSystem)
      (EquationSystemExactTransport.refl
        (castEquationReading h S).equationSystem) := by
  cases h
  rfl

/-- Source-base reindexing retains an identity equation-index map. -/
private theorem castSourceEquationExact_equationMap_heq
    {U : AtomCarrier.{u}}
    {A A' B : ArchitectureObject U}
    {D : Site.ContextPreorderCategory B}
    {G : ArchitecturalEquationSystem D}
    (h : A = A') (S : EquationReading A)
    (e : U.Atom ≃ U.Atom)
    (objectMap : ArchitectureObject U → ArchitectureObject U)
    (T : EquationSystemExactTransport S.equationSystem G e objectMap)
    (hmap : ∀ i, HEq (T.equationMap i) i)
    (i : (castEquationReading h S).equationSystem.Index) :
    HEq ((castSourceEquationExact h S e objectMap T).equationMap i) i := by
  cases h
  exact hmap i

/-- Source-base reindexing preserves detector compatibility. -/
private theorem castSourceEquationExact_detectorCode
    {U : AtomCarrier.{u}}
    {A A' B : ArchitectureObject U}
    {D : Site.ContextPreorderCategory B}
    {G : ArchitecturalEquationSystem D}
    (h : A = A') (S : EquationReading A)
    (e : U.Atom ≃ U.Atom)
    (objectMap : ArchitectureObject U → ArchitectureObject U)
    (T : EquationSystemExactTransport S.equationSystem G e objectMap)
    (targetCode : G.Index → CircuitDetectorCode U)
    (hcode : ∀ i,
      targetCode (T.equationMap i) = (S.circuits.code i).transport e)
    (i : (castEquationReading h S).equationSystem.Index) :
    targetCode
        ((castSourceEquationExact h S e objectMap T).equationMap i) =
      ((castEquationReading h S).circuits.code i).transport e := by
  cases h
  exact hcode i

/-- The inverse and forward Atom equivalences compose to the identity. -/
private def inverseCompositeEquationRefl {U : AtomCarrier.{u}}
    {A : ArchitectureObject U}
    {C : Site.ContextPreorderCategory A}
    (E : ArchitecturalEquationSystem C) (e : U.Atom ≃ U.Atom) :
    EquationSystemExactTransport E E (e.symm.trans e) _root_.id where
  contextEquivalence := CategoryTheory.Equivalence.refl
  equationEquiv := Equiv.refl _
  role_eq _ := rfl
  observableEquiv _ := RingEquiv.refl _
  observable_naturality := by intros; rfl
  violationCoordinate_eq := by intros; simp
  equationResidual_eq := by intros; simp

/-- Extensionality for the computational fields of exact equation transport. -/
private theorem equationExact_ext {U : AtomCarrier.{u}}
    {A B : ArchitectureObject U}
    {C : Site.ContextPreorderCategory A}
    {D : Site.ContextPreorderCategory B}
    {E : ArchitecturalEquationSystem C}
    {G : ArchitecturalEquationSystem D}
    {e : U.Atom ≃ U.Atom}
    {objectMap : ArchitectureObject U → ArchitectureObject U}
    {T S : EquationSystemExactTransport E G e objectMap}
    (hcontext : T.contextEquivalence = S.contextEquivalence)
    (hequation : T.equationEquiv = S.equationEquiv)
    (hobservable : HEq T.observableEquiv S.observableEquiv) : T = S := by
  cases T
  cases S
  cases hcontext
  cases hequation
  cases hobservable
  rfl

/-- Heterogeneous extensionality across equal transport parameters. -/
private theorem equationExact_hext {U : AtomCarrier.{u}}
    {A B : ArchitectureObject U}
    {C : Site.ContextPreorderCategory A}
    {D : Site.ContextPreorderCategory B}
    {E : ArchitecturalEquationSystem C}
    {G : ArchitecturalEquationSystem D}
    {e e' : U.Atom ≃ U.Atom}
    {objectMap objectMap' : ArchitectureObject U → ArchitectureObject U}
    {T : EquationSystemExactTransport E G e objectMap}
    {S : EquationSystemExactTransport E G e' objectMap'}
    (he : e = e') (hobjectMap : objectMap = objectMap')
    (hcontext : T.contextEquivalence = S.contextEquivalence)
    (hequation : T.equationEquiv = S.equationEquiv)
    (hobservable : HEq T.observableEquiv S.observableEquiv) : HEq T S := by
  cases he
  cases hobjectMap
  exact heq_of_eq (equationExact_ext hcontext hequation hobservable)

/-- Equal subsingleton types have heterogeneously equal inhabitants. -/
private theorem subsingleton_heq_of_type_eq_local
    {alpha beta : Sort v} [Subsingleton alpha] [Subsingleton beta]
    (h : alpha = beta) (a : alpha) (b : beta) : HEq a b := by
  cases h
  exact heq_of_eq (Subsingleton.elim _ _)

/-- Identity followed by an indexed ring cast is heterogeneously identity. -/
private theorem ringEquiv_refl_trans_cast_heq_refl
    {index : Type*} {R : index → Type*}
    [(i : index) → CommRing (R i)]
    {i j : index} (h : i = j) :
    HEq ((RingEquiv.refl (R i)).trans (RingEquiv.cast (R := R) h))
      (RingEquiv.refl (R i)) := by
  cases h
  rfl

/-- The inverse context transport followed by forward transport is identity. -/
private theorem inverseContextEquivalence_comp_transport {U : AtomCarrier.{u}}
    (e : U.Atom ≃ U.Atom) (A : ArchitectureObject U)
    (C : Site.ContextPreorderCategory A) :
    ((transportContextEquivalence e A C).symm.trans
        CategoryTheory.Equivalence.refl).trans
      (transportContextEquivalence e A C) =
        CategoryTheory.Equivalence.refl := by
  have hfunctor :
      (((transportContextEquivalence e A C).symm.trans
          CategoryTheory.Equivalence.refl).trans
        (transportContextEquivalence e A C)).functor =
          𝟭 (Site.ContextCategoryObject (transportContextPreorder e A C)) := by
    refine CategoryTheory.Functor.ext (fun W => ?_) ?_
    · exact transportContextFunctorInverse_obj_eq e A C W
    · intros
      exact Subsingleton.elim _ _
  have hinverse :
      (((transportContextEquivalence e A C).symm.trans
          CategoryTheory.Equivalence.refl).trans
        (transportContextEquivalence e A C)).inverse =
          𝟭 (Site.ContextCategoryObject (transportContextPreorder e A C)) := by
    refine CategoryTheory.Functor.ext (fun W => ?_) ?_
    · exact transportContextFunctorInverse_obj_eq e A C W
    · intros
      exact Subsingleton.elim _ _
  apply CategoryTheory.Equivalence.ext hfunctor hinverse
  · apply subsingleton_heq_of_type_eq_local
    apply congrArg
      (fun F => (𝟭 (Site.ContextCategoryObject
        (transportContextPreorder e A C))) ≅ F)
    rw [hfunctor, hinverse]
    rfl
  · apply subsingleton_heq_of_type_eq_local
    apply congrArg
      (fun F => F ≅ (𝟭 (Site.ContextCategoryObject
        (transportContextPreorder e A C))))
    rw [hfunctor, hinverse]
    rfl

/-- The generated identity-shaped equation transport is the true identity. -/
private theorem inverseCompositeEquationRefl_heq {U : AtomCarrier.{u}}
    {A : ArchitectureObject U}
    {C : Site.ContextPreorderCategory A}
    (E : ArchitecturalEquationSystem C) (e : U.Atom ≃ U.Atom) :
    HEq (inverseCompositeEquationRefl E e)
      (EquationSystemExactTransport.refl E) := by
  apply equationExact_hext
  · apply Equiv.ext
    intro atom
    simp
  · rfl
  · rfl
  · rfl
  · rfl

/-- The divided inverse equation transport also cancels in the reverse order. -/
private theorem inverseEquationForward_comp_backward_raw
    {U : AtomCarrier.{u}}
    (Q : AATCorePackage U) (e : U.Atom ≃ U.Atom) :
    HEq
      ((deconjugateEquationSystemExact e.symm e Q.object
          Q.reading.equationReading.contextPreorder
          Q.reading.equationReading.equationSystem _root_.id
          (inverseCompositeEquationRefl
            Q.reading.equationReading.equationSystem e)).comp
        (transportEquationSystemExact e.symm Q.object
          Q.reading.equationReading.contextPreorder
          Q.reading.equationReading.equationSystem))
      (EquationSystemExactTransport.refl
        (transportEquationSystem e.symm Q.object
          Q.reading.equationReading.contextPreorder
          Q.reading.equationReading.equationSystem)) := by
  apply equationExact_hext
  · apply Equiv.ext
    intro atom
    simp
  · funext A
    exact transportArchitectureObject_equiv_symm e A
  · exact inverseContextEquivalence_comp_transport e.symm Q.object
      Q.reading.equationReading.contextPreorder
  · apply Equiv.ext
    intro i
    rfl
  · apply Function.hfunext rfl
    intro W W' hW
    cases hW
    have hround := transportContextFunctorInverse_obj_eq e.symm Q.object
      Q.reading.equationReading.contextPreorder W
    change HEq
      ((RingEquiv.refl _).trans
        (transportObservableEquiv e.symm Q.object
          Q.reading.equationReading.contextPreorder
          Q.reading.equationReading.equationSystem
          ((transportContextInverse e.symm Q.object
            Q.reading.equationReading.contextPreorder).obj W)))
      (RingEquiv.refl _)
    have hcast :
        transportObservableEquiv e.symm Q.object
            Q.reading.equationReading.contextPreorder
            Q.reading.equationReading.equationSystem
            ((transportContextInverse e.symm Q.object
              Q.reading.equationReading.contextPreorder).obj W) =
          RingEquiv.cast
            (R := fun X : Site.ContextCategoryObject
              (transportContextPreorder e.symm Q.object
                Q.reading.equationReading.contextPreorder) =>
              (transportEquationSystem e.symm Q.object
                Q.reading.equationReading.contextPreorder
                Q.reading.equationReading.equationSystem).Observable X)
            hround.symm := by
      apply RingEquiv.ext
      intro x
      rfl
    rw [hcast]
    exact ringEquiv_refl_trans_cast_heq_refl hround.symm

/--
Exact equation transport from the inverse-reindexed package back to the target.
It is obtained by dividing the identity equation transport by the inverse
canonical conjugation.
-/
noncomputable def inverseCoreEquationForward {U : AtomCarrier.{u}}
    {X : ExtractionInstance U} (Q : AATCorePackage U)
    (f : X ⟶ packagePoint Q) :
    EquationSystemExactTransport
      (inverseCorePackage Q f).algebra.equationSystem
      Q.algebra.equationSystem f.doctrineHom.atomEquiv
      (transportArchitectureObject f.doctrineHom.atomEquiv) :=
  castSourceEquationExact
    (inverseBaseObject_eq Q f).symm
    (transportEquationReading f.doctrineHom.atomEquiv.symm
      Q.object Q.reading.equationReading)
    f.doctrineHom.atomEquiv
    (transportArchitectureObject f.doctrineHom.atomEquiv)
    (deconjugateEquationSystemExact f.doctrineHom.atomEquiv.symm
      f.doctrineHom.atomEquiv Q.object
      Q.reading.equationReading.contextPreorder
      Q.reading.equationReading.equationSystem _root_.id
      (inverseCompositeEquationRefl
        Q.reading.equationReading.equationSystem
        f.doctrineHom.atomEquiv))

/-- The generated forward equation transport retains the equation index. -/
@[simp]
theorem inverseCoreEquationForward_equationMap_heq {U : AtomCarrier.{u}}
    {X : ExtractionInstance U} (Q : AATCorePackage U)
    (f : X ⟶ packagePoint Q)
    (i : (inverseCorePackage Q f).algebra.equationSystem.Index) :
    HEq ((inverseCoreEquationForward Q f).equationMap i) i := by
  apply castSourceEquationExact_equationMap_heq
  intro j
  rfl

/-- The generated forward equation map transports exactly the authored detector code. -/
theorem inverseCoreEquationForward_detectorCode {U : AtomCarrier.{u}}
    {X : ExtractionInstance U} (Q : AATCorePackage U)
    (f : X ⟶ packagePoint Q)
    (i : (inverseCorePackage Q f).algebra.equationSystem.Index) :
    Q.algebra.circuits.code
        ((inverseCoreEquationForward Q f).equationMap i) =
      ((inverseCorePackage Q f).algebra.circuits.code i).transport
        f.doctrineHom.atomEquiv := by
  apply castSourceEquationExact_detectorCode
  intro j
  change Q.reading.equationReading.circuits.code j =
    ((Q.reading.equationReading.circuits.code j).transport
      f.doctrineHom.atomEquiv.symm).transport f.doctrineHom.atomEquiv
  simp

/--
The forward upper map from the inverse-reindexed package to the requested
target.  It is generated entirely by inverse Atom conjugation and its canonical
round trips.
-/
noncomputable def inverseCorePackageForwardUpper {U : AtomCarrier.{u}}
    {X : ExtractionInstance U} (Q : AATCorePackage U)
    (f : X ⟶ packagePoint Q) :
    SignedExactCoreReadingHom (inverseCorePackage Q f) Q where
  atomEquiv := f.doctrineHom.atomEquiv
  extraction_eq := by
    have hsource :
        f.doctrineHom.sourceMap X.source = Q.reading.source :=
      f.source_eq
    change Q.family =
      (X.doctrine.atomize X.source).transport f.doctrineHom.atomEquiv
    calc
      Q.family = Q.reading.doctrine.atomize
          (f.doctrineHom.sourceMap X.source) := by
        exact congrArg Q.reading.doctrine.atomize hsource.symm
      _ = (X.doctrine.atomize X.source).transport
          f.doctrineHom.atomEquiv :=
        f.doctrineHom.atomize_naturality X.source
  composition_eq F hF := by
    have h := transportCompositionReading_compose_transport
      f.doctrineHom.atomEquiv
      (transportCompositionReading f.doctrineHom.atomEquiv.symm
        Q.reading.composition) F hF
    rw [transportCompositionReading_symm_roundtrip
      f.doctrineHom.atomEquiv Q.reading.composition] at h
    exact h
  objectMap := transportArchitectureObject f.doctrineHom.atomEquiv
  object_formation_eq C := by
    have h := transportObjectReading_object_transport
      f.doctrineHom.atomEquiv
      (transportObjectReading f.doctrineHom.atomEquiv.symm
        Q.reading.objectReading) C
    rw [transportObjectReading_symm_roundtrip
      f.doctrineHom.atomEquiv Q.reading.objectReading] at h
    exact h
  configurationMap A :=
    AtomConfiguration.transportHom f.doctrineHom.atomEquiv A.configuration
  configurationMap_atomMap _ := rfl
  configuration_eq _ := rfl
  equationTransport := inverseCoreEquationForward Q f
  detectorCode_eq i := inverseCoreEquationForward_detectorCode Q f i
  operationMap op := op
  operation_naturality {A B} op := by
    apply ConfigurationHom.ext
    funext atom
    simp [inverseCorePackage, inverseCoreReading,
      transportOperationReading, ConfigurationHom.comp,
      castConfigurationHom_atomMap, transportConfigurationHom_atomMap,
      Function.comp_def]
  invariantMap := _root_.id
  invariant_transport i := by
    apply invariant_transport_deconjugate
      f.doctrineHom.atomEquiv.symm
      (Q.reading.invariantReading.invariant i)
      (Q.reading.invariantReading.invariant i)
      _root_.id
    exact Invariant.transportedAlong_refl
      (Q.reading.invariantReading.invariant i) _root_.id
  axisMap := _root_.id
  coordinateEquiv _ := Equiv.refl _
  axis_selected_iff _ := Iff.rfl
  coordinate_eq A i := by
    simp [inverseCorePackage, inverseCoreReading,
      transportArchitectureSignature]

/-- Equation transports cancel in the target-to-source-to-target direction. -/
private theorem inverseCorePackageBackward_comp_forward_equation
    {U : AtomCarrier.{u}}
    {X : ExtractionInstance U} (Q : AATCorePackage U)
    (f : X ⟶ packagePoint Q) :
    HEq
      ((inverseCorePackageBackwardUpper Q f).equationTransport.comp
        (inverseCorePackageForwardUpper Q f).equationTransport)
      (EquationSystemExactTransport.refl Q.algebra.equationSystem) := by
  let e := f.doctrineHom.atomEquiv
  let S := transportEquationReading e.symm
    Q.object Q.reading.equationReading
  let hbase := (inverseBaseObject_eq Q f).symm
  let T := transportEquationSystemExact e.symm Q.object
    Q.reading.equationReading.contextPreorder
    Q.reading.equationReading.equationSystem
  let H := inverseCompositeEquationRefl
    Q.reading.equationReading.equationSystem e
  let D := deconjugateEquationSystemExact e.symm e Q.object
    Q.reading.equationReading.contextPreorder
    Q.reading.equationReading.equationSystem _root_.id H
  have hcast : HEq
      ((castTargetEquationExact S hbase e.symm
          (transportArchitectureObject e.symm) T).comp
        (castSourceEquationExact hbase S e
          (transportArchitectureObject e) D))
      (T.comp D) :=
    castTargetEquationExact_comp_castSource S hbase e.symm e
      (transportArchitectureObject e.symm)
      (transportArchitectureObject e) T D
  have hcancel : HEq (T.comp D) H :=
    transportEquationSystemExact_comp_deconjugate e.symm e Q.object
      Q.reading.equationReading.contextPreorder
      Q.reading.equationReading.equationSystem _root_.id H
  exact HEq.trans
    (by
      simpa [e, S, hbase, T, H, D,
        inverseCorePackageBackwardUpper,
        inverseCorePackageForwardUpper,
        inverseCoreEquationForward] using hcast)
    (HEq.trans hcancel
      (inverseCompositeEquationRefl_heq
        Q.reading.equationReading.equationSystem e))

/-- Equation transports cancel in the source-to-target-to-source direction. -/
private theorem inverseCorePackageForward_comp_backward_equation
    {U : AtomCarrier.{u}}
    {X : ExtractionInstance U} (Q : AATCorePackage U)
    (f : X ⟶ packagePoint Q) :
    HEq
      ((inverseCorePackageForwardUpper Q f).equationTransport.comp
        (inverseCorePackageBackwardUpper Q f).equationTransport)
      (EquationSystemExactTransport.refl
        (inverseCorePackage Q f).algebra.equationSystem) := by
  let e := f.doctrineHom.atomEquiv
  let S := transportEquationReading e.symm
    Q.object Q.reading.equationReading
  let hbase := (inverseBaseObject_eq Q f).symm
  let T := transportEquationSystemExact e.symm Q.object
    Q.reading.equationReading.contextPreorder
    Q.reading.equationReading.equationSystem
  let H := inverseCompositeEquationRefl
    Q.reading.equationReading.equationSystem e
  let D := deconjugateEquationSystemExact e.symm e Q.object
    Q.reading.equationReading.contextPreorder
    Q.reading.equationReading.equationSystem _root_.id H
  have hcast : HEq
      ((castSourceEquationExact hbase S e
          (transportArchitectureObject e) D).comp
        (castTargetEquationExact S hbase e.symm
          (transportArchitectureObject e.symm) T))
      (D.comp T) :=
    castSourceEquationExact_comp_castTarget S hbase e e.symm
      (transportArchitectureObject e)
      (transportArchitectureObject e.symm) D T
  have hcancel : HEq (D.comp T)
      (EquationSystemExactTransport.refl S.equationSystem) := by
    exact inverseEquationForward_comp_backward_raw Q e
  exact HEq.trans
    (by
      simpa [e, S, hbase, T, H, D,
        inverseCorePackageForwardUpper,
        inverseCorePackageBackwardUpper,
        inverseCoreEquationForward] using hcast)
    (HEq.trans hcancel (equationExact_refl_cast_heq S hbase))

/-- The generated backward upper map followed by the forward map is identity. -/
theorem inverseCorePackageBackward_comp_forward {U : AtomCarrier.{u}}
    {X : ExtractionInstance U} (Q : AATCorePackage U)
    (f : X ⟶ packagePoint Q) :
    (inverseCorePackageBackwardUpper Q f).comp
        (inverseCorePackageForwardUpper Q f) =
      SignedExactCoreReadingHom.refl Q := by
  apply SignedExactCoreReadingHom.ext
  · apply Equiv.ext
    intro atom
    simp [SignedExactCoreReadingHom.comp,
      inverseCorePackageBackwardUpper,
      inverseCorePackageForwardUpper,
      SignedExactCoreReadingHom.refl]
  · funext A
    exact transportArchitectureObject_symm_equiv
      f.doctrineHom.atomEquiv A
  · exact inverseCorePackageBackward_comp_forward_equation Q f
  · apply Function.hfunext rfl
    intro A A' hA
    cases hA
    apply Function.hfunext rfl
    intro B B' hB
    cases hB
    apply Function.hfunext rfl
    intro op op' hop
    cases hop
    exact transportOperation_symm_heq f.doctrineHom.atomEquiv
      Q.reading.operationReading op
  · rfl
  · rfl
  · apply Function.hfunext rfl
    intro i i' hi
    cases hi
    apply heq_of_eq
    apply Equiv.ext
    intro coordinate
    rfl

/-- The generated forward upper map followed by the backward map is identity. -/
theorem inverseCorePackageForward_comp_backward {U : AtomCarrier.{u}}
    {X : ExtractionInstance U} (Q : AATCorePackage U)
    (f : X ⟶ packagePoint Q) :
    (inverseCorePackageForwardUpper Q f).comp
        (inverseCorePackageBackwardUpper Q f) =
      SignedExactCoreReadingHom.refl (inverseCorePackage Q f) := by
  apply SignedExactCoreReadingHom.ext
  · apply Equiv.ext
    intro atom
    simp [SignedExactCoreReadingHom.comp,
      inverseCorePackageForwardUpper,
      inverseCorePackageBackwardUpper,
      SignedExactCoreReadingHom.refl]
  · funext A
    exact transportArchitectureObject_equiv_symm
      f.doctrineHom.atomEquiv A
  · exact inverseCorePackageForward_comp_backward_equation Q f
  · apply Function.hfunext rfl
    intro A A' hA
    cases hA
    apply Function.hfunext rfl
    intro B B' hB
    cases hB
    apply Function.hfunext rfl
    intro op op' hop
    cases hop
    exact transportOperation_symm_heq f.doctrineHom.atomEquiv
      Q.reading.operationReading op
  · rfl
  · rfl
  · apply Function.hfunext rfl
    intro i i' hi
    cases hi
    apply heq_of_eq
    apply Equiv.ext
    intro coordinate
    rfl

/-! ## Strong cartesianness from a generated upper inverse -/

/--
The total hom from the inverse-reindexed package to the requested target.
Its lower component is exactly the supplied pointed morphism.
-/
noncomputable def inverseCorePackageHom {U : AtomCarrier.{u}}
    {X : ExtractionInstance U} (Q : AATCorePackage U)
    (f : X ⟶ packagePoint Q) :
    PackageTotalHom (inverseCorePackage Q f) Q where
  base := f
  upper := inverseCorePackageForwardUpper Q f
  atomEquiv_eq := rfl

/--
A total package hom with a specified two-sided upper inverse is strongly
cartesian.  This conditional criterion assumes only upper data, never an
inverse of the lower pointed doctrine morphism.  The arbitrary-target theorem
below instantiates every argument here with named constructions.
-/
theorem packageTotalHom_isStronglyCartesian_of_upper_inverse
    {U : AtomCarrier.{u}} {P Q : AATCorePackage U}
    (φ : PackageTotalHom P Q)
    (inv : SignedExactCoreReadingHom Q P)
    (hom_inv : φ.upper.comp inv = SignedExactCoreReadingHom.refl P)
    (inv_hom : inv.comp φ.upper = SignedExactCoreReadingHom.refl Q) :
    (packageProjection U).IsStronglyCartesian φ.base φ := by
  letI : (packageProjection U).IsHomLift φ.base φ := by
    change (packageProjection U).IsHomLift
      ((packageProjection U).map φ) φ
    infer_instance
  apply CategoryTheory.Functor.IsStronglyCartesian.mk
  intro R g h hLift
  have hbase : h.base = g.comp φ.base := by
    exact (CategoryTheory.IsHomLift.eq_of_isHomLift
      (packageProjection U) (g.comp φ.base) h).symm
  let k : PackageTotalHom R P := {
    base := g
    upper := h.upper.comp inv
    atomEquiv_eq := by
      apply Equiv.ext
      intro atom
      change inv.atomEquiv (h.upper.atomEquiv atom) =
        g.doctrineHom.atomEquiv atom
      rw [h.atomEquiv_eq]
      have hbaseAtom := congrArg
        (fun base => base.doctrineHom.atomEquiv atom) hbase
      change h.base.doctrineHom.atomEquiv atom =
        φ.base.doctrineHom.atomEquiv (g.doctrineHom.atomEquiv atom)
          at hbaseAtom
      rw [hbaseAtom, ← φ.atomEquiv_eq]
      have hcancel := congrArg
        (fun upper => upper.atomEquiv (g.doctrineHom.atomEquiv atom))
        hom_inv
      simpa [SignedExactCoreReadingHom.comp,
        SignedExactCoreReadingHom.refl] using hcancel
  }
  have hkfac : k.comp φ = h := by
    apply PackageTotalHom.ext
    · exact hbase.symm
    · change (h.upper.comp inv).comp φ.upper = h.upper
      rw [PackageTotalHom.upper_comp_assoc, inv_hom,
        PackageTotalHom.upper_comp_id]
  refine ⟨k, ?_, ?_⟩
  · constructor
    · change (packageProjection U).IsHomLift g k
      change (packageProjection U).IsHomLift
        ((packageProjection U).map k) k
      infer_instance
    · exact hkfac
  · intro k' hk'
    apply PackageTotalHom.ext
    · letI : (packageProjection U).IsHomLift g k' := hk'.1
      exact (CategoryTheory.IsHomLift.eq_of_isHomLift
        (packageProjection U) g k').symm
    · have hupper : k'.upper.comp φ.upper = h.upper := by
        simpa [PackageTotalHom.comp] using
          congrArg PackageTotalHom.upper hk'.2
      change k'.upper = h.upper.comp inv
      calc
        k'.upper = k'.upper.comp (SignedExactCoreReadingHom.refl P) :=
          (PackageTotalHom.upper_comp_id k'.upper).symm
        _ = k'.upper.comp (φ.upper.comp inv) := by rw [hom_inv]
        _ = (k'.upper.comp φ.upper).comp inv := by
          rw [PackageTotalHom.upper_comp_assoc]
        _ = h.upper.comp inv := by rw [hupper]

/-- The upper-inverse criterion after transporting endpoint equalities. -/
theorem packageTotalHom_isStronglyCartesian_of_upper_inverse_lift
    {U : AtomCarrier.{u}}
    {X Y : ExtractionInstance U}
    {P Q : AATCorePackage U}
    (base : X ⟶ Y) (φ : PackageTotalHom P Q)
    [hLift : (packageProjection U).IsHomLift base φ]
    (inv : SignedExactCoreReadingHom Q P)
    (hom_inv : φ.upper.comp inv = SignedExactCoreReadingHom.refl P)
    (inv_hom : inv.comp φ.upper = SignedExactCoreReadingHom.refl Q) :
    (packageProjection U).IsStronglyCartesian base φ := by
  subst_hom_lift (packageProjection U) base φ
  change (packageProjection U).IsStronglyCartesian φ.base φ
  exact packageTotalHom_isStronglyCartesian_of_upper_inverse
    φ inv hom_inv inv_hom

/-- The generated hom to an arbitrary target package is strongly cartesian. -/
theorem inverseCorePackageHom_isStronglyCartesian {U : AtomCarrier.{u}}
    {X : ExtractionInstance U} (Q : AATCorePackage U)
    (f : X ⟶ packagePoint Q) :
    (packageProjection U).IsStronglyCartesian f
      (inverseCorePackageHom Q f) :=
  packageTotalHom_isStronglyCartesian_of_upper_inverse
    (inverseCorePackageHom Q f)
    (inverseCorePackageBackwardUpper Q f)
    (inverseCorePackageForward_comp_backward Q f)
    (inverseCorePackageBackward_comp_forward Q f)

/-! ## Arbitrary target lifts and the global branch -/

/--
Construct a strong cartesian lift of any semantic bottom arrow to every package
in its target fiber.
-/
noncomputable def strongCartesianLiftOfTarget {U : AtomCarrier.{u}}
    (input : CartSemanticInput U)
    (targetPackage : CoreFiber input.target) :
    StrongCartesianLift input targetPackage := by
  rcases targetPackage with ⟨Q, hQ⟩
  let aligned : input.source ⟶ packagePoint Q :=
    input.hom ≫ eqToHom hQ.symm
  let φ := inverseCorePackageHom Q aligned
  letI : (packageProjection U).IsHomLift input.hom φ := by
    apply CategoryTheory.IsHomLift.of_fac'
      (packageProjection U) input.hom φ
      (inverseCorePackage_point Q aligned) hQ
    simp [φ, aligned, inverseCorePackageHom]
  exact {
    domain := inverseCorePackage Q aligned
    hom := φ
    isStronglyCartesian :=
      packageTotalHom_isStronglyCartesian_of_upper_inverse_lift
        input.hom φ (inverseCorePackageBackwardUpper Q aligned)
        (inverseCorePackageForward_comp_backward Q aligned)
        (inverseCorePackageBackward_comp_forward Q aligned)
  }

/-- The carrier-global left branch of the G-110 cartesian-lift disjunction. -/
theorem globalCartesianLift : GlobalCartesianLift.{u} := by
  intro U _ input targetPackage
  exact ⟨strongCartesianLiftOfTarget input.semantic targetPackage⟩

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
