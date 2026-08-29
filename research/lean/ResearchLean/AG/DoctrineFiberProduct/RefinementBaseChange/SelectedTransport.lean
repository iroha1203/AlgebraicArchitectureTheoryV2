import ResearchLean.AG.DoctrineFiberProduct.CartesianTransport
import ResearchLean.AG.DoctrineFiberProduct.CartesianRegimeSchema

/-!
# Cartesian transport to an arbitrary target package

This module constructs the object-level inverse reindexing needed to turn the
canonical-codomain cartesian theorem into a cartesian lift ending at an
arbitrary package in the target fiber.  Only the upper Atom equivalence is
inverted; the lower source map is never assumed invertible.
-/

namespace AAT.AG.DoctrineFiberProduct.SelectedRefinementTransport

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
The exact datum needed to re-author one actual target package at a selected
source.  Unlike an `ExtInstHom`, it asks for no global extraction reflection:
the family equality concerns only the selected source and the actual target
package.
-/
structure SelectedTransportData {U : AtomCarrier.{u}}
    (X : ExtractionInstance U) (Q : AATCorePackage U) where
  /-- Atom equivalence of the authored pointed refinement. -/
  atomEquiv : U.Atom ≃ U.Atom
  /-- Exact family equality recovered at the selected realized source. -/
  family_eq : Q.family = (X.doctrine.atomize X.source).transport atomEquiv

/--
The selected source family in the source pointed doctrine is list-finite.

The proof transports the target package's finiteness witness through the inverse
Atom equivalence and uses only the selected family equality.
-/
noncomputable def inverseFamilyListFinite {U : AtomCarrier.{u}}
    {X : ExtractionInstance U} (Q : AATCorePackage U)
    (data : SelectedTransportData X Q) :
    (X.doctrine.atomize X.source).ListFinite := by
  let e := data.atomEquiv
  have hfamily : Q.family =
      (X.doctrine.atomize X.source).transport e := data.family_eq
  have hfinite := Q.reading.family_listFinite.transport e.symm
  change (Q.family.transport e.symm).ListFinite at hfinite
  rw [hfamily] at hfinite
  simpa [e] using hfinite

/-- The base object generated by inverse-reindexing the target lower readings. -/
noncomputable def inverseBaseObject {U : AtomCarrier.{u}}
    {X : ExtractionInstance U} (Q : AATCorePackage U)
    (data : SelectedTransportData X Q) : ArchitectureObject U :=
  let e := data.atomEquiv
  let hfinite := inverseFamilyListFinite Q data
  (transportObjectReading e.symm Q.reading.objectReading).object
    ((transportCompositionReading e.symm Q.reading.composition).compose
      (X.doctrine.atomize X.source) hfinite)

/--
The inverse-reindexed lower readings generate exactly the inverse direct image
of the target package's base object.
-/
theorem inverseBaseObject_eq {U : AtomCarrier.{u}}
    {X : ExtractionInstance U} (Q : AATCorePackage U)
    (data : SelectedTransportData X Q) :
    inverseBaseObject Q data =
      transportArchitectureObject data.atomEquiv.symm Q.object := by
  let e := data.atomEquiv
  let hfinite := inverseFamilyListFinite Q data
  have hfamily : Q.family =
      (X.doctrine.atomize X.source).transport e := data.family_eq
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
    (data : SelectedTransportData X Q) : CoreReading U :=
  let e := data.atomEquiv
  let hfinite := inverseFamilyListFinite Q data
  {
    doctrine := X.doctrine
    source := X.source
    family_listFinite := hfinite
    composition := transportCompositionReading e.symm Q.reading.composition
    objectReading := transportObjectReading e.symm Q.reading.objectReading
    equationReading :=
      castEquationReading (inverseBaseObject_eq Q data).symm
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
    (data : SelectedTransportData X Q) : AATCorePackage U where
  axioms := Q.axioms
  reading := inverseCoreReading Q data

/-- The inverse-reindexed package lies over the source pointed doctrine. -/
@[simp]
theorem inverseCorePackage_point {U : AtomCarrier.{u}}
    {X : ExtractionInstance U} (Q : AATCorePackage U)
    (data : SelectedTransportData X Q) :
    packagePoint (inverseCorePackage Q data) = X := by
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

private theorem castTargetEquationExact_contextForward_obj_carriers
    {U : AtomCarrier.{u}}
    {A₀ A A' : ArchitectureObject U}
    {C₀ : Site.ContextPreorderCategory A₀}
    {E₀ : ArchitecturalEquationSystem C₀}
    (S : EquationReading A) (h : A = A')
    (e : U.Atom ≃ U.Atom)
    (objectMap : ArchitectureObject U → ArchitectureObject U)
    (T : EquationSystemExactTransport E₀ S.equationSystem e objectMap)
    (hT : ∀ W : Site.ContextCategoryObject C₀,
      (T.contextForward W).ctx.Support = W.ctx.Support ∧
        (T.contextForward W).ctx.Axis = W.ctx.Axis ∧
        (T.contextForward W).ctx.Observable = W.ctx.Observable ∧
        (T.contextForward W).ctx.Extension = W.ctx.Extension)
    (W : Site.ContextCategoryObject C₀) :
    ((castTargetEquationExact S h e objectMap T).contextForward W).ctx.Support =
        W.ctx.Support ∧
      ((castTargetEquationExact S h e objectMap T).contextForward W).ctx.Axis =
        W.ctx.Axis ∧
      ((castTargetEquationExact S h e objectMap T).contextForward W).ctx.Observable =
        W.ctx.Observable ∧
      ((castTargetEquationExact S h e objectMap T).contextForward W).ctx.Extension =
        W.ctx.Extension := by
  cases h
  exact hT W

private theorem castTargetEquationExact_contextBackward_obj_carriers
    {U : AtomCarrier.{u}}
    {A₀ A A' : ArchitectureObject U}
    {C₀ : Site.ContextPreorderCategory A₀}
    {E₀ : ArchitecturalEquationSystem C₀}
    (S : EquationReading A) (h : A = A')
    (e : U.Atom ≃ U.Atom)
    (objectMap : ArchitectureObject U → ArchitectureObject U)
    (T : EquationSystemExactTransport E₀ S.equationSystem e objectMap)
    (hT : ∀ W : Site.ContextCategoryObject S.contextPreorder,
      (T.contextBackward W).ctx.Support = W.ctx.Support ∧
        (T.contextBackward W).ctx.Axis = W.ctx.Axis ∧
        (T.contextBackward W).ctx.Observable = W.ctx.Observable ∧
        (T.contextBackward W).ctx.Extension = W.ctx.Extension)
    (W : Site.ContextCategoryObject
      (castEquationReading h S).contextPreorder) :
    ((castTargetEquationExact S h e objectMap T).contextBackward W).ctx.Support =
        W.ctx.Support ∧
      ((castTargetEquationExact S h e objectMap T).contextBackward W).ctx.Axis =
        W.ctx.Axis ∧
      ((castTargetEquationExact S h e objectMap T).contextBackward W).ctx.Observable =
        W.ctx.Observable ∧
      ((castTargetEquationExact S h e objectMap T).contextBackward W).ctx.Extension =
        W.ctx.Extension := by
  cases h
  exact hT W

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
is generated from `Q` and `data`; no upper comparison is accepted as input.
-/
noncomputable def inverseCorePackageBackwardUpper {U : AtomCarrier.{u}}
    {X : ExtractionInstance U} (Q : AATCorePackage U)
    (data : SelectedTransportData X Q) :
    SignedExactCoreReadingHom Q (inverseCorePackage Q data) where
  atomEquiv := data.atomEquiv.symm
  extraction_eq := by
    let e := data.atomEquiv
    have hfamily : Q.family =
        (X.doctrine.atomize X.source).transport e := data.family_eq
    change X.doctrine.atomize X.source = Q.family.transport e.symm
    rw [hfamily]
    exact (atomFamily_transport_equiv_symm
      (X.doctrine.atomize X.source) e).symm
  composition_eq F hF :=
    transportCompositionReading_compose_transport
      data.atomEquiv.symm Q.reading.composition F hF
  objectMap := transportArchitectureObject data.atomEquiv.symm
  object_formation_eq C :=
    transportObjectReading_object_transport
      data.atomEquiv.symm Q.reading.objectReading C
  configurationMap A :=
    AtomConfiguration.transportHom data.atomEquiv.symm A.configuration
  configurationMap_atomMap _ := rfl
  configuration_eq _ := rfl
  equationTransport :=
    castTargetEquationExact
      (transportEquationReading data.atomEquiv.symm
        Q.object Q.reading.equationReading)
      (inverseBaseObject_eq Q data).symm
      data.atomEquiv.symm
      (transportArchitectureObject data.atomEquiv.symm)
      (transportEquationSystemExact data.atomEquiv.symm
        Q.object Q.reading.equationReading.contextPreorder
        Q.reading.equationReading.equationSystem)
  detectorCode_eq i := by
    apply castTargetEquationExact_detectorCode
      (transportEquationReading data.atomEquiv.symm
        Q.object Q.reading.equationReading)
      (inverseBaseObject_eq Q data).symm
      data.atomEquiv.symm
      (transportArchitectureObject data.atomEquiv.symm)
      (transportEquationSystemExact data.atomEquiv.symm
        Q.object Q.reading.equationReading.contextPreorder
        Q.reading.equationReading.equationSystem)
      Q.reading.equationReading.circuits.code
    intro j
    rfl
  operationMap op :=
    transportOperation data.atomEquiv.symm
      Q.reading.operationReading op
  operation_naturality op :=
    transportOperation_naturality data.atomEquiv.symm
      Q.reading.operationReading op
  invariantMap := _root_.id
  invariant_transport i :=
    invariant_transportAlong data.atomEquiv.symm
      (Q.reading.invariantReading.invariant i)
  axisMap := _root_.id
  coordinateEquiv _ := Equiv.refl _
  axis_selected_iff _ := Iff.rfl
  coordinate_eq A i :=
    (transportArchitectureSignature_coordinate
      data.atomEquiv.symm Q.reading.signatureReading A i).symm

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

private theorem castSourceEquationExact_contextForward_obj_carriers
    {U : AtomCarrier.{u}}
    {A A' B : ArchitectureObject U}
    {D : Site.ContextPreorderCategory B}
    {G : ArchitecturalEquationSystem D}
    (h : A = A') (S : EquationReading A)
    (e : U.Atom ≃ U.Atom)
    (objectMap : ArchitectureObject U → ArchitectureObject U)
    (T : EquationSystemExactTransport S.equationSystem G e objectMap)
    (hT : ∀ W : Site.ContextCategoryObject S.contextPreorder,
      (T.contextForward W).ctx.Support = W.ctx.Support ∧
        (T.contextForward W).ctx.Axis = W.ctx.Axis ∧
        (T.contextForward W).ctx.Observable = W.ctx.Observable ∧
        (T.contextForward W).ctx.Extension = W.ctx.Extension)
    (W : Site.ContextCategoryObject
      (castEquationReading h S).contextPreorder) :
    ((castSourceEquationExact h S e objectMap T).contextForward W).ctx.Support =
        W.ctx.Support ∧
      ((castSourceEquationExact h S e objectMap T).contextForward W).ctx.Axis =
        W.ctx.Axis ∧
      ((castSourceEquationExact h S e objectMap T).contextForward W).ctx.Observable =
        W.ctx.Observable ∧
      ((castSourceEquationExact h S e objectMap T).contextForward W).ctx.Extension =
        W.ctx.Extension := by
  cases h
  exact hT W

private theorem castSourceEquationExact_contextBackward_obj_carriers
    {U : AtomCarrier.{u}}
    {A A' B : ArchitectureObject U}
    {D : Site.ContextPreorderCategory B}
    {G : ArchitecturalEquationSystem D}
    (h : A = A') (S : EquationReading A)
    (e : U.Atom ≃ U.Atom)
    (objectMap : ArchitectureObject U → ArchitectureObject U)
    (T : EquationSystemExactTransport S.equationSystem G e objectMap)
    (hT : ∀ W : Site.ContextCategoryObject D,
      (T.contextBackward W).ctx.Support = W.ctx.Support ∧
        (T.contextBackward W).ctx.Axis = W.ctx.Axis ∧
        (T.contextBackward W).ctx.Observable = W.ctx.Observable ∧
        (T.contextBackward W).ctx.Extension = W.ctx.Extension)
    (W : Site.ContextCategoryObject D) :
    ((castSourceEquationExact h S e objectMap T).contextBackward W).ctx.Support =
        W.ctx.Support ∧
      ((castSourceEquationExact h S e objectMap T).contextBackward W).ctx.Axis =
        W.ctx.Axis ∧
      ((castSourceEquationExact h S e objectMap T).contextBackward W).ctx.Observable =
        W.ctx.Observable ∧
      ((castSourceEquationExact h S e objectMap T).contextBackward W).ctx.Extension =
        W.ctx.Extension := by
  cases h
  exact hT W

private theorem castSourceEquationExact_contextForward_obj_eq
    {U : AtomCarrier.{u}}
    {A A' B : ArchitectureObject U}
    {D : Site.ContextPreorderCategory B}
    {G : ArchitecturalEquationSystem D}
    (h : A = A') (S : EquationReading A)
    (e : U.Atom ≃ U.Atom)
    (objectMap : ArchitectureObject U → ArchitectureObject U)
    (T : EquationSystemExactTransport S.equationSystem G e objectMap)
    (forwardObject : Site.ContextCategoryObject S.contextPreorder →
      Site.ArchitectureContext B)
    (hT : ∀ W, (T.contextForward W).ctx = forwardObject W)
    (W : Site.ContextCategoryObject
      (castEquationReading h S).contextPreorder) :
    ((castSourceEquationExact h S e objectMap T).contextForward W).ctx =
      forwardObject
        ⟨cast (congrArg Site.ArchitectureContext h.symm) W.ctx⟩ := by
  cases h
  exact hT W

private theorem castSourceEquationExact_contextBackward_obj_eq
    {U : AtomCarrier.{u}}
    {A A' B : ArchitectureObject U}
    {D : Site.ContextPreorderCategory B}
    {G : ArchitecturalEquationSystem D}
    (h : A = A') (S : EquationReading A)
    (e : U.Atom ≃ U.Atom)
    (objectMap : ArchitectureObject U → ArchitectureObject U)
    (T : EquationSystemExactTransport S.equationSystem G e objectMap)
    (backwardObject : Site.ContextCategoryObject D →
      Site.ArchitectureContext A)
    (hT : ∀ W, (T.contextBackward W).ctx = backwardObject W)
    (W : Site.ContextCategoryObject D) :
    ((castSourceEquationExact h S e objectMap T).contextBackward W).ctx =
      cast (congrArg Site.ArchitectureContext h) (backwardObject W) := by
  cases h
  exact hT W

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
    (data : SelectedTransportData X Q) :
    EquationSystemExactTransport
      (inverseCorePackage Q data).algebra.equationSystem
      Q.algebra.equationSystem data.atomEquiv
      (transportArchitectureObject data.atomEquiv) :=
  castSourceEquationExact
    (inverseBaseObject_eq Q data).symm
    (transportEquationReading data.atomEquiv.symm
      Q.object Q.reading.equationReading)
    data.atomEquiv
    (transportArchitectureObject data.atomEquiv)
    (deconjugateEquationSystemExact data.atomEquiv.symm
      data.atomEquiv Q.object
      Q.reading.equationReading.contextPreorder
      Q.reading.equationReading.equationSystem _root_.id
      (inverseCompositeEquationRefl
        Q.reading.equationReading.equationSystem
        data.atomEquiv))

/-- The generated forward equation transport retains the equation index. -/
@[simp]
theorem inverseCoreEquationForward_equationMap_heq {U : AtomCarrier.{u}}
    {X : ExtractionInstance U} (Q : AATCorePackage U)
    (data : SelectedTransportData X Q)
    (i : (inverseCorePackage Q data).algebra.equationSystem.Index) :
    HEq ((inverseCoreEquationForward Q data).equationMap i) i := by
  apply castSourceEquationExact_equationMap_heq
  intro j
  rfl

/-- The generated forward equation map transports exactly the authored detector code. -/
theorem inverseCoreEquationForward_detectorCode {U : AtomCarrier.{u}}
    {X : ExtractionInstance U} (Q : AATCorePackage U)
    (data : SelectedTransportData X Q)
    (i : (inverseCorePackage Q data).algebra.equationSystem.Index) :
    Q.algebra.circuits.code
        ((inverseCoreEquationForward Q data).equationMap i) =
      ((inverseCorePackage Q data).algebra.circuits.code i).transport
        data.atomEquiv := by
  apply castSourceEquationExact_detectorCode
  intro j
  change Q.reading.equationReading.circuits.code j =
    ((Q.reading.equationReading.circuits.code j).transport
      data.atomEquiv.symm).transport data.atomEquiv
  simp

/--
The forward upper map from the inverse-reindexed package to the requested
target.  It is generated entirely by inverse Atom conjugation and its canonical
round trips.
-/
noncomputable def inverseCorePackageForwardUpper {U : AtomCarrier.{u}}
    {X : ExtractionInstance U} (Q : AATCorePackage U)
    (data : SelectedTransportData X Q) :
    SignedExactCoreReadingHom (inverseCorePackage Q data) Q where
  atomEquiv := data.atomEquiv
  extraction_eq := by
    change Q.family =
      (X.doctrine.atomize X.source).transport data.atomEquiv
    exact data.family_eq
  composition_eq F hF := by
    have h := transportCompositionReading_compose_transport
      data.atomEquiv
      (transportCompositionReading data.atomEquiv.symm
        Q.reading.composition) F hF
    rw [transportCompositionReading_symm_roundtrip
      data.atomEquiv Q.reading.composition] at h
    exact h
  objectMap := transportArchitectureObject data.atomEquiv
  object_formation_eq C := by
    have h := transportObjectReading_object_transport
      data.atomEquiv
      (transportObjectReading data.atomEquiv.symm
        Q.reading.objectReading) C
    rw [transportObjectReading_symm_roundtrip
      data.atomEquiv Q.reading.objectReading] at h
    exact h
  configurationMap A :=
    AtomConfiguration.transportHom data.atomEquiv A.configuration
  configurationMap_atomMap _ := rfl
  configuration_eq _ := rfl
  equationTransport := inverseCoreEquationForward Q data
  detectorCode_eq i := inverseCoreEquationForward_detectorCode Q data i
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
      data.atomEquiv.symm
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

/--
The generated forward upper functor acts on complete contexts by the canonical
backward Atom transport, after aligning the generated source object.
-/
theorem inverseCorePackageForwardUpper_contextFunctor_obj_eq
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    (Q : AATCorePackage U) (data : SelectedTransportData X Q)
    (W : Site.ContextCategoryObject
      (inverseCorePackage Q data).algebra.contextPreorder) :
    ((inverseCorePackageForwardUpper Q data).equationTransport.contextForward
      W).ctx =
      transportArchitectureContextBackward data.atomEquiv.symm
        Q.object
        (cast (congrArg Site.ArchitectureContext (inverseBaseObject_eq Q data))
          W.ctx) := by
  change
    ((castSourceEquationExact (inverseBaseObject_eq Q data).symm
      (transportEquationReading data.atomEquiv.symm
        Q.object Q.reading.equationReading)
      data.atomEquiv
      (transportArchitectureObject data.atomEquiv)
      (deconjugateEquationSystemExact data.atomEquiv.symm
        data.atomEquiv Q.object
        Q.reading.equationReading.contextPreorder
        Q.reading.equationReading.equationSystem _root_.id
        (inverseCompositeEquationRefl
          Q.reading.equationReading.equationSystem
          data.atomEquiv))).contextForward W).ctx = _
  exact castSourceEquationExact_contextForward_obj_eq
    (h := (inverseBaseObject_eq Q data).symm)
    (S := transportEquationReading data.atomEquiv.symm
      Q.object Q.reading.equationReading)
    (e := data.atomEquiv)
    (objectMap := transportArchitectureObject data.atomEquiv)
    (T := deconjugateEquationSystemExact data.atomEquiv.symm
      data.atomEquiv Q.object
      Q.reading.equationReading.contextPreorder
      Q.reading.equationReading.equationSystem _root_.id
      (inverseCompositeEquationRefl
        Q.reading.equationReading.equationSystem
        data.atomEquiv))
    (forwardObject := fun V =>
      transportArchitectureContextBackward data.atomEquiv.symm
        Q.object V.ctx)
    (by intro V; rfl) W

/--
The inverse context functor of the generated forward upper is canonical forward
Atom transport, reindexed to the generated source object.
-/
theorem inverseCorePackageForwardUpper_contextInverse_obj_eq
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    (Q : AATCorePackage U) (data : SelectedTransportData X Q)
    (W : Site.ContextCategoryObject Q.algebra.contextPreorder) :
    ((inverseCorePackageForwardUpper Q data).equationTransport.contextBackward
      W).ctx =
      cast (congrArg Site.ArchitectureContext (inverseBaseObject_eq Q data).symm)
        (transportArchitectureContext data.atomEquiv.symm Q.object
          W.ctx) := by
  change
    ((castSourceEquationExact (inverseBaseObject_eq Q data).symm
      (transportEquationReading data.atomEquiv.symm
        Q.object Q.reading.equationReading)
      data.atomEquiv
      (transportArchitectureObject data.atomEquiv)
      (deconjugateEquationSystemExact data.atomEquiv.symm
        data.atomEquiv Q.object
        Q.reading.equationReading.contextPreorder
        Q.reading.equationReading.equationSystem _root_.id
        (inverseCompositeEquationRefl
          Q.reading.equationReading.equationSystem
          data.atomEquiv))).contextBackward W).ctx = _
  exact castSourceEquationExact_contextBackward_obj_eq
    (h := (inverseBaseObject_eq Q data).symm)
    (S := transportEquationReading data.atomEquiv.symm
      Q.object Q.reading.equationReading)
    (e := data.atomEquiv)
    (objectMap := transportArchitectureObject data.atomEquiv)
    (T := deconjugateEquationSystemExact data.atomEquiv.symm
      data.atomEquiv Q.object
      Q.reading.equationReading.contextPreorder
      Q.reading.equationReading.equationSystem _root_.id
      (inverseCompositeEquationRefl
        Q.reading.equationReading.equationSystem
        data.atomEquiv))
    (backwardObject := fun V =>
      transportArchitectureContext data.atomEquiv.symm
        Q.object V.ctx)
    (by intro V; rfl) W

private theorem inverseCorePackageForwardUpper_contextFunctor_obj_carriers
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    (Q : AATCorePackage U) (data : SelectedTransportData X Q)
    (W : Site.ContextCategoryObject
      (inverseCorePackage Q data).algebra.contextPreorder) :
    ((inverseCorePackageForwardUpper Q data).equationTransport.contextForward
      W).ctx.Support = W.ctx.Support ∧
      ((inverseCorePackageForwardUpper Q data).equationTransport.contextForward
        W).ctx.Axis = W.ctx.Axis ∧
      ((inverseCorePackageForwardUpper Q data).equationTransport.contextForward
        W).ctx.Observable = W.ctx.Observable ∧
      ((inverseCorePackageForwardUpper Q data).equationTransport.contextForward
        W).ctx.Extension = W.ctx.Extension := by
  unfold inverseCorePackageForwardUpper inverseCoreEquationForward
  apply castSourceEquationExact_contextForward_obj_carriers
  intro V
  exact ⟨rfl, rfl, rfl, rfl⟩

private theorem inverseCorePackageForwardUpper_contextInverse_obj_carriers
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    (Q : AATCorePackage U) (data : SelectedTransportData X Q)
    (W : Site.ContextCategoryObject Q.algebra.contextPreorder) :
    ((inverseCorePackageForwardUpper Q data).equationTransport.contextBackward
      W).ctx.Support = W.ctx.Support ∧
      ((inverseCorePackageForwardUpper Q data).equationTransport.contextBackward
        W).ctx.Axis = W.ctx.Axis ∧
      ((inverseCorePackageForwardUpper Q data).equationTransport.contextBackward
        W).ctx.Observable = W.ctx.Observable ∧
      ((inverseCorePackageForwardUpper Q data).equationTransport.contextBackward
        W).ctx.Extension = W.ctx.Extension := by
  unfold inverseCorePackageForwardUpper inverseCoreEquationForward
  apply castSourceEquationExact_contextBackward_obj_carriers
  intro V
  exact ⟨rfl, rfl, rfl, rfl⟩

private theorem inverseCorePackageBackwardUpper_contextFunctor_obj_carriers
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    (Q : AATCorePackage U) (data : SelectedTransportData X Q)
    (W : Site.ContextCategoryObject Q.algebra.contextPreorder) :
    ((inverseCorePackageBackwardUpper Q data).equationTransport.contextForward
      W).ctx.Support = W.ctx.Support ∧
      ((inverseCorePackageBackwardUpper Q data).equationTransport.contextForward
        W).ctx.Axis = W.ctx.Axis ∧
      ((inverseCorePackageBackwardUpper Q data).equationTransport.contextForward
        W).ctx.Observable = W.ctx.Observable ∧
      ((inverseCorePackageBackwardUpper Q data).equationTransport.contextForward
        W).ctx.Extension = W.ctx.Extension := by
  unfold inverseCorePackageBackwardUpper
  apply castTargetEquationExact_contextForward_obj_carriers
  intro V
  exact ⟨rfl, rfl, rfl, rfl⟩

private theorem inverseCorePackageBackwardUpper_contextInverse_obj_carriers
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    (Q : AATCorePackage U) (data : SelectedTransportData X Q)
    (W : Site.ContextCategoryObject
      (inverseCorePackage Q data).algebra.contextPreorder) :
    ((inverseCorePackageBackwardUpper Q data).equationTransport.contextBackward
      W).ctx.Support = W.ctx.Support ∧
      ((inverseCorePackageBackwardUpper Q data).equationTransport.contextBackward
        W).ctx.Axis = W.ctx.Axis ∧
      ((inverseCorePackageBackwardUpper Q data).equationTransport.contextBackward
        W).ctx.Observable = W.ctx.Observable ∧
      ((inverseCorePackageBackwardUpper Q data).equationTransport.contextBackward
        W).ctx.Extension = W.ctx.Extension := by
  unfold inverseCorePackageBackwardUpper
  apply castTargetEquationExact_contextBackward_obj_carriers
  intro V
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- The forward upper context functor preserves the support carrier. -/
theorem inverseCorePackageForwardUpper_contextFunctor_obj_support_type
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    (Q : AATCorePackage U) (data : SelectedTransportData X Q)
    (W : Site.ContextCategoryObject
      (inverseCorePackage Q data).algebra.contextPreorder) :
    ((inverseCorePackageForwardUpper Q data).equationTransport.contextForward
      W).ctx.Support = W.ctx.Support :=
  (inverseCorePackageForwardUpper_contextFunctor_obj_carriers Q data W).1

/-- The forward upper context functor preserves the axis carrier. -/
theorem inverseCorePackageForwardUpper_contextFunctor_obj_axis_type
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    (Q : AATCorePackage U) (data : SelectedTransportData X Q)
    (W : Site.ContextCategoryObject
      (inverseCorePackage Q data).algebra.contextPreorder) :
    ((inverseCorePackageForwardUpper Q data).equationTransport.contextForward
      W).ctx.Axis = W.ctx.Axis :=
  (inverseCorePackageForwardUpper_contextFunctor_obj_carriers Q data W).2.1

/-- The forward upper context functor preserves the observable carrier. -/
theorem inverseCorePackageForwardUpper_contextFunctor_obj_observable_type
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    (Q : AATCorePackage U) (data : SelectedTransportData X Q)
    (W : Site.ContextCategoryObject
      (inverseCorePackage Q data).algebra.contextPreorder) :
    ((inverseCorePackageForwardUpper Q data).equationTransport.contextForward
      W).ctx.Observable = W.ctx.Observable :=
  (inverseCorePackageForwardUpper_contextFunctor_obj_carriers Q data W).2.2.1

/-- The forward upper context functor preserves the extension carrier. -/
theorem inverseCorePackageForwardUpper_contextFunctor_obj_extension_type
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    (Q : AATCorePackage U) (data : SelectedTransportData X Q)
    (W : Site.ContextCategoryObject
      (inverseCorePackage Q data).algebra.contextPreorder) :
    ((inverseCorePackageForwardUpper Q data).equationTransport.contextForward
      W).ctx.Extension = W.ctx.Extension :=
  (inverseCorePackageForwardUpper_contextFunctor_obj_carriers Q data W).2.2.2

/-- The forward upper context inverse preserves the support carrier. -/
theorem inverseCorePackageForwardUpper_contextInverse_obj_support_type
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    (Q : AATCorePackage U) (data : SelectedTransportData X Q)
    (W : Site.ContextCategoryObject Q.algebra.contextPreorder) :
    ((inverseCorePackageForwardUpper Q data).equationTransport.contextBackward
      W).ctx.Support = W.ctx.Support :=
  (inverseCorePackageForwardUpper_contextInverse_obj_carriers Q data W).1

/-- The forward upper context inverse preserves the axis carrier. -/
theorem inverseCorePackageForwardUpper_contextInverse_obj_axis_type
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    (Q : AATCorePackage U) (data : SelectedTransportData X Q)
    (W : Site.ContextCategoryObject Q.algebra.contextPreorder) :
    ((inverseCorePackageForwardUpper Q data).equationTransport.contextBackward
      W).ctx.Axis = W.ctx.Axis :=
  (inverseCorePackageForwardUpper_contextInverse_obj_carriers Q data W).2.1

/-- The forward upper context inverse preserves the observable carrier. -/
theorem inverseCorePackageForwardUpper_contextInverse_obj_observable_type
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    (Q : AATCorePackage U) (data : SelectedTransportData X Q)
    (W : Site.ContextCategoryObject Q.algebra.contextPreorder) :
    ((inverseCorePackageForwardUpper Q data).equationTransport.contextBackward
      W).ctx.Observable = W.ctx.Observable :=
  (inverseCorePackageForwardUpper_contextInverse_obj_carriers Q data W).2.2.1

/-- The forward upper context inverse preserves the extension carrier. -/
theorem inverseCorePackageForwardUpper_contextInverse_obj_extension_type
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    (Q : AATCorePackage U) (data : SelectedTransportData X Q)
    (W : Site.ContextCategoryObject Q.algebra.contextPreorder) :
    ((inverseCorePackageForwardUpper Q data).equationTransport.contextBackward
      W).ctx.Extension = W.ctx.Extension :=
  (inverseCorePackageForwardUpper_contextInverse_obj_carriers Q data W).2.2.2

/-- The backward upper context functor preserves the support carrier. -/
theorem inverseCorePackageBackwardUpper_contextFunctor_obj_support_type
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    (Q : AATCorePackage U) (data : SelectedTransportData X Q)
    (W : Site.ContextCategoryObject Q.algebra.contextPreorder) :
    ((inverseCorePackageBackwardUpper Q data).equationTransport.contextForward
      W).ctx.Support = W.ctx.Support :=
  (inverseCorePackageBackwardUpper_contextFunctor_obj_carriers Q data W).1

/-- The backward upper context functor preserves the axis carrier. -/
theorem inverseCorePackageBackwardUpper_contextFunctor_obj_axis_type
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    (Q : AATCorePackage U) (data : SelectedTransportData X Q)
    (W : Site.ContextCategoryObject Q.algebra.contextPreorder) :
    ((inverseCorePackageBackwardUpper Q data).equationTransport.contextForward
      W).ctx.Axis = W.ctx.Axis :=
  (inverseCorePackageBackwardUpper_contextFunctor_obj_carriers Q data W).2.1

/-- The backward upper context functor preserves the observable carrier. -/
theorem inverseCorePackageBackwardUpper_contextFunctor_obj_observable_type
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    (Q : AATCorePackage U) (data : SelectedTransportData X Q)
    (W : Site.ContextCategoryObject Q.algebra.contextPreorder) :
    ((inverseCorePackageBackwardUpper Q data).equationTransport.contextForward
      W).ctx.Observable = W.ctx.Observable :=
  (inverseCorePackageBackwardUpper_contextFunctor_obj_carriers Q data W).2.2.1

/-- The backward upper context functor preserves the extension carrier. -/
theorem inverseCorePackageBackwardUpper_contextFunctor_obj_extension_type
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    (Q : AATCorePackage U) (data : SelectedTransportData X Q)
    (W : Site.ContextCategoryObject Q.algebra.contextPreorder) :
    ((inverseCorePackageBackwardUpper Q data).equationTransport.contextForward
      W).ctx.Extension = W.ctx.Extension :=
  (inverseCorePackageBackwardUpper_contextFunctor_obj_carriers Q data W).2.2.2

/-- The backward upper context inverse preserves the support carrier. -/
theorem inverseCorePackageBackwardUpper_contextInverse_obj_support_type
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    (Q : AATCorePackage U) (data : SelectedTransportData X Q)
    (W : Site.ContextCategoryObject
      (inverseCorePackage Q data).algebra.contextPreorder) :
    ((inverseCorePackageBackwardUpper Q data).equationTransport.contextBackward
      W).ctx.Support = W.ctx.Support :=
  (inverseCorePackageBackwardUpper_contextInverse_obj_carriers Q data W).1

/-- The backward upper context inverse preserves the axis carrier. -/
theorem inverseCorePackageBackwardUpper_contextInverse_obj_axis_type
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    (Q : AATCorePackage U) (data : SelectedTransportData X Q)
    (W : Site.ContextCategoryObject
      (inverseCorePackage Q data).algebra.contextPreorder) :
    ((inverseCorePackageBackwardUpper Q data).equationTransport.contextBackward
      W).ctx.Axis = W.ctx.Axis :=
  (inverseCorePackageBackwardUpper_contextInverse_obj_carriers Q data W).2.1

/-- The backward upper context inverse preserves the observable carrier. -/
theorem inverseCorePackageBackwardUpper_contextInverse_obj_observable_type
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    (Q : AATCorePackage U) (data : SelectedTransportData X Q)
    (W : Site.ContextCategoryObject
      (inverseCorePackage Q data).algebra.contextPreorder) :
    ((inverseCorePackageBackwardUpper Q data).equationTransport.contextBackward
      W).ctx.Observable = W.ctx.Observable :=
  (inverseCorePackageBackwardUpper_contextInverse_obj_carriers Q data W).2.2.1

/-- The backward upper context inverse preserves the extension carrier. -/
theorem inverseCorePackageBackwardUpper_contextInverse_obj_extension_type
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    (Q : AATCorePackage U) (data : SelectedTransportData X Q)
    (W : Site.ContextCategoryObject
      (inverseCorePackage Q data).algebra.contextPreorder) :
    ((inverseCorePackageBackwardUpper Q data).equationTransport.contextBackward
      W).ctx.Extension = W.ctx.Extension :=
  (inverseCorePackageBackwardUpper_contextInverse_obj_carriers Q data W).2.2.2

/-- Equation transports cancel in the target-to-source-to-target direction. -/
private theorem inverseCorePackageBackward_comp_forward_equation
    {U : AtomCarrier.{u}}
    {X : ExtractionInstance U} (Q : AATCorePackage U)
    (data : SelectedTransportData X Q) :
    HEq
      ((inverseCorePackageBackwardUpper Q data).equationTransport.comp
        (inverseCorePackageForwardUpper Q data).equationTransport)
      (EquationSystemExactTransport.refl Q.algebra.equationSystem) := by
  let e := data.atomEquiv
  let S := transportEquationReading e.symm
    Q.object Q.reading.equationReading
  let hbase := (inverseBaseObject_eq Q data).symm
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
    (data : SelectedTransportData X Q) :
    HEq
      ((inverseCorePackageForwardUpper Q data).equationTransport.comp
        (inverseCorePackageBackwardUpper Q data).equationTransport)
      (EquationSystemExactTransport.refl
        (inverseCorePackage Q data).algebra.equationSystem) := by
  let e := data.atomEquiv
  let S := transportEquationReading e.symm
    Q.object Q.reading.equationReading
  let hbase := (inverseBaseObject_eq Q data).symm
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
    (data : SelectedTransportData X Q) :
    (inverseCorePackageBackwardUpper Q data).comp
        (inverseCorePackageForwardUpper Q data) =
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
      data.atomEquiv A
  · exact inverseCorePackageBackward_comp_forward_equation Q data
  · apply Function.hfunext rfl
    intro A A' hA
    cases hA
    apply Function.hfunext rfl
    intro B B' hB
    cases hB
    apply Function.hfunext rfl
    intro op op' hop
    cases hop
    exact transportOperation_symm_heq data.atomEquiv
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
    (data : SelectedTransportData X Q) :
    (inverseCorePackageForwardUpper Q data).comp
        (inverseCorePackageBackwardUpper Q data) =
      SignedExactCoreReadingHom.refl (inverseCorePackage Q data) := by
  apply SignedExactCoreReadingHom.ext
  · apply Equiv.ext
    intro atom
    simp [SignedExactCoreReadingHom.comp,
      inverseCorePackageForwardUpper,
      inverseCorePackageBackwardUpper,
      SignedExactCoreReadingHom.refl]
  · funext A
    exact transportArchitectureObject_equiv_symm
      data.atomEquiv A
  · exact inverseCorePackageForward_comp_backward_equation Q data
  · apply Function.hfunext rfl
    intro A A' hA
    cases hA
    apply Function.hfunext rfl
    intro B B' hB
    cases hB
    apply Function.hfunext rfl
    intro op op' hop
    cases hop
    exact transportOperation_symm_heq data.atomEquiv
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

end AAT.AG.DoctrineFiberProduct.SelectedRefinementTransport

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct.SelectedRefinementTransport
