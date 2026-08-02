import ResearchLean.AG.AtomFoundation.Categories
import ResearchLean.AG.AtomFoundation.TransportLaws

/-!
# Canonical transport of complete AAT core packages

This module constructs the target package and its complete signed exact hom
from one source package and one exact extraction-doctrine morphism.  Every
upper component is obtained by conjugating the source reading with the supplied
Atom equivalence; no target package or completed transport certificate is an
input.
-/

namespace AAT.AG.AtomFoundation

universe u

open CategoryTheory

/-- Transport an architecture object by direct image of its configuration. -/
def transportArchitectureObject {U : AtomCarrier.{u}}
    (e : U.Atom ≃ U.Atom) (A : ArchitectureObject U) :
    ArchitectureObject U :=
  { A with configuration := A.configuration.transport e }

/-- Object transport changes exactly the underlying configuration. -/
@[simp]
theorem transportArchitectureObject_configuration {U : AtomCarrier.{u}}
    (e : U.Atom ≃ U.Atom) (A : ArchitectureObject U) :
    (transportArchitectureObject e A).configuration =
      A.configuration.transport e :=
  rfl

/-- Forward object transport followed by inverse transport is the identity. -/
@[simp]
theorem transportArchitectureObject_equiv_symm {U : AtomCarrier.{u}}
    (e : U.Atom ≃ U.Atom) (A : ArchitectureObject U) :
    transportArchitectureObject e.symm (transportArchitectureObject e A) = A := by
  cases A
  simp [transportArchitectureObject, atomConfiguration_transport_equiv_symm]

/-- Inverse object transport followed by forward transport is the identity. -/
@[simp]
theorem transportArchitectureObject_symm_equiv {U : AtomCarrier.{u}}
    (e : U.Atom ≃ U.Atom) (A : ArchitectureObject U) :
    transportArchitectureObject e (transportArchitectureObject e.symm A) = A := by
  cases A
  simp [transportArchitectureObject, atomConfiguration_transport_symm_equiv]

/-- Atom transport is an equivalence on architecture objects. -/
def transportArchitectureObjectEquiv {U : AtomCarrier.{u}}
    (e : U.Atom ≃ U.Atom) :
    ArchitectureObject U ≃ ArchitectureObject U where
  toFun := transportArchitectureObject e
  invFun := transportArchitectureObject e.symm
  left_inv := transportArchitectureObject_equiv_symm e
  right_inv := transportArchitectureObject_symm_equiv e

/-- Conjugate a configuration hom by an Atom equivalence. -/
def transportConfigurationHom {U : AtomCarrier.{u}}
    (e : U.Atom ≃ U.Atom) {C D : AtomConfiguration U}
    (h : ConfigurationHom C D) :
    ConfigurationHom (C.transport e) (D.transport e) where
  atomMap atom := e (h.atomMap (e.symm atom))
  maps_family := by
    rintro target ⟨source, hsource, rfl⟩
    exact ⟨h.atomMap source, h.maps_family hsource, by simp⟩
  maps_relation := by
    rintro target₁ target₂ ⟨source₁, source₂, hsource, rfl, rfl⟩
    exact ⟨h.atomMap source₁, h.atomMap source₂,
      h.maps_relation hsource, by simp, by simp⟩
  maps_identification := by
    rintro target₁ target₂ ⟨source₁, source₂, hsource, rfl, rfl⟩
    exact ⟨h.atomMap source₁, h.atomMap source₂,
      h.maps_identification hsource, by simp, by simp⟩

/-- The transported configuration hom conjugates the original Atom map. -/
@[simp]
theorem transportConfigurationHom_atomMap {U : AtomCarrier.{u}}
    (e : U.Atom ≃ U.Atom) {C D : AtomConfiguration U}
    (h : ConfigurationHom C D) :
    (transportConfigurationHom e h).atomMap =
      e ∘ h.atomMap ∘ e.symm :=
  rfl

/-- Reindex the endpoints of a configuration hom along equalities. -/
def castConfigurationHom {U : AtomCarrier.{u}}
    {C C' D D' : AtomConfiguration U}
    (hC : C = C') (hD : D = D') (h : ConfigurationHom C D) :
    ConfigurationHom C' D' := by
  cases hC
  cases hD
  exact h

/-- Casting endpoint configurations leaves the Atom map unchanged. -/
@[simp]
theorem castConfigurationHom_atomMap {U : AtomCarrier.{u}}
    {C C' D D' : AtomConfiguration U}
    (hC : C = C') (hD : D = D') (h : ConfigurationHom C D) :
    (castConfigurationHom hC hD h).atomMap = h.atomMap := by
  cases hC
  cases hD
  rfl

/-- Transport a composition rule by inverse/forward Atom conjugation. -/
def transportCompositionReading {U : AtomCarrier.{u}}
    (e : U.Atom ≃ U.Atom) (R : CompositionReading U) :
    CompositionReading U where
  compose F hF :=
    (R.compose (F.transport e.symm) (hF.transport e.symm)).transport e
  family_eq F hF := by
    change
      (R.compose (F.transport e.symm) (hF.transport e.symm)).family.transport e = F
    rw [R.family_eq, atomFamily_transport_symm_equiv]
  family_supported F hF :=
    familySupported_transport _ e
      (R.family_supported (F.transport e.symm) (hF.transport e.symm))

/-- The transported composition rule commutes with direct image from the source. -/
theorem transportCompositionReading_compose_transport {U : AtomCarrier.{u}}
    (e : U.Atom ≃ U.Atom) (R : CompositionReading U)
    (F : AtomFamily U) (hF : F.ListFinite) :
    (transportCompositionReading e R).compose
        (F.transport e) (hF.transport e) =
      (R.compose F hF).transport e := by
  let sourceInput : {G : AtomFamily U // G.ListFinite} :=
    ⟨(F.transport e).transport e.symm,
      (hF.transport e).transport e.symm⟩
  let targetInput : {G : AtomFamily U // G.ListFinite} := ⟨F, hF⟩
  have hinput : sourceInput = targetInput := by
    apply Subtype.ext
    exact atomFamily_transport_equiv_symm F e
  exact congrArg
    (fun input : {G : AtomFamily U // G.ListFinite} =>
      (R.compose input.1 input.2).transport e) hinput

/-- Transport an object-formation rule by inverse/forward Atom conjugation. -/
def transportObjectReading {U : AtomCarrier.{u}}
    (e : U.Atom ≃ U.Atom) (R : ObjectReading U) :
    ObjectReading U where
  object C :=
    transportArchitectureObject e (R.object (C.transport e.symm))
  configuration_eq C := by
    change (R.object (C.transport e.symm)).configuration.transport e = C
    rw [R.configuration_eq, atomConfiguration_transport_symm_equiv]

/-- Transported object formation commutes with direct image from the source. -/
theorem transportObjectReading_object_transport {U : AtomCarrier.{u}}
    (e : U.Atom ≃ U.Atom) (R : ObjectReading U)
    (C : AtomConfiguration U) :
    transportArchitectureObject e (R.object C) =
      (transportObjectReading e R).object (C.transport e) := by
  change transportArchitectureObject e (R.object C) =
    transportArchitectureObject e
      (R.object ((C.transport e).transport e.symm))
  rw [atomConfiguration_transport_equiv_symm]

/-- Transport one invariant by precomposition with inverse object transport. -/
def transportInvariant {U : AtomCarrier.{u}}
    (e : U.Atom ≃ U.Atom) : Invariant U → Invariant U
  | .function I => .function {
      Value := I.Value
      evaluate := fun A => I.evaluate (transportArchitectureObject e.symm A)
    }
  | .predicate I => .predicate {
      holds := fun A => I.holds (transportArchitectureObject e.symm A)
    }

/-- Transport an indexed invariant family without adding invariant data. -/
def transportInvariantFamily {U : AtomCarrier.{u}}
    (e : U.Atom ≃ U.Atom) (R : InvariantFamily U) :
    InvariantFamily U where
  Index := R.Index
  invariant i := transportInvariant e (R.invariant i)

/-- Each source invariant is transported by the canonical object map. -/
theorem invariant_transportAlong {U : AtomCarrier.{u}}
    (e : U.Atom ≃ U.Atom) (I : Invariant U) :
    Invariant.TransportedAlong I (transportInvariant e I)
      _root_.id (transportArchitectureObject e) := by
  cases I with
  | function I =>
      refine ⟨Equiv.refl I.Value, ?_⟩
      intro A
      simp
  | predicate I =>
      intro A
      simp

/-- Transport a signature by reading coordinates after inverse object transport. -/
def transportArchitectureSignature {U : AtomCarrier.{u}}
    (e : U.Atom ≃ U.Atom) (S : ArchitectureSignature U) :
    ArchitectureSignature U where
  Axis := S.Axis
  Coordinate := S.Coordinate
  selected := S.selected
  coordinate A i :=
    S.coordinate (transportArchitectureObject e.symm A) i

/-- Coordinate transport for the canonical object map is definitionally conjugate. -/
theorem transportArchitectureSignature_coordinate {U : AtomCarrier.{u}}
    (e : U.Atom ≃ U.Atom) (S : ArchitectureSignature U)
    (A : ArchitectureObject U) (i : S.Axis) :
    (transportArchitectureSignature e S).coordinate
        (transportArchitectureObject e A) i =
      S.coordinate A i := by
  simp [transportArchitectureSignature]

/-- Cast an operation whose two object indices are propositionally equal. -/
def castOperation {U : AtomCarrier.{u}} (R : OperationReading U)
    {A A' B B' : ArchitectureObject U}
    (hA : A = A') (hB : B = B') (op : R.Op A B) :
    R.Op A' B' := by
  cases hA
  cases hB
  exact op

/-- Casting operation endpoints leaves its configuration Atom map unchanged. -/
@[simp]
theorem castOperation_configurationMap_atomMap {U : AtomCarrier.{u}}
    (R : OperationReading U) {A A' B B' : ArchitectureObject U}
    (hA : A = A') (hB : B = B') (op : R.Op A B) :
    (R.configurationMap (castOperation R hA hB op)).atomMap =
      (R.configurationMap op).atomMap := by
  cases hA
  cases hB
  rfl

/-- Transport an operation reading by conjugating objects and configuration maps. -/
def transportOperationReading {U : AtomCarrier.{u}}
    (e : U.Atom ≃ U.Atom) (R : OperationReading U) :
    OperationReading U where
  Op A B :=
    R.Op (transportArchitectureObject e.symm A)
      (transportArchitectureObject e.symm B)
  configurationMap {A B} op :=
    castConfigurationHom
      (atomConfiguration_transport_symm_equiv A.configuration e)
      (atomConfiguration_transport_symm_equiv B.configuration e)
      (transportConfigurationHom e (R.configurationMap op))

/-- Canonical map from a source operation to its transported operation. -/
def transportOperation {U : AtomCarrier.{u}}
    (e : U.Atom ≃ U.Atom) (R : OperationReading U)
    {A B : ArchitectureObject U} (op : R.Op A B) :
    (transportOperationReading e R).Op
      (transportArchitectureObject e A) (transportArchitectureObject e B) :=
  castOperation R
    (transportArchitectureObject_equiv_symm e A).symm
    (transportArchitectureObject_equiv_symm e B).symm op

/-- The transported operation map is conjugation of the source Atom map. -/
theorem transportOperation_configurationMap_atomMap {U : AtomCarrier.{u}}
    (e : U.Atom ≃ U.Atom) (R : OperationReading U)
    {A B : ArchitectureObject U} (op : R.Op A B) :
    ((transportOperationReading e R).configurationMap
      (transportOperation e R op)).atomMap =
        e ∘ (R.configurationMap op).atomMap ∘ e.symm := by
  simp [transportOperationReading, transportOperation,
    transportConfigurationHom_atomMap]

/-- Canonical operation transport is natural with direct-image configuration maps. -/
theorem transportOperation_naturality {U : AtomCarrier.{u}}
    (e : U.Atom ≃ U.Atom) (R : OperationReading U)
    {A B : ArchitectureObject U} (op : R.Op A B) :
    ConfigurationHom.comp
        ((transportOperationReading e R).configurationMap
          (transportOperation e R op))
        (AtomConfiguration.transportHom e A.configuration) =
      ConfigurationHom.comp
        (AtomConfiguration.transportHom e B.configuration)
        (R.configurationMap op) := by
  apply ConfigurationHom.ext
  simp only [ConfigurationHom.comp,
    AtomConfiguration.transportHom_atomMap,
    transportOperation_configurationMap_atomMap]
  funext atom
  simp [Function.comp_def]

/-- Transport an architecture context to the direct-image object. -/
def transportArchitectureContext {U : AtomCarrier.{u}}
    (e : U.Atom ≃ U.Atom) (A : ArchitectureObject U)
    (W : Site.ArchitectureContext A) :
    Site.ArchitectureContext (transportArchitectureObject e A) where
  minimal := {
    Support := W.Support
    Axis := W.Axis
    Observable := W.Observable
    supportReads := fun support atom =>
      W.minimal.supportReads support (e.symm atom)
    supportReads_objectFamily := by
      intro support atom hread
      exact ⟨e.symm atom, W.supportReads_objectFamily hread,
        e.apply_symm_apply atom⟩
    axisReads := W.minimal.axisReads
    observableReads := W.minimal.observableReads
  }
  Extension := W.Extension
  extension := W.extension

/-- Canonical inverse transport of a context on a direct-image object. -/
def transportArchitectureContextBackward {U : AtomCarrier.{u}}
    (e : U.Atom ≃ U.Atom) (A : ArchitectureObject U)
    (W : Site.ArchitectureContext (transportArchitectureObject e A)) :
    Site.ArchitectureContext A where
  minimal := {
    Support := W.Support
    Axis := W.Axis
    Observable := W.Observable
    supportReads := fun support atom =>
      W.minimal.supportReads support (e atom)
    supportReads_objectFamily := by
      intro support atom hread
      have htarget := W.supportReads_objectFamily hread
      change (A.configuration.transport e).family.mem (e atom) at htarget
      rcases htarget with ⟨source, hsource, heq⟩
      have hsource_eq : source = atom := e.injective heq
      simpa [hsource_eq] using hsource
    axisReads := W.minimal.axisReads
    observableReads := W.minimal.observableReads
  }
  Extension := W.Extension
  extension := W.extension

/-- Backward context transport cancels forward context transport. -/
@[simp]
theorem transportArchitectureContext_backward_forward {U : AtomCarrier.{u}}
    (e : U.Atom ≃ U.Atom) (A : ArchitectureObject U)
    (W : Site.ArchitectureContext A) :
    transportArchitectureContextBackward e A
      (transportArchitectureContext e A W) = W := by
  rcases W with ⟨⟨Support, Axis, Observable, supportReads,
    supportReads_objectFamily, axisReads, observableReads⟩,
    Extension, extension⟩
  simp [transportArchitectureContext,
    transportArchitectureContextBackward,
    Site.ArchitectureContext.Support, Site.ArchitectureContext.Axis,
    Site.ArchitectureContext.Observable]

/-- Forward context transport cancels backward context transport. -/
@[simp]
theorem transportArchitectureContext_forward_backward {U : AtomCarrier.{u}}
    (e : U.Atom ≃ U.Atom) (A : ArchitectureObject U)
    (W : Site.ArchitectureContext (transportArchitectureObject e A)) :
    transportArchitectureContext e A
      (transportArchitectureContextBackward e A W) = W := by
  rcases W with ⟨⟨Support, Axis, Observable, supportReads,
    supportReads_objectFamily, axisReads, observableReads⟩,
    Extension, extension⟩
  simp [transportArchitectureContext,
    transportArchitectureContextBackward,
    Site.ArchitectureContext.Support, Site.ArchitectureContext.Axis,
    Site.ArchitectureContext.Observable]

/-- Atom transport is an equivalence of architecture-context types. -/
def transportArchitectureContextEquiv {U : AtomCarrier.{u}}
    (e : U.Atom ≃ U.Atom) (A : ArchitectureObject U) :
    Site.ArchitectureContext A ≃
      Site.ArchitectureContext (transportArchitectureObject e A) where
  toFun := transportArchitectureContext e A
  invFun := transportArchitectureContextBackward e A
  left_inv := transportArchitectureContext_backward_forward e A
  right_inv := transportArchitectureContext_forward_backward e A

/-- Reuse the computational maps of a backward-context morphism on target contexts. -/
def contextMorphismOfBackward {U : AtomCarrier.{u}}
    (e : U.Atom ≃ U.Atom) (A : ArchitectureObject U)
    {W V : Site.ArchitectureContext (transportArchitectureObject e A)}
    (h : Site.ContextMorphism
      (transportArchitectureContextBackward e A W)
      (transportArchitectureContextBackward e A V)) :
    Site.ContextMorphism W V where
  supportMap := h.supportMap
  axisMap := h.axisMap
  observableRestrict := h.observableRestrict

/-- Restriction status survives canonical context conjugation. -/
theorem contextMorphismOfBackward_isRestriction {U : AtomCarrier.{u}}
    (e : U.Atom ≃ U.Atom) (A : ArchitectureObject U)
    {W V : Site.ArchitectureContext (transportArchitectureObject e A)}
    (h : Site.ContextMorphism
      (transportArchitectureContextBackward e A W)
      (transportArchitectureContextBackward e A V))
    (hh : h.IsRestriction) :
    (contextMorphismOfBackward e A h).IsRestriction := by
  rcases hh with ⟨hsupport, haxis, hobservable, hnongenerating⟩
  refine ⟨?_, haxis, hobservable, ?_⟩
  · intro support atom hread
    have hsource :
        (transportArchitectureContextBackward e A W).minimal.supportReads
          support (e.symm atom) := by
      simpa [transportArchitectureContextBackward] using hread
    have htarget := hsupport hsource
    simpa [contextMorphismOfBackward,
      transportArchitectureContextBackward] using htarget
  · intro support atom hread
    have hsource :
        (transportArchitectureContextBackward e A V).minimal.supportReads
          (h.supportMap support) (e.symm atom) := by
      simpa [transportArchitectureContextBackward] using hread
    have hfamily := hnongenerating hsource
    change (A.configuration.transport e).family.mem atom
    exact ⟨e.symm atom, hfamily, e.apply_symm_apply atom⟩

/-- Transport a selected context preorder by the canonical context equivalence. -/
def transportContextPreorder {U : AtomCarrier.{u}}
    (e : U.Atom ≃ U.Atom) (A : ArchitectureObject U)
    (C : Site.ContextPreorderCategory A) :
    Site.ContextPreorderCategory (transportArchitectureObject e A) where
  le W V := C.le
    (transportArchitectureContextBackward e A W)
    (transportArchitectureContextBackward e A V)
  refl _W := C.refl _
  trans hWV hVX := C.trans hWV hVX
  readableMorphism h :=
    contextMorphismOfBackward e A (C.readableMorphism h)
  readableMorphism_isRestriction h :=
    contextMorphismOfBackward_isRestriction e A _
      (C.readableMorphism_isRestriction h)

/-- Forward functor on the thin context categories selected by transport. -/
def transportContextFunctor {U : AtomCarrier.{u}}
    (e : U.Atom ≃ U.Atom) (A : ArchitectureObject U)
    (C : Site.ContextPreorderCategory A) :
    Site.ContextCategoryObject C ⥤
      Site.ContextCategoryObject (transportContextPreorder e A C) where
  obj W := ⟨transportArchitectureContext e A W.ctx⟩
  map {X Y} h := by
    apply homOfLE
    change C.le
      (transportArchitectureContextBackward e A
        (transportArchitectureContext e A X.ctx))
      (transportArchitectureContextBackward e A
        (transportArchitectureContext e A Y.ctx))
    simpa using h.le
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- Inverse functor on the transported thin context category. -/
def transportContextInverse {U : AtomCarrier.{u}}
    (e : U.Atom ≃ U.Atom) (A : ArchitectureObject U)
    (C : Site.ContextPreorderCategory A) :
    Site.ContextCategoryObject (transportContextPreorder e A C) ⥤
      Site.ContextCategoryObject C where
  obj W := ⟨transportArchitectureContextBackward e A W.ctx⟩
  map h := homOfLE h.le
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- The forward-then-inverse context functor fixes each source object. -/
private theorem transportContextInverseFunctor_obj_eq {U : AtomCarrier.{u}}
    (e : U.Atom ≃ U.Atom) (A : ArchitectureObject U)
    (C : Site.ContextPreorderCategory A) (W : Site.ContextCategoryObject C) :
    (transportContextFunctor e A C ⋙ transportContextInverse e A C).obj W = W := by
  cases W with
  | mk ctx =>
      simp [transportContextFunctor, transportContextInverse]

/-- The inverse-then-forward context functor fixes each transported object. -/
private theorem transportContextFunctorInverse_obj_eq {U : AtomCarrier.{u}}
    (e : U.Atom ≃ U.Atom) (A : ArchitectureObject U)
    (C : Site.ContextPreorderCategory A)
    (W : Site.ContextCategoryObject (transportContextPreorder e A C)) :
    (transportContextInverse e A C ⋙ transportContextFunctor e A C).obj W = W := by
  cases W with
  | mk ctx =>
      simp [transportContextFunctor, transportContextInverse]

/-- Canonical equivalence of source and transported context categories. -/
def transportContextEquivalence {U : AtomCarrier.{u}}
    (e : U.Atom ≃ U.Atom) (A : ArchitectureObject U)
    (C : Site.ContextPreorderCategory A) :
    Site.ContextCategoryObject C ≌
      Site.ContextCategoryObject (transportContextPreorder e A C) :=
  CategoryTheory.Equivalence.mk
    (transportContextFunctor e A C)
    (transportContextInverse e A C)
    (NatIso.ofComponents
      (fun W => eqToIso (transportContextInverseFunctor_obj_eq e A C W).symm)
      (by intros; apply Subsingleton.elim))
    (NatIso.ofComponents
      (fun W => eqToIso (transportContextFunctorInverse_obj_eq e A C W))
      (by intros; apply Subsingleton.elim))

/-- Transport an architectural equation system by context, object, and Atom conjugation. -/
def transportEquationSystem {U : AtomCarrier.{u}}
    (e : U.Atom ≃ U.Atom) (A : ArchitectureObject U)
    (C : Site.ContextPreorderCategory A)
    (E : ArchitecturalEquationSystem C) :
    ArchitecturalEquationSystem (transportContextPreorder e A C) where
  Index := E.Index
  role := E.role
  Observable W := E.Observable ((transportContextInverse e A C).obj W)
  observableCommRing W := E.observableCommRing _
  restrict f := E.restrict ((transportContextInverse e A C).map f)
  restrict_id W x := by
    simpa only [Functor.map_id] using
      E.restrict_id ((transportContextInverse e A C).obj W) x
  restrict_comp f g x := by
    simpa only [Functor.map_comp] using E.restrict_comp
      ((transportContextInverse e A C).map f)
      ((transportContextInverse e A C).map g) x
  violationCoordinate W i atom :=
    E.violationCoordinate ((transportContextInverse e A C).obj W)
      i (e.symm atom)
  violationCoordinate_restrict f i atom := by
    exact E.violationCoordinate_restrict
      ((transportContextInverse e A C).map f) i (e.symm atom)
  equationResidual W B i atom :=
    E.equationResidual ((transportContextInverse e A C).obj W)
      (transportArchitectureObject e.symm B) i (e.symm atom)
  equationResidual_restrict f B i atom := by
    exact E.equationResidual_restrict
      ((transportContextInverse e A C).map f)
      (transportArchitectureObject e.symm B) i (e.symm atom)

/-- The source observable ring is canonically the forward-context target ring. -/
def transportObservableEquiv {U : AtomCarrier.{u}}
    (e : U.Atom ≃ U.Atom) (A : ArchitectureObject U)
    (C : Site.ContextPreorderCategory A)
    (E : ArchitecturalEquationSystem C)
    (W : Site.ContextCategoryObject C) :
    E.Observable W ≃+*
      (transportEquationSystem e A C E).Observable
        ((transportContextFunctor e A C).obj W) :=
  RingEquiv.cast (transportContextInverseFunctor_obj_eq e A C W).symm

/-- Observable restriction commutes with casts of its context endpoints. -/
private theorem observableCast_restrict {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} {C : Site.ContextPreorderCategory A}
    (E : ArchitecturalEquationSystem C)
    {W V W' V' : Site.ContextCategoryObject C}
    (hW : W' = W) (hV : V' = V)
    (f : W ⟶ V) (f' : W' ⟶ V') (x : E.Observable V) :
    RingEquiv.cast hW.symm (E.restrict f x) =
      E.restrict f' (RingEquiv.cast hV.symm x) := by
  cases hW
  cases hV
  have hf : f' = f := Subsingleton.elim _ _
  cases hf
  rfl

/-- A violation coordinate is invariant under a context-index cast. -/
private theorem observableCast_violation {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} {C : Site.ContextPreorderCategory A}
    (E : ArchitecturalEquationSystem C)
    {W W' : Site.ContextCategoryObject C} (hW : W' = W)
    (i : E.Index) (atom : U.Atom) :
    RingEquiv.cast hW.symm (E.violationCoordinate W i atom) =
      E.violationCoordinate W' i atom := by
  cases hW
  rfl

/-- An equation residual is invariant under context and object casts. -/
private theorem observableCast_residual {U : AtomCarrier.{u}}
    {A₀ : ArchitectureObject U} {C : Site.ContextPreorderCategory A₀}
    (E : ArchitecturalEquationSystem C)
    {W W' : Site.ContextCategoryObject C} (hW : W' = W)
    {B B' : ArchitectureObject U} (hB : B' = B)
    (i : E.Index) (atom : U.Atom) :
    RingEquiv.cast hW.symm (E.equationResidual W B i atom) =
      E.equationResidual W' B' i atom := by
  cases hW
  cases hB
  rfl

/-- Canonical exact equation-system transport induced by Atom conjugation. -/
def transportEquationSystemExact {U : AtomCarrier.{u}}
    (e : U.Atom ≃ U.Atom) (A : ArchitectureObject U)
    (C : Site.ContextPreorderCategory A)
    (E : ArchitecturalEquationSystem C) :
    EquationSystemExactTransport E (transportEquationSystem e A C E)
      e (transportArchitectureObject e) where
  contextEquivalence := transportContextEquivalence e A C
  equationEquiv := Equiv.refl E.Index
  role_eq _ := rfl
  observableEquiv := transportObservableEquiv e A C E
  observable_naturality {W V} f x := by
    change
      transportObservableEquiv e A C E W (E.restrict f x) =
        E.restrict
          ((transportContextInverse e A C).map
            ((transportContextFunctor e A C).map f))
          (transportObservableEquiv e A C E V x)
    exact observableCast_restrict E
      (transportContextInverseFunctor_obj_eq e A C W)
      (transportContextInverseFunctor_obj_eq e A C V) f _ x
  violationCoordinate_eq W i atom := by
    change transportObservableEquiv e A C E W
      (E.violationCoordinate W i atom) =
        E.violationCoordinate
          ((transportContextInverse e A C).obj
            ((transportContextFunctor e A C).obj W)) i
          (e.symm (e atom))
    simpa using observableCast_violation E
      (transportContextInverseFunctor_obj_eq e A C W) i atom
  equationResidual_eq W B i atom := by
    change transportObservableEquiv e A C E W
      (E.equationResidual W B i atom) =
        E.equationResidual
          ((transportContextInverse e A C).obj
            ((transportContextFunctor e A C).obj W))
          (transportArchitectureObject e.symm
            (transportArchitectureObject e B)) i (e.symm (e atom))
    simpa using observableCast_residual E
      (transportContextInverseFunctor_obj_eq e A C W)
      (transportArchitectureObject_equiv_symm e B) i atom

/-- Transport equation-indexed detector syntax along the Atom equivalence. -/
def transportEquationCircuits {U : AtomCarrier.{u}}
    (e : U.Atom ≃ U.Atom) (A : ArchitectureObject U)
    (C : Site.ContextPreorderCategory A)
    (E : ArchitecturalEquationSystem C)
    (R : EquationCircuitReading E) :
    EquationCircuitReading (transportEquationSystem e A C E) where
  code i := (R.code i).transport e

/-- Transported detector syntax remains sound for the conjugated equation system. -/
theorem transportEquationCircuits_sound {U : AtomCarrier.{u}}
    (e : U.Atom ≃ U.Atom) (A : ArchitectureObject U)
    (C : Site.ContextPreorderCategory A)
    (E : ArchitecturalEquationSystem C)
    (R : EquationCircuitReading E) (hR : R.Sound) :
    (transportEquationCircuits e A C E R).Sound := by
  intro i B datum hmatches heval hholds
  have hmatchesBack :
      (datum.transport e.symm).Matches
        (transportArchitectureObject e.symm B) :=
    (FiniteCircuitDatum.transport_matches_iff e.symm datum B
      (transportArchitectureObject e.symm B) rfl).mp hmatches
  have hevalBack :
      (R.code i).eval (datum.transport e.symm) = true := by
    calc
      (R.code i).eval (datum.transport e.symm) =
          ((R.code i).transport e).eval
            ((datum.transport e.symm).transport e) :=
        (CircuitDetectorCode.eval_transport e (R.code i)
          (datum.transport e.symm)).symm
      _ = ((R.code i).transport e).eval datum := by simp
      _ = true := heval
  have hnotSource := hR i (transportArchitectureObject e.symm B)
    (datum.transport e.symm) hmatchesBack hevalBack
  have htarget' :
      (transportEquationSystem e A C E).EquationHolds i
        (transportArchitectureObject e
          (transportArchitectureObject e.symm B)) := by
    simpa using hholds
  have hsource :=
    ((transportEquationSystemExact e A C E).equationHolds_iff i
      (transportArchitectureObject e.symm B)).mpr htarget'
  exact hnotSource hsource

/-- Transport a complete equation reading on the direct-image base object. -/
def transportEquationReading {U : AtomCarrier.{u}}
    (e : U.Atom ≃ U.Atom) (A : ArchitectureObject U)
    (R : EquationReading A) :
    EquationReading (transportArchitectureObject e A) where
  contextPreorder := transportContextPreorder e A R.contextPreorder
  equationSystem :=
    transportEquationSystem e A R.contextPreorder R.equationSystem
  circuits := transportEquationCircuits e A R.contextPreorder
    R.equationSystem R.circuits
  circuitSound := transportEquationCircuits_sound e A R.contextPreorder
    R.equationSystem R.circuits R.circuitSound

/-- Reindex an equation reading along equality of its base object. -/
def castEquationReading {U : AtomCarrier.{u}}
    {A B : ArchitectureObject U} (h : A = B) (R : EquationReading A) :
    EquationReading B := by
  cases h
  exact R

/-- The mapped canonical family remains explicitly list-finite. -/
def transportFamilyListFinite {U : AtomCarrier.{u}}
    {E : ExtractionDoctrine U} (R : CoreReading U)
    (f : ExactDoctrineHom R.doctrine E) :
    (E.atomize (f.sourceMap R.source)).ListFinite := by
  rw [f.atomize_naturality R.source]
  exact R.family_listFinite.transport f.atomEquiv

/-- The base object selected by all transported lower reading components. -/
def transportedBaseObject {U : AtomCarrier.{u}}
    {E : ExtractionDoctrine U} (R : CoreReading U)
    (f : ExactDoctrineHom R.doctrine E) : ArchitectureObject U :=
  (transportObjectReading f.atomEquiv R.objectReading).object
    ((transportCompositionReading f.atomEquiv R.composition).compose
      (E.atomize (f.sourceMap R.source))
      (transportFamilyListFinite R f))

/-- The transported lower readings select the direct image of the source base object. -/
theorem transportedBaseObject_eq {U : AtomCarrier.{u}}
    {E : ExtractionDoctrine U} (R : CoreReading U)
    (f : ExactDoctrineHom R.doctrine E) :
    transportedBaseObject R f =
      transportArchitectureObject f.atomEquiv
        (R.objectReading.object
          (R.composition.compose (R.doctrine.atomize R.source)
            R.family_listFinite)) := by
  let targetInput : {F : AtomFamily U // F.ListFinite} :=
    ⟨E.atomize (f.sourceMap R.source), transportFamilyListFinite R f⟩
  let directImageInput : {F : AtomFamily U // F.ListFinite} :=
    ⟨(R.doctrine.atomize R.source).transport f.atomEquiv,
      R.family_listFinite.transport f.atomEquiv⟩
  have hinput : targetInput = directImageInput := by
    apply Subtype.ext
    exact f.atomize_naturality R.source
  have hcomposition :
      (transportCompositionReading f.atomEquiv R.composition).compose
          targetInput.1 targetInput.2 =
        (R.composition.compose (R.doctrine.atomize R.source)
          R.family_listFinite).transport f.atomEquiv := by
    calc
      _ = (transportCompositionReading f.atomEquiv R.composition).compose
          directImageInput.1 directImageInput.2 :=
        congrArg
          (fun input : {F : AtomFamily U // F.ListFinite} =>
            (transportCompositionReading f.atomEquiv R.composition).compose
              input.1 input.2) hinput
      _ = _ := transportCompositionReading_compose_transport
        f.atomEquiv R.composition _ _
  change
    (transportObjectReading f.atomEquiv R.objectReading).object
        ((transportCompositionReading f.atomEquiv R.composition).compose
          targetInput.1 targetInput.2) = _
  rw [hcomposition]
  exact (transportObjectReading_object_transport f.atomEquiv
    R.objectReading _).symm

/-- Transport every component of a core reading along one exact doctrine morphism. -/
def transportCoreReading {U : AtomCarrier.{u}}
    {E : ExtractionDoctrine U} (R : CoreReading U)
    (f : ExactDoctrineHom R.doctrine E) : CoreReading U where
  doctrine := E
  source := f.sourceMap R.source
  family_listFinite := transportFamilyListFinite R f
  composition := transportCompositionReading f.atomEquiv R.composition
  objectReading := transportObjectReading f.atomEquiv R.objectReading
  equationReading :=
    castEquationReading (transportedBaseObject_eq R f).symm
      (transportEquationReading f.atomEquiv
        (R.objectReading.object
          (R.composition.compose (R.doctrine.atomize R.source)
            R.family_listFinite))
        R.equationReading)
  invariantReading := transportInvariantFamily f.atomEquiv R.invariantReading
  signatureReading :=
    transportArchitectureSignature f.atomEquiv R.signatureReading
  operationReading := transportOperationReading f.atomEquiv R.operationReading

/-- Canonical target core package generated from a source package and exact morphism. -/
def transportAlong {U : AtomCarrier.{u}}
    (P : AATCorePackage U) {E : ExtractionDoctrine U}
    (f : ExactDoctrineHom P.reading.doctrine E) : AATCorePackage U where
  axioms := P.axioms
  reading := transportCoreReading P.reading f

/-- Canonical package transport uses the target doctrine of its exact morphism. -/
@[simp]
theorem transportAlong_doctrine {U : AtomCarrier.{u}}
    (P : AATCorePackage U) {E : ExtractionDoctrine U}
    (f : ExactDoctrineHom P.reading.doctrine E) :
    (transportAlong P f).reading.doctrine = E :=
  rfl

/-- Canonical package transport maps the source through the doctrine morphism. -/
@[simp]
theorem transportAlong_source {U : AtomCarrier.{u}}
    (P : AATCorePackage U) {E : ExtractionDoctrine U}
    (f : ExactDoctrineHom P.reading.doctrine E) :
    (transportAlong P f).reading.source = f.sourceMap P.reading.source :=
  rfl

/-- Cast the target reading of an exact equation-system transport. -/
private def castEquationSystemExactTransport {U : AtomCarrier.{u}}
    {A₀ A B : ArchitectureObject U}
    (R : EquationReading A₀) (S : EquationReading A)
    (h : A = B) (e : U.Atom ≃ U.Atom)
    (objectMap : ArchitectureObject U → ArchitectureObject U)
    (T : EquationSystemExactTransport R.equationSystem S.equationSystem
      e objectMap) :
    EquationSystemExactTransport R.equationSystem
      (castEquationReading h S).equationSystem e objectMap := by
  cases h
  exact T

/-- Casting the target reading preserves the exact transport equation map. -/
private theorem castEquationSystemExactTransport_equationMap_heq
    {U : AtomCarrier.{u}} {A₀ A B : ArchitectureObject U}
    (R : EquationReading A₀) (S : EquationReading A)
    (h : A = B) (e : U.Atom ≃ U.Atom)
    (objectMap : ArchitectureObject U → ArchitectureObject U)
    (T : EquationSystemExactTransport R.equationSystem S.equationSystem
      e objectMap) (i : R.equationSystem.Index) :
    HEq
      ((castEquationSystemExactTransport R S h e objectMap T).equationMap i)
      (T.equationMap i) := by
  cases h
  rfl

/-- Casting the target reading preserves transported detector code. -/
private theorem castEquationSystemExactTransport_detectorCode {U : AtomCarrier.{u}}
    {A₀ A B : ArchitectureObject U}
    (R : EquationReading A₀) (S : EquationReading A)
    (h : A = B) (e : U.Atom ≃ U.Atom)
    (objectMap : ArchitectureObject U → ArchitectureObject U)
    (T : EquationSystemExactTransport R.equationSystem S.equationSystem
      e objectMap)
    (hcode : ∀ i,
      S.circuits.code (T.equationMap i) =
        (R.circuits.code i).transport e)
    (i : R.equationSystem.Index) :
    (castEquationReading h S).circuits.code
        ((castEquationSystemExactTransport R S h e objectMap T).equationMap i) =
      (R.circuits.code i).transport e := by
  cases h
  exact hcode i

/-- Canonical equation transport used by the transported core reading. -/
def transportCoreEquationSystemExact {U : AtomCarrier.{u}}
    {E : ExtractionDoctrine U} (R : CoreReading U)
    (f : ExactDoctrineHom R.doctrine E) :
    EquationSystemExactTransport R.equationReading.equationSystem
      (transportCoreReading R f).equationReading.equationSystem
      f.atomEquiv (transportArchitectureObject f.atomEquiv) :=
  castEquationSystemExactTransport R.equationReading
    (transportEquationReading f.atomEquiv
      (R.objectReading.object
        (R.composition.compose (R.doctrine.atomize R.source)
          R.family_listFinite))
      R.equationReading)
    (transportedBaseObject_eq R f).symm f.atomEquiv
    (transportArchitectureObject f.atomEquiv)
    (transportEquationSystemExact f.atomEquiv
      (R.objectReading.object
        (R.composition.compose (R.doctrine.atomize R.source)
          R.family_listFinite))
      R.equationReading.contextPreorder R.equationReading.equationSystem)

/-- Canonical core transport retains the source equation index up to its cast. -/
@[simp]
theorem transportCoreEquationSystemExact_equationMap_heq
    {U : AtomCarrier.{u}} {E : ExtractionDoctrine U} (R : CoreReading U)
    (f : ExactDoctrineHom R.doctrine E)
    (i : R.equationReading.equationSystem.Index) :
    HEq ((transportCoreEquationSystemExact R f).equationMap i) i := by
  exact castEquationSystemExactTransport_equationMap_heq
    R.equationReading
    (transportEquationReading f.atomEquiv
      (R.objectReading.object
        (R.composition.compose (R.doctrine.atomize R.source)
          R.family_listFinite))
      R.equationReading)
    (transportedBaseObject_eq R f).symm f.atomEquiv
    (transportArchitectureObject f.atomEquiv)
    (transportEquationSystemExact f.atomEquiv
      (R.objectReading.object
        (R.composition.compose (R.doctrine.atomize R.source)
          R.family_listFinite))
      R.equationReading.contextPreorder R.equationReading.equationSystem) i

/-- Detector transport is supplied by the same equation-reading conjugation. -/
theorem transportCore_detectorCode_eq {U : AtomCarrier.{u}}
    {E : ExtractionDoctrine U} (R : CoreReading U)
    (f : ExactDoctrineHom R.doctrine E)
    (i : R.equationReading.equationSystem.Index) :
    (transportCoreReading R f).equationReading.circuits.code
        ((transportCoreEquationSystemExact R f).equationMap i) =
      (R.equationReading.circuits.code i).transport f.atomEquiv := by
  apply castEquationSystemExactTransport_detectorCode
    R.equationReading
    (transportEquationReading f.atomEquiv
      (R.objectReading.object
        (R.composition.compose (R.doctrine.atomize R.source)
          R.family_listFinite))
      R.equationReading)
    (transportedBaseObject_eq R f).symm f.atomEquiv
    (transportArchitectureObject f.atomEquiv)
    (transportEquationSystemExact f.atomEquiv
      (R.objectReading.object
        (R.composition.compose (R.doctrine.atomize R.source)
          R.family_listFinite))
      R.equationReading.contextPreorder R.equationReading.equationSystem)
  intro j
  rfl

/-- The complete tautological signed exact hom into the transported package. -/
def transportAlongUpper {U : AtomCarrier.{u}}
    (P : AATCorePackage U) {E : ExtractionDoctrine U}
    (f : ExactDoctrineHom P.reading.doctrine E) :
    SignedExactCoreReadingHom P (transportAlong P f) where
  atomEquiv := f.atomEquiv
  extraction_eq := by
    change E.atomize (f.sourceMap P.reading.source) =
      (P.reading.doctrine.atomize P.reading.source).transport f.atomEquiv
    exact f.atomize_naturality P.reading.source
  composition_eq F hF :=
    transportCompositionReading_compose_transport
      f.atomEquiv P.reading.composition F hF
  objectMap := transportArchitectureObject f.atomEquiv
  object_formation_eq C :=
    transportObjectReading_object_transport
      f.atomEquiv P.reading.objectReading C
  configurationMap A :=
    AtomConfiguration.transportHom f.atomEquiv A.configuration
  configurationMap_atomMap _ := rfl
  configuration_eq _ := rfl
  equationTransport := transportCoreEquationSystemExact P.reading f
  detectorCode_eq i := transportCore_detectorCode_eq P.reading f i
  operationMap op :=
    transportOperation f.atomEquiv P.reading.operationReading op
  operation_naturality op :=
    transportOperation_naturality f.atomEquiv P.reading.operationReading op
  invariantMap := _root_.id
  invariant_transport i :=
    invariant_transportAlong f.atomEquiv
      (P.reading.invariantReading.invariant i)
  axisMap := _root_.id
  coordinateEquiv _ := Equiv.refl _
  axis_selected_iff _ := Iff.rfl
  coordinate_eq A i :=
    (transportArchitectureSignature_coordinate f.atomEquiv
      P.reading.signatureReading A i).symm

/-- The tautological total hom lying over the specified exact doctrine morphism. -/
def transportAlongHom {U : AtomCarrier.{u}}
    (P : AATCorePackage U) {E : ExtractionDoctrine U}
    (f : ExactDoctrineHom P.reading.doctrine E) :
    PackageTotalHom P (transportAlong P f) where
  base := {
    doctrineHom := f
    source_eq := rfl
  }
  upper := transportAlongUpper P f
  atomEquiv_eq := rfl

/-- The target package projects to the canonically mapped pointed doctrine. -/
theorem transportAlong_point {U : AtomCarrier.{u}}
    (P : AATCorePackage U) {E : ExtractionDoctrine U}
    (f : ExactDoctrineHom P.reading.doctrine E) :
    packagePoint (transportAlong P f) =
      ({ doctrine := E, source := f.sourceMap P.reading.source } :
        ExtractionInstance U) :=
  rfl

/-- Projection of the tautological total hom is the specified exact base morphism. -/
theorem transportAlong_projection {U : AtomCarrier.{u}}
    (P : AATCorePackage U) {E : ExtractionDoctrine U}
    (f : ExactDoctrineHom P.reading.doctrine E) :
    (packageProjection U).map (transportAlongHom P f) =
      ({ doctrineHom := f, source_eq := rfl } :
        ExtInstHom (packagePoint P) (packagePoint (transportAlong P f))) :=
  rfl

/-- Standalone family computation for canonical package transport. -/
theorem transportAlong_family_eq {U : AtomCarrier.{u}}
    (P : AATCorePackage U) {E : ExtractionDoctrine U}
    (f : ExactDoctrineHom P.reading.doctrine E) :
    (transportAlong P f).family = P.family.transport f.atomEquiv :=
  (transportAlongUpper P f).extraction_eq

/-- Standalone generated-configuration computation from the same upper hom. -/
theorem transportAlong_configuration_eq {U : AtomCarrier.{u}}
    (P : AATCorePackage U) {E : ExtractionDoctrine U}
    (f : ExactDoctrineHom P.reading.doctrine E) :
    (transportAlong P f).configuration =
      P.configuration.transport f.atomEquiv :=
  (transportAlongUpper P f).generatedConfiguration_eq

/-- Standalone generated-object computation from the same upper hom. -/
theorem transportAlong_object_eq {U : AtomCarrier.{u}}
    (P : AATCorePackage U) {E : ExtractionDoctrine U}
    (f : ExactDoctrineHom P.reading.doctrine E) :
    transportArchitectureObject f.atomEquiv P.object =
      (transportAlong P f).object :=
  (transportAlongUpper P f).base_eq

/-- Standalone detector-code computation from the canonical equation transport. -/
theorem transportAlong_detectorCode_eq {U : AtomCarrier.{u}}
    (P : AATCorePackage U) {E : ExtractionDoctrine U}
    (f : ExactDoctrineHom P.reading.doctrine E)
    (i : P.algebra.equationSystem.Index) :
    (transportAlong P f).algebra.circuits.code
        ((transportAlongUpper P f).equationMap i) =
      (P.algebra.circuits.code i).transport f.atomEquiv :=
  (transportAlongUpper P f).detectorCode_eq i

end AAT.AG.AtomFoundation

#assert_standard_axioms_only AAT.AG.AtomFoundation
