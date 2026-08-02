import ResearchLean.AG.AtomFoundation.Transport

/-!
# Deconjugation of canonical complete transport

This module divides a complete signed exact upper hom by the canonical
transport constructed in `Transport`.  The division uses only the supplied
Atom equivalences and the conjugated reading data; it does not invert the
source map of the underlying extraction-doctrine morphism.
-/

namespace AAT.AG.AtomFoundation

universe u v

open CategoryTheory

/--
Divide an equation-system transport by the canonical equation conjugation.

The source observable at a transported context is definitionally the original
observable at the inverse context.  Thus the divided observable map is the
given map evaluated there; no extra observable or equation data are selected.
-/
def deconjugateEquationSystemExact {U : AtomCarrier.{u}}
    (e t : Equiv U.Atom U.Atom)
    (A : ArchitectureObject U)
    (C : Site.ContextPreorderCategory A)
    (E : ArchitecturalEquationSystem C)
    {B : ArchitectureObject U}
    {D : Site.ContextPreorderCategory B}
    {G : ArchitecturalEquationSystem D}
    (objectMap : ArchitectureObject U → ArchitectureObject U)
    (H : EquationSystemExactTransport E G (e.trans t) objectMap) :
    EquationSystemExactTransport
      (transportEquationSystem e A C E) G t
      (fun X => objectMap (transportArchitectureObject e.symm X)) where
  contextEquivalence :=
    (transportContextEquivalence e A C).symm.trans H.contextEquivalence
  equationEquiv := H.equationEquiv
  role_eq i := H.role_eq i
  observableEquiv W :=
    H.observableEquiv ((transportContextInverse e A C).obj W)
  observable_naturality f x := by
    exact H.observable_naturality
      ((transportContextInverse e A C).map f) x
  violationCoordinate_eq W i atom := by
    simpa only [Equiv.trans_apply, Equiv.apply_symm_apply] using
      H.violationCoordinate_eq
        ((transportContextInverse e A C).obj W) i (e.symm atom)
  equationResidual_eq W X i atom := by
    simpa only [Equiv.trans_apply, Equiv.apply_symm_apply] using
      H.equationResidual_eq
        ((transportContextInverse e A C).obj W)
        (transportArchitectureObject e.symm X) i (e.symm atom)

/-- Reindex the source equation reading of an exact transport. -/
private def castSourceEquationSystemExact {U : AtomCarrier.{u}}
    {A A' B : ArchitectureObject U}
    {D : Site.ContextPreorderCategory B}
    {G : ArchitecturalEquationSystem D}
    (h : A = A') (R : EquationReading A)
    (e : Equiv U.Atom U.Atom)
    (objectMap : ArchitectureObject U → ArchitectureObject U)
    (T : EquationSystemExactTransport R.equationSystem G e objectMap) :
    EquationSystemExactTransport
      (castEquationReading h R).equationSystem G e objectMap := by
  cases h
  exact T

/--
Canonical upper deconjugation for the equation-system component of a transported
core.  The target system and the residual object map remain arbitrary.
-/
def transportCoreEquationSystemExactReverse {U : AtomCarrier.{u}}
    {E : ExtractionDoctrine U} (R : CoreReading U)
    (f : ExactDoctrineHom R.doctrine E)
    (t : Equiv U.Atom U.Atom)
    {B : ArchitectureObject U}
    {D : Site.ContextPreorderCategory B}
    {G : ArchitecturalEquationSystem D}
    (objectMap : ArchitectureObject U → ArchitectureObject U)
    (H : EquationSystemExactTransport R.equationReading.equationSystem G
      (f.atomEquiv.trans t) objectMap) :
    EquationSystemExactTransport
      (transportCoreReading R f).equationReading.equationSystem G t
      (fun X => objectMap
        (transportArchitectureObject f.atomEquiv.symm X)) :=
  castSourceEquationSystemExact
    (transportedBaseObject_eq R f).symm
    (transportEquationReading f.atomEquiv
      (R.objectReading.object
        (R.composition.compose (R.doctrine.atomize R.source)
          R.family_listFinite))
      R.equationReading)
    t (fun X => objectMap
      (transportArchitectureObject f.atomEquiv.symm X))
    (deconjugateEquationSystemExact f.atomEquiv t
      (R.objectReading.object
        (R.composition.compose (R.doctrine.atomize R.source)
          R.family_listFinite))
      R.equationReading.contextPreorder R.equationReading.equationSystem
      objectMap H)

/-- Reindex detector compatibility together with its source equation reading. -/
private theorem castSourceEquationSystemExact_detectorCode
    {U : AtomCarrier.{u}}
    {A A' B : ArchitectureObject U}
    {D : Site.ContextPreorderCategory B}
    {G : ArchitecturalEquationSystem D}
    (h : A = A') (R : EquationReading A)
    (e : Equiv U.Atom U.Atom)
    (objectMap : ArchitectureObject U → ArchitectureObject U)
    (T : EquationSystemExactTransport R.equationSystem G e objectMap)
    (targetCode : G.Index → CircuitDetectorCode U)
    (hcode : ∀ i,
      targetCode (T.equationMap i) = (R.circuits.code i).transport e)
    (i : (castEquationReading h R).equationSystem.Index) :
    targetCode
        ((castSourceEquationSystemExact h R e objectMap T).equationMap i) =
      ((castEquationReading h R).circuits.code i).transport e := by
  cases h
  exact hcode i

/-- Detector compatibility of canonical equation deconjugation. -/
theorem transportCoreEquationSystemExactReverse_detectorCode
    {U : AtomCarrier.{u}}
    {E : ExtractionDoctrine U} (R : CoreReading U)
    (f : ExactDoctrineHom R.doctrine E)
    (t : Equiv U.Atom U.Atom)
    {B : ArchitectureObject U}
    {D : Site.ContextPreorderCategory B}
    {G : ArchitecturalEquationSystem D}
    (objectMap : ArchitectureObject U → ArchitectureObject U)
    (H : EquationSystemExactTransport R.equationReading.equationSystem G
      (f.atomEquiv.trans t) objectMap)
    (targetCode : G.Index → CircuitDetectorCode U)
    (hcode : ∀ i,
      targetCode (H.equationMap i) =
        (R.equationReading.circuits.code i).transport
          (f.atomEquiv.trans t))
    (i : (transportCoreReading R f).equationReading.equationSystem.Index) :
    targetCode
        ((transportCoreEquationSystemExactReverse R f t objectMap H).equationMap i) =
      ((transportCoreReading R f).equationReading.circuits.code i).transport t := by
  apply castSourceEquationSystemExact_detectorCode
    (transportedBaseObject_eq R f).symm
    (transportEquationReading f.atomEquiv
      (R.objectReading.object
        (R.composition.compose (R.doctrine.atomize R.source)
          R.family_listFinite))
      R.equationReading)
    t (fun X => objectMap
      (transportArchitectureObject f.atomEquiv.symm X))
    (deconjugateEquationSystemExact f.atomEquiv t
      (R.objectReading.object
        (R.composition.compose (R.doctrine.atomize R.source)
          R.family_listFinite))
      R.equationReading.contextPreorder R.equationReading.equationSystem
      objectMap H)
    targetCode
  intro j
  change targetCode (H.equationMap j) =
    ((R.equationReading.circuits.code j).transport f.atomEquiv).transport t
  rw [CircuitDetectorCode.transport_trans]
  exact hcode j

/-- Reindex the Atom equivalence parameter of an exact equation transport. -/
private def castAtomEquationSystemExact {U : AtomCarrier.{u}}
    {A B : ArchitectureObject U}
    {C : Site.ContextPreorderCategory A}
    {D : Site.ContextPreorderCategory B}
    {E : ArchitecturalEquationSystem C}
    {G : ArchitecturalEquationSystem D}
    {e e' : Equiv U.Atom U.Atom}
    {objectMap : ArchitectureObject U → ArchitectureObject U}
    (he : e = e')
    (T : EquationSystemExactTransport E G e objectMap) :
    EquationSystemExactTransport E G e' objectMap := by
  cases he
  exact T

/-- Reindex detector compatibility with the Atom parameter of its transport. -/
private theorem castAtomEquationSystemExact_detectorCode
    {U : AtomCarrier.{u}}
    {A B : ArchitectureObject U}
    {C : Site.ContextPreorderCategory A}
    {D : Site.ContextPreorderCategory B}
    {E : ArchitecturalEquationSystem C}
    {G : ArchitecturalEquationSystem D}
    {e e' : Equiv U.Atom U.Atom}
    {objectMap : ArchitectureObject U → ArchitectureObject U}
    (he : e = e')
    (T : EquationSystemExactTransport E G e objectMap)
    (sourceCode : E.Index → CircuitDetectorCode U)
    (targetCode : G.Index → CircuitDetectorCode U)
    (hcode : ∀ i,
      targetCode (T.equationMap i) = (sourceCode i).transport e)
    (i : E.Index) :
    targetCode
        ((castAtomEquationSystemExact he T).equationMap i) =
      (sourceCode i).transport e' := by
  cases he
  exact hcode i

/-- Atom-parameter reindexing does not change the underlying exact transport. -/
private theorem castAtomEquationSystemExact_heq
    {U : AtomCarrier.{u}}
    {A B : ArchitectureObject U}
    {C : Site.ContextPreorderCategory A}
    {D : Site.ContextPreorderCategory B}
    {E : ArchitecturalEquationSystem C}
    {G : ArchitecturalEquationSystem D}
    {e e' : Equiv U.Atom U.Atom}
    {objectMap : ArchitectureObject U → ArchitectureObject U}
    (he : e = e')
    (T : EquationSystemExactTransport E G e objectMap) :
    HEq (castAtomEquationSystemExact he T) T := by
  cases he
  rfl

/-- Remove canonical object conjugation from an invariant transport proof. -/
theorem invariant_transport_deconjugate {U : AtomCarrier.{u}}
    (e : Equiv U.Atom U.Atom) (I J : Invariant U)
    (objectMap : ArchitectureObject U → ArchitectureObject U)
    (h : Invariant.TransportedAlong I J _root_.id objectMap) :
    Invariant.TransportedAlong (transportInvariant e I) J _root_.id
      (fun A => objectMap (transportArchitectureObject e.symm A)) := by
  cases I with
  | function I =>
      cases J with
      | function J =>
          rcases h with ⟨valueEquiv, hvalue⟩
          exact ⟨valueEquiv, fun A => hvalue
            (transportArchitectureObject e.symm A)⟩
      | predicate J => exact h
  | predicate I =>
      cases J with
      | function J => exact h
      | predicate J =>
          exact fun A => h (transportArchitectureObject e.symm A)

/-- Equal subsingleton types have heterogeneously equal inhabitants. -/
private theorem subsingleton_heq_of_type_eq
    {alpha beta : Sort v} [Subsingleton alpha] [Subsingleton beta]
    (h : alpha = beta) (a : alpha) (b : beta) : HEq a b := by
  cases h
  exact heq_of_eq (Subsingleton.elim _ _)

/-- Casting an indexed source ring before its pointwise equivalence is inert. -/
private theorem ringEquiv_cast_trans_heq
    {index : Type*}
    {source target : index → Type*}
    [(i : index) → CommRing (source i)]
    [(i : index) → CommRing (target i)]
    {i j : index} (h : i = j)
    (equivs : ∀ k, source k ≃+* target k) :
    HEq ((RingEquiv.cast (R := source) h).trans (equivs j)) (equivs i) := by
  cases h
  apply heq_of_eq
  apply RingEquiv.ext
  intro x
  rfl

/-- Canonical context conjugation cancels strictly at the equivalence record. -/
theorem transportContextEquivalence_trans_symm_trans
    {U : AtomCarrier.{u}}
    (e : Equiv U.Atom U.Atom)
    (A : ArchitectureObject U)
    (C : Site.ContextPreorderCategory A)
    {B : ArchitectureObject U}
    {D : Site.ContextPreorderCategory B}
    (H : Site.ContextCategoryObject C ≌
      Site.ContextCategoryObject D) :
    (transportContextEquivalence e A C).trans
        ((transportContextEquivalence e A C).symm.trans H) = H := by
  have hfunctor :
      ((transportContextEquivalence e A C).trans
        ((transportContextEquivalence e A C).symm.trans H)).functor =
          H.functor := by
    refine CategoryTheory.Functor.ext (fun W => ?_) ?_
    · change H.functor.obj
          ((transportContextInverse e A C).obj
            ((transportContextFunctor e A C).obj W)) = H.functor.obj W
      apply congrArg H.functor.obj
      cases W with
      | mk ctx =>
          simp [transportContextFunctor, transportContextInverse]
    · intros
      exact Subsingleton.elim _ _
  have hinverse :
      ((transportContextEquivalence e A C).trans
        ((transportContextEquivalence e A C).symm.trans H)).inverse =
          H.inverse := by
    refine CategoryTheory.Functor.ext (fun W => ?_) ?_
    · change
        (transportContextInverse e A C).obj
            ((transportContextFunctor e A C).obj (H.inverse.obj W)) =
          H.inverse.obj W
      cases hW : H.inverse.obj W with
      | mk ctx =>
          simp [transportContextFunctor, transportContextInverse]
    · intros
      exact Subsingleton.elim _ _
  apply Equivalence.ext hfunctor hinverse
  · apply subsingleton_heq_of_type_eq
    apply congrArg (fun F => (𝟭 (Site.ContextCategoryObject C)) ≅ F)
    rw [hfunctor, hinverse]
  · apply subsingleton_heq_of_type_eq
    apply congrArg (fun F => F ≅ (𝟭 (Site.ContextCategoryObject D)))
    rw [hfunctor, hinverse]

/-- Extensionality for the computational fields of exact equation transport. -/
private theorem equationSystemExactTransport_ext
    {U : AtomCarrier.{u}}
    {A B : ArchitectureObject U}
    {C : Site.ContextPreorderCategory A}
    {D : Site.ContextPreorderCategory B}
    {E : ArchitecturalEquationSystem C}
    {G : ArchitecturalEquationSystem D}
    {e : Equiv U.Atom U.Atom}
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

/-- Heterogeneous extensionality across equal Atom and object-map parameters. -/
private theorem equationSystemExactTransport_hext
    {U : AtomCarrier.{u}}
    {A B : ArchitectureObject U}
    {C : Site.ContextPreorderCategory A}
    {D : Site.ContextPreorderCategory B}
    {E : ArchitecturalEquationSystem C}
    {G : ArchitecturalEquationSystem D}
    {e e' : Equiv U.Atom U.Atom}
    {objectMap objectMap' : ArchitectureObject U → ArchitectureObject U}
    {T : EquationSystemExactTransport E G e objectMap}
    {S : EquationSystemExactTransport E G e' objectMap'}
    (he : e = e') (hobjectMap : objectMap = objectMap')
    (hcontext : T.contextEquivalence = S.contextEquivalence)
    (hequation : T.equationEquiv = S.equationEquiv)
    (hobservable : HEq T.observableEquiv S.observableEquiv) : HEq T S := by
  cases he
  cases hobjectMap
  exact heq_of_eq
    (equationSystemExactTransport_ext hcontext hequation hobservable)

/-- Object roundtrip underlying canonical context conjugation. -/
theorem transportContextInverseFunctor_obj_eq {U : AtomCarrier.{u}}
    (e : Equiv U.Atom U.Atom)
    (A : ArchitectureObject U)
    (C : Site.ContextPreorderCategory A)
    (W : Site.ContextCategoryObject C) :
    (transportContextInverse e A C).obj
        ((transportContextFunctor e A C).obj W) = W := by
  cases W with
  | mk ctx =>
      simp [transportContextFunctor, transportContextInverse]

/-- The other object roundtrip underlying canonical context conjugation. -/
theorem transportContextFunctorInverse_obj_eq {U : AtomCarrier.{u}}
    (e : Equiv U.Atom U.Atom)
    (A : ArchitectureObject U)
    (C : Site.ContextPreorderCategory A)
    (W : Site.ContextCategoryObject (transportContextPreorder e A C)) :
    (transportContextFunctor e A C).obj
        ((transportContextInverse e A C).obj W) = W := by
  cases W with
  | mk ctx =>
      simp [transportContextFunctor, transportContextInverse]

/-- Canonical context deconjugation is also a strict retraction. -/
theorem transportContextEquivalence_symm_trans_trans
    {U : AtomCarrier.{u}}
    (e : Equiv U.Atom U.Atom)
    (A : ArchitectureObject U)
    (C : Site.ContextPreorderCategory A)
    {B : ArchitectureObject U}
    {D : Site.ContextPreorderCategory B}
    (H : Site.ContextCategoryObject (transportContextPreorder e A C) ≌
      Site.ContextCategoryObject D) :
    (transportContextEquivalence e A C).symm.trans
        ((transportContextEquivalence e A C).trans H) = H := by
  have hfunctor :
      ((transportContextEquivalence e A C).symm.trans
        ((transportContextEquivalence e A C).trans H)).functor =
          H.functor := by
    refine CategoryTheory.Functor.ext (fun W => ?_) ?_
    · change H.functor.obj
          ((transportContextFunctor e A C).obj
            ((transportContextInverse e A C).obj W)) = H.functor.obj W
      apply congrArg H.functor.obj
      exact transportContextFunctorInverse_obj_eq e A C W
    · intros
      exact Subsingleton.elim _ _
  have hinverse :
      ((transportContextEquivalence e A C).symm.trans
        ((transportContextEquivalence e A C).trans H)).inverse =
          H.inverse := by
    refine CategoryTheory.Functor.ext (fun W => ?_) ?_
    · change
        (transportContextFunctor e A C).obj
            ((transportContextInverse e A C).obj (H.inverse.obj W)) =
          H.inverse.obj W
      exact transportContextFunctorInverse_obj_eq e A C (H.inverse.obj W)
    · intros
      exact Subsingleton.elim _ _
  apply Equivalence.ext hfunctor hinverse
  · apply subsingleton_heq_of_type_eq
    apply congrArg
      (fun F => (𝟭 (Site.ContextCategoryObject
        (transportContextPreorder e A C))) ≅ F)
    rw [hfunctor, hinverse]
  · apply subsingleton_heq_of_type_eq
    apply congrArg (fun F => F ≅ (𝟭 (Site.ContextCategoryObject D)))
    rw [hfunctor, hinverse]

/-- Canonical equation transport followed by its divided tail recovers the input. -/
theorem transportEquationSystemExact_comp_deconjugate
    {U : AtomCarrier.{u}}
    (e t : Equiv U.Atom U.Atom)
    (A : ArchitectureObject U)
    (C : Site.ContextPreorderCategory A)
    (E : ArchitecturalEquationSystem C)
    {B : ArchitectureObject U}
    {D : Site.ContextPreorderCategory B}
    {G : ArchitecturalEquationSystem D}
    (objectMap : ArchitectureObject U → ArchitectureObject U)
    (H : EquationSystemExactTransport E G (e.trans t) objectMap) :
    HEq
      ((transportEquationSystemExact e A C E).comp
        (deconjugateEquationSystemExact e t A C E objectMap H)) H := by
  apply equationSystemExactTransport_hext rfl
  · funext X
    exact congrArg objectMap (transportArchitectureObject_equiv_symm e X)
  · exact transportContextEquivalence_trans_symm_trans e A C
      H.contextEquivalence
  · apply Equiv.ext
    intro i
    rfl
  · apply Function.hfunext rfl
    intro W W' hW
    cases hW
    have hround := transportContextInverseFunctor_obj_eq e A C W
    change HEq
      ((transportObservableEquiv e A C E W).trans
        (H.observableEquiv
          ((transportContextInverse e A C).obj
            ((transportContextFunctor e A C).obj W))))
      (H.observableEquiv W)
    have hcast :
        transportObservableEquiv e A C E W =
          RingEquiv.cast
            (R := fun X : Site.ContextCategoryObject C => E.Observable X)
            hround.symm := by
      apply RingEquiv.ext
      intro x
      rfl
    rw [hcast]
    exact ringEquiv_cast_trans_heq hround.symm H.observableEquiv

/-- Dividing a canonical equation composite recovers its tail transport. -/
theorem deconjugateEquationSystemExact_comp
    {U : AtomCarrier.{u}}
    (e t : Equiv U.Atom U.Atom)
    (A : ArchitectureObject U)
    (C : Site.ContextPreorderCategory A)
    (E : ArchitecturalEquationSystem C)
    {B : ArchitectureObject U}
    {D : Site.ContextPreorderCategory B}
    {G : ArchitecturalEquationSystem D}
    (objectMap : ArchitectureObject U → ArchitectureObject U)
    (K : EquationSystemExactTransport
      (transportEquationSystem e A C E) G t objectMap) :
    HEq
      (deconjugateEquationSystemExact e t A C E
        (objectMap ∘ transportArchitectureObject e)
        ((transportEquationSystemExact e A C E).comp K)) K := by
  apply equationSystemExactTransport_hext rfl
  · funext X
    exact congrArg objectMap (transportArchitectureObject_symm_equiv e X)
  · exact transportContextEquivalence_symm_trans_trans e A C
      K.contextEquivalence
  · apply Equiv.ext
    intro i
    rfl
  · apply Function.hfunext rfl
    intro W W' hW
    cases hW
    have hround := transportContextFunctorInverse_obj_eq e A C W
    change HEq
      ((transportObservableEquiv e A C E
          ((transportContextInverse e A C).obj W)).trans
        (K.observableEquiv
          ((transportContextFunctor e A C).obj
            ((transportContextInverse e A C).obj W))))
      (K.observableEquiv W)
    have hcast :
        transportObservableEquiv e A C E
            ((transportContextInverse e A C).obj W) =
          RingEquiv.cast
            (R := fun X : Site.ContextCategoryObject
              (transportContextPreorder e A C) =>
                (transportEquationSystem e A C E).Observable X)
            hround.symm := by
      apply RingEquiv.ext
      intro x
      rfl
    rw [hcast]
    exact ringEquiv_cast_trans_heq hround.symm K.observableEquiv

/-- Reindex the target equation reading of an exact transport. -/
private def castTargetEquationSystemExact {U : AtomCarrier.{u}}
    {A₀ A A' : ArchitectureObject U}
    {C₀ : Site.ContextPreorderCategory A₀}
    {E₀ : ArchitecturalEquationSystem C₀}
    (S : EquationReading A)
    (h : A = A') (e : Equiv U.Atom U.Atom)
    (objectMap : ArchitectureObject U → ArchitectureObject U)
    (T : EquationSystemExactTransport E₀ S.equationSystem
      e objectMap) :
    EquationSystemExactTransport E₀
      (castEquationReading h S).equationSystem e objectMap := by
  cases h
  exact T

/-- Target and source reindexing cancel around equation-transport composition. -/
private theorem castTarget_comp_castSource
    {U : AtomCarrier.{u}}
    {A₀ A A' B : ArchitectureObject U}
    {C₀ : Site.ContextPreorderCategory A₀}
    {E₀ : ArchitecturalEquationSystem C₀}
    {D : Site.ContextPreorderCategory B}
    {G : ArchitecturalEquationSystem D}
    (S : EquationReading A) (h : A = A')
    (e t : Equiv U.Atom U.Atom)
    (objectMap₁ objectMap₂ : ArchitectureObject U → ArchitectureObject U)
    (T : EquationSystemExactTransport E₀ S.equationSystem e objectMap₁)
    (K : EquationSystemExactTransport S.equationSystem G t objectMap₂) :
    HEq
      ((castTargetEquationSystemExact
          S h e objectMap₁ T).comp
        (castSourceEquationSystemExact h S t objectMap₂ K))
      (T.comp K) := by
  cases h
  rfl

/-- Reindexing a divided canonical composite recovers an arbitrary casted tail. -/
private theorem castSource_deconjugate_castTarget_comp
    {U : AtomCarrier.{u}}
    (e t : Equiv U.Atom U.Atom)
    (A : ArchitectureObject U)
    (R : EquationReading A)
    {A' B : ArchitectureObject U}
    (h : transportArchitectureObject e A = A')
    {D : Site.ContextPreorderCategory B}
    {G : ArchitecturalEquationSystem D}
    (objectMap : ArchitectureObject U → ArchitectureObject U)
    (K : EquationSystemExactTransport
      (castEquationReading h (transportEquationReading e A R)).equationSystem
      G t objectMap) :
    HEq
      (castSourceEquationSystemExact h
        (transportEquationReading e A R) t
        (fun X => (objectMap ∘ transportArchitectureObject e)
          (transportArchitectureObject e.symm X))
        (deconjugateEquationSystemExact e t A R.contextPreorder
          R.equationSystem
          (objectMap ∘ transportArchitectureObject e)
          ((castTargetEquationSystemExact
            (transportEquationReading e A R) h e
            (transportArchitectureObject e)
            (transportEquationSystemExact e A R.contextPreorder
              R.equationSystem)).comp K))) K := by
  cases h
  exact deconjugateEquationSystemExact_comp e t A R.contextPreorder
    R.equationSystem objectMap K

/-- Core-level canonical equation transport cancels its divided tail. -/
theorem transportCoreEquationSystemExact_comp_reverse
    {U : AtomCarrier.{u}}
    {E : ExtractionDoctrine U} (R : CoreReading U)
    (f : ExactDoctrineHom R.doctrine E)
    (t : Equiv U.Atom U.Atom)
    {B : ArchitectureObject U}
    {D : Site.ContextPreorderCategory B}
    {G : ArchitecturalEquationSystem D}
    (objectMap : ArchitectureObject U → ArchitectureObject U)
    (H : EquationSystemExactTransport R.equationReading.equationSystem G
      (f.atomEquiv.trans t) objectMap) :
    HEq
      ((transportCoreEquationSystemExact R f).comp
        (transportCoreEquationSystemExactReverse R f t objectMap H)) H := by
  let A₀ := R.objectReading.object
    (R.composition.compose (R.doctrine.atomize R.source)
      R.family_listFinite)
  let S := transportEquationReading f.atomEquiv A₀ R.equationReading
  let hbase := (transportedBaseObject_eq R f).symm
  let T := transportEquationSystemExact f.atomEquiv A₀
    R.equationReading.contextPreorder R.equationReading.equationSystem
  let K := deconjugateEquationSystemExact f.atomEquiv t A₀
    R.equationReading.contextPreorder R.equationReading.equationSystem
    objectMap H
  change HEq
    ((castTargetEquationSystemExact S hbase f.atomEquiv
        (transportArchitectureObject f.atomEquiv) T).comp
      (castSourceEquationSystemExact hbase S t
        (fun X => objectMap
          (transportArchitectureObject f.atomEquiv.symm X)) K)) H
  exact HEq.trans
    (castTarget_comp_castSource S hbase f.atomEquiv t
      (transportArchitectureObject f.atomEquiv)
      (fun X => objectMap
        (transportArchitectureObject f.atomEquiv.symm X)) T K)
    (transportEquationSystemExact_comp_deconjugate f.atomEquiv t A₀
      R.equationReading.contextPreorder R.equationReading.equationSystem
      objectMap H)

/-- Core-level equation deconjugation is a retraction on arbitrary tails. -/
theorem transportCoreEquationSystemExact_reverse_comp
    {U : AtomCarrier.{u}}
    {E : ExtractionDoctrine U} (R : CoreReading U)
    (f : ExactDoctrineHom R.doctrine E)
    (t : Equiv U.Atom U.Atom)
    {B : ArchitectureObject U}
    {D : Site.ContextPreorderCategory B}
    {G : ArchitecturalEquationSystem D}
    (objectMap : ArchitectureObject U → ArchitectureObject U)
    (K : EquationSystemExactTransport
      (transportCoreReading R f).equationReading.equationSystem
      G t objectMap) :
    HEq
      (transportCoreEquationSystemExactReverse R f t
        (objectMap ∘ transportArchitectureObject f.atomEquiv)
        ((transportCoreEquationSystemExact R f).comp K)) K := by
  let A₀ := R.objectReading.object
    (R.composition.compose (R.doctrine.atomize R.source)
      R.family_listFinite)
  let S := transportEquationReading f.atomEquiv A₀ R.equationReading
  let hbase := (transportedBaseObject_eq R f).symm
  let T := transportEquationSystemExact f.atomEquiv A₀
    R.equationReading.contextPreorder R.equationReading.equationSystem
  change HEq
    (castSourceEquationSystemExact hbase S t
      (fun X => (objectMap ∘ transportArchitectureObject f.atomEquiv)
        (transportArchitectureObject f.atomEquiv.symm X))
      (deconjugateEquationSystemExact f.atomEquiv t A₀
        R.equationReading.contextPreorder
        R.equationReading.equationSystem
        (objectMap ∘ transportArchitectureObject f.atomEquiv)
        ((castTargetEquationSystemExact S hbase f.atomEquiv
          (transportArchitectureObject f.atomEquiv) T).comp K))) K
  exact castSource_deconjugate_castTarget_comp f.atomEquiv t A₀
    R.equationReading hbase objectMap K

/--
Divide a complete upper hom by canonical transport.

The tail Atom equivalence is supplied explicitly and must compose with the
canonical equivalence to the given upper equivalence.  All other tail fields
are computed from the given hom at inverse-transported inputs.
-/
noncomputable def deconjugateTransportUpper {U : AtomCarrier.{u}}
    (P R : AATCorePackage U)
    {E : ExtractionDoctrine U}
    (f : ExactDoctrineHom P.reading.doctrine E)
    (t : Equiv U.Atom U.Atom)
    (h : SignedExactCoreReadingHom P R)
    (hatom : h.atomEquiv = f.atomEquiv.trans t) :
    SignedExactCoreReadingHom (transportAlong P f) R where
  atomEquiv := t
  extraction_eq := by
    rw [h.extraction_eq, transportAlong_family_eq,
      atomFamily_transport_comp]
    apply congrArg (fun atomMap => P.family.transport atomMap)
    funext atom
    have hatomApply := congrArg (fun e : Equiv U.Atom U.Atom => e atom) hatom
    exact hatomApply
  composition_eq F hF := by
    have hcomp := h.composition_eq
      (F.transport f.atomEquiv.symm)
      (hF.transport f.atomEquiv.symm)
    have hleft :
        (f.atomEquiv.trans t : U.Atom → U.Atom) ∘
            (f.atomEquiv.symm : U.Atom → U.Atom) = t := by
      funext atom
      simp
    rw [hatom] at hcomp
    let sourceInput : {G : AtomFamily U // G.ListFinite} :=
      ⟨(F.transport f.atomEquiv.symm).transport (f.atomEquiv.trans t),
        (hF.transport f.atomEquiv.symm).transport (f.atomEquiv.trans t)⟩
    let targetInput : {G : AtomFamily U // G.ListFinite} :=
      ⟨F.transport t, hF.transport t⟩
    have hinput : sourceInput = targetInput := by
      apply Subtype.ext
      dsimp only [sourceInput, targetInput]
      rw [atomFamily_transport_comp, hleft]
    have hcomposeInput := congrArg
      (fun input : {G : AtomFamily U // G.ListFinite} =>
        R.reading.composition.compose input.1 input.2) hinput
    have hright :
        (t : U.Atom → U.Atom) ∘
            (f.atomEquiv : U.Atom → U.Atom) =
          (f.atomEquiv.trans t : U.Atom → U.Atom) := by
      rfl
    calc
      R.reading.composition.compose (F.transport t) (hF.transport t) =
          R.reading.composition.compose sourceInput.1 sourceInput.2 := by
            exact hcomposeInput.symm
      _ = (P.reading.composition.compose
            (F.transport f.atomEquiv.symm)
            (hF.transport f.atomEquiv.symm)).transport
              (f.atomEquiv.trans t) := hcomp
      _ = ((P.reading.composition.compose
              (F.transport f.atomEquiv.symm)
              (hF.transport f.atomEquiv.symm)).transport
                f.atomEquiv).transport t := by
            rw [atomConfiguration_transport_comp, hright]
      _ = ((transportAlong P f).reading.composition.compose F hF).transport t :=
        rfl
  objectMap A :=
    h.objectMap (transportArchitectureObject f.atomEquiv.symm A)
  object_formation_eq C := by
    have hobject := h.object_formation_eq
      (C.transport f.atomEquiv.symm)
    rw [hatom, atomConfiguration_transport_comp] at hobject
    have hleft :
        (f.atomEquiv.trans t : U.Atom → U.Atom) ∘
            (f.atomEquiv.symm : U.Atom → U.Atom) = t := by
      funext atom
      simp
    rw [hleft] at hobject
    change
      h.objectMap
          (transportArchitectureObject f.atomEquiv.symm
            (transportArchitectureObject f.atomEquiv
              (P.reading.objectReading.object
                (C.transport f.atomEquiv.symm)))) =
        R.reading.objectReading.object (C.transport t)
    rw [transportArchitectureObject_equiv_symm]
    exact hobject
  configurationMap A :=
    ConfigurationHom.comp
      (h.configurationMap
        (transportArchitectureObject f.atomEquiv.symm A))
      (AtomConfiguration.transportHom f.atomEquiv.symm A.configuration)
  configurationMap_atomMap A := by
    simp only [ConfigurationHom.comp,
      AtomConfiguration.transportHom_atomMap,
      h.configurationMap_atomMap, hatom]
    funext atom
    simp
  configuration_eq A := by
    rw [h.configuration_eq]
    rw [hatom]
    change
      (A.configuration.transport f.atomEquiv.symm).transport
          (f.atomEquiv.trans t) =
        A.configuration.transport t
    rw [atomConfiguration_transport_comp]
    apply congrArg (fun atomMap => A.configuration.transport atomMap)
    funext atom
    simp
  equationTransport :=
    transportCoreEquationSystemExactReverse P.reading f t h.objectMap
      (castAtomEquationSystemExact hatom h.equationTransport)
  detectorCode_eq i := by
    apply transportCoreEquationSystemExactReverse_detectorCode
      P.reading f t h.objectMap
      (castAtomEquationSystemExact hatom h.equationTransport)
      R.algebra.circuits.code
    intro j
    exact castAtomEquationSystemExact_detectorCode hatom
      h.equationTransport P.algebra.circuits.code
      R.algebra.circuits.code h.detectorCode_eq j
  operationMap op := h.operationMap op
  operation_naturality op := by
    apply ConfigurationHom.ext
    have hnaturality := congrArg ConfigurationHom.atomMap
      (h.operation_naturality op)
    simp only [ConfigurationHom.comp] at hnaturality ⊢
    rw [h.configurationMap_atomMap,
      h.configurationMap_atomMap] at hnaturality
    simp only [transportAlong, transportCoreReading,
      transportOperationReading,
      castConfigurationHom_atomMap,
      transportConfigurationHom_atomMap,
      h.configurationMap_atomMap,
      AtomConfiguration.transportHom_atomMap,
      hatom]
    funext atom
    have hatomNaturality := congrFun hnaturality (f.atomEquiv.symm atom)
    simpa only [Function.comp_apply, hatom, Equiv.trans_apply,
      Equiv.apply_symm_apply] using hatomNaturality
  invariantMap := h.invariantMap
  invariant_transport i := by
    exact invariant_transport_deconjugate f.atomEquiv
      (P.reading.invariantReading.invariant i)
      (R.reading.invariantReading.invariant (h.invariantMap i))
      h.objectMap (h.invariant_transport i)
  axisMap := h.axisMap
  coordinateEquiv i := h.coordinateEquiv i
  axis_selected_iff i := h.axis_selected_iff i
  coordinate_eq A i := by
    simpa only [transportAlong, transportCoreReading,
      transportArchitectureSignature] using
      h.coordinate_eq (transportArchitectureObject f.atomEquiv.symm A) i

/-- Mapping an operation reindexed along equal endpoints changes no operation data. -/
private theorem operationMap_castOperation_heq
    {U : AtomCarrier.{u}}
    (P R : AATCorePackage U)
    (h : SignedExactCoreReadingHom P R)
    {A A' B B' : ArchitectureObject U}
    (hA : A = A') (hB : B = B')
    (op : P.reading.operationReading.Op A B) :
    HEq
      (h.operationMap
        (castOperation P.reading.operationReading hA hB op))
      (h.operationMap op) := by
  cases hA
  cases hB
  rfl

/-- Mapping a canonically transported operation recovers the original mapped operation. -/
private theorem operationMap_transportOperation_heq
    {U : AtomCarrier.{u}}
    (P R : AATCorePackage U)
    (e : Equiv U.Atom U.Atom)
    (h : SignedExactCoreReadingHom P R)
    {A B : ArchitectureObject U}
    (op : P.reading.operationReading.Op A B) :
    HEq
      (h.operationMap
        (transportOperation e P.reading.operationReading op))
      (h.operationMap op) := by
  unfold transportOperation
  exact operationMap_castOperation_heq P R h
    (transportArchitectureObject_equiv_symm e A).symm
    (transportArchitectureObject_equiv_symm e B).symm op

/-- Reindexing the endpoints of an underlying conjugated operation is a no-op. -/
private theorem tailOperationMap_cast_heq
    {U : AtomCarrier.{u}}
    (P R : AATCorePackage U)
    {E : ExtractionDoctrine U}
    (f : ExactDoctrineHom P.reading.doctrine E)
    (k : SignedExactCoreReadingHom (transportAlong P f) R)
    {A A' B B' : ArchitectureObject U}
    (hA : A' = A) (hB : B' = B)
    (op : (transportAlong P f).reading.operationReading.Op A B) :
    HEq
      (k.operationMap
        (castOperation P.reading.operationReading
          (congrArg (transportArchitectureObject f.atomEquiv.symm) hA.symm)
          (congrArg (transportArchitectureObject f.atomEquiv.symm) hB.symm)
          op))
      (k.operationMap op) := by
  cases hA
  cases hB
  rfl

/-- Canonical transport of an already conjugated operation is a tail-map no-op. -/
private theorem tailOperationMap_transportOperation_heq
    {U : AtomCarrier.{u}}
    (P R : AATCorePackage U)
    {E : ExtractionDoctrine U}
    (f : ExactDoctrineHom P.reading.doctrine E)
    (k : SignedExactCoreReadingHom (transportAlong P f) R)
    {A B : ArchitectureObject U}
    (op : (transportAlong P f).reading.operationReading.Op A B) :
    HEq
      (k.operationMap
        (transportOperation f.atomEquiv P.reading.operationReading op))
      (k.operationMap op) := by
  unfold transportOperation
  exact tailOperationMap_cast_heq P R f k
    (transportArchitectureObject_symm_equiv f.atomEquiv A)
    (transportArchitectureObject_symm_equiv f.atomEquiv B) op

/-- Canonical upper transport followed by its deconjugated tail is the given hom. -/
theorem transportAlongUpper_comp_deconjugate {U : AtomCarrier.{u}}
    (P R : AATCorePackage U)
    {E : ExtractionDoctrine U}
    (f : ExactDoctrineHom P.reading.doctrine E)
    (t : Equiv U.Atom U.Atom)
    (h : SignedExactCoreReadingHom P R)
    (hatom : h.atomEquiv = f.atomEquiv.trans t) :
    (transportAlongUpper P f).comp
        (deconjugateTransportUpper P R f t h hatom) = h := by
  apply SignedExactCoreReadingHom.ext
  · exact hatom.symm
  · funext A
    exact congrArg h.objectMap
      (transportArchitectureObject_equiv_symm f.atomEquiv A)
  · exact HEq.trans
      (transportCoreEquationSystemExact_comp_reverse P.reading f t h.objectMap
        (castAtomEquationSystemExact hatom h.equationTransport))
      (castAtomEquationSystemExact_heq hatom h.equationTransport)
  · apply Function.hfunext rfl
    intro A A' hA
    cases hA
    apply Function.hfunext rfl
    intro B B' hB
    cases hB
    apply Function.hfunext rfl
    intro op op' hop
    cases hop
    exact operationMap_transportOperation_heq P R f.atomEquiv h op
  · apply heq_of_eq
    funext i
    rfl
  · apply heq_of_eq
    funext i
    rfl
  · apply Function.hfunext rfl
    intro i i' hi
    cases hi
    apply heq_of_eq
    apply Equiv.ext
    intro x
    rfl

/-- Deconjugating a canonical composite recovers its arbitrary upper tail. -/
theorem deconjugateTransportUpper_comp {U : AtomCarrier.{u}}
    (P R : AATCorePackage U)
    {E : ExtractionDoctrine U}
    (f : ExactDoctrineHom P.reading.doctrine E)
    (k : SignedExactCoreReadingHom (transportAlong P f) R) :
    deconjugateTransportUpper P R f k.atomEquiv
        ((transportAlongUpper P f).comp k) rfl = k := by
  apply SignedExactCoreReadingHom.ext
  · rfl
  · funext A
    exact congrArg k.objectMap
      (transportArchitectureObject_symm_equiv f.atomEquiv A)
  · exact transportCoreEquationSystemExact_reverse_comp P.reading f
      k.atomEquiv k.objectMap k.equationTransport
  · apply Function.hfunext rfl
    intro A A' hA
    cases hA
    apply Function.hfunext rfl
    intro B B' hB
    cases hB
    apply Function.hfunext rfl
    intro op op' hop
    cases hop
    exact tailOperationMap_transportOperation_heq P R f k op
  · apply heq_of_eq
    funext i
    rfl
  · apply heq_of_eq
    funext i
    rfl
  · apply Function.hfunext rfl
    intro i i' hi
    cases hi
    apply heq_of_eq
    apply Equiv.ext
    intro x
    rfl

/-- The residual Atom equivalence after removing a canonical prefix. -/
def canonicalTailAtomEquiv {U : AtomCarrier.{u}}
    (P R : AATCorePackage U)
    {E : ExtractionDoctrine U}
    (f : ExactDoctrineHom P.reading.doctrine E)
    (h : SignedExactCoreReadingHom P R) : Equiv U.Atom U.Atom :=
  f.atomEquiv.symm.trans h.atomEquiv

/-- The canonical prefix and residual Atom equivalence recover the given map. -/
theorem canonicalTailAtomEquiv_factor {U : AtomCarrier.{u}}
    (P R : AATCorePackage U)
    {E : ExtractionDoctrine U}
    (f : ExactDoctrineHom P.reading.doctrine E)
    (h : SignedExactCoreReadingHom P R) :
    h.atomEquiv = f.atomEquiv.trans (canonicalTailAtomEquiv P R f h) := by
  apply Equiv.ext
  intro atom
  simp [canonicalTailAtomEquiv]

/-- Deconjugation with the uniquely determined residual Atom equivalence. -/
noncomputable def canonicalDeconjugateTransportUpper {U : AtomCarrier.{u}}
    (P R : AATCorePackage U)
    {E : ExtractionDoctrine U}
    (f : ExactDoctrineHom P.reading.doctrine E)
    (h : SignedExactCoreReadingHom P R) :
    SignedExactCoreReadingHom (transportAlong P f) R :=
  deconjugateTransportUpper P R f (canonicalTailAtomEquiv P R f h) h
    (canonicalTailAtomEquiv_factor P R f h)

/-- Deconjugation is independent of rewriting an equal residual equivalence. -/
private theorem deconjugateTransportUpper_tail_eq {U : AtomCarrier.{u}}
    (P R : AATCorePackage U)
    {E : ExtractionDoctrine U}
    (f : ExactDoctrineHom P.reading.doctrine E)
    {t t' : Equiv U.Atom U.Atom}
    (ht : t = t')
    (h : SignedExactCoreReadingHom P R)
    (hatom : h.atomEquiv = f.atomEquiv.trans t)
    (hatom' : h.atomEquiv = f.atomEquiv.trans t') :
    deconjugateTransportUpper P R f t h hatom =
      deconjugateTransportUpper P R f t' h hatom' := by
  cases ht
  rfl

/-- Canonical deconjugation is a left inverse to canonical upper composition. -/
theorem canonicalDeconjugateTransportUpper_comp {U : AtomCarrier.{u}}
    (P R : AATCorePackage U)
    {E : ExtractionDoctrine U}
    (f : ExactDoctrineHom P.reading.doctrine E)
    (k : SignedExactCoreReadingHom (transportAlong P f) R) :
    canonicalDeconjugateTransportUpper P R f
        ((transportAlongUpper P f).comp k) = k := by
  have htail :
      canonicalTailAtomEquiv P R f ((transportAlongUpper P f).comp k) =
        k.atomEquiv := by
    apply Equiv.ext
    intro atom
    simp [canonicalTailAtomEquiv, SignedExactCoreReadingHom.comp,
      transportAlongUpper]
  unfold canonicalDeconjugateTransportUpper
  exact (deconjugateTransportUpper_tail_eq P R f htail
    ((transportAlongUpper P f).comp k)
    (canonicalTailAtomEquiv_factor P R f
      ((transportAlongUpper P f).comp k)) rfl).trans
    (deconjugateTransportUpper_comp P R f k)

/-- Precomposition by canonical upper transport is injective. -/
theorem transportAlongUpper_comp_injective {U : AtomCarrier.{u}}
    (P R : AATCorePackage U)
    {E : ExtractionDoctrine U}
    (f : ExactDoctrineHom P.reading.doctrine E) :
    Function.Injective
      (fun k : SignedExactCoreReadingHom (transportAlong P f) R =>
        (transportAlongUpper P f).comp k) :=
  Function.LeftInverse.injective
    (fun k => canonicalDeconjugateTransportUpper_comp P R f k)

/-- The deconjugated tail is the unique upper factor of a given canonical composite. -/
theorem deconjugateTransportUpper_unique {U : AtomCarrier.{u}}
    (P R : AATCorePackage U)
    {E : ExtractionDoctrine U}
    (f : ExactDoctrineHom P.reading.doctrine E)
    (t : Equiv U.Atom U.Atom)
    (h : SignedExactCoreReadingHom P R)
    (hatom : h.atomEquiv = f.atomEquiv.trans t)
    (k : SignedExactCoreReadingHom (transportAlong P f) R)
    (hfactor : (transportAlongUpper P f).comp k = h) :
    k = deconjugateTransportUpper P R f t h hatom := by
  apply transportAlongUpper_comp_injective P R f
  change (transportAlongUpper P f).comp k =
    (transportAlongUpper P f).comp
      (deconjugateTransportUpper P R f t h hatom)
  rw [hfactor, transportAlongUpper_comp_deconjugate P R f t h hatom]

end AAT.AG.AtomFoundation

#assert_standard_axioms_only AAT.AG.AtomFoundation
