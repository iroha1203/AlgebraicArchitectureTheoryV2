import ResearchLean.AG.DoctrineFiberProduct.FiniteGeneratedLiftNaturality

/-!
# Realization-compatible universe lifting for finite-model presentations

The finite code rebase produces a genuine high-universe `RealizableHom`, while
the generated strong-lift reflection uses the semantic arrow obtained by
lifting the low extraction instances directly.  Their finite source carriers
are canonically isomorphic, but not definitionally equal.  This module builds
that missing decoder-level arrow-category isomorphism from the presentation
alone.

No package, strong lift, nonexistence proof, or endpoint isomorphism is supplied
by the caller.  This decoder-level isomorphism remains a helper for the
right-branch named-package transport and its positive reflection fixture.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation

/-- Executable Atom equality on the universe-zero finite carrier. -/
local instance finiteModelRealizationULiftAtomDecidableEq :
    DecidableEq FiniteModel.carrier.Atom := by
  change DecidableEq FiniteModel.FiniteAtom
  infer_instance

/-! ## Direct semantic lifting -/

/-- Lift every endpoint and the lower arrow of a finite-model semantic input. -/
def finiteModelLiftSemanticInput
    (input : CartSemanticInput FiniteModel.carrier) :
    CartSemanticInput finiteModelLiftCarrier.{u} where
  source := finiteModelLiftExtractionInstance.{u} input.source
  target := finiteModelLiftExtractionInstance.{u} input.target
  hom := finiteModelLiftExtInstHom.{u} input.hom

/-- The direct semantic lift uses the pointwise lifted lower arrow. -/
@[simp]
theorem finiteModelLiftSemanticInput_hom
    (input : CartSemanticInput FiniteModel.carrier) :
    (finiteModelLiftSemanticInput.{u} input).hom =
      finiteModelLiftExtInstHom.{u} input.hom :=
  rfl

/-! ## Decoder-object isomorphisms -/

/--
Flatten the nested lifted finite source in a directly lifted decoder doctrine
to the first-order finite source used by the rebased decoder.
-/
def finiteModelLiftDecodedDoctrineHom
    (code : FiniteDoctrineCode FiniteModel.carrier) :
    ExactDoctrineHom
      (finiteModelLiftExtractionDoctrine.{u} code.toDoctrine)
      ((code.rebase finiteModelLiftCarrierEquiv.{u}).toDoctrine) where
  sourceMap source :=
    finiteSourceRebaseEquiv.{0, u} code.sourceCard source.down
  atomEquiv := Equiv.refl _
  normalize_eq source := by
    rcases source with ⟨source⟩
    rfl
  extraction_iff source atom := by
    rcases source with ⟨source⟩
    rcases atom with ⟨atom⟩
    change
      code.toDoctrine.extracts source atom ↔
        (code.rebase finiteModelLiftCarrierEquiv.{u}).toDoctrine.extracts
          (finiteSourceRebaseEquiv.{0, u} code.sourceCard source)
          (finiteModelLiftCarrierEquiv.{u}.atom atom)
    exact (FiniteDoctrineCode.toDoctrine_extracts_rebase_iff
      finiteModelLiftCarrierEquiv.{u} code source atom).symm

/--
Unflatten a rebased first-order finite source into the nested source carrier of
the directly lifted decoder doctrine.
-/
def finiteModelLiftDecodedDoctrineInv
    (code : FiniteDoctrineCode FiniteModel.carrier) :
    ExactDoctrineHom
      ((code.rebase finiteModelLiftCarrierEquiv.{u}).toDoctrine)
      (finiteModelLiftExtractionDoctrine.{u} code.toDoctrine) where
  sourceMap source :=
    ULift.up ((finiteSourceRebaseEquiv.{0, u} code.sourceCard).symm source)
  atomEquiv := Equiv.refl _
  normalize_eq source := by
    rcases source with ⟨source⟩
    rfl
  extraction_iff source atom := by
    rcases source with ⟨source⟩
    rcases atom with ⟨atom⟩
    change
      (code.rebase finiteModelLiftCarrierEquiv.{u}).toDoctrine.extracts
          (finiteSourceRebaseEquiv.{0, u} code.sourceCard (ULift.up source))
          (finiteModelLiftCarrierEquiv.{u}.atom atom) ↔
        code.toDoctrine.extracts (ULift.up source) atom
    exact FiniteDoctrineCode.toDoctrine_extracts_rebase_iff
      finiteModelLiftCarrierEquiv.{u} code (ULift.up source) atom

/-- The two decoder doctrines are canonically isomorphic on the finite image. -/
def finiteModelLiftDecodedDoctrineIso
    (code : FiniteDoctrineCode FiniteModel.carrier) :
    finiteModelLiftExtractionDoctrine.{u} code.toDoctrine ≅
      (code.rebase finiteModelLiftCarrierEquiv.{u}).toDoctrine where
  hom := finiteModelLiftDecodedDoctrineHom.{u} code
  inv := finiteModelLiftDecodedDoctrineInv.{u} code
  hom_inv_id := by
    apply ExactDoctrineHom.ext
    · funext source
      rcases source with ⟨source⟩
      rfl
    · rfl
  inv_hom_id := by
    apply ExactDoctrineHom.ext
    · funext source
      rcases source with ⟨source⟩
      rfl
    · rfl

/-- The forward doctrine isomorphism has the canonical finite-source graph. -/
@[simp]
theorem finiteModelLiftDecodedDoctrineIso_hom_sourceMap
    (code : FiniteDoctrineCode FiniteModel.carrier)
    (source : code.toDoctrine.Source) :
    (finiteModelLiftDecodedDoctrineIso.{u} code).hom.sourceMap
        (ULift.up source) =
      finiteSourceRebaseEquiv.{0, u} code.sourceCard source :=
  rfl

/-- The inverse doctrine isomorphism unflattens every rebased finite source. -/
@[simp]
theorem finiteModelLiftDecodedDoctrineIso_inv_sourceMap
    (code : FiniteDoctrineCode FiniteModel.carrier)
    (source : (code.rebase finiteModelLiftCarrierEquiv.{u}).toDoctrine.Source) :
    (finiteModelLiftDecodedDoctrineIso.{u} code).inv.sourceMap source =
      ULift.up ((finiteSourceRebaseEquiv.{0, u} code.sourceCard).symm source) :=
  rfl

/-- The forward doctrine isomorphism is the identity on lifted Atoms. -/
@[simp]
theorem finiteModelLiftDecodedDoctrineIso_hom_atomEquiv
    (code : FiniteDoctrineCode FiniteModel.carrier) :
    (finiteModelLiftDecodedDoctrineIso.{u} code).hom.atomEquiv = Equiv.refl _ :=
  rfl

/-- Lift the decoder-doctrine isomorphism to the selected finite point. -/
def finiteModelLiftDecodedInstanceIso
    (code : FiniteInstanceCode FiniteModel.carrier) :
    finiteModelLiftExtractionInstance.{u} code.toSemantic ≅
      (code.rebase finiteModelLiftCarrierEquiv.{u}).toSemantic where
  hom :=
    { doctrineHom := finiteModelLiftDecodedDoctrineIso.{u} code.doctrine |>.hom
      source_eq := by rfl }
  inv :=
    { doctrineHom := finiteModelLiftDecodedDoctrineIso.{u} code.doctrine |>.inv
      source_eq := by rfl }
  hom_inv_id := by
    apply ExtInstHom.ext
    exact (finiteModelLiftDecodedDoctrineIso.{u} code.doctrine).hom_inv_id
  inv_hom_id := by
    apply ExtInstHom.ext
    exact (finiteModelLiftDecodedDoctrineIso.{u} code.doctrine).inv_hom_id

/-- The pointed forward isomorphism retains the finite-source graph. -/
@[simp]
theorem finiteModelLiftDecodedInstanceIso_hom_sourceMap
    (code : FiniteInstanceCode FiniteModel.carrier)
    (source : code.doctrine.toDoctrine.Source) :
    (finiteModelLiftDecodedInstanceIso.{u} code).hom.doctrineHom.sourceMap
        (ULift.up source) =
      finiteSourceRebaseEquiv.{0, u} code.doctrine.sourceCard source :=
  rfl

/-! ## Arrow-category realization bridge -/

/--
The directly lifted decoder arrow and the decoder of the rebased presentation
are isomorphic as semantic bottom-arrow inputs.
-/
def finiteModelLiftPresentationSemanticIso
    (presentation : CartPresentation FiniteModel.carrier) :
    CartSemanticInputIso
      (finiteModelLiftSemanticInput.{u} (toSemanticCart presentation))
      (toSemanticCart (finiteModelLiftCartPresentation.{u} presentation)) where
  sourceIso :=
    finiteModelLiftDecodedInstanceIso.{u} presentation.1.source
  targetIso :=
    finiteModelLiftDecodedInstanceIso.{u} presentation.1.target
  hom_comm := by
    apply ExtInstHom.ext
    apply ExactDoctrineHom.ext
    · funext source
      rcases source with ⟨source⟩
      rfl
    · apply Equiv.ext
      intro atom
      rcases atom with ⟨atom⟩
      change
        (toSemanticCart
            (finiteModelLiftCartPresentation.{u} presentation)).hom.doctrineHom.atomEquiv
            (finiteModelLiftCarrierEquiv.{u}.atom atom) =
          (finiteModelLiftExtInstHom.{u}
            (toSemanticCart presentation).hom).doctrineHom.atomEquiv
            (finiteModelLiftCarrierEquiv.{u}.atom atom)
      unfold finiteModelLiftCartPresentation
      rw [toSemanticCart_rebase_atomEquiv]
      exact (finiteModelLiftExtInstHom_atomEquiv
        (toSemanticCart presentation).hom atom).symm

/-- The bridge's source component is generated from the presentation source code. -/
@[simp]
theorem finiteModelLiftPresentationSemanticIso_sourceIso
    (presentation : CartPresentation FiniteModel.carrier) :
    (finiteModelLiftPresentationSemanticIso.{u} presentation).sourceIso =
      finiteModelLiftDecodedInstanceIso.{u} presentation.1.source :=
  rfl

/-- The bridge's target component is generated from the presentation target code. -/
@[simp]
theorem finiteModelLiftPresentationSemanticIso_targetIso
    (presentation : CartPresentation FiniteModel.carrier) :
    (finiteModelLiftPresentationSemanticIso.{u} presentation).targetIso =
      finiteModelLiftDecodedInstanceIso.{u} presentation.1.target :=
  rfl

/-- The generated endpoint isomorphisms make the lifted lower square commute. -/
theorem finiteModelLiftPresentationSemanticIso_hom_comm
    (presentation : CartPresentation FiniteModel.carrier) :
    (finiteModelLiftPresentationSemanticIso.{u} presentation).sourceIso.hom ≫
        (toSemanticCart
          (finiteModelLiftCartPresentation.{u} presentation)).hom =
      (finiteModelLiftSemanticInput.{u}
          (toSemanticCart presentation)).hom ≫
        (finiteModelLiftPresentationSemanticIso.{u}
          presentation).targetIso.hom :=
  (finiteModelLiftPresentationSemanticIso.{u} presentation).hom_comm

/-- Canonically lift a realized finite-model arrow by rebasing its presentation. -/
def finiteModelLiftRealizableHom
    (input : RealizableHom FiniteModel.carrier) :
    RealizableHom finiteModelLiftCarrier.{u} :=
  realizableHomOf (finiteModelLiftCartPresentation.{u} input.presentation)

/-- The lifted realized arrow retains exactly the rebased finite presentation. -/
@[simp]
theorem finiteModelLiftRealizableHom_presentation
    (input : RealizableHom FiniteModel.carrier) :
    (finiteModelLiftRealizableHom.{u} input).presentation =
      finiteModelLiftCartPresentation.{u} input.presentation :=
  rfl

/--
Every realized finite-model arrow has the generated semantic-input isomorphism
between the direct semantic lift and its rebased realization.
-/
def finiteModelLiftRealizableHomSemanticIso
    (input : RealizableHom FiniteModel.carrier) :
    CartSemanticInputIso
      (finiteModelLiftSemanticInput.{u} input.semantic)
      (finiteModelLiftRealizableHom.{u} input).semantic := by
  rcases input with ⟨semantic, presentation, realization_eq⟩
  cases realization_eq
  exact finiteModelLiftPresentationSemanticIso.{u} presentation

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
