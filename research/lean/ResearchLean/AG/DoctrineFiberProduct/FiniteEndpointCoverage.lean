import ResearchLean.AG.DoctrineFiberProduct.ExactBottomCoverageSchema

/-!
# Finite-endpoint exact-bottom coverage

This module discharges G-112 K0.  A finite Atom carrier and finite source types
allow every semantic endpoint doctrine to be tabulated by a finite code.  The
semantic arrow is then conjugated across the two canonical endpoint codes,
yielding one typed presentation and an arrow-category isomorphism over the
same endpoint anchors.
-/

namespace AAT.AG.DoctrineFiberProduct

open CategoryTheory
open AtomFoundation

universe u

/-- The canonical first-order finite enumeration of a finite type. -/
noncomputable def finiteSourceEquiv (α : Type u) [Finite α] :
    FiniteSource.{u} (Nat.card α) ≃ α :=
  Equiv.ulift.trans (Finite.equivFin α).symm

/-- Encode an arbitrary predicate on a finite Atom carrier by its true table. -/
noncomputable def finiteAtomPredicateCode {U : AtomCarrier.{u}}
    [Finite U.Atom] [DecidableEq U.Atom] (predicate : U.Atom → Prop) :
    AtomPredicateCode U := by
  classical
  letI := Fintype.ofFinite U.Atom
  exact
    { defaultValue := false
      exceptions := Finset.univ.filter predicate }

@[simp]
theorem finiteAtomPredicateCode_holds_iff {U : AtomCarrier.{u}}
    [Finite U.Atom] [DecidableEq U.Atom] (predicate : U.Atom → Prop)
    (atom : U.Atom) :
    (finiteAtomPredicateCode predicate).Holds atom ↔ predicate atom := by
  classical
  simp [finiteAtomPredicateCode, AtomPredicateCode.Holds,
    AtomPredicateCode.eval]

/-- The four semantic admission fields evaluated at an already-normalized source. -/
def normalizedExtractionPredicate {U : AtomCarrier.{u}}
    (doctrine : ExtractionDoctrine U) (source : doctrine.Source)
    (atom : U.Atom) : Prop :=
  doctrine.vocabularyAllows doctrine.vocabulary atom ∧
    doctrine.semanticAllows doctrine.semanticReading source atom ∧
    doctrine.resolutionAllows doctrine.resolution source atom ∧
    doctrine.sourceSemantics source atom

@[simp]
theorem normalizedExtractionPredicate_normalize_iff
    {U : AtomCarrier.{u}} (doctrine : ExtractionDoctrine U)
    (source : doctrine.Source) (atom : U.Atom) :
    normalizedExtractionPredicate doctrine (doctrine.normalize source) atom ↔
      doctrine.extracts source atom :=
  Iff.rfl

/-- Canonically tabulate a finite-source doctrine on a finite Atom carrier. -/
noncomputable def finiteDoctrineCodeOf {U : AtomCarrier.{u}}
    [Finite U.Atom] [DecidableEq U.Atom]
    (doctrine : ExtractionDoctrine U) [Finite doctrine.Source] :
    FiniteDoctrineCode U where
  sourceCard := Nat.card doctrine.Source
  normalize := fun source =>
    (finiteSourceEquiv doctrine.Source).symm
      (doctrine.normalize (finiteSourceEquiv doctrine.Source source))
  extraction := fun source =>
    finiteAtomPredicateCode
      (normalizedExtractionPredicate doctrine
        (finiteSourceEquiv doctrine.Source source))

@[simp]
theorem finiteDoctrineCodeOf_normalize {U : AtomCarrier.{u}}
    [Finite U.Atom] [DecidableEq U.Atom]
    (doctrine : ExtractionDoctrine U) [Finite doctrine.Source]
    (source : (finiteDoctrineCodeOf doctrine).Source) :
    finiteSourceEquiv doctrine.Source
        ((finiteDoctrineCodeOf doctrine).normalize source) =
      doctrine.normalize (finiteSourceEquiv doctrine.Source source) := by
  simp [finiteDoctrineCodeOf]

@[simp]
theorem finiteDoctrineCodeOf_extracts_iff {U : AtomCarrier.{u}}
    [Finite U.Atom] [DecidableEq U.Atom]
    (doctrine : ExtractionDoctrine U) [Finite doctrine.Source]
    (source : (finiteDoctrineCodeOf doctrine).Source) (atom : U.Atom) :
    (finiteDoctrineCodeOf doctrine).toDoctrine.extracts source atom ↔
      doctrine.extracts (finiteSourceEquiv doctrine.Source source) atom := by
  rw [FiniteDoctrineCode.toDoctrine_extracts_iff]
  simp [finiteDoctrineCodeOf]

/-- The decoded finite doctrine is exactly isomorphic to the semantic doctrine. -/
noncomputable def finiteDoctrineCodeOfIso {U : AtomCarrier.{u}}
    [Finite U.Atom] [DecidableEq U.Atom]
    (doctrine : ExtractionDoctrine U) [Finite doctrine.Source] :
    (finiteDoctrineCodeOf doctrine).toDoctrine ≅ doctrine where
  hom :=
    { sourceMap := finiteSourceEquiv doctrine.Source
      atomEquiv := Equiv.refl U.Atom
      normalize_eq := fun source =>
        (finiteDoctrineCodeOf_normalize doctrine source).symm
      extraction_iff := by
        intro source atom
        simpa using finiteDoctrineCodeOf_extracts_iff doctrine source atom }
  inv :=
    { sourceMap := (finiteSourceEquiv doctrine.Source).symm
      atomEquiv := Equiv.refl U.Atom
      normalize_eq := by
        intro source
        apply (finiteSourceEquiv doctrine.Source).injective
        change
          finiteSourceEquiv doctrine.Source
              ((finiteDoctrineCodeOf doctrine).normalize
                ((finiteSourceEquiv doctrine.Source).symm source)) =
            finiteSourceEquiv doctrine.Source
              ((finiteSourceEquiv doctrine.Source).symm
                (doctrine.normalize source))
        rw [finiteDoctrineCodeOf_normalize]
        simp
      extraction_iff := by
        intro source atom
        symm
        simpa using finiteDoctrineCodeOf_extracts_iff doctrine
          ((finiteSourceEquiv doctrine.Source).symm source) atom }
  hom_inv_id := by
    apply ExactDoctrineHom.ext
    · funext source
      simp
    · ext atom
      rfl
  inv_hom_id := by
    apply ExactDoctrineHom.ext
    · funext source
      simp
    · ext atom
      rfl

/-- Canonical finite code and anchor for a finite-source semantic object. -/
noncomputable def finiteInstanceCodeOf {U : AtomCarrier.{u}}
    [Finite U.Atom] [DecidableEq U.Atom]
    (object : ExtractionInstance U) [Finite object.doctrine.Source] :
    FiniteInstanceCode U where
  doctrine := finiteDoctrineCodeOf object.doctrine
  point := (finiteSourceEquiv object.doctrine.Source).symm object.source

/-- The canonical code decodes to the original pointed object. -/
noncomputable def finiteInstanceCodeOfIso {U : AtomCarrier.{u}}
    [Finite U.Atom] [DecidableEq U.Atom]
    (object : ExtractionInstance U) [Finite object.doctrine.Source] :
    (finiteInstanceCodeOf object).toSemantic ≅ object where
  hom :=
    { doctrineHom := (finiteDoctrineCodeOfIso object.doctrine).hom
      source_eq := by
        change finiteSourceEquiv object.doctrine.Source
            ((finiteSourceEquiv object.doctrine.Source).symm object.source) =
          object.source
        simp }
  inv :=
    { doctrineHom := (finiteDoctrineCodeOfIso object.doctrine).inv
      source_eq := by
        change (finiteSourceEquiv object.doctrine.Source).symm object.source =
          (finiteSourceEquiv object.doctrine.Source).symm object.source
        rfl }
  hom_inv_id := by
    apply ExtInstHom.ext
    exact (finiteDoctrineCodeOfIso object.doctrine).hom_inv_id
  inv_hom_id := by
    apply ExtInstHom.ext
    exact (finiteDoctrineCodeOfIso object.doctrine).inv_hom_id

/-- Every Atom permutation on a finite carrier has a complete finite table. -/
noncomputable def finiteAtomPermutationCodeOf {U : AtomCarrier.{u}}
    [Finite U.Atom] [DecidableEq U.Atom] (equiv : Equiv.Perm U.Atom) :
    AtomPermutationCode U := by
  letI := Fintype.ofFinite U.Atom
  exact AtomPermutationCode.ofPerm Finset.univ equiv (by simp) (by simp)

@[simp]
theorem finiteAtomPermutationCodeOf_toEquiv {U : AtomCarrier.{u}}
    [Finite U.Atom] [DecidableEq U.Atom] (equiv : Equiv.Perm U.Atom) :
    (finiteAtomPermutationCodeOf equiv).toEquiv = equiv := by
  classical
  simp [finiteAtomPermutationCodeOf]

/-- Conjugate a semantic exact-bottom arrow across its canonical finite anchors. -/
noncomputable def finiteCartPresentationBetweenOf {U : AtomCarrier.{u}}
    [Finite U.Atom] [DecidableEq U.Atom]
    (input : CartSemanticInput U)
    [Finite input.source.doctrine.Source]
    [Finite input.target.doctrine.Source] :
    CartPresentationBetween (finiteInstanceCodeOf input.source)
      (finiteInstanceCodeOf input.target) where
  sourceMap := fun source =>
    (finiteSourceEquiv input.target.doctrine.Source).symm
      (input.hom.doctrineHom.sourceMap
        (finiteSourceEquiv input.source.doctrine.Source source))
  atomEquiv := finiteAtomPermutationCodeOf input.hom.doctrineHom.atomEquiv
  normalize_eq := by
    intro source
    apply (finiteSourceEquiv input.target.doctrine.Source).injective
    change
      finiteSourceEquiv input.target.doctrine.Source
          ((finiteDoctrineCodeOf input.target.doctrine).normalize
            ((finiteSourceEquiv input.target.doctrine.Source).symm
              (input.hom.doctrineHom.sourceMap
                (finiteSourceEquiv input.source.doctrine.Source source)))) =
        finiteSourceEquiv input.target.doctrine.Source
          ((finiteSourceEquiv input.target.doctrine.Source).symm
            (input.hom.doctrineHom.sourceMap
              (finiteSourceEquiv input.source.doctrine.Source
                ((finiteDoctrineCodeOf input.source.doctrine).normalize source))))
    rw [finiteDoctrineCodeOf_normalize]
    simp only [Equiv.apply_symm_apply]
    rw [finiteDoctrineCodeOf_normalize]
    exact input.hom.doctrineHom.normalize_eq _
  extraction_eq := by
    intro source
    simp only [finiteInstanceCodeOf]
    unfold finiteDoctrineCodeOf
    simp only
    rw [AtomPredicateCode.mk.injEq]
    refine ⟨rfl, ?_⟩
    ext atom
    simp only [Equiv.apply_symm_apply, finiteAtomPermutationCodeOf_toEquiv]
    simp only [AtomPredicateCode.transport, finiteAtomPredicateCode,
      Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map_equiv]
    change
      input.target.doctrine.extracts
          (input.hom.doctrineHom.sourceMap
            (finiteSourceEquiv input.source.doctrine.Source source)) atom ↔
        input.source.doctrine.extracts
          (finiteSourceEquiv input.source.doctrine.Source source)
          (input.hom.doctrineHom.atomEquiv.symm atom)
    simpa using (input.hom.doctrineHom.extraction_iff
      (finiteSourceEquiv input.source.doctrine.Source source)
      (input.hom.doctrineHom.atomEquiv.symm atom)).symm
  source_eq := by
    apply (finiteSourceEquiv input.target.doctrine.Source).injective
    simp [finiteInstanceCodeOf, input.hom.source_eq]

/-- The conjugated presentation commutes with the canonical endpoint anchors. -/
theorem finiteCartPresentationBetweenOf_hom_comm {U : AtomCarrier.{u}}
    [Finite U.Atom] [DecidableEq U.Atom]
    (input : CartSemanticInput U)
    [Finite input.source.doctrine.Source]
    [Finite input.target.doctrine.Source] :
    (finiteInstanceCodeOfIso input.source).hom ≫ input.hom =
      (toSemanticCart
        (finiteCartPresentationBetweenOf input).toPresentation).hom ≫
          (finiteInstanceCodeOfIso input.target).hom := by
  apply ExtInstHom.ext
  apply ExactDoctrineHom.ext
  · funext source
    change
      input.hom.doctrineHom.sourceMap
          (finiteSourceEquiv input.source.doctrine.Source source) =
        finiteSourceEquiv input.target.doctrine.Source
          ((finiteSourceEquiv input.target.doctrine.Source).symm
            (input.hom.doctrineHom.sourceMap
              (finiteSourceEquiv input.source.doctrine.Source source)))
    simp
  · apply Equiv.ext
    intro atom
    change input.hom.doctrineHom.atomEquiv atom =
      (finiteAtomPermutationCodeOf input.hom.doctrineHom.atomEquiv).toEquiv atom
    rw [finiteAtomPermutationCodeOf_toEquiv]

/-- K0: finite carrier and finite endpoints imply anchored arrow coverage. -/
theorem finiteEndpointCoverage : FiniteEndpointCoverage.{u} := by
  intro U _ _ input _ _
  let sourceAnchor : CoveredObjectWitness input.source :=
    { code := finiteInstanceCodeOf input.source
      iso := finiteInstanceCodeOfIso input.source }
  let targetAnchor : CoveredObjectWitness input.target :=
    { code := finiteInstanceCodeOf input.target
      iso := finiteInstanceCodeOfIso input.target }
  exact ⟨
    { sourceAnchor := sourceAnchor
      targetAnchor := targetAnchor
      arrow :=
        { presentation := finiteCartPresentationBetweenOf input
          square :=
            { sourceIso := sourceAnchor.iso
              targetIso := targetAnchor.iso
              hom_comm := finiteCartPresentationBetweenOf_hom_comm input }
          sourceIso_eq := rfl
          targetIso_eq := rfl } }⟩

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
