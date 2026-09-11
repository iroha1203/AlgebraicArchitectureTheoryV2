import ResearchLean.AG.FiniteDecoderRepresentability.FiniteCodeNormalization
import Formal.Util.AssertStandardAxioms

/-!
# Semantic invariance of finite code normalization

This module completes G-121(D)'s normalization comparison.  The normalized and
original finite codes decode to isomorphic pointed doctrines through maps whose
source map and Atom equivalence are both identities.  These components are
natural in every finite-code morphism and assemble into
`D₀⁰ ∘ R_fin ≅ D₀`.

## Implementation notes

The code structures are not claimed equal: their authored defaults can differ.
Only their decoded extraction predicates agree, by Cycle 13's evaluation
theorem.  Naturality compares the actual decoded source-map and Atom-equivalence
components; it does not accept a commutative square as additional data.
-/

namespace AAT.AG.FiniteDecoderRepresentability

universe u

open CategoryTheory AtomFoundation DoctrineFiberProduct

variable {U : AtomCarrier.{u}}

/--
G-121(D) semantic evaluation bridge: normalized and original pointed codes have
the same extraction proposition at every source and Atom.  This is the public
decoded API used by both directions of the component isomorphism.
-/
theorem normalizeFiniteInstanceCode_toSemantic_extracts_iff
    [DecidableEq U.Atom] [Finite U.Atom] (code : FiniteInstanceCode U)
    (source : code.doctrine.Source) (atom : U.Atom) :
    (normalizeFiniteInstanceCode code).toSemantic.doctrine.extracts source atom ↔
      code.toSemantic.doctrine.extracts source atom := by
  change (normalizeFiniteDoctrineCode code.doctrine).toDoctrine.extracts
      source atom ↔ code.doctrine.toDoctrine.extracts source atom
  rw [FiniteDoctrineCode.toDoctrine_extracts_iff,
    FiniteDoctrineCode.toDoctrine_extracts_iff]
  simp only [AtomPredicateCode.Holds,
    normalizeFiniteDoctrineCode_normalize,
    normalizeFiniteDoctrineCode_extraction_eval]

/--
G-121(D) forward semantic comparison from the normalized code to the original
code.  Both computational maps are identities; extraction exactness is derived
from preservation of table evaluation. `Finite` and `DecidableEq` come from the
finite normalization and decoder.
-/
noncomputable def normalizedToOriginalHom [DecidableEq U.Atom]
    [Finite U.Atom] (code : FiniteInstanceCode U) :
    (normalizeFiniteInstanceCode code).toSemantic ⟶ code.toSemantic where
  doctrineHom :=
    { sourceMap := id
      atomEquiv := Equiv.refl U.Atom
      normalize_eq := by
        intro source
        rfl
      extraction_iff := by
        intro source atom
        simpa only [id_eq, Equiv.refl_apply] using
          normalizeFiniteInstanceCode_toSemantic_extracts_iff code source atom }
  source_eq := rfl

/--
G-121(D) reverse semantic comparison from the original code to its normalized
code.  It has the same identity computational maps and uses the reverse of the
derived extraction equivalence.
-/
noncomputable def originalToNormalizedHom [DecidableEq U.Atom]
    [Finite U.Atom] (code : FiniteInstanceCode U) :
    code.toSemantic ⟶ (normalizeFiniteInstanceCode code).toSemantic where
  doctrineHom :=
    { sourceMap := id
      atomEquiv := Equiv.refl U.Atom
      normalize_eq := by
        intro source
        rfl
      extraction_iff := by
        intro source atom
        simpa only [id_eq, Equiv.refl_apply] using
          (normalizeFiniteInstanceCode_toSemantic_extracts_iff
            code source atom).symm }
  source_eq := rfl

/-- The forward semantic comparison has identity source map. -/
@[simp]
theorem normalizedToOriginalHom_sourceMap [DecidableEq U.Atom]
    [Finite U.Atom] (code : FiniteInstanceCode U) :
    (normalizedToOriginalHom code).doctrineHom.sourceMap = id :=
  rfl

/-- The forward semantic comparison has identity Atom equivalence. -/
@[simp]
theorem normalizedToOriginalHom_atomEquiv [DecidableEq U.Atom]
    [Finite U.Atom] (code : FiniteInstanceCode U) :
    (normalizedToOriginalHom code).doctrineHom.atomEquiv = Equiv.refl U.Atom :=
  rfl

/-- The reverse semantic comparison has identity source map. -/
@[simp]
theorem originalToNormalizedHom_sourceMap [DecidableEq U.Atom]
    [Finite U.Atom] (code : FiniteInstanceCode U) :
    (originalToNormalizedHom code).doctrineHom.sourceMap = id :=
  rfl

/-- The reverse semantic comparison has identity Atom equivalence. -/
@[simp]
theorem originalToNormalizedHom_atomEquiv [DecidableEq U.Atom]
    [Finite U.Atom] (code : FiniteInstanceCode U) :
    (originalToNormalizedHom code).doctrineHom.atomEquiv = Equiv.refl U.Atom :=
  rfl

/--
G-121(D) semantic component isomorphism.  This is an isomorphism after decoding,
not an equality of the two raw finite instance codes.
-/
noncomputable def finiteNormalizationRealizationIsoApp
    [DecidableEq U.Atom] [Finite U.Atom] (code : FiniteInstanceCode U) :
    (normalizeFiniteInstanceCode code).toSemantic ≅ code.toSemantic where
  hom := normalizedToOriginalHom code
  inv := originalToNormalizedHom code
  hom_inv_id := by
    apply ExtInstHom.ext
    apply ExactDoctrineHom.ext
    · rfl
    · apply Equiv.ext
      intro atom
      rfl
  inv_hom_id := by
    apply ExtInstHom.ext
    apply ExactDoctrineHom.ext
    · rfl
    · apply Equiv.ext
      intro atom
      rfl

/-- The semantic normalization isomorphism's forward source map is identity. -/
@[simp]
theorem finiteNormalizationRealizationIsoApp_hom_sourceMap
    [DecidableEq U.Atom] [Finite U.Atom] (code : FiniteInstanceCode U) :
    (finiteNormalizationRealizationIsoApp code).hom.doctrineHom.sourceMap = id :=
  normalizedToOriginalHom_sourceMap code

/-- The semantic normalization isomorphism's forward Atom equivalence is identity. -/
@[simp]
theorem finiteNormalizationRealizationIsoApp_hom_atomEquiv
    [DecidableEq U.Atom] [Finite U.Atom] (code : FiniteInstanceCode U) :
    (finiteNormalizationRealizationIsoApp code).hom.doctrineHom.atomEquiv =
      Equiv.refl U.Atom :=
  normalizedToOriginalHom_atomEquiv code

/--
G-121(D) naturality of the identity-component semantic comparison for an
arbitrary finite-code quotient morphism.  The equality is derived from its
representatives and the retained source-map and Atom-table computations.
-/
theorem finiteNormalizationRealizationIso_naturality
    [DecidableEq U.Atom] [Finite U.Atom]
    {source target : FiniteCodeCartCategory U} (hom : source ⟶ target) :
    (finiteCodeNormalizationFunctor ⋙
        falseDefaultFiniteCodeRealization).map hom ≫
        (finiteNormalizationRealizationIsoApp target).hom =
      (finiteNormalizationRealizationIsoApp source).hom ≫
        finiteCodeCartRealization.map hom := by
  refine Quotient.inductionOn hom ?_
  intro presentation
  apply ExtInstHom.ext
  apply ExactDoctrineHom.ext
  · rfl
  · apply Equiv.ext
    intro atom
    rfl

/--
G-121(D)'s natural isomorphism `D₀⁰ ∘ R_fin ≅ D₀`.  Its components
have identity source map and identity Atom equivalence, while raw code equality
is deliberately not asserted.
-/
noncomputable def finiteNormalizationRealizationIso [DecidableEq U.Atom]
    [Finite U.Atom] :
    finiteCodeNormalizationFunctor (U := U) ⋙
        falseDefaultFiniteCodeRealization (U := U) ≅
      finiteCodeCartRealization (U := U) :=
  NatIso.ofComponents
    (fun code => finiteNormalizationRealizationIsoApp (U := U) code)
    (fun hom => finiteNormalizationRealizationIso_naturality (U := U) hom)

#assert_standard_axioms_only AAT.AG.FiniteDecoderRepresentability

end AAT.AG.FiniteDecoderRepresentability
