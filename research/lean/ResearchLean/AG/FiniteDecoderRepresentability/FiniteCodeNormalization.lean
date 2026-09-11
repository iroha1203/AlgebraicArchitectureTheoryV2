import ResearchLean.AG.FiniteDecoderRepresentability.FiniteFullSubcategory
import Formal.Util.AssertStandardAxioms

/-!
# Finite-carrier code normalization

This module constructs the object and morphism parts of G-121(D)'s finite
normalization functor.  Every authored extraction table is replaced by the
canonical finite table with the same evaluation and default `false`; source
cardinality, normalization, selected point, source maps, and decoded Atom
permutations are retained.

## Implementation notes

The construction changes raw code structure, not semantic evaluation.  On
morphisms it rebuilds the raw extraction equality from equal false defaults and
the original presentation's evaluation equality.  Quotient representative
independence and the functor laws are proved using decoded source-map and Atom
components, never by choosing representatives as extra input.
-/

namespace AAT.AG.FiniteDecoderRepresentability

universe u

open CategoryTheory AtomFoundation DoctrineFiberProduct

variable {U : AtomCarrier.{u}}

/--
G-121(D) table normalization: keep a table's evaluation and choose authored
default `false`.  `Finite` supplies the internal enumeration used by
`finitePredicateCode`; `DecidableEq` is the evaluator requirement.
-/
noncomputable def normalizeAtomPredicateCode [DecidableEq U.Atom]
    [Finite U.Atom] (code : AtomPredicateCode U) : AtomPredicateCode U :=
  finitePredicateCode code.eval false

/--
G-121(D) evaluation API: normalized tables evaluate exactly as the original
authored tables. `Finite` builds the table, `DecidableEq` evaluates it, and the
`simp` direction removes normalization from an evaluation.
-/
@[simp]
theorem normalizeAtomPredicateCode_eval [DecidableEq U.Atom]
    [Finite U.Atom] (code : AtomPredicateCode U) (atom : U.Atom) :
    (normalizeAtomPredicateCode code).eval atom = code.eval atom := by
  simpa only [normalizeAtomPredicateCode] using
    (finitePredicateCode_eval code.eval false atom)

/--
G-121(D) default API: every normalized table has authored default `false`.
The instances have the same provenance as the constructor; the `simp` direction
exposes the chosen false default.
-/
@[simp]
theorem normalizeAtomPredicateCode_defaultValue [DecidableEq U.Atom]
    [Finite U.Atom] (code : AtomPredicateCode U) :
    (normalizeAtomPredicateCode code).defaultValue = false :=
  finitePredicateCode_defaultValue _ _

/--
G-121(D) doctrine-code normalization keeps Source and `normalize` literally and
replaces each extraction table independently by `normalizeAtomPredicateCode`.
-/
noncomputable def normalizeFiniteDoctrineCode [DecidableEq U.Atom]
    [Finite U.Atom] (code : FiniteDoctrineCode U) : FiniteDoctrineCode U where
  sourceCard := code.sourceCard
  normalize := code.normalize
  extraction := fun source => normalizeAtomPredicateCode (code.extraction source)

/--
G-121(D) doctrine computation API: normalization retains `sourceCard`; the
`simp` direction exposes the original finite Source cardinality.
-/
@[simp]
theorem normalizeFiniteDoctrineCode_sourceCard [DecidableEq U.Atom]
    [Finite U.Atom] (code : FiniteDoctrineCode U) :
    (normalizeFiniteDoctrineCode code).sourceCard = code.sourceCard :=
  rfl

/--
G-121(D) doctrine computation API: the normalization table is retained
literally; the `simp` direction exposes the original map.
-/
@[simp]
theorem normalizeFiniteDoctrineCode_normalize [DecidableEq U.Atom]
    [Finite U.Atom] (code : FiniteDoctrineCode U) :
    (normalizeFiniteDoctrineCode code).normalize = code.normalize :=
  rfl

/--
G-121(D) doctrine computation API: each new extraction table is exactly the
canonical normalization of the table at the same position.
-/
@[simp]
theorem normalizeFiniteDoctrineCode_extraction [DecidableEq U.Atom]
    [Finite U.Atom] (code : FiniteDoctrineCode U)
    (source : (normalizeFiniteDoctrineCode code).Source) :
    (normalizeFiniteDoctrineCode code).extraction source =
      normalizeAtomPredicateCode (code.extraction source) :=
  rfl

/--
G-121(D) doctrine default API: every normalized extraction table has default
`false`; the `simp` direction reduces the new table's authored default.
-/
@[simp]
theorem normalizeFiniteDoctrineCode_extraction_defaultValue
    [DecidableEq U.Atom] [Finite U.Atom]
    (code : FiniteDoctrineCode U)
    (source : (normalizeFiniteDoctrineCode code).Source) :
    ((normalizeFiniteDoctrineCode code).extraction source).defaultValue = false :=
  normalizeAtomPredicateCode_defaultValue _

/--
G-121(D) doctrine evaluation API: every normalized extraction table preserves
evaluation; the `simp` direction reduces it to the original table evaluation.
-/
@[simp]
theorem normalizeFiniteDoctrineCode_extraction_eval
    [DecidableEq U.Atom] [Finite U.Atom]
    (code : FiniteDoctrineCode U)
    (source : (normalizeFiniteDoctrineCode code).Source) (atom : U.Atom) :
    ((normalizeFiniteDoctrineCode code).extraction source).eval atom =
      (code.extraction source).eval atom :=
  normalizeAtomPredicateCode_eval _ _

/--
G-121(D) pointed-code normalization retains the source type, normalization,
and selected point while normalizing every authored extraction table.
-/
noncomputable def normalizeFiniteInstanceCode [DecidableEq U.Atom]
    [Finite U.Atom] (code : FiniteInstanceCode U) : FiniteInstanceCode U where
  doctrine := normalizeFiniteDoctrineCode code.doctrine
  point := code.point

/--
G-121(D) pointed-code computation API: the new doctrine is exactly the doctrine
normalization above.  The `simp` direction exposes that construction.
-/
@[simp]
theorem normalizeFiniteInstanceCode_doctrine [DecidableEq U.Atom]
    [Finite U.Atom] (code : FiniteInstanceCode U) :
    (normalizeFiniteInstanceCode code).doctrine =
      normalizeFiniteDoctrineCode code.doctrine :=
  rfl

/--
G-121(D) pointed-code computation API: source cardinality, hence the dependent
Source type, is retained.  The `simp` direction exposes the original cardinality.
-/
@[simp]
theorem normalizeFiniteInstanceCode_sourceCard [DecidableEq U.Atom]
    [Finite U.Atom] (code : FiniteInstanceCode U) :
    (normalizeFiniteInstanceCode code).doctrine.sourceCard =
      code.doctrine.sourceCard :=
  rfl

/--
G-121(D) pointed-code computation API: the source normalization map is retained;
the `simp` direction exposes the original normalization.
-/
@[simp]
theorem normalizeFiniteInstanceCode_normalize [DecidableEq U.Atom]
    [Finite U.Atom] (code : FiniteInstanceCode U) :
    (normalizeFiniteInstanceCode code).doctrine.normalize =
      code.doctrine.normalize :=
  rfl

/--
G-121(D) pointed-code API: the selected source point is retained literally;
the `simp` direction exposes the original point.
-/
@[simp]
theorem normalizeFiniteInstanceCode_point [DecidableEq U.Atom]
    [Finite U.Atom] (code : FiniteInstanceCode U) :
    (normalizeFiniteInstanceCode code).point = code.point :=
  rfl

/-- The normalized pointed code satisfies the exact `P₀⁰` object condition. -/
theorem normalizeFiniteInstanceCode_falseDefault [DecidableEq U.Atom]
    [Finite U.Atom] (code : FiniteInstanceCode U) :
    falseDefaultFiniteCodeProperty (normalizeFiniteInstanceCode code) := by
  intro input
  exact normalizeAtomPredicateCode_defaultValue _

/--
G-121(D) presentation normalization keeps the source map and finite Atom table,
while rebuilding extraction equality between the normalized endpoint codes.
-/
noncomputable def normalizeCartPresentation [DecidableEq U.Atom]
    [Finite U.Atom] {source target : FiniteInstanceCode U}
    (presentation : CartPresentationBetween source target) :
    CartPresentationBetween (normalizeFiniteInstanceCode source)
      (normalizeFiniteInstanceCode target) where
  sourceMap := presentation.sourceMap
  atomEquiv := presentation.atomEquiv
  normalize_eq := presentation.normalize_eq
  extraction_eq := by
    intro input
    apply atomPredicateCode_eq_of_defaultValue_eq_of_eval_eq
    · simp only [normalizeFiniteInstanceCode,
        normalizeFiniteDoctrineCode_extraction_defaultValue,
        atomPredicateCode_transport_defaultValue]
    · intro atom
      have hraw := congrArg (fun code : AtomPredicateCode U => code.eval atom)
        (presentation.extraction_eq input)
      change
        (target.doctrine.extraction
          (target.doctrine.normalize (presentation.sourceMap input))).eval atom =
        ((source.doctrine.extraction
          (source.doctrine.normalize input)).transport
            presentation.atomEquiv.toEquiv).eval atom at hraw
      simp only [normalizeFiniteInstanceCode_doctrine,
        normalizeFiniteDoctrineCode_extraction,
        normalizeAtomPredicateCode_eval]
      conv_rhs at hraw =>
        rw [← presentation.atomEquiv.toEquiv.apply_symm_apply atom]
      rw [AtomPredicateCode.eval_transport] at hraw
      conv_rhs =>
        rw [← presentation.atomEquiv.toEquiv.apply_symm_apply atom]
      rw [AtomPredicateCode.eval_transport, normalizeAtomPredicateCode_eval]
      exact hraw
  source_eq := presentation.source_eq

/--
G-121(D) presentation API: normalization retains the authored source map;
the `simp` direction exposes the original field.
-/
@[simp]
theorem normalizeCartPresentation_sourceMap [DecidableEq U.Atom]
    [Finite U.Atom] {source target : FiniteInstanceCode U}
    (presentation : CartPresentationBetween source target) :
    (normalizeCartPresentation presentation).sourceMap = presentation.sourceMap :=
  rfl

/--
G-121(D) presentation API: normalization retains the authored finite Atom table;
the `simp` direction exposes the original field and hence its decoded permutation.
-/
@[simp]
theorem normalizeCartPresentation_atomEquiv [DecidableEq U.Atom]
    [Finite U.Atom] {source target : FiniteInstanceCode U}
    (presentation : CartPresentationBetween source target) :
    (normalizeCartPresentation presentation).atomEquiv = presentation.atomEquiv :=
  rfl

/--
Decoded equality of presentations is preserved by normalization, establishing
representative independence for the quotient morphism action.
-/
theorem normalizeCartPresentation_rel
    [DecidableEq U.Atom] [Finite U.Atom]
    {source target : FiniteInstanceCode U}
    {first second : CartPresentationBetween source target}
    (hrel : (cartPresentationSetoid source target).r first second) :
    (cartPresentationSetoid (normalizeFiniteInstanceCode source)
      (normalizeFiniteInstanceCode target)).r
        (normalizeCartPresentation first) (normalizeCartPresentation second) := by
  apply ExtInstHom.ext
  apply ExactDoctrineHom.ext
  · simpa only [typedPresentationToSemantic_sourceMap,
      normalizeCartPresentation_sourceMap] using congrArg
      (fun hom => hom.doctrineHom.sourceMap) hrel
  · simpa only [typedPresentationToSemantic_atomEquiv,
      normalizeCartPresentation_atomEquiv] using congrArg
      (fun hom => hom.doctrineHom.atomEquiv) hrel

/--
G-121(D) quotient action: normalize a morphism independently of its chosen
representative. `Finite` and `DecidableEq` are inherited from table normalization.
-/
noncomputable def normalizeFiniteCodeCartHom [DecidableEq U.Atom]
    [Finite U.Atom] {source target : FiniteInstanceCode U}
    (hom : FiniteCodeCartHom source target) :
    FiniteCodeCartHom (normalizeFiniteInstanceCode source)
      (normalizeFiniteInstanceCode target) :=
  Quotient.map normalizeCartPresentation
    (fun _ _ hrel => normalizeCartPresentation_rel hrel) hom

/--
G-121(D) quotient computation API: an inserted presentation maps to its
normalized presentation; the `simp` direction exposes that representative.
-/
@[simp]
theorem normalizeFiniteCodeCartHom_ofPresentation [DecidableEq U.Atom]
    [Finite U.Atom] {source target : FiniteInstanceCode U}
    (presentation : CartPresentationBetween source target) :
    normalizeFiniteCodeCartHom
        (FiniteCodeCartHom.ofPresentation presentation) =
      FiniteCodeCartHom.ofPresentation (normalizeCartPresentation presentation) :=
  rfl

/--
G-121(D)'s finite normalization functor `R_fin : P₀ ⟶ P₀⁰`.
Object membership, representative independence, identities, and composition
are all constructed rather than accepted as fields from callers.
-/
noncomputable def finiteCodeNormalizationFunctor [DecidableEq U.Atom]
    [Finite U.Atom] :
    FiniteCodeCartCategory U ⥤ FalseDefaultFiniteCodeCategory U where
  obj code := ⟨normalizeFiniteInstanceCode code,
    normalizeFiniteInstanceCode_falseDefault code⟩
  map hom := ObjectProperty.homMk (normalizeFiniteCodeCartHom hom)
  map_id code := by
    apply ObjectProperty.hom_ext
    apply Quotient.sound
    apply ExtInstHom.ext
    apply ExactDoctrineHom.ext
    · change (normalizeCartPresentation
        (idTypedPresentation code)).sourceMap = id
      rw [normalizeCartPresentation_sourceMap]
      rfl
    · change (normalizeCartPresentation
        (idTypedPresentation code)).atomEquiv.toEquiv = Equiv.refl U.Atom
      rw [normalizeCartPresentation_atomEquiv]
      exact AtomPermutationCode.toEquiv_refl
  map_comp first second := by
    refine Quotient.inductionOn₂ first second ?_
    intro firstPresentation secondPresentation
    apply ObjectProperty.hom_ext
    apply Quotient.sound
    apply ExtInstHom.ext
    apply ExactDoctrineHom.ext
    · change (normalizeCartPresentation
        (compPresentation firstPresentation secondPresentation)).sourceMap =
        (compPresentation (normalizeCartPresentation firstPresentation)
          (normalizeCartPresentation secondPresentation)).sourceMap
      rw [normalizeCartPresentation_sourceMap]
      rfl
    · change (normalizeCartPresentation
        (compPresentation firstPresentation secondPresentation)).atomEquiv.toEquiv =
        (compPresentation (normalizeCartPresentation firstPresentation)
          (normalizeCartPresentation secondPresentation)).atomEquiv.toEquiv
      rw [normalizeCartPresentation_atomEquiv]
      rfl

/--
G-121(D) functor object API: forgetting membership exposes exactly the normalized
pointed code.  The `simp` direction removes the full-subcategory wrapper.
-/
@[simp]
theorem finiteCodeNormalizationFunctor_obj_obj [DecidableEq U.Atom]
    [Finite U.Atom] (code : FiniteCodeCartCategory U) :
    (finiteCodeNormalizationFunctor.obj code).obj =
      normalizeFiniteInstanceCode code :=
  rfl

/--
G-121(D) functor morphism API: forgetting membership exposes the
representative-independent quotient normalization.  The `simp` direction
removes the full-subcategory wrapper.
-/
@[simp]
theorem finiteCodeNormalizationFunctor_map_hom [DecidableEq U.Atom]
    [Finite U.Atom] {source target : FiniteCodeCartCategory U}
    (hom : source ⟶ target) :
    (finiteCodeNormalizationFunctor.map hom).hom =
      normalizeFiniteCodeCartHom hom :=
  rfl

#assert_standard_axioms_only AAT.AG.FiniteDecoderRepresentability

end AAT.AG.FiniteDecoderRepresentability
