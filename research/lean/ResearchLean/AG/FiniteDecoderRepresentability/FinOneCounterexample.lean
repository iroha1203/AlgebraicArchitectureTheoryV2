import ResearchLean.AG.FiniteDecoderRepresentability.FiniteNormalizationRealizationIso
import Formal.Util.AssertStandardAxioms

/-!
# The finite raw-code counterexample

This module completes G-121(D) with the specified one-Atom example.  Two raw
codes evaluate identically but carry opposite authored defaults.  Their decoded
semantic objects are isomorphic and finite normalization sends the true-default
code to the false-default code, while the original finite-code category has no
morphism in either direction between them.

The local instances below merely expose the reducible `Fin 1` Atom projection
to typeclass search inside this concrete fixture.  The public computation lemmas
record every target-relevant field without requiring clients to unfold the code.
-/

namespace AAT.AG.FiniteDecoderRepresentability

universe u

open CategoryTheory AtomFoundation DoctrineFiberProduct

/-- G-121(D)'s concrete one-Atom carrier, with all coordinate readings identity. -/
def finOneCarrier : AtomCarrier where
  AtomKind := Fin 1
  Axis := Fin 1
  Subject := Fin 1
  Predicate := Fin 1
  Payload := Fin 1
  Atom := Fin 1
  kind := id
  axis := id
  subject := id
  predicate := id
  payload := id

private instance : DecidableEq finOneCarrier.Atom := by
  change DecidableEq (Fin 1)
  infer_instance

private instance : Subsingleton finOneCarrier.Atom := by
  change Subsingleton (Fin 1)
  infer_instance

/-- The unique Atom of the fixed carrier. -/
def finOneAtom : finOneCarrier.Atom :=
  (0 : Fin 1)

/-- The authored table `(true, ∅)` on the one-Atom carrier. -/
def finOneTrueTable : AtomPredicateCode finOneCarrier where
  defaultValue := true
  exceptions := ∅

/-- The authored table `(false, {0})` on the one-Atom carrier. -/
def finOneFalseTable : AtomPredicateCode finOneCarrier where
  defaultValue := false
  exceptions := {finOneAtom}

/-- The true-default table evaluates to true at the unique Atom. -/
@[simp]
theorem finOneTrueTable_eval (atom : finOneCarrier.Atom) :
    finOneTrueTable.eval atom = true := by
  simp [finOneTrueTable, AtomPredicateCode.eval]

/-- The false-default exceptional table also evaluates to true at the unique Atom. -/
@[simp]
theorem finOneFalseTable_eval (atom : finOneCarrier.Atom) :
    finOneFalseTable.eval atom = true := by
  have hatom : atom = finOneAtom := Subsingleton.elim _ _
  subst atom
  simp [finOneFalseTable, AtomPredicateCode.eval]

/-- The two raw tables have identical evaluations on every Atom. -/
theorem finOneTable_evaluation_eq :
    atomPredicateCodeEvaluationEq finOneTrueTable finOneFalseTable := by
  intro atom
  rw [finOneTrueTable_eval, finOneFalseTable_eval]

/-- G-121(D)'s true-default singleton-source code `P_t`. -/
def finOneTrueCode : FiniteInstanceCode finOneCarrier where
  doctrine :=
    { sourceCard := 1
      normalize := id
      extraction := fun _ => finOneTrueTable }
  point := ULift.up 0

/-- G-121(D)'s false-default singleton-source code `P_f`. -/
def finOneFalseCode : FiniteInstanceCode finOneCarrier where
  doctrine :=
    { sourceCard := 1
      normalize := id
      extraction := fun _ => finOneFalseTable }
  point := ULift.up 0

/-- G-121(D) computation API: `simp` exposes the first code's source cardinality as one. -/
@[simp] theorem finOneTrueCode_sourceCard :
    finOneTrueCode.doctrine.sourceCard = 1 := rfl

/-- G-121(D) computation API: `simp` exposes the second code's source cardinality as one. -/
@[simp] theorem finOneFalseCode_sourceCard :
    finOneFalseCode.doctrine.sourceCard = 1 := rfl

/-- G-121(D) computation API: `simp` removes the first code's source normalization. -/
@[simp] theorem finOneTrueCode_normalize
    (source : finOneTrueCode.doctrine.Source) :
    finOneTrueCode.doctrine.normalize source = source := rfl

/-- G-121(D) computation API: `simp` removes the second code's source normalization. -/
@[simp] theorem finOneFalseCode_normalize
    (source : finOneFalseCode.doctrine.Source) :
    finOneFalseCode.doctrine.normalize source = source := rfl

/-- G-121(D) computation API: `simp` exposes every first-code table as `(true, ∅)`. -/
@[simp] theorem finOneTrueCode_extraction
    (source : finOneTrueCode.doctrine.Source) :
    finOneTrueCode.doctrine.extraction source = finOneTrueTable := rfl

/-- G-121(D) computation API: `simp` exposes every second-code table as `(false, {0})`. -/
@[simp] theorem finOneFalseCode_extraction
    (source : finOneFalseCode.doctrine.Source) :
    finOneFalseCode.doctrine.extraction source = finOneFalseTable := rfl

/-- G-121(D) computation API: `simp` exposes the first code's unique selected point. -/
@[simp] theorem finOneTrueCode_point :
    finOneTrueCode.point = ULift.up (0 : Fin 1) := rfl

/-- G-121(D) computation API: `simp` exposes the second code's unique selected point. -/
@[simp] theorem finOneFalseCode_point :
    finOneFalseCode.point = ULift.up (0 : Fin 1) := rfl

/-- Every normalized extraction of `P_t` has authored default true. -/
@[simp]
theorem finOneTrueCode_normalized_defaultValue
    (source : finOneTrueCode.doctrine.Source) :
    (normalizedExtractionCode finOneTrueCode source).defaultValue = true :=
  by simp [normalizedExtractionCode, finOneTrueCode, finOneTrueTable]

/-- Every normalized extraction of `P_f` has authored default false. -/
@[simp]
theorem finOneFalseCode_normalized_defaultValue
    (source : finOneFalseCode.doctrine.Source) :
    (normalizedExtractionCode finOneFalseCode source).defaultValue = false :=
  by simp [normalizedExtractionCode, finOneFalseCode, finOneFalseTable]

/-- The decoded extraction predicates of `P_t` and `P_f` agree everywhere. -/
theorem finOneCode_extracts_iff (source : finOneTrueCode.doctrine.Source)
    (atom : finOneCarrier.Atom) :
    finOneTrueCode.toSemantic.doctrine.extracts source atom ↔
      finOneFalseCode.toSemantic.doctrine.extracts source atom := by
  simp [FiniteInstanceCode.toSemantic, finOneTrueCode, finOneFalseCode,
    FiniteDoctrineCode.toDoctrine_extracts_iff, AtomPredicateCode.Holds]

/--
The identity source map and identity Atom equivalence give the forward semantic
arrow between the two equal-evaluation decodings.
-/
def finOneTrueToFalseSemanticHom :
    finOneTrueCode.toSemantic ⟶ finOneFalseCode.toSemantic where
  doctrineHom :=
    { sourceMap := id
      atomEquiv := Equiv.refl finOneCarrier.Atom
      normalize_eq := by intro; rfl
      extraction_iff := by
        intro source atom
        simpa only [id_eq, Equiv.refl_apply] using
          finOneCode_extracts_iff source atom }
  source_eq := rfl

/-- The reverse semantic arrow has the same identity computational components. -/
def finOneFalseToTrueSemanticHom :
    finOneFalseCode.toSemantic ⟶ finOneTrueCode.toSemantic where
  doctrineHom :=
    { sourceMap := id
      atomEquiv := Equiv.refl finOneCarrier.Atom
      normalize_eq := by intro; rfl
      extraction_iff := by
        intro source atom
        simpa only [id_eq, Equiv.refl_apply] using
          (finOneCode_extracts_iff source atom).symm }
  source_eq := rfl

/-- The two decoded semantic objects are isomorphic by identity components. -/
def finOneTrueFalseSemanticIso :
    finOneTrueCode.toSemantic ≅ finOneFalseCode.toSemantic where
  hom := finOneTrueToFalseSemanticHom
  inv := finOneFalseToTrueSemanticHom
  hom_inv_id := by
    apply ExtInstHom.ext
    apply ExactDoctrineHom.ext
    · rfl
    · apply Equiv.ext; intro; rfl
  inv_hom_id := by
    apply ExtInstHom.ext
    apply ExactDoctrineHom.ext
    · rfl
    · apply Equiv.ext; intro; rfl

/-- G-121(D) computation API: `simp` exposes the semantic isomorphism's forward source map as identity. -/
@[simp] theorem finOneTrueFalseSemanticIso_hom_sourceMap :
    finOneTrueFalseSemanticIso.hom.doctrineHom.sourceMap = id := rfl

/-- G-121(D) computation API: `simp` exposes the semantic isomorphism's forward Atom equivalence as identity. -/
@[simp] theorem finOneTrueFalseSemanticIso_hom_atomEquiv :
    finOneTrueFalseSemanticIso.hom.doctrineHom.atomEquiv =
      Equiv.refl finOneCarrier.Atom := rfl

/-- G-121(D) computation API: `simp` exposes the semantic isomorphism's inverse source map as identity. -/
@[simp] theorem finOneTrueFalseSemanticIso_inv_sourceMap :
    finOneTrueFalseSemanticIso.inv.doctrineHom.sourceMap = id := rfl

/-- G-121(D) computation API: `simp` exposes the semantic isomorphism's inverse Atom equivalence as identity. -/
@[simp] theorem finOneTrueFalseSemanticIso_inv_atomEquiv :
    finOneTrueFalseSemanticIso.inv.doctrineHom.atomEquiv =
      Equiv.refl finOneCarrier.Atom := rfl

/-- Normalizing the true table gives the explicit false-default exceptional table. -/
theorem normalize_finOneTrueTable_eq :
    normalizeAtomPredicateCode finOneTrueTable = finOneFalseTable := by
  apply atomPredicateCode_eq_of_defaultValue_eq_of_eval_eq
  · rfl
  · intro atom
    rw [normalizeAtomPredicateCode_eval, finOneTrueTable_eval,
      finOneFalseTable_eval]

/-- The underlying normalized raw code of `P_t` is exactly `P_f`. -/
theorem normalize_finOneTrueCode_eq :
    normalizeFiniteInstanceCode finOneTrueCode = finOneFalseCode := by
  unfold normalizeFiniteInstanceCode normalizeFiniteDoctrineCode
  unfold finOneTrueCode finOneFalseCode
  congr
  funext source
  exact normalize_finOneTrueTable_eq

/-- There is no original finite-code morphism from `P_t` to `P_f`. -/
theorem not_nonempty_finOneTrueToFalseCodeHom :
    ¬ Nonempty (FiniteCodeCartHom finOneTrueCode finOneFalseCode) := by
  rintro ⟨hom⟩
  refine Quotient.inductionOn hom ?_
  intro presentation
  have hdefault := (fixedPresentation_necessary
    (typedPresentationToSemantic presentation) presentation rfl).2
      (ULift.up (0 : Fin 1))
  simp only [finOneFalseCode_normalized_defaultValue,
    finOneTrueCode_normalized_defaultValue] at hdefault
  exact Bool.noConfusion hdefault

/-- There is no original finite-code morphism from `P_f` to `P_t`. -/
theorem not_nonempty_finOneFalseToTrueCodeHom :
    ¬ Nonempty (FiniteCodeCartHom finOneFalseCode finOneTrueCode) := by
  rintro ⟨hom⟩
  refine Quotient.inductionOn hom ?_
  intro presentation
  have hdefault := (fixedPresentation_necessary
    (typedPresentationToSemantic presentation) presentation rfl).2
      (ULift.up (0 : Fin 1))
  simp only [finOneTrueCode_normalized_defaultValue,
    finOneFalseCode_normalized_defaultValue] at hdefault
  exact Bool.noConfusion hdefault

/-- Consequently the semantic isomorphism cannot be replaced by an isomorphism in `P₀`. -/
theorem not_nonempty_finOneTrueFalseCodeIso :
    ¬ Nonempty
      ((finOneTrueCode : FiniteCodeCartCategory finOneCarrier) ≅
        (finOneFalseCode : FiniteCodeCartCategory finOneCarrier)) := by
  rintro ⟨iso⟩
  exact not_nonempty_finOneTrueToFalseCodeHom ⟨iso.hom⟩

#assert_standard_axioms_only AAT.AG.FiniteDecoderRepresentability

end AAT.AG.FiniteDecoderRepresentability
