import ResearchLean.AG.DoctrineFiberProduct.FiniteEndpointCoverage
import ResearchLean.AG.DoctrineFiberProduct.CartesianTargetWitnesses

/-!
# Exact-bottom coverage classification

This module discharges G-112 K1.  It characterizes semantic exact-bottom
coverage by the pre-registered endpoint-finite / target-extraction condition,
records the refutations of every earlier candidate, and constructs the
carrier-global negative branch.

## Implementation notes

The selected condition is represented by canonical finite/cofinite exception
tables because G-112 fixes semantic set finiteness, while the G-110 decoder
accepts finite tables.  A normalized source outside the image of `normalize`
receives the false table; decoder-facing API lemmas only read actual
normalization outputs, so no idempotence premise is introduced.  Encoding an
arbitrary predicate table or adding a realization witness to the condition was
rejected because either route would enlarge the closed F0 language.

The source endpoint uses the identity Atom equivalence and the target endpoint
uses the input hom's Atom equivalence.  This asymmetric placement makes the
typed presentation's code-level Atom permutation reflexive while the two
endpoint anchors retain the original semantic permutation.  Directly storing
the semantic arrow or its coverage square in a code was rejected as a
certificate-provenance escape.

The per-universe negative fixtures and the two-member qualification family are
the Lean transcription of the raw data fixed in
`research/fixtures/G-112-k1-o6-raw-data.md`.  Their raw structures contain only
carriers, endpoints, and arrows; firing and all negative/nondegeneracy claims
are separate theorem outputs.
-/

namespace AAT.AG.DoctrineFiberProduct

open CategoryTheory
open AtomFoundation

universe u

local instance exactBottomFiniteModelAtomDecidableEq :
    DecidableEq FiniteModel.carrier.Atom := by
  change DecidableEq FiniteModel.FiniteAtom
  infer_instance

/-- Encode a finite or cofinite predicate by its exceptional finite set. -/
noncomputable def finiteOrCofiniteAtomPredicateCode {U : AtomCarrier.{u}}
    [DecidableEq U.Atom] (predicate : U.Atom → Prop)
    (hfinite : Set.Finite {atom | predicate atom} ∨
      Set.Finite {atom | ¬ predicate atom}) : AtomPredicateCode U := by
  classical
  by_cases h : Set.Finite {atom | predicate atom}
  · exact
      { defaultValue := false
        exceptions := h.toFinset }
  · exact
      { defaultValue := true
        exceptions := (hfinite.resolve_left h).toFinset }

/-- The finite/cofinite exception table denotes exactly its input predicate. -/
@[simp]
theorem finiteOrCofiniteAtomPredicateCode_holds_iff
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (predicate : U.Atom → Prop)
    (hfinite : Set.Finite {atom | predicate atom} ∨
      Set.Finite {atom | ¬ predicate atom}) (atom : U.Atom) :
    (finiteOrCofiniteAtomPredicateCode predicate hfinite).Holds atom ↔
      predicate atom := by
  classical
  simp only [finiteOrCofiniteAtomPredicateCode]
  split
  · by_cases hp : predicate atom <;>
      simp [AtomPredicateCode.Holds, AtomPredicateCode.eval, hp]
  · by_cases hp : predicate atom <;>
      simp [AtomPredicateCode.Holds, AtomPredicateCode.eval, hp]

/-- Extensionally equal predicates receive the same canonical exception table. -/
theorem finiteOrCofiniteAtomPredicateCode_congr {U : AtomCarrier.{u}}
    [DecidableEq U.Atom] {first second : U.Atom → Prop}
    (hfirst : Set.Finite {atom | first atom} ∨
      Set.Finite {atom | ¬ first atom})
    (hsecond : Set.Finite {atom | second atom} ∨
      Set.Finite {atom | ¬ second atom})
    (hiff : ∀ atom, first atom ↔ second atom) :
    finiteOrCofiniteAtomPredicateCode first hfirst =
      finiteOrCofiniteAtomPredicateCode second hsecond := by
  classical
  have hset : {atom | first atom} = {atom | second atom} := by
    ext atom
    exact hiff atom
  have hfinite_iff : Set.Finite {atom | first atom} ↔
      Set.Finite {atom | second atom} := by rw [hset]
  unfold finiteOrCofiniteAtomPredicateCode
  split <;> split
  · rename_i hfirstFinite hsecondFinite
    rw [AtomPredicateCode.mk.injEq]
    exact ⟨rfl, by simp [hset]⟩
  · rename_i hfirstFinite hsecondNotFinite
    exact False.elim (hsecondNotFinite (hfinite_iff.mp hfirstFinite))
  · rename_i hfirstNotFinite hsecondFinite
    exact False.elim (hfirstNotFinite (hfinite_iff.mpr hsecondFinite))
  · rw [AtomPredicateCode.mk.injEq]
    refine ⟨rfl, ?_⟩
    have hcset : {atom | ¬ first atom} = {atom | ¬ second atom} := by
      ext atom
      exact not_congr (hiff atom)
    simp [hcset]

/--
At every source that occurs as a normalization output, the raw four-field
admission conjunction is finite or cofinite whenever all semantic extraction
sets are finite or cofinite.
-/
theorem normalizedExtractionPredicate_finiteOrCofinite_of_mem_range
    {U : AtomCarrier.{u}} (doctrine : ExtractionDoctrine U)
    (hall : ∀ source : doctrine.Source,
      (extractedAtomSet ⟨doctrine, source⟩ source).Finite ∨
        (extractedAtomSet ⟨doctrine, source⟩ source)ᶜ.Finite)
    (normalized : doctrine.Source)
    (hrange : ∃ source, doctrine.normalize source = normalized) :
    Set.Finite {atom | normalizedExtractionPredicate doctrine normalized atom} ∨
      Set.Finite {atom | ¬ normalizedExtractionPredicate doctrine normalized atom} := by
  rcases hrange with ⟨source, rfl⟩
  simpa [extractedAtomSet, Set.compl_setOf,
    normalizedExtractionPredicate_normalize_iff] using hall source

/-- A table for the raw admission conjunction, needed only on normalization outputs. -/
noncomputable def finiteCofiniteExtractionCode {U : AtomCarrier.{u}}
    [DecidableEq U.Atom] (doctrine : ExtractionDoctrine U)
    (hall : ∀ source : doctrine.Source,
      (extractedAtomSet ⟨doctrine, source⟩ source).Finite ∨
        (extractedAtomSet ⟨doctrine, source⟩ source)ᶜ.Finite)
    (atomEquiv : Equiv.Perm U.Atom) (source : doctrine.Source) :
    AtomPredicateCode U := by
  classical
  by_cases hrange : ∃ input, doctrine.normalize input = source
  · let predicate : U.Atom → Prop := fun atom =>
      normalizedExtractionPredicate doctrine source (atomEquiv atom)
    have hbase := normalizedExtractionPredicate_finiteOrCofinite_of_mem_range
      doctrine hall source hrange
    have htransport : Set.Finite {atom | predicate atom} ∨
        Set.Finite {atom | ¬ predicate atom} := by
      rcases hbase with hfinite | hcofinite
      · left
        exact hfinite.preimage (Set.injOn_of_injective atomEquiv.injective)
      · right
        exact hcofinite.preimage (Set.injOn_of_injective atomEquiv.injective)
    exact finiteOrCofiniteAtomPredicateCode predicate htransport
  · exact { defaultValue := false, exceptions := ∅ }

/-- On normalization outputs, the encoded raw table is exact. -/
@[simp]
theorem finiteCofiniteExtractionCode_holds_normalize_iff
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (doctrine : ExtractionDoctrine U)
    (hall : ∀ source : doctrine.Source,
      (extractedAtomSet ⟨doctrine, source⟩ source).Finite ∨
        (extractedAtomSet ⟨doctrine, source⟩ source)ᶜ.Finite)
    (atomEquiv : Equiv.Perm U.Atom) (source : doctrine.Source)
    (atom : U.Atom) :
    (finiteCofiniteExtractionCode doctrine hall atomEquiv
      (doctrine.normalize source)).Holds atom ↔
      doctrine.extracts source (atomEquiv atom) := by
  classical
  simp only [finiteCofiniteExtractionCode]
  split
  · exact finiteOrCofiniteAtomPredicateCode_holds_iff
      (fun atom => normalizedExtractionPredicate doctrine
        (doctrine.normalize source) (atomEquiv atom)) _ atom
  · rename_i hnot
    exact False.elim (hnot ⟨source, rfl⟩)

/--
API equality for two finite/cofinite extraction tables on normalization-image
sources.  It lets downstream presentations compare tables through the
underlying semantic predicates without unfolding either table definition.
-/
theorem finiteCofiniteExtractionCode_eq_of_mem_range
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (first second : ExtractionDoctrine U)
    (firstHall : ∀ source : first.Source,
      (extractedAtomSet ⟨first, source⟩ source).Finite ∨
        (extractedAtomSet ⟨first, source⟩ source)ᶜ.Finite)
    (secondHall : ∀ source : second.Source,
      (extractedAtomSet ⟨second, source⟩ source).Finite ∨
        (extractedAtomSet ⟨second, source⟩ source)ᶜ.Finite)
    (firstEquiv secondEquiv : Equiv.Perm U.Atom)
    (firstSource : first.Source) (secondSource : second.Source)
    (firstRange : ∃ source, first.normalize source = firstSource)
    (secondRange : ∃ source, second.normalize source = secondSource)
    (predicates_iff : ∀ atom,
      normalizedExtractionPredicate first firstSource (firstEquiv atom) ↔
        normalizedExtractionPredicate second secondSource (secondEquiv atom)) :
    finiteCofiniteExtractionCode first firstHall firstEquiv firstSource =
      finiteCofiniteExtractionCode second secondHall secondEquiv secondSource := by
  unfold finiteCofiniteExtractionCode
  simp only [firstRange, secondRange]
  apply finiteOrCofiniteAtomPredicateCode_congr
  · rcases normalizedExtractionPredicate_finiteOrCofinite_of_mem_range
      first firstHall firstSource firstRange with hfinite | hcofinite
    · left
      exact hfinite.preimage (Set.injOn_of_injective firstEquiv.injective)
    · right
      exact hcofinite.preimage (Set.injOn_of_injective firstEquiv.injective)
  · rcases normalizedExtractionPredicate_finiteOrCofinite_of_mem_range
      second secondHall secondSource secondRange with hfinite | hcofinite
    · left
      exact hfinite.preimage (Set.injOn_of_injective secondEquiv.injective)
    · right
      exact hcofinite.preimage (Set.injOn_of_injective secondEquiv.injective)
  · exact predicates_iff

/--
Tabulate a finite-source doctrine using an authored Atom equivalence from the
decoded code to the semantic doctrine.
-/
noncomputable def finiteCofiniteDoctrineCodeOf {U : AtomCarrier.{u}}
    [DecidableEq U.Atom] (doctrine : ExtractionDoctrine U)
    [Finite doctrine.Source]
    (hall : ∀ source : doctrine.Source,
      (extractedAtomSet ⟨doctrine, source⟩ source).Finite ∨
        (extractedAtomSet ⟨doctrine, source⟩ source)ᶜ.Finite)
    (atomEquiv : Equiv.Perm U.Atom) : FiniteDoctrineCode U where
  sourceCard := Nat.card doctrine.Source
  normalize := fun source =>
    (finiteSourceEquiv doctrine.Source).symm
      (doctrine.normalize (finiteSourceEquiv doctrine.Source source))
  extraction := fun source =>
    finiteCofiniteExtractionCode doctrine hall atomEquiv
      (finiteSourceEquiv doctrine.Source source)

/-- The source enumeration conjugates normalization for the general code. -/
@[simp]
theorem finiteCofiniteDoctrineCodeOf_normalize {U : AtomCarrier.{u}}
    [DecidableEq U.Atom] (doctrine : ExtractionDoctrine U)
    [Finite doctrine.Source]
    (hall : ∀ source : doctrine.Source,
      (extractedAtomSet ⟨doctrine, source⟩ source).Finite ∨
        (extractedAtomSet ⟨doctrine, source⟩ source)ᶜ.Finite)
    (atomEquiv : Equiv.Perm U.Atom)
    (source : (finiteCofiniteDoctrineCodeOf doctrine hall atomEquiv).Source) :
    finiteSourceEquiv doctrine.Source
        ((finiteCofiniteDoctrineCodeOf doctrine hall atomEquiv).normalize source) =
      doctrine.normalize (finiteSourceEquiv doctrine.Source source) := by
  simp [finiteCofiniteDoctrineCodeOf]

/--
The extraction table of the general doctrine code, exposed as its no-unfold
API for typed presentation proofs.
-/
@[simp]
theorem finiteCofiniteDoctrineCodeOf_extraction {U : AtomCarrier.{u}}
    [DecidableEq U.Atom] (doctrine : ExtractionDoctrine U)
    [Finite doctrine.Source]
    (hall : ∀ source : doctrine.Source,
      (extractedAtomSet ⟨doctrine, source⟩ source).Finite ∨
        (extractedAtomSet ⟨doctrine, source⟩ source)ᶜ.Finite)
    (atomEquiv : Equiv.Perm U.Atom)
    (source : (finiteCofiniteDoctrineCodeOf doctrine hall atomEquiv).Source) :
    (finiteCofiniteDoctrineCodeOf doctrine hall atomEquiv).extraction source =
      finiteCofiniteExtractionCode doctrine hall atomEquiv
        (finiteSourceEquiv doctrine.Source source) :=
  rfl

/-- The general decoder preserves semantic extraction along its Atom equivalence. -/
@[simp]
theorem finiteCofiniteDoctrineCodeOf_extracts_iff {U : AtomCarrier.{u}}
    [DecidableEq U.Atom] (doctrine : ExtractionDoctrine U)
    [Finite doctrine.Source]
    (hall : ∀ source : doctrine.Source,
      (extractedAtomSet ⟨doctrine, source⟩ source).Finite ∨
        (extractedAtomSet ⟨doctrine, source⟩ source)ᶜ.Finite)
    (atomEquiv : Equiv.Perm U.Atom)
    (source : (finiteCofiniteDoctrineCodeOf doctrine hall atomEquiv).Source)
    (atom : U.Atom) :
    (finiteCofiniteDoctrineCodeOf doctrine hall atomEquiv).toDoctrine.extracts
        source atom ↔
      doctrine.extracts (finiteSourceEquiv doctrine.Source source)
        (atomEquiv atom) := by
  rw [FiniteDoctrineCode.toDoctrine_extracts_iff]
  simp [finiteCofiniteDoctrineCodeOf]

/-- The general finite/cofinite code is isomorphic to its semantic doctrine. -/
noncomputable def finiteCofiniteDoctrineCodeOfIso {U : AtomCarrier.{u}}
    [DecidableEq U.Atom] (doctrine : ExtractionDoctrine U)
    [Finite doctrine.Source]
    (hall : ∀ source : doctrine.Source,
      (extractedAtomSet ⟨doctrine, source⟩ source).Finite ∨
        (extractedAtomSet ⟨doctrine, source⟩ source)ᶜ.Finite)
    (atomEquiv : Equiv.Perm U.Atom) :
    (finiteCofiniteDoctrineCodeOf doctrine hall atomEquiv).toDoctrine ≅
      doctrine where
  hom :=
    { sourceMap := finiteSourceEquiv doctrine.Source
      atomEquiv := atomEquiv
      normalize_eq := fun source =>
        (finiteCofiniteDoctrineCodeOf_normalize doctrine hall atomEquiv source).symm
      extraction_iff := finiteCofiniteDoctrineCodeOf_extracts_iff
        doctrine hall atomEquiv }
  inv :=
    { sourceMap := (finiteSourceEquiv doctrine.Source).symm
      atomEquiv := atomEquiv.symm
      normalize_eq := by
        intro source
        apply (finiteSourceEquiv doctrine.Source).injective
        change
          finiteSourceEquiv doctrine.Source
              ((finiteCofiniteDoctrineCodeOf doctrine hall atomEquiv).normalize
                ((finiteSourceEquiv doctrine.Source).symm source)) =
            finiteSourceEquiv doctrine.Source
              ((finiteSourceEquiv doctrine.Source).symm
                (doctrine.normalize source))
        rw [finiteCofiniteDoctrineCodeOf_normalize]
        simp
      extraction_iff := by
        intro source atom
        symm
        simpa only [Equiv.apply_symm_apply, Equiv.symm_apply_apply] using
          finiteCofiniteDoctrineCodeOf_extracts_iff doctrine hall
          atomEquiv ((finiteSourceEquiv doctrine.Source).symm source)
          (atomEquiv.symm atom) }
  hom_inv_id := by
    apply ExactDoctrineHom.ext
    · funext source
      simp
    · ext atom
      simp
  inv_hom_id := by
    apply ExactDoctrineHom.ext
    · funext source
      simp
    · ext atom
      simp

/-- Canonical code for a finite-source object with finite/cofinite extractions. -/
noncomputable def finiteCofiniteInstanceCodeOf {U : AtomCarrier.{u}}
    [DecidableEq U.Atom] (object : ExtractionInstance U)
    [Finite object.doctrine.Source]
    (hall : AllExtractionsFiniteOrCofinite object)
    (atomEquiv : Equiv.Perm U.Atom) : FiniteInstanceCode U where
  doctrine := finiteCofiniteDoctrineCodeOf object.doctrine hall atomEquiv
  point := (finiteSourceEquiv object.doctrine.Source).symm object.source

/-- The canonical object code decodes over the authored Atom equivalence. -/
noncomputable def finiteCofiniteInstanceCodeOfIso {U : AtomCarrier.{u}}
    [DecidableEq U.Atom] (object : ExtractionInstance U)
    [Finite object.doctrine.Source]
    (hall : AllExtractionsFiniteOrCofinite object)
    (atomEquiv : Equiv.Perm U.Atom) :
    (finiteCofiniteInstanceCodeOf object hall atomEquiv).toSemantic ≅ object where
  hom :=
    { doctrineHom := finiteCofiniteDoctrineCodeOfIso object.doctrine hall atomEquiv |>.hom
      source_eq := by
        change finiteSourceEquiv object.doctrine.Source
            ((finiteSourceEquiv object.doctrine.Source).symm object.source) =
          object.source
        simp }
  inv :=
    { doctrineHom := finiteCofiniteDoctrineCodeOfIso object.doctrine hall atomEquiv |>.inv
      source_eq := rfl }
  hom_inv_id := by
    apply ExtInstHom.ext
    exact (finiteCofiniteDoctrineCodeOfIso object.doctrine hall atomEquiv).hom_inv_id
  inv_hom_id := by
    apply ExtInstHom.ext
    exact (finiteCofiniteDoctrineCodeOfIso object.doctrine hall atomEquiv).inv_hom_id

/-- Finite/cofinite target extractions pull back along every exact doctrine hom. -/
theorem allExtractionsFiniteOrCofinite_source_of_hom {U : AtomCarrier.{u}}
    {source target : ExtractionInstance U} (hom : source ⟶ target)
    (htarget : AllExtractionsFiniteOrCofinite target) :
    AllExtractionsFiniteOrCofinite source := by
  intro input
  have hset : extractedAtomSet source input =
      hom.doctrineHom.atomEquiv ⁻¹'
        extractedAtomSet target (hom.doctrineHom.sourceMap input) := by
    ext atom
    exact hom.doctrineHom.extraction_iff input atom
  rcases htarget (hom.doctrineHom.sourceMap input) with hfinite | hcofinite
  · left
    rw [hset]
    exact hfinite.preimage
      (Set.injOn_of_injective hom.doctrineHom.atomEquiv.injective)
  · right
    rw [hset, ← Set.preimage_compl]
    exact hcofinite.preimage
      (Set.injOn_of_injective hom.doctrineHom.atomEquiv.injective)

/--
The selected endpoint-finite / target-finite-or-cofinite term is sufficient for
anchored coverage on every carrier.
-/
noncomputable def endpointFiniteTargetCofinitePresentation
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : CartSemanticInput U)
    [Finite input.source.doctrine.Source]
    [Finite input.target.doctrine.Source]
    (htarget : AllExtractionsFiniteOrCofinite input.target) :
    CartPresentationBetween
      (finiteCofiniteInstanceCodeOf input.source
        (allExtractionsFiniteOrCofinite_source_of_hom input.hom htarget)
        (Equiv.refl U.Atom))
      (finiteCofiniteInstanceCodeOf input.target htarget
        input.hom.doctrineHom.atomEquiv) where
  sourceMap := fun source =>
    (finiteSourceEquiv input.target.doctrine.Source).symm
      (input.hom.doctrineHom.sourceMap
        (finiteSourceEquiv input.source.doctrine.Source source))
  atomEquiv := AtomPermutationCode.refl
  normalize_eq := by
    intro source
    apply (finiteSourceEquiv input.target.doctrine.Source).injective
    change
      finiteSourceEquiv input.target.doctrine.Source
          ((finiteCofiniteDoctrineCodeOf input.target.doctrine htarget
            input.hom.doctrineHom.atomEquiv).normalize
            ((finiteSourceEquiv input.target.doctrine.Source).symm
              (input.hom.doctrineHom.sourceMap
                (finiteSourceEquiv input.source.doctrine.Source source)))) =
        finiteSourceEquiv input.target.doctrine.Source
          ((finiteSourceEquiv input.target.doctrine.Source).symm
            (input.hom.doctrineHom.sourceMap
              (finiteSourceEquiv input.source.doctrine.Source
                ((finiteCofiniteDoctrineCodeOf input.source.doctrine
                  (allExtractionsFiniteOrCofinite_source_of_hom input.hom htarget)
                  (Equiv.refl U.Atom)).normalize source))))
    rw [finiteCofiniteDoctrineCodeOf_normalize]
    simp only [Equiv.apply_symm_apply]
    rw [finiteCofiniteDoctrineCodeOf_normalize]
    exact input.hom.doctrineHom.normalize_eq _
  extraction_eq := by
    intro source
    have hsourceRange : ∃ sourceInput : input.source.doctrine.Source,
        input.source.doctrine.normalize sourceInput =
          input.source.doctrine.normalize
            (finiteSourceEquiv input.source.doctrine.Source source) :=
      ⟨finiteSourceEquiv input.source.doctrine.Source source, rfl⟩
    have htargetRange : ∃ targetSource,
        input.target.doctrine.normalize targetSource =
          input.target.doctrine.normalize
            (input.hom.doctrineHom.sourceMap
              (finiteSourceEquiv input.source.doctrine.Source source)) :=
      ⟨input.hom.doctrineHom.sourceMap
        (finiteSourceEquiv input.source.doctrine.Source source), rfl⟩
    let sourceHall :=
      allExtractionsFiniteOrCofinite_source_of_hom input.hom htarget
    simp only [finiteCofiniteInstanceCodeOf,
      finiteCofiniteDoctrineCodeOf_extraction,
      AtomPermutationCode.toEquiv_refl,
      AtomPredicateCode.transport_refl]
    rw [finiteCofiniteDoctrineCodeOf_normalize]
    simp only [Equiv.apply_symm_apply]
    rw [finiteCofiniteDoctrineCodeOf_normalize]
    apply finiteCofiniteExtractionCode_eq_of_mem_range
      input.target.doctrine input.source.doctrine htarget sourceHall
      input.hom.doctrineHom.atomEquiv (Equiv.refl U.Atom)
      (input.target.doctrine.normalize
        (input.hom.doctrineHom.sourceMap
          (finiteSourceEquiv input.source.doctrine.Source source)))
      (input.source.doctrine.normalize
        (finiteSourceEquiv input.source.doctrine.Source source))
      htargetRange hsourceRange
    intro atom
    simpa [normalizedExtractionPredicate_normalize_iff] using
      (input.hom.doctrineHom.extraction_iff
        (finiteSourceEquiv input.source.doctrine.Source source) atom).symm
  source_eq := by
    apply (finiteSourceEquiv input.target.doctrine.Source).injective
    simp [finiteCofiniteInstanceCodeOf, input.hom.source_eq]

/-- The general presentation commutes with its two generated endpoint anchors. -/
theorem endpointFiniteTargetCofinitePresentation_hom_comm
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : CartSemanticInput U)
    [Finite input.source.doctrine.Source]
    [Finite input.target.doctrine.Source]
    (htarget : AllExtractionsFiniteOrCofinite input.target) :
    (finiteCofiniteInstanceCodeOfIso input.source
        (allExtractionsFiniteOrCofinite_source_of_hom input.hom htarget)
        (Equiv.refl U.Atom)).hom ≫ input.hom =
      (toSemanticCart
        (endpointFiniteTargetCofinitePresentation input htarget).toPresentation).hom ≫
        (finiteCofiniteInstanceCodeOfIso input.target htarget
          input.hom.doctrineHom.atomEquiv).hom := by
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
      input.hom.doctrineHom.atomEquiv
        (AtomPermutationCode.refl.toEquiv atom)
    simp

/-- Endpoint finiteness plus target finite/cofinite extraction is sufficient. -/
theorem endpointFiniteTargetCofiniteCoverage
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : CartSemanticInput U)
    [Finite input.source.doctrine.Source]
    [Finite input.target.doctrine.Source]
    (htarget : AllExtractionsFiniteOrCofinite input.target) :
    Nonempty (AnchoredCoverageWitness input) := by
  let sourceHall :=
    allExtractionsFiniteOrCofinite_source_of_hom input.hom htarget
  let sourceAnchor : CoveredObjectWitness input.source :=
    { code := finiteCofiniteInstanceCodeOf input.source sourceHall
        (Equiv.refl U.Atom)
      iso := finiteCofiniteInstanceCodeOfIso input.source sourceHall
        (Equiv.refl U.Atom) }
  let targetAnchor : CoveredObjectWitness input.target :=
    { code := finiteCofiniteInstanceCodeOf input.target htarget
        input.hom.doctrineHom.atomEquiv
      iso := finiteCofiniteInstanceCodeOfIso input.target htarget
        input.hom.doctrineHom.atomEquiv }
  exact ⟨
    { sourceAnchor := sourceAnchor
      targetAnchor := targetAnchor
      arrow :=
        { presentation := endpointFiniteTargetCofinitePresentation input htarget
          square :=
            { sourceIso := sourceAnchor.iso
              targetIso := targetAnchor.iso
              hom_comm := endpointFiniteTargetCofinitePresentation_hom_comm
                input htarget }
          sourceIso_eq := rfl
          targetIso_eq := rfl } }⟩

/-- The source maps of an object isomorphism form an ordinary equivalence. -/
noncomputable def extractionInstanceIsoSourceEquiv {U : AtomCarrier.{u}}
    {first second : ExtractionInstance U} (iso : first ≅ second) :
    first.doctrine.Source ≃ second.doctrine.Source where
  toFun := iso.hom.doctrineHom.sourceMap
  invFun := iso.inv.doctrineHom.sourceMap
  left_inv := by
    intro source
    have h := congrArg
      (fun hom : first ⟶ first => hom.doctrineHom.sourceMap source)
      iso.hom_inv_id
    exact h
  right_inv := by
    intro source
    have h := congrArg
      (fun hom : second ⟶ second => hom.doctrineHom.sourceMap source)
      iso.inv_hom_id
    exact h

/-- A decoded finite instance has a finite source type. -/
theorem coveredObjectWitness_finiteSource {U : AtomCarrier.{u}}
    [DecidableEq U.Atom] {object : ExtractionInstance U}
    (witness : CoveredObjectWitness object) :
    Finite object.doctrine.Source := by
  exact Finite.of_equiv witness.code.doctrine.Source
    (extractionInstanceIsoSourceEquiv witness.iso)

/-- Every finite/cofinite exception table denotes a finite or cofinite set. -/
theorem atomPredicateCode_finiteOrCofinite {U : AtomCarrier.{u}}
    [DecidableEq U.Atom] (code : AtomPredicateCode U) :
    Set.Finite {atom | code.Holds atom} ∨
      Set.Finite {atom | ¬ code.Holds atom} := by
  cases hdefault : code.defaultValue <;>
    simp [AtomPredicateCode.Holds, AtomPredicateCode.eval, hdefault,
      code.exceptions.finite_toSet]

/-- Every decoded finite doctrine has finite/cofinite semantic extractions. -/
theorem finiteDoctrineCode_allExtractionsFiniteOrCofinite
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (code : FiniteInstanceCode U) :
    AllExtractionsFiniteOrCofinite code.toSemantic := by
  intro source
  have hset : extractedAtomSet code.toSemantic source =
      {atom |
        (code.doctrine.extraction (code.doctrine.normalize source)).Holds atom} := by
    ext atom
    exact FiniteDoctrineCode.toDoctrine_extracts_iff _ _ _
  rw [hset]
  simpa only [Set.compl_setOf] using atomPredicateCode_finiteOrCofinite
    (code.doctrine.extraction (code.doctrine.normalize source))

/-- Finite/cofinite extraction transfers across an isomorphism of instances. -/
theorem allExtractionsFiniteOrCofinite_target_of_iso
    {U : AtomCarrier.{u}} {first second : ExtractionInstance U}
    (iso : first ≅ second)
    (hfirst : AllExtractionsFiniteOrCofinite first) :
    AllExtractionsFiniteOrCofinite second := by
  intro targetSource
  let source := iso.inv.doctrineHom.sourceMap targetSource
  have hsourceMap : iso.hom.doctrineHom.sourceMap source = targetSource := by
    change (extractionInstanceIsoSourceEquiv iso)
        ((extractionInstanceIsoSourceEquiv iso).symm targetSource) = targetSource
    simp
  have himage : extractedAtomSet second targetSource =
      iso.hom.doctrineHom.atomEquiv '' extractedAtomSet first source := by
    ext atom
    constructor
    · intro htarget
      refine ⟨iso.hom.doctrineHom.atomEquiv.symm atom, ?_, by simp⟩
      exact (iso.hom.doctrineHom.extraction_iff source _).mpr (by
        simpa [extractedAtomSet, hsourceMap] using htarget)
    · rintro ⟨sourceAtom, hsource, rfl⟩
      simpa [extractedAtomSet, hsourceMap] using
        (iso.hom.doctrineHom.extraction_iff source sourceAtom).mp hsource
  rcases hfirst source with hfinite | hcofinite
  · left
    rw [himage]
    exact hfinite.image _
  · right
    have hcomplement : (extractedAtomSet second targetSource)ᶜ =
        iso.hom.doctrineHom.atomEquiv ''
          (extractedAtomSet first source)ᶜ := by
      ext atom
      constructor
      · intro hnot
        refine ⟨iso.hom.doctrineHom.atomEquiv.symm atom, ?_, by simp⟩
        intro hsource
        apply hnot
        rw [himage]
        exact ⟨_, hsource, by simp⟩
      · rintro ⟨sourceAtom, hnot, rfl⟩ htarget
        apply hnot
        have : iso.hom.doctrineHom.atomEquiv sourceAtom ∈
            iso.hom.doctrineHom.atomEquiv '' extractedAtomSet first source := by
          simpa [← himage] using htarget
        rcases this with ⟨candidate, hcandidate, heq⟩
        have hcandidate_eq : candidate = sourceAtom :=
          iso.hom.doctrineHom.atomEquiv.injective heq
        simpa [hcandidate_eq] using hcandidate
    rw [hcomplement]
    exact hcofinite.image _

/-- Every object anchor forces finite Source and finite/cofinite extraction. -/
theorem coveredObjectWitness_necessary {U : AtomCarrier.{u}}
    [DecidableEq U.Atom] {object : ExtractionInstance U}
    (witness : CoveredObjectWitness object) :
    Finite object.doctrine.Source ∧
      AllExtractionsFiniteOrCofinite object :=
  ⟨coveredObjectWitness_finiteSource witness,
    allExtractionsFiniteOrCofinite_target_of_iso witness.iso
      (finiteDoctrineCode_allExtractionsFiniteOrCofinite witness.code)⟩

/-! ## Fixed counterexamples for the earlier candidate terms -/

/-- A countably infinite Atom carrier used only for fixed K1 refutations. -/
def ExactBottomNatCarrier : AtomCarrier.{u} where
  AtomKind := PUnit
  Axis := PUnit
  Subject := PUnit
  Predicate := PUnit
  Payload := PUnit
  Atom := ULift.{u} Nat
  kind := fun _ => PUnit.unit
  axis := fun _ => PUnit.unit
  subject := fun _ => PUnit.unit
  predicate := fun _ => PUnit.unit
  payload := fun _ => PUnit.unit

local instance exactBottomNatCarrierDecidableEq :
    DecidableEq ExactBottomNatCarrier.{u}.Atom := by
  change DecidableEq (ULift.{u} Nat)
  infer_instance

/-- The authored even-number predicate. -/
def exactBottomEven (atom : ExactBottomNatCarrier.{u}.Atom) : Prop :=
  ∃ index : Nat, atom.down = 2 * index

/-- The even set is infinite. -/
theorem exactBottomEven_not_finite :
    ¬ Set.Finite {atom : ExactBottomNatCarrier.{u}.Atom | exactBottomEven atom} := by
  intro hfinite
  letI : Finite {atom : ExactBottomNatCarrier.{u}.Atom // exactBottomEven atom} :=
    hfinite.to_subtype
  have hnat : Finite Nat := by
    apply Finite.of_injective
      (fun index : Nat =>
        (⟨ULift.up (2 * index), ⟨index, rfl⟩⟩ :
          {atom : ExactBottomNatCarrier.{u}.Atom // exactBottomEven atom}))
    intro first second h
    have h := congrArg (fun atom => atom.1.down) h
    change 2 * first = 2 * second at h
    omega
  letI : Finite Nat := hnat
  letI : Fintype Nat := Fintype.ofFinite Nat
  exact Fintype.false (α := Nat) inferInstance

/-- The odd complement of the even set is also infinite. -/
theorem exactBottomEven_compl_not_finite :
    ¬ Set.Finite {atom : ExactBottomNatCarrier.{u}.Atom | exactBottomEven atom}ᶜ := by
  intro hfinite
  letI : Finite {atom : ExactBottomNatCarrier.{u}.Atom // ¬ exactBottomEven atom} :=
    hfinite.to_subtype
  have hnat : Finite Nat := by
    apply Finite.of_injective
      (fun index : Nat =>
        (⟨ULift.up (2 * index + 1), by
          intro heven
          rcases heven with ⟨other, heq⟩
          change 2 * index + 1 = 2 * other at heq
          omega⟩ : {atom : ExactBottomNatCarrier.{u}.Atom // ¬ exactBottomEven atom}))
    intro first second h
    have h := congrArg (fun atom => atom.1.down) h
    change 2 * first + 1 = 2 * second + 1 at h
    omega
  letI : Finite Nat := hnat
  letI : Fintype Nat := Fintype.ofFinite Nat
  exact Fintype.false (α := Nat) inferInstance

/-- There is no finite structure on `Nat`. -/
theorem exactBottomNat_not_finite : ¬ Finite Nat := by
  intro hfinite
  letI : Finite Nat := hfinite
  letI : Fintype Nat := Fintype.ofFinite Nat
  exact Fintype.false (α := Nat) inferInstance

/-- Universe lifting does not make `Nat` finite. -/
theorem exactBottomULiftNat_not_finite : ¬ Finite (ULift.{u} Nat) := by
  intro hfinite
  letI : Finite (ULift.{u} Nat) := hfinite
  exact exactBottomNat_not_finite
    (Finite.of_equiv (ULift.{u} Nat) Equiv.ulift)

/-- One-source doctrine whose unique extraction is the even set. -/
def exactBottomBadOneDoctrine : ExtractionDoctrine ExactBottomNatCarrier.{u} where
  Source := PUnit.{u + 1}
  Vocabulary := PUnit.{u + 1}
  SemanticReading := PUnit.{u + 1}
  Resolution := PUnit.{u + 1}
  vocabulary := PUnit.unit
  semanticReading := PUnit.unit
  resolution := PUnit.unit
  vocabularyAllows := fun _ _ => True
  semanticAllows := fun _ _ atom => exactBottomEven atom
  resolutionAllows := fun _ _ _ => True
  sourceSemantics := fun _ _ => True
  normalize := id

/-- Selected bad one-source object. -/
def exactBottomBadOneInstance : ExtractionInstance ExactBottomNatCarrier.{u} :=
  ⟨exactBottomBadOneDoctrine.{u}, PUnit.unit⟩

/-- Identity on the bad one-source object. -/
def exactBottomBadFiniteInput : CartSemanticInput ExactBottomNatCarrier.{u} :=
  ⟨exactBottomBadOneInstance, exactBottomBadOneInstance,
    𝟙 exactBottomBadOneInstance⟩

/-- All-admitting one-source doctrine. -/
def exactBottomAllOneDoctrine : ExtractionDoctrine ExactBottomNatCarrier.{u} where
  Source := PUnit.{u + 1}
  Vocabulary := PUnit.{u + 1}
  SemanticReading := PUnit.{u + 1}
  Resolution := PUnit.{u + 1}
  vocabulary := PUnit.unit
  semanticReading := PUnit.unit
  resolution := PUnit.unit
  vocabularyAllows := fun _ _ => True
  semanticAllows := fun _ _ _ => True
  resolutionAllows := fun _ _ _ => True
  sourceSemantics := fun _ _ => True
  normalize := id

/-- All-admitting infinite-source doctrine. -/
def exactBottomAllNatDoctrine : ExtractionDoctrine ExactBottomNatCarrier.{u} where
  Source := ULift.{u} Nat
  Vocabulary := PUnit.{u + 1}
  SemanticReading := PUnit.{u + 1}
  Resolution := PUnit.{u + 1}
  vocabulary := PUnit.unit
  semanticReading := PUnit.unit
  resolution := PUnit.unit
  vocabularyAllows := fun _ _ => True
  semanticAllows := fun _ _ _ => True
  resolutionAllows := fun _ _ _ => True
  sourceSemantics := fun _ _ => True
  normalize := id

/-- The selected one-cell all-extracting endpoint from the fixed O6 raw data. -/
def exactBottomAllOneInstance : ExtractionInstance ExactBottomNatCarrier.{u} :=
  ⟨exactBottomAllOneDoctrine.{u}, PUnit.unit⟩

/-- The selected zero cell of the infinite all-extracting endpoint. -/
def exactBottomAllNatInstance : ExtractionInstance ExactBottomNatCarrier.{u} :=
  ⟨exactBottomAllNatDoctrine.{u}, ULift.up 0⟩

/-- Exact map from the finite all-admitting source to the infinite one. -/
def exactBottomFiniteToInfiniteHom :
    exactBottomAllOneInstance.{u} ⟶ exactBottomAllNatInstance.{u} where
  doctrineHom :=
    { sourceMap := fun _ => ULift.up 0
      atomEquiv := Equiv.refl _
      normalize_eq := by intro source; cases source; rfl
      extraction_iff := by simp [ExtractionDoctrine.extracts,
        exactBottomAllOneInstance, exactBottomAllNatInstance,
        exactBottomAllOneDoctrine, exactBottomAllNatDoctrine] }
  source_eq := rfl

/-- Exact map from the infinite all-admitting source to the finite one. -/
def exactBottomInfiniteToFiniteHom :
    exactBottomAllNatInstance.{u} ⟶ exactBottomAllOneInstance.{u} where
  doctrineHom :=
    { sourceMap := fun _ => PUnit.unit
      atomEquiv := Equiv.refl _
      normalize_eq := by intro source; rfl
      extraction_iff := by simp [ExtractionDoctrine.extracts,
        exactBottomAllOneInstance, exactBottomAllNatInstance,
        exactBottomAllOneDoctrine, exactBottomAllNatDoctrine] }
  source_eq := rfl

/-- Fixed O6 semantic input from the one-cell endpoint to the infinite endpoint. -/
def exactBottomFiniteToInfiniteInput : CartSemanticInput ExactBottomNatCarrier.{u} :=
  ⟨exactBottomAllOneInstance, exactBottomAllNatInstance,
    exactBottomFiniteToInfiniteHom⟩

/-- Fixed O6 semantic input from the infinite endpoint to the one-cell endpoint. -/
def exactBottomInfiniteToFiniteInput : CartSemanticInput ExactBottomNatCarrier.{u} :=
  ⟨exactBottomAllNatInstance, exactBottomAllOneInstance,
    exactBottomInfiniteToFiniteHom⟩

/-- Fixed O6 infinite identity and final characterized-branch counterexample. -/
def exactBottomInfiniteIdentityInput : CartSemanticInput ExactBottomNatCarrier.{u} :=
  ⟨exactBottomAllNatInstance, exactBottomAllNatInstance,
    𝟙 exactBottomAllNatInstance⟩

/-- Two-source target: its selected cell is all-admitting and its unused cell is bad. -/
def exactBottomMixedTargetDoctrine : ExtractionDoctrine ExactBottomNatCarrier.{u} where
  Source := ULift.{u} Bool
  Vocabulary := PUnit.{u + 1}
  SemanticReading := PUnit.{u + 1}
  Resolution := PUnit.{u + 1}
  vocabulary := PUnit.unit
  semanticReading := PUnit.unit
  resolution := PUnit.unit
  vocabularyAllows := fun _ _ => True
  semanticAllows := fun _ source atom => source.down = false ∨ exactBottomEven atom
  resolutionAllows := fun _ _ _ => True
  sourceSemantics := fun _ _ => True
  normalize := id

/-- The selected all-extracting cell of the fixed mixed target endpoint. -/
def exactBottomMixedTargetInstance : ExtractionInstance ExactBottomNatCarrier.{u} :=
  ⟨exactBottomMixedTargetDoctrine.{u}, ULift.up false⟩

/-- The source map lands only in the target's all-admitting cell. -/
def exactBottomFiniteToMixedHom :
    exactBottomAllOneInstance.{u} ⟶ exactBottomMixedTargetInstance.{u} where
  doctrineHom :=
    { sourceMap := fun _ => ULift.up false
      atomEquiv := Equiv.refl _
      normalize_eq := by intro source; cases source; rfl
      extraction_iff := by simp [ExtractionDoctrine.extracts,
        exactBottomAllOneInstance, exactBottomMixedTargetInstance,
        exactBottomAllOneDoctrine, exactBottomMixedTargetDoctrine] }
  source_eq := rfl

/-- Fixed O6 input whose map avoids the mixed target's bad cell. -/
def exactBottomFiniteToMixedInput : CartSemanticInput ExactBottomNatCarrier.{u} :=
  ⟨exactBottomAllOneInstance, exactBottomMixedTargetInstance,
    exactBottomFiniteToMixedHom⟩

/-! ## Counterexample properties and the selected candidate -/

/-- Every extraction of the all-admitting one-source object is cofinite. -/
theorem exactBottomAllOne_allExtractions :
    AllExtractionsFiniteOrCofinite exactBottomAllOneInstance := by
  intro source
  right
  simp [extractedAtomSet, ExtractionDoctrine.extracts,
    exactBottomAllOneInstance, exactBottomAllOneDoctrine]

/-- Every extraction of the all-admitting infinite-source object is cofinite. -/
theorem exactBottomAllNat_allExtractions :
    AllExtractionsFiniteOrCofinite exactBottomAllNatInstance := by
  intro source
  right
  simp [extractedAtomSet, ExtractionDoctrine.extracts,
    exactBottomAllNatInstance, exactBottomAllNatDoctrine]

/-- The even-set object fails the finite/cofinite extraction condition. -/
theorem exactBottomBadOne_not_allExtractions :
    ¬ AllExtractionsFiniteOrCofinite exactBottomBadOneInstance := by
  intro hall
  rcases hall PUnit.unit with hfinite | hcofinite
  · apply exactBottomEven_not_finite
    simpa [extractedAtomSet, ExtractionDoctrine.extracts,
      exactBottomBadOneInstance, exactBottomBadOneDoctrine] using hfinite
  · apply exactBottomEven_compl_not_finite
    simpa [extractedAtomSet, ExtractionDoctrine.extracts,
      exactBottomBadOneInstance, exactBottomBadOneDoctrine] using hcofinite

/-- The unused `true` cell makes the mixed target fail the condition. -/
theorem exactBottomMixedTarget_not_allExtractions :
    ¬ AllExtractionsFiniteOrCofinite exactBottomMixedTargetInstance := by
  intro hall
  rcases hall (ULift.up true) with hfinite | hcofinite
  · apply exactBottomEven_not_finite
    simpa [extractedAtomSet, ExtractionDoctrine.extracts,
      exactBottomMixedTargetInstance, exactBottomMixedTargetDoctrine] using hfinite
  · apply exactBottomEven_compl_not_finite
    simpa [extractedAtomSet, ExtractionDoctrine.extracts,
      exactBottomMixedTargetInstance, exactBottomMixedTargetDoctrine] using hcofinite

/-- An infinite source endpoint cannot have an anchored finite-code witness. -/
theorem exactBottom_not_covered_of_source_infinite
    (input : CartSemanticInput ExactBottomNatCarrier.{u})
    (hinfinite : ¬ Finite input.source.doctrine.Source) :
    ¬ Nonempty (AnchoredCoverageWitness input) := by
  rintro ⟨witness⟩
  exact hinfinite (coveredObjectWitness_finiteSource witness.sourceAnchor)

/-- An infinite target endpoint cannot have an anchored finite-code witness. -/
theorem exactBottom_not_covered_of_target_infinite
    (input : CartSemanticInput ExactBottomNatCarrier.{u})
    (hinfinite : ¬ Finite input.target.doctrine.Source) :
    ¬ Nonempty (AnchoredCoverageWitness input) := by
  rintro ⟨witness⟩
  exact hinfinite (coveredObjectWitness_finiteSource witness.targetAnchor)

/-- A target with a non-finite/non-cofinite extraction cannot be covered. -/
theorem exactBottom_not_covered_of_target_bad
    (input : CartSemanticInput ExactBottomNatCarrier.{u})
    (hbad : ¬ AllExtractionsFiniteOrCofinite input.target) :
    ¬ Nonempty (AnchoredCoverageWitness input) := by
  rintro ⟨witness⟩
  exact hbad (coveredObjectWitness_necessary witness.targetAnchor).2

/-- The selected twelfth pre-registered term. -/
def endpointFiniteTargetCofiniteTerm :
    ExactBottomConditionSyntax FiniteModel.carrier :=
  .conjunction (.conjunction .sourceFinite .targetFinite)
    .allTargetExtractionsFiniteOrCofinite

/-- Candidate index eleven is definitionally the selected term. -/
theorem exactBottomCandidateTerm_eleven :
    exactBottomCandidateTerm ⟨11, by decide⟩ =
      endpointFiniteTargetCofiniteTerm :=
  rfl

/-- The selected evaluator exposes precisely its three mathematical clauses. -/
theorem eval_endpointFiniteTargetCofiniteTerm_iff
    {U : AtomCarrier.{u}} (input : CartSemanticInput U) :
    evalExactBottomCondition
        (rebaseExactBottomCondition endpointFiniteTargetCofiniteTerm) input ↔
      (Finite input.source.doctrine.Source ∧
        Finite input.target.doctrine.Source) ∧
        AllExtractionsFiniteOrCofinite input.target :=
  Iff.rfl

/-- The selected condition is sufficient on every Atom carrier. -/
theorem endpointFiniteTargetCofiniteTerm_sufficient
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : CartSemanticInput U)
    (membership : evalExactBottomCondition
      (rebaseExactBottomCondition endpointFiniteTargetCofiniteTerm) input) :
    Nonempty (AnchoredCoverageWitness input) := by
  rcases membership with ⟨⟨hsource, htarget⟩, hextractions⟩
  letI : Finite input.source.doctrine.Source := hsource
  letI : Finite input.target.doctrine.Source := htarget
  exact endpointFiniteTargetCofiniteCoverage input hextractions

/-- The finite bad identity is outside the anchored realization locus. -/
theorem exactBottomBadFiniteInput_not_covered :
    ¬ Nonempty (AnchoredCoverageWitness exactBottomBadFiniteInput) :=
  exactBottom_not_covered_of_target_bad exactBottomBadFiniteInput
    exactBottomBadOne_not_allExtractions

/-- The finite-to-infinite fixture is not covered. -/
theorem exactBottomFiniteToInfiniteInput_not_covered :
    ¬ Nonempty (AnchoredCoverageWitness exactBottomFiniteToInfiniteInput) := by
  apply exactBottom_not_covered_of_target_infinite
  exact exactBottomULiftNat_not_finite

/-- The infinite-to-finite fixture is not covered. -/
theorem exactBottomInfiniteToFiniteInput_not_covered :
    ¬ Nonempty (AnchoredCoverageWitness exactBottomInfiniteToFiniteInput) := by
  apply exactBottom_not_covered_of_source_infinite
  exact exactBottomULiftNat_not_finite

/-- The infinite identity fixture is not covered. -/
theorem exactBottomInfiniteIdentityInput_not_covered :
    ¬ Nonempty (AnchoredCoverageWitness exactBottomInfiniteIdentityInput) := by
  apply exactBottom_not_covered_of_source_infinite
  exact exactBottomULiftNat_not_finite

/-- The finite-to-mixed fixture is not covered. -/
theorem exactBottomFiniteToMixedInput_not_covered :
    ¬ Nonempty (AnchoredCoverageWitness exactBottomFiniteToMixedInput) :=
  exactBottom_not_covered_of_target_bad exactBottomFiniteToMixedInput
    exactBottomMixedTarget_not_allExtractions

/-- Candidate 0 fires on `bad-id`, whose target extraction cannot be encoded. -/
noncomputable def exactBottomCandidateRefutation0 :
    ExactBottomCandidateRefutation.{u}
      (exactBottomCandidateTerm ⟨0, by decide⟩) := by
  apply ExactBottomCandidateRefutation.insufficient exactBottomBadFiniteInput.{u}
  · change Finite PUnit ∧ Finite PUnit
    exact ⟨inferInstance, inferInstance⟩
  · exact exactBottomBadFiniteInput_not_covered

/-- Candidate 1 fires on `finite-to-infinite`, whose target Source is infinite. -/
noncomputable def exactBottomCandidateRefutation1 :
    ExactBottomCandidateRefutation.{u}
      (exactBottomCandidateTerm ⟨1, by decide⟩) := by
  apply ExactBottomCandidateRefutation.insufficient
    exactBottomFiniteToInfiniteInput.{u}
  · change Finite PUnit ∧
      AllExtractionsFiniteOrCofinite exactBottomAllOneInstance
    exact ⟨inferInstance, exactBottomAllOne_allExtractions⟩
  · exact exactBottomFiniteToInfiniteInput_not_covered

/-- Candidate 2 fires on `infinite-to-finite`, whose source Source is infinite. -/
noncomputable def exactBottomCandidateRefutation2 :
    ExactBottomCandidateRefutation.{u}
      (exactBottomCandidateTerm ⟨2, by decide⟩) := by
  apply ExactBottomCandidateRefutation.insufficient
    exactBottomInfiniteToFiniteInput.{u}
  · change Finite PUnit ∧
      AllExtractionsFiniteOrCofinite exactBottomAllOneInstance
    exact ⟨inferInstance, exactBottomAllOne_allExtractions⟩
  · exact exactBottomInfiniteToFiniteInput_not_covered

/-- Candidate 3 fires on `infinite-id`, whose source Source is infinite. -/
noncomputable def exactBottomCandidateRefutation3 :
    ExactBottomCandidateRefutation.{u}
      (exactBottomCandidateTerm ⟨3, by decide⟩) := by
  apply ExactBottomCandidateRefutation.insufficient exactBottomInfiniteIdentityInput.{u}
  · change AllExtractionsFiniteOrCofinite exactBottomAllNatInstance ∧
      AllExtractionsFiniteOrCofinite exactBottomAllNatInstance
    exact ⟨exactBottomAllNat_allExtractions,
      exactBottomAllNat_allExtractions⟩
  · exact exactBottomInfiniteIdentityInput_not_covered

/-- Candidate 4 fires on `finite-to-infinite`, whose target Source is infinite. -/
noncomputable def exactBottomCandidateRefutation4 :
    ExactBottomCandidateRefutation.{u}
      (exactBottomCandidateTerm ⟨4, by decide⟩) := by
  apply ExactBottomCandidateRefutation.insufficient
    exactBottomFiniteToInfiniteInput.{u}
  · change Finite PUnit ∧
      AllExtractionsFiniteOrCofinite exactBottomAllNatInstance
    exact ⟨inferInstance, exactBottomAllNat_allExtractions⟩
  · exact exactBottomFiniteToInfiniteInput_not_covered

/-- Candidate 5 fires on `infinite-to-finite`, whose source Source is infinite. -/
noncomputable def exactBottomCandidateRefutation5 :
    ExactBottomCandidateRefutation.{u}
      (exactBottomCandidateTerm ⟨5, by decide⟩) := by
  apply ExactBottomCandidateRefutation.insufficient
    exactBottomInfiniteToFiniteInput.{u}
  · change Finite PUnit ∧
      AllExtractionsFiniteOrCofinite exactBottomAllNatInstance
    exact ⟨inferInstance, exactBottomAllNat_allExtractions⟩
  · exact exactBottomInfiniteToFiniteInput_not_covered

/-- Candidate 6 fires on `finite-to-infinite`, whose target Source is infinite. -/
noncomputable def exactBottomCandidateRefutation6 :
    ExactBottomCandidateRefutation.{u}
      (exactBottomCandidateTerm ⟨6, by decide⟩) := by
  apply ExactBottomCandidateRefutation.insufficient
    exactBottomFiniteToInfiniteInput.{u}
  · change Finite PUnit
    infer_instance
  · exact exactBottomFiniteToInfiniteInput_not_covered

/-- Candidate 7 fires on `infinite-to-finite`, whose source Source is infinite. -/
noncomputable def exactBottomCandidateRefutation7 :
    ExactBottomCandidateRefutation.{u}
      (exactBottomCandidateTerm ⟨7, by decide⟩) := by
  apply ExactBottomCandidateRefutation.insufficient
    exactBottomInfiniteToFiniteInput.{u}
  · change Finite PUnit
    infer_instance
  · exact exactBottomInfiniteToFiniteInput_not_covered

/-- Candidate 8 fires on `infinite-id`, whose source Source is infinite. -/
noncomputable def exactBottomCandidateRefutation8 :
    ExactBottomCandidateRefutation.{u}
      (exactBottomCandidateTerm ⟨8, by decide⟩) := by
  apply ExactBottomCandidateRefutation.insufficient exactBottomInfiniteIdentityInput.{u}
  · change AllExtractionsFiniteOrCofinite exactBottomAllNatInstance
    exact exactBottomAllNat_allExtractions
  · exact exactBottomInfiniteIdentityInput_not_covered

/-- Candidate 9 fires on `infinite-id`, whose source Source is infinite. -/
noncomputable def exactBottomCandidateRefutation9 :
    ExactBottomCandidateRefutation.{u}
      (exactBottomCandidateTerm ⟨9, by decide⟩) := by
  apply ExactBottomCandidateRefutation.insufficient exactBottomInfiniteIdentityInput.{u}
  · change AllExtractionsFiniteOrCofinite exactBottomAllNatInstance
    exact exactBottomAllNat_allExtractions
  · exact exactBottomInfiniteIdentityInput_not_covered

/-- Candidate 10 fires on `finite-to-mixed`, whose unused target cell is bad. -/
noncomputable def exactBottomCandidateRefutation10 :
    ExactBottomCandidateRefutation.{u}
      (exactBottomCandidateTerm ⟨10, by decide⟩) := by
  apply ExactBottomCandidateRefutation.insufficient exactBottomFiniteToMixedInput.{u}
  · change (Finite PUnit.{u + 1} ∧ Finite (ULift.{u} Bool)) ∧
      AllExtractionsFiniteOrCofinite exactBottomAllOneInstance
    exact ⟨⟨inferInstance, inferInstance⟩, exactBottomAllOne_allExtractions⟩
  · exact exactBottomFiniteToMixedInput_not_covered

/-- The selected term is exactly the first non-refuted pre-registered candidate. -/
noncomputable def endpointFiniteTargetCofiniteSelection :
    ExactBottomCandidateSelection.{u} where
  index := ⟨11, by decide⟩
  priorRefutations := by
    intro prior
    refine Fin.cases exactBottomCandidateRefutation0 ?_ prior
    intro prior
    refine Fin.cases exactBottomCandidateRefutation1 ?_ prior
    intro prior
    refine Fin.cases exactBottomCandidateRefutation2 ?_ prior
    intro prior
    refine Fin.cases exactBottomCandidateRefutation3 ?_ prior
    intro prior
    refine Fin.cases exactBottomCandidateRefutation4 ?_ prior
    intro prior
    refine Fin.cases exactBottomCandidateRefutation5 ?_ prior
    intro prior
    refine Fin.cases exactBottomCandidateRefutation6 ?_ prior
    intro prior
    refine Fin.cases exactBottomCandidateRefutation7 ?_ prior
    intro prior
    refine Fin.cases exactBottomCandidateRefutation8 ?_ prior
    intro prior
    refine Fin.cases exactBottomCandidateRefutation9 ?_ prior
    intro prior
    refine Fin.cases exactBottomCandidateRefutation10 ?_ prior
    intro prior
    exact Fin.elim0 prior

/-! ## Qualification and the carrier-global branch -/

/-- A finite all-admitting object deliberately outside the strict code image. -/
def exactBottomDecoratedDoctrine : ExtractionDoctrine FiniteModel.carrier where
  Source := PUnit
  Vocabulary := Bool
  SemanticReading := PUnit
  Resolution := PUnit
  vocabulary := false
  semanticReading := PUnit.unit
  resolution := PUnit.unit
  vocabularyAllows := fun _ _ => True
  semanticAllows := fun _ _ _ => True
  resolutionAllows := fun _ _ _ => True
  sourceSemantics := fun _ _ => True
  normalize := id

/-- The selected object of the fixed strict-image-outside positive-family member. -/
def exactBottomDecoratedInstance : ExtractionInstance FiniteModel.carrier :=
  ⟨exactBottomDecoratedDoctrine, PUnit.unit⟩

/-- Every decorated extraction is cofinite. -/
theorem exactBottomDecorated_allExtractions :
    AllExtractionsFiniteOrCofinite exactBottomDecoratedInstance := by
  intro source
  right
  simp [extractedAtomSet, ExtractionDoctrine.extracts,
    exactBottomDecoratedInstance, exactBottomDecoratedDoctrine]

/-- Literal finite-code realization cannot manufacture a `Bool` vocabulary. -/
theorem exactBottomDecorated_not_strict :
    ¬ StrictCartRealizationImage
      (cartSemanticInputOfHom (𝟙 exactBottomDecoratedInstance)) := by
  rintro ⟨presentation, equality⟩
  have hvocabulary := congrArg
    (fun input : CartSemanticInput FiniteModel.carrier =>
      input.source.doctrine.Vocabulary) equality
  change PUnit = Bool at hvocabulary
  have hcard : Fintype.card PUnit = Fintype.card Bool :=
    Fintype.card_congr (Equiv.cast hvocabulary)
  norm_num at hcard

/-- A two-member family combines a realized noninvertible arrow and strict outsider. -/
def exactBottomPositiveFamily : ExactBottomPositiveFamilyRaw where
  Parameter := Bool
  distinguished := false
  source
    | false => finiteSelectiveTwoInput.semantic.source
    | true => exactBottomDecoratedInstance
  target
    | false => finiteSelectiveTwoInput.semantic.target
    | true => exactBottomDecoratedInstance
  hom
    | false => finiteSelectiveTwoInput.semantic.hom
    | true => 𝟙 exactBottomDecoratedInstance

/-- The two family members cannot be isomorphic as semantic arrows. -/
theorem exactBottomPositiveFamily_not_isomorphic :
    ¬ Nonempty (CartSemanticInputIso
      (exactBottomPositiveFamily.input false)
      (exactBottomPositiveFamily.input true)) := by
  rintro ⟨iso⟩
  let sourceEquiv := extractionInstanceIsoSourceEquiv iso.sourceIso
  change FiniteSource 2 ≃ PUnit at sourceEquiv
  have hcard := Fintype.card_congr sourceEquiv
  change 2 = 1 at hcard
  omega

/-- The selected pre-registered term satisfies all qualification gates. -/
noncomputable def endpointFiniteTargetCofiniteQualification :
    ExactBottomConditionQualification.{u} endpointFiniteTargetCofiniteTerm where
  isomorphic_invariant := by
    intro U first second iso
    rw [eval_endpointFiniteTargetCofiniteTerm_iff,
      eval_endpointFiniteTargetCofiniteTerm_iff]
    constructor
    · rintro ⟨⟨hsource, htarget⟩, hall⟩
      letI : Finite first.source.doctrine.Source := hsource
      letI : Finite first.target.doctrine.Source := htarget
      exact ⟨⟨
        Finite.of_equiv first.source.doctrine.Source
          (extractionInstanceIsoSourceEquiv iso.sourceIso),
        Finite.of_equiv first.target.doctrine.Source
          (extractionInstanceIsoSourceEquiv iso.targetIso)⟩,
        allExtractionsFiniteOrCofinite_target_of_iso iso.targetIso hall⟩
    · rintro ⟨⟨hsource, htarget⟩, hall⟩
      letI : Finite second.source.doctrine.Source := hsource
      letI : Finite second.target.doctrine.Source := htarget
      exact ⟨⟨
        Finite.of_equiv second.source.doctrine.Source
          (extractionInstanceIsoSourceEquiv iso.sourceIso).symm,
        Finite.of_equiv second.target.doctrine.Source
          (extractionInstanceIsoSourceEquiv iso.targetIso).symm⟩,
        allExtractionsFiniteOrCofinite_target_of_iso iso.targetIso.symm hall⟩
  identity_mem := by
    intro U _ object anchor
    rw [eval_endpointFiniteTargetCofiniteTerm_iff]
    have necessary := coveredObjectWitness_necessary anchor
    exact ⟨⟨necessary.1, necessary.1⟩, necessary.2⟩
  comp_mem := by
    intro U _ pair hfirst hsecond
    rw [eval_endpointFiniteTargetCofiniteTerm_iff] at hfirst hsecond ⊢
    exact ⟨⟨hfirst.1.1, hsecond.1.2⟩, hsecond.2⟩
  pullback_fst_mem := by
    intro U _ cospan hfirst hsecond
    rw [eval_endpointFiniteTargetCofiniteTerm_iff] at hfirst hsecond ⊢
    letI : Finite cospan.left.doctrine.Source := hfirst.1.1
    letI : Finite cospan.right.doctrine.Source := hsecond.1.1
    have hpullback :
        Finite (pointedPullback cospan.first cospan.second).doctrine.Source :=
      by
        apply Finite.of_injective
          (fun source => source.val)
        exact Subtype.val_injective
    exact ⟨⟨hpullback, hfirst.1.1⟩,
      allExtractionsFiniteOrCofinite_source_of_hom cospan.first hfirst.2⟩
  pullback_snd_mem := by
    intro U _ cospan hfirst hsecond
    rw [eval_endpointFiniteTargetCofiniteTerm_iff] at hfirst hsecond ⊢
    letI : Finite cospan.left.doctrine.Source := hfirst.1.1
    letI : Finite cospan.right.doctrine.Source := hsecond.1.1
    have hpullback :
        Finite (pointedPullback cospan.first cospan.second).doctrine.Source :=
      by
        apply Finite.of_injective
          (fun source => source.val)
        exact Subtype.val_injective
    exact ⟨⟨hpullback, hsecond.1.1⟩,
      allExtractionsFiniteOrCofinite_source_of_hom cospan.second hsecond.2⟩
  realization_image_mem := by
    intro U _ presentation
    rw [eval_endpointFiniteTargetCofiniteTerm_iff]
    change (Finite (FiniteSource presentation.1.source.doctrine.sourceCard) ∧
      Finite (FiniteSource presentation.1.target.doctrine.sourceCard)) ∧
      AllExtractionsFiniteOrCofinite presentation.1.target.toSemantic
    exact ⟨⟨inferInstance, inferInstance⟩,
      finiteDoctrineCode_allExtractionsFiniteOrCofinite presentation.1.target⟩
  positiveFamily := exactBottomPositiveFamily
  positive_fires := by
    intro parameter
    cases parameter
    · change (Finite (FiniteSource 2) ∧ Finite (FiniteSource 1)) ∧
        AllExtractionsFiniteOrCofinite finiteSelectiveOneInstance.toSemantic
      exact ⟨⟨inferInstance, inferInstance⟩,
        finiteDoctrineCode_allExtractionsFiniteOrCofinite
          finiteSelectiveOneInstance⟩
    · change (Finite PUnit ∧ Finite PUnit) ∧
        AllExtractionsFiniteOrCofinite exactBottomDecoratedInstance
      exact ⟨⟨inferInstance, inferInstance⟩,
        exactBottomDecorated_allExtractions⟩
  positive_strictly_outside := by
    refine ⟨true, ?_⟩
    simpa [ExactBottomPositiveFamilyRaw.input, exactBottomPositiveFamily] using
      exactBottomDecorated_not_strict
  positive_nonisomorphic_pair :=
    ⟨false, true, ⟨by
      change (false : Bool) ≠ true
      decide,
      exactBottomPositiveFamily_not_isomorphic⟩⟩
  positive_noninvertible := by
    refine ⟨false, ?_⟩
    simpa [exactBottomPositiveFamily] using finiteSelectiveTwoInput_not_isIso

/-- The carrier-global negative branch selected by the fixed candidate list. -/
noncomputable def characterizedExactBottomCoverage :
    CharacterizedExactBottomCoverage.{u} where
  selection := endpointFiniteTargetCofiniteSelection
  qualification := by
    simpa [endpointFiniteTargetCofiniteSelection,
      ExactBottomCandidateSelection.template,
      exactBottomCandidateTerm_eleven] using
      endpointFiniteTargetCofiniteQualification.{u}
  sufficient := by
    intro U _ input membership
    apply endpointFiniteTargetCofiniteTerm_sufficient input
    simpa [endpointFiniteTargetCofiniteSelection,
      ExactBottomCandidateSelection.template,
      exactBottomCandidateTerm_eleven] using membership
  counterexampleCarrier := ExactBottomNatCarrier.{u}
  counterexampleDecidableEq := exactBottomNatCarrierDecidableEq
  counterexample := exactBottomInfiniteIdentityInput.{u}
  counterexample_not_covered :=
    exactBottomInfiniteIdentityInput_not_covered.{u}

/-- G-112(b): one carrier-global disjunction, resolved by the negative branch. -/
noncomputable def exactBottomCoverageDisjunction :
    ExactBottomCoverageDisjunction.{u} :=
  .characterized characterizedExactBottomCoverage

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
