import ResearchLean.AG.DoctrineFiberProduct.CartesianRegimeSchema

/-!
# Canonical cross-universe reindexing of the finite G-110 code layer

This module fixes the first F0c2 boundary.  An `AtomCarrierEquiv` records a
uniform equivalence of every carrier coordinate and its compatibility with the
five Atom projections.  The finite presentation language is then rebased
computably along that equivalence: predicates, finite-support permutations,
doctrines, pointed instances, raw cartesian arrows, and validated
presentations.

The construction supplies the finite-code and decoder components of the
arbitrary-package helper route.  The branch-conditioned G-110 contract uses a
named package and strong-cartesian nonexistence transfer only when the right
branch is selected.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u v w

open AtomFoundation

/-! ## Carrier and first-order finite-source equivalences -/

/--
An equivalence of Atom carriers, including all five coordinate sorts and the
commuting laws for their projections.
-/
structure AtomCarrierEquiv (U : AtomCarrier.{u}) (V : AtomCarrier.{v}) where
  /-- Equivalence of Atom-kind coordinates. -/
  atomKind : U.AtomKind ≃ V.AtomKind
  /-- Equivalence of axis coordinates. -/
  axis : U.Axis ≃ V.Axis
  /-- Equivalence of subject coordinates. -/
  subject : U.Subject ≃ V.Subject
  /-- Equivalence of predicate coordinates. -/
  predicate : U.Predicate ≃ V.Predicate
  /-- Equivalence of payload coordinates. -/
  payload : U.Payload ≃ V.Payload
  /-- Equivalence of Atoms. -/
  atom : U.Atom ≃ V.Atom
  /-- Atom-kind projection commutes with reindexing. -/
  kind_comm : ∀ value, atomKind (U.kind value) = V.kind (atom value)
  /-- Axis projection commutes with reindexing. -/
  axis_comm : ∀ value, axis (U.axis value) = V.axis (atom value)
  /-- Subject projection commutes with reindexing. -/
  subject_comm : ∀ value, subject (U.subject value) = V.subject (atom value)
  /-- Predicate projection commutes with reindexing. -/
  predicate_comm : ∀ value,
    predicate (U.predicate value) = V.predicate (atom value)
  /-- Payload projection commutes with reindexing. -/
  payload_comm : ∀ value, payload (U.payload value) = V.payload (atom value)

/-- Reindex a first-order finite source without changing its natural-number cell. -/
def finiteSourceRebaseEquiv (card : ℕ) :
    FiniteSource.{u} card ≃ FiniteSource.{v} card where
  toFun source := ULift.up source.down
  invFun source := ULift.up source.down
  left_inv source := by cases source; rfl
  right_inv source := by cases source; rfl

/-- Reindexing a finite source leaves its underlying `Fin` cell unchanged. -/
@[simp]
theorem finiteSourceRebaseEquiv_apply_down (card : ℕ)
    (source : FiniteSource.{u} card) :
    (finiteSourceRebaseEquiv.{u, v} card source).down = source.down := rfl

/-! ## Finite Atom tables -/

namespace AtomPredicateCode

/-- Reindex a finite/cofinite Atom predicate along an Atom equivalence. -/
def rebase {U : AtomCarrier.{u}} {V : AtomCarrier.{v}}
    (equiv : U.Atom ≃ V.Atom) (code : AtomPredicateCode U) :
    AtomPredicateCode V where
  defaultValue := code.defaultValue
  exceptions := code.exceptions.map equiv.toEmbedding

/-- Predicate evaluation is natural under Atom reindexing. -/
@[simp]
theorem eval_rebase {U : AtomCarrier.{u}} {V : AtomCarrier.{v}}
    [DecidableEq U.Atom] [DecidableEq V.Atom]
    (equiv : U.Atom ≃ V.Atom) (code : AtomPredicateCode U)
    (atom : U.Atom) :
    (code.rebase equiv).eval (equiv atom) = code.eval atom := by
  simp [rebase, eval]

/-- Reindexing commutes with permutation transport by conjugation. -/
theorem rebase_transport {U : AtomCarrier.{u}} {V : AtomCarrier.{v}}
    [DecidableEq U.Atom] [DecidableEq V.Atom]
    (equiv : U.Atom ≃ V.Atom) (code : AtomPredicateCode U)
    (permutation : Equiv.Perm U.Atom) :
    (code.transport permutation).rebase equiv =
      (code.rebase equiv).transport
        (equiv.symm.trans (permutation.trans equiv)) := by
  cases code
  simp only [rebase, transport]
  congr 1
  rw [Finset.map_map, Finset.map_map]
  congr 1
  ext atom
  simp

end AtomPredicateCode

namespace AtomPermutationCode

/-- Reindex a finite-support permutation by conjugating it along an Atom equivalence. -/
def rebase {U : AtomCarrier.{u}} {V : AtomCarrier.{v}}
    [DecidableEq U.Atom] [DecidableEq V.Atom]
    (equiv : U.Atom ≃ V.Atom) (code : AtomPermutationCode U) :
    AtomPermutationCode V :=
  let conjugate : Equiv.Perm V.Atom :=
    equiv.symm.trans (code.toEquiv.trans equiv)
  ofPerm (code.support.map equiv.toEmbedding) conjugate
    (fun atom => by
      change equiv (code.toEquiv (equiv.symm atom)) ∈
          code.support.map equiv.toEmbedding ↔
        atom ∈ code.support.map equiv.toEmbedding
      simp only [Finset.mem_map_equiv]
      simpa using code.toEquiv_mem_superset_iff code.support (by simp)
        (equiv.symm atom))
    (fun atom hnot => by
      change equiv (code.toEquiv (equiv.symm atom)) = atom
      rw [Equiv.apply_eq_iff_eq_symm_apply]
      apply code.toEquiv_apply_not_mem
      intro hmem
      apply hnot
      exact Finset.mem_map.mpr
        ⟨equiv.symm atom, hmem, equiv.apply_symm_apply atom⟩)

/-- The authored support of a rebased permutation is the mapped source support. -/
@[simp]
theorem rebase_support {U : AtomCarrier.{u}} {V : AtomCarrier.{v}}
    [DecidableEq U.Atom] [DecidableEq V.Atom]
    (equiv : U.Atom ≃ V.Atom) (code : AtomPermutationCode U) :
    (code.rebase equiv).support = code.support.map equiv.toEmbedding := rfl

/-- Decoding a rebased table gives the conjugated permutation. -/
@[simp]
theorem toEquiv_rebase {U : AtomCarrier.{u}} {V : AtomCarrier.{v}}
    [DecidableEq U.Atom] [DecidableEq V.Atom]
    (equiv : U.Atom ≃ V.Atom) (code : AtomPermutationCode U) :
    (code.rebase equiv).toEquiv =
      equiv.symm.trans (code.toEquiv.trans equiv) := by
  simp [rebase]

end AtomPermutationCode

/-! ## Doctrine, instance, and cartesian-code reindexing -/

namespace FiniteDoctrineCode

/-- Reindex a finite doctrine while conjugating its finite normalization table. -/
def rebase {U : AtomCarrier.{u}} {V : AtomCarrier.{v}}
    (equiv : AtomCarrierEquiv U V) (code : FiniteDoctrineCode U) :
    FiniteDoctrineCode V where
  sourceCard := code.sourceCard
  normalize := fun source =>
    finiteSourceRebaseEquiv.{u, v} code.sourceCard
      (code.normalize
        ((finiteSourceRebaseEquiv.{u, v} code.sourceCard).symm source))
  extraction := fun source =>
    (code.extraction
      ((finiteSourceRebaseEquiv.{u, v} code.sourceCard).symm source)).rebase
        equiv.atom

/-- Doctrine reindexing preserves the authored first-order source cardinality. -/
@[simp]
theorem rebase_sourceCard {U : AtomCarrier.{u}} {V : AtomCarrier.{v}}
    (equiv : AtomCarrierEquiv U V) (code : FiniteDoctrineCode U) :
    (code.rebase equiv).sourceCard = code.sourceCard := rfl

/-- The rebased normalization table is the conjugate of the original table. -/
@[simp]
theorem rebase_normalize {U : AtomCarrier.{u}} {V : AtomCarrier.{v}}
    (equiv : AtomCarrierEquiv U V) (code : FiniteDoctrineCode U)
    (source : code.Source) :
    (code.rebase equiv).normalize
        (finiteSourceRebaseEquiv.{u, v} code.sourceCard source) =
      finiteSourceRebaseEquiv.{u, v} code.sourceCard
        (code.normalize source) := by
  simp [rebase, finiteSourceRebaseEquiv]

/-- The rebased extraction cell is exactly the reindexed original cell. -/
@[simp]
theorem rebase_extraction {U : AtomCarrier.{u}} {V : AtomCarrier.{v}}
    (equiv : AtomCarrierEquiv U V) (code : FiniteDoctrineCode U)
    (source : code.Source) :
    (code.rebase equiv).extraction
        (finiteSourceRebaseEquiv.{u, v} code.sourceCard source) =
      (code.extraction source).rebase equiv.atom := by
  simp [rebase, finiteSourceRebaseEquiv]

/-- The decoded extraction relation is invariant on corresponding source/Atom cells. -/
@[simp]
theorem toDoctrine_extracts_rebase_iff {U : AtomCarrier.{u}}
    {V : AtomCarrier.{v}} [DecidableEq U.Atom] [DecidableEq V.Atom]
    (equiv : AtomCarrierEquiv U V) (code : FiniteDoctrineCode U)
    (source : code.Source) (atom : U.Atom) :
    (code.rebase equiv).toDoctrine.extracts
        (finiteSourceRebaseEquiv.{u, v} code.sourceCard source)
        (equiv.atom atom) ↔
      code.toDoctrine.extracts source atom := by
  rw [FiniteDoctrineCode.toDoctrine_extracts_iff,
    FiniteDoctrineCode.toDoctrine_extracts_iff]
  simp [AtomPredicateCode.Holds]

end FiniteDoctrineCode

namespace FiniteInstanceCode

/-- Reindex a pointed finite instance, including its selected source cell. -/
def rebase {U : AtomCarrier.{u}} {V : AtomCarrier.{v}}
    (equiv : AtomCarrierEquiv U V) (code : FiniteInstanceCode U) :
    FiniteInstanceCode V where
  doctrine := code.doctrine.rebase equiv
  point := finiteSourceRebaseEquiv.{u, v} code.doctrine.sourceCard code.point

/-- The doctrine component of a rebased instance is the rebased doctrine. -/
@[simp]
theorem rebase_doctrine {U : AtomCarrier.{u}} {V : AtomCarrier.{v}}
    (equiv : AtomCarrierEquiv U V) (code : FiniteInstanceCode U) :
    (code.rebase equiv).doctrine = code.doctrine.rebase equiv := rfl

/-- The selected point of a rebased instance is the mapped selected point. -/
@[simp]
theorem rebase_point {U : AtomCarrier.{u}} {V : AtomCarrier.{v}}
    (equiv : AtomCarrierEquiv U V) (code : FiniteInstanceCode U) :
    (code.rebase equiv).point =
      finiteSourceRebaseEquiv.{u, v} code.doctrine.sourceCard code.point := rfl

end FiniteInstanceCode

namespace CartRawCode

/-- Reindex all four authored fields of a raw cartesian code. -/
def rebase {U : AtomCarrier.{u}} {V : AtomCarrier.{v}}
    [DecidableEq U.Atom] [DecidableEq V.Atom]
    (equiv : AtomCarrierEquiv U V) (code : CartRawCode U) : CartRawCode V where
  source := code.source.rebase equiv
  target := code.target.rebase equiv
  sourceMap := fun source =>
    finiteSourceRebaseEquiv.{u, v} code.target.doctrine.sourceCard
      (code.sourceMap
        ((finiteSourceRebaseEquiv.{u, v}
          code.source.doctrine.sourceCard).symm source))
  atomEquiv := code.atomEquiv.rebase equiv.atom

/-- The rebased source-map table is the conjugate of the original table. -/
@[simp]
theorem rebase_sourceMap {U : AtomCarrier.{u}} {V : AtomCarrier.{v}}
    [DecidableEq U.Atom] [DecidableEq V.Atom]
    (equiv : AtomCarrierEquiv U V) (code : CartRawCode U)
    (source : code.source.doctrine.Source) :
    (code.rebase equiv).sourceMap
        (finiteSourceRebaseEquiv.{u, v}
          code.source.doctrine.sourceCard source) =
      finiteSourceRebaseEquiv.{u, v}
        code.target.doctrine.sourceCard (code.sourceMap source) := by
  simp [CartRawCode.rebase]

/-- The decoded Atom component of a rebased raw code is the conjugate permutation. -/
@[simp]
theorem rebase_atomEquiv_apply {U : AtomCarrier.{u}} {V : AtomCarrier.{v}}
    [DecidableEq U.Atom] [DecidableEq V.Atom]
    (equiv : AtomCarrierEquiv U V) (code : CartRawCode U)
    (atom : U.Atom) :
    (code.rebase equiv).atomEquiv.toEquiv (equiv.atom atom) =
      equiv.atom (code.atomEquiv.toEquiv atom) := by
  simp [CartRawCode.rebase, AtomPermutationCode.toEquiv_rebase,
    Equiv.trans_apply]

/-- Well-formed raw codes remain well formed after canonical reindexing. -/
theorem WellFormed.rebase {U : AtomCarrier.{u}} {V : AtomCarrier.{v}}
    [DecidableEq U.Atom] [DecidableEq V.Atom]
    (equiv : AtomCarrierEquiv U V) {code : CartRawCode U}
    (wellFormed : code.WellFormed) : (code.rebase equiv).WellFormed := by
  refine ⟨?_, ?_, ?_⟩
  · intro source
    let original :=
      (finiteSourceRebaseEquiv.{u, v}
        code.source.doctrine.sourceCard).symm source
    have hsource : source = finiteSourceRebaseEquiv.{u, v}
        code.source.doctrine.sourceCard original := by
      simp [original]
    rw [hsource]
    change finiteSourceRebaseEquiv.{u, v} code.target.doctrine.sourceCard
        (code.target.doctrine.normalize (code.sourceMap original)) =
      finiteSourceRebaseEquiv.{u, v} code.target.doctrine.sourceCard
        (code.sourceMap (code.source.doctrine.normalize original))
    exact congrArg
      (finiteSourceRebaseEquiv.{u, v} code.target.doctrine.sourceCard)
      (wellFormed.1 original)
  · intro source
    let original :=
      (finiteSourceRebaseEquiv.{u, v}
        code.source.doctrine.sourceCard).symm source
    have equality := congrArg
      (AtomPredicateCode.rebase equiv.atom) (wellFormed.2.1 original)
    have hsource : source = finiteSourceRebaseEquiv.{u, v}
        code.source.doctrine.sourceCard original := by
      simp [original]
    rw [hsource]
    simpa [CartRawCode.rebase,
      AtomPredicateCode.rebase_transport] using equality
  · simp [CartRawCode.rebase, wellFormed.2.2]

end CartRawCode

/-- Reindex a validated cartesian presentation without adding any certificate field. -/
def rebaseCartPresentation {U : AtomCarrier.{u}} {V : AtomCarrier.{v}}
    [DecidableEq U.Atom] [DecidableEq V.Atom]
    (equiv : AtomCarrierEquiv U V) (presentation : CartPresentation U) :
    CartPresentation V :=
  ⟨presentation.1.rebase equiv, presentation.2.rebase equiv⟩

/-- Decoder source maps commute with finite-presentation reindexing. -/
@[simp]
theorem toSemanticCart_rebase_sourceMap {U : AtomCarrier.{u}}
    {V : AtomCarrier.{v}} [DecidableEq U.Atom] [DecidableEq V.Atom]
    (equiv : AtomCarrierEquiv U V) (presentation : CartPresentation U)
    (source : presentation.1.source.doctrine.Source) :
    (toSemanticCart (rebaseCartPresentation equiv presentation)).hom.doctrineHom.sourceMap
        (finiteSourceRebaseEquiv.{u, v}
          presentation.1.source.doctrine.sourceCard source) =
      finiteSourceRebaseEquiv.{u, v}
        presentation.1.target.doctrine.sourceCard
        ((toSemanticCart presentation).hom.doctrineHom.sourceMap source) := by
  simp [toSemanticCart, decodeCartDoctrineHom, rebaseCartPresentation]

/-- Decoder Atom permutations commute with finite-presentation reindexing. -/
@[simp]
theorem toSemanticCart_rebase_atomEquiv {U : AtomCarrier.{u}}
    {V : AtomCarrier.{v}} [DecidableEq U.Atom] [DecidableEq V.Atom]
    (equiv : AtomCarrierEquiv U V) (presentation : CartPresentation U)
    (atom : U.Atom) :
    (toSemanticCart (rebaseCartPresentation equiv presentation)).hom.doctrineHom.atomEquiv
        (equiv.atom atom) =
      equiv.atom ((toSemanticCart presentation).hom.doctrineHom.atomEquiv atom) := by
  simp [toSemanticCart, decodeCartDoctrineHom, rebaseCartPresentation]

/-- The selected source endpoint of the decoder is reindexed canonically. -/
@[simp]
theorem toSemanticCart_rebase_sourcePoint {U : AtomCarrier.{u}}
    {V : AtomCarrier.{v}} [DecidableEq U.Atom] [DecidableEq V.Atom]
    (equiv : AtomCarrierEquiv U V) (presentation : CartPresentation U) :
    (toSemanticCart (rebaseCartPresentation equiv presentation)).source.source =
      finiteSourceRebaseEquiv.{u, v}
        presentation.1.source.doctrine.sourceCard
        (toSemanticCart presentation).source.source := rfl

/-- The selected target endpoint of the decoder is reindexed canonically. -/
@[simp]
theorem toSemanticCart_rebase_targetPoint {U : AtomCarrier.{u}}
    {V : AtomCarrier.{v}} [DecidableEq U.Atom] [DecidableEq V.Atom]
    (equiv : AtomCarrierEquiv U V) (presentation : CartPresentation U) :
    (toSemanticCart (rebaseCartPresentation equiv presentation)).target.source =
      finiteSourceRebaseEquiv.{u, v}
        presentation.1.target.doctrine.sourceCard
        (toSemanticCart presentation).target.source := rfl

namespace CartPresentationBetween

/-- Reindex a typed cartesian presentation while preserving both endpoint indices. -/
def rebase {U : AtomCarrier.{u}} {V : AtomCarrier.{v}}
    [DecidableEq U.Atom] [DecidableEq V.Atom]
    (equiv : AtomCarrierEquiv U V)
    {source target : FiniteInstanceCode U}
    (presentation : CartPresentationBetween source target) :
    CartPresentationBetween (source.rebase equiv) (target.rebase equiv) :=
  ofPresentation (rebaseCartPresentation equiv presentation.toPresentation)

end CartPresentationBetween

/-! ## Reindexing of finite condition values -/

/-- Reindex the universe wrapper of a first-order value. -/
def uliftRebaseEquiv (α : Type w) : ULift.{u} α ≃ ULift.{v} α :=
  Equiv.ulift.trans Equiv.ulift.symm

/-- The universe-wrapper equivalence preserves the wrapped value. -/
@[simp]
theorem uliftRebaseEquiv_apply (α : Type w) (value : ULift.{u} α) :
    uliftRebaseEquiv.{u, v} α value = ULift.up value.down := rfl

/-- Reindex every cell of a finite list along an equivalence. -/
def listRebaseEquiv {α : Type u} {β : Type v} (equiv : α ≃ β) :
    List α ≃ List β where
  toFun := List.map equiv
  invFun := List.map equiv.symm
  left_inv values := by simp
  right_inv values := by simp

/-- List reindexing evaluates by mapping the element equivalence. -/
@[simp]
theorem listRebaseEquiv_apply {α : Type u} {β : Type v}
    (equiv : α ≃ β) (values : List α) :
    listRebaseEquiv equiv values = values.map equiv := rfl

/-- Reindex both the support and graph of a finite Atom table. -/
def atomTableValueRebaseEquiv {U : AtomCarrier.{u}} {V : AtomCarrier.{v}}
    (equiv : U.Atom ≃ V.Atom) : AtomTableValue U ≃ AtomTableValue V where
  toFun code :=
    { support := equiv.finsetCongr code.support
      values := (Equiv.prodCongr equiv equiv).finsetCongr code.values }
  invFun code :=
    { support := equiv.symm.finsetCongr code.support
      values := (Equiv.prodCongr equiv.symm equiv.symm).finsetCongr code.values }
  left_inv code := by
    cases code
    simp [Equiv.finsetCongr_apply, Finset.map_map]
    ext pair
    rcases pair with ⟨first, second⟩
    simp
  right_inv code := by
    cases code
    simp [Equiv.finsetCongr_apply, Finset.map_map]
    ext pair
    rcases pair with ⟨first, second⟩
    simp

/-- Atom-table reindexing maps both the support and the ordered graph. -/
@[simp]
theorem atomTableValueRebaseEquiv_apply {U : AtomCarrier.{u}}
    {V : AtomCarrier.{v}} (equiv : U.Atom ≃ V.Atom)
    (code : AtomTableValue U) :
    atomTableValueRebaseEquiv equiv code =
      { support := equiv.finsetCongr code.support
        values := (Equiv.prodCongr equiv equiv).finsetCongr code.values } := rfl

/-- Every fixed cartesian operand sort is carried equivalently across carriers. -/
def cartFieldValueRebaseEquiv {U : AtomCarrier.{u}} {V : AtomCarrier.{v}}
    (equiv : AtomCarrierEquiv U V) :
    (kind : CartFieldKind) → CartFieldValue U kind ≃ CartFieldValue V kind
  | .natural => uliftRebaseEquiv _
  | .sourceTable => uliftRebaseEquiv _
  | .boolTable => uliftRebaseEquiv _
  | .atomSetTable => listRebaseEquiv equiv.atom.finsetCongr
  | .atomSet => equiv.atom.finsetCongr
  | .atomTable => atomTableValueRebaseEquiv equiv.atom

/-- Natural-number field values retain their first-order value. -/
@[simp]
theorem cartFieldValueRebaseEquiv_natural_apply
    {U : AtomCarrier.{u}} {V : AtomCarrier.{v}}
    (equiv : AtomCarrierEquiv U V) (value : CartFieldValue U .natural) :
    cartFieldValueRebaseEquiv equiv .natural value = ULift.up value.down := rfl

/-- Source-table field values retain their first-order table. -/
@[simp]
theorem cartFieldValueRebaseEquiv_sourceTable_apply
    {U : AtomCarrier.{u}} {V : AtomCarrier.{v}}
    (equiv : AtomCarrierEquiv U V) (value : CartFieldValue U .sourceTable) :
    cartFieldValueRebaseEquiv equiv .sourceTable value =
      ULift.up value.down := rfl

/-- Boolean-table field values retain their first-order table. -/
@[simp]
theorem cartFieldValueRebaseEquiv_boolTable_apply
    {U : AtomCarrier.{u}} {V : AtomCarrier.{v}}
    (equiv : AtomCarrierEquiv U V) (value : CartFieldValue U .boolTable) :
    cartFieldValueRebaseEquiv equiv .boolTable value =
      ULift.up value.down := rfl

/-- Atom-set tables are mapped cellwise by the Atom equivalence. -/
@[simp]
theorem cartFieldValueRebaseEquiv_atomSetTable_apply
    {U : AtomCarrier.{u}} {V : AtomCarrier.{v}}
    (equiv : AtomCarrierEquiv U V) (value : CartFieldValue U .atomSetTable) :
    cartFieldValueRebaseEquiv equiv .atomSetTable value =
      value.map equiv.atom.finsetCongr := rfl

/-- Atom-set field values are mapped by the Atom equivalence. -/
@[simp]
theorem cartFieldValueRebaseEquiv_atomSet_apply
    {U : AtomCarrier.{u}} {V : AtomCarrier.{v}}
    (equiv : AtomCarrierEquiv U V) (value : CartFieldValue U .atomSet) :
    cartFieldValueRebaseEquiv equiv .atomSet value =
      equiv.atom.finsetCongr value := rfl

/-- Atom-table field values use the support-and-graph equivalence. -/
@[simp]
theorem cartFieldValueRebaseEquiv_atomTable_apply
    {U : AtomCarrier.{u}} {V : AtomCarrier.{v}}
    (equiv : AtomCarrierEquiv U V) (value : CartFieldValue U .atomTable) :
    cartFieldValueRebaseEquiv equiv .atomTable value =
      atomTableValueRebaseEquiv equiv.atom value := rfl

/-! ## Naturality of the finite presentation readers -/

/-- Conjugating a finite source table preserves its first-order graph. -/
@[simp]
theorem sourceTableValue_rebase {U : AtomCarrier.{u}} {V : AtomCarrier.{v}}
    (domainCard codomainCard : ℕ)
    (table : FiniteSource.{u} domainCard → FiniteSource.{u} codomainCard) :
    sourceTableValue V domainCard codomainCard
        (fun source => finiteSourceRebaseEquiv.{u, v} codomainCard
          (table ((finiteSourceRebaseEquiv.{u, v} domainCard).symm source))) =
      sourceTableValue U domainCard codomainCard table := by
  unfold sourceTableValue
  congr 1
  simp only [finiteSourceCells, List.map_map]
  congr 1

/-- The universe-lifted first-order graph is unchanged by source-table rebasing. -/
@[simp]
theorem sourceTableValue_rebase_ulift {U : AtomCarrier.{u}}
    {V : AtomCarrier.{v}} (domainCard codomainCard : ℕ)
    (table : FiniteSource.{u} domainCard → FiniteSource.{u} codomainCard) :
    (ULift.up (sourceTableValue U domainCard codomainCard table) :
        ULift.{v} SourceTableValue) =
      ULift.up (sourceTableValue V domainCard codomainCard
        (fun source => finiteSourceRebaseEquiv.{u, v} codomainCard
          (table ((finiteSourceRebaseEquiv.{u, v} domainCard).symm source)))) :=
  congrArg ULift.up
    (sourceTableValue_rebase domainCard codomainCard table).symm

/-- The named identity table is independent of the carrier universe. -/
@[simp]
theorem sourceTableValue_identity_rebase {U : AtomCarrier.{u}}
    {V : AtomCarrier.{v}} (card : ℕ) :
    sourceTableValue V card card id = sourceTableValue U card card id := by
  unfold sourceTableValue
  congr 1
  simp [finiteSourceCells, List.map_map, Function.comp_def]

/-- The universe-lifted named identity table is independent of the carrier universe. -/
@[simp]
theorem sourceTableValue_identity_rebase_ulift {U : AtomCarrier.{u}}
    {V : AtomCarrier.{v}} (card : ℕ) :
    (ULift.up (sourceTableValue U card card id) : ULift.{v} SourceTableValue) =
      ULift.up (sourceTableValue V card card id) :=
  congrArg ULift.up (sourceTableValue_identity_rebase card).symm

/-- Reindexing preserves the first-order normalization table exactly. -/
@[simp]
theorem doctrineNormalizeTable_rebase {U : AtomCarrier.{u}}
    {V : AtomCarrier.{v}} (equiv : AtomCarrierEquiv U V)
    (code : FiniteDoctrineCode U) :
    doctrineNormalizeTable (code.rebase equiv) = doctrineNormalizeTable code := by
  exact sourceTableValue_rebase code.sourceCard code.sourceCard code.normalize

/-- Reindexing preserves the Boolean extraction-default table exactly. -/
@[simp]
theorem doctrineExtractionDefaults_rebase {U : AtomCarrier.{u}}
    {V : AtomCarrier.{v}} (equiv : AtomCarrierEquiv U V)
    (code : FiniteDoctrineCode U) :
    doctrineExtractionDefaults (code.rebase equiv) =
      doctrineExtractionDefaults code := by
  simp [doctrineExtractionDefaults, FiniteDoctrineCode.rebase,
    finiteSourceCells, List.map_map, Function.comp_def,
    finiteSourceRebaseEquiv, AtomPredicateCode.rebase]

/-- Reindexing maps every finite extraction-exception support cellwise. -/
@[simp]
theorem doctrineExtractionExceptions_rebase {U : AtomCarrier.{u}}
    {V : AtomCarrier.{v}} (equiv : AtomCarrierEquiv U V)
    (code : FiniteDoctrineCode U) :
    (doctrineExtractionExceptions code).map equiv.atom.finsetCongr =
      doctrineExtractionExceptions (code.rebase equiv) := by
  simp [doctrineExtractionExceptions, FiniteDoctrineCode.rebase,
    finiteSourceCells, List.map_map, Function.comp_def,
    finiteSourceRebaseEquiv, AtomPredicateCode.rebase,
    Equiv.finsetCongr_apply]

/-- The complete finite Atom graph is reindexed by the product Atom equivalence. -/
@[simp]
theorem atomTableValue_rebase {U : AtomCarrier.{u}} {V : AtomCarrier.{v}}
    [DecidableEq U.Atom] [DecidableEq V.Atom]
    (equiv : U.Atom ≃ V.Atom) (code : AtomPermutationCode U) :
    atomTableValueRebaseEquiv equiv (atomTableValue code) =
      atomTableValue (code.rebase equiv) := by
  simp only [atomTableValueRebaseEquiv_apply, atomTableValue,
    Equiv.finsetCongr_apply, AtomPermutationCode.rebase_support,
    AtomPermutationCode.toEquiv_rebase]
  congr 1
  ext pair
  rcases pair with ⟨first, second⟩
  simp only [Equiv.trans_apply, Finset.mem_map_equiv, Finset.mem_image]
  constructor
  · rintro ⟨atom, hmem, hp⟩
    use equiv atom
    refine ⟨by simpa, ?_⟩
    simpa using congrArg (Equiv.prodCongr equiv equiv) hp
  · rintro ⟨atom, hmem, hp⟩
    use equiv.symm atom
    refine ⟨hmem, ?_⟩
    apply (Equiv.prodCongr equiv equiv).injective
    simpa using hp

/-- The explicit support-and-graph record agrees with reindexing the Atom table. -/
@[simp]
theorem atomTableValue_rebase_explicit {U : AtomCarrier.{u}}
    {V : AtomCarrier.{v}} [DecidableEq U.Atom] [DecidableEq V.Atom]
    (equiv : U.Atom ≃ V.Atom) (code : AtomPermutationCode U) :
    ({ support := code.support.map equiv.toEmbedding
       values := (atomTableValue code).values.map
         (Equiv.prodCongr equiv equiv).toEmbedding } : AtomTableValue V) =
      atomTableValue (code.rebase equiv) := by
  simpa [atomTableValueRebaseEquiv_apply,
    Equiv.finsetCongr_apply] using atomTableValue_rebase equiv code

/-- Every fixed projection commutes with validated-presentation reindexing. -/
@[simp]
theorem readCartProjection_rebase {U : AtomCarrier.{u}}
    {V : AtomCarrier.{v}} [DecidableEq U.Atom] [DecidableEq V.Atom]
    (equiv : AtomCarrierEquiv U V) {kind : CartFieldKind}
    (projection : CartProjection U kind) (presentation : CartPresentation U) :
    cartFieldValueRebaseEquiv equiv kind
        (readCartProjection projection presentation) =
      readCartProjection (rebaseCartProjection projection)
        (rebaseCartPresentation equiv presentation) := by
  cases projection <;>
    simp [readCartProjection,
      rebaseCartProjection, rebaseCartPresentation, CartRawCode.rebase,
      Equiv.finsetCongr_apply]
  · exact sourceTableValue_rebase_ulift _ _ presentation.1.sourceMap
  · exact atomTableValue_rebase_explicit equiv.atom presentation.1.atomEquiv

/-- Every allowed named constant commutes with presentation reindexing. -/
@[simp]
theorem readCartNamedConstant_rebase {U : AtomCarrier.{u}}
    {V : AtomCarrier.{v}} [DecidableEq U.Atom] [DecidableEq V.Atom]
    (equiv : AtomCarrierEquiv U V) {kind : CartFieldKind}
    (constant : CartNamedConstant U kind) (presentation : CartPresentation U) :
    cartFieldValueRebaseEquiv equiv kind
        (readCartNamedConstant constant presentation) =
      readCartNamedConstant (rebaseCartNamedConstant constant)
        (rebaseCartPresentation equiv presentation) := by
  cases constant <;>
    simp [readCartNamedConstant,
      rebaseCartNamedConstant, rebaseCartPresentation, CartRawCode.rebase,
      Equiv.finsetCongr_apply]
  exact sourceTableValue_identity_rebase_ulift _

/-- Evaluation of every fixed field term is natural under carrier reindexing. -/
@[simp]
theorem evalCartFieldTerm_rebase {U : AtomCarrier.{u}}
    {V : AtomCarrier.{v}} [DecidableEq U.Atom] [DecidableEq V.Atom]
    (equiv : AtomCarrierEquiv U V) {kind : CartFieldKind}
    (term : CartFieldTerm U kind) (presentation : CartPresentation U) :
    cartFieldValueRebaseEquiv equiv kind
        (evalCartFieldTerm term presentation) =
      evalCartFieldTerm (rebaseCartFieldTerm term)
        (rebaseCartPresentation equiv presentation) := by
  cases term <;> simp [evalCartFieldTerm, rebaseCartFieldTerm]

/-- Presentation-derived first-order finite sets are unchanged by reindexing. -/
@[simp]
theorem evalCartDerivedSet_rebase {U : AtomCarrier.{u}}
    {V : AtomCarrier.{v}} [DecidableEq U.Atom] [DecidableEq V.Atom]
    (equiv : AtomCarrierEquiv U V) (set : CartDerivedSet)
    (presentation : CartPresentation U) :
    evalCartDerivedSet set (rebaseCartPresentation equiv presentation) =
      evalCartDerivedSet set presentation := by
  cases set <;>
    simp [evalCartDerivedSet, rebaseCartPresentation, CartRawCode.rebase,
      FiniteInstanceCode.rebase, FiniteDoctrineCode.rebase,
      finiteSourceCells, List.map_map, Function.comp_def,
      finiteSourceRebaseEquiv]

/-! ## Naturality of the finite universal atoms and complete evaluator -/

/-- Source-map identity on first-order indices is reflected by source reindexing. -/
theorem sourceMapIndexIdentity_rebase_iff {U : AtomCarrier.{u}}
    {V : AtomCarrier.{v}} [DecidableEq U.Atom] [DecidableEq V.Atom]
    (equiv : AtomCarrierEquiv U V) (presentation : CartPresentation U) :
    (∀ source : (rebaseCartPresentation equiv presentation).1.source.doctrine.Source,
        ((rebaseCartPresentation equiv presentation).1.sourceMap source).down.val =
          source.down.val) ↔
      ∀ source : presentation.1.source.doctrine.Source,
        (presentation.1.sourceMap source).down.val = source.down.val := by
  constructor
  · intro h source
    have lifted := h (finiteSourceRebaseEquiv.{u, v}
      presentation.1.source.doctrine.sourceCard source)
    simpa [rebaseCartPresentation, CartRawCode.rebase] using lifted
  · intro h source
    let original := (finiteSourceRebaseEquiv.{u, v}
      presentation.1.source.doctrine.sourceCard).symm source
    have hsource : source = finiteSourceRebaseEquiv.{u, v}
        presentation.1.source.doctrine.sourceCard original := by
      simp [original]
    rw [hsource]
    simpa [rebaseCartPresentation, CartRawCode.rebase] using h original

/-- Fixedness on the authored Atom support is invariant under conjugation. -/
theorem atomMapIdentity_rebase_iff {U : AtomCarrier.{u}}
    {V : AtomCarrier.{v}} [DecidableEq U.Atom] [DecidableEq V.Atom]
    (equiv : U.Atom ≃ V.Atom) (code : AtomPermutationCode U) :
    (∀ atom ∈ (code.rebase equiv).support,
        (code.rebase equiv).toEquiv atom = atom) ↔
      ∀ atom ∈ code.support, code.toEquiv atom = atom := by
  constructor
  · intro h atom hmem
    have lifted := h (equiv atom) (by simp [hmem])
    have reflected := congrArg equiv.symm lifted
    simpa [AtomPermutationCode.toEquiv_rebase, Equiv.trans_apply] using reflected
  · intro h atom hmem
    have horiginal : equiv.symm atom ∈ code.support := by
      simpa using hmem
    have fixed := congrArg equiv (h (equiv.symm atom) horiginal)
    simpa [AtomPermutationCode.toEquiv_rebase, Equiv.trans_apply] using fixed

/-- Identity of a finite normalization table is reflected by source reindexing. -/
theorem normalizeIdentity_rebase_iff {U : AtomCarrier.{u}}
    {V : AtomCarrier.{v}} (equiv : AtomCarrierEquiv U V)
    (code : FiniteDoctrineCode U) :
    (∀ source : (code.rebase equiv).Source,
        (code.rebase equiv).normalize source = source) ↔
      ∀ source : code.Source, code.normalize source = source := by
  constructor
  · intro h source
    have lifted := h (finiteSourceRebaseEquiv.{u, v} code.sourceCard source)
    have reflected := congrArg
      (finiteSourceRebaseEquiv.{u, v} code.sourceCard).symm lifted
    simpa using reflected
  · intro h source
    let original :=
      (finiteSourceRebaseEquiv.{u, v} code.sourceCard).symm source
    have hsource : source =
        finiteSourceRebaseEquiv.{u, v} code.sourceCard original := by
      simp [original]
    rw [hsource]
    simpa using congrArg (finiteSourceRebaseEquiv.{u, v} code.sourceCard)
      (h original)

/-- Well-formed exactness forces preservation of every extraction default bit. -/
theorem extractionDefaultsPreserved_of_wellFormed {U : AtomCarrier.{u}}
    [DecidableEq U.Atom] (presentation : CartPresentation U) :
    ∀ source : presentation.1.source.doctrine.Source,
      (presentation.1.target.doctrine.extraction
        (presentation.1.target.doctrine.normalize
          (presentation.1.sourceMap source))).defaultValue =
      (presentation.1.source.doctrine.extraction
        (presentation.1.source.doctrine.normalize source)).defaultValue := by
  intro source
  simpa [AtomPredicateCode.transport] using congrArg
    AtomPredicateCode.defaultValue (presentation.2.2.1 source)

/-- Well-formed exactness forces the transported extraction-exception table. -/
theorem extractionExceptionsPreserved_of_wellFormed {U : AtomCarrier.{u}}
    [DecidableEq U.Atom] (presentation : CartPresentation U) :
    ∀ source : presentation.1.source.doctrine.Source,
      (presentation.1.target.doctrine.extraction
        (presentation.1.target.doctrine.normalize
          (presentation.1.sourceMap source))).exceptions =
      ((presentation.1.source.doctrine.extraction
        (presentation.1.source.doctrine.normalize source)).transport
          presentation.1.atomEquiv.toEquiv).exceptions := by
  intro source
  exact congrArg AtomPredicateCode.exceptions (presentation.2.2.1 source)

/-- All seven finite-universal equality atoms are invariant under reindexing. -/
@[simp]
theorem evalCartUniversalEquality_rebase {U : AtomCarrier.{u}}
    {V : AtomCarrier.{v}} [DecidableEq U.Atom] [DecidableEq V.Atom]
    (equiv : AtomCarrierEquiv U V) (equality : CartUniversalEquality)
    (presentation : CartPresentation U) :
    evalCartUniversalEquality equality
        (rebaseCartPresentation equiv presentation) =
      evalCartUniversalEquality equality presentation := by
  cases equality with
  | sourceMapNormalize =>
      simp only [evalCartUniversalEquality]
      apply Bool.decide_congr
      constructor
      · intro _
        exact presentation.2.1
      · intro _
        exact (rebaseCartPresentation equiv presentation).2.1
  | sourceMapIdentity =>
      simp only [evalCartUniversalEquality]
      congr 1
      exact Bool.decide_congr
        (sourceMapIndexIdentity_rebase_iff equiv presentation)
  | atomMapIdentity =>
      simp only [evalCartUniversalEquality]
      exact Bool.decide_congr
        (atomMapIdentity_rebase_iff equiv.atom presentation.1.atomEquiv)
  | sourceNormalizeIdentity =>
      simp only [evalCartUniversalEquality]
      exact Bool.decide_congr
        (normalizeIdentity_rebase_iff equiv presentation.1.source.doctrine)
  | targetNormalizeIdentity =>
      simp only [evalCartUniversalEquality]
      exact Bool.decide_congr
        (normalizeIdentity_rebase_iff equiv presentation.1.target.doctrine)
  | extractionDefaultsPreserved =>
      simp only [evalCartUniversalEquality]
      apply Bool.decide_congr
      constructor
      · intro _
        exact extractionDefaultsPreserved_of_wellFormed presentation
      · intro _
        exact extractionDefaultsPreserved_of_wellFormed
          (rebaseCartPresentation equiv presentation)
  | extractionExceptionsPreserved =>
      simp only [evalCartUniversalEquality]
      apply Bool.decide_congr
      constructor
      · intro _
        exact extractionExceptionsPreserved_of_wellFormed presentation
      · intro _
        exact extractionExceptionsPreserved_of_wellFormed
          (rebaseCartPresentation equiv presentation)

/-- The complete finite Boolean cartesian-condition evaluator is reindexing invariant. -/
theorem evalCartCondition_rebase {U : AtomCarrier.{u}} {V : AtomCarrier.{v}}
    [DecidableEq U.Atom] [DecidableEq V.Atom]
    (equiv : AtomCarrierEquiv U V) (term : CartConditionSyntax U)
    (presentation : CartPresentation U) :
    evalCartCondition (rebaseCartCondition (V := V) term)
        (rebaseCartPresentation equiv presentation) =
      evalCartCondition term presentation := by
  induction term with
  | fieldEq left right =>
      simp only [rebaseCartCondition, evalCartCondition]
      rw [← evalCartFieldTerm_rebase equiv left presentation,
        ← evalCartFieldTerm_rebase equiv right presentation]
      exact Bool.decide_congr
        (cartFieldValueRebaseEquiv equiv _).injective.eq_iff
  | fieldMem field set =>
      simp only [rebaseCartCondition, evalCartCondition]
      rw [← evalCartFieldTerm_rebase equiv field presentation,
        evalCartDerivedSet_rebase]
      rfl
  | allCells equality =>
      exact evalCartUniversalEquality_rebase equiv equality presentation
  | conjunction left right left_ih right_ih =>
      simp [rebaseCartCondition, evalCartCondition, left_ih, right_ih]

/-! ## The canonical finite-model carrier equivalence -/

local instance finiteModelULiftBaseAtomDecidableEq :
    DecidableEq FiniteModel.carrier.Atom := by
  change DecidableEq FiniteModel.FiniteAtom
  infer_instance

/-- The canonical equivalence between the finite carrier and its universe lift. -/
def finiteModelLiftCarrierEquiv :
    AtomCarrierEquiv FiniteModel.carrier finiteModelLiftCarrier.{u} where
  atomKind := Equiv.ulift.symm
  axis := Equiv.ulift.symm
  subject := Equiv.ulift.symm
  predicate := Equiv.ulift.symm
  payload := Equiv.ulift.symm
  atom := Equiv.ulift.symm
  kind_comm := by intro atom; rfl
  axis_comm := by intro atom; rfl
  subject_comm := by intro atom; rfl
  predicate_comm := by intro atom; rfl
  payload_comm := by intro atom; rfl

/-- Canonically lift a finite-model cartesian presentation to any universe. -/
def finiteModelLiftCartPresentation (presentation :
    CartPresentation FiniteModel.carrier) :
    CartPresentation finiteModelLiftCarrier.{u} :=
  rebaseCartPresentation finiteModelLiftCarrierEquiv presentation

/-- The canonical finite-model universe lift preserves every fixed condition evaluation. -/
theorem evalCartCondition_finiteModelLift
    (term : CartConditionSyntax FiniteModel.carrier)
    (presentation : CartPresentation FiniteModel.carrier) :
    evalCartCondition
        (rebaseCartCondition (V := finiteModelLiftCarrier.{u}) term)
        (finiteModelLiftCartPresentation.{u} presentation) =
      evalCartCondition term presentation :=
  evalCartCondition_rebase finiteModelLiftCarrierEquiv term presentation

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
