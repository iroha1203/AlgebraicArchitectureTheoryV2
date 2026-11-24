import Formal.SHIGURE.Part1.OperationWords

/-! # Example 2.7

Unary identity operations give structure maps with neither injectivity nor
surjectivity required by Theorem 2.6. Even an identity on carriers can
strictly enlarge a partial operation word's domain.
-/

namespace SHIGURE.Chapter2.OperationWordExamples

/-- A single sort with one unary total operation and no other symbols. -/
private def identitySignature : Signature.{0} where
  SortType := Unit
  Total := Unit
  Rel := Empty
  Partial := Empty
  Quantity := Empty
  totalArity _ := ⟨[()], ()⟩
  relInputs r := nomatch r
  partialArity p := nomatch p
  quantityArity q := nomatch q

/-- Interpret the unary operation as the identity on a chosen carrier. -/
private def identityStructure (X : Type) : Structure identitySignature where
  carrier _ := X
  total _ xs := xs .here
  relation r := nomatch r
  partialDomain p := nomatch p
  partialValue p := nomatch p
  quantity q := nomatch q

/-- Each function preserves the unary identity operation. -/
private def identityMap {X Y : Type} (f : X → Y) : StructureMap (identityStructure X) (identityStructure Y) where
  onSort _ := f
  total_comm _ _ := rfl
  relation_mem r := nomatch r
  partial_mem p := nomatch p
  partial_comm p := nomatch p
  quantity_comm q := nomatch q

/-- The two-point carrier collapses onto the one-point carrier. -/
def collapse : StructureMap (identityStructure Bool) (identityStructure Unit) := identityMap fun _ => ()

/-- The one-point carrier includes as the false point of the two-point carrier. -/
def includePoint : StructureMap (identityStructure Unit) (identityStructure Bool) := identityMap fun _ => false

/-- Both Boolean values have the same image under the collapse. -/
theorem collapse_not_injective : ¬ Function.Injective (collapse.onSort ()) := by
  intro injective
  exact Bool.false_ne_true (injective (show collapse.onSort () false = collapse.onSort () true from rfl))

/-- The true point is omitted by the inclusion of the false point. -/
theorem includePoint_not_surjective : ¬ Function.Surjective (includePoint.onSort ()) := by
  intro surjective
  obtain ⟨x, hx⟩ := surjective true
  exact Bool.false_ne_true hx

/-- Every word of identity operations has the original value at every input. -/
theorem identity_word_evaluates (X : Type) {t : identitySignature.SortType}
    (w : OperationWord identitySignature () t) (x : X) : w.Evaluates (identityStructure X) x x := by
  induction w with
  | nil => exact (OperationWord.evaluates_nil_iff (source := ()) (identityStructure X) x x).2 rfl
  | snoc w op unary ih =>
    apply (w.evaluates_snoc_iff op unary (identityStructure X) x x).2
    refine ⟨x, ih, ?_⟩
    cases op with
    | total f =>
      have inputSort : () = _ := List.cons.inj unary |>.1
      cases inputSort
      exact ((identityStructure X).graph_total_iff f _ _).2 rfl
    | partialOp p => exact nomatch p
    | quantity q => exact nomatch q

/-- Both structures have the constant observation of Example 2.7. -/
private def observe {X : Type} (_ : X) : Unit := ()

/-- The noninjective map preserves the observation of every word at every input. -/
theorem collapse_preserves_observation (w : OperationWord identitySignature () ()) (x : Bool) :
    let hx : x ∈ w.domain (identityStructure Bool) := ⟨x, identity_word_evaluates Bool w x⟩
    observe ((w.eval (identityStructure Unit) (collapse.onSort () x)).get
      (w.domain_image_subset collapse ⟨x, hx, rfl⟩)) =
        observe ((w.eval (identityStructure Bool) x).get hx) := by
  exact w.observation_comm collapse observe observe (fun _ => rfl) x _

/-- The nonsurjective map preserves the observation of every word at every input. -/
theorem includePoint_preserves_observation (w : OperationWord identitySignature () ()) (x : Unit) :
    let hx : x ∈ w.domain (identityStructure Unit) := ⟨x, identity_word_evaluates Unit w x⟩
    observe ((w.eval (identityStructure Bool) (includePoint.onSort () x)).get
      (w.domain_image_subset includePoint ⟨x, hx, rfl⟩)) =
        observe ((w.eval (identityStructure Unit) x).get hx) := by
  exact w.observation_comm includePoint observe observe (fun _ => rfl) x _

/-- A unary partial operation with a nullary quantity to test the word's arity constraint. -/
private def partialSignature : Signature.{0} where
  SortType := Unit
  Total := Empty
  Rel := Empty
  Partial := Unit
  Quantity := Unit
  totalArity f := nomatch f
  relInputs r := nomatch r
  partialArity _ := ⟨[()], ()⟩
  quantityArity _ := ⟨[], ()⟩

/-- Interpret the one-point partial operation with either the empty or full domain. -/
private def partialStructure (full : Bool) : Structure partialSignature where
  carrier _ := Unit
  total f := nomatch f
  relation r := nomatch r
  partialDomain _ := if full then Set.univ else ∅
  partialValue _ _ := ()
  quantity _ _ := ()

/-- The identity function on the one point carries the empty domain into the full domain. -/
def enlarge : StructureMap (partialStructure false) (partialStructure true) where
  onSort _ := id
  total_comm f := nomatch f
  relation_mem r := nomatch r
  partial_mem _ _ _ := Set.mem_univ _
  partial_comm _ _ := rfl
  quantity_comm _ _ := rfl

/-- The single-letter word that uses the named partial operation. -/
def partialWord : OperationWord partialSignature () () := OperationWord.nil.snoc (.partialOp ()) rfl

/-- The nullary quantity cannot be appended to a word ending at any sort. -/
theorem nullary_quantity_cannot_append : ¬ ∃ s : partialSignature.SortType,
    (Operation.quantity (sig := partialSignature) ()).arity.inputs = [s] := by
  rintro ⟨s, same⟩
  change ([] : List Unit) = [s] at same
  simp at same

/-- No point can enter the only primitive step in the source of the enlargement. -/
theorem partialWord_source_domain : partialWord.domain (partialStructure false) = ∅ := by
  ext x
  constructor
  · rintro ⟨y, evaluated⟩
    obtain ⟨z, _, edge⟩ := (OperationWord.evaluates_snoc_iff .nil (.partialOp (sig := partialSignature) ())
      rfl (partialStructure false) x y).1 evaluated
    exact ((partialStructure false).graph_partial_iff () _ _).1 edge |>.1
  · exact False.elim

/-- The target partial word is defined and returns the unique point. -/
theorem partialWord_target_value : partialWord.Evaluates (partialStructure true) () () := by
  apply (OperationWord.evaluates_snoc_iff .nil (.partialOp (sig := partialSignature) ())
    rfl (partialStructure true) () ()).2
  refine ⟨(), (OperationWord.evaluates_nil_iff (source := ()) (partialStructure true) () ()).2 rfl, ?_⟩
  exact ((partialStructure true).graph_partial_iff () _ _).2 ⟨Set.mem_univ _, rfl⟩

/-- The enlargement does not reflect the primitive partial domain in (2.9). -/
theorem enlarge_not_reflects : ¬ enlarge.ReflectsDomains := by
  intro reflects
  let xs := Assignment.cons (X := (partialStructure false).carrier) (s := ()) () Assignment.empty
  exact reflects () xs (Set.mem_univ _)

/-- The enlarging map satisfies all three parts of (2.8) for every word. -/
theorem enlarge_preserves_words (w : OperationWord partialSignature () ()) :
    enlarge.onSort () '' w.domain (partialStructure false) ⊆ w.domain (partialStructure true) ∧
    (∀ x (hx : x ∈ w.domain (partialStructure false)),
      let y := (w.eval (partialStructure true) (enlarge.onSort () x)).get
        (w.domain_image_subset enlarge ⟨x, hx, rfl⟩)
      enlarge.onSort () ((w.eval (partialStructure false) x).get hx) = y ∧
        observe y = observe ((w.eval (partialStructure false) x).get hx)) := by
  refine ⟨w.domain_image_subset enlarge, fun x hx => ⟨w.value_comm enlarge x hx, ?_⟩⟩
  exact w.observation_comm enlarge observe observe (fun _ => rfl) x hx

/-- The domain inclusion of (2.8) holds, while the preimage equality fails on the unique point. -/
theorem partialWord_domain_enlarges :
    enlarge.onSort () '' partialWord.domain (partialStructure false) ⊆ partialWord.domain (partialStructure true) ∧
      partialWord.domain (partialStructure false) ≠ enlarge.onSort () ⁻¹' partialWord.domain (partialStructure true) := by
  refine ⟨partialWord.domain_image_subset enlarge, ?_⟩
  intro same
  have target : () ∈ enlarge.onSort () ⁻¹' partialWord.domain (partialStructure true) :=
    ⟨(), partialWord_target_value⟩
  rw [← same, partialWord_source_domain] at target
  exact target

end SHIGURE.Chapter2.OperationWordExamples
