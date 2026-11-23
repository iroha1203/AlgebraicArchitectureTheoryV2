import Formal.SHIGURE.Part1.IdentityInterpretation
import Formal.SHIGURE.Part1.Reading

/-! # Evaluation in the assigned cover pieces

Compare a quantified formula on a retained relation and verify that an
unassigned primitive is unavailable in the target of the comparison.
-/

namespace SHIGURE.Chapter1.CoverTransport

/-- Distinguish two nullary relations so one can be kept and the other forgotten. -/
private def signature : Signature where
  SortType := Unit
  Total := Empty
  Rel := Bool
  Partial := Empty
  Quantity := Empty
  totalArity f := nomatch f
  relInputs _ := []
  partialArity p := nomatch p
  quantityArity q := nomatch q

/-- There are no Laws beyond the primitive relation declarations. -/
private def presentation : PrimitivePresentation where
  signature := signature
  laws :=
    { LawName := Empty
      statement := fun name => nomatch name
      role := fun name => nomatch name }
  derived name := nomatch name

/-- The retained relation holds and the other relation fails. -/
private def data : Structure signature where
  carrier _ := Bool
  total f := nomatch f
  relation r := if (show Bool from r) then ∅ else Set.univ
  partialDomain p := nomatch p
  partialValue p := nomatch p
  quantity q := nomatch q

/-- The side of the cover assigned by the comparison retains just one relation. -/
private def piece : DeclarationContext presentation where
  declarations := {d | d = .sort () ∨ d = .relation false}
  closed := by
    rintro a (rfl | rfl) d hd
    · exact hd.elim
    · obtain ⟨_, h, _⟩ := hd
      cases h

/-- The whole context retains both relations. -/
private def whole : DeclarationContext presentation := ⟨Set.univ, fun _ _ _ => Set.mem_univ _⟩

/-- The original cover consists of the whole context. -/
private def source : Reading where
  presentation := presentation
  structureData := data
  observation := StateObservation.ofSort () Bool id
  context := whole
  cover := ⟨Unit, fun _ => whole, fun _ _ h => h, fun h => ⟨(), h⟩⟩
  Family := Unit
  realize _ := data
  familyObservation := none
  ValueStructure := fun _ => Unit
  valueStructure := ()
  coefficients := none

/-- The two target pieces cover the whole context, but only one is assigned. -/
private def target : Reading :=
  { source with
    cover :=
      { Index := Bool
        piece := fun i => if i then piece else whole
        subset := fun _ _ _ => Set.mem_univ _
        covers := fun h => ⟨false, h⟩ } }

/-- Restrict the source to one relation and transport its support to the assigned piece. -/
private def coverChange : ReadingContextChange source target (Interpretation.identity presentation.theory) where
  retained := piece
  inside := fun _ _ => Set.mem_univ _
  supporting := Interpretation.identity presentation.theory
  sameSorts := rfl
  sameTranslation := HEq.rfl
  pieces := fun _ => {true}
  localSupport := by
    intro i a ha _ d hd
    refine ⟨true, Set.mem_singleton _, ?_⟩
    change d = .sort () ∨ d = .relation false
    rcases ha with rfl | rfl
    · exact Or.inl (Set.mem_singleton_iff.1 hd)
    · rcases hd with hsort | hrelation
      · obtain ⟨_, h, _⟩ := hsort
        cases h
      · exact Or.inr (Set.mem_singleton_iff.1 hrelation)

/-- The identity state map and the selected cover change belong to one comparison. -/
private def comparison : ReadingComparison source target where
  interpretation := Interpretation.identity presentation.theory
  targetModel := fun name => nomatch name.val
  state :=
    { onSort := fun _ x => x
      total_comm := fun f => nomatch f
      relation_mem := by
        intro r e h
        cases r
        · exact Set.mem_univ _
        · exact h.elim
      partial_mem := fun p => nomatch p
      partial_comm := fun p => nomatch p
      quantity_comm := fun q => nomatch q }
  contexts := rfl
  declarationChange := .changed coverChange
  coefficientChange := PUnit.unit
  value := id
  commutes := fun _ => rfl

/-- An existential can use the actual value of the retained nullary relation. -/
private def formula : Formula signature [] :=
  .ex (s := ()) (.atom (.rel false (fun i => nomatch i)))

/-- The support of that existential fits inside the retained source piece. -/
private theorem formulaSupported :
    Declaration.formulaSupport formula ⊆ (coverChange.sourcePiece ()).declarations := by
  intro d hd
  refine ⟨?_, Set.mem_univ _⟩
  rcases hd with hsort | hformula
  · obtain ⟨_, h, _⟩ := hsort
    cases h
  · exact hformula.imp Set.mem_singleton_iff.1 Set.mem_singleton_iff.1

/-- The local comparison really evaluates the relation in the assigned target piece. -/
theorem existential_transports_in_assigned_piece :
    (RestrictedEvaluation.restrict (coverChange.targetPiece ()) data).holds
      (comparison.interpretation.translation.formula formula)
      (coverChange.local_formula_support () formula formulaSupported)
      (comparison.interpretation.mapStates comparison.state Assignment.empty) :=
  comparison.transport_restricted_formula ⟨coverChange, rfl⟩ () formula formulaSupported
    Assignment.empty ⟨false, Set.mem_univ _⟩

/-- The deliberately unassigned relation cannot be read in the assigned target pieces. -/
theorem other_relation_is_not_assigned :
    Declaration.relation true ∉ (coverChange.targetPiece ()).declarations := by
  rintro ⟨i, hi, h⟩
  have same : i = true := Set.mem_singleton_iff.1 hi
  subst i
  change Declaration.relation (P := presentation) true = Declaration.sort () ∨
    Declaration.relation (P := presentation) true = Declaration.relation false at h
  rcases h with impossible | impossible <;> cases impossible

end SHIGURE.Chapter1.CoverTransport
