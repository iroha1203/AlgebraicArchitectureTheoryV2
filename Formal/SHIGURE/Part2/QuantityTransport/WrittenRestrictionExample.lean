import Formal.SHIGURE.Part2.QuantityTransport.WrittenRestriction

/-! # Coefficient literals over a one-point state

A singleton state provides the argument of three scalar quantities. The
required equations at that input are `q₀(x) = 0` and `q₁(x) = 1`.
The third equation has an empty designated input set, so the third
quantity is free. The reduct forgets that quantity, its equation and
the unused total state operation.
-/

namespace SHIGURE.Quantities.WrittenRestrictionExample

open DeclarationContext WrittenLaws.DeclarationSelection

noncomputable section

private def signature : Signature where
  SortType := Unit
  Total := Unit
  Rel := Empty
  Partial := Empty
  Quantity := Empty
  totalArity _ := ⟨[()], ()⟩
  relInputs r := nomatch r
  partialArity p := nomatch p
  quantityArity q := nomatch q

private def primitive : PrimitivePresentation where
  signature := signature
  laws :=
    { LawName := Empty
      statement n := nomatch n
      role n := nomatch n }
  derived none _ := nomatch none

private def written : WrittenLaws ℤ signature where
  Quantity := Fin 3
  domainContext _ := [()]
  Law := Fin 3
  inputContext _ := [()]
  Occurrence _ := Bool
  application l useThird := ⟨if useThird then (2 : Fin 3) else l, ⟨.var⟩⟩
  left _ := .quantity false
  right l := .scalar l.val

private abbrev Full := DeclarationContext.full primitive

private def retainedState : DeclarationContext primitive where
  declarations := {Declaration.sort ()}
  closed {a} ha := by
    have equal : a = Declaration.sort () := Set.mem_singleton_iff.mp ha
    subst a
    exact Set.empty_subset _

private def complete : WrittenLaws.DeclarationSelection (P := primitive) written where
  context := Full
  quantities := Set.univ
  laws := Set.univ
  domainSorts _ := Set.subset_univ _
  inputSorts _ := Set.subset_univ _
  applicationKept _ _ := Set.mem_univ _
  termKept _ _ := by
    intro s i d hd
    exact Set.mem_univ _

private theorem unitSorts : Declaration.sorts (P := primitive) [()] ⊆ retainedState.declarations := by
  rintro _ ⟨s, _, rfl⟩
  cases s
  rfl

private def retained : WrittenLaws.DeclarationSelection (P := primitive) written where
  context := retainedState
  quantities := {j | j.val < 2}
  laws := {l | l.val < 2}
  domainSorts _ := unitSorts
  inputSorts _ := unitSorts
  applicationKept {l} h a := by
    have used := a.property
    change a.val ∈ ({false} : Set Bool) ∪ ∅ at used
    have occurrence : a.val = false := by simpa using used
    change (written.application l a.val).1.val < 2
    rw [occurrence]
    exact h
  termKept _ _ := by
    intro s i
    change Declaration.termContext (Term.var (sig := signature) i) ≤ retainedState
    rw [Declaration.termContext_le_iff, Declaration.formulaSupport_eq]
    exact Set.union_subset (Declaration.sorts_cons_subset (by cases s; rfl) unitSorts) (Set.empty_subset _)

private def inclusion : Inclusion retained complete :=
  ⟨fun _ _ => Set.mem_univ _, Set.subset_univ _, Set.subset_univ _⟩

private def state : Structure signature where
  carrier _ := PUnit
  total _ xs := xs .here
  relation r := nomatch r
  partialDomain p := nomatch p
  partialValue p := nomatch p
  quantity q := nomatch q

private def ambient : ContextStructure Full := ContextStructure.ofStructure Full state

private def reading : complete.Interpretation ambient where
  domain _ := Set.univ
  input l := fun _ => l.val.val < 2
  value _ e _ := ⟨e.val, Set.mem_univ _⟩
  argument _ _ _ _ _ := rfl

private def statePoint : Assignment ambient.carrier [()] :=
  Assignment.cons
    ((Equiv.ofBijective (selectedMap Full state.carrier () (Set.mem_univ _))
      (selectedMap_bijective (U := Full) state.carrier () (Set.mem_univ _))).symm PUnit.unit)
    Assignment.empty

private def candidate (a : ℤ) : reading.presentation.Candidate ℤ :=
  fun j _ => if j.val.val < 2 then j.val.val else a

private def third : complete.quantities := ⟨(2 : Fin 3), Set.mem_univ _⟩

/-- The third scalar can take any value since its equation has no designated inputs. -/
theorem arbitrary_third_quantity (a : ℤ) :
    ∃ q : reading.presentation.Model ℤ, q.val third ⟨statePoint, Set.mem_univ _⟩ = a := by
  refine ⟨⟨candidate a, ?_⟩, ?_⟩
  · intro l e
    have atInput : l.val.val < 2 := e.property
    change (if l.val.val < 2 then (l.val.val : ℤ) else a) = algebraMap ℤ ℤ l.val.val
    simp [atInput]
  · change (if 2 < 2 then (2 : ℤ) else a) = a
    simp

/-- The retained literal 1 still excludes the all-zero candidate after the actual state reduct. -/
theorem retained_one_rejects_zero :
    ¬ (reading.restrict inclusion).presentation.Holds (R := ℤ) (fun _ _ => 0) := by
  intro holds
  let l : retained.laws := ⟨(1 : Fin 3), by change 1 < 2; decide⟩
  let e := ambient.restrictAssignmentEquiv inclusion.context (retained.inputSorts l.property)
  let x : (reading.restrict inclusion).input l := ⟨e.symm statePoint, by change 1 < 2; decide⟩
  have rejected := holds l x
  change (0 : ℤ) = algebraMap ℤ ℤ 1 at rejected
  exact zero_ne_one (rejected.trans (map_one _))

/-- No retained coordinate is sent to the third quantity. -/
theorem third_quantity_forgotten :
    ¬ ∃ j : retained.quantities, (reading.lawMap inclusion).name j = third := by
  rintro ⟨j, equal⟩
  have bound : j.val.val < 2 := j.property
  have tag := congrArg (fun q : complete.quantities => q.val.val) equal
  change j.val.val = 2 at tag
  exact (Nat.ne_of_lt bound) tag

/-- The comparison for the two retained literal equations allows every commutative coefficient algebra. -/
theorem literal_restriction_baseChange (R : Type) [CommRing R] [Algebra ℤ R] :
    let F := (reading.restrict inclusion).presentation
    let ι := reading.lawMap inclusion
    (baseChangeQuotient (R := ℤ) R reading.presentation.residualIdeal).symm.toAlgHom.comp
        (ι.extendedEquationMap R) =
      (ι.extendedLawMap R).comp (baseChangeQuotient (R := ℤ) R F.residualIdeal).symm.toAlgHom :=
  reading.lawMap_baseChange inclusion R

end

end SHIGURE.Quantities.WrittenRestrictionExample
