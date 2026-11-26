import Formal.SHIGURE.Part1.ContextExamples
import Formal.SHIGURE.Part1.ContextReading

/-! # Local input for a declaration cover with a retained Law -/

namespace SHIGURE.Chapter3

open CategoryTheory DeclarationContext

namespace OmittedLaw

/-- The reading of the two constant operations selects the context without the inverse Law. -/
def constantsReading : Reading.{0, 0, 0, 0} where
  presentation := presentation
  structureData := constants
  observation := StateObservation.ofSort () Bool id
  context := withoutLaw
  cover := primitiveCover
  Family := Unit
  realize _ := constants
  familyObservation := none
  ValueStructure _ := Unit
  valueStructure := ()
  coefficients := none

/-- The reading of the primitive context yields its ordinary local models. -/
noncomputable def constantsReadingLocalModels : OrdinaryMatch constantsReading.cover.piece :=
  constantsReading.selectedLocalModels
    (constantsReading.selectedTheory_holds_iff.2 fun name =>
      (law_omitted name.val.val name.val.property).elim)

/-- The same underlying reading fails the inverse Law in the original full theory. -/
theorem constantsReading_ambient_fails :
    ¬ constantsReading.presentation.theory.Holds constantsReading.structureData := by
  intro holds
  exact constants_fail_inverseLaw (holds ⟨(), rfl⟩)

/-- Interpret both retained total symbols by the constant zero map on the two-point carrier. -/
private def constantOrdinary : Structure (Selected.signature whole) where
  carrier _ := Bool
  total _ _ := false
  relation r := nomatch r.val
  partialDomain p := nomatch p.val
  partialValue p := nomatch p.val
  quantity q := nomatch q.val

/-- Identify the original and selected Bool carriers without changing their state names. -/
private def alignment : Selected.CarrierEquiv whole (fun _ => Bool) constantOrdinary.carrier :=
  fun _ _ => Equiv.refl Bool

/-- The graph comparison used in Proposition 3.2 rejects the empty graph
in this example because the retained total operation returns `false`
on the input `false` in the ordinary structure. -/
theorem missingGraph_not_matching : ¬ Selected.EvaluationMatches missingGraph constantOrdinary alignment := by
  intro impossible
  let keeps : Declaration.total (P := presentation) false ∈ whole.declarations := Set.mem_univ _
  let input : Assignment (fun _ => Bool) (presentation.signature.totalArity false).inputs :=
    Assignment.cons false Assignment.empty
  let retained := Declaration.ofOperation_total_mem (P := presentation) false keeps
  apply (impossible.graph (.total false) retained input false).1
  apply (Selected.graph_select_congr constantOrdinary alignment (.total false) retained (.total ⟨false, keeps⟩)
    (Selected.operation_total (P := presentation) (U := whole) false retained) input false).2
  rw [cast_eq, Structure.graph_total_iff]
  rfl

/-- View each primitive-only piece as a subcontext of the original presentation. -/
private theorem pieces_inside (i : Bool) : piece i ≤ whole :=
  Set.subset_univ _

/-- The two ordinary local models still cannot extend across the omitted required Law. -/
theorem no_ordinary_global_model :
    ¬ ∃ A : Model (Selected.theory whole), ∀ i,
      (Selected.modelRestriction (pieces_inside i)).obj A = (OrdinaryMatch.readObj matching).pieceModel i := by
  rintro ⟨A, restricts⟩
  apply no_global_model
  refine ⟨Selected.writeModel A, fun i => ?_⟩
  have localEq := congrArg (fun B : Model (Selected.theory (piece i)) => Selected.writeModel B) (restricts i)
  rw [Selected.modelRestriction_obj, OrdinaryMatch.readObj_pieceModel] at localEq
  simpa only [Selected.write_read_model] using localEq

/-- Equality of ordinary overlap reducts detects a disagreement of retained carriers. -/
theorem different_ordinary_carriers_no_overlap :
    (Selected.modelRestriction (overlapLeft piece false true)).obj (Selected.readModel (localModel false)) ≠
    (Selected.modelRestriction (overlapRight piece false true)).obj (Selected.readModel unitPiece) := by
  intro same
  apply different_carriers_no_overlap
  have localEq := congrArg (fun B : Model (Selected.theory (inter (piece false) (piece true))) =>
    Selected.writeModel B) same
  rw [Selected.modelRestriction_obj, Selected.modelRestriction_obj] at localEq
  simpa only [Selected.write_read_model] using localEq

/-- Read the two graph models as an ordinary matching family over the primitive cover. -/
private noncomputable def ordinaryFamily : OrdinaryMatch primitiveCover.piece :=
  OrdinaryMatch.readObj (primitiveCover.read primitiveModel)

/-- The ordinary collapse and identity cannot match after identifying the local model endpoints. -/
theorem different_ordinary_arrows_no_match_heq :
    ¬ ∃ f : OrdinaryMatch.Hom ordinaryFamily ordinaryFamily,
      HEq (f.pieceMap false) ((Selected.readFunctor (piece false)).map
        ((res (primitiveCover.subset false)).map collapse)) ∧
      f.pieceMap true = 𝟙 (ordinaryFamily.pieceModel true) := by
  rintro ⟨f, left, right⟩
  let raw := primitiveCover.read primitiveModel
  have same : OrdinaryMatch.writeFunctor.obj ordinaryFamily = raw :=
    (congrArg OrdinaryMatch.writeFunctor.obj (OrdinaryMatch.readFunctor_obj raw).symm).trans
      (Functor.congr_obj OrdinaryMatch.read_comp_write raw)
  let written : raw ⟶ raw := eqToHom same.symm ≫
    OrdinaryMatch.writeFunctor.map (show ordinaryFamily ⟶ ordinaryFamily from f) ≫ eqToHom same
  apply different_arrows_no_match
  refine ⟨(show Match.Hom raw raw from written), ?_, ?_⟩
  · apply eq_of_heq
    simp only [written, Match.comp_pieceMap, Match.eqToHom_pieceMap, eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
    refine (OrdinaryMatch.writeFunctor_map_pieceMap (show ordinaryFamily ⟶ ordinaryFamily from f) false).trans ?_
    have source : ordinaryFamily.pieceModel false =
        (Selected.readFunctor (piece false)).obj ((res (primitiveCover.subset false)).obj primitiveModel) := by
      change (OrdinaryMatch.readObj raw).pieceModel false = _
      rw [OrdinaryMatch.readObj_pieceModel, primitiveCover.read_pieceModel, res_obj]
      exact (Selected.readFunctor_obj _).symm
    refine (OrdinaryMatch.map_heq_of_endpoints (Selected.writeFunctor (piece false)) source source left).trans ?_
    simpa only [Functor.comp_map, Functor.id_map] using
      Functor.hcongr_hom (Selected.read_comp_write (piece false)) ((res (primitiveCover.subset false)).map collapse)
  · apply eq_of_heq
    simp only [written, Match.comp_pieceMap, Match.eqToHom_pieceMap, eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
    refine (OrdinaryMatch.writeFunctor_map_pieceMap (show ordinaryFamily ⟶ ordinaryFamily from f) true).trans ?_
    rw [right, (Selected.writeFunctor (primitiveCover.piece true)).map_id (ordinaryFamily.pieceModel true)]
    let point := (OrdinaryMatch.writeFunctor_obj_pieceModel ordinaryFamily true).symm.trans
      (congrArg (fun M => M.pieceModel true) same)
    exact (eqToHom_heq_id_dom _ _ point).symm.trans (eqToHom_heq_id_cod _ _ point)

/-- The ordinary collapse on one piece and identity on the other cannot form a matching map. -/
theorem different_ordinary_arrows_no_match :
    ¬ ∃ f : OrdinaryMatch.Hom ordinaryFamily ordinaryFamily,
      f.pieceMap false = (Selected.readFunctor (piece false)).map
        ((res (primitiveCover.subset false)).map collapse) ∧
      f.pieceMap true = 𝟙 (ordinaryFamily.pieceModel true) := by
  rintro ⟨f, left, right⟩
  exact different_ordinary_arrows_no_match_heq ⟨f, heq_of_eq left, right⟩

end OmittedLaw

namespace RetainedLaw

open OmittedLaw (signature applySymbol constants identities)

/-- The first piece's Law forces the first operation to be the identity. -/
def identityLaw : Law signature := Law.equality (applySymbol false (.var .here)) (.var .here)

/-- The other operation does not occur in the required Law. -/
def presentation : PrimitivePresentation where
  signature := signature
  laws := ⟨Unit, fun _ => identityLaw, fun _ => .required⟩
  derived _ role := by cases role

/-- The written identity Law mentions only the first total symbol. -/
private theorem true_not_referenced :
    Declaration.total (P := presentation) true ∉ Declaration.lawBody identityLaw := by
  intro used
  simp only [identityLaw, Declaration.lawBody_eq, Law.equality_eq, Formula.termEq_eq_ex,
    Term.graph_eq_graphAt, OmittedLaw.applySymbol_graphAt, Term.graphAt_var,
    Declaration.formula_truth, Declaration.formula_ex, Declaration.formula_conj,
    Declaration.formula_atom, Declaration.atomic_eq] at used
  simp [Declaration.sorts_eq_image] at used
  erw [Declaration.atomic_graph (P := presentation) (.total false), Declaration.ofOperation_total] at used
  simp at used

/-- The left piece retains the Law, its operation and the entire common sort. -/
def left : DeclarationContext presentation where
  declarations := {d | d ≠ .total true}
  closed {a} kept := by
    intro d used forbidden
    subst d
    cases a with
    | sort _ => rw [Declaration.sort_dependencies] at used; exact used
    | total f =>
      rw [Declaration.total_dependencies, Declaration.sorts_eq_image] at used
      rcases used with ⟨s, hs, same⟩
      cases same
    | relation r => exact nomatch r
    | partialOp p => exact nomatch p
    | quantity q => exact nomatch q
    | law n =>
      exact true_not_referenced (by
        have support := Declaration.nonderived_dependencies (P := presentation) n (fun h => LawRole.noConfusion h)
        rw [support, Declaration.declaredLawSupport_of_none _ rfl] at used
        exact used)

/-- The right piece has the second operation and the same common sort. -/
def right : DeclarationContext presentation where
  declarations := {d | d = .sort () ∨ d = .total true}
  closed kept := by
    rcases kept with rfl | rfl
    · rw [Declaration.sort_dependencies]
      exact Set.empty_subset _
    · rw [Declaration.total_dependencies, Declaration.sorts_eq_image]
      rintro _ ⟨s, _, rfl⟩
      cases s
      exact Or.inl rfl

/-- The Boolean cover has the Law-bearing left piece and the operation-bearing right piece. -/
def piece : Bool → DeclarationContext presentation
  | false => left
  | true => right

/-- Both pieces are proper subcontexts, and together they cover the complete presentation. -/
def cover : DeclarationCover (full presentation) where
  Index := Bool
  piece := piece
  subset _ := Set.subset_univ _
  covers {d} _ := by
    classical
    by_cases dTrue : d = .total true
    · exact ⟨true, Or.inr dTrue⟩
    · exact ⟨false, dTrue⟩

/-- Each piece really omits a declaration of the whole presentation. -/
theorem proper (i : Bool) : cover.piece i ≠ full presentation := by
  cases i
  · intro same
    have keeps : Declaration.total true ∈ (cover.piece false).declarations :=
      same.symm ▸ Set.mem_univ _
    exact keeps rfl
  · intro same
    have keeps : Declaration.law () ∈ (cover.piece true).declarations :=
      same.symm ▸ Set.mem_univ _
    rcases keeps with h | h <;> cases h

/-- On the left the identity law holds for all Boolean assignments. -/
theorem identities_hold : identityLaw.Holds identities := by
  apply (Law.holds_equality_totalValue_iff _ _ identities).2
  intro e
  rfl

/-- Use the two supplied unary operations to build the restricted Bool structure on the local piece. -/
private def localStructure (W : DeclarationContext presentation) (kept : Declaration.sort () ∈ W.declarations)
    (value : Bool → Bool → Bool) : ContextStructure W :=
  let A : Structure signature := {constants with total := fun f e => value f (e .here)}
  { carrier := fun _ => Bool
    omitted := fun s omitted => False.elim (omitted (by cases s; exact kept))
    evaluation := RestrictedEvaluation.restrict W A
    structural := RestrictedEvaluation.restrict_structural W A }

/-- The left local model supplies its Law, and the right local model supplies a constant. -/
noncomputable def localModel : (i : Bool) → Models (piece i)
  | false => ⟨localStructure left (by intro h; cases h) (fun _ x => x), fun n =>
      (RestrictedEvaluation.satisfies_restrict_iff left identities identityLaw
        (Declaration.lawBody_subset_of_mem n.property)).2 identities_hold⟩
  | true => ⟨localStructure right (Or.inl rfl) (fun _ _ => false), fun n =>
      False.elim (by
        have kept : Declaration.law n.val.val ∈ right.declarations := n.property
        rcases kept with h | h <;> cases h)⟩

/-- The independently given models agree on their shared Boolean sort. -/
noncomputable def matching : Match cover.piece where
  pieceModel := localModel
  overlap_eq i j := by
    cases i <;> cases j
    all_goals try rfl
    all_goals
      apply CategoryTheory.ObjectProperty.FullSubcategory.ext
      refine ContextStructure.ext (by rfl) ?_
      apply RestrictedEvaluation.ext
      · intro r
        exact nomatch r
      · intro p
        exact nomatch p
      · intro op kept
        cases op with
        | total f =>
          have absent : Declaration.total f ∉ (inter left right).declarations := by
            intro h
            rcases h.2 with impossible | same
            · cases impossible
            · exact h.1 same
          first | exact (absent kept).elim | exact (absent ⟨kept.2, kept.1⟩).elim
        | partialOp p => exact nomatch p
        | quantity q => exact nomatch q

/-- The ordinary local inputs uniquely assemble to a model of the required identity Law. -/
theorem assembles_ordinary : ∃! A : Model (Selected.presentation (full presentation)).theory, ∀ i,
    (Selected.modelRestriction (cover.subset i)).obj A = (OrdinaryMatch.readObj matching).pieceModel i :=
  cover.existsUnique_ordinary_glue (OrdinaryMatch.readObj matching)

end RetainedLaw
end SHIGURE.Chapter3
