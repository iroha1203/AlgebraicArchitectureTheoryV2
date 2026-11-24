import Formal.SHIGURE.Part1.Contexts

/-! # Why a declaration cover must cover the Laws

Two locally constant operations on a two-point carrier agree on the shared
sort. The composite is constant, so their local models do not extend to a
model of the omitted inverse Law.
-/

namespace SHIGURE.Chapter3.OmittedLaw

open CategoryTheory DeclarationContext

/-- The two unary symbols on the shared sort. `false` names `f` and `true` names `g`. -/
def signature : Signature where
  SortType := Unit
  Total := Bool
  totalArity _ := ⟨[()], ()⟩
  Rel := PEmpty
  relInputs r := nomatch r
  Partial := PEmpty
  partialArity p := nomatch p
  Quantity := PEmpty
  quantityArity q := nomatch q

/-- There are no partial symbols in the counterexample. -/
instance noPartial : IsEmpty signature.Partial := inferInstanceAs (IsEmpty PEmpty)

/-- Apply one of the two unary symbols to a term. -/
def applySymbol (f : Bool) (t : Term signature [()] ()) : Term signature [()] () :=
  .app (.total f) (fun i => match i with | .here => t)

/-- The graph of a unary application binds the sole argument before using the named symbol. -/
theorem applySymbol_graphAt (f : Bool) (t : Term signature [()] ())
    {Δ : List signature.SortType} (ρ : Renaming [()] Δ) (out : Var Δ ()) :
    (applySymbol f t).graphAt ρ out =
      (((t.graphAt (fun i => (ρ i).shift [()]) .here).conj .truth).conj
        (.atom (.graph (.total f) (Var.inLeft Δ) (out.shift [()])))).ex :=
  rfl

/-- The Law requires `g(f(x)) = x` at every value. -/
def inverseLaw : Law signature :=
  Law.equality (applySymbol true (applySymbol false (.var .here))) (.var .here)

/-- The presentation has one required Law. -/
def presentation : PrimitivePresentation where
  signature := signature
  laws := ⟨Unit, fun _ => inverseLaw, fun _ => .required⟩
  derived _ role := by cases role

/-- The whole presentation retains all three primitive names and the Law name. -/
def whole : DeclarationContext presentation := full presentation

/-- A local piece retains the common sort and just one named unary operation. -/
def piece (f : Bool) : DeclarationContext presentation where
  declarations := {d | d = .sort () ∨ d = .total f}
  closed kept := by
    rcases kept with rfl | rfl
    · exact Set.empty_subset _
    · rintro _ ⟨s, _, rfl⟩
      cases s
      exact Or.inl rfl

/-- Neither local piece retains a Law declaration. -/
theorem piece_omits_law (f : Bool) (name : presentation.laws.LawName) :
    Declaration.law name ∉ (piece f).declarations := by
  simp [piece]

/-- The collection covers the primitive-only context. -/
def withoutLaw : DeclarationContext presentation := union piece

/-- The two pieces are an actual cover of the primitive-only declaration context. -/
def primitiveCover : DeclarationCover withoutLaw where
  Index := Bool
  piece := piece
  subset := le_union piece
  covers := fun kept => kept

/-- The common sort is covered. -/
theorem sort_covered : Declaration.sort () ∈ withoutLaw.declarations :=
  ⟨false, Or.inl rfl⟩

/-- Both operation declarations are covered. -/
theorem symbol_covered (b : Bool) : Declaration.total b ∈ withoutLaw.declarations :=
  ⟨b, Or.inr rfl⟩

/-- The Law is not covered even though its symbols are. -/
theorem law_omitted (name : presentation.laws.LawName) : Declaration.law name ∉ withoutLaw.declarations := by
  rintro ⟨i, seen⟩
  exact piece_omits_law i name seen

/-- The well-typed input and conclusion of the omitted Law can still be evaluated. -/
theorem inverseLaw_supported : Declaration.lawBody (P := presentation) inverseLaw ⊆ withoutLaw.declarations := by
  intro d used
  cases d with
  | sort s => cases s; exact sort_covered
  | total b => exact symbol_covered b
  | relation r => exact nomatch r
  | partialOp p => exact nomatch p
  | quantity q => exact nomatch q
  | law name => exact (Declaration.law_notMem_lawBody name inverseLaw used).elim

/-- The given primitive interpretations assign the constant zero function to both symbols. -/
def constants : Structure signature where
  carrier _ := Bool
  total _ _ := false
  relation r := nomatch r
  partialDomain p := nomatch p
  partialValue p := nomatch p
  quantity q := nomatch q

/-- Either total primitive returns zero. -/
theorem constants_total (b : Bool) (e : Assignment constants.carrier ([()] : List Unit)) :
    constants.total b e = false :=
  rfl

/-- At the input one, the composite value is zero, so the required Law fails. -/
theorem constants_fail_inverseLaw : ¬ inverseLaw.Holds constants := by
  intro held
  have atOne := (Law.holds_equality_totalValue_iff _ _ constants).1 held
    (Assignment.cons true Assignment.empty)
  change false = true at atOne
  cases atOne

/-- Include each local declaration set into the context with every declaration. -/
private theorem piece_le_whole (f : Bool) : piece f ≤ whole :=
  Set.subset_univ _

/-- Compare the union of primitive declarations with the context that also retains the inverse Law. -/
private theorem withoutLaw_le_whole : withoutLaw ≤ whole :=
  Set.subset_univ _

/-- The local models evaluate the chosen constant on the entire shared Bool carrier. -/
noncomputable def localModel (f : Bool) : Models (piece f) :=
  ⟨(ContextStructure.ofStructure whole constants).restrict (piece_le_whole f), fun name =>
    (piece_omits_law f name.val.val name.property).elim⟩

/-- The exact local reducts on the common sort agree. -/
noncomputable def matching : Match piece where
  pieceModel := localModel
  overlap_eq i j := CategoryTheory.ObjectProperty.FullSubcategory.ext
    (((ContextStructure.ofStructure whole constants).restrict_comp (piece_le_whole i) (overlapLeft piece i j)).trans
      ((ContextStructure.ofStructure whole constants).restrict_comp (piece_le_whole j) (overlapRight piece i j)).symm)

/-- The primitive interpretation is a model in the context with the Law erased. -/
noncomputable def primitiveModel : Models withoutLaw :=
  ⟨(ContextStructure.ofStructure whole constants).restrict withoutLaw_le_whole,
    fun name => (law_omitted name.val.val name.property).elim⟩

/-- The primitive model restricts exactly to either local model. -/
theorem primitiveModel_restrict (i : Bool) : primitiveModel.restrict (primitiveCover.subset i) = localModel i :=
  CategoryTheory.ObjectProperty.FullSubcategory.ext
    ((ContextStructure.ofStructure whole constants).restrict_comp withoutLaw_le_whole (primitiveCover.subset i))

/-- Covering the operations and agreeing on their overlap cannot extend these local models to the Law. -/
theorem no_global_model : ¬ ∃ A : Models whole, ∀ i, A.restrict (piece_le_whole i) = matching.pieceModel i := by
  rintro ⟨A, restrictions⟩
  have same : A.restrict withoutLaw_le_whole = primitiveModel :=
    primitiveCover.models_eq_of_restrict_eq (fun i =>
      (A.restrict_comp withoutLaw_le_whole (primitiveCover.subset i)).trans
        ((restrictions i).trans (primitiveModel_restrict i).symm))
  have original : A.obj.evaluation.satisfies inverseLaw
      (fun _ h => withoutLaw_le_whole (inverseLaw_supported h)) :=
    A.satisfies_required ⟨⟨(), rfl⟩, Set.mem_univ _⟩
  have restricted := (A.obj.restrict_satisfies_iff withoutLaw_le_whole inverseLaw inverseLaw_supported).2 original
  have holds : primitiveModel.obj.evaluation.satisfies inverseLaw inverseLaw_supported :=
    same ▸ restricted
  have constantsHold := ((ContextStructure.ofStructure whole constants).restrict_satisfies_iff
    withoutLaw_le_whole inverseLaw inverseLaw_supported).1 holds
  exact constants_fail_inverseLaw ((ContextStructure.ofStructure_satisfies_iff whole constants inverseLaw
    (fun _ h => withoutLaw_le_whole (inverseLaw_supported h))).1 constantsHold)

/-- The constant-to-zero map preserves the actual primitive structure with both constant operations. -/
noncomputable def collapseStructure : ContextStructure.Hom
    (ContextStructure.ofStructure whole constants) (ContextStructure.ofStructure whole constants) where
  onSort _ kept _ := cast (selectedCarrier_kept constants.carrier kept).symm false
  relation_mem r := nomatch r
  domain_mem p := nomatch p
  graph_mem op kept e y _ := by
    cases op with
    | total f =>
      apply (ContextStructure.ofStructure_graph_iff whole constants (.total f) kept _ _).2
      rw [Structure.graph_total_iff, constants_total]
      simp only [selectedMap_apply, cast_cast]
      rfl
    | partialOp p => exact nomatch p
    | quantity q => exact nomatch q

/-- The primitive-only model has the associated genuine, non-injective endomorphism. -/
noncomputable def collapse : primitiveModel ⟶ primitiveModel :=
  ObjectProperty.homMk (collapseStructure.restrict withoutLaw_le_whole)

/-- The endomorphism sends the retained Boolean point one to zero. -/
theorem collapse_ne_id : collapse ≠ 𝟙 primitiveModel := by
  intro same
  let base := ContextStructure.ofStructure whole constants
  let equality : primitiveModel.obj.carrier () = Bool :=
    (base.restrict_carrier withoutLaw_le_whole sort_covered).trans
      (selectedCarrier_kept (U := whole) constants.carrier (withoutLaw_le_whole sort_covered))
  let one : primitiveModel.obj.carrier () := cast equality.symm true
  have h := congrArg (fun f : primitiveModel ⟶ primitiveModel =>
    cast equality (Models.onSort f () sort_covered one)) same
  have forbidden : false = true := by
    simpa only [collapse, Models.onSort, ObjectProperty.homMk_hom, ContextStructure.Hom.restrict_onSort,
      ContextStructure.Hom.restrictOnSort_apply, collapseStructure, Models.id_onSort, equality, one, selectedMap_apply,
      cast_cast] using h
  cases forbidden

/-- A nonidentity arrow is recovered from its restrictions to the genuinely split primitive cover. -/
theorem assemble_collapse : primitiveCover.assemble
    (show Match.Hom (primitiveCover.read primitiveModel) (primitiveCover.read primitiveModel) from
      primitiveCover.readFunctor.map collapse) = collapse :=
  primitiveCover.assemble_read collapse

/-- Both identity operations satisfy the retained inverse Law. -/
def identities : Structure signature :=
  { constants with total := fun _ e => e .here }

/-- The inverse Law fires with both operations interpreted as the Boolean identity. -/
theorem identities_hold_inverseLaw : inverseLaw.Holds identities := by
  apply (Law.holds_equality_totalValue_iff _ _ identities).2
  intro e
  rfl

/-- The whole presentation has a model satisfying its actual required Law. -/
noncomputable def fullModel : Models whole :=
  ⟨ContextStructure.ofStructure whole identities, fun name =>
    (ContextStructure.ofStructure_satisfies_iff whole identities inverseLaw
      (Declaration.lawBody_subset_of_mem name.property)).2 identities_hold_inverseLaw⟩

/-- A cover with a piece retaining the inverse Law assembles its family back to a model of that Law. -/
theorem glue_retained_inverseLaw :
    ((DeclarationCover.identity whole).read fullModel).glue (DeclarationCover.identity whole) = fullModel :=
  (DeclarationCover.identity whole).glue_read fullModel

/-- Raw graph data with no edges omit the output of a total operation. -/
def missingGraph : RestrictedEvaluation whole (fun _ => Bool) where
  relation _ _ _ := False
  domain _ _ _ := False
  graph _ _ _ _ := False

/-- The graph laws reject raw evaluation data missing a total output. -/
theorem missingGraph_not_structural : ¬ missingGraph.Structural := by
  intro structural
  have output := structural (.totality false) (Set.mem_univ _)
    (Assignment.cons false Assignment.empty) True.intro
  change ∃ _ : Bool, False at output
  exact output.elim (fun _ h => h)

/-- Unit supplies a different, valid carrier for the two constant operations. -/
def unitConstants : Structure signature where
  carrier _ := Unit
  total _ _ := ()
  relation r := nomatch r
  partialDomain p := nomatch p
  partialValue p := nomatch p
  quantity q := nomatch q

/-- A local model with a different interpretation of the shared sort. -/
noncomputable def unitPiece : Models (piece true) :=
  ⟨ContextStructure.ofStructure (piece true) unitConstants, fun name =>
    (piece_omits_law true name.val.val name.property).elim⟩

/-- Two valid local models fail strict matching when their shared carriers differ. -/
theorem different_carriers_no_overlap :
    (localModel false).restrict (overlapLeft piece false true) ≠
      unitPiece.restrict (overlapRight piece false true) := by
  intro same
  have shared : Declaration.sort () ∈ (inter (piece false) (piece true)).declarations := ⟨Or.inl rfl, Or.inl rfl⟩
  have left : ((localModel false).restrict (overlapLeft piece false true)).obj.carrier () = Bool :=
    ((localModel false).obj.restrict_carrier (overlapLeft piece false true) shared).trans
      (((ContextStructure.ofStructure whole constants).restrict_carrier (piece_le_whole false) shared.1).trans
        (selectedCarrier_kept (U := whole) constants.carrier (Set.mem_univ _)))
  have right : (unitPiece.restrict (overlapRight piece false true)).obj.carrier () = Unit :=
    (unitPiece.obj.restrict_carrier (overlapRight piece false true) shared).trans
      (selectedCarrier_kept (U := piece true) unitConstants.carrier shared.2)
  have both : Bool = Unit := left.symm.trans ((congrArg (fun M => M.obj.carrier ()) same).trans right)
  exact Bool.noConfusion ((Equiv.cast both).injective (Subsingleton.elim ((Equiv.cast both) false) ((Equiv.cast both) true)))

/-- On the primitive example, either piece reads the shared sort's entire arrow. -/
theorem arrow_eq_from_piece (i : Bool) (f g : primitiveModel ⟶ primitiveModel)
    (same : (res (primitiveCover.subset i)).map f = (res (primitiveCover.subset i)).map g) : f = g := by
  apply Models.hom_ext
  intro s keep x
  cases s
  let localKept : Declaration.sort () ∈ (piece i).declarations := Or.inl rfl
  let eq := primitiveModel.obj.restrict_carrier (primitiveCover.subset i) localKept
  have component := congrArg (fun h => Models.onSort h () localKept (cast eq.symm x)) same
  apply (Equiv.cast eq.symm).injective
  simpa only [res_onSort, selectedMap_apply, cast_cast, Equiv.cast_apply] using component

/-- The locally valid collapse and identity arrows do not agree on the common sort. -/
theorem different_arrows_no_match :
    ¬ ∃ f : Match.Hom (primitiveCover.read primitiveModel) (primitiveCover.read primitiveModel),
      f.pieceMap false = (res (primitiveCover.subset false)).map collapse ∧
        f.pieceMap true = 𝟙 ((primitiveCover.read primitiveModel).pieceModel true) := by
  rintro ⟨f, left, right⟩
  have a := arrow_eq_from_piece false (primitiveCover.assemble f) collapse
    ((primitiveCover.assemble_restrict f false).trans left)
  have b := arrow_eq_from_piece true (primitiveCover.assemble f) (𝟙 primitiveModel)
    ((primitiveCover.assemble_restrict f true).trans (right.trans ((res (primitiveCover.subset true)).map_id _).symm))
  exact collapse_ne_id (a.symm.trans b)

end SHIGURE.Chapter3.OmittedLaw
