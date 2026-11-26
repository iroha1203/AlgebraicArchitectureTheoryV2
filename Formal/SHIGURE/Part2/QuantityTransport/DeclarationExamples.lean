import Formal.SHIGURE.Part2.QuantityTransport.DeclarationRestriction

/-! # Declared quantity restriction over the integers

A partial quantity is defined at one integer. Its original guard asks
whether the primitive graph has a value there. The Law uses marked total
quantities for the fixed addition and zero, and varies only the partial
quantity.
-/

namespace SHIGURE.Quantities.DeclaredRestrictionExample

open DeclarationContext

noncomputable section

private def signature : Signature where
  SortType := Unit
  Total := Unit
  Rel := Empty
  Partial := Unit
  Quantity := Bool
  totalArity _ := ⟨[], ()⟩
  relInputs r := nomatch r
  partialArity _ := ⟨[()], ()⟩
  quantityArity
    | false => ⟨[], ()⟩
    | true => ⟨[(), ()], ()⟩

private def varying : Set (QuantityDeclaration signature) := {QuantityDeclaration.partialOp ()}

private def quantity : varying := ⟨.partialOp (), Set.mem_singleton _⟩

private def application : CoefficientTerm.Application varying [()] := ⟨quantity, ⟨.var⟩⟩

private def zeroSymbol : CoefficientSymbol signature ⟨[], ()⟩ := ⟨.quantity false, rfl⟩

private def addSymbol : CoefficientSymbol signature ⟨[(), ()], ()⟩ := ⟨.quantity true, rfl⟩

private def left : CoefficientTerm varying [()] () :=
  .add addSymbol (.quantity quantity application.2) (.quantity quantity application.2)

private def right : CoefficientTerm varying [()] () := .scalar zeroSymbol

private def guard : Formula signature [()] :=
  .ex (.atom (.graph (.partialOp ()) (fun i => .there i) .here))

private def declarations : LawDeclarations signature where
  LawName := Unit
  statement _ := ⟨[()], guard, Formula.termEq left.toTerm right.toTerm⟩
  role _ := .required

private def primitive : PrimitivePresentation where
  signature := signature
  laws := declarations
  derived _ impossible := by cases impossible

private def written : DeclaredQuantityLaws primitive where
  quantities := varying
  quantityLaws := Set.univ
  valueSort _ := ()
  left _ := left
  right _ := right
  expansion _ := .original _

private def base : Structure signature where
  carrier _ := ℤ
  total _ _ := 0
  relation r := nomatch r
  partialDomain _ := {e | e .here = 2}
  partialValue _ _ := 0
  quantity
    | false, _ => 0
    | true, e => e .here + e (.there .here)

private abbrev Full := DeclarationContext.full primitive

private def ambient : ContextStructure Full := ContextStructure.ofStructure Full base

private def carrierRead : ambient.carrier () ≃ ℤ :=
  Equiv.ofBijective (selectedMap Full base.carrier () (Set.mem_univ _))
    (selectedMap_bijective (U := Full) base.carrier () (Set.mem_univ _))

private theorem domainGuard (B : RestrictedEvaluation Full ambient.carrier) (valid : B.Structural)
    (e : Assignment ambient.carrier [()]) :
    B.holds guard (Set.subset_univ _) e ↔ B.domain () (Set.mem_univ _) e := by
  change (∃ y, B.graph (.partialOp ()) (Set.mem_univ _)
      ((Assignment.cons y e).pull (fun i => .there i)) ((Assignment.cons y e) .here)) ↔ _
  simp only [Assignment.pull_cons_there, Assignment.pull_id, Assignment.cons_here]
  have structural := RestrictedEvaluation.partial_graph_valid valid () (Set.mem_univ _)
  exact ⟨fun ⟨y, h⟩ => structural.2.1 e y h, structural.2.2 e⟩

private theorem application_eq (a : CoefficientTerm.Application varying [()])
    (used : Sum.inr a ∈ left.leaves ∪ right.leaves) : a = application := by
  rcases used with (h | h) | h
  · exact Sum.inr.inj (Set.mem_singleton_iff.mp h)
  · exact Sum.inr.inj (Set.mem_singleton_iff.mp h)
  · have different : Sum.inr a = Sum.inl (⟨(), zeroSymbol⟩ : CoefficientTerm.Literal signature) :=
      Set.mem_singleton_iff.mp h
    cases different

private theorem fixedOperation (op : TotalSymbol signature) :
    op.operation ∉ QuantityDeclaration.operation '' varying := by
  rintro ⟨declared, chosen, eq⟩
  replace chosen := Set.mem_singleton_iff.mp chosen
  subst declared
  cases op <;> cases eq

private theorem addRealizes :
    addSymbol.Realizes ambient (Set.mem_univ _) (selectedMap Full base.carrier)
      (fun a => a .here + a (.there .here)) := by
  intro a
  let v := addSymbol.nativeValue ambient (Set.mem_univ _) a
  have actualGraph := CoefficientSymbol.nativeValue_graph (P := primitive) (U := Full) addSymbol ambient (Set.mem_univ _) a
  have graph : ambient.evaluation.graph (.quantity true) (Set.mem_univ _) a v := actualGraph
  have actual := (ContextStructure.ofStructure_graph_iff Full base (.quantity true)
    (Set.mem_univ _) a v).1 graph
  rw [Structure.graph_quantity_iff] at actual
  exact actual.symm

private def interpretation : written.Interpretation (k := ℤ) ambient where
  read := selectedMap Full base.carrier
  lawRead l := selectedMap_bijective (U := Full) base.carrier (written.valueSort l.val) _
  quantityRead j := selectedMap_bijective (U := Full) base.carrier j.val.val.operation.arity.output _
  totalDomain _ := Set.univ
  arithmetic l a used := by
    have h : a = .add addSymbol := by
      rcases used with (atHead | rest) | rest
      · exact Set.mem_singleton_iff.mp atHead
      · rcases rest with h | h <;> exact False.elim h
      · exact False.elim rest
    subst a
    exact addRealizes
  fixedArithmetic l a used := by
    cases a with
    | add op | neg op | mul op => exact fixedOperation op.symbol
  fixedLiteral _ a := fixedOperation a.val.2.symbol
  value l e a := by
    have actual := application_eq a.val a.property
    obtain ⟨stored, used⟩ := a
    change stored = application at actual
    subst stored
    exact ⟨e.val, (domainGuard ambient.evaluation ambient.structural e.val).1 e.property⟩
  evaluates l e a s i := by
    have actual := application_eq a.val a.property
    obtain ⟨stored, used⟩ := a
    change stored = application at actual
    subst stored
    change ambient.evaluation.holds (Term.var i).graph _ (Assignment.cons (e.val i) e.val)
    exact rfl
  inputIndependent _ B same e :=
    (domainGuard ambient.evaluation ambient.structural e).trans
      ((same.domain () (Set.mem_univ _) e).trans (domainGuard B same.structural e).symm)
  argumentIndependent l B same e a s i := by
    have actual := application_eq a.val a.property
    obtain ⟨stored, used⟩ := a
    change stored = application at actual
    subst stored
    exact rfl

private def law : written.KeptLaw Full :=
  ⟨⟨⟨(), rfl⟩, Set.mem_univ _⟩, Set.mem_univ _⟩

private def input : written.lawInput ambient law := by
  let e := Assignment.cons (carrierRead.symm 2) Assignment.empty
  refine ⟨e, (domainGuard ambient.evaluation ambient.structural e).2 ?_⟩
  change mapAssignment (selectedMap Full base.carrier)
    (operationInputs (.partialOp ()) (Set.mem_univ _)) e ∈ base.partialDomain ()
  change carrierRead (carrierRead.symm 2) = 2
  exact carrierRead.apply_symm_apply 2

private def zeroLeaf : written.UsedLiteral law.val :=
  ⟨⟨(), zeroSymbol⟩, Or.inr (Set.mem_singleton _)⟩

private theorem literal_zero : interpretation.literalValue law zeroLeaf = 0 := by
  let v := zeroSymbol.nativeValue ambient (Set.mem_univ _) Assignment.empty
  have actualGraph := CoefficientSymbol.nativeValue_graph (P := primitive) (U := Full) zeroSymbol ambient
    (Set.mem_univ _) Assignment.empty
  have graph : ambient.evaluation.graph (.quantity false) (Set.mem_univ _) Assignment.empty v := actualGraph
  have actual := (ContextStructure.ofStructure_graph_iff Full base (.quantity false)
    (Set.mem_univ _) Assignment.empty v).1 graph
  rw [Structure.graph_quantity_iff] at actual
  exact actual.symm

/-- The original existential guard depends only on the fixed domain, even though
its written formula mentions the varying value graph. -/
theorem guard_reads_fixed_domain (q : interpretation.presentation.Candidate ℤ)
    (e : Assignment ambient.carrier [()]) :
    (interpretation.candidateStructure q).evaluation.holds guard (Set.subset_univ _) e ↔
      ambient.evaluation.domain () (Set.mem_univ _) e :=
  (domainGuard _ (interpretation.candidateStructure q).structural e).trans
    ((interpretation.candidateStructure_sameState q).domain () (Set.mem_univ _) e).symm

/-- The same guard genuinely refers to the varying graph in its written syntax. -/
theorem guard_mentions_varying_graph :
    ¬ StateFormula (QuantityDeclaration.operation '' varying) guard := by
  change ¬ (Operation.partialOp () ∉ QuantityDeclaration.operation '' varying)
  exact fun h => h ⟨.partialOp (), Set.mem_singleton _, rfl⟩

/-- The candidate with value zero satisfies the original Law on the entire fixed domain. -/
theorem candidate_zero_holds :
    (interpretation.candidateStructure (fun _ _ => (0 : ℤ))).evaluation.satisfies
      (primitive.theory.law law.val.val) (Declaration.lawBody_subset_of_mem law.property) := by
  apply (interpretation.candidate_satisfies_iff law _).2
  intro e
  rw [Presentation.evaluate_residual]
  change (0 + 0 : ℤ) - algebraMap ℤ ℤ (interpretation.literalValue law zeroLeaf) = 0
  rw [literal_zero, map_zero, add_zero, sub_zero]

/-- The candidate with value one fails the original declared Law at its actual input. -/
theorem candidate_one_fails :
    ¬ (interpretation.candidateStructure (fun _ _ => (1 : ℤ))).evaluation.satisfies
      (primitive.theory.law law.val.val) (Declaration.lawBody_subset_of_mem law.property) := by
  intro held
  have atInput := (interpretation.candidate_satisfies_iff law (fun _ _ => (1 : ℤ))).1 held input
  rw [Presentation.evaluate_residual] at atInput
  change (1 + 1 : ℤ) - algebraMap ℤ ℤ (interpretation.literalValue law zeroLeaf) = 0 at atInput
  rw [literal_zero, map_zero] at atInput
  norm_num at atInput

end

end SHIGURE.Quantities.DeclaredRestrictionExample
