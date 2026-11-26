import Formal.SHIGURE.Part2.QuantityTransport.DeclarationRestriction
import Mathlib.Data.ZMod.Basic

/-! # Reading a coefficient from a registered input

The registered equation compares the native values of a quantity and a
fixed state operation. Both read as scalars on the candidate
representatives `some r`. The original state has an additional native
value `none`, which the candidate encoding never uses.
-/

namespace SHIGURE.Quantities.CoefficientInputExample

open DeclarationContext

noncomputable section

/-- Coefficients and the input variable live in the three-element field. -/
private abbrev Scalar := ZMod 3

/-- The fixed embedding and the varying quantity both return the native result sort. -/
private def signature : Signature where
  SortType := Bool
  Total := Unit
  Rel := Empty
  Partial := Empty
  Quantity := Unit
  totalArity _ := ⟨[false], true⟩
  relInputs r := nomatch r
  partialArity p := nomatch p
  quantityArity _ := ⟨[false], true⟩

/-- The quantity has a designated coordinate at every input. -/
private def varying : Set (QuantityDeclaration signature) := {.total ()}

/-- The only varying operation has this declared name. -/
private def quantityName : varying := ⟨.total (), Set.mem_singleton _⟩

/-- The sole argument of both declared operations is the source variable. -/
private def stateVariable : Term signature [false] false := .var .here

/-- The left side reads the actual varying quantity. -/
private def left : CoefficientTerm varying [false] true := .quantity quantityName ⟨.var⟩

/-- The state term embeds the input in the native result carrier. -/
private def embedTerm : Term signature [false] true := Term.app (.total ()) (fun i => .var i)

/-- The right side reads a fixed coefficient from the state term on the input. -/
private def right : CoefficientTerm varying [false] true := .scalar embedTerm

/-- One registered source law covers all inputs. -/
private def equation : OrderedEquation signature :=
  ⟨[false], true, .truth, left.toTerm, right.toTerm⟩

/-- The presentation registers the original typed pair. -/
private def primitive : PrimitivePresentation where
  signature := signature
  laws := ⟨Unit, fun _ => equation.toLaw, fun _ => .required⟩
  otherOrderedEquation _ := some ⟨equation.write, rfl⟩
  derived _ impossible := by cases impossible

/-- Compile the registered syntax while retaining the required Law's name. -/
private def written : DeclaredQuantityLaws primitive where
  quantities := varying
  quantityLaws := Set.univ
  valueSort _ := true
  left _ := left
  right _ := right
  expansion _ := .original _
  registeredEquation l registered attached := by
    cases l.val.val
    cases Option.some.inj attached
    rfl

/-- The result sort has one more value than the coefficient sort. -/
private abbrev carrier : Bool → Type
  | false => Scalar
  | true => Option Scalar

/-- The fixed embedding returns `some` and the starting native quantity returns `none`. -/
private def base : Structure signature where
  carrier := carrier
  total _ args := some (args .here)
  relation r := nomatch r
  partialDomain p := nomatch p
  partialValue p := nomatch p
  quantity _ _ := none

/-- The example starts in the full declaration context. -/
private abbrev Full := DeclarationContext.full primitive

/-- The source evaluates the actual typed declarations. -/
private def ambient : ContextStructure Full := ContextStructure.ofStructure Full base

/-- Every term in the example is supported by the full context. -/
private def supported {Γ : List signature.SortType} {s : signature.SortType}
    (t : Term signature Γ s) : Full.TermIn Γ s := ⟨t, fun _ _ => Set.mem_univ _⟩

/-- Read the underlying carrier value of a retained term. -/
private def readCarrier (s : signature.SortType) : ambient.carrier s ≃ carrier s :=
  Equiv.ofBijective (selectedMap Full base.carrier s (Set.mem_univ _))
    (selectedMap_bijective (U := Full) base.carrier s (Set.mem_univ _))

/-- On representatives the result reads its scalar. The extra point has a default reading. -/
private def read (s : signature.SortType) (x : ambient.carrier s) : Scalar :=
  match s with
  | false => readCarrier false x
  | true => (readCarrier true x).getD 0

/-- The selected quantity uses the full argument set of its native graph. -/
private def appliedQuantity : written.KeptQuantity Full := ⟨quantityName, Set.mem_univ _⟩

/-- The Law refers to the actual selected quantity in its left term. -/
private theorem quantity_relevant (l : written.KeptLaw Full) :
    Declaration.ofOperation appliedQuantity.val.val.operation ∈ Declaration.lawBody (primitive.theory.law l.val.val) := by
  apply Or.inr
  change Declaration.ofOperation (P := primitive) (.quantity ()) ∈ Declaration.formula
    (Formula.termEq left.toTerm embedTerm)
  rw [Formula.termEq_eq_ex, Declaration.formula_ex, Declaration.formula_conj]
  exact Or.inr (Or.inl (Selected.termReferences_subset_graph (P := primitive) left.toTerm
    (Or.inl (Set.mem_singleton _))))

/-- The fixed embedding's native result is the representative of the state input. -/
private theorem embed_read (B : RestrictedEvaluation Full ambient.carrier)
    (same : written.SameDeclarationState ambient (fun _ => Set.univ) B)
    (e : Assignment ambient.carrier [false]) (y : ambient.carrier true)
    (eval : B.holds embedTerm.graph (Set.subset_univ _) (Assignment.cons y e)) :
    readCarrier true y = some (read false (e .here)) := by
  let C : ContextStructure Full := ⟨ambient.carrier, ambient.omitted, B, same.structural⟩
  obtain ⟨args, each, graph⟩ := (C.evaluates_app_iff (.total ()) (fun i => .var i)
    (supported embedTerm) rfl e (Set.mem_univ _) y).1 eval
  have sameArgs : args = e := by
    apply Assignment.ext
    intro s i
    obtain ⟨_, atVar⟩ := each i
    exact C.evaluates_unique (supported (.var i)) e atVar rfl
  have fixed : Operation.total (sig := signature) () ∉ QuantityDeclaration.operation '' varying := by
    rintro ⟨j, chosen, equal⟩
    cases Set.mem_singleton_iff.mp chosen
    cases equal
  have actual := (ContextStructure.ofStructure_graph_iff Full base (.total ())
    (Set.mem_univ _) e y).1 ((same.graph (.total ()) fixed (Set.mem_univ _) e y).2 (sameArgs ▸ graph))
  rw [Structure.graph_total_iff] at actual
  exact actual.symm

/-- The fixed state term is defined at every input. -/
private theorem embed_defined (C : ContextStructure Full) (e : Assignment C.carrier [false]) :
    ∃ y, C.evaluates (supported embedTerm) e y := by
  obtain ⟨z, graph⟩ := (C.total_graph_valid () (Set.mem_univ _)).2 e
  exact ⟨z, C.evaluates_app_of_graph (.total ()) (fun i => .var i) (supported embedTerm) rfl e e
    (fun i => ⟨(supported (.var i)).property, rfl⟩) (Set.mem_univ _) z graph⟩

/-- The quantity side has a native value at every input. -/
private theorem quantity_defined (C : ContextStructure Full) (e : Assignment C.carrier [false]) :
    ∃ y, C.evaluates (supported left.toTerm) e y := by
  obtain ⟨z, graph⟩ := (C.quantity_graph_valid () (Set.mem_univ _)).2 e
  exact ⟨z, C.evaluates_app_of_graph (.quantity ()) (fun i => .var i) (supported left.toTerm) rfl e e
    (fun i => ⟨(supported (.var i)).property, rfl⟩) (Set.mem_univ _) z graph⟩

/-- The only coefficient occurrence is the actual embedding of the input. -/
private theorem coefficient_eq (l : written.KeptLaw Full) (a : written.UsedCoefficient l.val) :
    a.val = ⟨true, embedTerm⟩ := by
  have used := a.property
  change Sum.inl a.val ∈ left.leaves ∪ right.leaves at used
  simpa [left, right, CoefficientTerm.leaves] using used

/-- The only quantity occurrence uses the original variable. -/
private theorem application_eq (l : written.KeptLaw Full) (a : written.UsedApplication l.val) :
    a.val = ⟨quantityName, ⟨.var⟩⟩ := by
  have used := a.property
  change Sum.inr a.val ∈ left.leaves ∪ right.leaves at used
  simpa [left, right, CoefficientTerm.leaves] using used

/-- Choose the `some` encoding explicitly for the native graph of every scalar candidate. -/
private def interpretation : written.Interpretation (k := Scalar) ambient where
  read s _ := read s
  selectedDomain _ := Set.univ
  quantityOutput j _ r := by
    rcases j with ⟨⟨name, _⟩, _⟩
    cases name with
    | total _ => exact (readCarrier true).symm (some r)
    | partialOp p => nomatch p
  quantityOutput_read j _ r := by
    rcases j with ⟨⟨name, _⟩, _⟩
    cases name with
    | total _ =>
      change (readCarrier true ((readCarrier true).symm (some r))).getD 0 = r
      rw [(readCarrier true).apply_symm_apply]
      rfl
    | partialOp p => nomatch p
  lawRead l e B same represents := by
    let C : ContextStructure Full := ⟨ambient.carrier, ambient.omitted, B, same.structural⟩
    have leftRead (y : ambient.carrier true) (held : C.evaluates (supported left.toTerm) e.val y) :
        readCarrier true y = some (read true y) := by
      obtain ⟨r, graph⟩ := represents appliedQuantity (quantity_relevant l) ⟨e.val, Set.mem_univ _⟩
      have expected : C.evaluates (supported left.toTerm) e.val ((readCarrier true).symm (some r)) :=
        C.evaluates_app_of_graph (.quantity ()) (fun i => .var i) _ rfl e.val e.val
          (fun i => ⟨(supported (.var i)).property, rfl⟩) (Set.mem_univ _) _ graph
      have native := C.evaluates_unique (supported left.toTerm) e.val held expected
      rw [native]
      change readCarrier true ((readCarrier true).symm (some r)) =
        some ((readCarrier true ((readCarrier true).symm (some r))).getD 0)
      rw [(readCarrier true).apply_symm_apply]
      rfl
    have rightRead (y : ambient.carrier true) (held : C.evaluates (supported right.toTerm) e.val y) :
        readCarrier true y = some (read true y) := by
      have native := embed_read B same e.val y held
      change readCarrier true y = some ((readCarrier true y).getD 0)
      rw [native]
      rfl
    intro x hx y hy equal
    exact (readCarrier true).injective
      ((hx.elim (leftRead x) (rightRead x)).trans ((congrArg some equal).trans
        (hy.elim (leftRead y) (rightRead y)).symm))
  arithmeticAt l a _ _ _ _ _ _ _ _ := by
    have used := a.property
    change a.val ∈ left.arithmeticApplications ∪ right.arithmeticApplications at used
    simp [left, right, CoefficientTerm.arithmeticApplications] at used
  coefficientDefined l a e := by
    obtain ⟨a, used⟩ := a
    have eq := coefficient_eq l ⟨a, used⟩
    change a = ⟨true, embedTerm⟩ at eq
    subst a
    exact embed_defined ambient e.val
  coefficientIndependent l a e B same _ x y original replacement := by
    obtain ⟨a, used⟩ := a
    have eq := coefficient_eq l ⟨a, used⟩
    change a = ⟨true, embedTerm⟩ at eq
    subst a
    have old := embed_read ambient.evaluation (DeclaredQuantityLaws.SameDeclarationState.refl written ambient _)
      e.val x original
    have new := embed_read B same e.val y replacement
    exact congrArg (fun z : Option Scalar => z.getD 0) (new.trans old.symm)
  value l e a := by
    obtain ⟨a, used⟩ := a
    have eq := application_eq l ⟨a, used⟩
    change a = ⟨quantityName, ⟨.var⟩⟩ at eq
    subst a
    exact ⟨e.val, Set.mem_univ _⟩
  argumentState l e a := by
    obtain ⟨a, used⟩ := a
    have eq := application_eq l ⟨a, used⟩
    change a = ⟨quantityName, ⟨.var⟩⟩ at eq
    subst a
    intro _ i
    cases i with
    | here => rfl
    | there i => nomatch i
  inputIndependent _ _ _ _ _ := Iff.rfl
  argumentIndependent l _ _ _ e a := by
    obtain ⟨a, used⟩ := a
    have eq := application_eq l ⟨a, used⟩
    change a = ⟨quantityName, ⟨.var⟩⟩ at eq
    subst a
    intro _ i
    cases i with
    | here => rfl
    | there i => nomatch i
  definedSides _ e B same _ :=
    let C : ContextStructure Full := ⟨ambient.carrier, ambient.omitted, B, same.structural⟩
    ⟨quantity_defined C e.val, embed_defined C e.val⟩

/-- There is no globally injective reading of this native equality carrier. -/
theorem no_global_read : ¬ ∃ f : ambient.carrier true → Scalar, Function.Injective f := by
  rintro ⟨f, injective⟩
  let g : Option Scalar → Scalar := f ∘ (readCarrier true).symm
  have bound := Fintype.card_le_of_injective g (injective.comp (readCarrier true).symm.injective)
  norm_num [Scalar] at bound

/-- The coordinate at the input uses the original assignment. -/
private def atInput {l : written.KeptLaw Full} (e : written.lawInput ambient l) :
    interpretation.domain appliedQuantity := ⟨e.val, Set.mem_univ _⟩

/-- The actual registered Law holds exactly when the candidate equals the input. -/
theorem scalar_input_law
    (l : written.KeptLaw Full) (e : written.lawInput ambient l) (q : interpretation.presentation.Candidate Scalar) :
    (interpretation.candidateStructure q).evaluation.holds (primitive.theory.law l.val.val).conclusion
        (lawConclusionSupport (Declaration.lawBody_subset_of_mem l.property)) e.val ↔
      q appliedQuantity (atInput e) = read false (e.val .here) := by
  rw [interpretation.candidate_conclusion_iff l e q, Presentation.evaluate_residual]
  let coefficient : written.UsedCoefficient l.val := ⟨⟨true, embedTerm⟩, by
    change Sum.inl ⟨true, embedTerm⟩ ∈ left.leaves ∪ right.leaves
    simp [left, right, CoefficientTerm.leaves]⟩
  obtain ⟨z, held⟩ := embed_defined ambient e.val
  have value := interpretation.coefficientValue_eq_of_evaluates l e coefficient z held
  have native := embed_read ambient.evaluation (DeclaredQuantityLaws.SameDeclarationState.refl written ambient _)
    e.val z held
  change interpretation.coefficientValue l e coefficient = (readCarrier true z).getD 0 at value
  rw [native] at value
  change q appliedQuantity (atInput e) - interpretation.coefficientValue l e coefficient = 0 ↔ _
  rw [value]
  exact sub_eq_zero

/-- Reading the input at the original position gives a solution on all inputs. -/
private def identityCandidate : interpretation.presentation.Candidate Scalar
  | ⟨⟨.total _, _⟩, _⟩, a => read false (a.val .here)
  | ⟨⟨.partialOp p, _⟩, _⟩, _ => nomatch p

/-- The registered input equation has a native solution. -/
theorem identity_candidate_satisfies (l : written.KeptLaw Full) :
    (interpretation.candidateStructure identityCandidate).evaluation.satisfies (primitive.theory.law l.val.val)
      (Declaration.lawBody_subset_of_mem l.property) := by
  intro a guard
  exact (scalar_input_law l ⟨a, guard⟩ identityCandidate).2 rfl

/-- The sole required Law is retained by the full context. -/
private def exampleLaw : written.KeptLaw Full :=
  ⟨⟨⟨(), rfl⟩, Set.mem_univ _⟩, Set.mem_univ _⟩

/-- The scalar input zero as an assignment. -/
private def zeroInput : written.lawInput ambient exampleLaw :=
  ⟨Assignment.cons ((readCarrier false).symm 0) Assignment.empty, trivial⟩

/-- The original state itself may have native values outside the chosen scalar encoding. -/
theorem original_quantity_outside_representation :
    ¬ written.RepresentsLaw ambient interpretation.quantityOutput exampleLaw ambient.evaluation := by
  intro represents
  obtain ⟨r, graph⟩ := represents appliedQuantity (quantity_relevant exampleLaw) (atInput zeroInput)
  have original := (ContextStructure.ofStructure_graph_iff Full base (.quantity ()) (Set.mem_univ _)
    zeroInput.val ((readCarrier true).symm (some r))).1 graph
  rw [Structure.graph_quantity_iff] at original
  change none = readCarrier true ((readCarrier true).symm (some r)) at original
  rw [(readCarrier true).apply_symm_apply] at original
  cases original

/-- A constant shift breaks the very same native equation. -/
theorem shifted_candidate_fails :
    ¬ (interpretation.candidateStructure (fun j a => identityCandidate j a + 1)).evaluation.satisfies
      (primitive.theory.law exampleLaw.val.val) (Declaration.lawBody_subset_of_mem exampleLaw.property) := by
  intro holds
  have evaluated := (scalar_input_law exampleLaw zeroInput _).1 (holds zeroInput.val zeroInput.property)
  change readCarrier false ((readCarrier false).symm 0) + 1 = readCarrier false ((readCarrier false).symm 0) at evaluated
  simp at evaluated

end

end SHIGURE.Quantities.CoefficientInputExample
