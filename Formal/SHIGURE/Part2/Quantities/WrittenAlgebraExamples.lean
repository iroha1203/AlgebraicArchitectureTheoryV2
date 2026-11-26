import Formal.SHIGURE.Part2.Quantities.AlgebraExample
import Formal.SHIGURE.Part2.Quantities.WrittenModels

/-!
# Written state terms in the algebra and module examples

Example 5.6 starts with the actual state operations. A scalar equation is
indexed by its coefficient, so each instance has a fixed written right
side. A unary quantity domain is identified with the state carrier by
reading its single entry.
-/

universe u

noncomputable section

namespace SHIGURE.Quantities

/-- The algebra and module examples each have a single state sort. -/
private abbrev StateSort := PUnit.{u + 1}

/-- The sort accepted and returned by each of the state operations. -/
private abbrev stateSort : StateSort := PUnit.unit

/-- A one-sorted state signature with the specified total operations. -/
private def operationSignature {O : Type u} (arity : O → List StateSort) : Signature.{u} where
  SortType := StateSort
  Total := O
  Rel := PEmpty
  Partial := PEmpty
  Quantity := PEmpty
  totalArity o := ⟨arity o, stateSort⟩
  relInputs := PEmpty.elim
  partialArity := PEmpty.elim
  quantityArity := PEmpty.elim

/-- All declared state operations in these examples are total. -/
local instance {O : Type u} {arity : O → List StateSort} : IsEmpty (operationSignature arity).Partial :=
  ⟨PEmpty.elim⟩

/-- Apply the declared operation to the variables of its full argument context. -/
private def operationTerm {O : Type u} {arity : O → List StateSort} (o : O) :
    Term (operationSignature arity) (arity o) stateSort :=
  Term.app (sig := operationSignature arity) (.total o) (fun i => Term.var i)

/-- Supply the one argument of a unary quantity application. -/
private def unaryArgument {sig : Signature.{u}} {Γ : List sig.SortType} {s : sig.SortType}
    (t : Term sig Γ s) : Substitution sig [s] Γ :=
  ⟨Term.argsCons t Term.argsNil⟩

/-- In these examples the full tuple domains are allowed and every state term is total. -/
private def totalInterpretation {k : Type u} {sig : Signature.{u}} [IsEmpty sig.Partial]
    (laws : WrittenLaws k sig) (A : Structure sig) : laws.Interpretation A where
  domain _ := Set.univ
  input _ := Set.univ
  defined l e a := fun i =>
    ⟨_, ((laws.application l a).2 i).evaluates_totalValue A e.val⟩
  inDomain _ _ _ := Set.mem_univ _

/-- The value read from the argument substitution is the value of the declared state term. -/
private theorem unaryArgument_value {sig : Signature.{u}} [IsEmpty sig.Partial] {Γ : List sig.SortType}
    {s : sig.SortType} (A : Structure sig) (t : Term sig Γ s) (e : (unaryArgument t).domain A) :
    (unaryArgument t).value A e (.here : Var [s] s) = t.totalValue A e.val := by
  apply t.evaluates_unique A e.val
  · exact (unaryArgument t).evaluatesAt_value A e (.here : Var [s] s)
  · exact t.evaluates_totalValue A e.val

/-- The full unary domain is in bijection with the given state values. -/
private def unaryDomainEquiv {sig : Signature.{u}} (A : Structure sig) (s : sig.SortType) :
    {x : Assignment A.carrier [s] // x ∈ (Set.univ : Set (Assignment A.carrier [s]))} ≃ A.carrier s where
  toFun x := x.val .here
  invFun x := ⟨Assignment.cons x Assignment.empty, Set.mem_univ _⟩
  left_inv x := by
    apply Subtype.ext
    apply Assignment.ext
    intro t i
    cases i with
    | here => rfl
    | there i => exact nomatch i
  right_inv _ := rfl

/-- The operation symbols and fixed Law instances for the algebra in Example 5.6. -/
inductive AlgebraStateLaw (k : Type u)
  /-- Addition in the fixed algebra. -/
  | add
  /-- Multiplication in the fixed algebra. -/
  | mul
  /-- The fixed unit. -/
  | one
  /-- The fixed image of one base coefficient. -/
  | scalar (a : k)

/-- Addition and multiplication take two states, while constants take no state argument. -/
private def algebraArity {k : Type u} : AlgebraStateLaw k → List StateSort
  | .add | .mul => [stateSort, stateSort]
  | .one | .scalar _ => []

/-- The fixed state operations are the actual operations of the algebra. -/
private def algebraState (k B : Type u) [CommRing k] [CommRing B] [Algebra k B] :
    Structure (operationSignature (algebraArity (k := k))) where
  carrier _ := B
  total
    | .add, x => x .here + x (.there .here)
    | .mul, x => x .here * x (.there .here)
    | .one, _ => 1
    | .scalar a, _ => algebraMap k B a
  relation r := PEmpty.elim r
  partialDomain p := PEmpty.elim p
  partialValue p := PEmpty.elim p
  quantity q := PEmpty.elim q

/-- The written algebra Laws with one fixed scalar equation for each coefficient. -/
def writtenAlgebraLaws (k : Type u) [CommRing k] : WrittenLaws k (operationSignature (algebraArity (k := k))) where
  Quantity := PUnit
  domainContext _ := [stateSort]
  Law := AlgebraStateLaw k
  inputContext := algebraArity
  Occurrence l := Option (Var (algebraArity l) stateSort)
  application l a := ⟨PUnit.unit, unaryArgument (a.elim (operationTerm (arity := algebraArity) l) (fun i => .var i))⟩
  left _ := .quantity none
  right
    | .add => .add (.quantity (some .here)) (.quantity (some (.there .here)))
    | .mul => .mul (.quantity (some .here)) (.quantity (some (.there .here)))
    | .one => .scalar 1
    | .scalar a => .scalar a

/-- Interpret the written algebra Laws using the defining operations of `B`. -/
def writtenAlgebraInterpretation (k B : Type u) [CommRing k] [CommRing B] [Algebra k B] :
    (writtenAlgebraLaws k).Interpretation (algebraState k B) :=
  totalInterpretation _ _

/-- The operation symbols and fixed Law instances for the module in Example 5.6. -/
inductive ModuleStateLaw (k : Type u)
  /-- Addition in the fixed module. -/
  | add
  /-- Multiplication by a specified scalar in the fixed module. -/
  | smul (a : k)

/-- Addition takes two states; multiplying by a fixed scalar takes one. -/
private def moduleArity {k : Type u} : ModuleStateLaw k → List StateSort
  | .add => [stateSort, stateSort]
  | .smul _ => [stateSort]

/-- The fixed state operations are the actual operations of the module. -/
private def moduleState (k N : Type u) [CommRing k] [AddCommGroup N] [Module k N] :
    Structure (operationSignature (moduleArity (k := k))) where
  carrier _ := N
  total
    | .add, x => x .here + x (.there .here)
    | .smul a, x => a • x .here
  relation r := PEmpty.elim r
  partialDomain p := PEmpty.elim p
  partialValue p := PEmpty.elim p
  quantity q := PEmpty.elim q

/-- The written module Laws with one fixed scaling equation for each coefficient. -/
def writtenModuleLaws (k : Type u) : WrittenLaws k (operationSignature (moduleArity (k := k))) where
  Quantity := PUnit
  domainContext _ := [stateSort]
  Law := ModuleStateLaw k
  inputContext := moduleArity
  Occurrence l := Option (Var (moduleArity l) stateSort)
  application l a := ⟨PUnit.unit, unaryArgument (a.elim (operationTerm (arity := moduleArity) l) (fun i => .var i))⟩
  left _ := .quantity none
  right
    | .add => .add (.quantity (some .here)) (.quantity (some (.there .here)))
    | .smul a => .mul (.scalar a) (.quantity (some .here))

/-- Interpret the written module Laws using the defining operations of `N`. -/
def writtenModuleInterpretation (k N : Type u) [CommRing k] [AddCommGroup N] [Module k N] :
    (writtenModuleLaws k).Interpretation (moduleState k N) :=
  totalInterpretation _ _

section Compare

variable {k B N R : Type u} [CommRing k] [CommRing B] [Algebra k B]
variable [AddCommGroup N] [Module k N] [CommRing R] [Algebra k R]

/-- Read an occurrence in the original algebra equation at the value of its actual state term. -/
private theorem algebra_evaluate (q : PUnit → B → R) (l : AlgebraStateLaw k)
    (e : (writtenAlgebraInterpretation k B).input l) (t : Expression k (Option (Var (algebraArity l) stateSort))) :
    (writtenAlgebraInterpretation k B).evaluate l e t (fun j x => q j (x.val .here)) =
      t.eval (fun a => q PUnit.unit ((a.elim (operationTerm (arity := algebraArity) l)
        (fun i => .var i)).totalValue (algebraState k B) e.val)) := by
  apply congrArg (fun f => t.eval f)
  funext a
  apply congrArg (q PUnit.unit)
  exact unaryArgument_value _ _ _

/-- Read an occurrence in the original module equation at the value of its actual state term. -/
private theorem module_evaluate (q : PUnit → N → R) (l : ModuleStateLaw k)
    (e : (writtenModuleInterpretation k N).input l) (t : Expression k (Option (Var (moduleArity l) stateSort))) :
    (writtenModuleInterpretation k N).evaluate l e t (fun j x => q j (x.val .here)) =
      t.eval (fun a => q PUnit.unit ((a.elim (operationTerm (arity := moduleArity) l)
        (fun i => .var i)).totalValue (moduleState k N) e.val)) := by
  apply congrArg (fun f => t.eval f)
  funext a
  apply congrArg (q PUnit.unit)
  exact unaryArgument_value _ _ _

/-- Compiling the written state terms of the algebra imposes exactly the four equation families
used for the algebra quotient in Example 5.6. -/
theorem algebraPresentation_holds_iff_written (q : (algebraPresentation k B).Candidate R) :
    (algebraPresentation k B).Holds q ↔
      (writtenAlgebraInterpretation k B).presentation.Holds (fun j x => q j (x.val .here)) := by
  rw [WrittenLaws.Interpretation.holds_iff_written]
  constructor
  · intro h l e
    rw [algebra_evaluate, algebra_evaluate]
    cases l with
    | add => exact h .add (e.val .here, e.val (.there .here))
    | mul => exact h .mul (e.val .here, e.val (.there .here))
    | one => exact h .one PUnit.unit
    | scalar a => exact h .scalar a
  · intro h l e
    cases l with
    | add =>
      have hw := h .add ⟨Assignment.cons e.1 (Assignment.cons e.2 Assignment.empty), Set.mem_univ _⟩
      rw [algebra_evaluate, algebra_evaluate] at hw
      exact hw
    | mul =>
      have hw := h .mul ⟨Assignment.cons e.1 (Assignment.cons e.2 Assignment.empty), Set.mem_univ _⟩
      rw [algebra_evaluate, algebra_evaluate] at hw
      exact hw
    | one =>
      have hw := h .one ⟨Assignment.empty, Set.mem_univ _⟩
      rw [algebra_evaluate, algebra_evaluate] at hw
      exact hw
    | scalar =>
      have hw := h (.scalar e) ⟨Assignment.empty, Set.mem_univ _⟩
      rw [algebra_evaluate, algebra_evaluate] at hw
      exact hw

/-- Compiling the written state terms of the module imposes exactly the additive and scalar equations
used for the symmetric algebra quotient in Example 5.6. -/
theorem modulePresentation_holds_iff_written (q : (modulePresentation k N).Candidate R) :
    (modulePresentation k N).Holds q ↔
      (writtenModuleInterpretation k N).presentation.Holds (fun j x => q j (x.val .here)) := by
  rw [WrittenLaws.Interpretation.holds_iff_written]
  constructor
  · intro h l e
    rw [module_evaluate, module_evaluate]
    cases l with
    | add => exact h .add (e.val .here, e.val (.there .here))
    | smul a => exact h .smul (a, e.val .here)
  · intro h l e
    cases l with
    | add =>
      have hw := h .add ⟨Assignment.cons e.1 (Assignment.cons e.2 Assignment.empty), Set.mem_univ _⟩
      rw [module_evaluate, module_evaluate] at hw
      exact hw
    | smul =>
      have hw := h (.smul e.1) ⟨Assignment.cons e.2 Assignment.empty, Set.mem_univ _⟩
      rw [module_evaluate, module_evaluate] at hw
      exact hw

/-- Reindex quantity functions by the state value in their single argument. -/
private def unaryCandidates {sig : Signature.{u}} (A : Structure sig) (s : sig.SortType) (R : Type u) :
    (PUnit.{u + 1} → A.carrier s → R) ≃
    (PUnit.{u + 1} → {x : Assignment A.carrier [s] // x ∈ (Set.univ : Set (Assignment A.carrier [s]))} → R) :=
  Equiv.arrowCongr (Equiv.refl _) (Equiv.arrowCongr (unaryDomainEquiv A s).symm (Equiv.refl R))

/-- The fixed written algebra Laws and the coordinate quotient model the same quantities. -/
def writtenAlgebraModelEquiv :
    (writtenAlgebraInterpretation k B).Model R ≃ (algebraPresentation k B).Model R :=
  (Equiv.subtypeEquiv (unaryCandidates (algebraState k B) stateSort R)
    algebraPresentation_holds_iff_written).symm

/-- The fixed written module Laws and the symmetric algebra quotient model the same quantities. -/
def writtenModuleModelEquiv :
    (writtenModuleInterpretation k N).Model R ≃ (modulePresentation k N).Model R :=
  (Equiv.subtypeEquiv (unaryCandidates (moduleState k N) stateSort R)
    modulePresentation_holds_iff_written).symm

end Compare

section Quotients

variable {k : Type u} [CommRing k] {sig sig' : Signature.{u}}
variable {A : Structure sig} {B : Structure sig'}

/-- Compare two quotient presentations by transporting each universal model through the
same correspondence that transports their models over every coefficient algebra. -/
private def compareQuotients (P : Presentation k A) (Q : Presentation k B)
    (e : ∀ (R : Type u) [CommRing R] [Algebra k R], P.Model R ≃ Q.Model R)
    (natural : ∀ {R S : Type u} [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]
      (f : R →ₐ[k] S) (q : P.Model R), e S (P.map f q) = Q.map f (e R q)) :
    P.LawAlgebra ≃ₐ[k] Q.LawAlgebra := by
  let f := P.modelAlgHomEquiv ((e Q.LawAlgebra).symm Q.universalModel)
  let g := Q.modelAlgHomEquiv (e P.LawAlgebra P.universalModel)
  have readP : P.modelAlgHomEquiv P.universalModel = AlgHom.id k P.LawAlgebra :=
    P.modelAlgHomEquiv.apply_symm_apply _
  have readQ : Q.modelAlgHomEquiv Q.universalModel = AlgHom.id k Q.LawAlgebra :=
    Q.modelAlgHomEquiv.apply_symm_apply _
  have mapP : P.map f P.universalModel = (e Q.LawAlgebra).symm Q.universalModel := by
    apply P.modelAlgHomEquiv.injective
    rw [P.modelAlgHomEquiv_natural, readP, AlgHom.comp_id]
  have mapQ : Q.map g Q.universalModel = e P.LawAlgebra P.universalModel := by
    apply Q.modelAlgHomEquiv.injective
    rw [Q.modelAlgHomEquiv_natural, readQ, AlgHom.comp_id]
  refine AlgEquiv.ofAlgHom f g ?_ ?_
  · change f.comp (Q.modelAlgHomEquiv (e P.LawAlgebra P.universalModel)) = _
    rw [← Q.modelAlgHomEquiv_natural, ← natural, mapP, Equiv.apply_symm_apply, readQ]
  · change g.comp (P.modelAlgHomEquiv ((e Q.LawAlgebra).symm Q.universalModel)) = _
    rw [← P.modelAlgHomEquiv_natural, ← readP]
    congr 1
    apply (e P.LawAlgebra).injective
    rw [natural, Equiv.apply_symm_apply, mapQ]

/-- The quotient of the actual written algebra Laws is the original algebra in Example 5.6. -/
def writtenAlgebraLawAlgebraEquiv (k C : Type u) [CommRing k] [CommRing C] [Algebra k C] :
    (writtenAlgebraInterpretation k C).presentation.LawAlgebra ≃ₐ[k] C :=
  (compareQuotients _ _ (fun _ _ _ => writtenAlgebraModelEquiv)
    (fun _ _ => Subtype.ext rfl)).trans (lawAlgebraEquiv k C)

/-- The quotient of the actual written module Laws is the symmetric algebra in Example 5.6. -/
def writtenModuleLawAlgebraEquiv (k N : Type u) [CommRing k] [AddCommGroup N] [Module k N] :
    (writtenModuleInterpretation k N).presentation.LawAlgebra ≃ₐ[k] SymmetricAlgebra k N :=
  (compareQuotients _ _ (fun _ _ _ => writtenModuleModelEquiv)
    (fun _ _ => Subtype.ext rfl)).trans (symmetricLawAlgebraEquiv k N)

end Quotients

end SHIGURE.Quantities
