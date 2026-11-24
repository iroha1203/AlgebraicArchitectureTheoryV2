import Formal.SHIGURE.Part1.ContextEvaluation
import Mathlib.Data.Fintype.EquivFin

/-! # Marked module vocabulary

Proposition 3.6 of SHIGURE Chapter 3 fixes the coefficient sort, the
generator counts and ranks, and the profiles of the multilinear symbols.

## Implementation notes

Each module sort has a block of canonical operation names, including a
distinct nullary operation for each coordinate generator. A user-specified
multilinear symbol has a list of declared input sorts, so two occurrences of
the same sort are distinct input positions. Both the coefficient and module
sorts are permitted at every input and output. This is the existing SHIGURE argument
syntax with no arity bound. A predicate adds block closure to the existing
declaration context, leaving the dependency closure for Laws and operations
to DeclarationContext.
-/

universe u

namespace SHIGURE.Marked

/-- The fixed coefficient operations used in Proposition 3.6. -/
inductive CoefficientOp : Type u
  | zero | one | add | neg | mul

/-- The standard operations and named generators of one declared module sort. -/
inductive ModuleOp (m : ℕ) : Type u
  | zero | add | neg | smul
  | generator (i : Fin m)

/-- The names, two natural numbers per sort, and finite arities in Proposition 3.6. -/
structure Vocabulary where
  /-- The declared module sorts apart from the coefficient sort. -/
  SortName : Type u
  /-- The number of named coordinate generators of each module. -/
  generators : SortName → ℕ
  /-- The required stalk rank of each declared module. -/
  rank : SortName → ℕ
  /-- The extra multilinear operation names. -/
  Multilinear : Type u
  /-- The ordered coefficient or module sort of each input position. -/
  inputs : Multilinear → List (Option SortName)
  /-- The coefficient or module sort returned by each multilinear operation. -/
  output : Multilinear → Option SortName

namespace Vocabulary

variable (V : Vocabulary.{u})

/-- The total names consist of the coefficient operations, module blocks and multilinear symbols. -/
inductive Symbol
  | coefficient (f : CoefficientOp.{u})
  | moduleOp (s : V.SortName) (f : ModuleOp.{u} (V.generators s))
  | multilinear (f : V.Multilinear)

/-- The total arity of a marked operation, with `none` reserved for the coefficient sort. -/
def arity : V.Symbol → Arity (Option V.SortName)
  | .coefficient .zero | .coefficient .one => ⟨[], none⟩
  | .coefficient .add | .coefficient .mul => ⟨[none, none], none⟩
  | .coefficient .neg => ⟨[none], none⟩
  | .moduleOp s .zero | .moduleOp s (.generator _) => ⟨[], some s⟩
  | .moduleOp s .add => ⟨[some s, some s], some s⟩
  | .moduleOp s .neg => ⟨[some s], some s⟩
  | .moduleOp s .smul => ⟨[none, some s], some s⟩
  | .multilinear f => ⟨V.inputs f, V.output f⟩

/-- The marked language is an ordinary total SHIGURE signature. -/
def signature : Signature.{u} where
  SortType := Option V.SortName
  Total := V.Symbol
  Rel := PEmpty
  Partial := PEmpty
  Quantity := PEmpty
  totalArity := V.arity
  relInputs r := nomatch r
  partialArity p := nomatch p
  quantityArity q := nomatch q

/-- All terms of the marked vocabulary are total. -/
instance noPartial : IsEmpty V.signature.Partial :=
  inferInstanceAs (IsEmpty PEmpty)

/-- A finite-arity position with its declared coefficient or module sort. -/
abbrev Position (f : V.Multilinear) := Σ s, Var (V.inputs f) s

/-- The position number of a typed argument lies within the arity's finite list. -/
private theorem position_lt {S : Type u} {Γ : List S} {s : S} (i : Var Γ s) :
    i.position < Γ.length := by
  induction i with
  | here => exact Nat.zero_lt_succ _
  | there _ ih => exact Nat.succ_lt_succ ih

/-- The input positions have the same indices as the written finite arity. -/
def positionIndex (f : V.Multilinear) (i : V.Position f) : Fin (V.inputs f).length :=
  ⟨i.2.position, position_lt i.2⟩

/-- Multilinearity is indexed by finitely many positions, even with arbitrary sorts. -/
instance finitePosition (f : V.Multilinear) : Finite (V.Position f) :=
  Finite.of_injective (V.positionIndex f) (fun _ _ h =>
    Var.position_injective (V.inputs f) (congrArg Fin.val h))

/-- Addition in either a coefficient or module sort, as a written term. -/
def addTerm {Γ : List (Option V.SortName)} : (s : Option V.SortName) →
    Term V.signature Γ s → Term V.signature Γ s → Term V.signature Γ s
  | none, x, y => Term.app (sig := V.signature) (.total (Symbol.coefficient .add))
      (x.argsCons (y.argsCons Term.argsNil))
  | some s, x, y => Term.app (sig := V.signature) (.total (Symbol.moduleOp s .add))
      (x.argsCons (y.argsCons Term.argsNil))

/-- Scalar multiplication in either sort. On the coefficient sort it is ring multiplication. -/
def smulTerm {Γ : List (Option V.SortName)} : (s : Option V.SortName) →
    Term V.signature Γ none → Term V.signature Γ s → Term V.signature Γ s
  | none, a, x => Term.app (sig := V.signature) (.total (Symbol.coefficient .mul))
      (a.argsCons (x.argsCons Term.argsNil))
  | some s, a, x => Term.app (sig := V.signature) (.total (Symbol.moduleOp s .smul))
      (a.argsCons (x.argsCons Term.argsNil))

/-- Replace just one typed argument in the variable tuple of a multilinear symbol. -/
noncomputable def updatedTerms {Γ : List (Option V.SortName)} {f : V.Multilinear}
    (names : Renaming (V.inputs f) Γ) (i : V.Position f) (x : Term V.signature Γ i.1) :
    (j : V.Position f) → Term V.signature Γ j.1 := by
  classical
  exact Function.update (fun j => Term.var (names j.2)) i x

/-- The replaced position has the new term. -/
theorem updatedTerms_same {Γ : List (Option V.SortName)} {f : V.Multilinear}
    (names : Renaming (V.inputs f) Γ) (i : V.Position f) (x : Term V.signature Γ i.1) :
    V.updatedTerms names i x i = x := by
  classical
  simp [updatedTerms]

/-- All other positions retain their original variable term. -/
theorem updatedTerms_other {Γ : List (Option V.SortName)} {f : V.Multilinear}
    (names : Renaming (V.inputs f) Γ) (i j : V.Position f) (x : Term V.signature Γ i.1) (different : j ≠ i) :
    V.updatedTerms names i x j = .var (names j.2) := by
  classical
  simp [updatedTerms, Function.update_of_ne different]

/-- Apply the symbol to a variable tuple with its indicated argument replaced. -/
noncomputable def updatedTerm {Γ : List (Option V.SortName)} {f : V.Multilinear}
    (names : Renaming (V.inputs f) Γ) (i : V.Position f) (x : Term V.signature Γ i.1) :
    Term V.signature Γ (V.output f) :=
  Term.app (sig := V.signature) (.total (Symbol.multilinear f))
    (fun j => V.updatedTerms names i x ⟨_, j⟩)

/-- Proposition 3.6 imposes additivity as a literal equality Law at each argument. -/
noncomputable def addLinearityLaw {f : V.Multilinear} (i : V.Position f) : Law V.signature :=
  let Γ := i.1 :: i.1 :: V.inputs f
  let names : Renaming (V.inputs f) Γ := fun j => j.there.there
  let x : Term V.signature Γ i.1 := .var .here
  let y : Term V.signature Γ i.1 := .var (.there .here)
  Law.equality (V.updatedTerm names i (V.addTerm i.1 x y))
    (V.addTerm (V.output f) (V.updatedTerm names i x) (V.updatedTerm names i y))

/-- Proposition 3.6 imposes scalar homogeneity as a literal equality Law at each argument. -/
noncomputable def smulLinearityLaw {f : V.Multilinear} (i : V.Position f) : Law V.signature :=
  let Γ := (none : Option V.SortName) :: i.1 :: V.inputs f
  let names : Renaming (V.inputs f) Γ := fun j => j.there.there
  let a : Term V.signature Γ none := .var .here
  let x : Term V.signature Γ i.1 := .var (.there .here)
  Law.equality (V.updatedTerm names i (V.smulTerm i.1 a x))
    (V.smulTerm (V.output f) a (V.updatedTerm names i x))

/-- Read the two terms of a position's addition Law through its public constructor. -/
theorem addLinearityLaw_eq {f : V.Multilinear} (i : V.Position f) :
    let Γ := i.1 :: i.1 :: V.inputs f
    let names : Renaming (V.inputs f) Γ := fun j => j.there.there
    let x : Term V.signature Γ i.1 := .var .here
    let y : Term V.signature Γ i.1 := .var (.there .here)
    V.addLinearityLaw i = Law.equality (V.updatedTerm names i (V.addTerm i.1 x y))
      (V.addTerm (V.output f) (V.updatedTerm names i x) (V.updatedTerm names i y)) :=
  rfl

/-- Read the two terms of a position's scalar Law through its public constructor. -/
theorem smulLinearityLaw_eq {f : V.Multilinear} (i : V.Position f) :
    let Γ := (none : Option V.SortName) :: i.1 :: V.inputs f
    let names : Renaming (V.inputs f) Γ := fun j => j.there.there
    let a : Term V.signature Γ none := .var .here
    let x : Term V.signature Γ i.1 := .var (.there .here)
    V.smulLinearityLaw i = Law.equality (V.updatedTerm names i (V.smulTerm i.1 a x))
      (V.smulTerm (V.output f) a (V.updatedTerm names i x)) :=
  rfl

/-- The names of the two required Laws at each written argument position. -/
inductive LinearityLaw
  | add (f : V.Multilinear) (position : V.Position f)
  | smul (f : V.Multilinear) (position : V.Position f)

/-- The multilinear symbol named in this required Law. -/
def LinearityLaw.symbol : V.LinearityLaw → V.Multilinear
  | .add f _ | .smul f _ => f

/-- The addition Law keeps the named multilinear symbol at its argument position. -/
theorem LinearityLaw.symbol_add {f : V.Multilinear} (i : V.Position f) :
    LinearityLaw.symbol V (.add f i) = f :=
  rfl

/-- The scalar multiplication Law keeps the named multilinear symbol at its argument position. -/
theorem LinearityLaw.symbol_smul {f : V.Multilinear} (i : V.Position f) :
    LinearityLaw.symbol V (.smul f i) = f :=
  rfl

/-- The SHIGURE equality imposed by each generated Law. -/
noncomputable def LinearityLaw.statement : V.LinearityLaw → Law V.signature
  | .add _ i => V.addLinearityLaw i
  | .smul _ i => V.smulLinearityLaw i

/-- An addition name selects its position's written addition Law. -/
theorem LinearityLaw.statement_add {f : V.Multilinear} (i : V.Position f) :
    LinearityLaw.statement V (.add f i) = V.addLinearityLaw i :=
  rfl

/-- A scalar multiplication name selects its position's written scalar Law. -/
theorem LinearityLaw.statement_smul {f : V.Multilinear} (i : V.Position f) :
    LinearityLaw.statement V (.smul f i) = V.smulLinearityLaw i :=
  rfl

/-- Add the literal multilinearity Laws to the written Law declarations. -/
noncomputable def withLinearity (written : LawDeclarations V.signature) : LawDeclarations V.signature where
  LawName := written.LawName ⊕ V.LinearityLaw
  statement := Sum.elim written.statement (LinearityLaw.statement V)
  role := Sum.elim written.role (fun _ => .required)

/-- The Law declarations and any derived proof data of a marked signature. -/
structure Laws where
  /-- Proposition 3.6 permits arbitrary Laws over the declared operations. -/
  declarations : LawDeclarations V.signature
  /-- A derived Law keeps its original checked derivation. -/
  derived (i : declarations.LawName) : declarations.role i = .derived →
    Derivation (V.withLinearity declarations).toTheory (declarations.statement i).input
      (declarations.statement i).conclusion

/-- The marked vocabulary includes the written and generated Laws in its ordinary presentation. -/
noncomputable def presentation (L : V.Laws) : PrimitivePresentation.{u} where
  signature := V.signature
  laws := V.withLinearity L.declarations
  derived
    | .inl name => L.derived name
    | .inr _ => fun h => nomatch h

/-- Each generated statement is actually required in the ordinary presentation. -/
theorem linearity_role (L : V.Laws) (name : V.LinearityLaw) :
    (V.presentation L).laws.role (.inr name) = .required :=
  rfl

/-- The registered generated statement is the original equality Law. -/
theorem linearity_statement (L : V.Laws) (name : V.LinearityLaw) :
    (V.presentation L).laws.statement (.inr name) = LinearityLaw.statement V name :=
  rfl

/-- A coefficient operation as a declaration in this marked presentation. -/
abbrev coefficientDecl (L : V.Laws) (f : CoefficientOp.{u}) : Declaration (V.presentation L) :=
  .total (Symbol.coefficient f)

/-- A module operation or generator as a declaration in this marked presentation. -/
abbrev moduleDecl (L : V.Laws) (s : V.SortName) (f : ModuleOp.{u} (V.generators s)) :
    Declaration (V.presentation L) :=
  .total (Symbol.moduleOp s f)

/-- A multilinear symbol as a declaration in this marked presentation. -/
abbrev multilinearDecl (L : V.Laws) (f : V.Multilinear) : Declaration (V.presentation L) :=
  .total (Symbol.multilinear f)

/-- The type of every input or result of a primitive coefficient operation is the coefficient sort. -/
theorem coefficient_dependency (L : V.Laws) (f : CoefficientOp.{u}) :
    Declaration.dependsOn (V.presentation L) (V.coefficientDecl L f) = {Declaration.sort none} := by
  ext d
  constructor
  · rintro ⟨s, within, rfl⟩
    have same : s = none := by
      cases f <;> simpa [presentation, signature, arity] using within
    rw [same]
    exact Set.mem_singleton _
  · intro kept
    have same := Set.mem_singleton_iff.mp kept
    subst d
    cases f <;> exact ⟨none, List.mem_cons_self, rfl⟩

/-- A module operation refers only to that module and the fixed coefficient sort. -/
theorem module_dependencies (L : V.Laws) (s : V.SortName) (f : ModuleOp.{u} (V.generators s)) :
    Declaration.dependsOn (V.presentation L) (V.moduleDecl L s f) ⊆
      {Declaration.sort (some s), Declaration.sort none} := by
  rintro _ ⟨t, occurs, rfl⟩
  cases f <;> simp_all [presentation, signature, arity]
  aesop

/-- The references of a multilinear declaration are its declared input and output sorts. -/
theorem multilinear_dependencies (L : V.Laws) (f : V.Multilinear) :
    Declaration.dependsOn (V.presentation L) (V.multilinearDecl L f) =
      Declaration.sorts (V.output f :: V.inputs f) :=
  rfl

variable {V} {L : V.Laws}

/-- A context containing the coefficient sort and all five primitive coefficient operations. -/
structure RetainsCoefficients (U : DeclarationContext (V.presentation L)) : Prop where
  /-- The coefficient sort is retained. -/
  sort : Declaration.sort none ∈ U.declarations
  /-- Every ring operation is retained. -/
  operation (f : CoefficientOp.{u}) : V.coefficientDecl L f ∈ U.declarations

/-- The whole block of standard operations and marks is kept for every retained module sort. -/
structure BlockClosed (U : DeclarationContext (V.presentation L)) : Prop where
  /-- Each retained module also retains the coefficient data. -/
  coefficients (s : V.SortName) : Declaration.sort (some s) ∈ U.declarations → RetainsCoefficients U
  /-- The block keeps addition, zero, negation, scalar action, and each mark. -/
  moduleOp (s : V.SortName) (kept : Declaration.sort (some s) ∈ U.declarations)
      (f : ModuleOp.{u} (V.generators s)) : V.moduleDecl L s f ∈ U.declarations

/-- The full declaration context contains every required block. -/
theorem full_blockClosed (L : V.Laws) :
    BlockClosed (DeclarationContext.full (V.presentation L)) :=
  ⟨fun _ _ => ⟨Set.mem_univ _, fun _ => Set.mem_univ _⟩, fun _ _ _ => Set.mem_univ _⟩

/-- The intersection of two marked contexts is again closed under the retained module blocks. -/
theorem BlockClosed.inter {U W : DeclarationContext (V.presentation L)}
    (hu : BlockClosed U) (hw : BlockClosed W) : BlockClosed (U.inter W) where
  coefficients s keep :=
    let left := hu.coefficients s keep.1
    let right := hw.coefficients s keep.2
    ⟨⟨left.sort, right.sort⟩, fun f => ⟨left.operation f, right.operation f⟩⟩
  moduleOp s keep f := ⟨hu.moduleOp s keep.1 f, hw.moduleOp s keep.2 f⟩

/-- A declaration cover by block-closed pieces keeps each block in the covered context. -/
theorem BlockClosed.of_cover {U : DeclarationContext (V.presentation L)}
    (cover : DeclarationCover U) (h : ∀ i, BlockClosed (cover.piece i)) : BlockClosed U where
  coefficients s keep := by
    obtain ⟨i, localKeep⟩ := cover.covers keep
    let coeffs := (h i).coefficients s localKeep
    exact ⟨cover.subset i coeffs.sort, fun f => cover.subset i (coeffs.operation f)⟩
  moduleOp s keep f := by
    obtain ⟨i, localKeep⟩ := cover.covers keep
    exact cover.subset i ((h i).moduleOp s localKeep f)

/-- Any coefficient or module input of a retained multilinear symbol is retained. -/
theorem multilinear_input_kept {U : DeclarationContext (V.presentation L)} {f : V.Multilinear}
    (kept : V.multilinearDecl L f ∈ U.declarations) (i : V.Position f) :
    Declaration.sort i.1 ∈ U.declarations :=
  DeclarationContext.operationInputs (P := V.presentation L) (U := U)
    (.total (Symbol.multilinear f)) kept
    ⟨_, i.2.sort_mem, rfl⟩

/-- A retained multilinear symbol forces retention of its coefficient or module result sort. -/
theorem multilinear_output_kept {U : DeclarationContext (V.presentation L)} {f : V.Multilinear}
    (kept : V.multilinearDecl L f ∈ U.declarations) :
    Declaration.sort (V.output f) ∈ U.declarations :=
  DeclarationContext.operationOutput (P := V.presentation L) (U := U)
    (.total (Symbol.multilinear f)) kept

end Vocabulary
end SHIGURE.Marked
