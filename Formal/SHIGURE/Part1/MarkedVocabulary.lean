import Formal.SHIGURE.Part1.ContextEvaluation
import Formal.SHIGURE.Part1.FixedModels
import Mathlib.LinearAlgebra.Multilinear.Basic

/-! # Marked module vocabulary

Proposition 3.6 of SHIGURE Chapter 3 fixes the coefficient sort, the
generator counts and ranks, and the profiles of the multilinear symbols.

## Implementation notes

Each module sort has a block of canonical operation names, including a
distinct nullary operation for each coordinate generator. A user-specified
multilinear symbol has a list of input sorts, so two occurrences of the same
sort are distinct input positions. This is the existing SHIGURE argument
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
  /-- The ordered module sort of each input position. -/
  inputs : Multilinear → List SortName
  /-- The module sort returned by each multilinear operation. -/
  output : Multilinear → SortName

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
  | .multilinear f => ⟨(V.inputs f).map some, some (V.output f)⟩

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

/-- A finite-arity position with its declared module sort. -/
abbrev Position (f : V.Multilinear) := Σ s, Var (V.inputs f) s

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

/-- The Law declarations and any derived proof data of a marked signature. -/
structure Laws where
  /-- Proposition 3.6 permits arbitrary Laws over the declared operations. -/
  declarations : LawDeclarations V.signature
  /-- A derived Law keeps its original checked derivation. -/
  derived (i : declarations.LawName) : declarations.role i = .derived →
    Derivation declarations.toTheory (declarations.statement i).input
      (declarations.statement i).conclusion

/-- The marked vocabulary and Laws form an ordinary declaration presentation. -/
def presentation (L : V.Laws) : PrimitivePresentation.{u} where
  signature := V.signature
  laws := L.declarations
  derived := L.derived

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

variable {V} {L : V.Laws}

/-- A context keeps the full coefficient signature whenever it contains a module. -/
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

/-- An input sort of a retained multilinear symbol is retained by ordinary dependency closure. -/
theorem multilinear_input_kept {U : DeclarationContext (V.presentation L)} {f : V.Multilinear}
    (kept : V.multilinearDecl L f ∈ U.declarations) (i : V.Position f) :
    Declaration.sort (some i.1) ∈ U.declarations :=
  DeclarationContext.operationInputs (P := V.presentation L) (U := U)
    (.total (Symbol.multilinear f)) kept
    ⟨_, List.mem_map_of_mem i.2.sort_mem, rfl⟩

/-- A retained multilinear symbol forces retention of its output module sort. -/
theorem multilinear_output_kept {U : DeclarationContext (V.presentation L)} {f : V.Multilinear}
    (kept : V.multilinearDecl L f ∈ U.declarations) :
    Declaration.sort (some (V.output f)) ∈ U.declarations :=
  DeclarationContext.operationOutput (P := V.presentation L) (U := U)
    (.total (Symbol.multilinear f)) kept

end Vocabulary
end SHIGURE.Marked
