import Formal.SHIGURE.Part1.MarkedQuotients
import Formal.SHIGURE.Part1.MarkedVocabulary
import Mathlib.LinearAlgebra.Multilinear.Basic

/-! # Restricting marked kernels and operations

This is the underlying data of a marked realization in Proposition 3.6.
It records kernels at retained module sorts and actual multilinear maps
at retained extra operation symbols.

## Implementation notes

The type of each map only depends on the kernels of its declared input
and output modules. Restricting an operation keeps precisely these kernels
by dependency closure. Equality across contexts compares maps
heterogeneously because those kernels are selected from potentially
different tuples. Equal kernels give equality of map types, so this
comparison is equality of transported maps.
-/

universe u

namespace SHIGURE.Marked

open Vocabulary

variable {V : Vocabulary.{u}} {L : V.Laws}
variable {U W : DeclarationContext (V.presentation L)}
variable (R : Type u) [CommRing R]

/-- The kernels of exactly the retained module sorts. -/
abbrev KernelFamily (U : DeclarationContext (V.presentation L)) :=
  ∀ s : V.SortName, Declaration.sort (some s) ∈ U.declarations → Kernel R (V.generators s)

/-- Only a module sort needs a kernel. The coefficient carrier is already fixed by `R`. -/
abbrev SortKernel (V : Vocabulary.{u}) (R : Type u) [CommRing R] : Option V.SortName → Type u
  | none => PUnit
  | some s => Kernel R (V.generators s)

/-- Interpret a declared sort as the fixed coefficients or the canonical module quotient. -/
abbrev SortCarrier {V : Vocabulary.{u}} {s : Option V.SortName} : SortKernel V R s → Type u :=
  match s with
  | none => fun _ => R
  | some _ => Quotient

/-- The coefficient ring and the canonical quotient both carry their existing addition. -/
instance sortCarrierAddCommGroup {s : Option V.SortName} (K : SortKernel V R s) :
    AddCommGroup (SortCarrier R K) := by
  cases s <;> infer_instance

/-- Both sorts use the native action of the fixed coefficient ring. -/
instance sortCarrierModule {s : Option V.SortName} (K : SortKernel V R s) :
    Module R (SortCarrier R K) := by
  cases s <;> infer_instance

/-- The appropriate kernel data at a retained coefficient or module sort. -/
def kernelAt {R : Type u} [CommRing R] (K : KernelFamily R U) :
    (s : Option V.SortName) → Declaration.sort s ∈ U.declarations → SortKernel V R s
  | none, _ => ⟨⟩
  | some s, keep => K s keep

/-- The kernels used to type one multilinear operation. -/
structure OperationKernels (f : V.Multilinear) where
  /-- There is one slot per argument position, including coefficient positions. -/
  inputs (i : V.Position f) : SortKernel V R i.1
  /-- The result slot uses the fixed coefficient ring or a quotient. -/
  output : SortKernel V R (V.output f)

namespace OperationKernels

variable {R} {f : V.Multilinear}

/-- These kernels determine the exact mathlib multilinear map type. -/
abbrev Map (profile : OperationKernels (V := V) R f) :=
  MultilinearMap R (fun i => SortCarrier R (profile.inputs i)) (SortCarrier R profile.output)

/-- Equality is determined by the typed input and output kernels. -/
@[ext] theorem ext {a b : OperationKernels (V := V) R f}
    (inputs : ∀ i, a.inputs i = b.inputs i) (output : a.output = b.output) : a = b := by
  cases a
  cases b
  cases funext inputs
  cases output
  rfl

end OperationKernels

/-- Retaining the symbol gives each kernel required for its interpretation. -/
def operationKernels {R : Type u} [CommRing R] (K : KernelFamily R U) {f : V.Multilinear}
    (keep : V.multilinearDecl L f ∈ U.declarations) :
    OperationKernels (V := V) R f where
  inputs i := kernelAt K i.1 (V.multilinear_input_kept keep i)
  output := kernelAt K (V.output f) (V.multilinear_output_kept keep)

/-- The kernel and multilinear interpretation data of Proposition 3.6. -/
structure Data (U : DeclarationContext (V.presentation L)) where
  /-- Each retained module uses its canonical quotient by this kernel. -/
  kernel : KernelFamily R U
  /-- Each retained operation is multilinear on the actual quotient modules. -/
  operation (f : V.Multilinear) (keep : V.multilinearDecl L f ∈ U.declarations) :
    (operationKernels kernel keep).Map

namespace Data

variable {R}

/-- Data on different contexts agree where both retain a module or multilinear symbol. -/
structure Agree (a : Data R U) (b : Data R W) : Prop where
  /-- The shared module relations are the same submodules. -/
  kernel (s : V.SortName) (left : Declaration.sort (some s) ∈ U.declarations)
    (right : Declaration.sort (some s) ∈ W.declarations) : a.kernel s left = b.kernel s right
  /-- Equality of shared maps is read after identifying the shared quotients. -/
  operation (f : V.Multilinear) (left : V.multilinearDecl L f ∈ U.declarations)
    (right : V.multilinearDecl L f ∈ W.declarations) :
    HEq (a.operation f left) (b.operation f right)

/-- At the coefficient sort there is no kernel choice, and at shared module sorts the kernels agree. -/
theorem Agree.kernelAt_eq {a : Data R U} {b : Data R W} (h : a.Agree b)
    (s : Option V.SortName) (left : Declaration.sort s ∈ U.declarations)
    (right : Declaration.sort s ∈ W.declarations) :
    kernelAt a.kernel s left = kernelAt b.kernel s right := by
  cases s with
  | none => rfl
  | some s => exact h.kernel s left right

/-- Agreement of kernels identifies the full input and output profile of a shared symbol. -/
theorem Agree.operationKernels_eq {a : Data R U} {b : Data R W} (h : a.Agree b)
    {f : V.Multilinear} (left : V.multilinearDecl L f ∈ U.declarations)
    (right : V.multilinearDecl L f ∈ W.declarations) :
    operationKernels a.kernel left = operationKernels b.kernel right :=
  OperationKernels.ext (fun i => h.kernelAt_eq i.1 _ _) (h.kernelAt_eq (V.output f) _ _)

/-- The overlap agreement is equality of the maps transported by the actual kernel equality. -/
theorem Agree.cast_operation {a : Data R U} {b : Data R W} (h : a.Agree b)
    (f : V.Multilinear) (left : V.multilinearDecl L f ∈ U.declarations)
    (right : V.multilinearDecl L f ∈ W.declarations) :
    cast (congrArg OperationKernels.Map (h.operationKernels_eq left right))
      (a.operation f left) = b.operation f right :=
  eq_of_heq ((cast_heq _ _).trans (h.operation f left right))

private theorem kernelAt_restrict (K : KernelFamily R U) (inside : W ≤ U) (s : Option V.SortName)
    (keep : Declaration.sort s ∈ W.declarations) :
    kernelAt (fun t ht => K t (inside ht)) s keep = kernelAt K s (inside keep) := by
  cases s <;> rfl

private theorem operationKernels_restrict (K : KernelFamily R U) (inside : W ≤ U) {f : V.Multilinear}
    (keep : V.multilinearDecl L f ∈ W.declarations) :
    operationKernels (fun s hs => K s (inside hs)) keep = operationKernels K (inside keep) :=
  OperationKernels.ext (fun i => kernelAt_restrict K inside i.1 _)
    (kernelAt_restrict K inside (V.output f) _)

/-- Restriction keeps only the declared kernel and multilinear data. -/
def restrict (a : Data R U) (inside : W ≤ U) : Data R W where
  kernel s keep := a.kernel s (inside keep)
  operation f keep := cast (congrArg OperationKernels.Map (operationKernels_restrict a.kernel inside keep).symm)
    (a.operation f (inside keep))

/-- Restriction keeps exactly the original kernel at a retained module sort. -/
theorem restrict_kernel (a : Data R U) (inside : W ≤ U) (s : V.SortName)
    (keep : Declaration.sort (some s) ∈ W.declarations) :
    (a.restrict inside).kernel s keep = a.kernel s (inside keep) :=
  rfl

/-- Restriction keeps exactly the map at a retained multilinear symbol. -/
theorem restrict_operation (a : Data R U) (inside : W ≤ U) (f : V.Multilinear)
    (keep : V.multilinearDecl L f ∈ W.declarations) :
    HEq ((a.restrict inside).operation f keep) (a.operation f (inside keep)) :=
  cast_heq _ _

/-- Data at a fixed context are determined by their kernels and operation interpretations. -/
@[ext] theorem ext {a b : Data R U}
    (kernels : ∀ s keep, a.kernel s keep = b.kernel s keep)
    (operations : ∀ f keep, HEq (a.operation f keep) (b.operation f keep)) :
    a = b := by
  cases a with
  | mk K a =>
    cases b with
    | mk J b =>
      have same : K = J := funext fun s => funext (kernels s)
      subst J
      have same : a = b := funext fun f => funext fun keep => eq_of_heq (operations f keep)
      subst b
      rfl

/-- Pointwise shared agreement gives equality after restricting the larger datum. -/
theorem Agree.restrict_eq {a : Data R U} {b : Data R W} (h : a.Agree b) (inside : W ≤ U) :
    a.restrict inside = b :=
  Data.ext (fun s keep => h.kernel s (inside keep) keep)
    (fun f keep => ((a.restrict_operation inside f keep).trans (h.operation f (inside keep) keep)))

/-- Two larger data have equal restriction to any common subcontext of their agreement. -/
theorem Agree.restrict_eq_restrict {a : Data R U} {b : Data R W} (h : a.Agree b)
    {T : DeclarationContext (V.presentation L)} (ha : T ≤ U) (hb : T ≤ W) :
    a.restrict ha = b.restrict hb :=
  Data.ext (fun s keep => h.kernel s (ha keep) (hb keep))
    (fun f keep => (a.restrict_operation ha f keep).trans
      ((h.operation f (ha keep) (hb keep)).trans (b.restrict_operation hb f keep).symm))

/-- Strict equality of intersection reducts gives pointwise shared agreement. -/
theorem agree_of_overlap {a : Data R U} {b : Data R W}
    (same : a.restrict (U.inter_le_left W) = b.restrict (U.inter_le_right W)) :
    a.Agree b where
  kernel s aKeep bKeep := congrArg (fun q => q.kernel s ⟨aKeep, bKeep⟩) same
  operation f aKeep bKeep :=
    let keep : V.multilinearDecl L f ∈ (U.inter W).declarations := ⟨aKeep, bKeep⟩
    (a.restrict_operation (U.inter_le_left W) f keep).symm.trans
      ((by rw [same] : HEq ((a.restrict (U.inter_le_left W)).operation f keep)
        ((b.restrict (U.inter_le_right W)).operation f keep)).trans
        (b.restrict_operation (U.inter_le_right W) f keep))

end Data
end SHIGURE.Marked
