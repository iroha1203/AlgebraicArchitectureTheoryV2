import Formal.SHIGURE.Part1.MarkedData
import Formal.SHIGURE.Part1.ContextSelectedRoundtrip

/-! # SHIGURE interpretations of marked data

The marked quotients give the carriers and module operations. The extra
symbols use the underlying functions of their actual multilinear maps.

## Implementation notes

The context evaluation API reads a full-signature structure and forgets
its omitted declarations. We supply a canonical default outside the
context: zero kernels at omitted sorts and zero multilinear maps at
omitted symbols. Laws are only read where their whole support is
retained, so their validity depends only on the given marked data. This
allows use of the ordinary context structures and their restriction API.
-/

universe u

namespace SHIGURE.Marked

open Vocabulary DeclarationContext

variable {V : Vocabulary.{u}} {L : V.Laws} {R : Type u} [CommRing R]
variable {U W : DeclarationContext (V.presentation L)}

/-- The carrier family determined by a coefficient ring and a kernel per module sort. -/
abbrev quotientCarriers (K : ∀ s : V.SortName, Kernel R (V.generators s)) : Option V.SortName → Type u
  | none => R
  | some s => Quotient (K s)

/-- The input and output kernels of a symbol in a complete family of quotients. -/
def kernelsOf (K : ∀ s : V.SortName, Kernel R (V.generators s)) (f : V.Multilinear) :
    OperationKernels (V := V) R f :=
  ⟨fun i => K i.1, K (V.output f)⟩

private def operationValue (K : ∀ s : V.SortName, Kernel R (V.generators s))
    (maps : ∀ f, (kernelsOf K f).Map) :
    (f : V.Symbol) → Assignment (quotientCarriers K) (V.arity f).inputs →
      quotientCarriers K (V.arity f).output
  | .coefficient .zero => fun _ => (0 : R)
  | .coefficient .one => fun _ => (1 : R)
  | .coefficient .add => fun xs => (xs .here : R) + xs (.there .here)
  | .coefficient .neg => fun xs => -(xs .here : R)
  | .coefficient .mul => fun xs => (xs .here : R) * xs (.there .here)
  | .moduleOp s .zero => fun _ => (0 : Quotient (K s))
  | .moduleOp s .add => fun xs => (xs .here : Quotient (K s)) + xs (.there .here)
  | .moduleOp s .neg => fun xs => -(xs .here : Quotient (K s))
  | .moduleOp s .smul => fun xs => (xs .here : R) • (xs (.there .here) : Quotient (K s))
  | .moduleOp s (.generator i) => fun _ => generator (K s) i
  | .multilinear f => fun xs => maps f (fun i => xs (i.2.mapSorts some))

/-- The ordinary SHIGURE structure of a family of canonical quotients and typed maps. -/
def quotientStructure (K : ∀ s : V.SortName, Kernel R (V.generators s))
    (maps : ∀ f, (kernelsOf K f).Map) : Structure V.signature where
  carrier := quotientCarriers K
  total := operationValue K maps
  relation r := nomatch r
  partialDomain p := nomatch p
  partialValue p := nomatch p
  quantity q := nomatch q

/-- The multilinear symbol in that structure is the underlying function of the chosen map. -/
theorem quotientStructure_total_multilinear (K : ∀ s : V.SortName, Kernel R (V.generators s))
    (maps : ∀ f, (kernelsOf K f).Map) (f : V.Multilinear)
    (xs : Assignment (quotientCarriers K) (V.arity (.multilinear f)).inputs) :
    (quotientStructure K maps).total (.multilinear f) xs =
      maps f (fun i => xs (i.2.mapSorts some)) :=
  rfl

/-- Equality of kernels and transported maps determines the canonical ordinary structure. -/
theorem quotientStructure_congr {K J : ∀ s : V.SortName, Kernel R (V.generators s)}
    {FM : ∀ f, (kernelsOf K f).Map} {GM : ∀ f, (kernelsOf J f).Map}
    (kernels : K = J) (maps : ∀ f, HEq (FM f) (GM f)) :
    quotientStructure K FM = quotientStructure J GM := by
  subst J
  have same : FM = GM := funext (fun f => eq_of_heq (maps f))
  subst GM
  rfl

namespace Data

/-- The ambient kernel takes the retained kernel at selected sorts. -/
noncomputable def ambientKernel (a : Data R U) (s : V.SortName) : Kernel R (V.generators s) := by
  classical
  exact if keep : Declaration.sort (some s) ∈ U.declarations then a.kernel s keep else ⊥

/-- At a retained sort no default kernel contributes to the interpretation. -/
theorem ambientKernel_kept (a : Data R U) {s : V.SortName}
    (keep : Declaration.sort (some s) ∈ U.declarations) :
    a.ambientKernel s = a.kernel s keep := by
  classical
  exact dif_pos keep

/-- The ambient carrier uses the actual coefficient ring and each standard quotient of coordinates. -/
abbrev carrier (a : Data R U) : Option V.SortName → Type u :=
  quotientCarriers a.ambientKernel

/-- The coefficient carrier is the fixed ring. -/
theorem carrier_coefficients (a : Data R U) : a.carrier none = R :=
  rfl

/-- The retained module carrier is the indicated marked quotient. -/
theorem carrier_module (a : Data R U) {s : V.SortName}
    (keep : Declaration.sort (some s) ∈ U.declarations) : a.carrier (some s) = Quotient (a.kernel s keep) :=
  congrArg Quotient (a.ambientKernel_kept keep)

/-- The ambient input and result kernels of a multilinear operation. -/
noncomputable def ambientOperationKernels (a : Data R U) (f : V.Multilinear) : OperationKernels (V := V) R f :=
  kernelsOf a.ambientKernel f

/-- At a retained symbol the ambient map type is given by the retained kernels. -/
theorem ambientOperationKernels_kept (a : Data R U) {f : V.Multilinear}
    (keep : V.multilinearDecl L f ∈ U.declarations) :
    a.ambientOperationKernels f = operationKernels a.kernel keep :=
  OperationKernels.ext (fun i => a.ambientKernel_kept (V.multilinear_input_kept keep i))
    (a.ambientKernel_kept (V.multilinear_output_kept keep))

/-- Read the actual multilinear map at a retained symbol, with zero on omitted symbols. -/
noncomputable def ambientOperation (a : Data R U) (f : V.Multilinear) : (a.ambientOperationKernels f).Map := by
  classical
  exact if keep : V.multilinearDecl L f ∈ U.declarations then
    cast (congrArg OperationKernels.Map (a.ambientOperationKernels_kept keep).symm) (a.operation f keep)
    else 0

/-- The ambient operation reads the retained map on the corresponding equal quotient modules. -/
theorem ambientOperation_kept (a : Data R U) {f : V.Multilinear}
    (keep : V.multilinearDecl L f ∈ U.declarations) :
    HEq (a.ambientOperation f) (a.operation f keep) := by
  classical
  rw [ambientOperation, dif_pos keep]
  exact cast_heq _ _

/-- Evaluate a tuple of arguments by the ring, the module blocks or the indicated multilinear map. -/
noncomputable def totalValue (a : Data R U) (f : V.Symbol)
    (xs : Assignment a.carrier (V.arity f).inputs) : a.carrier (V.arity f).output :=
  operationValue a.ambientKernel a.ambientOperation f xs

/-- The canonical marked data interpret the original total SHIGURE structure. -/
noncomputable def structureData (a : Data R U) : Structure V.signature :=
  quotientStructure a.ambientKernel a.ambientOperation

/-- The structure's primitive operation is exactly the indicated coefficient, module or map value. -/
theorem structure_total (a : Data R U) (f : V.Symbol) (xs : Assignment a.carrier (V.arity f).inputs) :
    a.structureData.total f xs = a.totalValue f xs :=
  rfl

/-- The selected context structure reads just the retained part of the marked value data. -/
noncomputable def contextStructure (a : Data R U) : ContextStructure U :=
  ContextStructure.ofStructure U a.structureData

/-- The semantic reading of a supported Law is its ordinary satisfaction on the marked values. -/
theorem contextStructure_satisfies_iff (a : Data R U) (law : Law V.signature)
    (kept : Declaration.lawBody (P := V.presentation L) law ⊆ U.declarations) :
    a.contextStructure.evaluation.satisfies law kept ↔ law.Holds a.structureData :=
  ContextStructure.ofStructure_satisfies_iff U a.structureData law kept

end Data
end SHIGURE.Marked
