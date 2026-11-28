import Formal.SHIGURE.Part2.Families.SchemeTensorStructures
import Formal.SHIGURE.Part2.Realizations.TensorInputs

/-! # Interpreting scheme tensor structures on open sections

The primitive maps in Definition 6.1 induce the existing multilinear
`TensorStructure` on every open set. These comparisons interpret written
tensor and polynomial Laws on the actual module-sheaf carriers.

## Implementation notes

The map from the tensor of sections to sections of the tensor sheaf is
the sheafification unit, extracted using `tensorModuleHomEquiv`.
Iterating this linear map, with the existing ordered-input comparisons,
gives a linear map from `InputTensor`; composing with mathlib's universal
pure tensor gives a multilinear map without choosing bases or assuming
that sections commute with sheaf tensor products. Only the canonical
map is used; no surjectivity or isomorphism of section tensors is assumed.
-/

namespace SHIGURE.RealizationFamilies

open AlgebraicGeometry CategoryTheory Opposite SchemeDescent TensorRealization
open scoped TensorProduct

noncomputable section

universe u

variable {X : Scheme.{u}} {S : Type u} {sig : Signature.{u}}

/-- The canonical linear map from a tensor of sections to sections of the
tensor sheaf. This API is the unit of module sheafification, not an affine
comparison isomorphism. -/
def sectionTensorMap (M N : X.Modules) (U : X.Opens) :
    (M.val.obj (op U) ⊗[Γ(X, U)] N.val.obj (op U)) →ₗ[Γ(X, U)]
      (tensorModule M N).val.obj (op U) :=
  ((tensorModuleHomEquiv M N (tensorModule M N) (𝟙 _)).app (op U)).hom

/-- The tensor-of-sections map commutes with the actual semilinear
restriction maps. This is the binary comparison API for Definition 6.1. -/
theorem sectionTensorMap_restrict_tmul (M N : X.Modules) {U V : X.Opens}
    (inside : V ≤ U) (x : M.val.obj (op U)) (y : N.val.obj (op U)) :
    (tensorModule M N).val.map (homOfLE inside).op
        (sectionTensorMap M N U (x ⊗ₜ[Γ(X, U)] y)) =
      sectionTensorMap M N V
        (M.val.map (homOfLE inside).op x ⊗ₜ[Γ(X, V)]
          N.val.map (homOfLE inside).op y) := by
  exact (PresheafOfModules.naturality_apply
    (tensorModuleHomEquiv M N (tensorModule M N) (𝟙 _))
    (homOfLE inside).op (x ⊗ₜ[Γ(X, U)] y)).symm

/-- The canonical tensor-of-sections map on an ordered input context.
Implementation notes: the recursion uses the existing `InputTensor` unit
and first-factor equivalences, followed by the sheafification-unit map.
It retains repeated input sorts as distinct typed positions. -/
def inputSectionsMap (E : S → X.Modules) (U : X.Opens) :
    (Γ : List S) →
      InputTensor Γ(X, U) (fun s => (E s).val.obj (op U)) Γ →ₗ[Γ(X, U)]
        (tensorModules E Γ).val.obj (op U)
  | [] => (inputTensorUnit Γ(X, U) (fun s => (E s).val.obj (op U))).toLinearMap
  | s :: ss =>
    (sectionTensorMap (E s) (tensorModules E ss) U).comp
      ((TensorProduct.map LinearMap.id (inputSectionsMap E U ss)).comp
        (inputTensorCons Γ(X, U) (fun s => (E s).val.obj (op U)) s ss).toLinearMap)

/-- A tuple of sections gives its pure tensor section.
Implementation notes: composition with the universal multilinear map
provides multilinearity over the section ring, including the empty arity. -/
def pureTensorSections (E : S → X.Modules) (U : X.Opens) (Γ : List S) :
    MultilinearMap Γ(X, U) (fun i : TensorPosition Γ => (E i.1).val.obj (op U))
      ((tensorModules E Γ).val.obj (op U)) :=
  (inputSectionsMap E U Γ).compMultilinearMap (PiTensorProduct.tprod Γ(X, U))

/-- API for the pure tensor on an empty context: its value is the unit
section. The simplifier evaluates the empty pure tensor. -/
@[simp]
theorem pureTensorSections_nil (E : S → X.Modules) (U : X.Opens)
    (x : ∀ i : TensorPosition ([] : List S), (E i.1).val.obj (op U)) :
    pureTensorSections E U [] x = (1 : Γ(X, U)) := by
  exact inputTensorUnit_tprod Γ(X, U) (fun s => (E s).val.obj (op U)) x

/-- API for a pure tensor on a nonempty context: split off its first entry.
The simplifier exposes the binary tensor-of-sections map. -/
@[simp]
theorem pureTensorSections_cons (E : S → X.Modules) (U : X.Opens)
    (s : S) (ss : List S)
    (x : ∀ i : TensorPosition (s :: ss), (E i.1).val.obj (op U)) :
    pureTensorSections E U (s :: ss) x =
      sectionTensorMap (E s) (tensorModules E ss) U
        (x ⟨s, .here⟩ ⊗ₜ[Γ(X, U)]
          pureTensorSections E U ss (fun i => x ⟨i.1, .there i.2⟩)) := by
  change sectionTensorMap (E s) (tensorModules E ss) U
    ((TensorProduct.map LinearMap.id (inputSectionsMap E U ss))
      (inputTensorCons Γ(X, U) (fun s => (E s).val.obj (op U)) s ss
        (PiTensorProduct.tprod Γ(X, U) x))) = _
  rw [inputTensorCons_tprod, TensorProduct.map_tmul]
  rfl

/-- Ordered pure tensor sections commute with semilinear restriction.
This API transports the primitive-operation input tuples between opens. -/
theorem pureTensorSections_restrict (E : S → X.Modules) {U V : X.Opens}
    (inside : V ≤ U) (ss : List S)
    (x : ∀ i : TensorPosition ss, (E i.1).val.obj (op U)) :
    (tensorModules E ss).val.map (homOfLE inside).op (pureTensorSections E U ss x) =
      pureTensorSections E V ss
        (fun i => (E i.1).val.map (homOfLE inside).op (x i)) := by
  induction ss with
  | nil =>
    rw [pureTensorSections_nil, pureTensorSections_nil]
    exact map_one (X.presheaf.map (homOfLE inside).op).hom
  | cons s ss ih =>
    rw [pureTensorSections_cons, pureTensorSections_cons]
    change (tensorModule (E s) (tensorModules E ss)).val.map (homOfLE inside).op
      (sectionTensorMap (E s) (tensorModules E ss) U
        (x ⟨s, .here⟩ ⊗ₜ[Γ(X, U)]
          pureTensorSections E U ss (fun i => x ⟨i.1, .there i.2⟩))) = _
    rw [sectionTensorMap_restrict_tmul, ih]

/-- The primitive operation on sections induced by an actual tensor-sheaf
morphism. Implementation notes: the map is composed with the canonical
pure tensor section; no basis or local freeness is used. -/
def sectionOperation (E : S → X.Modules) (U : X.Opens) (a : Arity S)
    (f : tensorModules E a.inputs ⟶ E a.output) :
    TensorOperation Γ(X, U) (fun s => (E s).val.obj (op U)) a :=
  (f.val.app (op U)).hom.compMultilinearMap (pureTensorSections E U a.inputs)

/-- API for evaluating a primitive operation on sections: apply its actual
sheaf map to the pure tensor section. The simplifier evaluates this comparison. -/
@[simp]
theorem sectionOperation_apply (E : S → X.Modules) (U : X.Opens) (a : Arity S)
    (f : tensorModules E a.inputs ⟶ E a.output)
    (x : ∀ i : TensorPosition a.inputs, (E i.1).val.obj (op U)) :
    sectionOperation E U a f x =
      f.val.app (op U) (pureTensorSections E U a.inputs x) := rfl

/-- Primitive operations on sections commute with the actual semilinear
restriction maps. Its only premise is the given primitive sheaf morphism. -/
theorem sectionOperation_restrict (E : S → X.Modules) {U V : X.Opens}
    (inside : V ≤ U) (a : Arity S) (f : tensorModules E a.inputs ⟶ E a.output)
    (x : ∀ i : TensorPosition a.inputs, (E i.1).val.obj (op U)) :
    (E a.output).val.map (homOfLE inside).op (sectionOperation E U a f x) =
      sectionOperation E V a f
        (fun i => (E i.1).val.map (homOfLE inside).op (x i)) := by
  change (E a.output).val.map (homOfLE inside).op
    (f.val.app (op U) (pureTensorSections E U a.inputs x)) = _
  rw [← PresheafOfModules.naturality_apply, pureTensorSections_restrict]
  rfl

/-- The structure of Definition 6.1 gives a multilinear tensor structure
over the section ring of every open set. Implementation notes: this
connects actual sheaf interpretations to the existing Law semantics. -/
@[simps]
def sectionsStructure (A : SchemeTensorStructure X sig) (U : X.Opens) :
    TensorStructure Γ(X, U) sig where
  carrier s := (A.carrier s).val.obj (op U)
  total op := sectionOperation A.carrier U (sig.totalArity op) (A.total op)
  quantity q := sectionOperation A.carrier U (sig.quantityArity q) (A.quantity q)

/-- API for the section interpretation: total primitives respect the
semilinear restriction maps between arbitrary opens. -/
theorem sectionsStructure_total_restrict (A : SchemeTensorStructure X sig)
    {U V : X.Opens} (inside : V ≤ U) (op : sig.Total)
    (x : ∀ i : TensorPosition (sig.totalArity op).inputs,
      (A.carrier i.1).val.obj (Opposite.op U)) :
    (A.carrier (sig.totalArity op).output).val.map (homOfLE inside).op
        ((sectionsStructure A U).total op x) =
      (sectionsStructure A V).total op
        (fun i => (A.carrier i.1).val.map (homOfLE inside).op (x i)) :=
  sectionOperation_restrict A.carrier inside (sig.totalArity op) (A.total op) x

/-- API for the section interpretation: primitive quantities respect the
semilinear restriction maps between arbitrary opens. -/
theorem sectionsStructure_quantity_restrict (A : SchemeTensorStructure X sig)
    {U V : X.Opens} (inside : V ≤ U) (q : sig.Quantity)
    (x : ∀ i : TensorPosition (sig.quantityArity q).inputs,
      (A.carrier i.1).val.obj (op U)) :
    (A.carrier (sig.quantityArity q).output).val.map (homOfLE inside).op
        ((sectionsStructure A U).quantity q x) =
      (sectionsStructure A V).quantity q
        (fun i => (A.carrier i.1).val.map (homOfLE inside).op (x i)) :=
  sectionOperation_restrict A.carrier inside (sig.quantityArity q) (A.quantity q) x

end

end SHIGURE.RealizationFamilies
