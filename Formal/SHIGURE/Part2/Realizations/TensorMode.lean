import Formal.SHIGURE.Part1.ContextSelectedPresentation
import Formal.SHIGURE.Part2.Realizations.CoefficientModels
import Formal.SHIGURE.Part2.Realizations.TensorExpressions
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# The tensor mode as a coefficient realization

The mode uses arbitrary module carriers and includes every linear family
preserving the specified operations. The coefficient rule compares the
changed carriers with actual scalar extensions and specifies the primitive
operations there on generating tuples. Construction 4.8 supplies this rule.
-/

open CategoryTheory
open scoped TensorProduct

universe u

noncomputable section

namespace SHIGURE

/-- Tensor structures over a specified coefficient ring. -/
abbrev TensorAt (R : CoefficientRing.{u}) (sig : Signature.{u}) :=
  letI := R.ring
  TensorStructure R.Carrier sig

variable {sig : Signature.{u}}

/-- A tensor coefficient rule specifies scalar-extended carriers and the
values of the changed operations on the generating tuples. -/
structure TensorCoefficientRule (sig : Signature.{u}) where
  /-- The raw structure at the new coefficient ring. -/
  change {R S : CoefficientRing.{u}} (f : R.Hom S) : TensorAt R sig → TensorAt S sig
  /-- The carrier comparison with extension of scalars. -/
  carrierIso {R S : CoefficientRing.{u}} (f : R.Hom S) (A : TensorAt R sig) (s : sig.SortType) :
    letI := R.ring
    letI := S.ring
    letI := f.toAlgebra
    (S.Carrier ⊗[R.Carrier] A.carrier s) ≃ₗ[S.Carrier] (change f A).carrier s
  /-- Changed operations take a tuple of unit tensors to the unit tensor of the original value. -/
  total_unit {R S : CoefficientRing.{u}} (f : R.Hom S) (A : TensorAt R sig) (op : sig.Total) :
    letI := R.ring
    letI := S.ring
    letI := f.toAlgebra
    ∀ (x : ∀ i : (s : sig.SortType) × Var (sig.totalArity op).inputs s, A.carrier i.1),
      (change f A).total op (fun i => carrierIso f A i.1 ((1 : S.Carrier) ⊗ₜ[R.Carrier] x i)) =
        carrierIso f A _ ((1 : S.Carrier) ⊗ₜ[R.Carrier] (A.total op x))
  /-- Changed quantities take a tuple of unit tensors to the unit tensor of the original value. -/
  quantity_unit {R S : CoefficientRing.{u}} (f : R.Hom S) (A : TensorAt R sig) (q : sig.Quantity) :
    letI := R.ring
    letI := S.ring
    letI := f.toAlgebra
    ∀ (x : ∀ i : (s : sig.SortType) × Var (sig.quantityArity q).inputs s, A.carrier i.1),
      (change f A).quantity q (fun i => carrierIso f A i.1 ((1 : S.Carrier) ⊗ₜ[R.Carrier] x i)) =
        carrierIso f A _ ((1 : S.Carrier) ⊗ₜ[R.Carrier] (A.quantity q x))

/-- The coefficient map on a state sends it to its unit tensor under the carrier comparison. -/
def TensorCoefficientRule.changeState (rule : TensorCoefficientRule sig)
    {R S : CoefficientRing.{u}} (f : R.Hom S) (A : TensorAt R sig) (s : sig.SortType) :
    letI := R.ring
    letI := S.ring
    A.carrier s → (rule.change f A).carrier s :=
  letI := R.ring
  letI := S.ring
  letI := f.toAlgebra
  fun x => rule.carrierIso f A s ((1 : S.Carrier) ⊗ₜ[R.Carrier] x)

variable {R : Type u} [CommRing R]

/-- Tensor preservation is the condition of commuting with the primitive
operations and quantities on a family of module arrows. -/
def tensorStructureRule (R : Type u) [CommRing R] (sig : Signature.{u}) :
    StructureRule (fun _ : sig.SortType => Cat.of (ModuleCat.{u} R)) (TensorStructure R sig) where
  carrier A := A.carrier
  preserves f := ∃ h : TensorStructure.Hom _ _, (fun s => ModuleCat.ofHom (h.onSort s)) = f
  preserves_id A := ⟨TensorStructure.Hom.id A, rfl⟩
  preserves_comp := by
    rintro A B D f g ⟨f', rfl⟩ ⟨g', rfl⟩
    exact ⟨f'.comp g', rfl⟩

/-- The carrier tuples in the general structure rule are exactly the
structure-preserving linear maps. -/
def tensorStructureHomEquiv (sig : Signature.{u})
    (A B : (tensorStructureRule R sig).Category) :
    (A ⟶ B) ≃ TensorStructure.Hom A B where
  toFun h := h.property.choose
  invFun h := ⟨fun s => ModuleCat.ofHom (h.onSort s), ⟨h, rfl⟩⟩
  left_inv h := Subtype.ext h.property.choose_spec
  right_inv h := by
    apply TensorStructure.Hom.ext
    funext s
    exact congrArg (fun f => (f s).hom) (Exists.choose_spec (⟨h, rfl⟩ :
      ∃ g : TensorStructure.Hom A B, (fun i => ModuleCat.ofHom (g.onSort i)) =
        (fun i => ModuleCat.ofHom (h.onSort i))))

/-- The typed interpretation of every named required Law of a theory over the base. -/
abbrev TensorLawInterpretation (base : CoefficientRing.{u}) (T : Theory.{u}) :=
  letI := base.ring
  T.LawName → TensorLaw base.Carrier T.signature

/-- The full-domain tensor mode of Definition 4.1, with named Laws and its
specified coefficient rule. -/
def tensorMode (base : CoefficientRing.{u}) (T : Theory.{u})
    (rule : TensorCoefficientRule T.signature) (law : TensorLawInterpretation base T) :
    CoefficientRealizationMode base T where
  Object S := TensorAt S.scalars T.signature
  Carrier S _ :=
    letI := S.scalars.ring
    Cat.of (ModuleCat.{u} S.scalars.Carrier)
  rule S :=
    letI := S.scalars.ring
    tensorStructureRule S.scalars.Carrier T.signature
  admissible _ _ := FullDomainTensorSignature T.signature
  Native := TensorAt base T.signature
  nativeStates A s :=
    letI := base.ring
    A.carrier s
  States S A s :=
    letI := S.scalars.ring
    A.carrier s
  realizeNative S := rule.change S.fromBase
  nativePoints S := rule.changeState S.fromBase
  change f := rule.change f
  changePoints f := rule.changeState f
  holds S A name :=
    letI := base.ring
    letI := S.scalars.ring
    ((law name).mapScalars S.fromBase).holds A

/-- The tensor semantics of exactly the declarations selected by the context. -/
abbrev SelectedTensorModels {P : PrimitivePresentation.{u}} (U : DeclarationContext P)
    {base : CoefficientRing.{u}} (S : CoefficientAlgebra base)
    (rule : TensorCoefficientRule (DeclarationContext.Selected.presentation U).signature)
    (law : TensorLawInterpretation base (DeclarationContext.Selected.presentation U).theory) :=
  (tensorMode base (DeclarationContext.Selected.presentation U).theory rule law).Models S

end SHIGURE
