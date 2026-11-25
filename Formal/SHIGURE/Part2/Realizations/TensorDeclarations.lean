import Formal.SHIGURE.Part2.Realizations.TensorMode
import Formal.SHIGURE.Part2.Realizations.TensorRestriction

/-!
# Tensor Law declarations and their contexts

A tensor equation is written over a dependency-closed primitive signature.
A larger context can evaluate it by restricting the actual module
structure to that signature. Required Law names and their equations come
from the declarations retained by the context.
-/

universe u

noncomputable section

namespace SHIGURE

/-- Primitive sort declarations in a written tensor shape. -/
def TensorShape.support {P : PrimitivePresentation.{u}} {K : Type u}
    (name : K → P.signature.SortType) : TensorShape K → Set (Declaration P)
  | .unit => ∅
  | .sort s => {Declaration.sort (name s)}
  | .arguments Γ => Declaration.sorts (Γ.map name)
  | .tensor X Y => X.support name ∪ Y.support name

/-- Sorts in the types and primitive symbols appearing anywhere in a written tensor expression. -/
def TensorExpression.support {P : PrimitivePresentation.{u}} {R : Type u} {sig : Signature.{u}}
    (names : SignatureNames sig P.signature) {X Y : TensorShape sig.SortType}
    (e : TensorExpression R sig X Y) : Set (Declaration P) :=
  X.support names.onSort ∪ Y.support names.onSort ∪
    match e with
    | .total f => {Declaration.total (names.onTotal f)}
    | .quantity q => {Declaration.quantity (names.onQuantity q)}
    | .comp f g => f.support names ∪ g.support names
    | .tensor f g => f.support names ∪ g.support names
    | .add f g => f.support names ∪ g.support names
    | .smul _ f => f.support names
    | _ => ∅

/-- Both written expressions contribute their symbols and types to the Law's support. -/
def TensorLaw.support {P : PrimitivePresentation.{u}} {R : Type u} {sig : Signature.{u}}
    (law : TensorLaw R sig) (names : SignatureNames sig P.signature) : Set (Declaration P) :=
  law.left.support names ∪ law.right.support names

/-- A tensor Law is written on the primitive declarations it is allowed to use. -/
structure ScopedTensorLaw (base : CoefficientRing.{u}) (P : PrimitivePresentation.{u}) where
  /-- The retained primitive signature used when writing the equation. -/
  scope : DeclarationContext P
  /-- The original tensor statement. -/
  equation :
    letI := base.ring
    TensorLaw base.Carrier (DeclarationContext.Selected.signature scope)

  /-- The written signature is the least context containing the actual support. -/
  scope_exact :
    DeclarationContext.closure (equation.support (DeclarationContext.Selected.names scope)) = scope

/-- Only the primitive symbols actually occurring in a Law are required to retain it. -/
theorem ScopedTensorLaw.scope_le_iff_support {base : CoefficientRing.{u}} {P : PrimitivePresentation.{u}}
    (law : ScopedTensorLaw base P) (V : DeclarationContext P) :
    law.scope ≤ V ↔ law.equation.support (DeclarationContext.Selected.names law.scope) ⊆ V.declarations :=
  (Iff.of_eq (congrArg (· ≤ V) law.scope_exact.symm)).trans DeclarationContext.closure_le_iff

/-- The named tensor declarations of a primitive presentation. -/
structure TensorLawDeclarations (base : CoefficientRing.{u}) (P : PrimitivePresentation.{u}) where
  /-- Names of tensor Laws. -/
  Name : Type u
  /-- The written Law associated to each name. -/
  statement : Name → ScopedTensorLaw base P
  /-- Which declared Laws are required. -/
  required : Set Name

/-- A choice of retained primitive declarations and tensor Law names closed under
the primitive dependencies of each retained Law. -/
structure TensorDeclarationContext {base : CoefficientRing.{u}} {P : PrimitivePresentation.{u}}
    (D : TensorLawDeclarations base P) where
  /-- The dependency-closed primitive declaration context. -/
  primitives : DeclarationContext P
  /-- The chosen primitives have no separate required positive declarations. -/
  noPositiveRequirement : IsEmpty (DeclarationContext.Selected.presentation primitives).theory.LawName
  /-- All tensor Law declarations retained by this context. -/
  retained : Set D.Name
  /-- Each retained equation can be evaluated in this primitive context. -/
  dependencies (l : D.Name) : l ∈ retained →
    (D.statement l).equation.support (DeclarationContext.Selected.names (D.statement l).scope) ⊆
      primitives.declarations

namespace TensorDeclarationContext

variable {base : CoefficientRing.{u}} {P : PrimitivePresentation.{u}} {D : TensorLawDeclarations base P}
variable (U : TensorDeclarationContext D)

/-- Required tensor names are exactly the required declarations retained by the context. -/
abbrev Required := {l : D.Name // l ∈ D.required ∧ l ∈ U.retained}

/-- Each required name carries its original tensor statement and its dependency inclusion. -/
def presentation : RealizationTheory.{u} where
  signature := DeclarationContext.Selected.signature U.primitives
  LawName := U.Required
  Statement := {law : ScopedTensorLaw base P // law.scope ≤ U.primitives}
  law l := ⟨D.statement l.val, ((D.statement l.val).scope_le_iff_support U.primitives).mpr
    (U.dependencies l.val l.property.2)⟩

/-- Interpret the written tensor Law on the actual structure restricted to its scope. -/
def holds (S : CoefficientAlgebra base)
    (A : TensorAt S.scalars (DeclarationContext.Selected.signature U.primitives))
    (law : U.presentation.Statement) : Prop :=
  letI := base.ring
  letI := S.scalars.ring
  (law.val.equation.mapScalars S.fromBase).holds
    (A.restrict (DeclarationContext.Selected.namesOfLE law.property))

/-- The coefficient mode of the closed tensor declarations. -/
def mode (scope : FullDomainTensorSignature U.presentation.signature)
    (rule : TensorCoefficientRule U.presentation.signature) :
    CoefficientRealizationMode base U.presentation :=
  tensorModeOfPresentation base U.presentation scope rule U.holds

end TensorDeclarationContext

/-- The semantic category with exactly the written tensor Laws retained by the context. -/
abbrev SelectedTensorModels {base : CoefficientRing.{u}} {P : PrimitivePresentation.{u}}
    {D : TensorLawDeclarations base P} (U : TensorDeclarationContext D) (S : CoefficientAlgebra base)
    (scope : FullDomainTensorSignature U.presentation.signature)
    (rule : TensorCoefficientRule U.presentation.signature) :=
  (U.mode scope rule).Models S

/-- A model in the selected category satisfies the actual equation at each required name. -/
theorem selectedTensorModel_holds {base : CoefficientRing.{u}} {P : PrimitivePresentation.{u}}
    {D : TensorLawDeclarations base P} {U : TensorDeclarationContext D} {S : CoefficientAlgebra base}
    {scope : FullDomainTensorSignature U.presentation.signature}
    {rule : TensorCoefficientRule U.presentation.signature} (A : SelectedTensorModels U S scope rule)
    (l : U.Required) : U.holds S A.obj (U.presentation.law l) :=
  A.property.2 l

end SHIGURE
