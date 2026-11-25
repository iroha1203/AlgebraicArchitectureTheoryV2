import Formal.SHIGURE.Part2.Realizations.TensorMode
import Formal.SHIGURE.Part2.Realizations.TensorRestriction

/-!
# Tensor Law declarations and their contexts

A tensor equation is written over a dependency-closed primitive signature.
A larger context can evaluate it by restricting the actual module
structure to that signature. Required Law names and their equations come
from the declarations retained by the context.

## Implementation notes

The primitive dependencies use Part I's closed contexts. A tensor Law
has its own typed equation and name because tensor shape and linear
equality are part of that declaration. Storing the equation on its
exact support lets the same statement be evaluated in different
contexts by restricting their structures. A fixed ambient signature
would make an equation depend on every sort and operation of that
signature when reading it in a smaller context.
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
  /-- The symbols interpreted by the full-domain tensor structure. -/
  fullDomain : FullDomainTensorSignature (DeclarationContext.Selected.signature primitives)
  /-- A tensor reading of each original required Law retained from Part I. -/
  positiveReading : ∀ l : (DeclarationContext.Selected.presentation primitives).theory.LawName,
    TensorLawReading base fullDomain ((DeclarationContext.Selected.presentation primitives).theory.law l)
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

/-- Together, the retained required names carry the compatible readings of Part I Laws and
the original equations and scopes of native tensor declarations. -/
def presentation : RealizationTheory.{u} where
  signature := DeclarationContext.Selected.signature U.primitives
  LawName := (DeclarationContext.Selected.presentation U.primitives).theory.LawName ⊕ U.Required
  Statement :=
    letI := base.ring
    TensorLaw base.Carrier (DeclarationContext.Selected.signature U.primitives) ⊕
      {law : ScopedTensorLaw base P // law.scope ≤ U.primitives}
  law
    | .inl l => .inl (U.positiveReading l).equation
    | .inr l => .inr ⟨D.statement l.val, ((D.statement l.val).scope_le_iff_support U.primitives).mpr
        (U.dependencies l.val l.property.2)⟩

/-- Interpret the written tensor Law on the actual structure restricted to its scope. -/
def holds (S : CoefficientAlgebra base) (A : TensorAt S.scalars U.presentation.signature) :
    U.presentation.Statement → Prop :=
  letI := base.ring
  letI := S.scalars.ring
  fun
    | .inl law => (law.mapScalars S.fromBase).holds A
    | .inr law => (law.val.equation.mapScalars S.fromBase).holds
        (A.restrict (DeclarationContext.Selected.namesOfLE law.property))

/-- The coefficient mode of the closed tensor declarations. -/
def modeWithRule (rule : TensorCoefficientRule U.presentation.signature) :
    CoefficientRealizationMode base U.presentation :=
  tensorModeOfPresentation base U.presentation U.fullDomain rule U.holds

end TensorDeclarationContext

/-- The semantic category with exactly the written tensor Laws retained by the context. -/
abbrev SelectedTensorModels {base : CoefficientRing.{u}} {P : PrimitivePresentation.{u}}
    {D : TensorLawDeclarations base P} (U : TensorDeclarationContext D) (S : CoefficientAlgebra base) :=
  TensorModelsAt U.presentation S U.fullDomain (U.holds S)

/-- A model in the selected category satisfies the actual equation at each required name. -/
theorem selectedTensorModel_holds {base : CoefficientRing.{u}} {P : PrimitivePresentation.{u}}
    {D : TensorLawDeclarations base P} {U : TensorDeclarationContext D} {S : CoefficientAlgebra base}
    (A : SelectedTensorModels U S) (l : U.Required) :
    U.holds S A.obj (U.presentation.law (.inr l)) :=
  A.property.2 (.inr l)

/-- The same object also satisfies each retained required Law written in Part I. -/
theorem selectedTensorModel_holds_positive {base : CoefficientRing.{u}} {P : PrimitivePresentation.{u}}
    {D : TensorLawDeclarations base P} {U : TensorDeclarationContext D} {S : CoefficientAlgebra base}
    (A : SelectedTensorModels U S) (l : (DeclarationContext.Selected.presentation U.primitives).theory.LawName) :
    letI := S.scalars.ring
    ((DeclarationContext.Selected.presentation U.primitives).theory.law l).Holds
      (A.obj.elementStructure U.fullDomain) :=
  ((U.positiveReading l).correct S A.obj).mp (A.property.2 (.inl l))

end SHIGURE
