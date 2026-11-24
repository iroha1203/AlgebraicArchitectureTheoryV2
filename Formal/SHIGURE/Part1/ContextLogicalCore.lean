import Formal.SHIGURE.Part1.ContextSupports

/-! # Logical declaration dependencies

An ordered residual's ring presentation is optional evaluation metadata.
The Chapter 3 contexts retain written Laws, required roles, derivations and
primitive declarations. A reading that also needs the optional ring data
uses the stronger attachment dependencies of the annotated presentation.
-/

universe u

namespace SHIGURE
namespace PrimitivePresentation

/-- The primitive language and proof data, independently of optional residual metadata. -/
def logicalCore (P : PrimitivePresentation.{u}) : PrimitivePresentation.{u} where
  signature := P.signature
  laws := P.laws
  domainInclusions := P.domainInclusions
  derived := P.derived

/-- Logical cores retain every declaration name and its kind. -/
def logicalNames (P : PrimitivePresentation.{u}) : Declaration P ≃ Declaration P.logicalCore where
  toFun
    | .sort s => .sort s
    | .total f => .total f
    | .relation r => .relation r
    | .partialOp p => .partialOp p
    | .quantity q => .quantity q
    | .law i => .law i
  invFun
    | .sort s => .sort s
    | .total f => .total f
    | .relation r => .relation r
    | .partialOp p => .partialOp p
    | .quantity q => .quantity q
    | .law i => .law i
  left_inv d := by cases d <;> rfl
  right_inv d := by cases d <;> rfl

/-- The attached original proof of a derived Law is retained verbatim. -/
theorem logicalCore_derived (P : PrimitivePresentation.{u}) (name : P.laws.LawName)
    (role : P.laws.role name = .derived) : P.logicalCore.derived name role = P.derived name role :=
  rfl

/-- The logical dependencies of a Law are its written support and its actual derived proof, when present. -/
theorem logicalCore_law_dependencies (P : PrimitivePresentation.{u}) (name : P.laws.LawName) :
    Declaration.dependsOn P.logicalCore (.law name) =
      Declaration.lawBody (P := P.logicalCore) (P.laws.statement name) ∪
      match role : P.laws.role name with
      | .derived => Declaration.derivation (P := P.logicalCore) (P.derived name role)
      | .required | .additional => ∅ := by
  simp only [Declaration.dependsOn, Declaration.ringEquationSupport, logicalCore, Set.empty_union]
  rfl

/-- Required and additional written Laws have no proof-tree dependencies. -/
theorem logicalCore_nonderived_dependencies (P : PrimitivePresentation.{u}) (name : P.laws.LawName)
    (role : P.laws.role name ≠ .derived) :
    Declaration.dependsOn P.logicalCore (.law name) =
      Declaration.lawBody (P := P.logicalCore) (P.laws.statement name) := by
  rw [logicalCore_law_dependencies]
  split
  · rename_i h
    exact (role h).elim
  · exact Set.union_empty _
  · exact Set.union_empty _

end PrimitivePresentation

/-- A Chapter 3 declaration context uses the four logical dependency rules of Definition 3.1. -/
abbrev ChapterContext (P : PrimitivePresentation.{u}) := DeclarationContext P.logicalCore

end SHIGURE
