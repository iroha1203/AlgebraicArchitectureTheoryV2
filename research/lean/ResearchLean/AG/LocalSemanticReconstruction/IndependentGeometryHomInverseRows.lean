import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitiveDeclaration
import ResearchLean.AG.LocalSemanticReconstruction.IndependentInverseGraphReadings
import Formal.Util.AssertStandardAxioms

/-!
# Inverse-role projections of the common Hom declaration

Common Hom pairs retain source/target order in both direction tags. The
independent inverse-graph API instead places the backward input first.
Reversing that primitive point pair is the exact conversion; it introduces
no selected function or equivalence. Every inverse native role uses this
same conversion explicitly.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.InverseRows

universe u v

open Site

variable {U : AtomCarrier.{u}} {mode : Mode}

/-- Reverse the two primitive carrier references and their corresponding points. -/
def reverse : IndependentCarrierGraph.Query.{u, v} → IndependentCarrierGraph.Query.{v, u}
  | .edge S T x y => .edge T S y x

/-- Reversing a primitive carrier point pair twice restores it exactly. -/
theorem reverse_reverse (q : IndependentCarrierGraph.Query.{u, v}) : reverse (reverse q) = q := by
  cases q
  rfl

/-- Convert common ordered direction-tagged points to the native inverse-graph orientation. -/
def asInverse (p : Direction → IndependentCarrierGraph.Table.{u, u}) : IndependentInverseGraph.Table.{u, u}
  | .forward q => p .forward q
  | .backward q => p .backward (reverse q)

/-- Recover common source/target-ordered points from a pair of independently oriented graphs. -/
def fromInverse (p : IndependentInverseGraph.Table.{u, u}) : Direction → IndependentCarrierGraph.Table.{u, u}
  | .forward, q => p (.forward q)
  | .backward, q => p (.backward (reverse q))

/-- The orientation conversion preserves every forward and backward candidate point. -/
theorem asInverse_fromInverse (p : IndependentInverseGraph.Table.{u, u}) :
    asInverse (fromInverse p) = p := by
  funext q
  cases q with
  | forward q => rfl
  | backward q => simp only [asInverse, fromInverse, reverse_reverse]

/-- Common ordered pairs are also exactly recovered after both orientation conversions. -/
theorem fromInverse_asInverse (p : Direction → IndependentCarrierGraph.Table.{u, u}) :
    fromInverse (asInverse p) = p := by
  funext direction q
  cases direction with
  | forward => rfl
  | backward => simp only [asInverse, fromInverse, reverse_reverse]

/-- Equation-index inverse points, declared before either native equation-index carrier. -/
def equation (h : Table.{u, v} U mode) (A B : ArchitectureObject U) : IndependentInverseGraph.Table.{u, u} :=
  asInverse (fun direction q => h (.atObjects A B (.equation direction q)))

/-- Observable inverse points at one candidate forward-context pair. -/
def observable (h : Table.{u, v} U mode) (A B : ArchitectureObject U) (W : ArchCtx A) (V : ArchCtx B) :
    IndependentInverseGraph.Table.{u, u} :=
  asInverse (fun direction q => h (.atObjects A B (.observable direction W V q)))

/-- Signature-coordinate inverse points at a candidate axis carrier/point pair. -/
def signatureCoordinate (h : Table.{u, v} U mode) (I J : Type u) (i : I) (j : J) :
    IndependentInverseGraph.Table.{u, u} :=
  asInverse (fun direction q => h (.signatureCoordinate direction I J i j q))

/-- Explicit raw coordinate inverse points at a candidate inverse-context pair. -/
def coordinate (h : Table.{u, v} U .explicit) (A B : ArchitectureObject U)
    (W : ArchCtx A) (V : ArchCtx B) : IndependentInverseGraph.Table.{u, u} :=
  asInverse (fun direction q => h (.atObjects A B (.raw (.coordinate direction W V q))))

/-- Explicit local-data inverse points at candidate coordinate carrier/point references. -/
def localData (h : Table.{u, v} U .explicit) (A B : ArchitectureObject U)
    (W : ArchCtx A) (V : ArchCtx B) (C D : Type u) (c : C) (d : D) : IndependentInverseGraph.Table.{u, u} :=
  asInverse (fun direction q => h (.atObjects A B (.raw (.localData direction W V C D c d q))))

/-- Explicit relation-generator inverse points retain the same inverse-context indexing. -/
def relation (h : Table.{u, v} U .explicit) (A B : ArchitectureObject U)
    (W : ArchCtx A) (V : ArchCtx B) : IndependentInverseGraph.Table.{u, u} :=
  asInverse (fun direction q => h (.atObjects A B (.raw (.relation direction W V q))))

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.InverseRows

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.InverseRows
