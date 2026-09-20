import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitiveDeclaration
import ResearchLean.AG.LocalSemanticReconstruction.CompleteGeometryGraphAssembly
import Formal.Util.AssertStandardAxioms

/-!
# Overlap transport from primitive context and comparison points

Three inverse-context points select the source triple. Two derived overlap
matching cells select its source and target results. A forward context point
then compares those results in both target preorder directions. Equality of
context objects is not imposed: the native thin-category isomorphism is built
from exactly the two order comparisons.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.Overlap

noncomputable section

universe u v

open Site CategoryTheory AtomFoundation GeometryTransport CompleteGeometryGraphAssembly

variable {U : AtomCarrier.{u}} {mode : Mode} {A B : ArchitectureObject U}

/-- One overlap instance uses six Boolean guard cells and the two original target order cells. -/
def PointLaws (s : IndependentOverlapCandidate.Table A) (t : IndependentOverlapCandidate.Table B)
    (d : IndependentContextPrimitive.Table B) (h : Table.{u, v} U mode) : Prop :=
  ∀ W X Y base left right R S T,
    h (.atObjects A B (.context .backward W base)) = true →
    h (.atObjects A B (.context .backward X left)) = true →
    h (.atObjects A B (.context .backward Y right)) = true →
    (s (.matching W X Y R)).down = true → (t (.matching base left right S)).down = true →
    h (.atObjects A B (.context .forward R T)) = true →
    (d (.le T S)).down ∧ (d (.le S T)).down

variable {G H : GeometryPackage.{u, v} U}

/-- Comparison premises identify the two reconstructed context functions; no overlap certificate is assumed. -/
structure Maps (f : PackageTotalHom G.core H.core) (h : Table.{u, v} U mode) : Prop where
  forward : ∀ W V, h (.atObjects G.core.object H.core.object (.context .forward W V)) = true ↔
    contextMap f W = V
  backward : ∀ W V, h (.atObjects G.core.object H.core.object (.context .backward W V)) = true ↔
    contextBackwardMap f V = W

/-- The independent point condition on the native primitive overlap and context readings. -/
abbrev NativePoints (G H : GeometryPackage.{u, v} U) (h : Table.{u, v} U mode) :=
  PointLaws (IndependentOverlapCandidate.read G.core.contextPreorder G.geometry.overlap)
    (IndependentOverlapCandidate.read H.core.contextPreorder H.geometry.overlap)
    (IndependentContextPrimitive.read H.core.contextPreorder) h

variable (f : PackageTotalHom G.core H.core) (h : Table.{u, v} U mode) (hm : Maps f h)

include hm in
/-- Both original overlap orders are consequences of their actual primitive matching points. -/
theorem orders_of_points (hp : NativePoints G H h) (base left right) :
    overlapSource f base left right ≤ overlapTarget base left right ∧
      overlapTarget base left right ≤ overlapSource f base left right := by
  apply hp (contextBackwardMap f base) (contextBackwardMap f left) (contextBackwardMap f right)
    base left right
    (G.geometry.overlap.overlap (contextBackwardMap f base) (contextBackwardMap f left) (contextBackwardMap f right))
    (H.geometry.overlap.overlap base left right)
    (contextMap f (G.geometry.overlap.overlap
      (contextBackwardMap f base) (contextBackwardMap f left) (contextBackwardMap f right)))
  · exact (hm.backward _ base).2 rfl
  · exact (hm.backward _ left).2 rfl
  · exact (hm.backward _ right).2 rfl
  · simp [IndependentOverlapCandidate.read, IndependentOverlapCandidate.ContextMatch.read]
  · simp [IndependentOverlapCandidate.read, IndependentOverlapCandidate.ContextMatch.read]
  · exact (hm.forward _ _).2 rfl

/-- Construct the original thin-category overlap comparison from the two primitive order directions. -/
def assemble (hp : NativePoints G H h) : OverlapTransport G H f :=
  assembleOverlap (fun base left right => (orders_of_points f h hm hp base left right).1)
    (fun base left right => (orders_of_points f h hm hp base left right).2)

include hm in
/-- The native overlap comparison implies each point instance after the guard cells identify its arguments. -/
theorem points_of_native (hp : OverlapTransport G H f) : NativePoints G H h := by
  classical
  intro W X Y base left right R S T hW hX hY hR hS hT
  obtain rfl := (hm.backward W base).1 hW
  obtain rfl := (hm.backward X left).1 hX
  obtain rfl := (hm.backward Y right).1 hY
  have hr : R = G.geometry.overlap.overlap
      (contextBackwardMap f base) (contextBackwardMap f left) (contextBackwardMap f right) :=
    of_decide_eq_true hR
  have hs : S = H.geometry.overlap.overlap base left right := of_decide_eq_true hS
  subst R
  subst S
  obtain rfl := (hm.forward _ T).1 hT
  exact ⟨leOfHom (hp.overlapIso base left right).hom, leOfHom (hp.overlapIso base left right).inv⟩

include hm in
/-- The primitive order condition holds exactly when the original overlap transport exists. -/
theorem points_iff_native : NativePoints G H h ↔ Nonempty (OverlapTransport G H f) :=
  ⟨fun hp => ⟨assemble f h hm hp⟩, fun ⟨hp⟩ => points_of_native f h hm hp⟩

/-- Thinness makes assembly recover the entire native overlap comparison, with no lost isomorphism choices. -/
theorem assemble_points_of_native (hp : OverlapTransport G H f) :
    assemble f h hm (points_of_native f h hm hp) = hp := Subsingleton.elim _ _

end

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.Overlap

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.Overlap
