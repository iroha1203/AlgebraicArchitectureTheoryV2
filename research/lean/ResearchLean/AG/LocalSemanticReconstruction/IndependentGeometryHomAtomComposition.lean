import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomAtomReadings
import ResearchLean.AG.LocalSemanticReconstruction.IndependentIndexedCarrierComposition
import Formal.Util.AssertStandardAxioms

/-!
# Direct point identity and composition for the two Atom roles

Implementation notes: forward composition queries the second table at the
first forward row's unique point; backward composition queries the first
table at the second backward row's point. Native equivalences are used only
for comparison and closure proofs. Each direction uses two primitive cells.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.Atom

noncomputable section

universe u

variable {U : AtomCarrier.{u}}

/-- Compose direction-tagged Atom points in forward order and reverse backward order. -/
def compose (p : PointTable U) (hp : IsLawful p) (q : PointTable U) (hq : IsLawful q) : PointTable U
  | .forward, a, c => IndependentIndexedCarrierGraph.composeIndex (p .forward) hp.forward (q .forward) a c
  | .backward, a, c => IndependentIndexedCarrierGraph.composeIndex (fun c b => q .backward b c) hq.backward
      (fun b a => p .backward a b) c a

/-- Direct Atom point composition reads exactly the composite of the two reconstructed native equivalences. -/
theorem compose_eq_read (p : PointTable U) (hp : IsLawful p) (q : PointTable U) (hq : IsLawful q) :
    compose p hp q hq = read ((assemble p hp).trans (assemble q hq)) := by
  funext d a c
  cases d with
  | forward => exact (congrArg (fun r => r .forward (assemble p hp a) c) (read_assemble q hq)).symm
  | backward => exact (congrArg (fun r => r .backward a ((assemble q hq).symm c)) (read_assemble p hp)).symm

/-- Primitive Atom composition preserves exact-one forward/backward rows and their inverse point rule. -/
theorem compose_isLawful (p : PointTable U) (hp : IsLawful p) (q : PointTable U) (hq : IsLawful q) :
    IsLawful (compose p hp q hq) := by
  rw [compose_eq_read]
  exact read_isLawful _

/-- Atom assembly sends direct point composition to the original native equivalence composition. -/
theorem assemble_compose (p : PointTable U) (hp : IsLawful p) (q : PointTable U) (hq : IsLawful q) :
    assemble (compose p hp q hq) (compose_isLawful p hp q hq) = (assemble p hp).trans (assemble q hq) := by
  have he : (⟨compose p hp q hq, compose_isLawful p hp q hq⟩ : {r // IsLawful r}) =
      ⟨read ((assemble p hp).trans (assemble q hq)), read_isLawful _⟩ := Subtype.ext (compose_eq_read p hp q hq)
  exact (congrArg readingEquiv.symm he).trans (assemble_read _)

/-- One first forward image cell and one second output cell determine a forward Atom composite. -/
theorem compose_forward_support (p p' : PointTable U) (hp : IsLawful p) (hp' : IsLawful p')
    (q q' : PointTable U) (hq : IsLawful q) (hq' : IsLawful q') (a c : U.Atom)
    (h1 : p .forward a (assemble p hp a) = p' .forward a (assemble p hp a))
    (h2 : q .forward (assemble p hp a) c = q' .forward (assemble p hp a) c) :
    compose p hp q hq .forward a c = compose p' hp' q' hq' .forward a c :=
  IndependentIndexedCarrierGraph.composeIndex_point_support _ _ hp.forward hp'.forward _ _ a c h1 h2

/-- One second backward image cell and one first output cell determine a backward Atom composite. -/
theorem compose_backward_support (p p' : PointTable U) (hp : IsLawful p) (hp' : IsLawful p')
    (q q' : PointTable U) (hq : IsLawful q) (hq' : IsLawful q') (a c : U.Atom)
    (h1 : q .backward ((assemble q hq).symm c) c = q' .backward ((assemble q hq).symm c) c)
    (h2 : p .backward a ((assemble q hq).symm c) = p' .backward a ((assemble q hq).symm c)) :
    compose p hp q hq .backward a c = compose p' hp' q' hq' .backward a c :=
  IndependentIndexedCarrierGraph.composeIndex_point_support
    (fun c b => q .backward b c) (fun c b => q' .backward b c) hq.backward hq'.backward
    (fun b a => p .backward a b) (fun b a => p' .backward a b) c a h1 h2

/-- Primitive Atom identity is diagonal in the original input order of each direction. -/
def identity : PointTable U := by
  classical
  exact fun d a b => match d with
    | .forward => decide (a = b)
    | .backward => decide (b = a)

/-- Diagonal Atom rows have exactly one image in both directions and satisfy the inverse rule. -/
theorem identity_isLawful : IsLawful (identity : PointTable U) := read_isLawful (Equiv.refl U.Atom)

/-- The direct diagonal point table assembles to the native Atom identity equivalence. -/
theorem assemble_identity : assemble (identity : PointTable U) identity_isLawful = Equiv.refl U.Atom :=
  assemble_read (Equiv.refl U.Atom)

/-- Either direction of the primitive identity is true exactly when the two Atom points agree. -/
theorem identity_point_iff (d : Direction) (a b : U.Atom) : identity d a b = true ↔ a = b := by
  classical
  cases d with
  | forward => exact decide_eq_true_iff
  | backward => exact decide_eq_true_iff.trans eq_comm

end

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.Atom

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.Atom
