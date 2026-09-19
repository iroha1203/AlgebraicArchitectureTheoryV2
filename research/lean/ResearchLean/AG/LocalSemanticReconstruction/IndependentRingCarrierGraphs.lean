import ResearchLean.AG.LocalSemanticReconstruction.IndependentInverseGraphReadings
import ResearchLean.AG.LocalSemanticReconstruction.IndependentRingPrimitiveReadings
import Mathlib.Algebra.Ring.Equiv
import Formal.Util.AssertStandardAxioms

/-!
# Ring homs and ring equivalences from candidate point graphs

The point-graph query precedes the chosen ring carriers. The four preservation
rules use only zero/one/add/mul point evaluations and true point pairs.
Directed coefficient maps and invertible observable maps have separate native
read/assembly equivalences, with no invertibility imposed on the former.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentRingCarrierGraph

noncomputable section

universe u v

variable {K : Type u} {L : Type v}

/-- Primitive preservation clauses at true candidate carrier graph pairs. -/
structure Preserves (s : IndependentRingPrimitive.Table K) (t : IndependentRingPrimitive.Table L)
    (g : IndependentCarrierGraph.Table.{u, v}) : Prop where
  /-- The primitive zero pair is true. -/
  zero : g (.edge K L (s .zero) (t .zero)) = true
  /-- The primitive one pair is true. -/
  one : g (.edge K L (s .one) (t .one)) = true
  /-- Addition at two true input/output pairs gives a true result pair. -/
  add : ∀ a b c d, g (.edge K L a c) = true → g (.edge K L b d) = true →
    g (.edge K L (s (.add a b)) (t (.add c d))) = true
  /-- Multiplication at the same primitive pairs gives a true result pair. -/
  mul : ∀ a b c d, g (.edge K L a c) = true → g (.edge K L b d) = true →
    g (.edge K L (s (.mul a b)) (t (.mul c d))) = true

variable (s : IndependentRingPrimitive.Table K) (t : IndependentRingPrimitive.Table L)

/-- Exact-one carrier graph rows turn the four primitive clauses into ordinary point-function ring laws. -/
theorem function_laws (hs : IndependentRingPrimitive.IsLawful s) (ht : IndependentRingPrimitive.IsLawful t)
    (g : IndependentCarrierGraph.Table.{u, v}) (hg : IndependentCarrierGraph.IsLawful K L g)
    (hl : Preserves s t g) :
    letI := IndependentRingPrimitive.assemble s hs
    letI := IndependentRingPrimitive.assemble t ht
    IndependentRingPrimitive.Hom.IsLawful (IndependentCarrierGraph.assemble K L g hg) := by
  letI := IndependentRingPrimitive.assemble s hs
  letI := IndependentRingPrimitive.assemble t ht
  constructor
  · exact IndependentCarrierGraph.assemble_eq_of_edge K L g hg hl.zero
  · exact IndependentCarrierGraph.assemble_eq_of_edge K L g hg hl.one
  · intro a b
    exact IndependentCarrierGraph.assemble_eq_of_edge K L g hg
      (hl.add a b _ _ (IndependentCarrierGraph.edge_assemble K L g hg a)
        (IndependentCarrierGraph.edge_assemble K L g hg b))
  · intro a b
    exact IndependentCarrierGraph.assemble_eq_of_edge K L g hg
      (hl.mul a b _ _ (IndependentCarrierGraph.edge_assemble K L g hg a)
        (IndependentCarrierGraph.edge_assemble K L g hg b))

/-- Native ring structures are used only after the candidate query and point laws have been declared. -/
abbrev IsLawful (K : Type u) (L : Type v) [CommRing K] [CommRing L] (g : IndependentCarrierGraph.Table.{u, v}) : Prop :=
  IndependentCarrierGraph.IsLawful K L g ∧
    Preserves (IndependentRingPrimitive.read (inferInstance : CommRing K))
      (IndependentRingPrimitive.read (inferInstance : CommRing L)) g

variable [CommRing K] [CommRing L]

/-- Read every native directed ring hom as candidate point pairs. -/
def read (f : K →+* L) : IndependentCarrierGraph.Table.{u, v} := IndependentCarrierGraph.read K L f

/-- Every native ring hom satisfies exactly the four primitive graph-preservation clauses. -/
theorem read_isLawful (f : K →+* L) : IsLawful K L (read f) := by
  refine ⟨IndependentCarrierGraph.read_isLawful K L f, ?_⟩
  constructor
  · exact (IndependentCarrierGraph.read_edge K L f _ _).2 f.map_zero
  · exact (IndependentCarrierGraph.read_edge K L f _ _).2 f.map_one
  · intro a b c d hac hbd
    have hc := (IndependentCarrierGraph.read_edge K L f a c).1 hac
    have hd := (IndependentCarrierGraph.read_edge K L f b d).1 hbd
    apply (IndependentCarrierGraph.read_edge K L f _ _).2
    exact (f.map_add a b).trans (congrArg₂ (fun x y : L => x + y) hc hd)
  · intro a b c d hac hbd
    have hc := (IndependentCarrierGraph.read_edge K L f a c).1 hac
    have hd := (IndependentCarrierGraph.read_edge K L f b d).1 hbd
    apply (IndependentCarrierGraph.read_edge K L f _ _).2
    exact (f.map_mul a b).trans (congrArg₂ (fun x y : L => x * y) hc hd)

/-- Construct the directed native ring hom from total point rows and primitive preservation. -/
def assemble (g : IndependentCarrierGraph.Table.{u, v}) (h : IsLawful K L g) : K →+* L where
  toFun := IndependentCarrierGraph.assemble K L g h.1
  map_zero' := IndependentCarrierGraph.assemble_eq_of_edge K L g h.1 h.2.zero
  map_one' := IndependentCarrierGraph.assemble_eq_of_edge K L g h.1 h.2.one
  map_add' a b := IndependentCarrierGraph.assemble_eq_of_edge K L g h.1
    (h.2.add a b _ _ (IndependentCarrierGraph.edge_assemble K L g h.1 a)
      (IndependentCarrierGraph.edge_assemble K L g h.1 b))
  map_mul' a b := IndependentCarrierGraph.assemble_eq_of_edge K L g h.1
    (h.2.mul a b _ _ (IndependentCarrierGraph.edge_assemble K L g h.1 a)
      (IndependentCarrierGraph.edge_assemble K L g h.1 b))

/-- Full native directed ring maps are recovered from their point graphs. -/
theorem assemble_read (f : K →+* L) : assemble (read f) (read_isLawful f) = f := by
  apply RingHom.ext
  intro x
  exact congrFun (IndependentCarrierGraph.assemble_read K L f) x

/-- Every candidate ring-map graph cell survives assembly and re-reading. -/
theorem read_assemble (g : IndependentCarrierGraph.Table.{u, v}) (h : IsLawful K L g) :
    read (assemble g h) = g := IndependentCarrierGraph.read_assemble K L g h.1

/-- All directed ring homs, including noninjective maps, have exact primitive presentations. -/
def readingEquiv : (K →+* L) ≃ {g : IndependentCarrierGraph.Table.{u, v} // IsLawful K L g} where
  toFun f := ⟨read f, read_isLawful f⟩
  invFun g := assemble g.val g.property
  left_inv := assemble_read
  right_inv g := Subtype.ext (read_assemble g.val g.property)

/-- A native ring equivalence requires two inverse point graphs in addition to forward preservation. -/
abbrev EquivLawful (K : Type u) (L : Type v) [CommRing K] [CommRing L] (g : IndependentInverseGraph.Table.{u, v}) : Prop :=
  IndependentInverseGraph.IsLawful K L g ∧
    Preserves (IndependentRingPrimitive.read (inferInstance : CommRing K))
      (IndependentRingPrimitive.read (inferInstance : CommRing L)) (IndependentInverseGraph.forward g)

/-- Read an invertible observable ring map through its two directed candidate graphs. -/
def readEquiv (e : K ≃+* L) : IndependentInverseGraph.Table.{u, v} :=
  IndependentInverseGraph.read K L e.toEquiv

/-- Native ring equivalences supply the inverse point rules and all preservation instances. -/
theorem readEquiv_isLawful (e : K ≃+* L) : EquivLawful K L (readEquiv e) :=
  ⟨IndependentInverseGraph.read_isLawful K L e.toEquiv, (read_isLawful e.toRingHom).2⟩

/-- Assemble the complete native ring equivalence without storing one in a local field. -/
def assembleEquiv (g : IndependentInverseGraph.Table.{u, v}) (h : EquivLawful K L g) : K ≃+* L where
  toEquiv := IndependentInverseGraph.assemble K L g h.1
  map_add' a b := (assemble (IndependentInverseGraph.forward g) ⟨h.1.forward, h.2⟩).map_add a b
  map_mul' a b := (assemble (IndependentInverseGraph.forward g) ⟨h.1.forward, h.2⟩).map_mul a b

/-- Native observable ring equivalences are restored on all computational data. -/
theorem assembleEquiv_readEquiv (e : K ≃+* L) :
    assembleEquiv (readEquiv e) (readEquiv_isLawful e) = e := by
  apply RingEquiv.ext
  intro x
  exact congrArg (fun f : K ≃ L => f x) (IndependentInverseGraph.assemble_read K L e.toEquiv)

/-- Both inverse candidate graphs survive native ring-equivalence assembly. -/
theorem readEquiv_assembleEquiv (g : IndependentInverseGraph.Table.{u, v}) (h : EquivLawful K L g) :
    readEquiv (assembleEquiv g h) = g := IndependentInverseGraph.read_assemble K L g h.1

/-- Full native ring equivalences and primitive inverse point graphs have exact inverse presentations. -/
def equivReadingEquiv : (K ≃+* L) ≃ {g : IndependentInverseGraph.Table.{u, v} // EquivLawful K L g} where
  toFun e := ⟨readEquiv e, readEquiv_isLawful e⟩
  invFun g := assembleEquiv g.val g.property
  left_inv := assembleEquiv_readEquiv
  right_inv g := Subtype.ext (readEquiv_assembleEquiv g.val g.property)

end

end AAT.AG.LocalSemanticReconstruction.IndependentRingCarrierGraph

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentRingCarrierGraph
