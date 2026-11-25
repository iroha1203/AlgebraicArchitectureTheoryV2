import Formal.SHIGURE.Part2.Realizations.SectionStructures

/-!
# Structure maps and positive formulas on the relative site

Preservation of an atom is the existing Part I preservation theorem
on sections. An existential witness or a disjunct is carried along the
same covering sieve.
-/

open CategoryTheory Opposite

universe u v w

namespace SHIGURE.SheafStructure

variable {C : Type v} [Category.{w} C] {J : GrothendieckTopology C}
variable {sig : Signature.{u}} {Γ : List sig.SortType}
variable {A B : SheafStructure sig J}

/-- On sections an atomic formula is the corresponding fact in the Part I structure. -/
theorem mem_interpretAtom_iff_sections (A : SheafStructure sig J) (p : Atomic sig Γ)
    (U : Cᵒᵖ) (a : (sheafTuple A.carrier Γ).val.obj U) :
    a ∈ (A.interpretAtom p).carrier.obj U ↔ p.Holds (A.sections U) a := by
  cases p with
  | eq _ _ => rfl
  | rel _ _ => rfl
  | domain _ _ => rfl
  | graph op xs y =>
    cases op with
    | total f =>
      rw [interpretAtom, SheafPredicate.mem_equal_iff, Atomic.holds_graph, Structure.graph_total_iff]
      rfl
    | quantity q =>
      rw [interpretAtom, SheafPredicate.mem_equal_iff, Atomic.holds_graph, Structure.graph_quantity_iff]
      rfl
    | partialOp p =>
      rw [interpretAtom, Atomic.holds_graph, Structure.graph_partial_iff]
      exact A.mem_partialGraph_iff p xs y U a

/-- Each positive formula is preserved by a structure-preserving sheaf morphism. -/
theorem Hom.preservesFormula (h : Hom A B) (p : Formula sig Γ) (U : Cᵒᵖ)
    (a : (sheafTuple A.carrier Γ).val.obj U)
    (ha : a ∈ (A.interpretFormula p).carrier.obj U) :
    (sheafTupleMap h.onSort Γ).val.app U a ∈ (B.interpretFormula p).carrier.obj U := by
  induction p generalizing U with
  | atom p =>
    apply (mem_interpretAtom_iff_sections B p U _).mpr
    exact (h.sections U).atomic_holds_map p a ((mem_interpretAtom_iff_sections A p U a).mp ha)
  | truth => exact SheafPredicate.mem_truth _ _
  | falsehood =>
    simp only [interpretFormula, SheafPredicate.falsehood, SheafPredicate.mem_ofLocal_iff] at ha ⊢
    exact J.superset_covering (fun _ _ hg => hg) ha
  | conj p q hp hq =>
    exact ⟨hp U a ha.1, hq U a ha.2⟩
  | disj p q hp hq =>
    simp only [interpretFormula, SheafPredicate.mem_disj_iff] at ha ⊢
    refine J.superset_covering ?_ ha
    intro V g hg
    let b := (sheafTuple A.carrier _).val.map g.op a
    have hn := FunctorToTypes.naturality _ _ (sheafTupleMap h.onSort _).val g.op a
    change b ∈ (A.interpretFormula p).carrier.obj (op V) ∨
      b ∈ (A.interpretFormula q).carrier.obj (op V) at hg
    change (sheafTuple B.carrier _).val.map g.op ((sheafTupleMap h.onSort _).val.app U a) ∈
       (B.interpretFormula p).carrier.obj (op V) ∨
      (sheafTuple B.carrier _).val.map g.op ((sheafTupleMap h.onSort _).val.app U a) ∈
       (B.interpretFormula q).carrier.obj (op V)
    rw [← hn]
    exact hg.elim (fun hb => Or.inl (hp (op V) b hb)) (fun hb => Or.inr (hq (op V) b hb))
  | @ex Γ s p ih =>
    simp only [interpretFormula, SheafPredicate.mem_existsAlong_iff] at ha ⊢
    refine J.superset_covering ?_ ha
    intro V g hg
    obtain ⟨⟨b, hb⟩, he⟩ := hg
    let source := sheafTupleRename A.carrier (Γ := Γ) (Δ := s :: Γ) (fun i => .there i)
    let target := sheafTupleRename B.carrier (Γ := Γ) (Δ := s :: Γ) (fun i => .there i)
    let prev := sheafTupleMap h.onSort Γ
    let next := sheafTupleMap h.onSort (s :: Γ)
    change source.val.app (op V) b = (sheafTuple A.carrier Γ).val.map g.op a at he
    refine ⟨⟨next.val.app (op V) b, ih (op V) b hb⟩, ?_⟩
    have hn := FunctorToTypes.naturality _ _ prev.val g.op a
    change target.val.app (op V) (next.val.app (op V) b) =
      (sheafTuple B.carrier Γ).val.map g.op (prev.val.app U a)
    rw [← hn, ← he]
    rfl

/-- Isomorphic interpreted structures satisfy exactly the same written Laws. -/
theorem holdsLaw_of_iso (e : A ≅ B) (l : Law sig) (h : A.holdsLaw l) : B.holdsLaw l := by
  intro U a ha
  let b := (sheafTupleMap e.inv.onSort l.context).val.app U a
  have hb := e.inv.preservesFormula l.input U a ha
  have hdone := e.hom.preservesFormula l.conclusion U b (h U hb)
  have hcomp : (fun s => e.inv.onSort s ≫ e.hom.onSort s) = fun s => 𝟙 (B.carrier s) := by
    exact congrArg Hom.onSort e.inv_hom_id
  have ht : (sheafTupleMap e.hom.onSort l.context).val.app U b = a := by
    change ((sheafTupleMap e.inv.onSort l.context ≫ sheafTupleMap e.hom.onSort l.context).val.app U) a = a
    rw [← sheafTupleMap_comp, hcomp, sheafTupleMap_id]
    rfl
  exact ht ▸ hdone

end SHIGURE.SheafStructure
