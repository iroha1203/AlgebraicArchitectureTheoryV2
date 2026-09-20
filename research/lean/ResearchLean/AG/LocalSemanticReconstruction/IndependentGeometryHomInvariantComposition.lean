import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomInvariantPoints
import ResearchLean.AG.LocalSemanticReconstruction.IndependentInverseGraphComposition
import ResearchLean.AG.LocalSemanticReconstruction.RemainingComponentGraphCoherence
import Formal.Util.AssertStandardAxioms

/-!
# Identity, composition, and rejection for invariant presentations

Auxiliary function rows compose by primitive graph points; predicates use no
auxiliary points. Object composition is supplied in its point form with one
intermediate architecture object. These are the invariant component's closure
proofs; constructing the complete common Hom composition remains a separate
integration obligation.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.InvariantWitness

noncomputable section

universe u v

variable {U : AtomCarrier.{u}} {mode : Mode}

/-- Identity rows are diagonal value graphs for functions and inactive for predicates. -/
def identityRow : Invariant U → IndependentInverseGraph.Table.{u, u}
  | .function F => IndependentInverseGraph.read F.Value F.Value (Equiv.refl F.Value)
  | .predicate _ => fun _ => false

/-- A diagonal object graph preserves every invariant kind using primitive identity rows. -/
theorem identityRow_law (I : Invariant U)
    (h : IndependentGeometryHomPrimitive.Table.{u, v} U mode)
    (hi : ∀ A B, h (.object A B) = true → A = B) : RowLaw I I h (identityRow I) := by
  cases I with
  | function F =>
    refine ⟨IndependentInverseGraph.read_isLawful _ _ _, ?_⟩
    intro A B hAB
    have he := hi A B hAB
    subst B
    exact (IndependentCarrierGraph.read_edge _ _ (Equiv.refl F.Value) _ _).2 rfl
  | predicate P =>
    intro A B hAB
    rw [hi A B hAB]

/-- Compose auxiliary rows without constructing or receiving a native Hom. -/
def composeRow (S M T : Invariant U)
    (h k : IndependentGeometryHomPrimitive.Table.{u, v} U mode)
    (w z : IndependentInverseGraph.Table.{u, u})
    (hw : RowLaw S M h w) (hz : RowLaw M T k z) : IndependentInverseGraph.Table.{u, u} := by
  cases S with
  | function F =>
    cases M with
    | function G =>
      cases T with
      | function H => exact IndependentInverseGraph.compose F.Value G.Value H.Value w hw.1 z hz.1
      | predicate _ => exact False.elim hz
    | predicate _ => exact False.elim hw
  | predicate P =>
    cases M with
    | function _ => exact False.elim hw
    | predicate Q =>
      cases T with
      | function _ => exact False.elim hz
      | predicate _ => exact fun _ => false

/-- A composite object edge's single intermediate point proves invariant preservation under composition. -/
theorem composeRow_law (S M T : Invariant U)
    (h k l : IndependentGeometryHomPrimitive.Table.{u, v} U mode)
    (w z : IndependentInverseGraph.Table.{u, u})
    (hw : RowLaw S M h w) (hz : RowLaw M T k z)
    (hl : ∀ A C, l (.object A C) = true → ∃ B, h (.object A B) = true ∧ k (.object B C) = true) :
    RowLaw S T l (composeRow S M T h k w z hw hz) := by
  cases S with
  | function F =>
    cases M with
    | function G =>
      cases T with
      | function H =>
        refine ⟨IndependentInverseGraph.compose_isLawful _ _ _ _ hw.1 _ hz.1, ?_⟩
        intro A C hAC
        obtain ⟨B, hAB, hBC⟩ := hl A C hAC
        change IndependentCarrierGraph.compose F.Value G.Value H.Value
          (IndependentInverseGraph.forward w) hw.1.forward (IndependentInverseGraph.forward z)
            (.edge F.Value H.Value (F.evaluate A) (H.evaluate C)) = true
        rw [IndependentCarrierGraph.compose_edge]
        have he := IndependentCarrierGraph.assemble_eq_of_edge _ _
          (IndependentInverseGraph.forward w) hw.1.forward (hw.2 A B hAB)
        rw [he]
        exact hz.2 B C hBC
      | predicate _ => exact False.elim hz
    | predicate _ => exact False.elim hw
  | predicate P =>
    cases M with
    | function _ => exact False.elim hw
    | predicate Q =>
      cases T with
      | function _ => exact False.elim hz
      | predicate R =>
        intro A C hAC
        obtain ⟨B, hAB, hBC⟩ := hl A C hAC
        exact (hw A B hAB).trans (hz B C hBC)

/-- A function/predicate mismatch is rejected at its active invariant index point. -/
theorem mixed_kind_rejected {I J : InvariantFamily U}
    (p : Presentation.{u, v} I J mode) (i : I.Index) (j : J.Index)
    (hij : p.retained.table (.invariant (.edge I.Index J.Index i j)) = true)
    (F : FunctionInvariant U) (P : PredicateInvariant U)
    (hs : I.invariant i = .function F) (ht : J.invariant j = .predicate P) : False := by
  have h := p.rows i j hij
  rw [hs, ht] at h
  exact h

/-- A predicate/function mismatch is rejected in the opposite direction too. -/
theorem reverse_mixed_kind_rejected {I J : InvariantFamily U}
    (p : Presentation.{u, v} I J mode) (i : I.Index) (j : J.Index)
    (hij : p.retained.table (.invariant (.edge I.Index J.Index i j)) = true)
    (P : PredicateInvariant U) (F : FunctionInvariant U)
    (hs : I.invariant i = .predicate P) (ht : J.invariant j = .function F) : False := by
  have h := p.rows i j hij
  rw [hs, ht] at h
  exact h

/-- A counterexample to the original transport excludes every coherent presentation with these data. -/
theorem native_failure_rejected {I J : InvariantFamily U}
    (p : Presentation.{u, v} I J mode) (i : I.Index)
    (hf : ¬ Invariant.TransportedAlong (I.invariant i)
      (J.invariant (p.retained.indexMap i)) id p.retained.objectMap) : False :=
  hf ((assemblePresentation I J p).property i)

/-- The successor counterexample is rejected by coherent point rows, even though every finite prefix extends. -/
theorem successor_row_rejected {V : AtomCarrier.{0}}
    (f : ArchitectureObject V → ℕ) (hf : Function.Surjective f)
    (h : IndependentGeometryHomPrimitive.Table.{0, v} V mode)
    (hi : ∀ A, h (.object A A) = true) (w : IndependentInverseGraph.Table.{0, 0}) :
    ¬ RowLaw (.function ⟨ℕ, f⟩) (.function ⟨ℕ, fun A => f A + 1⟩) h w := by
  intro hw
  let e := IndependentInverseGraph.assemble ℕ ℕ w hw.1
  obtain ⟨n, hn⟩ := e.surjective 0
  obtain ⟨A, hA⟩ := hf n
  have hx := IndependentCarrierGraph.assemble_eq_of_edge ℕ ℕ
    (IndependentInverseGraph.forward w) hw.1.forward (hw.2 A A (hi A))
  change e (f A) = f A + 1 at hx
  rw [hA, hn] at hx
  omega

/-- The quotient supplies the existing package assembler's invariant-transport field. -/
theorem package_transport (P Q : AATCorePackage U)
    (p : Local.{u, v} P.reading.invariantReading Q.reading.invariantReading mode) :
    RemainingComponentGraphCoherence.IsInvariantTransport P Q
      (retained _ _ p).objectMap (retained _ _ p).indexMap := by
  induction p using Quotient.inductionOn with
  | _ p => exact (assemblePresentation _ _ p).property

end

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.InvariantWitness

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.InvariantWitness
