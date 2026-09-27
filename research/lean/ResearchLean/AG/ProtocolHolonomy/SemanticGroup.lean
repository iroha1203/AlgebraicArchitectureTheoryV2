import ResearchLean.AG.ProtocolHolonomy.SemanticComposition
import Formal.Util.AssertStandardAxioms

/-!
# The semantic presentation of the original change group

Each visible change is paired with an actual isomorphism of independently
constructed quotient-execution realizations. The semantic presentation reads
the original A1/A2 change group and its visible projection.
-/

namespace AAT.AG.ProtocolHolonomy

open AAT.AG.RealizationReconstruction CategoryTheory

universe u v w

namespace FiniteProtocolInput

variable {Q : FixedFDirectedMultigraph.{u, v}}
  (P : FiniteProtocolInput.{u, v, w} Q)

/-- Original H elements paired with full semantic natural isomorphisms. -/
def SemanticIsoPair :=
  Σ g : P.H, P.realization ≅ P.renamedRealization g.1 g.2

/-- The complete semantic pairs correspond to the original A1 lift pairs,
retaining the visible automorphism and each vertexwise equivalence. -/
def liftPairEquivSemanticPair :
    P.data.LiftPair P.H ≃ P.SemanticIsoPair where
  toFun p := ⟨p.1, P.liftIso p.1.1 p.1.2 p.2⟩
  invFun p := ⟨p.1, P.isoToLift p.1.1 p.1.2 p.2⟩
  left_inv p := by
    rcases p with ⟨g, a⟩
    change (⟨g, P.isoToLift g.1 g.2 (P.liftIso g.1 g.2 a)⟩ :
      P.data.LiftPair P.H) = ⟨g, a⟩
    rw [P.isoToLift_liftIso]
  right_inv p := by
    rcases p with ⟨g, i⟩
    change (⟨g, P.liftIso g.1 g.2 (P.isoToLift g.1 g.2 i)⟩ :
      P.SemanticIsoPair) = ⟨g, i⟩
    rw [P.liftIso_isoToLift]

/-- Semantic pairs carry the original A2 multiplication through the proved
bidirectional correspondence. -/
noncomputable instance : Group P.SemanticIsoPair :=
  P.liftPairEquivSemanticPair.symm.group

/-- The original A2 pair group and the full semantic isomorphism pairs are
group-isomorphic. -/
noncomputable def liftPairMulEquivSemanticPair :
    P.data.LiftPair P.H ≃* P.SemanticIsoPair where
  toEquiv := P.liftPairEquivSemanticPair
  map_mul' a b := by
    let E := P.liftPairEquivSemanticPair
    change E (a * b) = E (E.symm (E a) * E.symm (E b))
    simp

/-- Semantic multiplication on every pair coming from original A1 lifts
has precisely the reindexed quotient-execution composite as its hom. -/
theorem semanticPair_mul_toNatTrans
    (a b : P.data.LiftPair P.H) :
    ((P.liftPairMulEquivSemanticPair (a * b)).2).hom.toNatTrans =
      P.liftIsoSemanticComposite a.1.1 b.1.1 a.1.2 b.1.2 a.2 b.2 := by
  change (P.liftIso (a * b).1.1 (a * b).1.2 (a * b).2).hom.toNatTrans = _
  exact (P.liftIsoSemanticComposite_eq a.1.1 b.1.1 a.1.2 b.1.2 a.2 b.2).symm

/-- For arbitrary semantic isomorphism pairs, their group product is the
image of the original A2 product, and its hom is the genuine reindexed
natural-isomorphism composite. The inverse equivalence supplies the unique
original A1 lifts of the two semantic isomorphisms. -/
theorem semanticPair_mul_composite (p q : P.SemanticIsoPair) :
    p * q = P.liftPairMulEquivSemanticPair
        (P.liftPairMulEquivSemanticPair.symm p *
          P.liftPairMulEquivSemanticPair.symm q) ∧
      ((P.liftPairMulEquivSemanticPair
        (P.liftPairMulEquivSemanticPair.symm p *
          P.liftPairMulEquivSemanticPair.symm q)).2).hom.toNatTrans =
        P.liftIsoSemanticComposite
          (P.liftPairMulEquivSemanticPair.symm p).1.1
          (P.liftPairMulEquivSemanticPair.symm q).1.1
          (P.liftPairMulEquivSemanticPair.symm p).1.2
          (P.liftPairMulEquivSemanticPair.symm q).1.2
          (P.liftPairMulEquivSemanticPair.symm p).2
          (P.liftPairMulEquivSemanticPair.symm q).2 := by
  constructor
  · calc
      p * q = P.liftPairMulEquivSemanticPair
          (P.liftPairMulEquivSemanticPair.symm p) *
          P.liftPairMulEquivSemanticPair
          (P.liftPairMulEquivSemanticPair.symm q) := by simp
      _ = _ := (P.liftPairMulEquivSemanticPair.map_mul
        (P.liftPairMulEquivSemanticPair.symm p)
        (P.liftPairMulEquivSemanticPair.symm q)).symm
  · exact P.semanticPair_mul_toNatTrans
      (P.liftPairMulEquivSemanticPair.symm p)
      (P.liftPairMulEquivSemanticPair.symm q)

/-- The semantic presentation projects to the same original visible H. -/
noncomputable def semanticPairProjection : P.SemanticIsoPair →* P.H :=
  (P.data.liftPairProjection P.H).comp
    P.liftPairMulEquivSemanticPair.symm.toMonoidHom

@[simp] theorem semanticPairProjection_apply (p : P.SemanticIsoPair) :
    P.semanticPairProjection p = p.1 := by
  rcases p with ⟨g, i⟩
  change P.data.liftPairProjection P.H
    ⟨g, P.isoToLift g.1 g.2 i⟩ = g
  exact P.data.liftPairProjection_apply _

/-- The literal semantic projection kernel consists exactly of pairs whose
original visible component is identity. -/
theorem semanticPair_mem_ker_iff (p : P.SemanticIsoPair) :
    p ∈ P.semanticPairProjection.ker ↔ p.1 = 1 := by
  simp [MonoidHom.mem_ker]

/-- Under the semantic correspondence, kernel membership is exactly the
original pair projection kernel, with no replacement vertical group. -/
theorem liftPairEquivSemanticPair_mem_ker_iff
    (p : P.data.LiftPair P.H) :
    P.liftPairMulEquivSemanticPair p ∈ P.semanticPairProjection.ker ↔
      p ∈ (P.data.liftPairProjection P.H).ker := by
  simp [MonoidHom.mem_ker]
  rfl

end FiniteProtocolInput
end AAT.AG.ProtocolHolonomy

#print axioms AAT.AG.ProtocolHolonomy.FiniteProtocolInput.liftPairEquivSemanticPair
#print axioms AAT.AG.ProtocolHolonomy.FiniteProtocolInput.liftPairMulEquivSemanticPair
#print axioms AAT.AG.ProtocolHolonomy.FiniteProtocolInput.semanticPair_mul_toNatTrans
#print axioms AAT.AG.ProtocolHolonomy.FiniteProtocolInput.semanticPair_mul_composite
#print axioms AAT.AG.ProtocolHolonomy.FiniteProtocolInput.semanticPairProjection
#print axioms AAT.AG.ProtocolHolonomy.FiniteProtocolInput.semanticPairProjection_apply
#print axioms AAT.AG.ProtocolHolonomy.FiniteProtocolInput.semanticPair_mem_ker_iff
#print axioms AAT.AG.ProtocolHolonomy.FiniteProtocolInput.liftPairEquivSemanticPair_mem_ker_iff
#assert_standard_axioms_only AAT.AG.ProtocolHolonomy
