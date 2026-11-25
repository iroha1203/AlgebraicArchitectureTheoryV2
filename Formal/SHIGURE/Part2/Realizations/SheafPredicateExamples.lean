import Formal.SHIGURE.Part2.Realizations.ZariskiConstants

/-!
# A covering test for a predicate sheaf

The empty scheme has an empty covering. The empty subpresheaf omits its
required section. Taking local membership supplies that section.
-/

open AlgebraicGeometry CategoryTheory Opposite

universe u

noncomputable section

namespace SHIGURE.Copying

private def emptyTest (S : Scheme.{u}) : Over S :=
  Over.mk (Scheme.emptyTo S)

private theorem emptyTest_cover (S : Scheme.{u}) :
    (⊥ : Sieve (emptyTest S)) ∈ (Scheme.zariskiTopology.over S) (emptyTest S) := by
  have h : Sieve.overEquiv (emptyTest S) ⊥ = ⊥ := by
    ext U f
    constructor
    · rintro ⟨_, _, _, hf, _⟩
      exact hf.elim
    · intro hf
      exact hf.elim
  rw [GrothendieckTopology.mem_over_iff, h]
  exact Scheme.bot_mem_grothendieckTopology (∅ : Scheme.{u})

private def singletonSection (S : Scheme.{u}) : (constantCarrier S PUnit).val.obj (op (emptyTest S)) :=
  LocallyConstant.const _ PUnit.unit

private theorem emptySubfunctor_sieve (S : Scheme.{u}) :
    (⊥ : Subfunctor (constantCarrier S PUnit).val).sieveOfSection (singletonSection S) = ⊥ := by
  ext Y f
  rfl

/-- The empty subpresheaf fails the sheaf condition on the empty covering. -/
theorem emptySubfunctor_notSheaf (S : Scheme.{u}) :
    ¬ Presieve.IsSheaf (Scheme.zariskiTopology.over S)
      (⊥ : Subfunctor (constantCarrier S PUnit).val).toFunctor := by
  intro h
  have hs := (isSheaf_iff_isSheaf_of_type _ _).mp (constantCarrier S PUnit).cond
  have hm := (Subfunctor.isSheaf_iff _ hs).mp h (op (emptyTest S)) (singletonSection S) (by
    rw [emptySubfunctor_sieve]
    exact emptyTest_cover S)
  exact hm

/-- The same section belongs to the predicate obtained by local membership. -/
theorem emptySubfunctor_localSection (S : Scheme.{u}) :
    singletonSection S ∈ (SheafPredicate.ofLocal (F := constantCarrier S PUnit) ⊥).carrier.obj (op (emptyTest S)) := by
  rw [SheafPredicate.mem_ofLocal_iff, emptySubfunctor_sieve]
  exact emptyTest_cover S

end SHIGURE.Copying
