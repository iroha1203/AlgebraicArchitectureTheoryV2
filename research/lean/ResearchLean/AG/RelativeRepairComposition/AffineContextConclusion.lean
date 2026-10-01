import ResearchLean.AG.RelativeRepairComposition.AffineContextFamilies

/-! # The finite generated-C contextual conclusion on original actual strict repairs -/
namespace AAT.AG.RelativeRepairComposition.NativeAffine.AffineContextInput
open TransportCoherence AbelianLiftingObstruction
universe uk uG
variable {k : Type uk} [Field k] [Fintype k] [DecidableEq k] {d : Nat}
variable {W : FiniteTransportPresentation.{uG}}
variable {LW RW : ∀ {i j : W.Vertex}, W.Edge i j → Operations k (Fin d → k)}
variable {cW : W.TwoCell → (Fin d → k)} {PW : ClosedRegion W} {CW : Set (EdgeName (K := W))}
variable (I J : AffineContextInput W LW RW cW PW CW)
variable [DecidablePred (· ∈ I.fixed.edges)] [DecidablePred (· ∈ I.fixed.faces)]
variable [DecidablePred (· ∈ I.shared.edges)] [DecidablePred (· ∈ I.candidates)]
variable [DecidableEq (EdgeName (K := I.geometry))] [DecidableEq I.geometry.TwoCell]
variable [DecidablePred (· ∈ J.fixed.edges)] [DecidablePred (· ∈ J.fixed.faces)]
variable [DecidablePred (· ∈ J.shared.edges)] [DecidablePred (· ∈ J.candidates)]
variable [DecidableEq (EdgeName (K := J.geometry))] [DecidableEq J.geometry.TwoCell]
variable (ek : FiniteElimination.Enumeration k)
variable (ei : FiniteElimination.Enumeration (EdgeName (K := I.geometry)))
variable (fi : FiniteElimination.Enumeration I.geometry.TwoCell)
variable (ej : FiniteElimination.Enumeration (EdgeName (K := J.geometry)))
variable (fj : FiniteElimination.Enumeration J.geometry.TwoCell)
variable {S : Set (EdgeName (K := W))} (a : I.Range S) (b : J.Range S)
local notation "Env" => Environments (W := W) (LW := LW) (RW := RW) (cW := cW) (PW := PW) (CW := CW) S

/-- The same generated public C equality is equivalent to literal original strict repair existence
in every actual external environment, with all compatible internal candidate permissions. -/
theorem contextual_generated_strict :
    (∀ env : Env, Nonempty (StrictRepairs I env.1 a env.2) ↔
      Nonempty (StrictRepairs J env.1 b env.2)) ↔
        I.generatedShared ek ei fi a = J.generatedShared ek ej fj b := by
  rw [generated_shared_actual,generated_shared_actual]
  exact I.contextual_strict_actual a J b

/-- The same conclusion holds for every family admitting the explicit primitive pin additions. -/
theorem contextual_generated_family (family : Set Env) (hf : I.AdmitsPins S family) :
    (∀ env : family, Nonempty (StrictRepairs I env.1.1 a env.1.2) ↔
      Nonempty (StrictRepairs J env.1.1 b env.1.2)) ↔
        I.generatedShared ek ei fi a = J.generatedShared ek ej fj b := by
  rw [generated_shared_actual,generated_shared_actual]
  exact I.contextual_family_strict S J a b family hf

/-- All named shared ranges reuse the same original generators in both regions and test every
actual member of each primitive-addition-closed environment family. -/
theorem contextual_generated_family_all
    (ai : ∀ S : Set (EdgeName (K := W)), I.Range S)
    (aj : ∀ S : Set (EdgeName (K := W)), J.Range S)
    (family : ∀ S : Set (EdgeName (K := W)), Set
      (Environments (W := W) (LW := LW) (RW := RW) (cW := cW) (PW := PW) (CW := CW) S))
    (hf : ∀ S, I.AdmitsPins S (family S)) :
    (∀ S, ∀ env : family S, Nonempty (StrictRepairs I env.1.1 (ai S) env.1.2) ↔
      Nonempty (StrictRepairs J env.1.1 (aj S) env.1.2)) ↔
        ∀ S, I.generatedShared ek ei fi (ai S) = J.generatedShared ek ej fj (aj S) := by
  constructor
  · intro h S
    exact (I.contextual_generated_family J ek ei fi ej fj (ai S) (aj S) (family S) (hf S)).mp (h S)
  · intro h S
    exact (I.contextual_generated_family J ek ei fi ej fj (ai S) (aj S) (family S) (hf S)).mpr (h S)

end AAT.AG.RelativeRepairComposition.NativeAffine.AffineContextInput
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.NativeAffine.AffineContextInput
