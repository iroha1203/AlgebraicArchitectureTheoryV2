import ResearchLean.AG.RelativeRepairComposition.AffineStrictContexts

/-!
# Actual environment families admitting the finite forbidden-pin additions

Admissibility concerns membership of explicit complete primitive affine inputs
and their compatible permissions. It does not assume that a singleton boundary
relation exists. That relation is proved from the actual pin face operations.
-/
namespace AAT.AG.RelativeRepairComposition.NativeAffine.AffineContextInput
open TransportCoherence AbelianLiftingObstruction
universe uk uA uG
variable {k : Type uk} [Field k] {A : Type uA} [AddCommGroup A] [Module k A]
variable {W : FiniteTransportPresentation.{uG}}
variable {LW RW : ∀ {i j : W.Vertex}, W.Edge i j → Operations k A}
variable {cW : W.TwoCell → A} {PW : ClosedRegion W} {CW : Set (EdgeName (K := W))}
variable (I : AffineContextInput W LW RW cW PW CW) (S : Set (EdgeName (K := W)))
local notation "Env" => Environments (W := W) (LW := LW) (RW := RW) (cW := cW) (PW := PW) (CW := CW) S

/-- The explicit finite actual input formed by the original W and the forbidden parallel pins. -/
noncomputable def pinEnvironment (t : Repair W RW cW (fixedEdgesForRange PW.edges CW S)) : Env :=
  ⟨ParallelPins.contextInput W LW RW cW PW CW
    I.shared_aligned I.shared_three_law I.shared_fixed_law S t,
   ParallelPins.contextRange W LW RW cW PW CW
    I.shared_aligned I.shared_three_law I.shared_fixed_law S t⟩

/-- The primitive addition has its singleton property by evaluating its actual operations. -/
theorem pin_environment_range (t : Repair W RW cW (fixedEdgesForRange PW.edges CW S)) :
    Set.range ((I.pinEnvironment S t).1.boundary (I.pinEnvironment S t).2) =
      {realCorrection W RW cW (fixedEdgesForRange PW.edges CW S) t} :=
  ParallelPins.context_singleton_range W LW RW cW PW CW
    I.shared_aligned I.shared_three_law I.shared_fixed_law S t

/-- Admissibility of every specified primitive parallel-pin addition and its never-allowed new candidates. -/
def AdmitsPins (family : Set Env) : Prop :=
  ∀ t : Repair W RW cW (fixedEdgesForRange PW.edges CW S), I.pinEnvironment S t ∈ family

/-- The complete actual input universe admits the specified finite additions. -/
theorem all_admits_pins : I.AdmitsPins S Set.univ := fun _ => trivial

/-- A genuine shared repair makes the empty family reject the specified primitive pin addition. -/
theorem not_admits_pins_empty_of_repair
    (t : Repair W RW cW (fixedEdgesForRange PW.edges CW S)) :
    ¬ I.AdmitsPins S ∅ := fun h => h t

variable (J : AffineContextInput W LW RW cW PW CW)
variable (a : I.Range S) (b : J.Range S)

/-- Every admissible actual family detects precisely equality of full realized shared values. -/
theorem contextual_family_ranges (family : Set Env) (hf : I.AdmitsPins S family) :
    (∀ env : family, Nonempty (ContextRelations.StrictJoin (I.boundary a) (env.1.1.boundary env.1.2)) ↔
      Nonempty (ContextRelations.StrictJoin (J.boundary b) (env.1.1.boundary env.1.2))) ↔
        Set.range (I.boundary a) = Set.range (J.boundary b) := by
  apply ContextRelations.contextual_ranges (I.boundary a) (J.boundary b)
    (fun env : family => env.1.1.Repairs env.1.2)
    (fun env : family => env.1.1.boundary env.1.2)
  intro x hx
  rcases hx with ⟨s,hs⟩ | ⟨s,hs⟩
  · let t := I.sharedRepair a s
    refine ⟨⟨I.pinEnvironment S t,hf t⟩, ?_⟩
    exact (I.pin_environment_range S t).trans
      (congrArg (fun v => ({v} : Set (EdgeName (K := W) → A))) hs)
  · let t := J.sharedRepair b s
    refine ⟨⟨I.pinEnvironment S t,hf t⟩, ?_⟩
    exact (I.pin_environment_range S t).trans
      (congrArg (fun v => ({v} : Set (EdgeName (K := W) → A))) hs)

/-- Actual strict gluing in any such family has the same original contextual characterization. -/
theorem contextual_family_strict (family : Set Env) (hf : I.AdmitsPins S family) :
    (∀ env : family, Nonempty (StrictRepairs I env.1.1 a env.1.2) ↔
      Nonempty (StrictRepairs J env.1.1 b env.1.2)) ↔
        Set.range (I.boundary a) = Set.range (J.boundary b) := by
  simpa only [strict_repairs_nonempty,ContextRelations.strict_join_nonempty] using
    I.contextual_family_ranges S J a b family hf

end AAT.AG.RelativeRepairComposition.NativeAffine.AffineContextInput
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.NativeAffine.AffineContextInput
