import ResearchLean.AG.RelativeRepairComposition.AffinePinContextInput
import ResearchLean.AG.RelativeRepairComposition.AffineSharedLaws

/-!
# Every actual affine external context detects exactly the realized shared relation

The external quantifier contains every primitive finite affine input and every
compatible whole candidate range. Parallel pins supply witnesses for the
converse; their complete primitive laws are derived from the original input.
-/
namespace AAT.AG.RelativeRepairComposition.NativeAffine.AffineContextInput
open TransportCoherence AbelianLiftingObstruction
universe uk uA uG
variable {k : Type uk} [Field k] {A : Type uA} [AddCommGroup A] [Module k A]
variable {W : FiniteTransportPresentation.{uG}}
variable {LW RW : ∀ {i j : W.Vertex}, W.Edge i j → Operations k A}
variable {cW : W.TwoCell → A} {PW : ClosedRegion W} {CW : Set (EdgeName (K := W))}
variable (I J : AffineContextInput W LW RW cW PW CW)

/-- All original actual finite external inputs with all compatible whole permissions. -/
abbrev Environments (S : Set (EdgeName (K := W))) :=
  Σ E : AffineContextInput W LW RW cW PW CW, E.Range S

include I in
/-- An actual singleton context is generated for each genuine shared repair. -/
theorem actual_singleton_context {S : Set (EdgeName (K := W))}
    (t : Repair W RW cW (fixedEdgesForRange PW.edges CW S)) :
    ∃ env : Environments (W := W) (LW := LW) (RW := RW) (cW := cW) (PW := PW) (CW := CW) S,
      Set.range (env.1.boundary env.2) =
        {realCorrection W RW cW (fixedEdgesForRange PW.edges CW S) t} := by
  let E := ParallelPins.contextInput W LW RW cW PW CW
    I.shared_aligned I.shared_three_law I.shared_fixed_law S t
  let a := ParallelPins.contextRange W LW RW cW PW CW
    I.shared_aligned I.shared_three_law I.shared_fixed_law S t
  exact ⟨⟨E,a⟩, ParallelPins.context_singleton_range W LW RW cW PW CW
    I.shared_aligned I.shared_three_law I.shared_fixed_law S t⟩

/-- Whole independent repairs in every actual external environment distinguish precisely
the equality of the full actual shared correction ranges. -/
theorem contextual_actual_ranges {S : Set (EdgeName (K := W))}
    (a : I.Range S) (b : J.Range S) :
    (∀ env : Environments (W := W) (LW := LW) (RW := RW) (cW := cW) (PW := PW) (CW := CW) S,
      Nonempty (ContextRelations.StrictJoin (I.boundary a) (env.1.boundary env.2)) ↔
        Nonempty (ContextRelations.StrictJoin (J.boundary b) (env.1.boundary env.2))) ↔
      Set.range (I.boundary a) = Set.range (J.boundary b) := by
  apply ContextRelations.contextual_ranges (I.boundary a) (J.boundary b)
    (fun env : Environments (W := W) (LW := LW) (RW := RW) (cW := cW) (PW := PW) (CW := CW) S =>
      env.1.Repairs env.2)
    (fun env : Environments (W := W) (LW := LW) (RW := RW) (cW := cW) (PW := PW) (CW := CW) S =>
      env.1.boundary env.2)
  intro x hx
  rcases hx with ⟨s,hs⟩ | ⟨s,hs⟩
  · obtain ⟨env,he⟩ := I.actual_singleton_context (I.sharedRepair a s)
    exact ⟨env,he.trans (congrArg (fun v => ({v} : Set (EdgeName (K := W) → A))) hs)⟩
  · obtain ⟨env,he⟩ := I.actual_singleton_context (J.sharedRepair b s)
    exact ⟨env,he.trans (congrArg (fun v => ({v} : Set (EdgeName (K := W) → A))) hs)⟩

/-- The contextual characterization holds simultaneously for every named shared range. -/
theorem contextual_all_ranges
    (a : ∀ S : Set (EdgeName (K := W)), I.Range S)
    (b : ∀ S : Set (EdgeName (K := W)), J.Range S) :
    (∀ S, ∀ env : Environments (W := W) (LW := LW) (RW := RW) (cW := cW) (PW := PW) (CW := CW) S,
      Nonempty (ContextRelations.StrictJoin (I.boundary (a S)) (env.1.boundary env.2)) ↔
        Nonempty (ContextRelations.StrictJoin (J.boundary (b S)) (env.1.boundary env.2))) ↔
      ∀ S, Set.range (I.boundary (a S)) = Set.range (J.boundary (b S)) := by
  constructor
  · intro h S
    exact (I.contextual_actual_ranges J (a S) (b S)).mp (h S)
  · intro h S
    exact (I.contextual_actual_ranges J (a S) (b S)).mpr (h S)

end AAT.AG.RelativeRepairComposition.NativeAffine.AffineContextInput
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.NativeAffine.AffineContextInput
