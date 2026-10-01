import ResearchLean.AG.RelativeRepairComposition.AffineContextInput
import ResearchLean.AG.RelativeRepairComposition.ParallelPinEmbedding
import ResearchLean.AG.RelativeRepairComposition.AffinePinCandidates
import ResearchLean.AG.RelativeRepairComposition.AffineTranslationWords

/-!
# The actual parallel-pin test is a lawful compatible external input

All geometry and affine operations are generated before reading a boundary
relation. Original fixed cells and candidate names match the shared input;
pins are new candidates and are never allowed by the constructed range.
-/
namespace AAT.AG.RelativeRepairComposition.NativeAffine.ParallelPins
open TransportCoherence AbelianLiftingObstruction
universe uk uA uG
variable {k : Type uk} [Field k] {A : Type uA} [AddCommGroup A] [Module k A]
variable (W : FiniteTransportPresentation.{uG})
variable (LW RW : ∀ {i j : W.Vertex}, W.Edge i j → Operations k A)
variable (cW : W.TwoCell → A) (PW : ClosedRegion W) (CW : Set (EdgeName (K := W)))
variable (hf : ∀ f : W.TwoCell,
  (GroupExtension.pathValue W RW (W.twoLeft f)).linear =
    (GroupExtension.pathValue W RW (W.twoRight f)).linear)
variable (hthree : ∀ f : W.ThreeCell,
  pastingOperation W RW cW (W.threeLeft f) = pastingOperation W RW cW (W.threeRight f))
variable (hfixed : ∀ f ∈ PW.faces,
  translation (k := k) (cW f) * GroupExtension.pathValue W RW (W.twoLeft f) =
    GroupExtension.pathValue W RW (W.twoRight f))
variable (S : Set (EdgeName (K := W)))
variable (t : Repair W RW cW (fixedEdgesForRange PW.edges CW S))
local notation "J" => ParallelPinGeometry.presentation W
local notation "tv" => realCorrection W RW cW (fixedEdgesForRange PW.edges CW S) t

/-- The generated pin construction is a complete actual input sharing precisely the original W. -/
noncomputable def contextInput : AffineContextInput W LW RW cW PW CW where
  geometry := J
  embedding := ParallelPinGeometry.embedding W
  shared := ParallelPinGeometry.oldRegion W ClosedRegion.all
  shared_vertices := by change Set.univ = Set.range id; exact Set.range_id.symm
  shared_edges := Set.image_univ
  shared_faces := Set.image_univ
  shared_triples := by change Set.univ = Set.range id; exact Set.range_id.symm
  originals := original W LW
  references := reference W RW tv
  comparisons := comparison W cW
  aligned := reference_faces W RW tv hf
  three_law := reference_three_law W RW tv cW hthree
  fixed := ParallelPinGeometry.oldRegion W PW
  fixed_faces := by
    rintro _ ⟨f,hp,rfl⟩
    change translation (k := k) (cW f) *
      GroupExtension.pathValue J (reference W RW tv) (ParallelPinGeometry.includePath W (W.twoLeft f)) =
      GroupExtension.pathValue J (reference W RW tv) (ParallelPinGeometry.includePath W (W.twoRight f))
    rw [included_word_value,included_word_value]
    exact hfixed f hp
  candidates := candidates W CW
  shared_reference _ := rfl
  shared_core _ := rfl
  shared_comparison _ := rfl
  shared_fixed_vertices _ := Iff.rfl
  shared_fixed_edges := by
    intro e
    change ParallelPinGeometry.oldEdgeName W e ∈ ParallelPinGeometry.oldEdgeName W '' PW.edges ↔ _
    constructor
    · rintro ⟨a,ha,he⟩
      exact (old_name_injective W he) ▸ ha
    · intro he; exact ⟨e,he,rfl⟩
  shared_fixed_faces := by
    intro f
    change Sum.inl f ∈ Sum.inl '' PW.faces ↔ f ∈ PW.faces
    constructor
    · rintro ⟨a,ha,he⟩
      exact (Sum.inl_injective he) ▸ ha
    · intro hf; exact ⟨f,hf,rfl⟩
  shared_fixed_triples _ := Iff.rfl
  shared_candidates := by
    intro e
    change ParallelPinGeometry.oldEdgeName W e ∈ candidates W CW ↔ e ∈ CW
    constructor
    · rintro (⟨a,ha,he⟩ | ⟨a,he⟩)
      · exact (old_name_injective W he) ▸ ha
      · exact (ParallelPinGeometry.old_ne_pin W e a he.symm).elim
    · intro he; exact Or.inl ⟨e,he,rfl⟩

local notation "I" => contextInput W LW RW cW PW CW hf hthree hfixed S t

/-- Original compatible permissions leave every new pin forbidden. -/
def contextRange : (I).Range S where
  allowed := allowed W S
  shared_allowed e _ := by
    change ParallelPinGeometry.oldEdgeName W e ∈ allowed W S ↔ e ∈ S
    constructor
    · rintro ⟨a,ha,he⟩
      exact (old_name_injective W he) ▸ ha
    · intro he; exact ⟨e,he,rfl⟩

/-- The actual whole forbidden set is the original shared condition plus the new uniformly forbidden pins. -/
theorem context_fixed_set :
    fixedEdgesForRange (I).fixed.edges (I).candidates
      (contextRange W LW RW cW PW CW hf hthree hfixed S t).allowed =
        forbidden W (fixedEdgesForRange PW.edges CW S) :=
  fixed_range_eq W PW CW S

/-- Reading any actual test object retains all its operations at the same raw pin fixed conditions. -/
def rawContextRepair (s : (I).Repairs (contextRange W LW RW cW PW CW hf hthree hfixed S t)) :
    Repair J (reference W RW tv) (comparison W cW) (forbidden W (fixedEdgesForRange PW.edges CW S)) where
  operation := s.operation
  linear := s.linear
  face := s.face
  fixed_value e he := by
    apply s.fixed_value e
    rw [context_fixed_set]
    exact he

/-- The genuine shared repair constructs an actual compatible whole test object. -/
noncomputable def contextRepair : (I).Repairs (contextRange W LW RW cW PW CW hf hthree hfixed S t) where
  operation := (singletonRepair W RW cW (fixedEdgesForRange PW.edges CW S) t).operation
  linear := (singletonRepair W RW cW (fixedEdgesForRange PW.edges CW S) t).linear
  face := (singletonRepair W RW cW (fixedEdgesForRange PW.edges CW S) t).face
  fixed_value e he := by
    apply (singletonRepair W RW cW (fixedEdgesForRange PW.edges CW S) t).fixed_value e
    rw [context_fixed_set] at he
    exact he

/-- Restriction of any compatible whole test object has exactly the original t repair operations. -/
theorem context_shared_operation
    (s : (I).Repairs (contextRange W LW RW cW PW CW hf hthree hfixed S t))
    {i j : W.Vertex} (e : W.Edge i j) :
    ((I).sharedRepair (contextRange W LW RW cW PW CW hf hthree hfixed S t) s).operation e =
      t.operation e := by
  change s.operation (.inl e) = t.operation e
  have h := forced_old_operation W RW cW (fixedEdgesForRange PW.edges CW S) tv
    (rawContextRepair W LW RW cW PW CW hf hthree hfixed S t s) e
  exact h.trans (real_correction_restore W RW cW (fixedEdgesForRange PW.edges CW S) t e).symm

/-- Full original repair equality follows from the independently evaluated actual edge operations. -/
theorem context_shared_repair
    (s : (I).Repairs (contextRange W LW RW cW PW CW hf hthree hfixed S t)) :
    (I).sharedRepair (contextRange W LW RW cW PW CW hf hthree hfixed S t) s = t := by
  apply Repair.ext
  intro i j e
  exact context_shared_operation W LW RW cW PW CW hf hthree hfixed S t s e

/-- The actual lawful compatible test environment realizes precisely the original singleton boundary. -/
theorem context_singleton_range :
    Set.range ((I).boundary (contextRange W LW RW cW PW CW hf hthree hfixed S t)) = {tv} := by
  ext u
  constructor
  · rintro ⟨s,rfl⟩
    apply Set.mem_singleton_iff.mpr
    change realCorrection W RW cW (fixedEdgesForRange PW.edges CW S)
      ((I).sharedRepair (contextRange W LW RW cW PW CW hf hthree hfixed S t) s) = tv
    rw [context_shared_repair]
  · intro hu
    have h := Set.mem_singleton_iff.mp hu
    refine ⟨contextRepair W LW RW cW PW CW hf hthree hfixed S t, ?_⟩
    change realCorrection W RW cW (fixedEdgesForRange PW.edges CW S)
      ((I).sharedRepair (contextRange W LW RW cW PW CW hf hthree hfixed S t) _) = u
    rw [context_shared_repair,h]

end AAT.AG.RelativeRepairComposition.NativeAffine.ParallelPins
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.NativeAffine.ParallelPins
