import ResearchLean.AG.RelativeRepairComposition.AffinePinOperations

/-!
# An actual singleton test environment with full real operations

A genuine shared repair supplies t. New parallel candidates stay forbidden.
Their authored identity faces force each old repaired edge to translation t R.
The statements concern object values; vertex relabellings are not fixed here.
-/
namespace AAT.AG.RelativeRepairComposition.NativeAffine.ParallelPins
open TransportCoherence AbelianLiftingObstruction
universe uk uA uG
variable {k : Type uk} [Field k] {A : Type uA} [AddCommGroup A] [Module k A]
variable (K : FiniteTransportPresentation.{uG})
variable (R : ∀ {i j : K.Vertex}, K.Edge i j → Operations k A)
variable (c : K.TwoCell → A) (fixed : Set (EdgeName (K := K)))
local notation "J" => ParallelPinGeometry.presentation K

/-- Old physically fixed edges and all new forbidden pins have their reference values. -/
def forbidden : Set (EdgeName (K := J)) :=
  ParallelPinGeometry.oldEdgeName K '' fixed ∪ Set.range (ParallelPinGeometry.pinEdgeName K)

/-- Restrict any actual environment repair to the independently defined old repair. -/
def restrictRepair (t : EdgeName (K := K) → A)
    (s : Repair J (reference K R t) (comparison K c) (forbidden K fixed)) :
    Repair K R c fixed where
  operation := oldOperation K s.operation
  linear e := s.linear (.inl e)
  face f := by
    have h := s.face (.inl f)
    change translation (k := k) (c f) *
      GroupExtension.pathValue J s.operation (ParallelPinGeometry.includePath K (K.twoLeft f)) =
      GroupExtension.pathValue J s.operation (ParallelPinGeometry.includePath K (K.twoRight f)) at h
    rw [included_word_value, included_word_value] at h
    exact h
  fixed_value e he := s.fixed_value (ParallelPinGeometry.oldEdgeName K e) (Or.inl ⟨e, he, rfl⟩)

/-- A genuine old repair supplies real operations on both names of each parallel pair. -/
def singletonRepair (t : Repair K R c fixed) :
    Repair J (reference K R (realCorrection K R c fixed t)) (comparison K c)
      (forbidden K fixed) where
  operation := extendOperation K t.operation t.operation
  linear e := by
    cases e with
    | inl e => exact t.linear e
    | inr e => exact (t.linear e).trans (pin_linear K R _ e).symm
  face f := by
    cases f with
    | inl f =>
      change translation (k := k) (c f) *
        GroupExtension.pathValue J (extendOperation K t.operation t.operation)
          (ParallelPinGeometry.includePath K (K.twoLeft f)) =
        GroupExtension.pathValue J (extendOperation K t.operation t.operation)
          (ParallelPinGeometry.includePath K (K.twoRight f))
      rw [included_word_value, included_word_value]
      exact t.face f
    | inr e =>
      change translation (k := k) (0 : A) * (1 * t.operation e.2.2) = 1 * t.operation e.2.2
      have hz : translation (k := k) (0 : A) = 1 := by ext x; simp
      rw [hz, one_mul]
  fixed_value e he := by
    rcases he with ⟨a, ha, rfl⟩ | ⟨a, rfl⟩
    · exact t.fixed_value a ha
    · exact real_correction_restore K R c fixed t a.2.2

/-- A pin face and its prohibition force the same actual old operation specified by t. -/
theorem forced_old_operation (t : EdgeName (K := K) → A)
    (s : Repair J (reference K R t) (comparison K c) (forbidden K fixed))
    {i j : K.Vertex} (e : K.Edge i j) :
    s.operation (.inl e) = translation (k := k) (t ⟨i,j,e⟩) * R e := by
  have hf := s.face (.inr ⟨i,j,e⟩)
  change translation (k := k) (0 : A) * (1 * s.operation (.inl e)) =
    1 * s.operation (.inr e) at hf
  have hz : translation (k := k) (0 : A) = 1 := by ext x; simp
  rw [hz, one_mul, one_mul, one_mul] at hf
  exact hf.trans (s.fixed_value (ParallelPinGeometry.pinEdgeName K ⟨i,j,e⟩)
    (Or.inr ⟨⟨i,j,e⟩, rfl⟩))

/-- Every environment repair restricts to exactly the specified full shared correction. -/
theorem singleton_correction (t : EdgeName (K := K) → A)
    (s : Repair J (reference K R t) (comparison K c) (forbidden K fixed)) :
    realCorrection K R c fixed (restrictRepair K R c fixed t s) = t := by
  funext e
  unfold realCorrection
  change (s.operation (.inl e.2.2) * (R e.2.2)⁻¹) 0 = t e
  rw [forced_old_operation, mul_assoc, mul_inv_cancel, mul_one]
  simp

/-- The actual test environment has one shared value and admits that value. -/
theorem singleton_boundary (t : Repair K R c fixed) (u : EdgeName (K := K) → A) :
    (∃ s : Repair J (reference K R (realCorrection K R c fixed t)) (comparison K c)
        (forbidden K fixed),
      realCorrection K R c fixed (restrictRepair K R c fixed _ s) = u) ↔
      u = realCorrection K R c fixed t := by
  constructor
  · rintro ⟨s, hs⟩
    exact hs.symm.trans (singleton_correction K R c fixed _ s)
  · intro h
    refine ⟨singletonRepair K R c fixed t, ?_⟩
    exact (singleton_correction K R c fixed _ _).trans h.symm

/-- The test operations restrict to the same independently specified old repair. -/
theorem restrict_singleton (t : Repair K R c fixed) :
    restrictRepair K R c fixed _ (singletonRepair K R c fixed t) = t := by
  apply Repair.ext
  intro i j e
  rfl

end AAT.AG.RelativeRepairComposition.NativeAffine.ParallelPins
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.NativeAffine.ParallelPins
