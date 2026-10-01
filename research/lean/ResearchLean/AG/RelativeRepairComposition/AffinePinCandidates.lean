import ResearchLean.AG.RelativeRepairComposition.AffineSingletonEnvironment

/-! # Same original candidate names and the uniformly forbidden new pins -/
namespace AAT.AG.RelativeRepairComposition.NativeAffine.ParallelPins
open TransportCoherence
universe uG
variable (K : FiniteTransportPresentation.{uG})
local notation "J" => ParallelPinGeometry.presentation K

/-- Old candidates keep their names; every parallel pin is an additional candidate. -/
def candidates (C : Set (EdgeName (K := K))) : Set (EdgeName (K := J)) :=
  ParallelPinGeometry.oldEdgeName K '' C ∪ Set.range (ParallelPinGeometry.pinEdgeName K)

/-- The allowed range keeps exactly the old allowed names and includes no pin. -/
def allowed (S : Set (EdgeName (K := K))) : Set (EdgeName (K := J)) :=
  ParallelPinGeometry.oldEdgeName K '' S

/-- Inclusion of old names is injective for all typed endpoints and parallel edges. -/
theorem old_name_injective : Function.Injective (ParallelPinGeometry.oldEdgeName K) := by
  rintro ⟨i,j,e⟩ ⟨a,b,f⟩ h
  cases h
  rfl

/-- The new candidate names cannot occur in any old allowed range. -/
theorem pin_never_allowed (S : Set (EdgeName (K := K))) (e : EdgeName (K := K)) :
    ParallelPinGeometry.pinEdgeName K e ∉ allowed K S := by
  rintro ⟨f, _, h⟩
  exact ParallelPinGeometry.old_ne_pin K f e h

/-- Physical fixed edges and forbidden candidates are exactly the old conditions plus all pins. -/
theorem fixed_range_eq (P : ClosedRegion K) (C S : Set (EdgeName (K := K))) :
    fixedEdgesForRange (ParallelPinGeometry.oldRegion K P).edges
      (candidates K C) (allowed K S) = forbidden K (fixedEdgesForRange P.edges C S) := by
  ext e
  constructor
  · rintro (⟨a,ha,rfl⟩ | ⟨hc,hs⟩)
    · exact Or.inl ⟨a,Or.inl ha,rfl⟩
    · rcases hc with ⟨a,ha,rfl⟩ | hp
      · refine Or.inl ⟨a,Or.inr ⟨ha,?_⟩,rfl⟩
        intro hsa
        exact hs ⟨a,hsa,rfl⟩
      · exact Or.inr hp
  · rintro (⟨a,(hp | hc),rfl⟩ | ⟨a,rfl⟩)
    · exact Or.inl ⟨a,hp,rfl⟩
    · refine Or.inr ⟨Or.inl ⟨a,hc.1,rfl⟩,?_⟩
      rintro ⟨b,hb,he⟩
      have hab : b = a := old_name_injective K he
      exact hc.2 (hab ▸ hb)
    · exact Or.inr ⟨Or.inr ⟨a,rfl⟩, pin_never_allowed K S a⟩

/-- Expanding the old allowed range preserves the exact pin prohibition. -/
theorem allowed_mono {S T : Set (EdgeName (K := K))} (h : S ⊆ T) :
    allowed K S ⊆ allowed K T := Set.image_mono h

end AAT.AG.RelativeRepairComposition.NativeAffine.ParallelPins
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.NativeAffine.ParallelPins
