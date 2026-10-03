import ResearchLean.AG.RepairObservationDuality.SelectedCokernel
import ResearchLean.AG.RelativeRepairComposition.OriginalCandidateColumns
import ResearchLean.AG.RelativeRepairComposition.FiniteNativeCoordinates
import ResearchLean.AG.RelativeRepairComposition.FiniteFamilyCoordinates

/-!
# Full original correction coordinates from the prescribed vertex kernel bases

## Implementation notes

G-131 A/C / n1017 §3.5, §6 uses the complete prescribed kernel basis at each
original target. Always corrections vanish at P and at every candidate;
selected corrections retain each permitted candidate's whole kernel. The
linear coordinate maps have both inverses and keep the original names.
The input is the G-130 native coefficients, modules and full vertex bases.
-/
namespace AAT.AG.RepairObservationDuality.FullCorrectionCoordinates
open TransportCoherence AbelianLiftingObstruction RelativeRepairComposition
set_option autoImplicit false
universe uk uG uA
variable {k : Type uk} [Field k]
variable {K : FiniteTransportPresentation.{uG}} (M : LocalCoefficients.{uG,uA} K)
variable [∀ v, Module k (M.A v)]
variable (bases : FiniteFamily.Bases (k := k) M.A)
variable (P : ClosedRegion K) (candidates : Set (EdgeName (K := K)))
attribute [local instance] Classical.propDecidable
local notation "A₁" => (fun e : EdgeName (K := K) => M.A (Sigma.fst (Sigma.snd e)))
local notation "B₁" => bases.comap M.A (fun e : EdgeName (K := K) => Sigma.fst (Sigma.snd e))

/-- G-131 A/C / n1017 §3.5, §6 constructor: the full masked original
edge family carries its pointwise whole-kernel module. -/
local instance alwaysRelativeModule : Module k (Family.relative A₁ Set.univ (P.edges ∪ candidates)) :=
  FiniteFamily.relativeModule A₁ Set.univ (P.edges ∪ candidates)

/-- G-131 A/C / n1017 §3.5, §6 API: the whole always space is exactly the
original edge family vanishing at P and all original candidates. -/
def alwaysFamily : OriginalColumns.alwaysSpace (k := k) M P candidates ≃ₗ[k]
    Family.relative A₁ Set.univ (P.edges ∪ candidates) where
  toFun h := ⟨h.1.1,by
    intro e he
    rcases he with hp | hc
    · exact h.1.2 e hp
    · exact h.2 ⟨e.1,hc⟩⟩
  invFun h := ⟨⟨h.1,by intro e hp; exact h.2 e (Or.inl hp)⟩,
    by intro e; exact h.2 ⟨e.1,Set.mem_univ e.1⟩ (Or.inr e.2)⟩
  left_inv h := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv h := by apply Subtype.ext; rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- G-131 A/C / n1017 §3.5, §6 constructor: every original always edge carries
all prescribed kernel coordinates; only fixed and candidate zeros are removed. -/
abbrev AlwaysIndex := FiniteFamily.Index A₁ B₁ Set.univ (P.edges ∪ candidates)

/-- G-131 A/C / n1017 §3.5, §6 constructor: whole always values in the fixed
original kernel bases, with both inverse maps. -/
noncomputable def alwaysCoordinate : OriginalColumns.alwaysSpace (k := k) M P candidates ≃ₗ[k]
    (AlwaysIndex M bases P candidates → k) :=
  (alwaysFamily M P candidates).trans (FiniteFamily.equivalence A₁ B₁ Set.univ (P.edges ∪ candidates))

/-- G-131 A/C / n1017 §3.5, §6 API: the always coordinate reads its same
original edge and prescribed complete kernel basis. -/
theorem always_value (h : OriginalColumns.alwaysSpace (k := k) M P candidates)
    (j : AlwaysIndex M bases P candidates) :
    alwaysCoordinate M bases P candidates h j =
      bases.coordinate j.1.1.2.1 (h.1.1 ⟨j.1.1,Set.mem_univ j.1.1⟩) j.2 := rfl

/-- G-131 A/C / n1017 §3.5, §6 constructor: selected candidates retain their
own original names and every prescribed target-kernel basis coordinate. -/
abbrev SelectedValues (S : Set candidates) :=
  ∀ e : S, Fin (bases.dimension e.1.1.2.1) → k

/-- G-131 A/C / n1017 §3.5, §6 constructor: every selected whole candidate
kernel has complete numerical coordinates and an inverse. -/
def selectedCoordinate (S : Set candidates) :
    (∀ e : S, M.A e.1.1.2.1) ≃ₗ[k] SelectedValues M bases candidates S :=
  LinearEquiv.piCongrRight fun e => bases.coordinate e.1.1.2.1

/-- G-131 A/C / n1017 §3.5, §6 API: a selected numerical value is its exact
original candidate's prescribed full basis value. -/
theorem selected_value (S : Set candidates) (h : ∀ e : S, M.A e.1.1.2.1)
    (e : S) (j : Fin (bases.dimension e.1.1.2.1)) :
    selectedCoordinate M bases candidates S h e j = bases.coordinate e.1.1.2.1 (h e) j := rfl

/-- G-131 A/C / n1017 §3.5, §6 constructor: the full numerical output consists
of all always coordinates and all selected candidate kernel coordinates. -/
abbrev NumericalValues (S : Set candidates) :=
  (AlwaysIndex M bases P candidates → k) × SelectedValues M bases candidates S

/-- G-131 A/C / n1017 §3.5, §6: complete original correction values and their
numerical basis values are linearly isomorphic, without image reduction. -/
noncomputable def coordinate (S : Set candidates) :
    (OriginalColumns.alwaysSpace (k := k) M P candidates × (∀ e : S, M.A e.1.1.2.1)) ≃ₗ[k]
      NumericalValues M bases P candidates S :=
  (alwaysCoordinate M bases P candidates).prodCongr (selectedCoordinate M bases candidates S)

/-- G-131 A/C / n1017 §3.5, §6 API: the inverse always coordinates restore
all prescribed kernel values of each original nonfixed, noncandidate edge. -/
theorem always_restore_value (x : AlwaysIndex M bases P candidates → k)
    (e : EdgeName (K := K)) (he : e ∉ P.edges ∪ candidates) :
    ((alwaysCoordinate M bases P candidates).symm x).1.1 ⟨e,Set.mem_univ e⟩ =
      (bases.coordinate e.2.1).symm (fun j => x ⟨⟨e,Set.mem_univ e,he⟩,j⟩) := by
  exact FiniteFamily.restore_value A₁ B₁ Set.univ (P.edges ∪ candidates) x
    ⟨e,Set.mem_univ e⟩ he

/-- G-131 A/C / n1017 §3.5, §6 API: the inverse full always coordinate map
returns zero on each original fixed edge and each original candidate. -/
theorem always_restore_zero (x : AlwaysIndex M bases P candidates → k)
    (e : EdgeName (K := K)) (he : e ∈ P.edges ∪ candidates) :
    ((alwaysCoordinate M bases P candidates).symm x).1.1 ⟨e,Set.mem_univ e⟩ = 0 := by
  exact ((alwaysFamily M P candidates)
    ((alwaysCoordinate M bases P candidates).symm x)).2 ⟨e,Set.mem_univ e⟩ he

/-- G-131 A/C / n1017 §3.5, §6 API: the inverse selected coordinate map
restores the whole prescribed kernel at the identical original candidate. -/
theorem selected_restore_value (S : Set candidates) (x : SelectedValues M bases candidates S)
    (e : S) :
    (selectedCoordinate M bases candidates S).symm x e =
      (bases.coordinate e.1.1.2.1).symm (x e) := rfl

end AAT.AG.RepairObservationDuality.FullCorrectionCoordinates
#assert_standard_axioms_only AAT.AG.RepairObservationDuality.FullCorrectionCoordinates
