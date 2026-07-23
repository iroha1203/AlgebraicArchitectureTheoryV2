import Formal.AG.LawAlgebra.StanleyReisner

noncomputable section

namespace AAT.AG
namespace LawAlgebra

universe u v

namespace ObstructionIdeal

variable (A : Type v) [CommRing A]

/--
III.定義6.1: selected law witness ideals on one local chart.

This abstracts the R4 law-indexed ideals into the data needed for the local
obstruction ideal. Selection is explicit: only laws selected in the current
law universe contribute to `I_Ob^U(W)`.
-/
structure SelectedLawWitnessIdealFamily where
  LawIndex : Type u
  selected : LawIndex -> Prop
  witnessIdeal : LawIndex -> Ideal A

namespace SelectedLawWitnessIdealFamily

/-- III.定義6.1: elements of selected law witness ideals. -/
def selectedElementSet (F : SelectedLawWitnessIdealFamily A) : Set A :=
  {x | ∃ L, F.selected L ∧ x ∈ F.witnessIdeal L}

/-- III.定義6.1: local obstruction ideal `I_Ob^U(W) = Σ_L I_L(W)`. -/
def localObstructionIdeal (F : SelectedLawWitnessIdealFamily A) : Ideal A :=
  Ideal.span F.selectedElementSet

/-- III.定義6.1: a selected law witness ideal is contained in the local sum. -/
theorem witnessIdeal_le_localObstructionIdeal (F : SelectedLawWitnessIdealFamily A)
    {L : F.LawIndex} (hL : F.selected L) :
    F.witnessIdeal L ≤ F.localObstructionIdeal := by
  intro x hx
  exact Ideal.subset_span ⟨L, hL, hx⟩

/-- III.定義6.1: the local obstruction ideal is the least ideal containing all selected ideals. -/
theorem localObstructionIdeal_le_iff (F : SelectedLawWitnessIdealFamily A) (I : Ideal A) :
    F.localObstructionIdeal ≤ I ↔
      ∀ L, F.selected L -> F.witnessIdeal L ≤ I := by
  constructor
  · intro h L hL
    exact le_trans (witnessIdeal_le_localObstructionIdeal A F hL) h
  · intro h
    rw [localObstructionIdeal]
    apply Ideal.span_le.mpr
    rintro x ⟨L, hL, hx⟩
    exact h L hL hx

/--
III.定義6.1: the local obstruction ideal is the supremum of the witness ideals
indexed by selected laws.
-/
theorem localObstructionIdeal_eq_iSup (F : SelectedLawWitnessIdealFamily A) :
    F.localObstructionIdeal =
      ⨆ L : {L : F.LawIndex // F.selected L}, F.witnessIdeal L.1 := by
  apply le_antisymm
  · refine (localObstructionIdeal_le_iff A F _).2 ?_
    intro L hL
    exact le_iSup_of_le ⟨L, hL⟩ le_rfl
  · refine iSup_le ?_
    rintro ⟨L, hL⟩
    exact witnessIdeal_le_localObstructionIdeal A F hL

variable {A}

/--
III.定義6.2 / 定義10.2: compatibility data for restricting local obstruction
ideals along a ring restriction map.
-/
structure RestrictionCompatible {B : Type v} [CommRing B]
    (source : SelectedLawWitnessIdealFamily A)
    (target : SelectedLawWitnessIdealFamily B) (res : A →+* B) where
  maps_selected :
    ∀ L, source.selected L ->
      ∃ M, target.selected M ∧ Ideal.map res (source.witnessIdeal L) ≤ target.witnessIdeal M

/--
III.定義6.2 / 定義10.2: restriction maps selected local obstruction ideals into
the target local obstruction ideal.
-/
theorem map_localObstructionIdeal_le {B : Type v} [CommRing B]
    {source : SelectedLawWitnessIdealFamily A}
    {target : SelectedLawWitnessIdealFamily B} {res : A →+* B}
    (H : RestrictionCompatible source target res) :
    Ideal.map res source.localObstructionIdeal ≤ target.localObstructionIdeal := by
  rw [Ideal.map_le_iff_le_comap]
  rw [localObstructionIdeal]
  apply Ideal.span_le.mpr
  rintro x ⟨L, hL, hx⟩
  change res x ∈ target.localObstructionIdeal
  rcases H.maps_selected L hL with ⟨M, hM, hmap⟩
  exact witnessIdeal_le_localObstructionIdeal B target hM (hmap (Ideal.mem_map_of_mem res hx))

end SelectedLawWitnessIdealFamily

end ObstructionIdeal

end LawAlgebra
end AAT.AG
