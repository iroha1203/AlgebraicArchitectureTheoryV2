import Formal.AG.SemanticRepair.Conormal.LawGeneratedBooleanCircleLawCore
import Formal.AG.SemanticRepair.Conormal.LawGeneratedBooleanCircleTopology
import Formal.Util.AssertStandardAxioms
import Mathlib.Algebra.Category.Grp.Ulift
import Mathlib.CategoryTheory.Sites.Sheaf

/-!
# Raw conormal sheaf on the Boolean-circle site

The square-zero law-generated raw conormal presheaf satisfies the full
generated topology.  The proof first computes a unique ambient-ring
representative for every conormal class from the proved square-zero ideal,
then glues the three selected chart values through their pair overlaps.  The
Cycle 19 topology classification reduces every other precoverage pullback to
that selected sieve or the top sieve.

No sheaf condition, coefficient comparison, cocycle, cohomology class, or
vanishing conclusion is accepted as a field.
-/

noncomputable section

namespace AAT.AG.SemanticRepair.Conormal
namespace LawGeneratedBooleanCircleRawConormalSheaf

open CategoryTheory Opposite
open AAT.AG
open LawGeneratedBooleanCircleSite
open LawGeneratedBooleanCircleLawCore
open LawGeneratedBooleanCircleTopology
open LawGeneratedIdealPowerSequence

/-- The square-zero raw conormal additive presheaf. -/
abbrev rawConormal := Raw.conormalCoefficient squareZeroCore

/-- Its underlying type-valued presheaf. -/
abbrev rawConormalType := rawConormal ⋙ forget AddCommGrpCat

/-- The idempotent raw conormal additive presheaf. -/
abbrev idempotentRawConormal := Raw.conormalCoefficient idempotentCore

/-- Its underlying type-valued presheaf. -/
abbrev idempotentRawConormalType := idempotentRawConormal ⋙ forget AddCommGrpCat

/-- Square-zero makes the quotient map from the generated ideal injective. -/
theorem active_toCotangent_injective (W : site.category) :
    Function.Injective (squareZeroCore.obstructionIdeal W).toCotangent := by
  intro x y h
  rw [(squareZeroCore.obstructionIdeal W).toCotangent_eq] at h
  rw [squareZero_obstructionIdeal_sq] at h
  apply Subtype.ext
  exact sub_eq_zero.mp (by simpa using h)

/-- Every raw conormal class has a unique representative in its generated ideal. -/
noncomputable def activeIdealEquiv (W : site.category) :
    squareZeroCore.obstructionIdeal W ≃+ Raw.Conormal squareZeroCore W :=
  AddEquiv.ofBijective
    (squareZeroCore.obstructionIdeal W).toCotangent.toAddMonoidHom
    ⟨active_toCotangent_injective W,
      (squareZeroCore.obstructionIdeal W).toCotangent_surjective⟩

/-- The unique ambient-ring representative of a raw conormal class. -/
noncomputable def activeValue (W : site.category)
    (x : Raw.Conormal squareZeroCore W) : AmbientRing :=
  ((activeIdealEquiv W).symm x).1

theorem activeValue_injective (W : site.category) :
    Function.Injective (activeValue W) := by
  intro x y h
  apply (activeIdealEquiv W).symm.injective
  apply Subtype.ext
  exact h

@[simp]
theorem activeValue_toCotangent (W : site.category)
    (x : squareZeroCore.obstructionIdeal W) :
    activeValue W ((squareZeroCore.obstructionIdeal W).toCotangent x) = x.1 := by
  change ((activeIdealEquiv W).symm ((activeIdealEquiv W) x)).1 = x.1
  rw [(activeIdealEquiv W).symm_apply_apply]

/-- Away from the deep context, raw conormal restriction preserves the representative. -/
theorem conormalRestrict_activeValue (source target : site.category)
    (hs : ¬ Deep source) (f : source ⟶ target)
    (x : Raw.Conormal squareZeroCore target) :
    activeValue source (Raw.conormalRestrict squareZeroCore f x) =
      activeValue target x := by
  obtain ⟨y, rfl⟩ :=
    (squareZeroCore.obstructionIdeal target).toCotangent_surjective x
  rw [Raw.conormalRestrict_toCotangent, activeValue_toCotangent,
    activeValue_toCotangent]
  change ambientRestrict f y.1 = y.1
  rw [ambientRestrict_of_not_deep f hs]
  rfl

abbrev chartObject (i : cover.Index) : site.category :=
  Site.ContextCategoryObject.of contextPreorder (cover.patch i)

theorem chart_not_deep (i : cover.Index) : ¬ Deep (chartObject i) := by
  change Fin 3 at i
  rintro ⟨_, h⟩
  change indexOf (context (chartContextIndex i)) = Finset.univ at h
  simp only [indexOf_context, chartContextIndex] at h
  have hc := congrArg Finset.card h
  change ({i} : Finset (Fin 3)).card = (Finset.univ : Finset (Fin 3)).card at hc
  norm_num at hc

theorem base_not_deep : ¬ Deep base := by
  rintro ⟨_, h⟩
  change indexOf (context ∅) = Finset.univ at h
  have h' : (∅ : Finset (Fin 3)) = Finset.univ := by simpa using h
  have hc := congrArg Finset.card h'
  norm_num at hc

/-- Pair-overlap compatibility identifies all three active chart values. -/
theorem active_pair_compatible
    (x : (i : cover.Index) → rawConormalType.obj (op (chartObject i)))
    (hx : Presieve.Arrows.Compatible rawConormalType
      (fun i : cover.Index => homOfLE (cover.inclusion i)) x)
    (i j : cover.Index) :
    activeValue (chartObject i) (x i) = activeValue (chartObject j) (x j) := by
  change Fin 3 at i j
  let pair : site.category := Site.ContextCategoryObject.of contextPreorder
    (context (chartContextIndex i ∪ chartContextIndex j))
  have hpair : ¬ Deep pair := by
    rintro ⟨_, h⟩
    change indexOf (context (chartContextIndex i ∪ chartContextIndex j)) =
      Finset.univ at h
    have h' : ({i, j} : Finset (Fin 3)) = Finset.univ := by
      simpa [chartContextIndex] using h
    have hc := congrArg Finset.card h'
    have hle : ({i, j} : Finset (Fin 3)).card ≤ 2 := Finset.card_le_two
    norm_num [hc] at hle
  let gi : pair ⟶ chartObject i := homOfLE
    (Or.inr ⟨chartContextIndex i ∪ chartContextIndex j,
      chartContextIndex i, rfl, rfl, Finset.subset_union_left⟩)
  let gj : pair ⟶ chartObject j := homOfLE
    (Or.inr ⟨chartContextIndex i ∪ chartContextIndex j,
      chartContextIndex j, rfl, rfl, Finset.subset_union_right⟩)
  have hcompat := hx i j pair gi gj (Subsingleton.elim _ _)
  calc
    activeValue (chartObject i) (x i) =
        activeValue pair (Raw.conormalRestrict squareZeroCore gi (x i)) :=
      (conormalRestrict_activeValue pair _ hpair gi (x i)).symm
    _ = activeValue pair (Raw.conormalRestrict squareZeroCore gj (x j)) :=
      congrArg (activeValue pair) hcompat
    _ = activeValue (chartObject j) (x j) :=
      conormalRestrict_activeValue pair _ hpair gj (x j)

/-- The raw conormal presheaf glues uniquely on the actual three-chart cover. -/
theorem raw_selectedCover_isSheafFor :
    Presieve.IsSheafFor rawConormalType cover.presieve := by
  change Presieve.IsSheafFor rawConormalType
    (Presieve.ofArrows
      (fun i : cover.Index => chartObject i)
      (fun i : cover.Index => homOfLE (cover.inclusion i)))
  rw [Presieve.isSheafFor_arrows_iff]
  intro x hx
  let i0 : cover.Index := by change Fin 3; exact 0
  let y0 : squareZeroCore.obstructionIdeal (chartObject i0) :=
    (activeIdealEquiv (chartObject i0)).symm (x i0)
  let ybase : squareZeroCore.obstructionIdeal base :=
    ⟨y0.1, by
      rw [squareZero_obstructionIdeal_of_not_deep base base_not_deep]
      rw [← squareZero_obstructionIdeal_of_not_deep
        (chartObject i0) (chart_not_deep i0)]
      exact y0.property⟩
  let glue : Raw.Conormal squareZeroCore base :=
    (squareZeroCore.obstructionIdeal base).toCotangent ybase
  refine ⟨glue, ?_, ?_⟩
  · intro i
    apply activeValue_injective (chartObject i)
    change activeValue (chartObject i)
        (Raw.conormalRestrict squareZeroCore (homOfLE (cover.inclusion i)) glue) =
      activeValue (chartObject i) (x i)
    calc
      activeValue (chartObject i)
          (Raw.conormalRestrict squareZeroCore (homOfLE (cover.inclusion i)) glue) =
          activeValue base glue :=
        conormalRestrict_activeValue (chartObject i) base (chart_not_deep i) _ glue
      _ = ybase.1 := activeValue_toCotangent base ybase
      _ = y0.1 := rfl
      _ = activeValue (chartObject i) (x i) := active_pair_compatible x hx i0 i
  · intro other hother
    apply activeValue_injective base
    have h0 := hother i0
    change Raw.conormalRestrict squareZeroCore (homOfLE (cover.inclusion i0)) other =
      x i0 at h0
    have hn := conormalRestrict_activeValue (chartObject i0) base
      (chart_not_deep i0) (homOfLE (cover.inclusion i0)) other
    calc
      activeValue base other = activeValue (chartObject i0)
          (Raw.conormalRestrict squareZeroCore (homOfLE (cover.inclusion i0)) other) := hn.symm
      _ = activeValue (chartObject i0) (x i0) := congrArg _ h0
      _ = y0.1 := rfl
      _ = activeValue base glue := by simp [glue, ybase]

/-- The same gluing theorem for the sieve generated by the three charts. -/
theorem raw_selectedSieve_isSheafFor :
    Presieve.IsSheafFor rawConormalType selectedSieve.arrows :=
  (Presieve.isSheafFor_iff_generate cover.presieve).mp raw_selectedCover_isSheafFor

/-- The raw square-zero conormal type presheaf is a sheaf for the full generated topology. -/
theorem rawConormalType_isSheaf :
    Presieve.IsSheaf site.topology rawConormalType := by
  change Presieve.IsSheaf
    (Site.admissiblePrecoverage coverageRequirements contextOverlap).toGrothendieck
    rawConormalType
  rw [Precoverage.isSheaf_toGrothendieck_iff]
  intro X Y f R hR
  rcases hR with ⟨F, rfl⟩
  have hX := family_base_eq F
  subst X
  by_cases hY : Y = base
  · subst Y
    have hf : f = 𝟙 base := Subsingleton.elim _ _
    subst f
    rw [Sieve.pullback_id]
    rcases familySieve_eq_selected_or_top F with h | h
    · rw [h]
      exact raw_selectedSieve_isSheafFor
    · rw [h]
      exact Presieve.isSheafFor_top rawConormalType
  · rw [familySieve_pullback_eq_top_of_ne_base F f hY]
    exact Presieve.isSheafFor_top rawConormalType

/-- The concrete square-zero raw conormal is a sheaf valued in additive groups. -/
theorem squareZeroRawConormal_isSheaf :
    Presheaf.IsSheaf site.topology rawConormal := by
  apply Presheaf.isSheaf_of_isSheaf_comp site.topology rawConormal
    AddCommGrpCat.uliftFunctor.{1, 0}
  rw [Presheaf.isSheaf_iff_isSheaf_forget site.topology
    (rawConormal ⋙ AddCommGrpCat.uliftFunctor.{1, 0})
    (forget AddCommGrpCat)]
  rw [isSheaf_iff_isSheaf_of_type]
  change Presieve.IsSheaf site.topology
    (rawConormalType ⋙ CategoryTheory.uliftFunctor.{1, 0})
  apply (isSheaf_iff_isSheaf_of_type site.topology _).mp
  exact Presheaf.isSheaf_comp_of_isSheaf site.topology rawConormalType
    CategoryTheory.uliftFunctor.{1, 0}
    ((isSheaf_iff_isSheaf_of_type site.topology _).mpr rawConormalType_isSheaf)

/-- The idempotent raw conormal type presheaf is a sheaf because all values are zero. -/
theorem idempotentRawConormalType_isSheaf :
    Presieve.IsSheaf site.topology idempotentRawConormalType := by
  intro X R _hR x _hx
  refine ⟨0, ?_, ?_⟩
  · intro Y f hf
    change Raw.conormalRestrict idempotentCore f 0 = x f hf
    calc
      Raw.conormalRestrict idempotentCore f 0 = 0 :=
        map_zero (Raw.conormalRestrict idempotentCore f)
      _ = x f hf := (idempotent_conormal_eq_zero Y (x f hf)).symm
  · intro other _hother
    exact idempotent_conormal_eq_zero X other

/-- The concrete idempotent raw conormal is a sheaf valued in additive groups. -/
theorem idempotentRawConormal_isSheaf :
    Presheaf.IsSheaf site.topology idempotentRawConormal := by
  apply Presheaf.isSheaf_of_isSheaf_comp site.topology idempotentRawConormal
    AddCommGrpCat.uliftFunctor.{1, 0}
  rw [Presheaf.isSheaf_iff_isSheaf_forget site.topology
    (idempotentRawConormal ⋙ AddCommGrpCat.uliftFunctor.{1, 0})
    (forget AddCommGrpCat)]
  rw [isSheaf_iff_isSheaf_of_type]
  change Presieve.IsSheaf site.topology
    (idempotentRawConormalType ⋙ CategoryTheory.uliftFunctor.{1, 0})
  apply (isSheaf_iff_isSheaf_of_type site.topology _).mp
  exact Presheaf.isSheaf_comp_of_isSheaf site.topology idempotentRawConormalType
    CategoryTheory.uliftFunctor.{1, 0}
    ((isSheaf_iff_isSheaf_of_type site.topology _).mpr
      idempotentRawConormalType_isSheaf)

end LawGeneratedBooleanCircleRawConormalSheaf
end AAT.AG.SemanticRepair.Conormal

#assert_standard_axioms_only AAT.AG.SemanticRepair.Conormal.LawGeneratedBooleanCircleRawConormalSheaf
