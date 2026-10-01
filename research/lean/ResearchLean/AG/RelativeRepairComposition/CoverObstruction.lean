import ResearchLean.AG.RelativeRepairComposition.CoverCohomology

/-!
# The integration obstruction for the same full relative repairs

The specified local plans give z = hV| - hU|. The quotient uses both full local
H1 images. All constructions preserve the original closed fixed part P.
## Implementation notes

G-130 B specifies the second-minus-first cycle of the actual local plans.
The quotient denominator is the sum of both full local H1 ranges. The
explicit quotient permits plan changes on either side and is not a quotient
by only one local range or a chosen pair of plan classes.
-/
namespace AAT.AG.RelativeRepairComposition
open CategoryTheory TransportCoherence AbelianLiftingObstruction
universe uG uA
namespace CoverObstruction
variable {K : FiniteTransportPresentation.{uG}}
variable (M : LocalCoefficients.{uG,uA} K) (P : ClosedRegion K)
variable (δ : RelativeCover.C2 M ClosedRegion.all P) (U V : ClosedRegion K)

/-- The difference of the specified plans is a full overlap one-cycle. -/
noncomputable def differenceCycle (hU : CoverEquation.Solution M P δ U)
    (hV : CoverEquation.Solution M P δ V) : CoverCohomology.Z1 M P (ClosedRegion.inter U V) :=
  ⟨RelativeCover.r1 M P (ClosedRegion.inter_right U V) hV.1 -
    RelativeCover.r1 M P (ClosedRegion.inter_left U V) hU.1,by
    change RelativeCover.d1 M (ClosedRegion.inter U V) P (_ - _) = 0
    rw [map_sub,← RelativeCover.r_d1,← RelativeCover.r_d1,hU.2,hV.2,map_neg,map_neg]
    exact sub_self _⟩

/-- The overlap difference retains the original edge values with the second-minus-first sign. -/
theorem difference_cycle_value (hU : CoverEquation.Solution M P δ U)
    (hV : CoverEquation.Solution M P δ V) (e : (ClosedRegion.inter U V).edges) :
    (differenceCycle M P δ U V hU hV).1.1 e =
      hV.1.1 ⟨e.1,e.2.2⟩ - hU.1.1 ⟨e.1,e.2.1⟩ := rfl

/-- The two specified plans have an overlap gauge exactly when their H1 difference is zero. -/
theorem seam_exists_iff (hU : CoverEquation.Solution M P δ U)
    (hV : CoverEquation.Solution M P δ V) :
    (∃ b : RelativeCover.C0 M (ClosedRegion.inter U V) P,
      RelativeCover.r1 M P (ClosedRegion.inter_right U V) hV.1 =
        RelativeCover.r1 M P (ClosedRegion.inter_left U V) hU.1 +
          RelativeCover.d0 M (ClosedRegion.inter U V) P b) ↔
    (QuotientAddGroup.mk (differenceCycle M P δ U V hU hV) :
      CoverCohomology.H1 M P (ClosedRegion.inter U V)) = 0 := by
  rw [CoverCohomology.h1_eq_zero_iff]
  constructor
  · rintro ⟨b,hb⟩
    refine ⟨b,Subtype.ext ?_⟩
    change RelativeCover.d0 M (ClosedRegion.inter U V) P b = _ - _
    rw [hb]
    abel
  · rintro ⟨b,hb⟩
    have h := congrArg Subtype.val hb
    change RelativeCover.d0 M (ClosedRegion.inter U V) P b =
      RelativeCover.r1 M P (ClosedRegion.inter_right U V) hV.1 -
        RelativeCover.r1 M P (ClosedRegion.inter_left U V) hU.1 at h
    exact ⟨b,by rw [h]; abel⟩

/-- Both full local H1 images form exactly the denominator required by G-130 B. -/
noncomputable def localImages : AddSubgroup (CoverCohomology.H1 M P (ClosedRegion.inter U V)) :=
  (CoverCohomology.restrictH1 M P (ClosedRegion.inter_left U V)).range ⊔
    (CoverCohomology.restrictH1 M P (ClosedRegion.inter_right U V)).range

/-- The integration obstruction group is the quotient by the sum of both local images. -/
abbrev Omega := CoverCohomology.H1 M P (ClosedRegion.inter U V) ⧸ localImages M P U V

/-- The actual specified local plans determine their integration class. -/
noncomputable def omega (hU : CoverEquation.Solution M P δ U)
    (hV : CoverEquation.Solution M P δ V) : Omega M P U V :=
  QuotientAddGroup.mk (QuotientAddGroup.mk (differenceCycle M P δ U V hU hV) :
    CoverCohomology.H1 M P (ClosedRegion.inter U V))

/-- Adding any full relative cycle chooses another solution of the same actual equation. -/
noncomputable def shiftSolution (X : ClosedRegion K) (h : CoverEquation.Solution M P δ X)
    (z : CoverCohomology.Z1 M P X) : CoverEquation.Solution M P δ X :=
  ⟨h.1 + z.1,by rw [map_add,h.2,z.2,add_zero]⟩

/-- All local plan changes are the full original cycle differences. -/
noncomputable def planChange (X : ClosedRegion K) (h h' : CoverEquation.Solution M P δ X) :
    CoverCohomology.Z1 M P X :=
  ⟨h'.1 - h.1,by change RelativeCover.d1 M X P (_ - _) = 0
                 rw [map_sub,h'.2,h.2,sub_self]⟩

/-- Every other plan is obtained from its original full cycle difference. -/
theorem shift_plan_change (X : ClosedRegion K) (h h' : CoverEquation.Solution M P δ X) :
    shiftSolution M P δ X h (planChange M P δ X h h') = h' := by
  apply Subtype.ext
  change h.1 + (h'.1 - h.1) = h'.1
  abel

/-- Changing both plans changes their difference only by the two local H1 images. -/
theorem difference_cycle_change (hU hU' : CoverEquation.Solution M P δ U)
    (hV hV' : CoverEquation.Solution M P δ V) :
    differenceCycle M P δ U V hU' hV' = differenceCycle M P δ U V hU hV +
      CoverCohomology.restrictZ1 M P (ClosedRegion.inter_right U V)
        (planChange M P δ V hV hV') -
      CoverCohomology.restrictZ1 M P (ClosedRegion.inter_left U V)
        (planChange M P δ U hU hU') := by
  apply Subtype.ext
  change _ - _ = (_ - _) + RelativeCover.r1 M P (ClosedRegion.inter_right U V) (_ - _) -
    RelativeCover.r1 M P (ClosedRegion.inter_left U V) (_ - _)
  rw [map_sub,map_sub]
  abel

/-- The integration class is independent of both actual local plan choices. -/
theorem omega_independent (hU hU' : CoverEquation.Solution M P δ U)
    (hV hV' : CoverEquation.Solution M P δ V) :
    omega M P δ U V hU' hV' = omega M P δ U V hU hV := by
  let q1 := QuotientAddGroup.mk' (CoverCohomology.boundary1 M P (ClosedRegion.inter U V)).range
  let q := QuotientAddGroup.mk' (localImages M P U V)
  have hu : q (q1 (CoverCohomology.restrictZ1 M P (ClosedRegion.inter_left U V)
      (planChange M P δ U hU hU'))) = 0 := by
    change (QuotientAddGroup.mk (q1 (CoverCohomology.restrictZ1 M P (ClosedRegion.inter_left U V)
      (planChange M P δ U hU hU'))) : Omega M P U V) = 0
    rw [QuotientAddGroup.eq_zero_iff]
    exact AddSubgroup.mem_sup_left ⟨QuotientAddGroup.mk (planChange M P δ U hU hU'),rfl⟩
  have hv : q (q1 (CoverCohomology.restrictZ1 M P (ClosedRegion.inter_right U V)
      (planChange M P δ V hV hV'))) = 0 := by
    change (QuotientAddGroup.mk (q1 (CoverCohomology.restrictZ1 M P (ClosedRegion.inter_right U V)
      (planChange M P δ V hV hV'))) : Omega M P U V) = 0
    rw [QuotientAddGroup.eq_zero_iff]
    exact AddSubgroup.mem_sup_right ⟨QuotientAddGroup.mk (planChange M P δ V hV hV'),rfl⟩
  have hh := congrArg (fun z => q (q1 z))
    (difference_cycle_change M P δ U V hU hU' hV hV')
  change q (q1 (differenceCycle M P δ U V hU' hV')) =
    q (q1 (differenceCycle M P δ U V hU hV))
  simp only [map_sub,map_add] at hh
  rw [hu,hv] at hh
  exact hh.trans (by abel)

/-- Zero integration obstruction is equivalent to an original global solution. -/
theorem omega_eq_zero_iff_global (hc : ClosedRegion.Cover U V)
    (hU : CoverEquation.Solution M P δ U) (hV : CoverEquation.Solution M P δ V) :
    omega M P δ U V hU hV = 0 ↔ Nonempty (CoverEquation.Solution M P δ ClosedRegion.all) := by
  constructor
  · intro hw
    change (QuotientAddGroup.mk (QuotientAddGroup.mk (differenceCycle M P δ U V hU hV) :
      CoverCohomology.H1 M P (ClosedRegion.inter U V)) : Omega M P U V) = 0 at hw
    rw [QuotientAddGroup.eq_zero_iff] at hw
    obtain ⟨a,ha,b,hb,hab⟩ := AddSubgroup.mem_sup.mp hw
    obtain ⟨u,rfl⟩ := ha
    obtain ⟨v,rfl⟩ := hb
    obtain ⟨u,rfl⟩ := QuotientAddGroup.mk'_surjective (CoverCohomology.boundary1 M P U).range u
    obtain ⟨v,rfl⟩ := QuotientAddGroup.mk'_surjective (CoverCohomology.boundary1 M P V).range v
    let hU' := shiftSolution M P δ U hU u
    let hV' := shiftSolution M P δ V hV (-v)
    let q1 := QuotientAddGroup.mk' (CoverCohomology.boundary1 M P (ClosedRegion.inter U V)).range
    have hh : differenceCycle M P δ U V hU' hV' =
        differenceCycle M P δ U V hU hV -
          CoverCohomology.restrictZ1 M P (ClosedRegion.inter_left U V) u -
          CoverCohomology.restrictZ1 M P (ClosedRegion.inter_right U V) v := by
      apply Subtype.ext
      change RelativeCover.r1 M P (ClosedRegion.inter_right U V) (hV.1 + -v.1) -
        RelativeCover.r1 M P (ClosedRegion.inter_left U V) (hU.1 + u.1) =
        (RelativeCover.r1 M P (ClosedRegion.inter_right U V) hV.1 -
          RelativeCover.r1 M P (ClosedRegion.inter_left U V) hU.1) -
          RelativeCover.r1 M P (ClosedRegion.inter_left U V) u.1 -
          RelativeCover.r1 M P (ClosedRegion.inter_right U V) v.1
      rw [map_add,map_add,map_neg]
      abel
    have hz : (QuotientAddGroup.mk (differenceCycle M P δ U V hU' hV') :
        CoverCohomology.H1 M P (ClosedRegion.inter U V)) = 0 := by
      change q1 (differenceCycle M P δ U V hU' hV') = 0
      change q1 (CoverCohomology.restrictZ1 M P (ClosedRegion.inter_left U V) u) +
        q1 (CoverCohomology.restrictZ1 M P (ClosedRegion.inter_right U V) v) =
        q1 (differenceCycle M P δ U V hU hV) at hab
      rw [hh,map_sub,map_sub,← hab]
      abel
    obtain ⟨c,hc'⟩ := (seam_exists_iff M P δ U V hU' hV').mpr hz
    let X : CoverEquation.Descent M P δ U V :=
      { left := ⟨(),hU'⟩
        right := ⟨(),hV'⟩
        hom := Equation.homOfLabel _ _ _ _ c hc' }
    obtain ⟨a,h,ha,hh,heq⟩ := CoverEquation.glue_solution M P δ U V hc X
    refine ⟨⟨h,?_⟩⟩
    rw [CoverEquation.defect_all]
    exact heq
  · rintro ⟨h⟩
    let hu := CoverEquation.restrictSolution M P δ (ClosedRegion.to_all U) h
    let hv := CoverEquation.restrictSolution M P δ (ClosedRegion.to_all V) h
    rw [← omega_independent M P δ U V hU hu hV hv]
    have hz : differenceCycle M P δ U V hu hv = 0 := by
      apply Subtype.ext
      change RelativeCover.r1 M P (ClosedRegion.inter_right U V)
        (RelativeCover.r1 M P (ClosedRegion.to_all V) h.1) -
        RelativeCover.r1 M P (ClosedRegion.inter_left U V)
          (RelativeCover.r1 M P (ClosedRegion.to_all U) h.1) = 0
      exact sub_self _
    change (QuotientAddGroup.mk' (localImages M P U V))
      ((QuotientAddGroup.mk' (CoverCohomology.boundary1 M P (ClosedRegion.inter U V)).range)
        (differenceCycle M P δ U V hu hv)) = 0
    rw [hz,map_zero,map_zero]

end CoverObstruction
end AAT.AG.RelativeRepairComposition
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
