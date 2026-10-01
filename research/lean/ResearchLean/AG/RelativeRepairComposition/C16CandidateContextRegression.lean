import ResearchLean.AG.RelativeRepairComposition.C16CandidateRepairs

/-!
# Internal candidate projection: distinct original inputs have identical contexts

The two actual regions impose z=y and z=2y. Their named internal correction is
retained through candidate zero and only then projected away. The forbidden
range has boundary {0}; the allowed range has the entire full F3 coordinate.
-/
namespace AAT.AG.RelativeRepairComposition.C16CandidateContextRegression
open TransportCoherence AbelianLiftingObstruction NativeAffine
open C16CandidateGeometry C16CandidateRepairs

/-- Forbidden internal candidates force the literal original shared operation to identity. -/
theorem forbidden_shared_operation (double : Bool) (S : Set (EdgeName (K := boundaryGeometry)))
    (s : (input double).Repairs (permissions double false S)) :
    s.operation (i := ()) (j := ()) false = 1 := by
  have ht := s.fixed_value (⟨(),(),true⟩ : EdgeName (K := geometry double))
    ((forbidden double false S _).mpr ⟨rfl,rfl⟩)
  change s.operation (i := ()) (j := ()) true = 1 at ht
  have hf := s.face ()
  cases double
  · change translation (k := ZMod 3) (0 : V) * (1 * s.operation (i := ()) (j := ()) true) =
      1 * s.operation (i := ()) (j := ()) false at hf
    simpa only [ht,translation_zero,one_mul] using hf.symm
  · change translation (k := ZMod 3) (0 : V) *
      ((1 * s.operation (i := ()) (j := ()) true) * s.operation (i := ()) (j := ()) true) =
        1 * s.operation (i := ()) (j := ()) false at hf
    simpa only [ht,translation_zero,one_mul] using hf.symm

/-- The forbidden range's full actual shared family is zero for every independent repair. -/
theorem forbidden_boundary (double : Bool) (S : Set (EdgeName (K := boundaryGeometry)))
    (s : (input double).Repairs (permissions double false S)) :
    (input double).boundary (permissions double false S) s = 0 := by
  funext ⟨i,j,e⟩
  cases i; cases j; cases e
  change (s.operation (i := ()) (j := ()) false * (1 : Operations (ZMod 3) V)⁻¹) 0 = 0
  rw [forbidden_shared_operation double S s,inv_one,one_mul]
  rfl

/-- Projection after all candidate zero conditions gives exactly {0} in either original input. -/
theorem forbidden_range (double : Bool) (S : Set (EdgeName (K := boundaryGeometry))) :
    Set.range ((input double).boundary (permissions double false S)) = {0} := by
  ext v
  constructor
  · rintro ⟨s,rfl⟩
    exact Set.mem_singleton_iff.mpr (forbidden_boundary double S s)
  · intro h
    refine ⟨repair double false S 0 (fun _ => rfl), ?_⟩
    exact (forbidden_boundary double S _).trans (Set.mem_singleton_iff.mp h).symm

/-- Every full shared translation has a genuine original repair when the internal candidate is allowed. -/
theorem allowed_range (double : Bool) (S : Set (EdgeName (K := boundaryGeometry))) :
    Set.range ((input double).boundary (permissions double true S)) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro v
  let e : EdgeName (K := boundaryGeometry) := ⟨(),(),()⟩
  let y := scaled double (v e)
  refine ⟨repair double true S y (fun h => Bool.noConfusion h), ?_⟩
  rw [repair_boundary]
  funext ⟨i,j,a⟩
  cases i; cases j; cases a
  exact scaled_inverse double (v e)

/-- The two different whole original candidate words have the same all-range boundary relations. -/
theorem boundary_ranges_equal (permit : Bool) (S : Set (EdgeName (K := boundaryGeometry))) :
    Set.range ((input false).boundary (permissions false permit S)) =
      Set.range ((input true).boundary (permissions true permit S)) := by
  cases permit
  · rw [forbidden_range,forbidden_range]
  · rw [allowed_range,allowed_range]

/-- The general theorem yields equal actual repair-existence outcomes in every full actual external context. -/
theorem every_actual_context (permit : Bool) (S : Set (EdgeName (K := boundaryGeometry))) :
    ∀ env : AffineContextInput.Environments (W := boundaryGeometry) (LW := boundaryReference)
      (RW := boundaryReference) (cW := fun f => Empty.elim f) (PW := ClosedRegion.empty) (CW := ∅) S,
      Nonempty (AffineContextInput.StrictRepairs (input false) env.1 (permissions false permit S) env.2) ↔
        Nonempty (AffineContextInput.StrictRepairs (input true) env.1 (permissions true permit S) env.2) :=
  ((input false).contextual_strict_actual (permissions false permit S) (input true)
    (permissions true permit S)).mpr (boundary_ranges_equal permit S)

/-- The same named internal candidate value one is retained in both independent actual inputs. -/
theorem internal_one_retained (double : Bool) (S : Set (EdgeName (K := boundaryGeometry))) :
    realCorrection (geometry double) (reference double) (fun _ => 0)
      (fixedEdgesForRange (input double).fixed.edges (input double).candidates
        (permissions double true S).allowed)
      (repair double true S (fun _ => 1) (fun h => Bool.noConfusion h)) ⟨(),(),true⟩ = (fun _ => 1) :=
  repair_internal double true S (fun _ => 1) (fun h => Bool.noConfusion h)

/-- Before eliminating internal candidates, equal internal value one has different original shared values. -/
theorem internal_relations_different (S : Set (EdgeName (K := boundaryGeometry))) :
    (input false).boundary (permissions false true S)
      (repair false true S (fun _ => 1) (fun h => Bool.noConfusion h)) ≠
    (input true).boundary (permissions true true S)
      (repair true true S (fun _ => 1) (fun h => Bool.noConfusion h)) := by
  rw [repair_boundary,repair_boundary]
  intro h
  have hv := congrArg (fun f => f ⟨(),(),()⟩ 0) h
  change (1 : ZMod 3) = 2 at hv
  exact (by decide : (1 : ZMod 3) ≠ 2) hv

end AAT.AG.RelativeRepairComposition.C16CandidateContextRegression
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.C16CandidateContextRegression
