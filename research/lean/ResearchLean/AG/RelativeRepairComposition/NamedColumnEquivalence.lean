import ResearchLean.AG.RelativeRepairComposition.NamedDualRanges

/-!
# Full named range and dual transport across linear equivalences

Name transport, every entire source kernel and the whole quotient participate.
The hypotheses are literal whole column values. Applications discharge them
from the actual correction, differential and quotient constructions.
-/
namespace AAT.AG.RelativeRepairComposition.NamedColumnEquivalence
universe uk ue uf uy uz uo up
variable {k : Type uk} [Field k]
variable {E : Type ue} {F : Type uf} {Y : E → Type uy} {Z : F → Type uz}
variable [∀ e, AddCommGroup (Y e)] [∀ f, AddCommGroup (Z f)]
variable [∀ e, Module k (Y e)] [∀ f, Module k (Z f)]
variable {O : Type uo} {P : Type up} [AddCommGroup O] [AddCommGroup P]
variable [Module k O] [Module k P]
variable (B : ∀ e, Y e →ₗ[k] O) (C : ∀ f, Z f →ₗ[k] P)
variable (names : E ≃ F) (kernels : ∀ e, Y e ≃ₗ[k] Z (names e)) (quotient : P ≃ₗ[k] O)
variable (hcolumns : ∀ e x, quotient (C (names e) (kernels e x)) = B e x)

include hcolumns in
/-- Every selected whole range is carried to the range of all corresponding original whole columns. -/
theorem range_map (S : Set E) :
    (NamedDual.ranges C (names '' S)).map quotient.toLinearMap = NamedDual.ranges B S := by
  apply le_antisymm
  · apply Submodule.map_le_iff_le_comap.mpr
    apply iSup_le
    intro f
    apply iSup_le
    rintro ⟨e,he,rfl⟩
    rintro _ ⟨z,rfl⟩
    obtain ⟨x,rfl⟩ := (kernels e).surjective z
    change quotient (C (names e) (kernels e x)) ∈ NamedDual.ranges B S
    rw [hcolumns]
    exact NamedDual.range_le B S e he ⟨x,rfl⟩
  · apply iSup_le
    intro e
    apply iSup_le
    intro he
    rintro _ ⟨x,rfl⟩
    refine ⟨C (names e) (kernels e x),?_,hcolumns e x⟩
    exact NamedDual.range_le C (names '' S) (names e) ⟨e,he,rfl⟩ ⟨kernels e x,rfl⟩

include hcolumns in
/-- Entire selected range membership is reflected by the whole quotient equivalence. -/
theorem mem_range_iff (S : Set E) (o : P) :
    o ∈ NamedDual.ranges C (names '' S) ↔ quotient o ∈ NamedDual.ranges B S := by
  rw [← range_map B C names kernels quotient hcolumns S]
  constructor
  · intro h
    exact ⟨o,h,rfl⟩
  · rintro ⟨p,hp,he⟩
    exact (quotient.injective he) ▸ hp

/-- Transport all quotient duals using the actual whole quotient linear equivalence. -/
noncomputable def dualEquiv : Module.Dual k O ≃ₗ[k] Module.Dual k P := quotient.dualMap

/-- Transported dual evaluation retains the value of every quotient element. -/
theorem dualEquiv_value (phi : Module.Dual k O) (o : P) :
    dualEquiv quotient phi o = phi (quotient o) := rfl

include hcolumns in
/-- Vanishing on a whole new column is precisely vanishing on its original whole column. -/
theorem annihilates_iff (phi : Module.Dual k O) (e : E) :
    (dualEquiv quotient phi).comp (C (names e)) = 0 ↔ phi.comp (B e) = 0 := by
  constructor
  · intro h
    ext x
    have hv := LinearMap.congr_fun h (kernels e x)
    change phi (quotient (C (names e) (kernels e x))) = 0 at hv
    rw [hcolumns] at hv
    exact hv
  · intro h
    ext z
    obtain ⟨x,rfl⟩ := (kernels e).surjective z
    change phi (quotient (C (names e) (kernels e x))) = 0
    rw [hcolumns]
    exact LinearMap.congr_fun h x

include hcolumns in
/-- Every nonzero whole-column dual support retains exactly all its original complete names. -/
theorem support_eq (phi : Module.Dual k O) :
    NamedDual.support C (dualEquiv quotient phi) = names '' NamedDual.support B phi := by
  ext f
  obtain ⟨e,rfl⟩ := names.surjective f
  rw [Set.mem_image]
  constructor
  · intro h
    exact ⟨e,fun hz => h ((annihilates_iff B C names kernels quotient hcolumns phi e).mpr hz),rfl⟩
  · rintro ⟨j,hj,he⟩
    have hje := names.injective he
    subst j
    exact fun hz => hj ((annihilates_iff B C names kernels quotient hcolumns phi e).mp hz)

include hcolumns in
/-- The entire family of dual supports nonzero on the same obstruction is preserved. -/
theorem obstruction_support_family (o : P) :
    {U : Set F | ∃ psi : Module.Dual k P, psi o ≠ 0 ∧ U = NamedDual.support C psi} =
      {U : Set F | ∃ phi : Module.Dual k O, phi (quotient o) ≠ 0 ∧
        U = names '' NamedDual.support B phi} := by
  ext U
  constructor
  · rintro ⟨psi,hp,rfl⟩
    obtain ⟨phi,rfl⟩ := (dualEquiv quotient).surjective psi
    exact ⟨phi,hp,support_eq B C names kernels quotient hcolumns phi⟩
  · rintro ⟨phi,hp,rfl⟩
    exact ⟨dualEquiv quotient phi,hp,(support_eq B C names kernels quotient hcolumns phi).symm⟩

include hcolumns in
/-- Hitting every full obstruction support is equivalent for every named permission range. -/
theorem hits_iff (o : P) (S : Set E) :
    NamedDual.Hits C o (names '' S) ↔ NamedDual.Hits B (quotient o) S := by
  rw [← NamedDual.mem_ranges_iff_hits,← NamedDual.mem_ranges_iff_hits]
  exact mem_range_iff B C names kernels quotient hcolumns S o

include hcolumns in
/-- Inclusion-minimal full ranges retain precisely their corresponding complete names. -/
theorem minimal_range_iff (o : P) (S : Set E) :
    Minimal (fun V => o ∈ NamedDual.ranges C V) (names '' S) ↔
      Minimal (fun V => quotient o ∈ NamedDual.ranges B V) S := by
  constructor
  · rintro ⟨hs,hm⟩
    refine ⟨(mem_range_iff B C names kernels quotient hcolumns S o).mp hs,?_⟩
    intro V hv hvs e he
    have hnew := hm ((mem_range_iff B C names kernels quotient hcolumns V o).mpr hv)
      (Set.image_mono hvs) ⟨e,he,rfl⟩
    obtain ⟨j,hj,hje⟩ := hnew
    exact (names.injective hje) ▸ hj
  · rintro ⟨hs,hm⟩
    refine ⟨(mem_range_iff B C names kernels quotient hcolumns S o).mpr hs,?_⟩
    intro V hv hvs f hf
    rcases hf with ⟨e,he,rfl⟩
    have hq : quotient o ∈ NamedDual.ranges B (names.symm '' V) := by
      apply (mem_range_iff B C names kernels quotient hcolumns _ o).mp
      rw [names.image_symm_image]
      exact hv
    have hsub : names.symm '' V ⊆ S := by
      rintro _ ⟨j,hj,rfl⟩
      obtain ⟨a,ha,haj⟩ := hvs hj
      simpa only [← haj,Equiv.symm_apply_apply] using ha
    obtain ⟨j,hj,hje⟩ := hm hq hsub he
    have heq : j = names e := by
      rw [← hje,Equiv.apply_symm_apply]
    exact heq ▸ hj

include hcolumns in
/-- Minimal transversals of all nonzero obstruction duals are preserved for every permission range. -/
theorem minimal_hits_iff (o : P) (S : Set E) :
    Minimal (NamedDual.Hits C o) (names '' S) ↔
      Minimal (NamedDual.Hits B (quotient o)) S := by
  rw [← NamedDual.minimal_iff,← NamedDual.minimal_iff]
  exact minimal_range_iff B C names kernels quotient hcolumns o S

end AAT.AG.RelativeRepairComposition.NamedColumnEquivalence
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.NamedColumnEquivalence
