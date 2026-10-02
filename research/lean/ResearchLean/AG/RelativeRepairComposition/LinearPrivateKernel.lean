import ResearchLean.AG.RelativeRepairComposition.LinearPrivateComparison

/-!
# Whole private image and kernel of a supplemental linear comparison

## Implementation notes

The private differential ignores the supplemental summand because that
identity is proved by the actual cochain consumer. Restricting the full private
equivalence retains every kernel vector and every supplemental value. Image
equality uses the full inverse on each old private input.
-/
namespace AAT.AG.RelativeRepairComposition.LinearPrivateKernel
universe uk ux un uv ur
variable {k : Type uk} [Field k]
variable {X : Type ux} {N : Type un} {V : Type uv} {R : Type ur}
variable [AddCommGroup X] [AddCommGroup N] [AddCommGroup V] [AddCommGroup R]
variable [Module k X] [Module k N] [Module k V] [Module k R]
variable (e : N ≃ₗ[k] (X × R)) (Dn : N →ₗ[k] V) (Do : X →ₗ[k] V)
variable (hd : ∀ x, Dn x = Do (e x).1)

include hd in
/-- Every full private image is preserved in both directions. -/
theorem range_eq : LinearMap.range Dn = LinearMap.range Do := by
  ext v
  constructor
  · rintro ⟨x,rfl⟩
    exact ⟨(e x).1,(hd x).symm⟩
  · rintro ⟨x,rfl⟩
    refine ⟨e.symm (x,0),?_⟩
    rw [hd,e.apply_symm_apply]

/-- The whole new private kernel has all old kernel and supplemental values. -/
def equivalence : LinearMap.ker Dn ≃ₗ[k] (LinearMap.ker Do × R) where
  toFun x := (⟨(e x.1).1,by
    change Do (e x.1).1 = 0
    rw [← hd]
    exact x.2⟩,(e x.1).2)
  invFun x := ⟨e.symm (x.1.1,x.2),by
    change Dn (e.symm (x.1.1,x.2)) = 0
    rw [hd,e.apply_symm_apply]
    exact x.1.2⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x.1)
  right_inv x := by
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst (e.apply_symm_apply (x.1.1,x.2))
    · change (e (e.symm (x.1.1,x.2))).2 = x.2
      exact congrArg Prod.snd (e.apply_symm_apply (x.1.1,x.2))
  map_add' x y := by
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst (e.map_add x.1 y.1)
    · change (e (x.1 + y.1)).2 = (e x.1).2 + (e y.1).2
      exact congrArg Prod.snd (e.map_add x.1 y.1)
  map_smul' a x := by
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst (e.map_smul a x.1)
    · change (e (a • x.1)).2 = a • (e x.1).2
      exact congrArg Prod.snd (e.map_smul a x.1)

/-- Kernel coordinates read the complete private equivalence on every original kernel vector. -/
theorem equivalence_value (x : LinearMap.ker Dn) :
    ((equivalence e Dn Do hd x).1.1,(equivalence e Dn Do hd x).2) = e x.1 := rfl

/-- Kernel restoration recovers the full inverse on every old kernel and supplemental value. -/
theorem equivalence_inverse_value (x : LinearMap.ker Do) (r : R) :
    ((equivalence e Dn Do hd).symm (x,r)).1 = e.symm (x.1,r) := rfl

end AAT.AG.RelativeRepairComposition.LinearPrivateKernel
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.LinearPrivateKernel
