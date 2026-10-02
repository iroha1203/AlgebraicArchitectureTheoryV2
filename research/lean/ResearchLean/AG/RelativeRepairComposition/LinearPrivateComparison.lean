import ResearchLean.AG.RelativeRepairComposition.FiniteCoordinatePartition

/-!
# Full private spaces under a public-preserving linear comparison

## Implementation notes

This is the restriction of a complete linear equivalence to zero public
coordinates. The supplemental coordinate is unrestricted. The comparison law
is an input to this general linear API and is proved from the actual local
collapse by its subdivision consumer.
-/
namespace AAT.AG.RelativeRepairComposition.LinearPrivateComparison
universe uk ux un uz uw ur
variable {k : Type uk} [Field k]
variable {X : Type ux} {N : Type un} {Z : Type uz} {W : Type uw} {R : Type ur}
variable [AddCommGroup X] [AddCommGroup N] [AddCommGroup Z] [AddCommGroup W] [AddCommGroup R]
variable [Module k X] [Module k N] [Module k Z] [Module k W] [Module k R]
variable (L : (N × W) ≃ₗ[k] ((X × Z) × R)) (p : W ≃ₗ[k] Z)
variable (hp : ∀ h, p h.2 = (L h).1.2)

include p hp in
/-- A full private input has exactly zero old public component. -/
theorem forward_public_zero (x : N) : (L (x,0)).1.2 = 0 := by
  rw [← hp (x,0),map_zero]

include p hp in
/-- Restoring all old private and supplemental values has zero new public component. -/
theorem inverse_public_zero (x : X) (r : R) : (L.symm ((x,0),r)).2 = 0 := by
  apply p.injective
  rw [hp,L.apply_symm_apply,map_zero]

/-- Forward private coordinates retain all old private and all supplemental values. -/
def forward : N →ₗ[k] (X × R) :=
  ((LinearMap.fst k X Z).comp
    ((LinearMap.fst k (X × Z) R).comp L.toLinearMap)).prod
    ((LinearMap.snd k (X × Z) R).comp L.toLinearMap) |>.comp (LinearMap.inl k N W)

/-- Inverse private coordinates restore both unrestricted input components. -/
def restore : (X × R) →ₗ[k] N :=
  (LinearMap.fst k N W).comp (L.symm.toLinearMap.comp
    (((LinearMap.inl k X Z).comp (LinearMap.fst k X R)).prod (LinearMap.snd k X R)))

/-- The forward API reads the full equivalence rather than a chosen zero section. -/
theorem forward_value (x : N) : forward L x = ((L (x,0)).1.1,(L (x,0)).2) := rfl

/-- The inverse API reads the full inverse on every private and supplemental value. -/
theorem restore_value (x : X) (r : R) : restore L (x,r) = (L.symm ((x,0),r)).1 := rfl

include p hp in
/-- Inserting the forward private pair recovers the entire compared input. -/
theorem forward_insert (x : N) :
    (((forward L x).1,0),(forward L x).2) = L (x,0) := by
  rw [forward_value]
  exact Prod.ext (Prod.ext rfl (forward_public_zero L p hp x).symm) rfl

include p hp in
/-- Inserting the inverse private value recovers the entire inverse input. -/
theorem restore_insert (x : X) (r : R) :
    (restore L (x,r),0) = L.symm ((x,0),r) := by
  rw [restore_value]
  exact Prod.ext rfl (inverse_public_zero L p hp x r).symm

/-- Restriction to private coordinates is a full linear equivalence with the whole supplement. -/
def equivalence : N ≃ₗ[k] (X × R) where
  toFun := forward L
  invFun := restore L
  left_inv x := by
    change (L.symm (((forward L x).1,0),(forward L x).2)).1 = x
    rw [forward_insert L p hp,L.symm_apply_apply]
  right_inv xr := by
    rcases xr with ⟨x,r⟩
    rw [forward_value,restore_insert L p hp,L.apply_symm_apply]
  map_add' := (forward L).map_add
  map_smul' := (forward L).map_smul

/-- The restricted equivalence has the full forward private values. -/
theorem equivalence_value (x : N) : equivalence L p hp x = forward L x := rfl

/-- The restricted inverse has the full restored private values. -/
theorem equivalence_inverse_value (x : X) (r : R) :
    (equivalence L p hp).symm (x,r) = restore L (x,r) := rfl

end AAT.AG.RelativeRepairComposition.LinearPrivateComparison
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.LinearPrivateComparison
