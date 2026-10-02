import ResearchLean.AG.RelativeRepairComposition.NativeIdentityComplex

/-!
# Native projection onto a factor with a contractible complement

The native chain maps are the original coordinate projection and zero section.
The homotopy uses the supplied native contraction of the second whole complex.

## Implementation notes

This lemma is used with the constructed full identity-kernel contraction. Its
input homotopy is not an unproved field in the subdivision data. Projection
identities are checked on every original coordinate and in every degree.
-/
namespace AAT.AG.RelativeRepairComposition.NativeProductComplex
open CategoryTheory Limits
universe u
variable (K L : CochainComplex AddCommGrpCat.{u} ℕ)

/-- The coordinate zero section followed by the original projection is the literal identity. -/
theorem inl_fst : inl K L ≫ fst K L = 𝟙 K := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro x
  rfl

/-- Both original coordinate projectors sum to the literal identity in every degree. -/
theorem projector_sum : fst K L ≫ inl K L + snd K L ≫ inr K L = 𝟙 (complex K L) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro x
  exact Prod.ext (add_zero _) (zero_add _)

/-- A contraction of the entire second complex gives the projection a native homotopy inverse. -/
noncomputable def contractionEquiv (h : Homotopy (𝟙 L) 0) : HomotopyEquiv (complex K L) K where
  hom := fst K L
  inv := inl K L
  homotopyHomInvId := by
    have hs : Homotopy (snd K L ≫ inr K L) 0 := by
      simpa using (h.compLeft (snd K L)).compRight (inr K L)
    exact ((Homotopy.ofEq (projector_sum K L).symm).trans
      (((Homotopy.refl (fst K L ≫ inl K L)).add hs).trans
        (Homotopy.ofEq (add_zero _)))).symm
  homotopyInvHomId := Homotopy.ofEq (inl_fst K L)

/-- Every native homology degree is preserved by the same coordinate projection. -/
noncomputable def homologyIso (h : Homotopy (𝟙 L) 0) (n : ℕ) :
    (complex K L).homology n ≅ K.homology n :=
  (contractionEquiv K L h).toHomologyIso n

/-- The native homology isomorphism uses precisely the original coordinate projection. -/
theorem homologyIso_hom (h : Homotopy (𝟙 L) 0) (n : ℕ) :
    (homologyIso K L h n).hom = HomologicalComplex.homologyMap (fst K L) n := rfl

end AAT.AG.RelativeRepairComposition.NativeProductComplex
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.NativeProductComplex
