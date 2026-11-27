import Formal.SHIGURE.Part2.Schemes.AffineFppfFaithfulness
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap

/-! # Joint faithfulness of fppf scheme covers for scheme maps -/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v

/-- Every original fppf covering family detects equality of maps into a scheme.
The scheme coproduct uses one original chart over each base point. -/
theorem fppfCover_hom_ext {X Y : Scheme.{u}} (cover : FppfCover.{u,v} X)
    {g h : X ⟶ Y} (equal : ∀ i, cover.f i ≫ g = cover.f i ≫ h) : g = h := by
  let chosen := fppfPointSubcover cover
  let c := Sigma.desc chosen.f
  haveI : Flat c :=
    IsZariskiLocalAtSource.sigmaDesc (P := @Flat) fun i => (chosen.map_prop i).1
  haveI : Surjective c := Surjective.sigmaDesc_of_union_range_eq_univ chosen.iUnion_range
  haveI : Epi c := Flat.epi_of_flat_of_surjective _
  apply (cancel_epi c).1
  apply Sigma.hom_ext
  intro i
  change Sigma.ι chosen.X i ≫ Sigma.desc chosen.f ≫ g = Sigma.ι chosen.X i ≫ Sigma.desc chosen.f ≫ h
  simp only [Sigma.ι_desc_assoc]
  exact equal (cover.idx i)

end

end SHIGURE.SchemeDescent
