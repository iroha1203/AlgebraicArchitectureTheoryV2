import Formal.SHIGURE.Part2.Families.SchemeLaws
import Formal.SHIGURE.Part2.Schemes.ConstantRankExamples

/-! # A nonvacuous scheme-Law instance pair

For Definition 6.1 and the instance-pair criterion, a single nullary
primitive is interpreted on the actual rank-one structure sheaf over
`Spec ℤ`. The fixed written Law requires its designated section to vanish.
The zero sheaf morphism satisfies it, while the identity sheaf morphism
does not. Both carriers have the same proved finite locally free rank one.

## Implementation notes

The empty input of this primitive is the tensor unit `𝒪`, rather than an
empty signature. The negative witness evaluates the actual section map on
the empty pure tensor at the whole affine open; `ΓSpecIso` detects `1 ≠ 0`.
-/

namespace SHIGURE.RealizationFamilies.SchemeLawExamples

open AlgebraicGeometry CategoryTheory Opposite SchemeDescent TensorRealization

noncomputable section

/-- The concrete signature for the Definition 6.1 instance pair has one
sort and one nullary total primitive, with no relations or quantities. -/
def sectionSignature : Signature where
  SortType := Unit
  Total := Unit
  Rel := Empty
  Partial := Empty
  Quantity := Empty
  totalArity _ := ⟨[], ()⟩
  relInputs := Empty.elim
  partialArity := Empty.elim
  quantityArity := Empty.elim

/-- The written equation for the instance pair sets the designated
section of the sole carrier to zero. -/
def vanishingSectionLaw : TensorLaw ℤ sectionSignature where
  source := .arguments []
  target := .sort ()
  left := .total ()
  right := .zero _ _

/-- A fixed, nonempty tensor-Law presentation used for both instances. -/
def vanishingSectionLaws : AffineLawPresentation ℤ sectionSignature where
  tensorIndex := Unit
  tensorLaw _ := vanishingSectionLaw
  polynomialIndex := Empty
  inputs := Empty.elim
  output := Empty.elim
  polynomialLaw i := nomatch i

/-- Interpret the nullary primitive by an actual endomorphism of the
structure sheaf. This connects the fixture directly to sheaf semantics. -/
def sectionStructure
    (f : unitModule (Spec (CommRingCat.of ℤ)) ⟶ unitModule (Spec (CommRingCat.of ℤ))) :
    SchemeTensorStructure (Spec (CommRingCat.of ℤ)) sectionSignature where
  carrier _ := unitModule _
  total _ := f
  quantity q := nomatch q

/-- Both fixtures carry the actual free rank-one structure sheaf; the
rank premise in the realization property is discharged geometrically. -/
theorem sectionStructure_rank_one
    (f : unitModule (Spec (CommRingCat.of ℤ)) ⟶ unitModule (Spec (CommRingCat.of ℤ)))
    (s : sectionSignature.SortType) :
    IsFiniteLocallyFreeOfRank ((sectionStructure f).carrier s) 1 := by
  apply (IsFiniteLocallyFreeOfRank.ofIso (N := unitModule (Spec (CommRingCat.of ℤ)))
    (M := (tilde.functor (CommRingCat.of ℤ)).obj (ModuleCat.of ℤ ℤ)) ?_
    (tildeSelf (R := CommRingCat.of ℤ)))
  apply (affineTilde_finiteLocallyFreeOfRank_iff _ 1).mpr
  refine ⟨CoefficientDescent.finiteLocallyFree_iff_finite_projective.mpr
    ⟨inferInstance, inferInstance⟩, ?_⟩
  intro p
  simp only [Module.rankAtStalk_self, Pi.one_apply]

/-- The zero nullary sheaf morphism satisfies the fixed written Law on
every affine open, supplying the positive scheme-Law instance. -/
theorem zeroSection_satisfiesSchemeLaws :
    SatisfiesSchemeLaws vanishingSectionLaws (𝟙 _) (sectionStructure 0) := by
  intro U
  constructor
  · intro i
    change PiTensorProduct.lift ((sectionsStructure (sectionStructure 0) U.1).total ()) = 0
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro x
    change (PiTensorProduct.lift ((sectionsStructure (sectionStructure 0) U.1).total ()))
      (PiTensorProduct.tprod _ x) = 0
    rw [PiTensorProduct.lift.tprod]
    change (0 : unitModule (Spec (CommRingCat.of ℤ)) ⟶ _).val.app (op U.1)
      (pureTensorSections (sectionStructure 0).carrier U.1 [] x) = 0
    rfl
  · intro i
    exact nomatch i

/-- The identity nullary sheaf morphism sends the empty pure tensor to
`1` on the whole affine open, contradicting the same written Law. -/
theorem identitySection_not_satisfiesSchemeLaws :
    ¬ SatisfiesSchemeLaws vanishingSectionLaws (𝟙 _) (sectionStructure (𝟙 _)) := by
  intro h
  let U : (Spec (CommRingCat.of ℤ)).affineOpens := ⟨⊤, isAffineOpen_top _⟩
  have law := h.tensor U ()
  change PiTensorProduct.lift ((sectionsStructure (sectionStructure (𝟙 _)) U.1).total ()) = 0 at law
  have value := LinearMap.congr_fun law
    (PiTensorProduct.tprod Γ(Spec (CommRingCat.of ℤ), U.1) (fun i => nomatch i.2))
  rw [PiTensorProduct.lift.tprod] at value
  change pureTensorSections (sectionStructure (𝟙 _)).carrier U.1 [] _ = 0 at value
  rw [pureTensorSections_nil] at value
  have scalar := congrArg (fun x => (Scheme.ΓSpecIso (CommRingCat.of ℤ)).hom x) value
  exact (by decide : (1 : ℤ) ≠ 0) (by simpa only [map_one, map_zero] using scalar)

/-- The positive Law instance and its proved carrier rank combine to a
rank-one realization of Definition 6.1. -/
theorem zeroSection_schemeRealizationProperty :
    schemeRealizationProperty vanishingSectionLaws (fun _ => 1) (𝟙 _) (sectionStructure 0) :=
  ⟨sectionStructure_rank_one 0, zeroSection_satisfiesSchemeLaws⟩

/-- The identity fixture has the same rank-one carrier but fails the
realization property because its designated section violates the Law. -/
theorem identitySection_not_schemeRealizationProperty :
    ¬ schemeRealizationProperty vanishingSectionLaws (fun _ => 1) (𝟙 _)
      (sectionStructure (𝟙 _)) :=
  fun h => identitySection_not_satisfiesSchemeLaws h.2

end

end SHIGURE.RealizationFamilies.SchemeLawExamples
