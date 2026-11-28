import Formal.SHIGURE.Part2.Schemes.AffineSingletonFromCoefficients
import Mathlib.Algebra.Algebra.Prod
import Mathlib.Algebra.Algebra.Rat

/-! # A nontrivial affine singleton descent example -/

namespace SHIGURE.SchemeDescent.AffineSingletonExamples

open AlgebraicGeometry CategoryTheory

noncomputable section

private abbrev Base := ℚ
private abbrev Cover := ℚ × ℚ

/-- The two-component product algebra gives a genuine faithfully flat affine
singleton whose geometric comparison is an equivalence. -/
theorem splitComparison_equivalence :
    (quasiCoherentModulesPseudofunctor.toDescentData
      (fun _ : Unit => affineScalarMap Base Cover)).IsEquivalence :=
  affineSingletonFaithfullyFlatDescent (A := Base) (B := Cover)

/-- The equivalence still distinguishes zero from identity on the line. -/
theorem splitComparison_distinguishes_maps :
    let T := affineTildeFunctor (CommRingCat.of Base)
    let K := quasiCoherentModulesPseudofunctor.toDescentData
      (fun _ : Unit => affineScalarMap Base Cover)
    let L := ModuleCat.of Base Base
    K.map (T.map (𝟙 L)) ≠ K.map (T.map (0 : L ⟶ L)) := by
  dsimp only
  let T := affineTildeFunctor (CommRingCat.of Base)
  let K := quasiCoherentModulesPseudofunctor.toDescentData
    (fun _ : Unit => affineScalarMap Base Cover)
  let L := ModuleCat.of Base Base
  letI : K.IsEquivalence := splitComparison_equivalence
  intro equal
  have same : (𝟙 L : L ⟶ L) = 0 :=
    (affineTildeEquivalence (CommRingCat.of Base)).fullyFaithfulFunctor.map_injective
      (K.map_injective equal)
  have value := congrArg (fun f : L ⟶ L => f (1 : Base)) same
  norm_num at value

/-- The map to the zero ring is not faithfully flat over a nonzero base. -/
theorem zeroRing_not_faithfullyFlat : ¬ Module.FaithfullyFlat Base PUnit := by
  intro flat
  letI : Module.FaithfullyFlat Base PUnit := flat
  have equal : (0 : Base) = 1 :=
    eq_of_smul_eq_smul (α := PUnit) (fun _ => Subsingleton.elim _ _)
  exact zero_ne_one equal

end
end SHIGURE.SchemeDescent.AffineSingletonExamples
