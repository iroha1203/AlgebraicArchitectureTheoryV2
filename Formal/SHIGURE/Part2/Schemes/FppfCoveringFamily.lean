import Formal.SHIGURE.Part2.Schemes.FppfDescentData
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck

/-! # Fppf covering sieves contain actual fppf covering families -/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

/-- A sieve covering in the fppf topology contains the sieve of an actual
jointly surjective family of flat, locally finitely presented arrows. -/
theorem fppfTopology_exists_covering_family {X : Scheme.{u}} {S : Sieve X}
    (covering : S ∈ fppfTopology X) :
    ∃ cover : FppfCover.{u,u+1} X, Sieve.ofArrows cover.X cover.f ≤ S := by
  let J := Scheme.precoverage FppfComponent
  letI : J.HasIsos := ⟨fun f _ =>
    (Scheme.singleton_mem_precoverage_iff FppfComponent f).2
      ⟨(show Surjective f from inferInstance).surj,
        (inferInstance : Flat f), (inferInstance : LocallyOfFinitePresentation f)⟩⟩
  have mem : S ∈ J.toGrothendieck X := covering
  obtain ⟨R, hR, inclusion⟩ := (J.mem_toGrothendieck_iff_of_isStableUnderComposition).1 mem
  let cover : FppfCover.{u,u+1} X :=
    ⟨R.preZeroHypercover, R.presieve₀_preZeroHypercover.symm ▸ hR⟩
  have eq : cover.presieve₀ = R := R.presieve₀_preZeroHypercover
  refine ⟨cover, ?_⟩
  change Sieve.generate cover.presieve₀ ≤ S
  rw [eq, Sieve.generate_le_iff]
  exact inclusion

end

end SHIGURE.SchemeDescent
