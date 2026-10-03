import ResearchLean.AG.RelativeRepairComposition.W3ActualArrows

/-! # Complete W3 isomorphisms from the original loop

The converse constructs a full label on both original vertices for arbitrary
actual objects. It does not replace the repair category with its loop values.
-/
namespace AAT.AG.RelativeRepairComposition.W3LoopIsomorphisms
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
open NativeAffine W3LinearAction W3AffineInput W3Regions W3AuthoredOperations
open W3ActualRepairs W3GaugeLabels W3GaugeAction W3ActualArrows
attribute [local instance] actualAction

/-- The loop is the actual composition of both independent repaired operations. -/
def loopCoordinate {sheared : Bool} {S : Set (EdgeName (K := geometry))}
    (R : ActualCategory sheared S) : A :=
  loopValue sheared (parameters R.back).1 (parameters R.back).2

/-- Arbitrary actual repairs are isomorphic exactly when their original loop difference is in (I-T)A. -/
theorem isomorphic_iff_loop (sheared : Bool) (R Q : ActualCategory sheared candidates) :
    IsIsomorphic R Q ↔ ∃ bs : A,
      loopCoordinate Q = loopCoordinate R + (bs - linearAction sheared bs) := by
  constructor
  · rintro ⟨f⟩
    exact ⟨f.hom.1.toAdd.1 vertexS, hom_loop f.hom⟩
  · rintro ⟨bs, h⟩
    let bt := bs + (parameters Q.back).1 - (parameters R.back).1
    let b := unrestrictedLabel sheared bs bt
    have hb : b +ᵥ R.back = Q.back := by
      apply (gauge_eq_iff_parameters sheared candidates b R.back Q.back).mpr
      constructor
      · rw [unrestricted_source, unrestricted_target]
        dsimp only [bt]
        abel_nf
      · rw [unrestricted_source, unrestricted_target]
        dsimp only [bt]
        have hv : (parameters Q.back).2 =
            loopCoordinate R + (bs - linearAction sheared bs) -
              linearAction sheared (parameters Q.back).1 :=
          eq_sub_of_add_eq h
        rw [hv]
        unfold loopCoordinate loopValue
        rw [map_sub, map_add]
        abel_nf
    exact ⟨(Groupoid.isoEquivHom R Q).symm ⟨Multiplicative.ofAdd b, hb⟩⟩

/-- The shear's complete loop class is its actual second coordinate. -/
def shearInvariant (R : ActualCategory true candidates) : ZMod 3 := loopCoordinate R 1

/-- Shear actual repairs are isomorphic precisely when these original second coordinates agree. -/
theorem shear_isomorphic_iff (R Q : ActualCategory true candidates) :
    IsIsomorphic R Q ↔ shearInvariant R = shearInvariant Q := by
  rw [isomorphic_iff_loop]
  constructor
  · rintro ⟨bs,h⟩
    have h1 := congrFun h 1
    change loopCoordinate Q 1 = loopCoordinate R 1 + (bs 1 - bs 1) at h1
    simpa [shearInvariant] using h1.symm
  · intro h
    let bs : A := fun i => if i = 0 then 0 else loopCoordinate R 0 - loopCoordinate Q 0
    refine ⟨bs, ?_⟩
    funext i
    fin_cases i
    · change loopCoordinate Q 0 = loopCoordinate R 0 +
        (0 - (0 + (loopCoordinate R 0 - loopCoordinate Q 0)))
      abel_nf
    · change loopCoordinate Q 1 = loopCoordinate R 1 + (bs 1 - bs 1)
      simpa [shearInvariant] using h.symm

/-- Identity actual repairs are isomorphic precisely when their entire original loop vectors agree. -/
theorem identity_isomorphic_iff (R Q : ActualCategory false candidates) :
    IsIsomorphic R Q ↔ loopCoordinate R = loopCoordinate Q := by
  rw [isomorphic_iff_loop]
  constructor
  · rintro ⟨bs,h⟩
    simpa [identity_apply] using h.symm
  · intro h
    exact ⟨0, by simpa using h.symm⟩

end AAT.AG.RelativeRepairComposition.W3LoopIsomorphisms
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.W3LoopIsomorphisms
