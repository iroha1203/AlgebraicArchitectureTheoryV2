import ResearchLean.AG.FaceRelationSubdivision.ElementaryRawConnection
import ResearchLean.AG.FaceRelationSubdivision.ElementaryLawLift

/-!
# 指定持ち上げと同じ有限列文脈の読み戻し

## Implementation notes

指定原始三角面補正を同じ生成sectionへ照合し、前後の任意実射を合成しても
標準ホモトピーと旧H1読み戻しが保たれることを証明する。
前後には原始有限列の直接実射を具体適用でき、別の診断certificateを必要としない。
-/
noncomputable section
open CategoryTheory
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution ResolutionInvariance TwoPhase AtlasDefectComposition
universe u
variable {Source : Type u} [Fintype Source] {q : Reading Source}
variable {X Y : ThreeCochainComplex.{0,u} ℚ}
namespace TriangleAddition
variable (N : TargetSupportedNerve q) (e : N.nerve.EdgeComponent)
variable (laws : FiniteLawFamily Source) (ha : laws.Adequate q)
variable (before : ThreeCochainComplex.Hom X ((supported N e).lawGeneratedComplex laws ha))
variable (after : ThreeCochainComplex.Hom (N.lawGeneratedComplex laws ha) Y)

/-- 指定持ち上げを同じ実有限列の前後へ合成した標準ホモトピー。 -/
def rawLiftContextHomotopy : Homotopy
    (zeroExtensionMap (cochainComp (cochainComp before (liftedLawS N e laws ha)) after))
    (zeroExtensionMap (cochainComp (cochainComp before ((rawEquivalence N e).lawS laws ha ha)) after)) := by
  rw [rawEquivalence_lawS_eq]
  simp only [zeroExtensionMap_comp]
  exact ((liftedLawHomotopy N e laws ha).compLeft (zeroExtensionMap before)).compRight (zeroExtensionMap after)

/-- 同じ指定持ち上げを任意有限列文脈に置いても全整数次数の読み戻しは同じ。 -/
theorem rawLiftContext_homologyMap (n : ℤ) :
    HomologicalComplex.homologyMap
      (zeroExtensionMap (cochainComp (cochainComp before (liftedLawS N e laws ha)) after)) n =
    HomologicalComplex.homologyMap
      (zeroExtensionMap (cochainComp (cochainComp before ((rawEquivalence N e).lawS laws ha ha)) after)) n :=
  (rawLiftContextHomotopy N e laws ha before after).homologyMap_eq n

/-- 同じ指定持ち上げを任意有限列文脈に置いても既存H1商の読み戻しは同じ。 -/
theorem rawLiftContext_h1Map :
    (cochainComp (cochainComp before (liftedLawS N e laws ha)) after).h1Map =
      (cochainComp (cochainComp before ((rawEquivalence N e).lawS laws ha ha)) after).h1Map := by
  rw [cochainComp_h1Map, cochainComp_h1Map, cochainComp_h1Map, cochainComp_h1Map,
    liftedLawS_h1Map, rawEquivalence_lawS_eq]

end TriangleAddition
namespace EdgeSubdivision
variable (N : TargetSupportedNerve q) (e : N.nerve.EdgeComponent)
variable (o : Occurrence N e)
variable (laws : FiniteLawFamily Source) (ha : laws.Adequate q)
variable (before : ThreeCochainComplex.Hom X ((supported N e).lawGeneratedComplex laws ha))
variable (after : ThreeCochainComplex.Hom (N.lawGeneratedComplex laws ha) Y)

/-- 指定持ち上げを同じ実有限列の前後へ合成した標準ホモトピー。 -/
def rawLiftContextHomotopy : Homotopy
    (zeroExtensionMap (cochainComp (cochainComp before (liftedLawS N e o laws ha)) after))
    (zeroExtensionMap (cochainComp (cochainComp before ((rawEquivalence N e).lawS laws ha ha)) after)) := by
  rw [rawEquivalence_lawS_eq]
  simp only [zeroExtensionMap_comp]
  exact ((liftedLawHomotopy N e o laws ha).compLeft (zeroExtensionMap before)).compRight (zeroExtensionMap after)

/-- 同じ指定持ち上げを任意有限列文脈に置いても全整数次数の読み戻しは同じ。 -/
theorem rawLiftContext_homologyMap (n : ℤ) :
    HomologicalComplex.homologyMap
      (zeroExtensionMap (cochainComp (cochainComp before (liftedLawS N e o laws ha)) after)) n =
    HomologicalComplex.homologyMap
      (zeroExtensionMap (cochainComp (cochainComp before ((rawEquivalence N e).lawS laws ha ha)) after)) n :=
  (rawLiftContextHomotopy N e o laws ha before after).homologyMap_eq n

/-- 同じ指定持ち上げを任意有限列文脈に置いても既存H1商の読み戻しは同じ。 -/
theorem rawLiftContext_h1Map :
    (cochainComp (cochainComp before (liftedLawS N e o laws ha)) after).h1Map =
      (cochainComp (cochainComp before ((rawEquivalence N e).lawS laws ha ha)) after).h1Map := by
  rw [cochainComp_h1Map, cochainComp_h1Map, cochainComp_h1Map, cochainComp_h1Map,
    liftedLawS_h1Map, rawEquivalence_lawS_eq]

end EdgeSubdivision
end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
