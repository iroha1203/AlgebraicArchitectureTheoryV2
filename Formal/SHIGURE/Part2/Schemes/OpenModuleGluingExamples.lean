import Formal.SHIGURE.Part2.Schemes.DescentRechart
import Formal.SHIGURE.Part2.Schemes.OpenModuleGluing
import Formal.SHIGURE.Part2.Schemes.QuasiCoherentZariskiStack

/-! # Module gluing on the principal opens of 2 and 3 in Spec ℤ -/

namespace SHIGURE.SchemeDescent.OpenModuleGluingExamples

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Scheme.Modules

noncomputable section

private def integers : CommRingCat := .of ℤ

private def chartDenominator (i : Bool) : ℤ := if i then 3 else 2

private theorem charts_span : Ideal.span (Set.range chartDenominator) = ⊤ := by
  apply (Ideal.eq_top_iff_one _).2
  have two : (2 : ℤ) ∈ Ideal.span (Set.range chartDenominator) :=
    Ideal.subset_span ⟨false, rfl⟩
  have three : (3 : ℤ) ∈ Ideal.span (Set.range chartDenominator) :=
    Ideal.subset_span ⟨true, rfl⟩
  exact (show (1 : ℤ) = 3 - 2 by decide) ▸ (Ideal.span (Set.range chartDenominator)).sub_mem three two

private def cover : (Spec integers).OpenCover :=
  (Scheme.affineOpenCoverOfSpanRangeEqTop (R := integers) chartDenominator charts_span).openCover

private abbrev integerComparison := quasiCoherentModulesPseudofunctor.toDescentData cover.f

private def integerQuasiCoherent : quasiCoherentModulesPseudofunctor.obj (.mk (op (Spec integers))) :=
  ⟨(tilde.functor integers).obj (ModuleCat.of integers integers),
    isQuasiCoherentModule_of_tilde _ ⟨ModuleCat.of integers integers, ⟨Iso.refl _⟩⟩⟩

/-- On the original principal opens `D(2)` and `D(3)`, every compatible pair
of maps between the rank-one restrictions descends uniquely. -/
theorem integersQuasiCoherentMapDescent
    (localMap : integerComparison.obj integerQuasiCoherent ⟶ integerComparison.obj integerQuasiCoherent) :
    ∃! f : integerQuasiCoherent ⟶ integerQuasiCoherent, integerComparison.map f = localMap := by
  letI : integerComparison.IsEquivalence := openCoverComparison_isEquivalence_anySize cover
  refine ⟨integerComparison.preimage localMap, integerComparison.map_preimage localMap, ?_⟩
  intro f h
  exact integerComparison.map_injective (h.trans (integerComparison.map_preimage localMap).symm)

private abbrev D := cover.gluedCover

private def rankOne : D.glued.Modules := SheafOfModules.unit D.glued.ringCatSheaf

private def charts : ModuleGluingData D := ModuleGluingData.ofModule rankOne

/-- The glued scheme of the two principal opens is the original affine scheme. -/
def integersChartGluing : D.glued ≅ Spec integers := asIso cover.fromGlued

/-- The rank-one modules on the two principal opens recover the original sheaf. -/
def integersModuleGluing : rankOne ≅ charts.compatibleModule :=
  ModuleGluingData.reglueIso rankOne

/-- The local identity maps satisfy the actual overlap equations. -/
private def chartIdentity : charts.CompatibleMorphisms charts where
  map i := 𝟙 (charts.module i)
  naturality i j := by simp

/-- Gluing the two local identity maps yields the unique global identity. -/
theorem integersModuleMapGluing :
    ModuleGluingData.glueMorphism chartIdentity = 𝟙 charts.compatibleModule := by
  obtain ⟨g, hg, unique⟩ := ModuleGluingData.existsUnique_glueMorphism chartIdentity
  exact (unique _ (ModuleGluingData.glueMorphism_chart chartIdentity)).trans
    (unique _ (fun i => by simp [chartIdentity])).symm

private def negateIso {X : Scheme} {M N : X.Modules} (e : M ≅ N) : M ≅ N where
  hom := -e.hom
  inv := -e.inv
  hom_inv_id := by simp
  inv_hom_id := by simp

private def liftedCover : Scheme.OpenCover.{1} (Spec integers) :=
  cover.reindex (Equiv.ulift : ULift.{1} cover.I₀ ≃ cover.I₀)

private abbrev liftedComparison := quasiCoherentModulesPseudofunctor.toDescentData liftedCover.f
private abbrev liftedRankOne := liftedComparison.obj integerQuasiCoherent

private def signedChart (i : liftedCover.I₀) : liftedRankOne.obj i ≅ liftedRankOne.obj i :=
  if (show Bool from i.down) = true then
    let I := (quasiCoherentModulesProperty.prop (.mk (op (liftedCover.X i)))).fullyFaithfulι
    I.preimageIso (negateIso (Iso.refl (liftedRankOne.obj i).obj))
  else Iso.refl _

private def signedLocalData : quasiCoherentModulesPseudofunctor.DescentData liftedCover.f :=
  descentRechart (X := liftedRankOne.obj) liftedRankOne signedChart

set_option maxHeartbeats 550000 in
/-- Use opposite rank-one trivializations on `D(2)` and `D(3)`, with the
indices in a larger universe. The compatible-sections inverse recovers both
local modules and their changed overlap comparison. -/
def integersLiftedOpenCoverObjectDescent :
    let e := openCoverComparisonEquivalence_anySize liftedCover
    e.functor.obj (e.inverse.obj signedLocalData) ≅ signedLocalData :=
  (openCoverComparisonEquivalence_anySize liftedCover).counitIso.app signedLocalData

private def badCharts : ModuleGluingData D where
  module := charts.module
  transition i j := negateIso (charts.transition i j)

private theorem badRight (i j : D.J) :
    badCharts.restrictRight i j = -charts.restrictRight i j := by
  simp [ModuleGluingData.restrictRight, badCharts, negateIso, Preadditive.comp_neg]

private abbrev twoChart : D.J := false

private def twoOpen : D.glued.Opens := (D.ι twoChart) ''ᵁ (⊤ : (D.U twoChart).Opens)

private theorem twoOpen_le : twoOpen ≤ (D.ι twoChart).opensRange :=
  (D.ι twoChart).image_le_opensRange _

private def scalarToRational : Localization.Away (2 : ℤ) →+* ℚ :=
  IsLocalization.Away.lift (g := Int.castRingHom ℚ) (x := 2) (isUnit_iff_ne_zero.mpr (by norm_num))

private def sectionToRational : Γ(D.glued, twoOpen) →+* ℚ :=
  scalarToRational.comp
    (((Scheme.ΓSpecIso (CommRingCat.of (Localization.Away (2 : ℤ)))).hom).hom.comp
      ((D.ι twoChart).appIso (⊤ : (D.U twoChart).Opens)).hom.hom)

private def unitOnChart :
    Γ(rankOne, twoOpen) ⟶ Γ(charts.chartPushforward twoChart, twoOpen) :=
  ((restrictAdjunction (D.ι twoChart)).unit.app rankOne).app twoOpen

private theorem unitOnChart_isIso : IsIso unitOnChart := by
  unfold unitOnChart
  rw [restrictAdjunction_unit_app_app]
  have eq := ((D.ι twoChart).image_preimage_eq_opensRange_inf twoOpen).trans (inf_eq_right.mpr twoOpen_le)
  have same : homOfLE ((D.ι twoChart).image_preimage_le twoOpen) = eqToHom eq := Subsingleton.elim _ _
  rw [same]
  infer_instance

private def oneSection : Γ(rankOne, twoOpen) := (1 : Γ(D.glued, twoOpen))

private theorem oneSection_ne_neg : oneSection ≠ -oneSection := by
  intro h
  change (1 : Γ(D.glued, twoOpen)) = -(1 : Γ(D.glued, twoOpen)) at h
  have impossible := congrArg sectionToRational h
  norm_num at impossible

/-- Negating the transitions on the same nonzero modules breaks the self-overlap condition. -/
theorem nonIdentityTransition_not_cocycle : ¬ badCharts.Cocycle := by
  intro condition
  have correct := charts.transport_restrictRight twoChart twoChart twoOpen twoOpen_le
  have identity : charts.transport twoChart twoChart twoOpen twoOpen_le = 𝟙 _ :=
    (ModuleGluingData.ofModule_cocycle rankOne).identity twoChart twoOpen twoOpen_le
  rw [identity, Category.id_comp] at correct
  have invalid := badCharts.transport_restrictRight twoChart twoChart twoOpen twoOpen_le
  rw [condition.identity, Category.id_comp] at invalid
  have equal : (charts.restrictRight twoChart twoChart).app twoOpen =
      - (charts.restrictRight twoChart twoChart).app twoOpen :=
    correct.trans (invalid.symm.trans (congrArg (fun f => f.app twoOpen) (badRight twoChart twoChart)))
  letI := charts.restrictRight_app_isIso twoChart twoChart twoOpen twoOpen_le
  letI := unitOnChart_isIso
  apply oneSection_ne_neg
  apply ((ConcreteCategory.isIso_iff_bijective unitOnChart).mp inferInstance).injective
  apply ((ConcreteCategory.isIso_iff_bijective ((charts.restrictRight twoChart twoChart).app twoOpen)).mp
    inferInstance).injective
  have opposite := congrArg (fun f => f (unitOnChart oneSection)) equal
  simpa only [map_neg] using opposite

end

end SHIGURE.SchemeDescent.OpenModuleGluingExamples
