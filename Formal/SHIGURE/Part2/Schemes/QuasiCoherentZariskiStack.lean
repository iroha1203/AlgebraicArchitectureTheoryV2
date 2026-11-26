import Mathlib.AlgebraicGeometry.Sites.BigZariski
import Mathlib.CategoryTheory.Sites.Descent.Precoverage
import Formal.SHIGURE.Part2.Schemes.OpenCoverDescentEquivalence

/-! # The Zariski stack of quasi-coherent modules -/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Pseudofunctor Opposite

noncomputable section

universe t u

private abbrev Q := quasiCoherentModulesPseudofunctor

variable {X : Scheme.{u}} (cover : Scheme.OpenCover.{t} X)

private abbrev OpenIndices := Set.range (fun i : cover.I₀ => (cover.f i).opensRange)

private def representative (U : OpenIndices cover) : cover.I₀ := U.property.choose

private theorem representative_range (U : OpenIndices cover) :
    (cover.f (representative cover U)).opensRange = U.val := U.property.choose_spec

private def smallOpenCover : Scheme.OpenCover.{u} X where
  toPreZeroHypercover := cover.toPreZeroHypercover.restrictIndex (representative cover)
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun x => ?_, fun U => cover.map_prop (representative cover U)⟩
    obtain ⟨i, y, hy⟩ := cover.exists_eq x
    let U : OpenIndices cover := ⟨(cover.f i).opensRange, ⟨i, rfl⟩⟩
    have hx : x ∈ (cover.f (representative cover U)).opensRange := by
      rw [representative_range]
      exact ⟨y, hy⟩
    obtain ⟨z, hz⟩ := hx
    exact ⟨U, z, hz⟩

private def rangeIndex (i : cover.I₀) : OpenIndices cover :=
  ⟨(cover.f i).opensRange, ⟨i, rfl⟩⟩

private def representativeIso (i : cover.I₀) :
    cover.X i ≅ (smallOpenCover cover).X (rangeIndex cover i) :=
  IsOpenImmersion.isoOfRangeEq (cover.f i) (cover.f (representative cover (rangeIndex cover i)))
    (congrArg (fun U : X.Opens => (U : Set X)) (representative_range cover (rangeIndex cover i)).symm)

private theorem restrictRepresentativeSquare (U : OpenIndices cover) :
    𝟙 ((smallOpenCover cover).X U) ≫ cover.f (representative cover U) =
      (smallOpenCover cover).f U ≫ (𝟙 X) := by
  simp only [Category.id_comp, Category.comp_id]
  rfl

private theorem expandRepresentativeSquare (i : cover.I₀) :
    (representativeIso cover i).hom ≫ (smallOpenCover cover).f (rangeIndex cover i) = cover.f i ≫ 𝟙 X := by
  rw [Category.comp_id]
  exact IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

private def representativeDescentEquivalence : Q.DescentData cover.f ≌ Q.DescentData (smallOpenCover cover).f :=
  DescentData.pullFunctorEquivalence Q (Iso.refl X) (α := representative cover) (β := rangeIndex cover)
    (p' := fun U => 𝟙 ((smallOpenCover cover).X U)) (q' := fun i => (representativeIso cover i).hom)
    (restrictRepresentativeSquare cover) (expandRepresentativeSquare cover)

set_option maxHeartbeats 500000 in
private def representativeDescentComparison :
    Q.toDescentData cover.f ⋙ (representativeDescentEquivalence cover).functor ≅
      Q.toDescentData (smallOpenCover cover).f := by
  let small := smallOpenCover cover
  let P := Q.toDescentData small.f
  let i : (Q.map (𝟙 (LocallyDiscrete.mk (op X)))).toFunctor ≅ 𝟭 _ :=
    Cat.Hom.toNatIso (Q.mapId (LocallyDiscrete.mk (op X)))
  let k := DescentData.toDescentDataCompPullFunctorIso Q (p := 𝟙 X)
    (f' := small.f) (α := representative cover) (p' := fun U => 𝟙 (small.X U))
    (restrictRepresentativeSquare cover)
  exact k ≪≫ Functor.isoWhiskerRight i P ≪≫ Functor.leftUnitor P

private def equivalenceThroughRefinement {C D E : Type*} [Category C] [Category D] [Category E]
    (L : C ≌ E) (R : D ≌ E) (F : C ⥤ D) (h : F ⋙ R.functor ≅ L.functor) : C ≌ D :=
  (L.trans R.symm).changeFunctor (h.isoCompInverse (H := R)).symm

set_option maxHeartbeats 500000 in
/-- The inverse first restricts the datum to representative image opens and
then uses their compatible sections. The original comparison is the forward
functor, and its counit recovers every original chart and transition. -/
def openCoverComparisonEquivalence_anySize : Q.obj (.mk (op X)) ≌ Q.DescentData cover.f :=
  equivalenceThroughRefinement (openCoverComparisonEquivalence (smallOpenCover cover))
    (representativeDescentEquivalence cover) (Q.toDescentData cover.f)
    (representativeDescentComparison cover)

/-- Effective descent applies to the original covering family at any index universe. -/
theorem openCoverComparison_isEquivalence_anySize :
    (Q.toDescentData cover.f).IsEquivalence :=
  (openCoverComparisonEquivalence_anySize cover).isEquivalence_functor

/-- Geometric quasi-coherent modules with all module maps form a stack for
Zariski covers, by their compatible sections and local module maps. -/
theorem quasiCoherentModules_isZariskiStack :
    quasiCoherentModulesPseudofunctor.{u}.IsStack Scheme.zariskiTopology := by
  apply IsStack.of_precoverage (J := Scheme.zariskiPrecoverage)
  intro X R hR
  let cover : Scheme.OpenCover.{u + 1} X :=
    ⟨R.preZeroHypercover, R.presieve₀_preZeroHypercover.symm ▸ hR⟩
  have eq : cover.presieve₀ = R := R.presieve₀_preZeroHypercover
  rw [← eq]
  exact (isStackFor_ofArrows_iff quasiCoherentModulesPseudofunctor cover.f).2
    (openCoverComparison_isEquivalence_anySize cover)

end

end SHIGURE.SchemeDescent
