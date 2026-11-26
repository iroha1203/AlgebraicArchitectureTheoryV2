import Formal.SHIGURE.Part2.Schemes.OpenCoverEffective

/-! # The functor of compatible sections and its natural comparison -/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Pseudofunctor Opposite

noncomputable section

universe u

private abbrev Q := quasiCoherentModulesPseudofunctor

variable {X : Scheme.{u}} (cover : Scheme.OpenCover.{u} X)

private abbrev C := Q.toDescentData cover.f

private def openCoverComparison_fullyFaithful : (C cover).FullyFaithful := by
  letI := openCoverComparison_isEquivalence cover
  exact Functor.FullyFaithful.ofFullyFaithful _

set_option maxHeartbeats 600000 in
/-- The inverse sends descent data to the module of compatible sections and
sends local arrows to the corresponding unique global arrow. -/
def openCoverCompatibleSectionsInverse : Q.DescentData cover.f ⥤ Q.obj (.mk (op X)) where
  obj := openCoverGluedObject cover
  map {M N} f := (openCoverComparison_fullyFaithful cover).preimage
    ((openCoverGluedIso cover M).hom ≫ f ≫ (openCoverGluedIso cover N).inv)
  map_id M := by
    let h := openCoverComparison_fullyFaithful cover
    let e := openCoverGluedIso cover M
    apply h.map_injective
    change (C cover).map (h.preimage (e.hom ≫ 𝟙 M ≫ e.inv)) =
      (C cover).map (𝟙 (openCoverGluedObject cover M))
    rw [h.map_preimage, (C cover).map_id, Category.id_comp, e.hom_inv_id]
  map_comp {M N L} f g := by
    let h := openCoverComparison_fullyFaithful cover
    let a := openCoverGluedIso cover M
    let b := openCoverGluedIso cover N
    let c := openCoverGluedIso cover L
    apply h.map_injective
    change (C cover).map (h.preimage (a.hom ≫ (f ≫ g) ≫ c.inv)) =
      (C cover).map (h.preimage (a.hom ≫ f ≫ b.inv) ≫ h.preimage (b.hom ≫ g ≫ c.inv))
    rw [(C cover).map_comp, h.map_preimage, h.map_preimage, h.map_preimage]
    simp only [Category.assoc, b.inv_hom_id_assoc]

set_option maxHeartbeats 600000 in
/-- The compatible-sections construction gives back the original datum
naturally in every descent morphism. -/
def openCoverCompatibleSectionsCounit :
    openCoverCompatibleSectionsInverse cover ⋙ C cover ≅ 𝟭 (Q.DescentData cover.f) :=
  NatIso.ofComponents (openCoverGluedIso cover) (by
    intro M N f
    let h := openCoverComparison_fullyFaithful cover
    change (C cover).map (h.preimage ((openCoverGluedIso cover M).hom ≫ f ≫
      (openCoverGluedIso cover N).inv)) ≫ (openCoverGluedIso cover N).hom =
      (openCoverGluedIso cover M).hom ≫ f
    rw [h.map_preimage]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id])

set_option maxHeartbeats 600000 in
/-- The comparison equivalence uses the compatible-sections functor as its
actual inverse, with the displayed chart comparison as counit. -/
def openCoverComparisonEquivalence : Q.obj (.mk (op X)) ≌ Q.DescentData cover.f where
  functor := C cover
  inverse := openCoverCompatibleSectionsInverse cover
  unitIso := NatIso.ofComponents
    (fun M => (openCoverComparison_fullyFaithful cover).preimageIso
      (openCoverGluedIso cover ((C cover).obj M)).symm) (by
    intro M N f
    let h := openCoverComparison_fullyFaithful cover
    let e := openCoverCompatibleSectionsCounit cover
    let a := openCoverGluedIso cover ((C cover).obj M)
    let b := openCoverGluedIso cover ((C cover).obj N)
    let v := (openCoverCompatibleSectionsInverse cover).map ((C cover).map f)
    apply h.map_injective
    change (C cover).map (f ≫ h.preimage b.inv) = (C cover).map (h.preimage a.inv ≫ v)
    rw [(C cover).map_comp, (C cover).map_comp, h.map_preimage, h.map_preimage]
    exact e.inv.naturality ((C cover).map f))
  counitIso := openCoverCompatibleSectionsCounit cover
  functor_unitIso_comp M := by
    let h := openCoverComparison_fullyFaithful cover
    let e := openCoverGluedIso cover ((C cover).obj M)
    change (C cover).map (h.preimage e.inv) ≫ e.hom = 𝟙 _
    rw [h.map_preimage, e.inv_hom_id]

end

end SHIGURE.SchemeDescent
