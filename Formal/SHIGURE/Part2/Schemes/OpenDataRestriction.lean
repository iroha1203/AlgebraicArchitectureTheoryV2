import Formal.SHIGURE.Part2.Schemes.OpenRestrictionDescent

/-! # Ordinary restrictions of open-cover descent data -/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory Opposite Scheme.Modules
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

noncomputable section

universe u

variable {ι : Type u} {X : Scheme.{u}} {U : ι → Scheme.{u}} {f : ∀ i, U i ⟶ X}
  (data : quasiCoherentModulesPseudofunctor.DescentData f)

set_option maxHeartbeats 450000 in
/-- The comparison of descent data on an open test scheme, expressed as an
isomorphism between ordinary restrictions. -/
def openDataRestrictIso {T : Scheme.{u}} {i j : ι} (base : T ⟶ X)
    (a : T ⟶ U i) (b : T ⟶ U j) [IsOpenImmersion a] [IsOpenImmersion b]
    (ha : a ≫ f i = base) (hb : b ≫ f j = base) :
    (data.obj i).obj.restrict a ≅ (data.obj j).obj.restrict b := by
  let inclusion := (quasiCoherentModulesProperty.prop (.mk (op T))).ι
  let first := (restrictFunctorIsoPullback a).app (data.obj i).obj
  let last := (restrictFunctorIsoPullback b).app (data.obj j).obj
  let middle := inclusion.mapIso (data.iso base a b ha hb)
  exact first ≪≫ middle ≪≫ last.symm

private theorem openDataRestrictIso_hom {T : Scheme.{u}} {i j : ι} (base : T ⟶ X)
    (a : T ⟶ U i) (b : T ⟶ U j) [IsOpenImmersion a] [IsOpenImmersion b]
    (ha : a ≫ f i = base) (hb : b ≫ f j = base) :
    (openDataRestrictIso data base a b ha hb).hom =
      (restrictFunctorIsoPullback a).hom.app (data.obj i).obj ≫
      (quasiCoherentModulesProperty.prop (.mk (op T))).ι.map (data.hom base a b ha hb) ≫
      (restrictFunctorIsoPullback b).inv.app (data.obj j).obj := rfl

set_option maxRecDepth 1400 in
set_option maxHeartbeats 425000 in
/-- The restriction comparisons on two test schemes agree after restricting
along an open immersion over the base. -/
theorem openDataRestrictIso_naturality {T V : Scheme.{u}} {i j : ι}
    (k : T ⟶ V) (base : V ⟶ X) (base' : T ⟶ X) (hb₀ : k ≫ base = base')
    (p : V ⟶ U i) (q : V ⟶ U j) [IsOpenImmersion k] [IsOpenImmersion p] [IsOpenImmersion q]
    (hp : p ≫ f i = base) (hq : q ≫ f j = base)
    (a : T ⟶ U i) (b : T ⟶ U j) [IsOpenImmersion a] [IsOpenImmersion b]
    (ha : k ≫ p = a) (hb : k ≫ q = b)
    (ha' : a ≫ f i = base') (hb' : b ≫ f j = base') :
    openDataRestrictIso data base' a b ha' hb' =
      ((restrictFunctorCongr ha).symm ≪≫ restrictFunctorComp k p).app (data.obj i).obj ≪≫
      (restrictFunctor k).mapIso (openDataRestrictIso data base p q hp hq) ≪≫
      (((restrictFunctorCongr hb).symm ≪≫ restrictFunctorComp k q).app (data.obj j).obj).symm := by
  let I := (quasiCoherentModulesProperty.prop (.mk (op T))).ι
  let P := (data.obj i).obj
  let Q := (data.obj j).obj
  let φ := data.hom base p q hp hq
  let lhs := data.hom base' a b ha' hb'
  let rhs := pullHom φ k a b ha hb
  have pull : lhs = rhs := (data.pullHom_hom k base base' hb₀ p q hp hq a b ha hb).symm
  let haIso := (restrictFunctorIsoPullback a).app P
  let hbIso := (restrictFunctorIsoPullback b).app Q
  let ca := (restrictFunctorComp k p).app P
  let cb := (restrictFunctorComp k q).app Q
  let ga := (restrictFunctorCongr ha).app P
  let gb := (restrictFunctorCongr hb).app Q
  let RF := restrictFunctor k
  let t := (openDataRestrictIso data base p q hp hq).hom
  have ok : haIso.hom ≫ I.map rhs ≫ hbIso.inv = ga.inv ≫ ca.hom ≫ RF.map t ≫ cb.inv ≫ gb.hom :=
    openRestriction_pullHom k p q φ a b ha hb
  have left : (openDataRestrictIso data base' a b ha' hb').hom =
      haIso.hom ≫ I.map lhs ≫ hbIso.inv :=
    openDataRestrictIso_hom data base' a b ha' hb'
  have mapped : I.map lhs = I.map rhs :=
    congrArg I.map pull
  have mid : haIso.hom ≫ I.map lhs ≫ hbIso.inv = haIso.hom ≫ I.map rhs ≫ hbIso.inv :=
    congrArg (fun m : (pullback a).obj P ⟶ (pullback b).obj Q => haIso.hom ≫ m ≫ hbIso.inv) mapped
  let z₁ := ((restrictFunctorCongr ha).symm ≪≫ restrictFunctorComp k p).app P
  let z₂ := RF.mapIso (openDataRestrictIso data base p q hp hq)
  let z₃ := ((restrictFunctorCongr hb).symm ≪≫ restrictFunctorComp k q).app Q
  have hom₁ : z₁.hom = ga.inv ≫ ca.hom := rfl
  have hom₂ : z₂.hom = RF.map t := rfl
  have inv₃ : z₃.inv = cb.inv ≫ gb.hom := rfl
  have right : (z₁ ≪≫ z₂ ≪≫ z₃.symm).hom =
      ga.inv ≫ ca.hom ≫ RF.map t ≫ cb.inv ≫ gb.hom := by
    rw [Iso.trans_hom, Iso.trans_hom, Iso.symm_hom, hom₁, hom₂, inv₃, Category.assoc]
  have out : (openDataRestrictIso data base' a b ha' hb').hom = (z₁ ≪≫ z₂ ≪≫ z₃.symm).hom :=
    left.trans (mid.trans (ok.trans right.symm))
  exact Iso.ext out

end

end SHIGURE.SchemeDescent
