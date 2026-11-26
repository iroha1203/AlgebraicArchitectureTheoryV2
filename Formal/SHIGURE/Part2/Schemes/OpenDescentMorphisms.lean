import Formal.SHIGURE.Part2.Schemes.OpenDataRestriction

/-! # Morphisms of open-cover descent data under ordinary restriction -/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory Opposite Scheme.Modules

noncomputable section

universe u

variable {ι : Type u} {X T : Scheme.{u}} {U : ι → Scheme.{u}} {f : ∀ i, U i ⟶ X}
  {D₁ D₂ : quasiCoherentModulesPseudofunctor.DescentData f} {i j : ι}
  (base : T ⟶ X) (p : T ⟶ U i) (q : T ⟶ U j) [IsOpenImmersion p] [IsOpenImmersion q]
  (hp : p ≫ f i = base) (hq : q ≫ f j = base)
  (a : D₁.obj i ⟶ D₂.obj i) (b : D₁.obj j ⟶ D₂.obj j)

set_option maxHeartbeats 750000 in
/-- Open-overlap compatibility of module maps can be checked using ordinary
restriction, while the original descent category uses pseudofunctor pullback. -/
theorem openDescentHom_comm_iff :
    ((quasiCoherentModulesPseudofunctor.map p.op.toLoc).toFunctor.map a ≫ D₂.hom base p q hp hq =
      D₁.hom base p q hp hq ≫ (quasiCoherentModulesPseudofunctor.map q.op.toLoc).toFunctor.map b) ↔
    ((restrictFunctor p).map ((quasiCoherentModulesProperty.prop (.mk (op (U i)))).ι.map a) ≫
      (openDataRestrictIso D₂ base p q hp hq).hom =
      (openDataRestrictIso D₁ base p q hp hq).hom ≫
        (restrictFunctor q).map ((quasiCoherentModulesProperty.prop (.mk (op (U j)))).ι.map b)) := by
  let I := (quasiCoherentModulesProperty.prop (.mk (op T))).ι
  let m := (quasiCoherentModulesProperty.prop (.mk (op (U i)))).ι.map a
  let n := (quasiCoherentModulesProperty.prop (.mk (op (U j)))).ι.map b
  let δ₁ := I.map (D₁.hom base p q hp hq)
  let δ₂ := I.map (D₂.hom base p q hp hq)
  let P := restrictFunctorIsoPullback p
  let Q := restrictFunctorIsoPullback q
  let lp₁ := P.app (D₁.obj i).obj
  let lp₂ := P.app (D₂.obj i).obj
  let rq₁ := Q.app (D₁.obj j).obj
  let rq₂ := Q.app (D₂.obj j).obj
  let ma := (quasiCoherentModulesPseudofunctor.map p.op.toLoc).toFunctor.map a
  let nb := (quasiCoherentModulesPseudofunctor.map q.op.toLoc).toFunctor.map b
  have left : (restrictFunctor p).map m ≫ lp₂.hom = lp₁.hom ≫ I.map ma := P.hom.naturality m
  have right : rq₁.inv ≫ (restrictFunctor q).map n = I.map nb ≫ rq₂.inv := (Q.inv.naturality n).symm
  have leftAssoc : ∀ Z (z : (pullback p).obj (D₂.obj i).obj ⟶ Z),
      (restrictFunctor p).map m ≫ lp₂.hom ≫ z = lp₁.hom ≫ I.map ma ≫ z := by
    intro Z z
    rw [← Category.assoc, left, Category.assoc]
  have comp₁ : (openDataRestrictIso D₁ base p q hp hq).hom = lp₁.hom ≫ δ₁ ≫ rq₁.inv := rfl
  have comp₂ : (openDataRestrictIso D₂ base p q hp hq).hom = lp₂.hom ≫ δ₂ ≫ rq₂.inv := rfl
  change (ma ≫ D₂.hom base p q hp hq = D₁.hom base p q hp hq ≫ nb) ↔ _
  rw [comp₁, comp₂, leftAssoc, Category.assoc, Category.assoc, right]
  rw [← Category.assoc (I.map ma), ← Category.assoc δ₁]
  rw [← I.map_comp, ← I.map_comp]
  let x := ma ≫ D₂.hom base p q hp hq
  let y := D₁.hom base p q hp hq ≫ nb
  change x = y ↔ lp₁.hom ≫ I.map x ≫ rq₂.inv = lp₁.hom ≫ I.map y ≫ rq₂.inv
  constructor
  · intro h
    have mapped : I.map x = I.map y := congrArg I.map h
    exact congrArg (fun t : (pullback p).obj (D₁.obj i).obj ⟶ (pullback q).obj (D₂.obj j).obj =>
      lp₁.hom ≫ t ≫ rq₂.inv) mapped
  · intro h
    have app : I.map x ≫ rq₂.inv = I.map y ≫ rq₂.inv := (cancel_epi lp₁.hom).1 h
    have mapped : I.map x = I.map y := (cancel_mono rq₂.inv).1 app
    exact I.map_injective mapped

end

end SHIGURE.SchemeDescent
