import Formal.SHIGURE.Part2.Schemes.OpenCanonicalComparison
import Formal.SHIGURE.Part2.Schemes.OpenGluingChartTransition
import Formal.SHIGURE.Part2.Schemes.OpenDescentMorphisms

/-! # Descent of quasi-coherent module maps over open charts -/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Pseudofunctor Opposite Scheme.Modules

noncomputable section

universe u

private abbrev Q := quasiCoherentModulesPseudofunctor
variable {D : Scheme.GlueData.{u}} {M N : Q.obj (.mk (op D.glued))}
  (φ : (Q.toDescentData D.ι).obj M ⟶ (Q.toDescentData D.ι).obj N)

private def chartRestrictionMap (i : D.J) :
    M.obj.restrict (D.ι i) ⟶ N.obj.restrict (D.ι i) :=
  (restrictFunctorIsoPullback (D.ι i)).hom.app M.obj ≫
    (quasiCoherentModulesProperty.prop (.mk (op (D.U i)))).ι.map (φ.hom i) ≫
    (restrictFunctorIsoPullback (D.ι i)).inv.app N.obj

private theorem restrict_morphism_square {C : Type*} [Category C]
    {X X' Y Y' U U' V V' : C}
    (a : X ≅ X') (b : Y ≅ Y') (c : U ≅ U') (d : V ≅ V')
    (t₁ : X ⟶ Y) (t₂ : U ⟶ V) (s₁ : X' ⟶ Y') (s₂ : U' ⟶ V')
    (m : X' ⟶ U') (n : Y' ⟶ V')
    (h₁ : a.hom ≫ s₁ = t₁ ≫ b.hom) (h₂ : c.hom ≫ s₂ = t₂ ≫ d.hom)
    (comm : m ≫ s₂ = s₁ ≫ n) :
    (a.hom ≫ m ≫ c.inv) ≫ t₂ = t₁ ≫ b.hom ≫ n ≫ d.inv := by
  have inv : c.inv ≫ t₂ = s₂ ≫ d.inv := by
    apply (cancel_epi c.hom).1
    rw [Iso.hom_inv_id_assoc, ← Category.assoc c.hom, h₂,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]
  simp only [Category.assoc, inv]
  rw [← Category.assoc m, comm, Category.assoc, ← Category.assoc a.hom, h₁, Category.assoc]

set_option maxHeartbeats 425000 in
private theorem chartRestrictionMap_comm (i j : D.J) :
    (restrictFunctor (D.f i j)).map (chartRestrictionMap φ i) ≫
      ((ModuleGluingData.ofModule N.obj).transition i j).hom =
    ((ModuleGluingData.ofModule M.obj).transition i j).hom ≫
      (restrictFunctor (overlapRight D i j)).map (chartRestrictionMap φ j) := by
  let p := D.f i j
  let q := overlapRight D i j
  let base := p ≫ D.ι i
  have base' : q ≫ D.ι j = base := overlapRight_comp_chart D i j
  let A := restrictFunctor p
  let B := restrictFunctor q
  let compM := (openDataRestrictIso ((Q.toDescentData D.ι).obj M) base p q rfl base').hom
  let compN := (openDataRestrictIso ((Q.toDescentData D.ι).obj N) base p q rfl base').hom
  let tM := ((ModuleGluingData.ofModule M.obj).transition i j).hom
  let tN := ((ModuleGluingData.ofModule N.obj).transition i j).hom
  let aM := (restrictFunctorIsoPullback (D.ι i)).app M.obj
  let aN := (restrictFunctorIsoPullback (D.ι i)).app N.obj
  let bM := (restrictFunctorIsoPullback (D.ι j)).app M.obj
  let bN := (restrictFunctorIsoPullback (D.ι j)).app N.obj
  let m := (quasiCoherentModulesProperty.prop (.mk (op (D.U i)))).ι.map (φ.hom i)
  let n := (quasiCoherentModulesProperty.prop (.mk (op (D.U j)))).ι.map (φ.hom j)
  have left : A.map aM.hom ≫ compM = tM ≫ B.map bM.hom :=
    openCanonicalComparison (f := D.ι) i j p q base'.symm M
  have right : A.map aN.hom ≫ compN = tN ≫ B.map bN.hom :=
    openCanonicalComparison (f := D.ι) i j p q base'.symm N
  have compare : A.map m ≫ compN = compM ≫ B.map n :=
    (openDescentHom_comm_iff (D₁ := (Q.toDescentData D.ι).obj M) (D₂ := (Q.toDescentData D.ι).obj N)
      base p q rfl base' (φ.hom i) (φ.hom j)).1 (φ.comm base p q rfl base')
  have l : A.map (chartRestrictionMap φ i) =
      (A.mapIso aM).hom ≫ A.map m ≫ (A.mapIso aN).inv := by
    change A.map (aM.hom ≫ m ≫ aN.inv) = A.map aM.hom ≫ A.map m ≫ A.map aN.inv
    rw [A.map_comp, A.map_comp]
  have r : B.map (chartRestrictionMap φ j) =
      (B.mapIso bM).hom ≫ B.map n ≫ (B.mapIso bN).inv := by
    change B.map (bM.hom ≫ n ≫ bN.inv) = B.map bM.hom ≫ B.map n ≫ B.map bN.inv
    rw [B.map_comp, B.map_comp]
  rw [l, r]
  exact restrict_morphism_square (A.mapIso aM) (B.mapIso bM) (A.mapIso aN) (B.mapIso bN)
    tM tN compM compN (A.map m) (B.map n) left right compare

private def openGluedHom : M ⟶ N :=
  ObjectProperty.homMk
    (ModuleGluingData.glueGlobalMap
      { map := chartRestrictionMap φ
        naturality := chartRestrictionMap_comm φ })

set_option maxHeartbeats 750000 in
private theorem openGluedHom_map :
    (Q.toDescentData D.ι).map (openGluedHom φ) = φ := by
  apply DescentData.hom_ext
  intro i
  let I := (quasiCoherentModulesProperty.prop (.mk (op (D.U i)))).ι
  let J := (quasiCoherentModulesProperty.prop (.mk (op D.glued))).ι
  let R := restrictFunctor (D.ι i)
  let P := pullback (D.ι i)
  let e := restrictFunctorIsoPullback (D.ι i)
  let m := J.map (openGluedHom φ)
  let chart := I.map (φ.hom i)
  apply I.map_injective
  change P.map m = chart
  have lifted : R.map m = chartRestrictionMap φ i :=
    ModuleGluingData.glueGlobalMap_chart
      { map := chartRestrictionMap φ
        naturality := chartRestrictionMap_comm φ } i
  have natural : R.map m ≫ e.hom.app N.obj = e.hom.app M.obj ≫ P.map m :=
    e.hom.naturality m
  rw [lifted] at natural
  have same : (e.app M.obj).hom ≫ chart ≫ (e.app N.obj).inv ≫ (e.app N.obj).hom =
      (e.app M.obj).hom ≫ P.map m := by
    change (chartRestrictionMap φ i) ≫ (e.hom.app N.obj) = _
    exact natural
  exact ((cancel_epi (e.app M.obj).hom).1 (by
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using same)).symm

set_option maxHeartbeats 800000 in
private theorem openGluedHom_faithful (M N : Q.obj (.mk (op D.glued)))
    {m n : M ⟶ N} (same : (Q.toDescentData D.ι).map m = (Q.toDescentData D.ι).map n) : m = n := by
  let J := (quasiCoherentModulesProperty.prop (.mk (op D.glued))).ι
  apply J.map_injective
  apply ModuleGluingData.hom_ext_of_restrictCharts
  intro i
  let I := (quasiCoherentModulesProperty.prop (.mk (op (D.U i)))).ι
  let e := restrictFunctorIsoPullback (D.ι i)
  have chart := congrArg (fun h : (Q.toDescentData D.ι).obj M ⟶ (Q.toDescentData D.ι).obj N =>
    I.map (h.hom i)) same
  have equal : (pullback (D.ι i)).map (J.map m) = (pullback (D.ι i)).map (J.map n) := chart
  apply (cancel_mono (e.hom.app N.obj)).1
  let R := restrictFunctor (D.ι i)
  let P := pullback (D.ι i)
  have mNatural : R.map (J.map m) ≫ e.hom.app N.obj = e.hom.app M.obj ≫ P.map (J.map m) :=
    e.hom.naturality (J.map m)
  have nNatural : R.map (J.map n) ≫ e.hom.app N.obj = e.hom.app M.obj ≫ P.map (J.map n) :=
    e.hom.naturality (J.map n)
  exact mNatural.trans ((congrArg (e.hom.app M.obj ≫ ·) equal).trans nNatural.symm)

/-- The ordinary chart gluing recovers all maps of quasi-coherent modules. -/
def openGlueComparison_fullyFaithful (D : Scheme.GlueData.{u}) :
    (Q.toDescentData D.ι).FullyFaithful where
  preimage := openGluedHom
  map_preimage := openGluedHom_map
  preimage_map := fun m => openGluedHom_faithful _ _ (openGluedHom_map ((Q.toDescentData D.ι).map m))

end

end SHIGURE.SchemeDescent
