import Formal.SHIGURE.Part2.Realizations.CoordinateModulePullback
import Formal.SHIGURE.Part2.Realizations.CoordinateModuleMatrix

/-! # The actual basis maps commute with pullback of coordinate sheaves -/

namespace SHIGURE.RealizationFamilies

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

noncomputable section

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)

private abbrev termModule (T : Scheme.{u}) : T.Modules := SheafOfModules.unit T.ringCatSheaf

private abbrev unitComparison :
    (Scheme.Modules.pullback f).obj (termModule Y) ⟶ termModule X :=
  SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom

/-- Pulling back the original coordinate projection agrees with taking the
projection from the standard free module on the new scheme. -/
theorem coordinateModulePullbackIso_projection (i : Fin n) :
    (coordinateModulePullbackIso f n).hom ≫ Pi.π (fun _ : Fin n => termModule X) i =
      (Scheme.Modules.pullback f).map (Pi.π (fun _ : Fin n => termModule Y) i) ≫ unitComparison f := by
  unfold coordinateModulePullbackIso
  rw [Iso.trans_hom, Category.assoc]
  change (PreservesProduct.iso (Scheme.Modules.pullback f) (fun _ : Fin n => termModule Y)).hom ≫
    CategoryTheory.Limits.Pi.map (f := fun _ : Fin n => (Scheme.Modules.pullback f).obj (termModule Y))
      (g := fun _ : Fin n => termModule X) (fun _ => unitComparison f) ≫ Pi.π (fun _ : Fin n => termModule X) i = _
  rw [Pi.map_π, ← Category.assoc, PreservesProduct.iso_hom, piComparison_comp_π]

open Classical in
/-- The basis vector is the original unit sheaf included in the specified
coordinate of the finite product. -/
def coordinateModuleBasisMap (T : Scheme.{u}) (j : Fin n) : termModule T ⟶ coordinateModuleSheaf T n :=
  Pi.lift (fun i : Fin n => if i = j then 𝟙 (termModule T) else 0)

open Classical in
/-- The sheaf basis map gives the unit in its coordinate and zero in the others. -/
theorem coordinateModuleBasisMap_projection (T : Scheme.{u}) (i j : Fin n) :
    coordinateModuleBasisMap n T j ≫ Pi.π (fun _ : Fin n => termModule T) i =
      if i = j then 𝟙 (termModule T) else 0 :=
  Pi.lift_π _ _

/-- The actual pulled-back basis vector is the one in the same position on the new scheme. -/
theorem coordinateModulePullbackIso_basis (j : Fin n) :
    (Scheme.Modules.pullback f).map (coordinateModuleBasisMap n Y j) ≫ (coordinateModulePullbackIso f n).hom =
      unitComparison f ≫ coordinateModuleBasisMap n X j := by
  classical
  apply Pi.hom_ext
  intro i
  let L := Scheme.Modules.pullback f
  have projections := coordinateModulePullbackIso_projection f n i
  change L.map (coordinateModuleBasisMap n Y j) ≫ (coordinateModulePullbackIso f n).hom ≫
      Pi.π (fun _ : Fin n => termModule X) i =
    unitComparison f ≫ coordinateModuleBasisMap n X j ≫ Pi.π (fun _ : Fin n => termModule X) i
  rw [projections, ← Category.assoc, ← L.map_comp,
    coordinateModuleBasisMap_projection, coordinateModuleBasisMap_projection]
  by_cases same : i = j
  · simp only [same, if_true, L.map_id, Category.id_comp, Category.comp_id]
  · simp only [if_neg same, L.map_zero, Limits.zero_comp, Limits.comp_zero]

private theorem preimageFinalForUnit : (Opens.map f.base).Final := by
  apply Functor.final_of_exists_of_isFiltered
  · intro U
    exact ⟨⊤, ⟨homOfLE (by simp)⟩⟩
  · intro U V a b
    exact ⟨V, 𝟙 V, congrArg (· ≫ (Opens.map f.base).map (𝟙 V)) (Subsingleton.elim a b)⟩

/-- The actual pullback of the unit module is the unit module, through the
same adjunction comparison used in the coordinate pullback. -/
def schemeUnitPullbackIso : (Scheme.Modules.pullback f).obj (termModule Y) ≅ termModule X := by
  letI : (Opens.map f.base).Final := preimageFinalForUnit f
  letI : (SheafOfModules.pushforward.{u} f.toRingCatSheafHom).IsRightAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction f).isRightAdjoint
  letI : IsIso (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) :=
    SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal f.toRingCatSheafHom
  exact asIso (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom)

/-- An endomorphism of the original unit module pulls its global
coefficient along the original map of structure rings. -/
theorem pullbackUnitMap_coefficient (a : termModule Y ⟶ termModule Y) :
    (((schemeUnitPullbackIso f).inv ≫ (Scheme.Modules.pullback f).map a ≫
      (schemeUnitPullbackIso f).hom).val.app (op (⊤ : X.Opens))) (1 : Γ(X, ⊤)) =
      f.appTop.hom (a.val.app (op (⊤ : Y.Opens)) (1 : Γ(Y, ⊤))) := by
  let L := Scheme.Modules.pullback f
  let P := Scheme.Modules.pushforward f
  let c := schemeUnitPullbackIso f
  let adj := Scheme.Modules.pullbackPushforwardAdjunction f
  let h := c.inv ≫ L.map a ≫ c.hom
  let m := SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom
  have compare : c.hom ≫ h = L.map a ≫ c.hom := by
    dsimp only [h]
    rw [Iso.hom_inv_id_assoc]
  have direct : adj.homEquiv _ _ c.hom = m :=
    SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit f.toRingCatSheafHom
  have commute : m ≫ P.map h = a ≫ m := by
    calc
      _ = adj.homEquiv _ _ (c.hom ≫ h) := by
        rw [adj.homEquiv_naturality_right, direct]
      _ = adj.homEquiv _ _ (L.map a ≫ c.hom) := congrArg (adj.homEquiv _ _) compare
      _ = _ := by rw [adj.homEquiv_naturality_left, direct]
  have globalValue := congrArg (fun μ => μ.val.app (op (⊤ : Y.Opens)) (1 : Γ(Y, ⊤))) commute
  change h.val.app (op (⊤ : X.Opens)) (f.appTop.hom 1) =
    f.appTop.hom (a.val.app (op (⊤ : Y.Opens)) (1 : Γ(Y, ⊤))) at globalValue
  rw [map_one] at globalValue
  exact globalValue

/-- The adjoint of the canonical pullback comparison applies the actual
structure-ring map to every coordinate of a global section. -/
theorem coordinateAdjunct_top_apply
    (x : (coordinateModuleSheaf Y n).val.obj (op (⊤ : Y.Opens))) (i : Fin n) :
    (coordinateModuleSectionIso X n (op (⊤ : X.Opens))).hom
      (((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _
        (coordinateModulePullbackIso f n).hom).val.app (op (⊤ : Y.Opens)) x) i =
    f.appTop.hom ((coordinateModuleSectionIso Y n (op (⊤ : Y.Opens))).hom x i) := by
  let b := coordinateModulePullbackIso f n
  let L := Scheme.Modules.pullback f
  let P := Scheme.Modules.pushforward f
  let adj := Scheme.Modules.pullbackPushforwardAdjunction f
  let c := schemeUnitPullbackIso f
  let m := SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom
  let π₀ := Pi.π (fun _ : Fin n => termModule Y) i
  let π₁ := Pi.π (fun _ : Fin n => termModule X) i
  have direct : adj.homEquiv _ _ c.hom = m :=
    SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit f.toRingCatSheafHom
  have proj : b.hom ≫ π₁ = L.map π₀ ≫ c.hom := coordinateModulePullbackIso_projection f n i
  have commute : adj.homEquiv _ _ b.hom ≫ P.map π₁ = π₀ ≫ m := by
    calc
      _ = adj.homEquiv _ _ (b.hom ≫ π₁) := (adj.homEquiv_naturality_right _ _).symm
      _ = adj.homEquiv _ _ (L.map π₀ ≫ c.hom) := congrArg (adj.homEquiv _ _) proj
      _ = _ := by rw [adj.homEquiv_naturality_left, direct]
  rw [coordinateModuleSectionIso_apply X n, coordinateModuleSectionIso_apply Y n]
  exact congrArg (fun v => v.val.app (op (⊤ : Y.Opens)) x) commute

end

end SHIGURE.RealizationFamilies
