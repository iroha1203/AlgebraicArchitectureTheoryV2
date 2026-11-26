import Formal.SHIGURE.Part2.Schemes.RelativeSpecSheaves
import Mathlib.Topology.Sheaves.Skyscraper

/-! # Stalks of inverse images of commutative ring sheaves -/

namespace SHIGURE.SchemeDescent

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open TopCat

noncomputable section

universe u

variable {S T : TopCat.{u}}

/-- The stalk functor of commutative ring sheaves. -/
abbrev ringSheafStalk (x : S) : S.Sheaf CommRingCat.{u} ⥤ CommRingCat.{u} :=
  Sheaf.forget CommRingCat S ⋙ Presheaf.stalkFunctor CommRingCat x

private theorem sheafification_stalk_isIso (P : S.Presheaf CommRingCat) (x : S) :
    IsIso ((Presheaf.stalkFunctor CommRingCat x).map (toSheafify (Opens.grothendieckTopology S) P)) := by
  classical
  let a := sheafificationAdjunction (Opens.grothendieckTopology S) CommRingCat
  let b := stalkSkyscraperSheafAdjunction (C := CommRingCat) x
  let c := skyscraperPresheafStalkAdjunction (C := CommRingCat) x
  let e := c.leftAdjointUniq (a.comp b)
  have eq : e.hom.app P =
      (Presheaf.stalkFunctor CommRingCat x).map (toSheafify (Opens.grothendieckTopology S) P) := by
    apply (c.homEquiv _ _).injective
    rw [Adjunction.homEquiv_leftAdjointUniq_hom_app, Adjunction.homEquiv_apply, Adjunction.comp_unit_app]
    exact c.unit.naturality (a.unit.app P)
  rw [← eq]
  infer_instance

private theorem stalkPushforward_naturality (g : T ⟶ S)
    {F G : T.Presheaf CommRingCat} (a : F ⟶ G) (y : T) :
    (Presheaf.stalkFunctor CommRingCat (g y)).map ((Presheaf.pushforward CommRingCat g).map a) ≫
        G.stalkPushforward CommRingCat g y =
      F.stalkPushforward CommRingCat g y ≫ (Presheaf.stalkFunctor CommRingCat y).map a := by
  apply Presheaf.stalk_hom_ext
  intro U hx
  simp only [Presheaf.stalkFunctor_map_germ_assoc, Presheaf.stalkPushforward_germ,
    Presheaf.stalkPushforward_germ_assoc, Presheaf.stalkFunctor_map_germ]
  rfl

/-- Send a germ in the base sheaf to its germ in the inverse image. -/
def inverseImageStalkHom (g : T ⟶ S) (F : S.Sheaf CommRingCat.{u}) (y : T) :
    (ringSheafStalk (g y)).obj F ⟶ (ringSheafStalk y).obj ((Sheaf.pullback CommRingCat g).obj F) :=
  let P : T.Presheaf CommRingCat := ((Sheaf.pullback CommRingCat g).obj F).val
  (ringSheafStalk (g y)).map ((Sheaf.pullbackPushforwardAdjunction CommRingCat g).unit.app F) ≫
    P.stalkPushforward CommRingCat g y

/-- Inverse image preserves the stalk at the corresponding point. -/
theorem inverseImageStalkHom_isIso (g : T ⟶ S) (F : S.Sheaf CommRingCat.{u}) (y : T) :
    IsIso (inverseImageStalkHom g F y) := by
  let A := Presheaf.pushforwardPullbackAdjunction CommRingCat g
  let J := Opens.grothendieckTopology S
  let K := Opens.grothendieckTopology T
  let B := sheafificationAdjunction K CommRingCat
  let E := Sheaf.pullbackIso CommRingCat g
  let P := (Presheaf.pullback CommRingCat g).obj F.val
  have homUnit :
      ((Sheaf.pullbackPushforwardAdjunction CommRingCat g).unit.app F).val ≫
        (Presheaf.pushforward CommRingCat g).map (E.hom.app F).val =
      A.unit.app F.val ≫ (Presheaf.pushforward CommRingCat g).map (B.unit.app P) := by
    let constructed := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (Opens.map g) CommRingCat J K
    have compare := Adjunction.unit_leftAdjointUniq_hom_app
      (Sheaf.pullbackPushforwardAdjunction CommRingCat g) constructed F
    have unit : ((Sheaf.pullbackPushforwardAdjunction CommRingCat g).unit.app F).val ≫
        (Presheaf.pushforward CommRingCat g).map (E.hom.app F).val =
        (constructed.unit.app F).val :=
      congrArg CategoryTheory.Sheaf.Hom.val compare
    rw [unit]
    change (sheafToPresheaf J CommRingCat).map (constructed.unit.app F) = _
    unfold constructed Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    rw [Adjunction.map_restrictFullyFaithful_unit_app, Adjunction.comp_unit_app]
    simp only [Iso.refl_hom, NatTrans.id_app]
    rfl
  have composition :
      inverseImageStalkHom g F y ≫ (ringSheafStalk y).map (E.hom.app F) =
        (Presheaf.stalkPullbackIso CommRingCat g F.val y).hom ≫
          (Presheaf.stalkFunctor CommRingCat y).map (B.unit.app P) := by
    unfold inverseImageStalkHom
    change ((Presheaf.stalkFunctor CommRingCat (g y)).map
      ((Sheaf.pullbackPushforwardAdjunction CommRingCat g).unit.app F).val ≫ _) ≫
        (Presheaf.stalkFunctor CommRingCat y).map (E.hom.app F).val = _
    simp only [Category.assoc]
    rw [← stalkPushforward_naturality g (E.hom.app F).val y, ← Functor.map_comp_assoc, homUnit,
      Functor.map_comp, Category.assoc]
    exact (congrArg ((Presheaf.stalkFunctor CommRingCat (g y)).map (A.unit.app F.val) ≫ ·)
      (stalkPushforward_naturality g (B.unit.app P) y)).trans (Category.assoc _ _ _).symm
  haveI : IsIso ((Presheaf.stalkFunctor CommRingCat y).map (B.unit.app P)) :=
    sheafification_stalk_isIso P y
  haveI : IsIso (inverseImageStalkHom g F y ≫ (ringSheafStalk y).map (E.hom.app F)) :=
    composition ▸ inferInstance
  exact IsIso.of_isIso_comp_right _ ((ringSheafStalk y).map (E.hom.app F))

/-- Stalks preserve pushouts of commutative ring sheaves. -/
instance ringSheafStalk_isLeftAdjoint (x : S) : (ringSheafStalk x).IsLeftAdjoint := by
  classical
  exact (stalkSkyscraperSheafAdjunction (C := CommRingCat) x).isLeftAdjoint

/-- Take the stalk map adjoint to a map into direct-image functions. -/
def directImageStalkMap (g : T ⟶ S) {F : S.Sheaf CommRingCat.{u}} {G : T.Sheaf CommRingCat.{u}}
    (a : F ⟶ (Sheaf.pushforward CommRingCat g).obj G) (y : T) :
    (ringSheafStalk (g y)).obj F ⟶ (ringSheafStalk y).obj G :=
  (ringSheafStalk (g y)).map a ≫ Presheaf.stalkPushforward CommRingCat g G.val y

@[reassoc]
theorem germ_directImageStalkMap (g : T ⟶ S)
    {F : S.Sheaf CommRingCat.{u}} {G : T.Sheaf CommRingCat.{u}}
    (a : F ⟶ (Sheaf.pushforward CommRingCat g).obj G) (y : T) (U : Opens S) (inside : g y ∈ U) :
    Presheaf.germ F.val U (g y) inside ≫ directImageStalkMap g a y =
      a.val.app (.op U) ≫ Presheaf.germ G.val ((Opens.map g).obj U) y inside := by
  change _ ≫ ((Presheaf.stalkFunctor CommRingCat (g y)).map a.val ≫ _) = _
  rw [Presheaf.stalkFunctor_map_germ_assoc]
  exact congrArg (a.val.app (.op U) ≫ ·)
    (Presheaf.stalkPushforward_germ CommRingCat g G.val U y inside)

/-- The adjoint sheaf map acts on germs by the map into its direct image. -/
theorem inverseImageStalkHom_mate (g : T ⟶ S)
    {F : S.Sheaf CommRingCat.{u}} {G : T.Sheaf CommRingCat.{u}}
    (a : F ⟶ (Sheaf.pushforward CommRingCat g).obj G) (y : T) :
    let adj := Sheaf.pullbackPushforwardAdjunction CommRingCat g
    inverseImageStalkHom g F y ≫ (ringSheafStalk y).map ((adj.homEquiv F G).symm a) =
      directImageStalkMap g a y := by
  let adj := Sheaf.pullbackPushforwardAdjunction CommRingCat g
  let b := (adj.homEquiv F G).symm a
  change ((Presheaf.stalkFunctor CommRingCat (g y)).map (adj.unit.app F).val ≫ _) ≫
        (Presheaf.stalkFunctor CommRingCat y).map b.val =
    (Presheaf.stalkFunctor CommRingCat (g y)).map a.val ≫ _
  have mate : (adj.unit.app F).val ≫ (Presheaf.pushforward CommRingCat g).map b.val = a.val := by
    have eq : adj.unit.app F ≫ (Sheaf.pushforward CommRingCat g).map b = a := by
      exact (adj.homEquiv_apply F G b).symm.trans (Equiv.apply_symm_apply (adj.homEquiv F G) a)
    exact congrArg CategoryTheory.Sheaf.Hom.val eq
  rw [Category.assoc, ← stalkPushforward_naturality g b.val, ← Functor.map_comp_assoc, mate]

/-- The identification of stalks with those of the inverse image respects maps of sheaves. -/
@[reassoc]
theorem inverseImageStalkHom_naturality (g : T ⟶ S) {F G : S.Sheaf CommRingCat.{u}}
    (a : F ⟶ G) (y : T) :
    (ringSheafStalk (g y)).map a ≫ inverseImageStalkHom g G y =
      inverseImageStalkHom g F y ≫ (ringSheafStalk y).map ((Sheaf.pullback CommRingCat g).map a) := by
  let adj := Sheaf.pullbackPushforwardAdjunction CommRingCat g
  let SX := Presheaf.stalkFunctor CommRingCat (g y)
  let SY := Presheaf.stalkFunctor CommRingCat y
  let b := (Sheaf.pullback CommRingCat g).map a
  change SX.map a.val ≫ (SX.map (adj.unit.app G).val ≫ _) =
    (SX.map (adj.unit.app F).val ≫ _) ≫ SY.map b.val
  have natural :
      a.val ≫ (adj.unit.app G).val =
        (adj.unit.app F).val ≫ (Presheaf.pushforward CommRingCat g).map b.val :=
    congrArg CategoryTheory.Sheaf.Hom.val (adj.unit.naturality a)
  rw [Category.assoc, ← stalkPushforward_naturality g b.val, ← Functor.map_comp_assoc,
    ← Functor.map_comp_assoc, natural]

end

end SHIGURE.SchemeDescent
