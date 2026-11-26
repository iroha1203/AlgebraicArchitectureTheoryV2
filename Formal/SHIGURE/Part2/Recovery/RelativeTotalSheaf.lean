import Formal.SHIGURE.Part2.Recovery.RelativeSchemeMaps
import Mathlib.AlgebraicGeometry.Sites.Representability
import Mathlib.CategoryTheory.Limits.Types.Pullbacks

/-!
# A relative sheaf as an absolute sheaf over the base

A section consists of a map to the base and a section on that relative
test. Gluing first glues the map to the base, then glues the sections on
the resulting relative test.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

noncomputable section

namespace SHIGURE.Copying

variable {S : Scheme.{u}} (F : ZariskiSheaf S)

private abbrev TotalSection (X : Scheme.{u}) := Σ p : X ⟶ S, F.val.obj (op (Over.mk p))

private def sectionAs (T : Over S) (x : TotalSection F T.left) (h : x.1 = T.hom) :
    F.val.obj (op T) :=
  F.val.map (Over.homMk (𝟙 T.left) ((Category.id_comp _).trans h) :
    T ⟶ Over.mk x.1).op x.2

private def totalMk (T : Over S) (x : F.val.obj (op T)) : TotalSection F T.left :=
  ⟨T.hom, F.val.map (Over.homMk (𝟙 T.left) (Category.id_comp _) : Over.mk T.hom ⟶ T).op x⟩

private theorem sectionAs_totalMk (T : Over S) (x : F.val.obj (op T)) :
    sectionAs F T (totalMk F T x) rfl = x := by
  unfold sectionAs totalMk
  rw [← FunctorToTypes.map_comp_apply, ← op_comp]
  have he : (Over.homMk (𝟙 T.left) (Category.id_comp _) : T ⟶ Over.mk T.hom) ≫
      (Over.homMk (𝟙 T.left) (Category.id_comp _) : Over.mk T.hom ⟶ T) = 𝟙 T :=
    Over.OverMorphism.ext (Category.id_comp _)
  rw [he, op_id, FunctorToTypes.map_id_apply]

private theorem totalSection_ext {X : Scheme.{u}} (x y : TotalSection F X) (h : x.1 = y.1)
    (e : sectionAs F (Over.mk y.1) x h = y.2) : x = y := by
  obtain ⟨a, x⟩ := x
  obtain ⟨b, y⟩ := y
  change a = b at h
  subst b
  change F.val.map (Over.homMk (𝟙 X) _ : Over.mk a ⟶ Over.mk a).op x = y at e
  have hi : (Over.homMk (𝟙 X) (Category.id_comp _) : Over.mk a ⟶ Over.mk a) = 𝟙 _ :=
    Over.OverMorphism.ext rfl
  rw [hi, op_id, FunctorToTypes.map_id_apply] at e
  subst y
  rfl

private def totalMap {X Y : Scheme.{u}} (g : X ⟶ Y) (x : TotalSection F Y) : TotalSection F X :=
  ⟨g ≫ x.1, F.val.map (Over.homMk g : Over.mk (g ≫ x.1) ⟶ Over.mk x.1).op x.2⟩

private theorem sectionAs_totalMap {T U : Over S} (g : U ⟶ T) (x : TotalSection F T.left) (hx : x.1 = T.hom)
    (hy : (totalMap F g.left x).1 = U.hom) :
    sectionAs F U (totalMap F g.left x) hy = F.val.map g.op (sectionAs F T x hx) := by
  unfold sectionAs totalMap
  rw [← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply, ← op_comp, ← op_comp]
  congr 2

private theorem totalMk_sectionAs (T : Over S) (x : TotalSection F T.left) (h : x.1 = T.hom) :
    totalMk F T (sectionAs F T x h) = x := by
  apply totalSection_ext F _ _ h.symm
  unfold sectionAs totalMk
  rw [← FunctorToTypes.map_comp_apply, ← op_comp, ← FunctorToTypes.map_comp_apply, ← op_comp]
  have he : ((Over.homMk (𝟙 T.left) ((Category.id_comp _).trans h.symm) :
        Over.mk x.1 ⟶ Over.mk T.hom) ≫
      (Over.homMk (𝟙 T.left) (Category.id_comp _) : Over.mk T.hom ⟶ T)) ≫
      (Over.homMk (𝟙 T.left) ((Category.id_comp _).trans h) : T ⟶ Over.mk x.1) = 𝟙 _ := by
    apply Over.OverMorphism.ext
    change (𝟙 T.left ≫ 𝟙 T.left) ≫ 𝟙 T.left = 𝟙 T.left
    simp only [Category.id_comp]
  exact (congrArg (fun k : Over.mk x.1 ⟶ Over.mk x.1 => F.val.map k.op x.2) he).trans
    (by rw [op_id, FunctorToTypes.map_id_apply])

private theorem sectionAs_injective {T : Over S} {x y : TotalSection F T.left}
    (hx : x.1 = T.hom) (hy : y.1 = T.hom) (eq : sectionAs F T x hx = sectionAs F T y hy) : x = y := by
  rw [← totalMk_sectionAs F T x hx, ← totalMk_sectionAs F T y hy, eq]

/-- A section over an absolute test records the base map and its relative section. -/
def relativeTotalPresheaf : Scheme.{u}ᵒᵖ ⥤ Type u where
  obj T := TotalSection F T.unop
  map g := ↾totalMap F g.unop
  map_id T := by
    ext x : 1
    let U := Over.mk x.1
    change totalMap F (𝟙 T.unop) x = x
    have e := sectionAs_totalMap F (𝟙 U) x rfl (Category.id_comp x.1)
    rw [op_id, FunctorToTypes.map_id_apply] at e
    exact sectionAs_injective F (T := U) (Category.id_comp x.1) rfl e
  map_comp {X Y Z} f g := by
    ext x : 1
    let V := Over.mk x.1
    let U := Over.mk (f.unop ≫ x.1)
    let W := Over.mk (g.unop ≫ f.unop ≫ x.1)
    let a : U ⟶ V := Over.homMk f.unop
    let b : W ⟶ U := Over.homMk g.unop
    change totalMap F (g.unop ≫ f.unop) x = totalMap F g.unop (totalMap F f.unop x)
    apply sectionAs_injective F (T := W) (Category.assoc _ _ _) rfl
    have e := sectionAs_totalMap F (b ≫ a) x rfl (Category.assoc _ _ _)
    rw [op_comp, FunctorToTypes.map_comp_apply] at e
    exact e.trans ((congrArg (F.val.map b.op) (sectionAs_totalMap F a x rfl rfl).symm).trans
      (sectionAs_totalMap F b (totalMap F f.unop x) rfl rfl).symm)

/-- An absolute section has its canonical map to the base scheme. -/
def relativeTotalToBase : relativeTotalPresheaf F ⟶ yoneda.obj S where
  app _ := ↾Sigma.fst
  naturality _ _ _ := rfl

private theorem sectionAs_congr {T : Over S} {x y : TotalSection F T.left}
    (e : x = y) (hx : x.1 = T.hom) (hy : y.1 = T.hom) :
    sectionAs F T x hx = sectionAs F T y hy := by
  subst y
  rfl

/-- Relative sheaf sections glued with their base maps form an absolute Zariski sheaf. -/
def relativeTotalSheaf : Sheaf Scheme.zariskiTopology (Type u) where
  val := relativeTotalPresheaf F
  cond := by
    apply (isSheaf_iff_isSheaf_of_type _ _).mpr
    intro X R hR x compatible
    let base := x.map (relativeTotalToBase F)
    have compatibleBase : base.Compatible := compatible.map (relativeTotalToBase F)
    let hBase := (isSheaf_iff_isSheaf_of_type _ _).mp (Scheme.zariskiTopology.yoneda.obj S).cond R hR
    let p : X ⟶ S := hBase.amalgamate base compatibleBase
    let T := Over.mk p
    let Q := (Sieve.overEquiv T).symm R
    have hQ : Q ∈ (Scheme.zariskiTopology.over S) T :=
      Scheme.zariskiTopology.overEquiv_symm_mem_over T R hR
    let absolute {U : Over S} (g : U ⟶ T) (hg : Q g) : R g.left := (Sieve.overEquiv_symm_iff R g).mp hg
    have preservesBase {U : Over S} (g : U ⟶ T) (hg : Q g) : (x g.left (absolute g hg)).1 = U.hom :=
      (hBase.valid_glue compatibleBase g.left (absolute g hg)).symm.trans (Over.w g)
    let localSections : Presieve.FamilyOfElements F.val Q.arrows := fun U g hg =>
      sectionAs F U (x g.left (absolute g hg)) (preservesBase g hg)
    have localCompatible : localSections.Compatible := by
      intro U V W a b f g hf hg e
      let x₁ := x f.left (absolute f hf)
      let x₂ := x g.left (absolute g hg)
      have he := compatible a.left b.left (absolute f hf) (absolute g hg)
        (congrArg (fun t : W ⟶ T => t.left) e)
      change totalMap F a.left x₁ = totalMap F b.left x₂ at he
      change F.val.map a.op (sectionAs F U x₁ (preservesBase f hf)) =
        F.val.map b.op (sectionAs F V x₂ (preservesBase g hg))
      have ha : (totalMap F a.left x₁).1 = W.hom := by
        change a.left ≫ x₁.1 = W.hom
        rw [preservesBase f hf, Over.w a]
      have hb : (totalMap F b.left x₂).1 = W.hom := by
        change b.left ≫ x₂.1 = W.hom
        rw [preservesBase g hg, Over.w b]
      exact (sectionAs_totalMap F a x₁ (preservesBase f hf) ha).symm.trans
        ((sectionAs_congr F he ha hb).trans (sectionAs_totalMap F b x₂ (preservesBase g hg) hb))
    let hF := (isSheaf_iff_isSheaf_of_type _ _).mp F.cond Q hQ
    let glued := hF.amalgamate localSections localCompatible
    refine ⟨totalMk F T glued, ?_, ?_⟩
    · intro U g hg
      let V := Over.mk (g ≫ p)
      let v : V ⟶ T := Over.homMk g
      have hv : Q v := (Sieve.overEquiv_symm_iff R v).mpr hg
      change totalMap F v.left (totalMk F T glued) = x v.left (absolute v hv)
      apply sectionAs_injective F (T := V) rfl (preservesBase v hv)
      rw [sectionAs_totalMap F v (totalMk F T glued) rfl rfl, sectionAs_totalMk]
      exact hF.valid_glue localCompatible v hv
    · intro y hy
      have yBase : y.1 = p := by
        apply hBase.isSeparatedFor.ext
        intro U g hg
        have he := congrArg (fun z : TotalSection F U => z.1) (hy g hg)
        exact he.trans (hBase.valid_glue compatibleBase g hg).symm
      apply sectionAs_injective F (T := T) yBase rfl
      rw [sectionAs_totalMk]
      apply hF.isSeparatedFor.ext
      intro U g hg
      have hgy : (totalMap F g.left y).1 = U.hom := by
        change g.left ≫ y.1 = U.hom
        rw [yBase]
        exact Over.w g
      rw [← sectionAs_totalMap F g y yBase hgy, hF.valid_glue localCompatible g hg]
      exact sectionAs_congr F (hy g.left (absolute g hg)) hgy (preservesBase g hg)

private theorem totalMk_natural {T U : Over S} (g : U ⟶ T) (x : F.val.obj (op T)) :
    totalMap F g.left (totalMk F T x) = totalMk F U (F.val.map g.op x) := by
  apply sectionAs_injective F (T := U) (Over.w g) rfl
  rw [sectionAs_totalMap F g (totalMk F T x) rfl (Over.w g), sectionAs_totalMk, sectionAs_totalMk]

section LocalRepresentation

variable {U : Scheme.{u}} (f : U ⟶ S) (Y : Over U)
variable (e : (Scheme.zariskiTopology.overMapPullback (Type u) f).obj F ≅ relativePoints U Y)

private def chartRepresentationMap : yoneda.obj Y.left ⟶ relativeTotalPresheaf F :=
  yonedaEquiv.symm (totalMk F ((Over.map f).obj Y)
    (e.inv.val.app (op Y) ((relativePointsEquiv U Y Y).symm (𝟙 Y))))

private theorem chartRepresentationMap_app {T : Over U} (g : T ⟶ Y) :
    (chartRepresentationMap F f Y e).app (op T.left) g.left =
      totalMk F ((Over.map f).obj T) (e.inv.val.app (op T) ((relativePointsEquiv U T Y).symm g)) := by
  let y := (relativePointsEquiv U Y Y).symm (𝟙 Y)
  rw [chartRepresentationMap, yonedaEquiv_symm_app_apply]
  change totalMap F g.left (totalMk F ((Over.map f).obj Y) (e.inv.val.app (op Y) y)) = _
  refine (totalMk_natural F ((Over.map f).map g) (e.inv.val.app (op Y) y)).trans ?_
  apply congrArg (totalMk F ((Over.map f).obj T))
  have h := FunctorToTypes.naturality _ _ e.inv.val g.op y
  have hpt : (relativePoints U Y).val.map g.op y = (relativePointsEquiv U T Y).symm g := by
    apply Subtype.ext
    exact Category.comp_id _
  rw [hpt] at h
  exact h.symm

private theorem chartRepresentationMap_base {X : Scheme.{u}} (g : X ⟶ Y.left) :
    ((chartRepresentationMap F f Y e).app (op X) g).1 = (g ≫ Y.hom) ≫ f := by
  exact congrArg Sigma.fst (chartRepresentationMap_app F f Y e (Over.homMk g :
    Over.mk (g ≫ Y.hom) ⟶ Y))

private theorem chartRepresentationMap_pullback : IsPullback (chartRepresentationMap F f Y e) (yoneda.map Y.hom)
    (relativeTotalToBase F) (yoneda.map f) := by
  have w : chartRepresentationMap F f Y e ≫ relativeTotalToBase F = yoneda.map Y.hom ≫ yoneda.map f := by
    ext X g
    exact chartRepresentationMap_base F f Y e g
  apply IsPullback.of_isLimit' (⟨w⟩ : CommSq _ _ _ _)
  apply evaluationJointlyReflectsLimits
  intro X
  refine (isLimitMapConePullbackConeEquiv ((evaluation (Schemeᵒᵖ) (Type u)).obj X) w).symm ?_
  apply IsPullback.isLimit
  apply (Types.isPullback_iff _ _ _ _).mpr
  refine ⟨NatTrans.congr_app w X, ?_, ?_⟩
  · intro a b hab
    change (chartRepresentationMap F f Y e).app X a = (chartRepresentationMap F f Y e).app X b ∧
      a ≫ Y.hom = b ≫ Y.hom at hab
    let T : Over U := Over.mk (a ≫ Y.hom)
    let a' : T ⟶ Y := Over.homMk a
    let b' : T ⟶ Y := Over.homMk b hab.2.symm
    let x := (relativePointsEquiv U T Y).symm a'
    let y := (relativePointsEquiv U T Y).symm b'
    have h := ((chartRepresentationMap_app F f Y e a').symm.trans hab.1).trans
      (chartRepresentationMap_app F f Y e b')
    have h' := sectionAs_congr F (T := (Over.map f).obj T) h rfl rfl
    rw [sectionAs_totalMk, sectionAs_totalMk] at h'
    have hXY : x = y := (((sheafToPresheaf _ _).mapIso e.symm).app (op T)).toEquiv.injective h'
    exact congrArg Subtype.val hXY
  · intro x q hx
    change x.1 = q ≫ f at hx
    let T : Over U := Over.mk q
    let V := (Over.map f).obj T
    let y := sectionAs F V x hx
    let z := e.hom.val.app (op T) y
    let g := (relativePointsEquiv U T Y) z
    refine ⟨g.left, ?_, Over.w g⟩
    change (chartRepresentationMap F f Y e).app (op T.left) g.left = x
    rw [chartRepresentationMap_app, Equiv.symm_apply_apply]
    have he := (((sheafToPresheaf _ _).mapIso e).app (op T)).toEquiv.left_inv y
    change e.inv.val.app (op T) z = y at he
    rw [he, totalMk_sectionAs]

private theorem chartRepresentationMap_open [IsOpenImmersion f] :
    IsOpenImmersion.presheaf (chartRepresentationMap F f Y e) := by
  apply MorphismProperty.relative.of_exists
  intro X a
  obtain ⟨g, hg⟩ := yoneda.map_surjective (a ≫ relativeTotalToBase F)
  let p := pullback.fst g f
  let q := pullback.snd g f
  have hp : IsPullback (yoneda.map p) (yoneda.map q) (a ≫ relativeTotalToBase F) (yoneda.map f) := by
    rw [← hg]
    exact (IsPullback.of_hasPullback g f).map yoneda
  let square := chartRepresentationMap_pullback F f Y e
  have w : (yoneda.map p ≫ a) ≫ relativeTotalToBase F = yoneda.map q ≫ yoneda.map f := by
    rw [Category.assoc]
    exact hp.w
  let m := square.lift (yoneda.map p ≫ a) (yoneda.map q) w
  refine ⟨pullback g f, m, p, ?_, inferInstance⟩
  have hq : m ≫ yoneda.map Y.hom = yoneda.map q := square.lift_snd _ _ _
  have hm : yoneda.map p ≫ a = m ≫ chartRepresentationMap F f Y e := (square.lift_fst _ _ _).symm
  rw [← hq] at hp
  exact (hp.of_bot hm square).flip

end LocalRepresentation

/-- A relative sheaf is represented by a scheme equipped with its map to the base. -/
structure RelativeRepresentation where
  /-- The representing scheme over the coefficient scheme. -/
  space : Over S
  /-- Identify the sheaf with the relative points of this scheme. -/
  points : relativePoints S space ≅ F

private theorem chartRepresentation_locallySurjective (C : Scheme.OpenCover.{u} S)
    (models : ∀ i, RelativeRepresentation ((Scheme.zariskiTopology.overMapPullback (Type u) (C.f i)).obj F)) :
    Presheaf.IsLocallySurjective Scheme.zariskiTopology
      (Sigma.desc fun i => chartRepresentationMap F (C.f i) (models i).space (models i).points.symm) where
  imageSieve_mem {X} x := by
    let A := C.pullback₁ x.1
    let maps := fun i => chartRepresentationMap F (C.f i) (models i).space (models i).points.symm
    refine Scheme.mem_grothendieckTopology_iff.mpr ⟨A, ?_⟩
    rintro _ _ ⟨i⟩
    let W := A.X i
    let u := A.f i
    let v := C.pullbackHom x.1 i
    let x' := totalMap F u x
    let h := (chartRepresentationMap_pullback F (C.f i) (models i).space (models i).points.symm).map
      ((evaluation _ (Type u)).obj (op W))
    have hw : (relativeTotalToBase F).app (op W) x' = (yoneda.map (C.f i)).app (op W) v :=
      (C.pullbackHom_map x.1 i).symm
    obtain ⟨g, hg, _⟩ := Types.exists_of_isPullback h x' v hw
    refine ⟨(Sigma.ι (fun i => yoneda.obj (models i).space.left) i).app (op W) g, ?_⟩
    exact (congrArg (fun m : yoneda.obj (models i).space.left ⟶ relativeTotalPresheaf F => m.app (op W) g)
      (Sigma.ι_desc maps i)).trans hg

private def representationOfAbsolute {Z : Scheme.{u}} (e : yoneda.obj Z ≅ relativeTotalPresheaf F) :
    RelativeRepresentation F := by
  let p := yonedaEquiv (e.hom ≫ relativeTotalToBase F)
  let Y := Over.mk p
  have hp : e.hom ≫ relativeTotalToBase F = yoneda.map p :=
    yonedaEquiv.injective (yonedaEquiv_yoneda_map p).symm
  have hBase {X : Scheme.{u}} (g : X ⟶ Z) : (e.hom.app (op X) g).1 = g ≫ p :=
    congrArg (fun m => m.app (op X) g) hp
  let fiber (T : Over S) :
      (relativePoints S Y).val.obj (op T) ≃ F.val.obj (op T) :=
    { toFun g := sectionAs F T (e.hom.app (op T.left) g.val) ((hBase g.val).trans g.property)
      invFun x :=
        let g := e.inv.app (op T.left) (totalMk F T x)
        have he : e.hom.app (op T.left) g = totalMk F T x :=
          (e.app (op T.left)).toEquiv.right_inv _
        ⟨g, (hBase g).symm.trans (congrArg Sigma.fst he)⟩
      left_inv g := by
        apply Subtype.ext
        change e.inv.app (op T.left) (totalMk F T (sectionAs F T (e.hom.app (op T.left) g.val) _)) = g.val
        rw [totalMk_sectionAs]
        exact (e.app (op T.left)).toEquiv.left_inv _
      right_inv x := by
        change sectionAs F T (e.hom.app (op T.left) (e.inv.app (op T.left) (totalMk F T x))) _ = x
        exact (sectionAs_congr F ((e.app (op T.left)).toEquiv.right_inv _) _ rfl).trans
          (sectionAs_totalMk F T x) }
  refine ⟨Y, (fullyFaithfulSheafToPresheaf _ _).preimageIso (NatIso.ofComponents (fun T => (fiber T.unop).toIso) ?_)⟩
  intro T V a
  ext g
  let b := a.unop
  let z := e.hom.app (op T.unop.left) g.val
  have hn : e.hom.app (op V.unop.left) (b.left ≫ g.val) = totalMap F b.left z :=
    FunctorToTypes.naturality _ _ e.hom b.left.op g.val
  have hz : z.1 = T.unop.hom := (hBase g.val).trans g.property
  have hv : (totalMap F b.left z).1 = V.unop.hom :=
    (congrArg (b.left ≫ ·) hz).trans (Over.w b)
  have hv' : (e.hom.app (op V.unop.left) (b.left ≫ g.val)).1 = V.unop.hom := (congrArg Sigma.fst hn).trans hv
  change sectionAs F V.unop (e.hom.app (op V.unop.left) (b.left ≫ g.val)) hv' =
    F.val.map b.op (sectionAs F T.unop z hz)
  exact (sectionAs_congr F hn hv' hv).trans (sectionAs_totalMap F b z hz hv)

/-- A relative sheaf represented over every open chart is represented by the glued scheme. -/
def RelativeRepresentation.ofOpenCover (C : Scheme.OpenCover.{u} S)
    (Y : ∀ i, RelativeRepresentation ((Scheme.zariskiTopology.overMapPullback (Type u) (C.f i)).obj F)) :
    RelativeRepresentation F := by
  let maps := fun i => chartRepresentationMap F (C.f i) (Y i).space (Y i).points.symm
  have opens : ∀ i, IsOpenImmersion.presheaf (maps i) :=
    fun i => chartRepresentationMap_open F (C.f i) (Y i).space (Y i).points.symm
  let hsurj : Presheaf.IsLocallySurjective Scheme.zariskiTopology (Sigma.desc maps) :=
    chartRepresentation_locallySurjective F C Y
  let e := @Scheme.LocalRepresentability.yonedaIsoSheaf
    (relativeTotalSheaf F) C.I₀ (fun i => (Y i).space.left) maps opens hsurj
  exact representationOfAbsolute F ((sheafToPresheaf _ _).mapIso e)

end SHIGURE.Copying
