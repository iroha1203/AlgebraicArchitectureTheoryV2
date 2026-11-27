import Formal.SHIGURE.Part2.Schemes.FiberwiseSectionDescent
import Formal.SHIGURE.Part2.Schemes.FppfRelativeAffineSections
import Mathlib.CategoryTheory.Sites.Descent.Precoverage

/-! # Descent of sections represented by affine schemes -/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Pseudofunctor Opposite

noncomputable section

universe u v a b

variable {F : Pseudofunctor (LocallyDiscrete (Scheme.{u})ᵒᵖ) Cat.{a,b}}
  (A : FiberwiseSections F) {X : Scheme.{u}} (M : F.obj (.mk (op X)))

namespace FiberwiseSections

/-- Express a restriction in the pullback of the global object along
the composite map, using the actual composition isomorphism. -/
def normalizedSection {Y Z : Scheme.{u}} (p : Y ⟶ X) (q : Z ⟶ Y) (r : Z ⟶ X)
    (equal : q ≫ p = r)
    (s : (A.fiber (.mk (op Y))).obj ((F.map p.op.toLoc).toFunctor.obj M)) :
    (A.fiber (.mk (op Z))).obj ((F.map r.op.toLoc).toFunctor.obj M) :=
  (A.fiber (.mk (op Z))).map
    ((F.mapComp' p.op.toLoc q.op.toLoc r.op.toLoc
      (congrArg (fun k => k.op.toLoc) equal)).inv.toNatTrans.app M)
    ((A.restrict q.op.toLoc).app ((F.map p.op.toLoc).toFunctor.obj M) s)

/-- For the actual composite, the normalized section is the restricted
section transported by the inverse composition comparison. -/
theorem normalizedSection_comp {Y Z : Scheme.{u}} (p : Y ⟶ X) (q : Z ⟶ Y)
    (s : (A.fiber (.mk (op Y))).obj ((F.map p.op.toLoc).toFunctor.obj M)) :
    A.normalizedSection M p q (q ≫ p) rfl s =
      (A.fiber (.mk (op Z))).map ((F.mapComp p.op.toLoc q.op.toLoc).inv.toNatTrans.app M)
        ((A.restrict q.op.toLoc).app ((F.map p.op.toLoc).toFunctor.obj M) s) := by
  have equality : p.op.toLoc ≫ q.op.toLoc = (q ≫ p).op.toLoc := rfl
  have comparison : F.mapComp' p.op.toLoc q.op.toLoc (q ≫ p).op.toLoc equality =
      F.mapComp p.op.toLoc q.op.toLoc := F.mapComp'_eq_mapComp p.op.toLoc q.op.toLoc
  unfold normalizedSection
  rw [comparison]

/-- Restricting the global section twice gives its actual restriction to the composite. -/
theorem normalizedSection_global {Y Z : Scheme.{u}} (p : Y ⟶ X) (q : Z ⟶ Y) (r : Z ⟶ X)
    (equal : q ≫ p = r) (s : (A.fiber (.mk (op X))).obj M) :
    A.normalizedSection M p q r equal ((A.restrict p.op.toLoc).app M s) =
      (A.restrict r.op.toLoc).app M s := by
  subst r
  let P := A.fiber (.mk (op Z))
  let c := (Cat.Hom.toNatIso (F.mapComp p.op.toLoc q.op.toLoc)).app M
  have hc : P.map c.hom ((A.restrict (q ≫ p).op.toLoc).app M s) =
      (A.restrict q.op.toLoc).app ((F.map p.op.toLoc).toFunctor.obj M) ((A.restrict p.op.toLoc).app M s) :=
    A.restrict_comp p.op.toLoc q.op.toLoc M s
  have eq : p.op.toLoc ≫ q.op.toLoc = (q ≫ p).op.toLoc := rfl
  have composition : F.mapComp' p.op.toLoc q.op.toLoc (q ≫ p).op.toLoc eq =
      F.mapComp p.op.toLoc q.op.toLoc := F.mapComp'_eq_mapComp p.op.toLoc q.op.toLoc
  unfold normalizedSection
  rw [composition]
  exact (congrArg (P.map c.inv) hc).symm.trans
    (FunctorToTypes.map_inv_map_hom_apply P c _)

private theorem normalizedSection_agree {Y Z T : Scheme.{u}} (p : Y ⟶ X) (q : Z ⟶ X)
    (r : T ⟶ Y) (s : T ⟶ Z) (k : T ⟶ X) (hr : r ≫ p = k) (hs : s ≫ q = k)
    (m : (A.fiber (.mk (op Y))).obj ((F.map p.op.toLoc).toFunctor.obj M))
    (n : (A.fiber (.mk (op Z))).obj ((F.map q.op.toLoc).toFunctor.obj M))
    (compat : let P := A.fiber (.mk (op T))
      let c := (F.mapComp' p.op.toLoc r.op.toLoc k.op.toLoc (congrArg (fun l => l.op.toLoc) hr)).inv.toNatTrans.app M
      let d := (F.mapComp' q.op.toLoc s.op.toLoc k.op.toLoc (congrArg (fun l => l.op.toLoc) hs)).hom.toNatTrans.app M
      P.map (c ≫ d) ((A.restrict r.op.toLoc).app _ m) = (A.restrict s.op.toLoc).app _ n) :
    A.normalizedSection M p r k hr m = A.normalizedSection M q s k hs n := by
  let P := A.fiber (.mk (op T))
  let c := (Cat.Hom.toNatIso (F.mapComp' p.op.toLoc r.op.toLoc k.op.toLoc
    (congrArg (fun l => l.op.toLoc) hr))).app M
  let d := (Cat.Hom.toNatIso (F.mapComp' q.op.toLoc s.op.toLoc k.op.toLoc
    (congrArg (fun l => l.op.toLoc) hs))).app M
  let l := (A.restrict r.op.toLoc).app _ m
  let t := (A.restrict s.op.toLoc).app _ n
  have h : P.map d.hom (P.map c.inv l) = t :=
    (FunctorToTypes.map_comp_apply P c.inv d.hom l).symm.trans compat
  exact (FunctorToTypes.map_inv_map_hom_apply P d _).symm.trans (congrArg (P.map d.inv) h)

/-- Restriction along the identity is the unit isomorphism on the sections. -/
def restrictionIdentityEquiv :
    (A.fiber (.mk (op X))).obj M ≃ (A.fiber (.mk (op X))).obj
      ((F.map (𝟙 X).op.toLoc).toFunctor.obj M) where
  toFun := (A.restrict (𝟙 X).op.toLoc).app M
  invFun := (A.fiber (.mk (op X))).map ((F.mapId (.mk (op X))).hom.toNatTrans.app M)
  left_inv := A.restrict_id (.mk (op X)) M
  right_inv s := by
    let P := A.fiber (.mk (op X))
    let c := (Cat.Hom.toNatIso (F.mapId (.mk (op X)))).app M
    apply (show Function.Injective (P.map c.hom) from
      (show Function.LeftInverse (P.map c.inv) (P.map c.hom) from
        FunctorToTypes.map_inv_map_hom_apply P c).injective)
    exact A.restrict_id (.mk (op X)) M (P.map c.hom s)

end FiberwiseSections

/-- Representability of the sections of a fixed object on test schemes by
an affine morphism over its base. The naturality equation refers to the
actual restriction and composition comparisons in Appendix B.3. -/
structure AffineRepresentedSections where
  total : Scheme.{u}
  projection : total ⟶ X
  affine : IsAffineHom projection
  sections {Y : Scheme.{u}} (p : Y ⟶ X) :
    (A.fiber (.mk (op Y))).obj ((F.map p.op.toLoc).toFunctor.obj M) ≃
      (Over.mk p ⟶ Over.mk projection)
  naturality {Y Z : Scheme.{u}} (p : Y ⟶ X) (q : Z ⟶ Y) (r : Z ⟶ X)
    (equal : q ≫ p = r)
    (s : (A.fiber (.mk (op Y))).obj ((F.map p.op.toLoc).toFunctor.obj M)) :
    sections r (A.normalizedSection M p q r equal s) =
      (Over.homMk q equal : Over.mk r ⟶ Over.mk p) ≫ sections p s

namespace AffineRepresentedSections

variable {A M} (R : AffineRepresentedSections A M)

/-- The representation identifies global sections with actual sections of the affine morphism. -/
def globalSections :
    (A.fiber (.mk (op X))).obj M ≃ (Over.mk (𝟙 X) ⟶ Over.mk R.projection) :=
  (A.restrictionIdentityEquiv M).trans (R.sections (𝟙 X))

/-- The restriction of a global section corresponds to precomposing its representing map. -/
theorem globalSections_restrict {Y : Scheme.{u}} (q : Y ⟶ X)
    (s : (A.fiber (.mk (op X))).obj M) :
    R.sections q ((A.restrict q.op.toLoc).app M s) =
      (Over.homMk q (Category.comp_id q) : Over.mk q ⟶ Over.mk (𝟙 X)) ≫ R.globalSections s := by
  have h := R.naturality (𝟙 X) q q (Category.comp_id q) ((A.restrict (𝟙 X).op.toLoc).app M s)
  rw [A.normalizedSection_global] at h
  exact h

include R in
private theorem sections_descend_for_object (cover : FppfCover.{u,v} X)
    (localSections : A.localSections cover.f M)
    (compat : ∀ (Y : Scheme.{u}) (q : Y ⟶ X) (i j : cover.I₀) (p : Y ⟶ cover.X i) (r : Y ⟶ cover.X j)
      (hp : p ≫ cover.f i = q) (hr : r ≫ cover.f j = q),
      (A.fiber (.mk (op Y))).map (((F.toDescentData cover.f).obj M).hom q p r hp hr)
        ((A.restrict p.op.toLoc).app _ (localSections i)) = (A.restrict r.op.toLoc).app _ (localSections j)) :
    ∃! t, ∀ i, A.canonicalLocal cover.f M t i = localSections i := by
  let m (i : cover.I₀) := R.sections (cover.f i) (localSections i)
  have overLocal (i : cover.I₀) : (m i).left ≫ R.projection = cover.f i := Over.w (m i)
  have compatible : Presieve.Arrows.Compatible (yoneda.obj R.total) cover.f (fun i => (m i).left) := by
    intro i j T p q equal
    let k := p ≫ cover.f i
    have same : A.normalizedSection M (cover.f i) p k rfl (localSections i) =
        A.normalizedSection M (cover.f j) q k equal.symm (localSections j) :=
      A.normalizedSection_agree M (cover.f i) (cover.f j) p q k rfl equal.symm
        (localSections i) (localSections j) (compat T k i j p q rfl equal.symm)
    have left := R.naturality (cover.f i) p k rfl (localSections i)
    have right := R.naturality (cover.f j) q k equal.symm (localSections j)
    have asOver := left.symm.trans ((congrArg (R.sections k) same).trans right)
    exact congrArg (fun h : Over.mk k ⟶ Over.mk R.projection => h.left) asOver
  letI : IsAffineHom R.projection := R.affine
  obtain ⟨g, ⟨overG, onG⟩, unique⟩ :=
    relativeAffineSection_descent (cover := cover) R.projection (fun i => (m i).left) overLocal compatible
  let g' : Over.mk (𝟙 X) ⟶ Over.mk R.projection := Over.homMk g overG
  let t := R.globalSections.symm g'
  have matching (i : cover.I₀) : A.canonicalLocal cover.f M t i = localSections i := by
    apply (R.sections (cover.f i)).injective
    change R.sections (cover.f i) ((A.restrict (cover.f i).op.toLoc).app M t) = m i
    rw [R.globalSections_restrict, show R.globalSections t = g' from R.globalSections.apply_symm_apply _]
    apply (Over.forget X).map_injective
    exact onG i
  refine ⟨t, matching, ?_⟩
  intro s hs
  apply R.globalSections.injective
  rw [show R.globalSections t = g' from R.globalSections.apply_symm_apply _]
  apply (Over.forget X).map_injective
  apply unique (R.globalSections s).left
  refine ⟨Over.w (R.globalSections s), ?_⟩
  intro i
  have formula := R.globalSections_restrict (cover.f i) s
  have si : (A.restrict (cover.f i).op.toLoc).app M s = localSections i := hs i
  rw [si] at formula
  exact (congrArg (fun h : Over.mk (cover.f i) ⟶ Over.mk R.projection => h.left) formula).symm

end AffineRepresentedSections

/-- The section descent hypothesis for the pair comparison follows from
the representability of each test section functor by an affine scheme. -/
theorem sectionDescent_of_affineRepresentation
    (represent : ∀ N : F.obj (.mk (op X)), AffineRepresentedSections A N) (cover : FppfCover.{u,v} X) :
    A.HasSectionDescent cover.f :=
  fun N => (represent N).sections_descend_for_object cover


/-- A family of affinely represented sections over an fppf stack gives an
fppf stack of pairs, using the original fppf comparison on every cover. -/
theorem affinelyRepresentedSections_isFppfStack (A : FiberwiseSections F)
    [F.IsStack fppfTopology]
    (represent : ∀ (T : Scheme.{u}) (N : F.obj (.mk (op T))), AffineRepresentedSections A N) :
    A.pseudofunctor.IsStack fppfTopology := by
  letI : MorphismProperty.IsMultiplicative
      (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) :=
    { id_mem := fun T => inferInstanceAs (LocallyOfFinitePresentation (𝟙 T)) }
  apply IsStack.of_precoverage (J := Scheme.precoverage FppfComponent)
  intro T P hP
  let cover : FppfCover.{u,u+1} T := ⟨P.preZeroHypercover, P.presieve₀_preZeroHypercover.symm ▸ hP⟩
  have comparison : cover.presieve₀ = P := P.presieve₀_preZeroHypercover
  letI : (F.toDescentData cover.f).IsEquivalence :=
    F.isEquivalence_toDescentData cover.f (fppfCover_sieve_mem cover)
  rw [← comparison]
  exact (A.pseudofunctor.isStackFor_ofArrows_iff cover.f).2
    (A.comparison_isEquivalence cover.f (sectionDescent_of_affineRepresentation A (represent T) cover))

end

end SHIGURE.SchemeDescent
