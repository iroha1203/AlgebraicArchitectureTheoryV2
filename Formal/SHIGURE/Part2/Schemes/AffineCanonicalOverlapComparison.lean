import Formal.SHIGURE.Part2.Schemes.AffinePullbackComparison
import Formal.SHIGURE.Part2.Schemes.AffineTildeCongruence
import Formal.SHIGURE.Part2.Descent.CanonicalScalarComparison
import Formal.SHIGURE.Part2.Schemes.AffineQuasiCoherentFiber
import Formal.SHIGURE.Part2.Schemes.CanonicalDescentComparison

/-! # Canonical affine descent on double overlaps

## Implementation notes

Appendix B.3 uses the actual geometric comparison and Lemma B.4 uses the
canonical scalar comparison. We compare the two in the category of module
sheaves after composing pullback functors. Writing the components of the
natural comparisons with the same endpoints makes their equality explicit.
-/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory Opposite Scheme.Modules SHIGURE.CoefficientDescent

noncomputable section

universe u

private theorem compose_chart_components {C D : Type*} [Category C] [Category D]
    (G : D ⥤ C) {X₀ X₁ I₀ I₁ : C} {U₀ U₁ V₀ V₁ : D}
    (r₀ : X₀ ⟶ I₀) (r₁ : X₁ ⟶ I₁) (back : I₁ ⟶ X₁) (inverse : back ≫ r₁ = 𝟙 I₁)
    (a₀ : I₀ ⟶ G.obj U₀) (a₁ : I₁ ⟶ G.obj U₁)
    (c : I₀ ⟶ I₁) (e : U₀ ⟶ U₁)
    (s₀ : U₀ ≅ V₀) (s₁ : U₁ ≅ V₁) (k₀ : X₀ ⟶ G.obj V₀) (k₁ : X₁ ≅ G.obj V₁)
    (left : r₀ ≫ a₀ ≫ G.map s₀.hom = k₀)
    (right : r₁ ≫ a₁ ≫ G.map s₁.hom = k₁.hom)
    (middle : c ≫ a₁ = a₀ ≫ G.map e) :
    r₀ ≫ c ≫ back = k₀ ≫ G.map (s₀.inv ≫ e ≫ s₁.hom) ≫ k₁.inv := by
  apply (cancel_mono k₁.hom).1
  simp only [G.map_comp, Category.assoc, k₁.inv_hom_id, Category.comp_id]
  rw [← right, ← Category.assoc back, inverse, Category.id_comp, ← left]
  simp only [Category.assoc]
  rw [← Category.assoc (G.map s₀.hom), ← G.map_comp, s₀.hom_inv_id, G.map_id, Category.id_comp]
  rw [← Category.assoc c, middle, Category.assoc]

private theorem map_identity_comparison {C D : Type*} [Category C] [Category D]
    (G : D ⥤ C) {X : C} {Y : D} (f : X ⟶ G.obj Y) :
    𝟙 X ≫ f = f ≫ G.map (𝟙 Y) := by
  rw [Category.id_comp, G.map_id, Category.comp_id]

section Affine

variable {R S T : CommRingCat.{u}} (f : R ⟶ S) (M : ModuleCat.{u} R)

/-- The iterated tilde comparison for the two actual pullbacks in the
canonical affine descent datum of Appendix B.3. -/
def affineIteratedTildeChart (g : S ⟶ T) :
    (pullback (Spec.map f) ⋙ pullback (Spec.map g)).obj (((affineTildeFunctor R).obj M).obj) ≅
      (tilde.functor T).obj ((ModuleCat.extendScalars f.hom ⋙ ModuleCat.extendScalars g.hom).obj M) :=
  (pullback (Spec.map g)).mapIso ((tildePullbackIso f).app M) ≪≫
    (tildePullbackIso g).app ((ModuleCat.extendScalars f.hom).obj M)

private def directChart (r : R ⟶ T) (N : ModuleCat.{u} R) := (tildePullbackIso r).app N

private def scalarComposition (g : S ⟶ T) :
    (ModuleCat.extendScalars (f ≫ g).hom).obj M ≅
      (ModuleCat.extendScalars f.hom ⋙ ModuleCat.extendScalars g.hom).obj M := (ModuleCat.extendScalarsComp f.hom g.hom).app M

private def scalarCongruence {r s : R ⟶ T} (equal : r = s) (N : ModuleCat.{u} R) :
    (ModuleCat.extendScalars r.hom).obj N ≅ (ModuleCat.extendScalars s.hom).obj N :=
  (extensionAlongCongruence (congrArg (fun k : R ⟶ T => k.hom) equal)).app N

set_option maxRecDepth 2048 in
private theorem computed_composition (g : S ⟶ T) :
    (affinePullbackComposition f g).hom.app ((affineTildeFunctor R).obj M).obj ≫ (directChart (f ≫ g) M).hom ≫
      (tilde.functor T).map (scalarComposition f M g).hom = (affineIteratedTildeChart f M g).hom :=
  tildePullbackIso_comp_at f g M

set_option maxRecDepth 2048 in
private theorem computed_congruence {r s : R ⟶ T} (equal : r = s) (N : ModuleCat.{u} R) :
    (pullbackCongr (congrArg (fun k : R ⟶ T => Spec.map k) equal)).hom.app ((affineTildeFunctor R).obj N).obj ≫ (directChart s N).hom =
      (directChart r N).hom ≫ (tilde.functor T).map (scalarCongruence equal N).hom := by
  subst s
  change 𝟙 _ ≫ (directChart r N).hom = (directChart r N).hom ≫ (tilde.functor T).map (𝟙 _)
  exact map_identity_comparison (tilde.functor T) (directChart r N).hom

set_option maxRecDepth 2048 in
set_option maxHeartbeats 40000 in
private def overlapComponents (p q : S ⟶ T) (h : f ≫ p = f ≫ q) :=
  compose_chart_components (C := (Spec T).Modules) (D := ModuleCat.{u} T) (tilde.functor T)
    ((affinePullbackComposition f p).hom.app ((affineTildeFunctor R).obj M).obj)
    ((affinePullbackComposition f q).hom.app ((affineTildeFunctor R).obj M).obj)
    ((affinePullbackComposition f q).inv.app ((affineTildeFunctor R).obj M).obj)
    (Iso.inv_hom_id_app (affinePullbackComposition f q) ((affineTildeFunctor R).obj M).obj)
    (directChart (f ≫ p) M).hom
    (directChart (f ≫ q) M).hom
    ((pullbackCongr (congrArg (fun k : R ⟶ T => Spec.map k) h)).hom.app ((affineTildeFunctor R).obj M).obj)
    (scalarCongruence h M).hom
    (scalarComposition f M p)
    (scalarComposition f M q)
    (affineIteratedTildeChart f M p).hom
    (affineIteratedTildeChart f M q)
    (computed_composition f M p)
    (computed_composition f M q)
    (computed_congruence h M)

private theorem canonical_comparison_hom {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (p q : S →+* T) (equal : p.comp f = q.comp f) (M : ModuleCat.{u} R) :
    (canonicalScalarComparison f p q equal M).hom =
      ((ModuleCat.extendScalarsComp f p).app M).inv ≫
        (extensionAlongCongruence equal).hom.app M ≫ ((ModuleCat.extendScalarsComp f q).app M).hom :=
  rfl

set_option maxRecDepth 2048 in
set_option maxHeartbeats 110000 in
/-- The comparison of the two geometric restrictions is the tilde of the
canonical comparison of the two successive scalar extensions. -/
theorem affineCanonicalOverlapComparison (p q : S ⟶ T) (h : f ≫ p = f ≫ q) :
    (affinePullbackComposition f p).hom.app ((affineTildeFunctor R).obj M).obj ≫
      (pullbackCongr (congrArg (fun k : R ⟶ T => Spec.map k) h)).hom.app ((affineTildeFunctor R).obj M).obj ≫
      (affinePullbackComposition f q).inv.app ((affineTildeFunctor R).obj M).obj =
    (affineIteratedTildeChart f M p).hom ≫ (tilde.functor T).map
      (canonicalScalarComparison f.hom p.hom q.hom (congrArg (fun k : R ⟶ T => k.hom) h) M).hom ≫
      (affineIteratedTildeChart f M q).inv := by
  have canonicalHom : (canonicalScalarComparison f.hom p.hom q.hom
      (congrArg (fun k : R ⟶ T => k.hom) h) M).hom =
      (scalarComposition f M p).inv ≫ (scalarCongruence h M).hom ≫ (scalarComposition f M q).hom :=
    canonical_comparison_hom f.hom p.hom q.hom (congrArg (fun k : R ⟶ T => k.hom) h) M
  rw [canonicalHom]
  exact overlapComponents f M p q h

end Affine

variable {R S T : CommRingCat.{u}}

/-- The quasi-coherent pseudofunctor used for affine descent in Appendix B.3. -/
private abbrev Q := quasiCoherentModulesPseudofunctor.{u}

private theorem mappedDescentIso_hom
    {C : Type*} [Category C]
    {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat}
    {ι : Type*} {S T : C} {U : ι → C} {f : ∀ i, U i ⟶ S}
    (D : F.DescentData f) (b : T ⟶ S) {i j : ι}
    (r : T ⟶ U i) (s : T ⟶ U j)
    (hr : r ≫ f i = b) (hs : s ≫ f j = b)
    {E : Type*} [Category E] (I : F.obj (.mk (op T)) ⥤ E) :
    (I.mapIso (D.iso b (i₁ := i) (i₂ := j) r s hr hs)).hom =
      I.map (D.hom b (i₁ := i) (i₂ := j) r s hr hs) := rfl

/-- The underlying map of the canonical singleton isomorphism between the
two iterated pullbacks of the original module sheaf. -/
theorem singletonMappedIso_hom_betweenPullbacks
    {X Y Z : Scheme.{u}} (a : Y ⟶ X) (r s : Z ⟶ Y) (b : Z ⟶ X)
    (hr : r ≫ a = b) (hs : s ≫ a = b)
    (N : Q.obj (.mk (op X))) :
    @Eq ((pullback a ⋙ pullback r).obj N.obj ⟶
         (pullback a ⋙ pullback s).obj N.obj)
      (Iso.hom (C := Z.Modules)
        (X := (pullback a ⋙ pullback r).obj N.obj)
        (Y := (pullback a ⋙ pullback s).obj N.obj)
        ((quasiCoherentModulesProperty.prop (.mk (op Z))).ι.mapIso
          (((quasiCoherentModulesPseudofunctor.toDescentData
              (fun _ : Unit => a)).obj N).iso b
            (i₁ := ()) (i₂ := ()) r s hr hs)))
      ((quasiCoherentModulesProperty.prop (.mk (op Z))).ι.map
        (((Q.toDescentData (fun _ : Unit => a)).obj N).hom b
          (i₁ := ()) (i₂ := ()) r s hr hs)) := by
  unfold Q
  exact mappedDescentIso_hom
    (F := quasiCoherentModulesPseudofunctor) (f := fun _ : Unit => a)
    ((quasiCoherentModulesPseudofunctor.toDescentData
      (fun _ : Unit => a)).obj N)
    b (i := ()) (j := ()) r s hr hs
    (quasiCoherentModulesProperty.prop (.mk (op Z))).ι

/-- State the comparison in the actual category of module sheaves. -/
private theorem singletonComparisonSchemeModules
    {X Y Z : Scheme.{u}} (a : Y ⟶ X) (r s : Z ⟶ Y) (b₀ b₁ b : Z ⟶ X)
    (hr : r ≫ a = b) (hs : s ≫ a = b) (h₀ : r ≫ a = b₀) (h₁ : s ≫ a = b₁) (equal : b₀ = b₁)
    (N : Q.obj (.mk (op X))) :
    @Eq ((pullback a ⋙ pullback r).obj N.obj ⟶ (pullback a ⋙ pullback s).obj N.obj)
      ((quasiCoherentModulesProperty.prop (.mk (op Z))).ι.map
        (((Q.toDescentData (fun _ : Unit => a)).obj N).hom b
          (i₁ := ()) (i₂ := ()) r s hr hs))
      ((pullbackCompositionFor a r b₀ h₀).hom.app N.obj ≫
        (pullbackCongr equal).hom.app N.obj ≫
        (pullbackCompositionFor a s b₁ h₁).inv.app N.obj) :=
  singletonCanonicalComparison_along a r s b₀ b₁ b hr hs h₀ h₁ equal N

private def singletonFactorisation (f : R ⟶ S) (p q : S ⟶ T) (h : f ≫ p = f ≫ q)
    (M : ModuleCat.{u} R) (b : Spec T ⟶ Spec R)
    (hp : Spec.map p ≫ Spec.map f = b) (hq : Spec.map q ≫ Spec.map f = b) :=
  singletonComparisonSchemeModules (Spec.map f) (Spec.map p) (Spec.map q)
    (Spec.map (f ≫ p)) (Spec.map (f ≫ q)) b hp hq (Spec.map_comp f p).symm
    (Spec.map_comp f q).symm (congrArg (fun k : R ⟶ T => Spec.map k) h) ((affineTildeFunctor R).obj M)

private theorem affinePullbackComposition_eq (f : R ⟶ S) (p : S ⟶ T) :
    pullbackCompositionFor (Spec.map f) (Spec.map p) (Spec.map (f ≫ p))
      (Spec.map_comp f p).symm = affinePullbackComposition f p := rfl

private theorem normaliseGeometricOverlap (f : R ⟶ S) (p q : S ⟶ T)
    (h : f ≫ p = f ≫ q) (N : (Spec R).Modules) :
    (pullbackCompositionFor (Spec.map f) (Spec.map p) (Spec.map (f ≫ p))
      (Spec.map_comp f p).symm).hom.app N ≫
      (pullbackCongr (congrArg (fun k : R ⟶ T => Spec.map k) h)).hom.app N ≫
      (pullbackCompositionFor (Spec.map f) (Spec.map q) (Spec.map (f ≫ q))
        (Spec.map_comp f q).symm).inv.app N =
    (affinePullbackComposition f p).hom.app N ≫
      (pullbackCongr (congrArg (fun k : R ⟶ T => Spec.map k) h)).hom.app N ≫
      (affinePullbackComposition f q).inv.app N := by
  rw [affinePullbackComposition_eq, affinePullbackComposition_eq]

set_option maxRecDepth 2048 in
set_option maxHeartbeats 80000 in
private def singletonFactorsNormal (f : R ⟶ S) (p q : S ⟶ T) (h : f ≫ p = f ≫ q)
    (M : ModuleCat.{u} R) (b : Spec T ⟶ Spec R)
    (hp : Spec.map p ≫ Spec.map f = b) (hq : Spec.map q ≫ Spec.map f = b) :=
  Eq.trans (singletonFactorisation f p q h M b hp hq)
    (normaliseGeometricOverlap f p q h ((affineTildeFunctor R).obj M).obj)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 135000 in
private def singletonComparisonProof (f : R ⟶ S) (p q : S ⟶ T) (h : f ≫ p = f ≫ q)
    (M : ModuleCat.{u} R) (b : Spec T ⟶ Spec R)
    (hp : Spec.map p ≫ Spec.map f = b) (hq : Spec.map q ≫ Spec.map f = b) :=
  Eq.trans (singletonFactorsNormal f p q h M b hp hq) (affineCanonicalOverlapComparison f M p q h)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 160000 in
/-- For the singleton affine family in Appendix B.3, the transition of the
actual geometric comparison is the tilde of the canonical scalar comparison
from Lemma B.4, conjugated by the two iterated tilde charts. The two test
maps have the same composite to the base. -/
theorem singletonCanonicalAffineComparison (f : R ⟶ S) (p q : S ⟶ T) (h : f ≫ p = f ≫ q)
    (M : ModuleCat.{u} R) (b : Spec T ⟶ Spec R)
    (hp : Spec.map p ≫ Spec.map f = b) (hq : Spec.map q ≫ Spec.map f = b) :
    @Eq ((pullback (Spec.map f) ⋙ pullback (Spec.map p)).obj ((affineTildeFunctor R).obj M).obj ⟶
      (pullback (Spec.map f) ⋙ pullback (Spec.map q)).obj ((affineTildeFunctor R).obj M).obj)
      ((quasiCoherentModulesProperty.prop (.mk (op (Spec T)))).ι.map
        (((Q.toDescentData (fun _ : Unit => Spec.map f)).obj ((affineTildeFunctor R).obj M)).hom b
          (i₁ := ()) (i₂ := ()) (Spec.map p) (Spec.map q) hp hq))
      ((affineIteratedTildeChart f M p).hom ≫ (tilde.functor T).map
        (canonicalScalarComparison f.hom p.hom q.hom (congrArg (fun k : R ⟶ T => k.hom) h) M).hom ≫
        (affineIteratedTildeChart f M q).inv) :=
  singletonComparisonProof f p q h M b hp hq

end

end SHIGURE.SchemeDescent
