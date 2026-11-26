import Formal.SHIGURE.Part2.Schemes.TildeBaseChange
import Formal.SHIGURE.Part2.Schemes.FiniteCoverLocalizations
import Mathlib.Algebra.Category.ModuleCat.Localization

/-! # The affine localization criterion for module sheaves

On a spectrum, principal-open restrictions detect the counit of the
associated-module/global-sections adjunction. The detection uses the
basis of principal opens and the localization universal property.

## Implementation notes

The counit of the associated-module/global-sections adjunction supplies
a canonical comparison. Principal opens detect this map, then the
finite-limit localization theorem handles finite principal covers.
The affine communication lemma extends the result to an arbitrary
affine cover. Choosing a different associated module on every open
would require separate compatibility isomorphisms for these comparisons.
-/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Scheme.Modules

noncomputable section

universe u

variable {R : CommRingCat.{u}}

private theorem isIso_of_basis {X : TopCat.{u}} {ι : Type u} {C : Type (u + 1)}
    [Category.{u} C] {B : ι → Opens X} (basis : Opens.IsBasis (Set.range B))
    {F G : TopCat.Sheaf C X} (m : F ⟶ G) (localIso : ∀ i, IsIso (m.val.app (op (B i)))) :
    IsIso m := by
  let restriction := (inducedFunctor B).op
  let restricted := Functor.whiskerLeft restriction m.val
  haveI : ∀ i, IsIso (restricted.app i) := fun i => localIso i.unop
  haveI : IsIso restricted := NatIso.isIso_of_isIso_app restricted
  let backwards := TopCat.Sheaf.restrictHomEquivHom G.val F basis (inv restricted)
  refine ⟨⟨⟨backwards⟩, ?_, ?_⟩⟩
  · apply CategoryTheory.Sheaf.hom_ext
    apply TopCat.Sheaf.hom_ext F.val F basis
    intro i
    change m.val.app (op (B i)) ≫ backwards.app (op (B i)) = 𝟙 _
    rw [TopCat.Sheaf.extend_hom_app]
    exact (asIso restricted).hom_inv_id_app (op i)
  · apply CategoryTheory.Sheaf.hom_ext
    apply TopCat.Sheaf.hom_ext G.val G basis
    intro i
    change backwards.app (op (B i)) ≫ m.val.app (op (B i)) = 𝟙 _
    rw [TopCat.Sheaf.extend_hom_app]
    exact (asIso restricted).inv_hom_id_app (op i)

/-- A sheaf on a spectrum has the expected localization maps from its global
sections to all principal opens.
This is the principal-open criterion for the affine presentations in Appendix B. The maps are
the actual restrictions of a module sheaf on a spectrum. -/
def PrincipalLocalizations (M : (Spec R).Modules) : Prop :=
  ∀ r : R, IsLocalizedModule (Submonoid.powers r)
    ((modulesSpecToSheaf.obj M).val.map (homOfLE (show PrimeSpectrum.basicOpen r ≤ ⊤ from le_top)).op).hom

/-- Principal localizations make the actual tilde–global sections counit an isomorphism.
This is the recovery step for Appendix B.3. The finite-cover argument supplies the
principal-open localization hypotheses. -/
theorem fromTildeΓ_isIso_of_principalLocalizations (M : (Spec R).Modules)
    (localizes : PrincipalLocalizations M) : IsIso M.fromTildeΓ := by
  letI := (SpecModulesToSheafFullyFaithful (R := R)).reflectsIsomorphisms
  haveI : IsIso (modulesSpecToSheaf.map M.fromTildeΓ) := by
    apply isIso_of_basis PrimeSpectrum.isBasis_basic_opens
    intro r
    let N := (modulesSpecToSheaf.obj M).presheaf.obj (op ⊤)
    let W := PrimeSpectrum.basicOpen r
    let p := tilde.toOpen N W
    let q := (modulesSpecToSheaf.obj M).val.map (homOfLE (show W ≤ ⊤ from le_top)).op
    let u := (modulesSpecToSheaf.map M.fromTildeΓ).val.app (op W)
    letI : IsLocalizedModule (Submonoid.powers r) q.hom := localizes r
    let e := (IsLocalizedModule.linearEquiv (Submonoid.powers r) p.hom q.hom).toModuleIso
    have equal : u = e.hom := by
      apply ModuleCat.hom_ext
      apply IsLocalizedModule.ext (Submonoid.powers r) p.hom
      · exact IsLocalizedModule.map_units q.hom
      · ext x
        have agrees := congrArg (fun f : N ⟶ _ => f x) (M.toOpen_fromTildeΓ_app W)
        change u (p x) = q x at agrees
        change u (p x) = (IsLocalizedModule.linearEquiv (Submonoid.powers r) p.hom q.hom) (p x)
        rw [IsLocalizedModule.linearEquiv_apply]
        exact agrees
    change IsIso u
    rw [equal]
    infer_instance
  exact isIso_of_reflects_iso M.fromTildeΓ modulesSpecToSheaf


/-- An invertible tilde–global sections counit exhibits each principal
restriction map as the actual localization of the global sections.
This is the converse criterion for Appendix B. The counit is invertible for a tilde presentation
by the tilde-global-sections adjunction. -/
theorem principalLocalizations_of_fromTildeΓ_isIso (M : (Spec R).Modules)
    [IsIso M.fromTildeΓ] : PrincipalLocalizations M := by
  intro r
  let N := (modulesSpecToSheaf.obj M).presheaf.obj (op ⊤)
  let W := PrimeSpectrum.basicOpen r
  let p := tilde.toOpen N W
  let q := (modulesSpecToSheaf.obj M).val.map (homOfLE (show W ≤ ⊤ from le_top)).op
  let g := modulesSpecToSheaf.map M.fromTildeΓ
  let u := g.val.app (op W)
  haveI : IsIso g := inferInstance
  haveI : IsIso g.val := (TopCat.Sheaf.forget _ _).map_isIso g
  haveI : IsIso u := inferInstanceAs (IsIso (g.val.app (op W)))
  have equation : p ≫ u = q := M.toOpen_fromTildeΓ_app W
  change IsLocalizedModule (Submonoid.powers r) q.hom
  rw [← equation]
  exact IsLocalizedModule.of_linearEquiv (Submonoid.powers r) p.hom (asIso u).toLinearEquiv

/-- A module sheaf on an affine scheme is a tilde sheaf precisely when its
global-to-principal restriction maps are localizations.
This API identifies the principal-open condition of Appendix B.3 and the affine tilde
representation via the canonical counit. -/
theorem principalLocalizations_iff_tilde (M : (Spec R).Modules) :
    PrincipalLocalizations M ↔ (tilde.functor R).essImage M := by
  rw [← isIso_fromTildeΓ_iff]
  exact ⟨fromTildeΓ_isIso_of_principalLocalizations M, fun _ => principalLocalizations_of_fromTildeΓ_isIso M⟩


private theorem restrictUnit_app_isIso {X Y : Scheme.{u}} (g : X ⟶ Y) [IsOpenImmersion g]
    (M : Y.Modules) (U : Y.Opens) (leImage : U ≤ g.opensRange) :
    IsIso (((restrictAdjunction g).unit.app M).app U) := by
  rw [restrictAdjunction_unit_app_app]
  have equal := (g.image_preimage_eq_opensRange_inf U).trans (inf_eq_right.mpr leImage)
  have same : homOfLE (g.image_preimage_le U) = eqToHom equal := Subsingleton.elim _ _
  rw [same]
  infer_instance

private theorem restrictedPrincipalMap_localizes {S : CommRingCat.{u}} (f : R ⟶ S)
    (N : (Spec S).Modules) (hN : PrincipalLocalizations N) (r : R)
    (U V : (Spec S).Opens) (incl : op U ⟶ op V)
    (top : U = ⊤) (principal : V = PrimeSpectrum.basicOpen (f r)) :
    IsLocalizedModule (Submonoid.powers r)
      ((((modulesSpecToSheaf.obj N).val ⋙ ModuleCat.restrictScalars f.hom).map incl).hom) := by
  subst U V
  have eq : incl = (homOfLE (le_top : PrimeSpectrum.basicOpen (f r) ≤ ⊤)).op := Subsingleton.elim _ _
  subst incl
  let P := (modulesSpecToSheaf.obj N).val
  let M := P.obj (op ⊤)
  let M' := P.obj (op (PrimeSpectrum.basicOpen (f r)))
  let h := P.map (homOfLE (le_top : PrimeSpectrum.basicOpen (f r) ≤ ⊤)).op
  letI : Algebra R S := f.hom.toAlgebra
  letI : Module R M := Module.compHom M f.hom
  letI : Module R M' := Module.compHom M' f.hom
  letI : IsScalarTower R S M := .of_algebraMap_smul fun _ _ => rfl
  letI : IsScalarTower R S M' := .of_algebraMap_smul fun _ _ => rfl
  letI : IsLocalizedModule (Algebra.algebraMapSubmonoid S (Submonoid.powers r)) h.hom := by
    change IsLocalizedModule ((Submonoid.powers r).map f.hom) h.hom
    rw [Submonoid.map_powers]
    exact hN (f r)
  exact isLocalizedModule_restrictScalars_of_map (Submonoid.powers r) h.hom

/-- An affine pushforward of an associated module sheaf has an associated module presentation.
This API supplies the reverse affine algebra comparison in Lemma B.7. Its inputs are a ring map
and a tilde presentation on its source spectrum. -/
theorem affinePushforward_essImage {S : CommRingCat.{u}} (f : R ⟶ S)
    (N : (Spec S).Modules) (tildeN : (tilde.functor S).essImage N) :
    (tilde.functor R).essImage ((pushforward (Spec.map f)).obj N) := by
  let g := Spec.map f
  apply (principalLocalizations_iff_tilde _).1
  intro r
  let U := PrimeSpectrum.basicOpen r
  let j : op (⊤ : (Spec R).Opens) ⟶ op U := (homOfLE le_top).op
  let P := (modulesSpecToSheaf.obj ((pushforward g).obj N)).val
  let Q := (Opens.map g.base).op ⋙ (modulesSpecToSheaf.obj N).val ⋙ ModuleCat.restrictScalars f.hom
  let comparison : P ≅ Q := moduleSpecPushforwardPresheafIso f N
  let e := comparison.app (op ⊤)
  let e' := comparison.app (op U)
  have equal : P.map j = e.hom ≫ Q.map j ≫ e'.inv := by
    apply (cancel_mono e'.hom).1
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using comparison.hom.naturality j
  letI : IsLocalizedModule (Submonoid.powers r) (Q.map j).hom :=
    restrictedPrincipalMap_localizes f N ((principalLocalizations_iff_tilde N).2 tildeN) r
      (g ⁻¹ᵁ ⊤) (g ⁻¹ᵁ U) ((Opens.map g.base).op.map j) g.preimage_top
      (SpecMap_preimage_basicOpen f r)
  change IsLocalizedModule (Submonoid.powers r) (P.map j).hom
  rw [equal]
  letI : IsLocalizedModule (Submonoid.powers r) ((Q.map j).hom.comp e.toLinearEquiv.toLinearMap) :=
    IsLocalizedModule.of_linearEquiv_right (Submonoid.powers r) (Q.map j).hom e.toLinearEquiv
  exact IsLocalizedModule.of_linearEquiv (Submonoid.powers r)
    ((Q.map j).hom.comp e.toLinearEquiv.toLinearMap) e'.symm.toLinearEquiv

/-- If the restriction to an open affine chart has a tilde presentation,
restricting its sections to a principal open of the ambient affine scheme
localizes them at the ambient scalar.
This is the localization on one chart for Appendix B.3. The chart inclusion and its tilde
presentation give the comparison on principal opens. -/
theorem affineChart_sections_localize {S : CommRingCat.{u}} (f : R ⟶ S)
    [IsOpenImmersion (Spec.map f)] (M : (Spec R).Modules)
    (localTilde : (tilde.functor S).essImage (M.restrict (Spec.map f))) (r : R) :
    IsLocalizedModule (Submonoid.powers r)
      (((modulesSpecToSheaf.obj M).val.map
        (homOfLE (inf_le_left : (Spec.map f).opensRange ⊓ PrimeSpectrum.basicOpen r ≤
          (Spec.map f).opensRange)).op).hom) := by
  let g := Spec.map f
  let N := M.restrict g
  let U := g.opensRange
  let V := U ⊓ PrimeSpectrum.basicOpen r
  let incl : op U ⟶ op V := (homOfLE inf_le_left).op
  let P := (modulesSpecToSheaf.obj M).val
  let Q := (TopologicalSpace.Opens.map g.base).op ⋙
    (modulesSpecToSheaf.obj N).val ⋙ ModuleCat.restrictScalars f.hom
  let eta := (restrictAdjunction g).unit.app M
  let comparison : P ⟶ Q := (modulesSpecToSheaf.map eta).val ≫ (moduleSpecPushforwardPresheafIso f N).hom
  have compareIso (Z : (Spec R).Opens) (hZ : Z ≤ g.opensRange) :
      IsIso (comparison.app (op Z)) := by
    have baseIso : IsIso (eta.app Z) := restrictUnit_app_isIso g M Z hZ
    have bijective := (ConcreteCategory.isIso_iff_bijective (eta.app Z)).1 baseIso
    haveI : IsIso ((modulesSpecToSheaf.map eta).val.app (op Z)) :=
      (ConcreteCategory.isIso_iff_bijective _).2 bijective
    change IsIso ((modulesSpecToSheaf.map eta).val.app (op Z) ≫
      (moduleSpecPushforwardPresheafIso f N).hom.app (op Z))
    infer_instance
  letI := compareIso U le_rfl
  letI := compareIso V inf_le_left
  let e := asIso (comparison.app (op U))
  let e' := asIso (comparison.app (op V))
  have natural := comparison.naturality incl
  have equal : P.map incl = e.hom ≫ Q.map incl ≫ e'.inv := by
    apply (cancel_mono e'.hom).1
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using natural
  have top : g ⁻¹ᵁ U = ⊤ := g.preimage_opensRange
  have principal : g ⁻¹ᵁ V = PrimeSpectrum.basicOpen (f r) := by
    change g ⁻¹ᵁ (U ⊓ PrimeSpectrum.basicOpen r) = _
    rw [Scheme.Hom.preimage_inf, top, top_inf_eq]
    exact SpecMap_preimage_basicOpen f r
  letI : IsLocalizedModule (Submonoid.powers r) (Q.map incl).hom :=
    restrictedPrincipalMap_localizes f N ((principalLocalizations_iff_tilde N).2 localTilde) r
      (g ⁻¹ᵁ U) (g ⁻¹ᵁ V) ((TopologicalSpace.Opens.map g.base).op.map incl) top principal
  change IsLocalizedModule (Submonoid.powers r) (P.map incl).hom
  rw [equal]
  letI : IsLocalizedModule (Submonoid.powers r) ((Q.map incl).hom.comp e.toLinearEquiv.toLinearMap) :=
    IsLocalizedModule.of_linearEquiv_right (Submonoid.powers r) (Q.map incl).hom e.toLinearEquiv
  exact IsLocalizedModule.of_linearEquiv (Submonoid.powers r)
    ((Q.map incl).hom.comp e.toLinearEquiv.toLinearMap) e'.symm.toLinearEquiv


/-- A module sheaf is presented by a module over the section ring of an
affine open when its actual restriction is the associated module sheaf.
This is the affine module presentation from the opening of Appendix B. The given open is affine
and its canonical spectrum map supplies the restriction. -/
def HasTildeOn {X : Scheme.{u}} (M : X.Modules) {U : X.Opens} (affine : IsAffineOpen U) : Prop :=
  (tilde.functor Γ(X, U)).essImage (M.restrict affine.fromSpec)

/-- Tilde presentations restrict along any inclusion of affine opens.
This API restricts a presentation from the opening of Appendix B along an inclusion of affine
opens, using the induced ring map. -/
theorem HasTildeOn.restrict {X : Scheme.{u}} {M : X.Modules} {U V : X.Opens}
    {hU : IsAffineOpen U} {hV : IsAffineOpen V} (inside : V ≤ U) (localTilde : HasTildeOn M hU) :
    HasTildeOn M hV := by
  let f := X.presheaf.map (homOfLE inside).op
  have composite : Spec.map f ≫ hU.fromSpec = hV.fromSpec :=
    hU.map_fromSpec hV (homOfLE inside).op
  haveI : IsOpenImmersion (Spec.map f ≫ hU.fromSpec) := by rw [composite]; infer_instance
  letI : IsOpenImmersion (Spec.map f) := IsOpenImmersion.of_comp _ hU.fromSpec
  obtain ⟨N, ⟨e⟩⟩ := localTilde
  refine ⟨(ModuleCat.extendScalars f.hom).obj N, ⟨?_⟩⟩
  exact ((tildeRestrictIso f).app N).symm ≪≫ (restrictFunctor (Spec.map f)).mapIso e ≪≫
    ((restrictFunctorComp (Spec.map f) hU.fromSpec).app M).symm ≪≫
    (restrictFunctorCongr composite).app M

private theorem localizedRestriction_congr (P : (Spec R).Opensᵒᵖ ⥤ ModuleCat.{u} R)
    (S : Submonoid R) {U V U' V' : (Spec R).Opens}
    (inside : V ≤ U) (inside' : V' ≤ U') (upper : U = U') (lower : V = V')
    (h : IsLocalizedModule S (P.map (homOfLE inside).op).hom) :
    IsLocalizedModule S (P.map (homOfLE inside').op).hom := by
  subst U' V'
  exact h

/-- On an affine open of a spectrum with a tilde presentation, its section
map to the intersection with an ambient principal open is localization.
This is the localization used on opens and double intersections in Appendix B.3. It uses the
given tilde presentation on the affine open. -/
theorem affineOpen_sections_localize (M : (Spec R).Modules) {U : (Spec R).Opens}
    (hU : IsAffineOpen U) (presentation : HasTildeOn M hU) (r : R) :
    IsLocalizedModule (Submonoid.powers r)
      (((modulesSpecToSheaf.obj M).val.map
        (homOfLE (inf_le_left : U ⊓ PrimeSpectrum.basicOpen r ≤ U)).op).hom) := by
  let f : R ⟶ Γ(Spec R, U) := (Scheme.Spec.preimage hU.fromSpec).unop
  have same : Spec.map f = hU.fromSpec := Scheme.Spec.map_preimage _
  haveI : IsOpenImmersion (Spec.map f) := by rw [same]; infer_instance
  obtain ⟨N, ⟨e⟩⟩ := presentation
  have localTilde : (tilde.functor Γ(Spec R, U)).essImage (M.restrict (Spec.map f)) :=
    ⟨N, ⟨e ≪≫ ((restrictFunctorCongr same).app M).symm⟩⟩
  have range : (Spec.map f).opensRange = U :=
    (Opens.ext (congrArg (fun g : Spec Γ(Spec R, U) ⟶ Spec R => Set.range g) same)).trans
      hU.opensRange_fromSpec
  exact localizedRestriction_congr (modulesSpecToSheaf.obj M).val (Submonoid.powers r)
    inf_le_left inf_le_left range (congrArg (· ⊓ PrimeSpectrum.basicOpen r) range)
    (affineChart_sections_localize f M localTilde r)


/-- An associated module presentation on the image of an open immersion
pulls back to the same affine open in the source.
This is the restriction comparison in Appendix B.3 for an open immersion. Its image-open
presentation is over the structure ring isomorphic to that of the source open. -/
theorem HasTildeOn.pullbackImage {X Y : Scheme.{u}} {g : Y ⟶ X} [IsOpenImmersion g]
    {M : X.Modules} {V : Y.Opens} {hV : IsAffineOpen V}
    {hImage : IsAffineOpen (g ''ᵁ V)} (presentation : HasTildeOn M hImage) :
    HasTildeOn (M.restrict g) hV := by
  let f := (g.appIso V).hom
  have same : Spec.map f ≫ hImage.fromSpec = hV.fromSpec ≫ g := by
    rw [show f = g.appLE (g ''ᵁ V) V (g.preimage_image_eq V).ge from g.appIso_hom' V]
    exact IsAffineOpen.SpecMap_appLE_fromSpec g hImage hV (g.preimage_image_eq V).ge
  letI : IsIso f := (g.appIso V).isIso_hom
  letI : IsOpenImmersion (Spec.map f) := inferInstance
  obtain ⟨N, ⟨e⟩⟩ := presentation
  refine ⟨(ModuleCat.extendScalars f.hom).obj N, ⟨?_⟩⟩
  exact ((tildeRestrictIso f).app N).symm ≪≫ (restrictFunctor (Spec.map f)).mapIso e ≪≫
    ((restrictFunctorComp (Spec.map f) hImage.fromSpec).app M).symm ≪≫
    (restrictFunctorCongr same).app M ≪≫ (restrictFunctorComp hV.fromSpec g).app M


/-- Local tilde presentations on a finite principal cover of a spectrum
give a tilde presentation on the entire spectrum.
This proves the affine case of Appendix B.3. The principal cover and its local presentations
come from the affine communication lemma. -/
theorem affineTilde_of_finite_principalCover (M : (Spec R).Modules) {ι : Type u}
    [Fintype ι] [DecidableEq ι] (r : ι → R)
    (cover : (⨆ i, PrimeSpectrum.basicOpen (r i)) = ⊤)
    (presentations : ∀ i, HasTildeOn M (IsAffineOpen.Spec_basicOpen (r i))) :
    (tilde.functor R).essImage M := by
  apply (principalLocalizations_iff_tilde M).1
  intro f
  let P := modulesSpecToSheaf.obj M
  let U (i : ι) : (Spec R).Opens := PrimeSpectrum.basicOpen (r i)
  let W : (Spec R).Opens := PrimeSpectrum.basicOpen f
  have localizes := isLocalizedModule_sectionsRestrict_of_pairwise U W P (Submonoid.powers f) (by
    intro j
    cases j with
    | single i => exact affineOpen_sections_localize M _ (presentations i) f
    | pair i j =>
      have affine : IsAffineOpen (X := Spec R) (U i ⊓ U j) := by
        change IsAffineOpen (X := Spec R) (PrimeSpectrum.basicOpen (r i) ⊓ PrimeSpectrum.basicOpen (r j))
        rw [← PrimeSpectrum.basicOpen_mul]
        exact IsAffineOpen.Spec_basicOpen _
      have present : HasTildeOn M affine := (presentations i).restrict inf_le_left
      have intersection :
          (U i ⊓ U j) ⊓ W = (U i ⊓ W) ⊓ (U j ⊓ W) := by
        calc
          _ = (U i ⊓ U j) ⊓ (W ⊓ W) := by rw [inf_idem]
          _ = _ := by ac_rfl
      exact localizedRestriction_congr P.val (Submonoid.powers f) inf_le_left _ rfl intersection
        (affineOpen_sections_localize M affine present f))
  have intersections : (⨆ i, U i ⊓ W) = W := by rw [← iSup_inf_eq, cover, top_inf_eq]
  exact localizedRestriction_congr P.val (Submonoid.powers f) _ le_top cover intersections localizes

/-- Having a tilde presentation on each affine open defines a quasi-coherent module sheaf. We
keep the statement in the form used in Appendix B. The separate comparison
`isQuasiCoherentModule_iff_mathlib` identifies it with the existing site-theoretic criterion.
This is the module condition in the opening of Appendix B. It quantifies over all affine opens
of an arbitrary scheme. -/
def IsQuasiCoherentModule {X : Scheme.{u}} (M : X.Modules) : Prop :=
  ∀ U : X.affineOpens, HasTildeOn M U.property

/-- Affine-local presentations on some affine open cover.
This is the cover condition equivalent to the definition in the opening of Appendix B. The cover
is arbitrary in the universe of the scheme. -/
def HasAffineTildeCover {X : Scheme.{u}} (M : X.Modules) : Prop :=
  ∃ (I : Type u) (U : I → X.affineOpens), (⨆ i, (U i : X.Opens)) = ⊤ ∧
    ∀ i, HasTildeOn M (U i).property

private theorem hasTildeOn_congr {X : Scheme.{u}} {M : X.Modules} {U V : X.Opens}
    (same : U = V) {hU : IsAffineOpen U} {hV : IsAffineOpen V} (value : HasTildeOn M hU) :
    HasTildeOn M hV := by
  subst V
  exact value

/-- The affine-local presentation on one affine cover extends to every affine open.
This is the main module criterion from the opening of Appendix B. Finite principal refinements
are constructed for each affine open in the proof. -/
theorem isQuasiCoherentModule_iff_affineCover {X : Scheme.{u}} (M : X.Modules) :
    IsQuasiCoherentModule M ↔ HasAffineTildeCover M := by
  constructor
  · intro each
    exact ⟨X.affineOpens, id, iSup_affineOpens_eq_top X, each⟩
  · rintro ⟨ι, U, cover, localTilde⟩ V
    apply of_affine_open_cover (P := fun V => HasTildeOn M V.property) U cover V _ _ localTilde
    · intro W f present
      exact present.restrict (X.basicOpen_le f)
    · intro W s spanning presents
      classical
      let g := W.property.fromSpec
      let N := M.restrict g
      have generating : Ideal.span (Set.range (fun f : s => f.val)) = ⊤ :=
        (Subtype.range_val (s := (s : Set Γ(X, W)))) ▸ spanning
      have covers : (⨆ f : s, PrimeSpectrum.basicOpen f.val) = ⊤ :=
        PrimeSpectrum.iSup_basicOpen_eq_top_iff.mpr generating
      apply affineTilde_of_finite_principalCover N _ covers
      intro f
      let Z := PrimeSpectrum.basicOpen f.val
      have hZ := IsAffineOpen.Spec_basicOpen f.val
      have hImage : IsAffineOpen (g ''ᵁ Z) := hZ.image_of_isOpenImmersion g
      have image : g ''ᵁ Z = X.basicOpen f.val := W.property.fromSpec_image_basicOpen f.val
      have present : HasTildeOn M hImage := hasTildeOn_congr image.symm (presents f)
      exact HasTildeOn.pullbackImage (g := g) (hV := hZ) (hImage := hImage) present


/-- An associated module sheaf on a spectrum is quasi-coherent on every affine open.
This API builds the associated module sheaf case of Appendix B. It takes a single tilde
presentation on the ambient spectrum. -/
theorem isQuasiCoherentModule_of_tilde (M : (Spec R).Modules)
    (presentation : (tilde.functor R).essImage M) : IsQuasiCoherentModule M := by
  intro U
  let f : R ⟶ Γ(Spec R, U.1) := (Scheme.Spec.preimage U.property.fromSpec).unop
  have same : Spec.map f = U.property.fromSpec := Scheme.Spec.map_preimage _
  haveI : IsOpenImmersion (Spec.map f) := by rw [same]; infer_instance
  obtain ⟨N, ⟨e⟩⟩ := presentation
  refine ⟨(ModuleCat.extendScalars f.hom).obj N, ⟨?_⟩⟩
  exact ((tildeRestrictIso f).app N).symm ≪≫
    (restrictFunctor (Spec.map f)).mapIso e ≪≫ (restrictFunctorCongr same).app M


end

end SHIGURE.SchemeDescent
