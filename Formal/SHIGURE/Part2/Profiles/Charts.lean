import Formal.SHIGURE.Part2.Profiles.Coordinates
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Support-profile charts and closed immersions

Definition 4.5 uses the spectrum of the coefficient presentation. For an
inclusion of profiles the coordinate ring map sets the added generators to
zero. This realizes enlargement of a profile on points by the same rows.

## Implementation notes

The affine point correspondence uses full faithfulness of `Spec` to land
directly in the test algebra. Specializing the global-sections route of
Lemma B.2 would carry the `ΓSpecIso` through the point diagram. The
comparison in `SchemeComposition` supplies that identification for the
composition morphism, where points of general test schemes are needed.
-/

open AlgebraicGeometry CategoryTheory MvPolynomial Opposite

noncomputable section

namespace SHIGURE.Copying.SupportProfile

universe u

variable {X Y : Type u} {F G : SupportProfile X Y}
variable {k R S : Type u} [CommRing k] [CommRing R] [CommRing S]
variable [Algebra k R] [Algebra k S]

/-- The coordinate ring of the affine chart for a support profile. -/
abbrev CoordinateRing (k : Type u) [CommRing k] (F : SupportProfile X Y) :=
  (F.presentation k).CoordinateRing

/-- The affine scheme of Definition 4.5, with its structural map to the base. -/
def chart (k : Type u) [CommRing k] (F : SupportProfile X Y) : Over (Spec (CommRingCat.of k)) :=
  specOver (F.CoordinateRing k)

/-- The scheme defined by the support equations is affine. -/
theorem isAffine_chart (F : SupportProfile X Y) : IsAffine (F.chart k).left := by
  change IsAffine (Spec (CommRingCat.of (F.CoordinateRing k)))
  infer_instance

/-- Maps from the coordinate ring correspond to the coefficient rows of the chart. -/
def homRowsEquiv (F : SupportProfile X Y) :
    (F.CoordinateRing k →ₐ[k] R) ≃ F.RowsAt R :=
  ((F.presentation k).assignmentEquiv R).symm.trans F.assignmentRowsEquiv

/-- On the allowed support, the row coefficient is the image of the corresponding generator. -/
theorem homRowsEquiv_apply (f : F.CoordinateRing k →ₐ[k] R) (x : X) (y : F x) :
    (F.homRowsEquiv f).val.val x y.val = f ((F.presentation k).generator ⟨x, y⟩) :=
  F.rowOfValues_apply_mem _ x y

/-- On disallowed indices, the row coefficients evaluated from an algebra map vanish. -/
theorem homRowsEquiv_apply_notMem (f : F.CoordinateRing k →ₐ[k] R) (x : X) (y : Y)
    (h : y ∉ F x) : (F.homRowsEquiv f).val.val x y = 0 :=
  F.rowOfValues_apply_notMem _ x y h

/-- Map of coefficients of a chart in a larger algebra over the same base. -/
def mapCoefficients (g : R →ₐ[k] S) (a : F.RowsAt R) : F.RowsAt S :=
  ⟨mapRows g.toRingHom a.val, by
    intro x
    change (mapRowCoefficients g.toRingHom (a.val.val x)).support ⊆ F x
    unfold mapRowCoefficients
    exact Finsupp.support_mapRange.trans (a.property x)⟩

/-- Evaluation of the equations commutes with maps of coefficient algebras. -/
theorem homRowsEquiv_natural (f : F.CoordinateRing k →ₐ[k] R) (g : R →ₐ[k] S) :
    F.homRowsEquiv (g.comp f) = mapCoefficients g (F.homRowsEquiv f) := by
  apply Subtype.ext
  apply Subtype.ext
  funext x
  apply Finsupp.ext
  intro y
  classical
  change (F.homRowsEquiv (g.comp f)).val.val x y =
    mapRowCoefficients g.toRingHom ((F.homRowsEquiv f).val.val x) y
  rw [mapRowCoefficients_apply]
  by_cases hy : y ∈ F x
  · rw [F.homRowsEquiv_apply f x ⟨y, hy⟩]
    exact F.homRowsEquiv_apply (g.comp f) x ⟨y, hy⟩
  · rw [homRowsEquiv_apply_notMem _ _ _ hy, homRowsEquiv_apply_notMem _ _ _ hy, map_zero]

/-- A family of rows with allowed support (F) also defines rows at any larger profile. -/
def enlargeRows (h : F ≤ G) (a : F.RowsAt R) : G.RowsAt R :=
  ⟨a.val, fun x => (a.property x).trans (h x)⟩

/-- The coordinate homomorphism for enlarging a profile in Definition 4.5. -/
def transitionRingMap (h : F ≤ G) : G.CoordinateRing k →ₐ[k] F.CoordinateRing k :=
  G.homRowsEquiv.symm <| enlargeRows h <| F.homRowsEquiv (AlgHom.id k (F.CoordinateRing k))

/-- The transition homomorphism preserves retained coordinates. -/
theorem transitionRingMap_generator (h : F ≤ G) (x : X) (y : F x) :
    transitionRingMap (k := k) h ((G.presentation k).generator ⟨x, ⟨y.val, h x y.property⟩⟩) =
      (F.presentation k).generator ⟨x, y⟩ := by
  rw [← G.homRowsEquiv_apply]
  rw [transitionRingMap, Equiv.apply_symm_apply]
  exact F.homRowsEquiv_apply (AlgHom.id k (F.CoordinateRing k)) x y

/-- Newly added coordinates are sent to zero by the transition homomorphism. -/
theorem transitionRingMap_generator_notMem (h : F ≤ G) (x : X) (y : G x)
    (hy : y.val ∉ F x) : transitionRingMap (k := k) h ((G.presentation k).generator ⟨x, y⟩) = 0 := by
  rw [← G.homRowsEquiv_apply]
  rw [transitionRingMap, Equiv.apply_symm_apply]
  exact F.homRowsEquiv_apply_notMem (AlgHom.id k (F.CoordinateRing k)) x y.val hy

/-- Every generator of the smaller chart is the image of its retained coordinate. -/
theorem transitionRingMap_surjective (h : F ≤ G) :
    Function.Surjective (transitionRingMap (k := k) h) := by
  let q : MvPolynomial F.Coordinate k →ₐ[k] F.CoordinateRing k :=
    Ideal.Quotient.mkₐ k (F.presentation k).lawIdeal
  let g : MvPolynomial F.Coordinate k →ₐ[k] G.CoordinateRing k :=
    aeval (fun v => (G.presentation k).generator ⟨v.1, ⟨v.2.val, h v.1 v.2.property⟩⟩)
  have heq : (transitionRingMap h).comp g = q := by
    apply MvPolynomial.algHom_ext
    rintro ⟨x, y⟩
    simp only [AlgHom.comp_apply, g, aeval_X]
    exact transitionRingMap_generator h x y
  intro a
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  exact ⟨g p, DFunLike.congr_fun heq p⟩

/-- The transition from a chart to a chart with enlarged support. -/
def transition (h : F ≤ G) : F.chart k ⟶ G.chart k :=
  specOverMap (transitionRingMap h)

/-- Enlarging the allowed support is a closed immersion in Definition 4.5. -/
theorem isClosedImmersion_transition (h : F ≤ G) :
    IsClosedImmersion (transition (k := k) h).left := by
  rw [transition, specOverMap_left]
  exact IsClosedImmersion.spec_of_surjective _ (transitionRingMap_surjective h)

/-- Enlarging the profile of a point preserves each coefficient, including the zero coefficients. -/
theorem homRowsEquiv_transition (h : F ≤ G) (f : F.CoordinateRing k →ₐ[k] R) :
    G.homRowsEquiv (f.comp (transitionRingMap h)) = enlargeRows h (F.homRowsEquiv f) := by
  rw [homRowsEquiv_natural, transitionRingMap, Equiv.apply_symm_apply]
  exact congrArg (enlargeRows h) <| by
    simpa only [AlgHom.comp_id] using
      (homRowsEquiv_natural (AlgHom.id k (F.CoordinateRing k)) f).symm

/-- The affine test points are represented by the algebra maps themselves. -/
private theorem specOverMap_bijective {A : Type u} [CommRing A] [Algebra k A] :
    Function.Bijective (specOverMap : (A →ₐ[k] R) → (specOver R ⟶ specOver A)) := by
  constructor
  · intro f g h
    apply AlgHom.coe_ringHom_injective
    exact congrArg CommRingCat.Hom.hom <| Spec.map_injective <|
      congrArg (fun a : specOver R ⟶ specOver A => a.left) h
  · intro f
    obtain ⟨g, hg⟩ := Scheme.Spec.map_surjective
      (X := op (CommRingCat.of R)) (Y := op (CommRingCat.of A)) f.left
    have hleft : Spec.map g.unop = f.left := hg
    have hw : CommRingCat.ofHom (algebraMap k A) ≫ g.unop =
        CommRingCat.ofHom (algebraMap k R) := by
      apply Spec.map_injective
      rw [Spec.map_comp, hleft]
      exact Over.w f
    let a : A →ₐ[k] R :=
      ⟨g.unop.hom, fun c => congrArg (fun q : CommRingCat.of k ⟶ CommRingCat.of R => q c) hw⟩
    exact ⟨a, Over.OverMorphism.ext hleft⟩

/-- Evaluation of the chart at an affine test algebra, as a relative scheme Hom. -/
def affinePointRowsEquiv (F : SupportProfile X Y) :
    (specOver R ⟶ F.chart k) ≃ F.RowsAt R :=
  (Equiv.ofBijective specOverMap specOverMap_bijective).symm.trans F.homRowsEquiv

/-- The point induced by a coordinate algebra map has the coefficients read from that map. -/
theorem affinePointRowsEquiv_specOverMap (f : F.CoordinateRing k →ₐ[k] R) :
    F.affinePointRowsEquiv (specOverMap f) = F.homRowsEquiv f :=
  congrArg F.homRowsEquiv ((Equiv.ofBijective specOverMap specOverMap_bijective).symm_apply_apply f)

/-- Contravariance of the relative spectrum on a composite of coefficient maps. -/
private theorem specOverMap_comp {A : Type u} [CommRing A] [Algebra k A]
    (f : A →ₐ[k] R) (g : R →ₐ[k] S) :
    specOverMap (g.comp f) = specOverMap g ≫ specOverMap f := by
  apply Over.OverMorphism.ext
  exact Spec.map_comp (CommRingCat.ofHom f.toRingHom) (CommRingCat.ofHom g.toRingHom)

/-- The point map of a closed immersion of charts keeps the same coefficients. -/
theorem affinePointRowsEquiv_transition (h : F ≤ G) (p : specOver R ⟶ F.chart k) :
    G.affinePointRowsEquiv (p ≫ transition h) = enlargeRows h (F.affinePointRowsEquiv p) := by
  obtain ⟨f, rfl⟩ := specOverMap_bijective.surjective p
  rw [transition, ← specOverMap_comp, affinePointRowsEquiv_specOverMap,
    affinePointRowsEquiv_specOverMap, homRowsEquiv_transition]

/-- Precomposition along a map of test algebras applies it to every coefficient. -/
theorem affinePointRowsEquiv_natural (g : R →ₐ[k] S) (p : specOver R ⟶ F.chart k) :
    F.affinePointRowsEquiv (specOverMap g ≫ p) = mapCoefficients g (F.affinePointRowsEquiv p) := by
  obtain ⟨f, rfl⟩ := specOverMap_bijective.surjective p
  rw [← specOverMap_comp, affinePointRowsEquiv_specOverMap,
    affinePointRowsEquiv_specOverMap, homRowsEquiv_natural]

end SHIGURE.Copying.SupportProfile
