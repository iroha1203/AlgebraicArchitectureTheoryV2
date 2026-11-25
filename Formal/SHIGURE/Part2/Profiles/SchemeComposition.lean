import Formal.SHIGURE.Part2.Profiles.Composition
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic

/-!
# Composition morphisms of the support-profile charts

The product projections supply the universal pair of coefficient rows in
Theorem 4.6. Evaluating the finite sums in the global sections of the product
and applying Lemma B.2 gives the scheme morphism.

## Implementation notes

The product projections are already universal points with coefficients in
the global sections of the product. A tensor product presentation of the
coordinate ring would require comparing its spectrum with the scheme
product. Using the projections and Lemma B.2 gives the morphism and its
calculation on all test schemes. The affine comparison evaluates it on the
same coordinates used for the filtered colimit.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

namespace SHIGURE.Copying.SupportProfile

universe u

variable {k : Type u} [CommRing k]
variable {X Y Z W : Type u}
variable {F : SupportProfile X Y} {H : SupportProfile Y Z} {J : SupportProfile Z W}
variable {T T' : Over (Spec (CommRingCat.of k))}

/-- Maps from any test scheme to one affine chart are represented by bounded rows
in the global sections of that scheme. -/
def pointRowsEquiv (F : SupportProfile X Y) (T : Over (Spec (CommRingCat.of k))) :
    (T ⟶ F.chart k) ≃ F.RowsAt Γ(T.left, ⊤) := by
  letI := globalSectionsAlgebra T
  exact (specOverPointEquiv T (F.CoordinateRing k)).trans F.homRowsEquiv

/-- Restriction along a map of test schemes pulls back all coefficient sections. -/
theorem pointRowsEquiv_precomp (F : SupportProfile X Y) (f : T' ⟶ T) (p : T ⟶ F.chart k) :
    letI := globalSectionsAlgebra T
    letI := globalSectionsAlgebra T'
    F.pointRowsEquiv T' (f ≫ p) = mapCoefficients (globalSectionsMap f) (F.pointRowsEquiv T p) := by
  letI := globalSectionsAlgebra T
  letI := globalSectionsAlgebra T'
  change F.homRowsEquiv (specOverPointEquiv T' (F.CoordinateRing k) (f ≫ p)) = _
  rw [specOverPointEquiv_precomp, homRowsEquiv_natural]
  rfl

/-- The closed immersion that enlarges a chart preserves the represented rows over any test scheme. -/
theorem pointRowsEquiv_transition {F G : SupportProfile X Y} (h : F ≤ G) (p : T ⟶ F.chart k) :
    G.pointRowsEquiv T (p ≫ transition h) = enlargeRows h (F.pointRowsEquiv T p) := by
  letI := globalSectionsAlgebra T
  change G.homRowsEquiv (specOverPointEquiv T (G.CoordinateRing k) (p ≫ specOverMap (transitionRingMap h))) =
    enlargeRows h (F.homRowsEquiv (specOverPointEquiv T (F.CoordinateRing k) p))
  rw [specOverPointEquiv_postcomp, homRowsEquiv_transition]

/-- The scheme morphism of Theorem 4.6 from the product of two profiles to the composite profile. -/
def chartComp (F : SupportProfile X Y) (H : SupportProfile Y Z) :
    F.chart k ⨯ H.chart k ⟶ (compProfile F H).chart k :=
  ((compProfile F H).pointRowsEquiv _).symm <|
    compRows (F.pointRowsEquiv _ prod.fst) (H.pointRowsEquiv _ prod.snd)

/-- The coefficients of the composition morphism on the product are the composition
of the coefficients of its two projections. -/
theorem chartComp_rows (F : SupportProfile X Y) (H : SupportProfile Y Z) :
    (compProfile F H).pointRowsEquiv (F.chart k ⨯ H.chart k) (chartComp F H) =
      compRows (F.pointRowsEquiv _ prod.fst) (H.pointRowsEquiv _ prod.snd) :=
  Equiv.apply_symm_apply _ _

/-- The scheme morphism of Theorem 4.6 evaluates equation (4.2) on the coefficients
of any pair of chart points. -/
theorem chartComp_points (p : T ⟶ F.chart k) (q : T ⟶ H.chart k) :
    (compProfile F H).pointRowsEquiv T (prod.lift p q ≫ chartComp F H) =
      compRows (F.pointRowsEquiv T p) (H.pointRowsEquiv T q) := by
  letI := globalSectionsAlgebra (F.chart k ⨯ H.chart k)
  letI := globalSectionsAlgebra T
  rw [pointRowsEquiv_precomp, chartComp_rows, compRows_natural,
    ← pointRowsEquiv_precomp, ← pointRowsEquiv_precomp,
    prod.lift_fst, prod.lift_snd]

/-- Enlarging the input charts commutes with the composition morphism. -/
theorem chartComp_transition {F' : SupportProfile X Y} {H' : SupportProfile Y Z}
    (hF : F ≤ F') (hH : H ≤ H') :
    prod.map (transition (k := k) hF) (transition hH) ≫ chartComp F' H' =
      chartComp F H ≫ transition (compProfile_mono hF hH) := by
  have hmap : prod.map (transition (k := k) hF) (transition hH) =
      prod.lift (prod.fst ≫ transition hF) (prod.snd ≫ transition hH) := by
    apply prod.hom_ext <;> simp
  apply ((compProfile F' H').pointRowsEquiv _).injective
  rw [pointRowsEquiv_transition, chartComp_rows, hmap, chartComp_points,
    pointRowsEquiv_transition, pointRowsEquiv_transition, compRows_enlarge]

/-- The identity of copying maps taken as a point of the identity profile. -/
def chartIdentity (T : Over (Spec (CommRingCat.of k))) (X : Type u) :
    T ⟶ (identityProfile X).chart k :=
  ((identityProfile X).pointRowsEquiv T).symm (identityRows Γ(T.left, ⊤) X)

/-- The identity chart point simplifies to the unit row at each source state. -/
@[simp]
theorem pointRowsEquiv_chartIdentity (T : Over (Spec (CommRingCat.of k))) (X : Type u) :
    (identityProfile X).pointRowsEquiv T (chartIdentity T X) = identityRows Γ(T.left, ⊤) X :=
  Equiv.apply_symm_apply _ _

/-- The composition morphism has the identity chart point as a left unit. -/
theorem chartComp_identity_source (p : T ⟶ F.chart k) :
    prod.lift (chartIdentity T X) p ≫ chartComp (identityProfile X) F ≫
      transition (le_of_eq (compProfile_identity_source F)) = p := by
  apply (F.pointRowsEquiv T).injective
  rw [← Category.assoc, pointRowsEquiv_transition, chartComp_points, pointRowsEquiv_chartIdentity]
  exact Subtype.ext (compRows_identity_source _)

/-- The composition morphism has the identity chart point as a right unit. -/
theorem chartComp_identity_target (p : T ⟶ F.chart k) :
    prod.lift p (chartIdentity T Y) ≫ chartComp F (identityProfile Y) ≫
      transition (le_of_eq (compProfile_identity_target F)) = p := by
  apply (F.pointRowsEquiv T).injective
  rw [← Category.assoc, pointRowsEquiv_transition, chartComp_points, pointRowsEquiv_chartIdentity]
  exact Subtype.ext (compRows_identity_target _)

/-- The two composites of three chart points agree after the canonical profile comparison. -/
theorem chartComp_assoc (p : T ⟶ F.chart k) (q : T ⟶ H.chart k) (r : T ⟶ J.chart k) :
    prod.lift (prod.lift p q ≫ chartComp F H) r ≫ chartComp (compProfile F H) J ≫
      transition (le_of_eq (compProfile_assoc F H J)) =
    prod.lift p (prod.lift q r ≫ chartComp H J) ≫ chartComp F (compProfile H J) := by
  apply ((compProfile F (compProfile H J)).pointRowsEquiv T).injective
  rw [← Category.assoc, pointRowsEquiv_transition, chartComp_points, chartComp_points,
    chartComp_points, chartComp_points]
  exact Subtype.ext (compRows_assoc _ _ _)

/-- Composition of chart points commutes with pulling their coefficient sections back
along any base-preserving map of test schemes. -/
theorem chartComp_precomp (f : T' ⟶ T) (p : T ⟶ F.chart k) (q : T ⟶ H.chart k) :
    f ≫ (prod.lift p q ≫ chartComp F H) = prod.lift (f ≫ p) (f ≫ q) ≫ chartComp F H := by
  apply ((compProfile F H).pointRowsEquiv T').injective
  letI := globalSectionsAlgebra T
  letI := globalSectionsAlgebra T'
  rw [pointRowsEquiv_precomp, chartComp_points, chartComp_points, pointRowsEquiv_precomp,
    pointRowsEquiv_precomp, compRows_natural]

/-- Under the Γ–Spec adjunction a spectrum map is given by the ring map followed by the affine section isomorphism. -/
private theorem specGlobalHom_specMap {A R : CommRingCat.{u}} (f : A ⟶ R) :
    specGlobalHom (Spec.map f) = f ≫ (Scheme.ΓSpecIso R).inv := by
  have hi : specGlobalHom (𝟙 (Spec R)) = (Scheme.ΓSpecIso R).inv := by
    change ((ΓSpec.adjunction.homEquiv (Spec R) (op R)).symm (𝟙 (Spec R))).unop = _
    rw [Adjunction.homEquiv_counit, (Scheme.Γ.rightOp).map_id (Spec R), Category.id_comp,
      ΓSpec.adjunction_counit_app]
    rfl
  rw [← Category.id_comp (Spec.map f), specGlobalHom_postcomp, hi]

variable {R : Type u} [CommRing R] [Algebra k R]

/-- The affine section isomorphism in the direction from the test algebra to global sections. -/
private def affineSectionsMap :
    letI := globalSectionsAlgebra (specOver (k := k) R)
    R →ₐ[k] Γ((specOver (k := k) R).left, ⊤) := by
  letI := globalSectionsAlgebra (specOver (k := k) R)
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom, fun c => ?_⟩
  change (Scheme.ΓSpecIso (CommRingCat.of R)).inv (algebraMap k R c) =
    (specGlobalHom (Spec.map (CommRingCat.ofHom (algebraMap k R)))).hom c
  rw [specGlobalHom_specMap]
  rfl

/-- The general test-scheme coordinates restrict to the affine coordinates under the section isomorphism. -/
private theorem pointRowsEquiv_affine (F : SupportProfile X Y) (p : specOver R ⟶ F.chart k) :
    letI := globalSectionsAlgebra (specOver (k := k) R)
    F.pointRowsEquiv (specOver R) p =
      mapCoefficients affineSectionsMap (F.affinePointRowsEquiv p) := by
  letI := globalSectionsAlgebra (specOver (k := k) R)
  let f : F.CoordinateRing k →ₐ[k] R := F.homRowsEquiv.symm (F.affinePointRowsEquiv p)
  have hp : specOverMap f = p := by
    apply F.affinePointRowsEquiv.injective
    rw [affinePointRowsEquiv_specOverMap, Equiv.apply_symm_apply]
  rw [← hp, affinePointRowsEquiv_specOverMap]
  change F.homRowsEquiv
    (specOverPointEquiv (specOver (k := k) R) (F.CoordinateRing k) (specOverMap f)) = _
  rw [← homRowsEquiv_natural]
  congr 1
  ext z
  rw [specOverPointEquiv_apply, specOverMap_left]
  exact congrArg
    (fun g : CommRingCat.of (F.CoordinateRing k) ⟶ Γ((specOver (k := k) R).left, ⊤) => g z)
    (specGlobalHom_specMap (CommRingCat.ofHom f.toRingHom))

/-- At every affine test algebra, the composition morphism is equation (4.2)
on the same row coordinates used for the filtered colimit in Theorem 4.6. -/
theorem chartComp_affinePoints (p : specOver R ⟶ F.chart k) (q : specOver R ⟶ H.chart k) :
    (compProfile F H).affinePointRowsEquiv (prod.lift p q ≫ chartComp F H) =
      compRows (F.affinePointRowsEquiv p) (H.affinePointRowsEquiv q) := by
  letI := globalSectionsAlgebra (specOver (k := k) R)
  have h := chartComp_points p q
  rw [pointRowsEquiv_affine, pointRowsEquiv_affine, pointRowsEquiv_affine, ← compRows_natural] at h
  apply Subtype.ext
  apply Subtype.ext
  funext x
  apply Finsupp.ext
  intro z
  have he := congrArg
    (fun a : (compProfile F H).RowsAt Γ((specOver (k := k) R).left, ⊤) => a.val.val x z) h
  change (Scheme.ΓSpecIso (CommRingCat.of R)).inv
      (((compProfile F H).affinePointRowsEquiv (prod.lift p q ≫ chartComp F H)).val.val x z) =
    (Scheme.ΓSpecIso (CommRingCat.of R)).inv
      ((compRows (F.affinePointRowsEquiv p) (H.affinePointRowsEquiv q)).val.val x z) at he
  exact ((ConcreteCategory.isIso_iff_bijective
    (Scheme.ΓSpecIso (CommRingCat.of R)).inv).mp inferInstance).injective he

end SHIGURE.Copying.SupportProfile
