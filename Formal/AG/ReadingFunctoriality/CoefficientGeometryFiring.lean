import Formal.AG.ReadingFunctoriality.FiniteExamples
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.Category.Ring.Under.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Over
import Mathlib.CategoryTheory.Limits.Shapes.FiniteMultiequalizer

/-!
# Finite coefficient-geometry sheafification

This module constructs the algebra-valued sheafification instances required by
the R9f coefficient-geometry firing.  The actual finite reference site has a
large object type because an architecture context stores carrier types, but its
readable isomorphism classes have a small finite-profile classification.

## Implementation notes

`ContextCode` records every finite Atom subset jointly read by one support,
together with the nonempty and readable states of the axis and observable
carriers.  A readable restriction preserves this code in the appropriate
direction, and equality of codes reconstructs restrictions in both directions.
Consequently the thin context category is essentially small.

Sheafification is constructed on Mathlib's small model and transported back
along the site equivalence.  The topology itself is unchanged.  The target
category `AATCommAlgCat` is an under-category; local concrete-category data
identifies its concrete forgetful functor with `Under.forget` followed by the
commutative-ring forgetful functor, allowing the standard left-exact
sheafification construction to apply.

For coefficient extension, the same finite classification is strengthened to
an actual finite matching argument.  The site is transported to the thin
skeleton of its small model.  Every covering sieve there has finitely many
arrows and relations, so its matching multicospan is finite.  Flat coefficient
extension preserves that finite limit, and `HasSheafCompose` transports back
to the original finite-site topology.

The firing geometry uses the single affine chart at `finiteBase`.  Its
semantic core generates the constant equation `2`, and the identity raw
presentation realizes that equation through the Part 3 bridge theorem.  To
detect the coefficient change, two maps to `ZMod 2` are constructed on the
actual pushout defining the changed sheafified section ring: both agree on the
source section ring, while the new coefficient `Polynomial.X` is sent to `0`
and `1`.  They kill the generated target law ideal, descend to the lawful
closed subscheme, and show that the canonical lawful-locus map is not an
isomorphism.
-/

noncomputable section

namespace AAT.AG.ReadingFunctorialityFinite

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open scoped AlgebraicGeometry

private local instance : Fintype FiniteModel.FiniteAtom where
  elems := FiniteModel.FiniteAtom.all.toFinset
  complete atom := by
    simpa using FiniteModel.FiniteAtom.mem_all atom

private structure ContextCode where
  support : Finset (Finset FiniteModel.FiniteAtom)
  axisNonempty : Prop
  axisReadable : Prop
  observableNonempty : Prop
  observableReadable : Prop

private noncomputable def contextSupportCode (W : finiteSite.category) :
    Finset (Finset FiniteModel.FiniteAtom) := by
  classical
  exact Finset.univ.filter fun p => ∃ s : W.ctx.Support,
    ∀ a ∈ p, W.ctx.minimal.supportReads s a

private noncomputable def contextCode (W : finiteSite.category) : ContextCode where
  support := contextSupportCode W
  axisNonempty := Nonempty W.ctx.Axis
  axisReadable := ∃ x : W.ctx.Axis, W.ctx.minimal.axisReads x
  observableNonempty := Nonempty W.ctx.Observable
  observableReadable := ∃ x : W.ctx.Observable, W.ctx.minimal.observableReads x

private theorem supportCode_mono {W V : finiteSite.category}
    (h : finiteSite.contextPreorder.le W.ctx V.ctx) :
    contextSupportCode W ⊆ contextSupportCode V := by
  classical
  rcases h with ⟨f, hf⟩
  intro p hp
  rw [contextSupportCode, Finset.mem_filter] at hp ⊢
  refine ⟨hp.1, ?_⟩
  rcases hp.2 with ⟨s, hs⟩
  exact ⟨f.supportMap s, fun a ha => hf.1 (hs a ha)⟩

private theorem axisNonempty_mono {W V : finiteSite.category}
    (h : finiteSite.contextPreorder.le W.ctx V.ctx) :
    Nonempty W.ctx.Axis → Nonempty V.ctx.Axis := by
  rcases h with ⟨f, _hf⟩
  rintro ⟨x⟩
  exact ⟨f.axisMap x⟩

private theorem axisReadable_mono {W V : finiteSite.category}
    (h : finiteSite.contextPreorder.le W.ctx V.ctx) :
    (∃ x : W.ctx.Axis, W.ctx.minimal.axisReads x) →
      ∃ x : V.ctx.Axis, V.ctx.minimal.axisReads x := by
  rcases h with ⟨f, hf⟩
  rintro ⟨x, hx⟩
  exact ⟨f.axisMap x, hf.2.1 hx⟩

private theorem observableNonempty_anti {W V : finiteSite.category}
    (h : finiteSite.contextPreorder.le W.ctx V.ctx) :
    Nonempty V.ctx.Observable → Nonempty W.ctx.Observable := by
  rcases h with ⟨f, _hf⟩
  rintro ⟨x⟩
  exact ⟨f.observableRestrict x⟩

private theorem observableReadable_anti {W V : finiteSite.category}
    (h : finiteSite.contextPreorder.le W.ctx V.ctx) :
    (∃ x : V.ctx.Observable, V.ctx.minimal.observableReads x) →
      ∃ x : W.ctx.Observable, W.ctx.minimal.observableReads x := by
  rcases h with ⟨f, hf⟩
  rintro ⟨x, hx⟩
  exact ⟨f.observableRestrict x, hf.2.2.1 hx⟩

private theorem contextCode_eq_of_mutual {W V : finiteSite.category}
    (hWV : finiteSite.contextPreorder.le W.ctx V.ctx)
    (hVW : finiteSite.contextPreorder.le V.ctx W.ctx) :
    contextCode W = contextCode V := by
  unfold contextCode
  congr 1
  · exact Finset.Subset.antisymm (supportCode_mono hWV) (supportCode_mono hVW)
  · exact propext ⟨axisNonempty_mono hWV, axisNonempty_mono hVW⟩
  · exact propext ⟨axisReadable_mono hWV, axisReadable_mono hVW⟩
  · exact propext ⟨observableNonempty_anti hVW, observableNonempty_anti hWV⟩
  · exact propext ⟨observableReadable_anti hVW, observableReadable_anti hWV⟩

private theorem contextLe_of_code_eq {W V : finiteSite.category}
    (hcode : contextCode W = contextCode V) :
    finiteSite.contextPreorder.le W.ctx V.ctx := by
  classical
  have hsupport : ∀ s : W.ctx.Support, ∃ t : V.ctx.Support,
      ∀ a, W.ctx.minimal.supportReads s a →
        V.ctx.minimal.supportReads t a := by
    intro s
    let p : Finset FiniteModel.FiniteAtom :=
      Finset.univ.filter fun a => W.ctx.minimal.supportReads s a
    have hpW : p ∈ contextSupportCode W := by
      rw [contextSupportCode, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, s, ?_⟩
      intro a ha
      exact (Finset.mem_filter.mp ha).2
    have hpV : p ∈ contextSupportCode V := by
      have hs := congrArg ContextCode.support hcode
      change contextSupportCode W = contextSupportCode V at hs
      rw [← hs]
      exact hpW
    rw [contextSupportCode, Finset.mem_filter] at hpV
    rcases hpV.2 with ⟨t, ht⟩
    refine ⟨t, fun a ha => ht a ?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩
  let supportMap : W.ctx.Support → V.ctx.Support :=
    fun s => Classical.choose (hsupport s)
  have hsupportMap : ∀ {s a}, W.ctx.minimal.supportReads s a →
      V.ctx.minimal.supportReads (supportMap s) a := by
    intro s a hread
    exact Classical.choose_spec (hsupport s) a hread
  have haxisNonempty : Nonempty W.ctx.Axis → Nonempty V.ctx.Axis := by
    have h := congrArg ContextCode.axisNonempty hcode
    change (Nonempty W.ctx.Axis : Prop) = Nonempty V.ctx.Axis at h
    exact fun hW => h ▸ hW
  have haxisReadable : (∃ x : W.ctx.Axis, W.ctx.minimal.axisReads x) →
      ∃ x : V.ctx.Axis, V.ctx.minimal.axisReads x := by
    have h := congrArg ContextCode.axisReadable hcode
    change (∃ x : W.ctx.Axis, W.ctx.minimal.axisReads x) =
      (∃ x : V.ctx.Axis, V.ctx.minimal.axisReads x) at h
    exact fun hW => h ▸ hW
  let axisMap : W.ctx.Axis → V.ctx.Axis := fun x =>
    if hx : W.ctx.minimal.axisReads x then
      Classical.choose (haxisReadable ⟨x, hx⟩)
    else Classical.choice (haxisNonempty ⟨x⟩)
  have haxisMap : ∀ {x}, W.ctx.minimal.axisReads x →
      V.ctx.minimal.axisReads (axisMap x) := by
    intro x hx
    simp only [axisMap, dif_pos hx]
    exact Classical.choose_spec (haxisReadable ⟨x, hx⟩)
  have hobservableNonempty : Nonempty V.ctx.Observable → Nonempty W.ctx.Observable := by
    have h := congrArg ContextCode.observableNonempty hcode
    change (Nonempty W.ctx.Observable : Prop) = Nonempty V.ctx.Observable at h
    exact fun hV => h.symm ▸ hV
  have hobservableReadable :
      (∃ x : V.ctx.Observable, V.ctx.minimal.observableReads x) →
        ∃ x : W.ctx.Observable, W.ctx.minimal.observableReads x := by
    have h := congrArg ContextCode.observableReadable hcode
    change (∃ x : W.ctx.Observable, W.ctx.minimal.observableReads x) =
      (∃ x : V.ctx.Observable, V.ctx.minimal.observableReads x) at h
    exact fun hV => h.symm ▸ hV
  let observableRestrict : V.ctx.Observable → W.ctx.Observable := fun x =>
    if hx : V.ctx.minimal.observableReads x then
      Classical.choose (hobservableReadable ⟨x, hx⟩)
    else Classical.choice (hobservableNonempty ⟨x⟩)
  have hobservableRestrict : ∀ {x}, V.ctx.minimal.observableReads x →
      W.ctx.minimal.observableReads (observableRestrict x) := by
    intro x hx
    simp only [observableRestrict, dif_pos hx]
    exact Classical.choose_spec (hobservableReadable ⟨x, hx⟩)
  let f : Site.ContextMorphism W.ctx V.ctx := {
    supportMap := supportMap
    axisMap := axisMap
    observableRestrict := observableRestrict }
  refine ⟨f, ?_⟩
  exact ⟨hsupportMap, haxisMap, hobservableRestrict,
    fun hread => V.ctx.supportReads_objectFamily hread⟩

private theorem contextCode_eq_of_isomorphic (W V : finiteSite.category)
    (h : (CategoryTheory.isIsomorphicSetoid finiteSite.category).r W V) :
    contextCode W = contextCode V := by
  rcases h with ⟨i⟩
  exact contextCode_eq_of_mutual (leOfHom i.hom) (leOfHom i.inv)

private noncomputable def skeletonContextCode :
    Skeleton finiteSite.category → ContextCode :=
  Quotient.lift contextCode contextCode_eq_of_isomorphic

private theorem skeletonContextCode_injective :
    Function.Injective skeletonContextCode := by
  intro q r
  refine Quotient.inductionOn₂ q r ?_
  intro W V hcode
  apply Quotient.sound
  refine ⟨{
    hom := homOfLE (contextLe_of_code_eq hcode)
    inv := homOfLE (contextLe_of_code_eq hcode.symm) }⟩

private theorem finiteSite_essentiallySmall :
    EssentiallySmall.{0} finiteSite.category := by
  apply CategoryTheory.essentiallySmall_iff_of_thin.mpr
  exact small_of_injective skeletonContextCode_injective

private noncomputable instance finiteSiteEssentiallySmall :
    EssentiallySmall.{0} finiteSite.category :=
  finiteSite_essentiallySmall

private abbrev coefficientBase (k : Type) [CommRing k] :=
  CommRingCat.of (ULift.{0} k)

private abbrev CoefficientUnder (k : Type) [CommRing k] :=
  Under (coefficientBase k)

private instance coefficientUnderHomFunLike {k : Type} [CommRing k]
    (A B : CoefficientUnder k) : FunLike (A ⟶ B) A B where
  coe f := f.right
  coe_injective' f g h := by
    ext x
    exact congrFun h x

private instance coefficientUnderConcreteCategory {k : Type} [CommRing k] :
    ConcreteCategory (CoefficientUnder k) (fun A B => A ⟶ B) where
  hom := id
  ofHom := id
  hom_ofHom _ := rfl
  ofHom_hom _ := rfl
  id_apply _ := rfl
  comp_apply _ _ _ := rfl

private instance coefficientUnderForgetPreservesLimits
    {k : Type} [CommRing k] :
    PreservesLimits (forget (CoefficientUnder k)) := by
  change PreservesLimits
    (Under.forget (coefficientBase k) ⋙ forget CommRingCat.{0})
  infer_instance

private instance coefficientUnderForgetReflectsIsomorphisms
    {k : Type} [CommRing k] :
    (forget (CoefficientUnder k)).ReflectsIsomorphisms := by
  change (Under.forget (coefficientBase k) ⋙
    forget CommRingCat.{0}).ReflectsIsomorphisms
  infer_instance

private instance coefficientUnderForgetPreservesFilteredColimits
    {k : Type} [CommRing k] :
    PreservesFilteredColimits (forget (CoefficientUnder k)) := by
  change PreservesFilteredColimits
    (Under.forget (coefficientBase k) ⋙ forget CommRingCat.{0})
  infer_instance

private noncomputable def finiteCommRingHasSheafify
    (k : Type) [CommRing k] :
    HasSheafify finiteSite.topology
      (LawAlgebra.AATCommAlgCat.{0, 0} k) := by
  letI : EssentiallySmall.{0} finiteSite.category :=
    finiteSite_essentiallySmall
  exact CategoryTheory.hasSheafifyEssentiallySmallSite _ _

/-- Algebra-valued sheafification for integer coefficients on the finite reference site. -/
noncomputable def finiteIntHasSheafify :
    HasSheafify finiteSite.topology
      (LawAlgebra.AATCommAlgCat.{0, 0} Int) :=
  finiteCommRingHasSheafify Int

/-- Algebra-valued sheafification for polynomial coefficients on the finite reference site. -/
noncomputable def finitePolynomialIntHasSheafify :
    HasSheafify finiteSite.topology
      (LawAlgebra.AATCommAlgCat.{0, 0} (Polynomial Int)) :=
  finiteCommRingHasSheafify (Polynomial Int)

attribute [local instance] finiteIntHasSheafify finitePolynomialIntHasSheafify

private noncomputable instance finiteSiteSmallModelThin :
    Quiver.IsThin (SmallModel.{0} finiteSite.category) := fun X Y => by
  constructor
  intro f g
  apply (equivSmallModel finiteSite.category).inverse.map_injective
  exact Subsingleton.elim _ _

private noncomputable def finiteSiteSmallEquivalence :
    finiteSite.category ≌
      ThinSkeleton (SmallModel.{0} finiteSite.category) :=
  (equivSmallModel finiteSite.category).trans
    (ThinSkeleton.equivalence (SmallModel.{0} finiteSite.category)).symm

private noncomputable def smallSkeletonContextCode :
    Skeleton (SmallModel.{0} finiteSite.category) → ContextCode :=
  fun W => skeletonContextCode
    ((equivSmallModel finiteSite.category).skeletonEquiv.symm W)

private noncomputable instance finiteContextCode : Finite ContextCode := by
  apply Finite.of_injective
    (fun c : ContextCode =>
      (c.support, c.axisNonempty, c.axisReadable,
        c.observableNonempty, c.observableReadable))
  intro c d h
  rcases c with ⟨cs, ca, car, co, cor⟩
  rcases d with ⟨ds, da, dar, dob, dor⟩
  simp only [Prod.mk.injEq] at h
  simp_all

private theorem smallSkeletonContextCode_injective :
    Function.Injective smallSkeletonContextCode :=
  skeletonContextCode_injective.comp
    (equivSmallModel finiteSite.category).skeletonEquiv.symm.injective

private noncomputable instance finiteSmallSkeleton :
    Finite (ThinSkeleton (SmallModel.{0} finiteSite.category)) :=
  Finite.of_injective smallSkeletonContextCode
    smallSkeletonContextCode_injective

private noncomputable abbrev finiteTopologySmall :
    GrothendieckTopology
      (ThinSkeleton (SmallModel.{0} finiteSite.category)) :=
  finiteSiteSmallEquivalence.inverse.inducedTopology finiteSite.topology

private noncomputable instance finiteCoverArrow
    {C : Type} [SmallCategory C] [FinCategory C]
    (J : GrothendieckTopology C) (X : C) (S : J.Cover X) :
    Finite S.Arrow := by
  apply Finite.of_injective
    (fun I : S.Arrow => (⟨I.Y, I.f⟩ : Σ Y : C, Y ⟶ X))
  intro I K h
  cases I
  cases K
  simp_all

private noncomputable instance finiteCoverArrowRelation
    {C : Type} [SmallCategory C] [FinCategory C]
    (J : GrothendieckTopology C) (X : C) (S : J.Cover X)
    (I K : S.Arrow) : Finite (I.Relation K) := by
  apply Finite.of_injective
    (fun r : I.Relation K =>
      (⟨r.Z, (r.g₁, r.g₂)⟩ :
        Σ Z : C, (Z ⟶ I.Y) × (Z ⟶ K.Y)))
  intro r s h
  cases r
  cases s
  simp only [Sigma.mk.inj_iff] at h
  rcases h with ⟨hZ, hpair⟩
  cases hZ
  cases hpair
  rfl

private noncomputable instance finiteCoverRelation
    {C : Type} [SmallCategory C] [FinCategory C]
    (J : GrothendieckTopology C) (X : C) (S : J.Cover X) :
    Finite S.Relation := by
  apply Finite.of_surjective
    (fun t : Σ I : S.Arrow, Σ K : S.Arrow, I.Relation K =>
      (⟨t.2.2⟩ : S.Relation))
  intro r
  exact ⟨⟨r.fst, r.snd, r.r⟩, by cases r; rfl⟩

private noncomputable instance coefficientExtensionSmallHasSheafCompose :
    finiteTopologySmall.HasSheafCompose
      (intPolynomialFlatChange.coefficientExtension :
        LawAlgebra.AATCommAlgCat.{0, 0} Int ⥤
          LawAlgebra.AATCommAlgCat.{0, 0} (Polynomial Int)) := by
  letI : ∀ (X : ThinSkeleton (SmallModel.{0} finiteSite.category))
      (S : finiteTopologySmall.Cover X)
      (P : (ThinSkeleton (SmallModel.{0} finiteSite.category))ᵒᵖ ⥤
        LawAlgebra.AATCommAlgCat.{0, 0} Int),
      PreservesLimit (S.index P).multicospan
        (intPolynomialFlatChange.coefficientExtension :
          LawAlgebra.AATCommAlgCat.{0, 0} Int ⥤
            LawAlgebra.AATCommAlgCat.{0, 0} (Polynomial Int)) := by
    intro X S P
    classical
    letI : Fintype S.Arrow := Fintype.ofFinite S.Arrow
    letI : Fintype S.Relation := Fintype.ofFinite S.Relation
    letI : Fintype S.shape.L := by
      change Fintype S.Arrow
      exact Fintype.ofFinite S.Arrow
    letI : Fintype S.shape.R := by
      change Fintype S.Relation
      exact Fintype.ofFinite S.Relation
    letI : DecidableEq S.shape.L := Classical.decEq _
    letI : DecidableEq S.shape.R := Classical.decEq _
    letI : FinCategory (WalkingMulticospan S.shape) := by
      infer_instance
    infer_instance
  exact CategoryTheory.hasSheafCompose_of_preservesMulticospan _ _

/-- The flat extension from integers to integer polynomials preserves sheaves
on the actual finite reference-site topology.  Its matching limits are finite
after transport to the finite thin skeleton and are preserved by flat
coefficient extension. -/
noncomputable instance coefficientExtension_hasSheafCompose :
    finiteSite.topology.HasSheafCompose
      (intPolynomialFlatChange.coefficientExtension :
        LawAlgebra.AATCommAlgCat.{0, 0} Int ⥤
          LawAlgebra.AATCommAlgCat.{0, 0} (Polynomial Int)) :=
  finiteSiteSmallEquivalence.hasSheafCompose
    finiteSite.topology finiteTopologySmall _

/-- The changed finite affine chart is the canonical coefficient pullback. -/
noncomputable def coefficientSectionSpecBaseChangeIso_fires :
    LawAlgebra.architectureChartSpec
        (coefficientRaw.baseChange intPolynomialFlatChange.hom) finiteBase ≅
      pullback
        (AlgebraicGeometry.Scheme.Spec.map
          (coefficientRaw.toRingedSite.structureSheaf.val.obj
            (op finiteBase)).hom.op)
        (AlgebraicGeometry.Scheme.Spec.map
          (CommRingCat.ofHom intPolynomialFlatChange.liftedHom).op) :=
  LawAlgebra.RawAmbientRestrictionSystem.sheafifiedSectionSpecBaseChangeIso
    coefficientRaw intPolynomialFlatChange finiteBase

/-! ## Concrete coefficient geometry -/

private def coefficientProductObject
    (X Y : finiteSite.category) : finiteSite.category :=
  Site.ContextCategoryObject.of finiteSite.contextPreorder
    (Site.productContext X.ctx Y.ctx)

private noncomputable def coefficientProductLeft
    (X Y : finiteSite.category) : coefficientProductObject X Y ⟶ X :=
  homOfLE (Site.productContextFiniteMeet.meet_le_left X.ctx Y.ctx)

private noncomputable def coefficientProductRight
    (X Y : finiteSite.category) : coefficientProductObject X Y ⟶ Y :=
  homOfLE (Site.productContextFiniteMeet.meet_le_right X.ctx Y.ctx)

private theorem finiteSitePresheaf_isSheaf_of_bijective
    (P : CategoryTheory.Functor finiteSite.categoryᵒᵖ Type)
    (hbij : ∀ {X Y : finiteSite.category} (f : X ⟶ Y),
      Function.Bijective (P.map f.op)) :
    Presieve.IsSheaf finiteSite.topology P := by
  rw [Site.AATSite.topology, Site.AATGrothendieckTopology]
  rw [Precoverage.isSheaf_toGrothendieck_iff]
  intro X Y f R hR
  rcases hR with ⟨F, rfl⟩
  intro family hfamily
  classical
  rcases F.admissible.atomSupportCoverage
      FiniteModel.FiniteAtom.componentA (Or.inl rfl) with ⟨i, hi⟩
  let patchObject := Site.ContextCategoryObject.of finiteSite.contextPreorder
    (F.patch i)
  let Q := coefficientProductObject Y patchObject
  let q : Q ⟶ Y := coefficientProductLeft Y patchObject
  let qpatch : Q ⟶ patchObject := coefficientProductRight Y patchObject
  have hq : (Sieve.generate F.presieve).pullback f q := by
    change Sieve.generate F.presieve (q ≫ f)
    have hinclusion : Sieve.generate F.presieve
        (homOfLE (F.inclusion i)) :=
      Sieve.le_generate F.presieve _ (Presieve.ofArrows.mk i)
    have hcomp := (Sieve.generate F.presieve).downward_closed hinclusion qpatch
    convert hcomp using 1
  rcases (hbij q).2 (family q hq) with ⟨global, hglobal⟩
  refine ⟨global, ?_, ?_⟩
  · intro Z g hg
    let PQ := coefficientProductObject Z Q
    let pz : PQ ⟶ Z := coefficientProductLeft Z Q
    let pq : PQ ⟶ Q := coefficientProductRight Z Q
    apply (hbij pz).1
    have hcompat := hfamily pz pq hg hq (Subsingleton.elim _ _)
    calc
      P.map pz.op (P.map g.op global) =
          P.map pq.op (P.map q.op global) := by
            rw [← FunctorToTypes.map_comp_apply,
              ← FunctorToTypes.map_comp_apply]
            congr 2
      _ = P.map pq.op (family q hq) := by rw [hglobal]
      _ = P.map pz.op (family g hg) := hcompat.symm
  · intro other hother
    apply (hbij q).1
    rw [hglobal]
    exact hother q hq

private theorem coefficientRawRestriction_bijective
    {X Y : finiteSite.category} (f : X ⟶ Y) :
    Function.Bijective (coefficientRaw.toPresheaf.map f.op).right := by
  change Function.Bijective
    ((coefficientRaw.restrictionStable f).quotientDesc)
  let q := (coefficientRaw.restrictionStable f).quotientDesc
  let r := (coefficientRaw.restrictionStable f).restriction.polynomialMap
  have hr : r.comp r = RingHom.id _ := by
    have hsign :
        (LawAlgebra.FiniteExamples.RawPresheaf.gauge X *
          LawAlgebra.FiniteExamples.RawPresheaf.gauge Y) *
        (LawAlgebra.FiniteExamples.RawPresheaf.gauge X *
          LawAlgebra.FiniteExamples.RawPresheaf.gauge Y) = 1 := by
      calc
        _ = (LawAlgebra.FiniteExamples.RawPresheaf.gauge X *
              LawAlgebra.FiniteExamples.RawPresheaf.gauge X) *
            (LawAlgebra.FiniteExamples.RawPresheaf.gauge Y *
              LawAlgebra.FiniteExamples.RawPresheaf.gauge Y) := by ring
        _ = 1 := by
          rw [LawAlgebra.FiniteExamples.RawPresheaf.gauge_sq,
            LawAlgebra.FiniteExamples.RawPresheaf.gauge_sq, one_mul]
    apply MvPolynomial.ringHom_ext
    · intro z
      simp [r, LawAlgebra.TypedCoordinateRestriction.polynomialMap]
    · intro i
      cases i
      change
        (LawAlgebra.FiniteExamples.RawPresheaf.coordinateRestriction f).polynomialMap
            ((LawAlgebra.FiniteExamples.RawPresheaf.coordinateRestriction f).polynomialMap
              (MvPolynomial.X ())) =
          MvPolynomial.X ()
      rw [LawAlgebra.FiniteExamples.RawPresheaf.coordinateRestriction_polynomialMap_X,
        map_mul]
      erw [LawAlgebra.TypedCoordinateRestriction.polynomialMap_C]
      rw [LawAlgebra.FiniteExamples.RawPresheaf.coordinateRestriction_polynomialMap_X]
      rw [← mul_assoc]
      erw [← MvPolynomial.C.map_mul]
      rw [hsign, map_one, one_mul]
  have hinv : ∀ x, q (q x) = x := by
    intro x
    refine Quotient.inductionOn x ?_
    intro p
    change q (q ((coefficientRaw.relationFamily Y).quotientMap p)) =
      (coefficientRaw.relationFamily Y).quotientMap p
    rw [LawAlgebra.RestrictionStableStructuralRelations.quotientDesc_mk]
    change q ((coefficientRaw.relationFamily Y).quotientMap
      ((coefficientRaw.restrictionStable f).restriction.polynomialMap p)) =
        (coefficientRaw.relationFamily Y).quotientMap p
    rw [LawAlgebra.RestrictionStableStructuralRelations.quotientDesc_mk]
    change (coefficientRaw.relationFamily Y).quotientMap
        ((r.comp r) p) =
      (coefficientRaw.relationFamily Y).quotientMap p
    rw [hr]
    rfl
  exact ⟨fun x y h => by
      calc
        x = q (q x) := (hinv x).symm
        _ = q (q y) := congrArg q h
        _ = y := hinv y,
    fun y => ⟨q y, hinv y⟩⟩

private theorem coefficientRawPresheaf_isSheaf :
    Presheaf.IsSheaf finiteSite.topology coefficientRaw.toPresheaf := by
  intro E
  apply finiteSitePresheaf_isSheaf_of_bijective
  intro X Y f
  letI : IsIso (coefficientRaw.toPresheaf.map f.op) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact coefficientRawRestriction_bijective f
  change Function.Bijective (fun g : E ⟶
    coefficientRaw.toPresheaf.obj (op Y) =>
      g ≫ coefficientRaw.toPresheaf.map f.op)
  constructor
  · intro a b h
    exact (cancel_mono (coefficientRaw.toPresheaf.map f.op)).mp h
  · intro b
    exact ⟨b ≫ inv (coefficientRaw.toPresheaf.map f.op), by simp⟩

/-- The concrete source geometry is the actual single-affine chart at the finite base context. -/
noncomputable def coefficientScheme :
    LawAlgebra.StandardArchitectureScheme coefficientRaw :=
  LawAlgebra.StandardArchitectureScheme.singleAffine coefficientRaw finiteBase

private theorem coefficientRawRestriction_id
    (W : finiteSite.category) (x : coefficientRaw.rawAlgebra W) :
    (coefficientRaw.restrictionStable (𝟙 W)).quotientDesc x = x := by
  have h := congrArg (fun q => q x) (coefficientRaw.quotientDesc_id W)
  simpa using h

private theorem coefficientRawRestriction_comp
    {W₀ W₁ W₂ : finiteSite.category}
    (f : W₀ ⟶ W₁) (g : W₁ ⟶ W₂)
    (x : coefficientRaw.rawAlgebra W₂) :
    (coefficientRaw.restrictionStable (f ≫ g)).quotientDesc x =
      (coefficientRaw.restrictionStable f).quotientDesc
        ((coefficientRaw.restrictionStable g).quotientDesc x) := by
  have h := congrArg (fun q => q x) (coefficientRaw.quotientDesc_comp f g)
  simpa [RingHom.comp_apply] using h

/-- The coefficient firing core generates the proper equation `(2)` from its selected atom. -/
noncomputable def coefficientSemanticCore :
    LawAlgebra.SemanticLawEquationWitnessIdealCore finiteSite where
  Observable W := coefficientRaw.rawAlgebra W
  observableCommRing W := inferInstance
  restrict f := (coefficientRaw.restrictionStable f).quotientDesc
  restrict_id := coefficientRawRestriction_id
  restrict_comp := coefficientRawRestriction_comp
  violationWitness W _ atom :=
    match atom with
    | FiniteModel.FiniteAtom.componentA => 2
    | _ => 0
  violationWitness_restrict := by
    intro source target f lawIndex atom
    cases atom <;> simp only [map_ofNat, map_zero]
  supportAtom := FiniteModel.FiniteAtom.componentA
  supportLawIndex := PUnit.unit
  supportLawIndex_required := FiniteModel.lawUniverse_required PUnit.unit

/-- The semantic observable ring is identified with the selected raw quotient objectwise. -/
noncomputable def coefficientBridge :
    LawAlgebra.SemanticLawEquationSchemeBridge
      coefficientRaw coefficientSemanticCore where
  toRawPresentation W := RingEquiv.refl (coefficientRaw.rawAlgebra W)

/-- The identity presentation is restriction-natural and its canonical units are invertible. -/
theorem coefficientBridge_valid :
    LawAlgebra.IsSemanticLawEquationSchemeBridge
      coefficientRaw coefficientSemanticCore coefficientBridge where
  restriction_natural := by
    intro source target f x
    have hn := coefficientRaw.toRingedSite.canonical.naturality f.op
    have ha := congrArg (fun q => q.right x) hn
    change
      (coefficientRaw.toRingedSite.canonical.app (op source)).right
          ((coefficientRaw.restrictionStable f).quotientDesc x) =
        (coefficientRaw.toRingedSite.structureSheaf.val.map f.op).right
          ((coefficientRaw.toRingedSite.canonical.app (op target)).right x)
    simpa only [CommRingCat.comp_apply,
      LawAlgebra.RawAmbientRestrictionSystem.toRingedSite_raw] using ha
  presentation_stable W := {
    canonical_isIso := by
      haveI : IsIso (CategoryTheory.toSheafify
          finiteSite.topology coefficientRaw.toPresheaf) :=
        CategoryTheory.isIso_toSheafify finiteSite.topology
          coefficientRawPresheaf_isSheaf
      change IsIso ((CategoryTheory.toSheafify
        finiteSite.topology coefficientRaw.toPresheaf).app (op W))
      infer_instance }

/-- The concrete bridge realizes the semantic-core ideal sheaf on the source chart. -/
theorem coefficientSemanticCore_realized :
    LawAlgebra.SemanticCoreIdealSheafRealized coefficientRaw coefficientScheme
      coefficientSemanticCore coefficientBridge :=
  LawAlgebra.semanticCoreIdealSheaf_realized coefficientRaw coefficientScheme
    coefficientSemanticCore coefficientBridge coefficientBridge_valid

/-- The realized source equation agrees with its transported equation on the changed chart. -/
theorem coefficientSemanticCore_baseChangedChart
    (j : coefficientScheme.atlas.Index)
    (i : finiteSite.lawUniverse.Index) :
    let R' :=
      LawAlgebra.ClosedEquationalLawReading.baseChangeOfSemanticCore
        coefficientRaw coefficientScheme coefficientSemanticCore
          coefficientBridge intPolynomialFlatChange
    let hR' :=
      (LawAlgebra.ClosedEquationalLawReading.baseChangeOfSemanticCore_valid
        coefficientRaw coefficientScheme coefficientSemanticCore
          coefficientBridge intPolynomialFlatChange).witness_compatible
    let j' := cast
      (coefficientScheme.baseChangedAtlas_Index
        coefficientRaw intPolynomialFlatChange).symm j
    Scheme.IdealSheafData.comap
        (Scheme.IdealSheafData.ofIdealTop
          (X := (coefficientScheme.atlas.chart j).domain)
          (Ideal.map
            (AlgebraicGeometry.Scheme.ΓSpecIso
              (LawAlgebra.SheafifiedSectionRing coefficientRaw
                (coefficientScheme.atlas.chart j).context)).inv.hom
            (Ideal.map
              (coefficientBridge.toSheafifiedSection
                (coefficientScheme.atlas.chart j).context)
              (coefficientSemanticCore.lawWitnessIdeal
                (coefficientScheme.atlas.chart j).context i))))
        (coefficientScheme.baseChangedChartMap
          coefficientRaw intPolynomialFlatChange j) =
      Scheme.IdealSheafData.comap
        (LawAlgebra.lawWitnessIdealSheaf
          (coefficientRaw.baseChange intPolynomialFlatChange.hom)
          (coefficientScheme.baseChange
            coefficientRaw intPolynomialFlatChange)
          R' hR' i (Set.mem_univ i))
        ((coefficientScheme.baseChangedAtlas
          coefficientRaw intPolynomialFlatChange).chart j').map :=
  LawAlgebra.semanticCoreLawWitnessIdeal_baseChangedChart
    coefficientRaw coefficientScheme coefficientSemanticCore
      coefficientBridge coefficientBridge_valid intPolynomialFlatChange j i

open AAT.AG.LawAlgebra

private abbrev targetRaw :=
  coefficientRaw.baseChange intPolynomialFlatChange.hom

private abbrev targetScheme :=
  coefficientScheme.baseChange coefficientRaw intPolynomialFlatChange

private abbrev targetReading :=
  ClosedEquationalLawReading.baseChangeOfSemanticCore coefficientRaw
    coefficientScheme coefficientSemanticCore coefficientBridge
      intPolynomialFlatChange

private abbrev targetReadingValid :=
  ClosedEquationalLawReading.baseChangeOfSemanticCore_valid coefficientRaw
    coefficientScheme coefficientSemanticCore coefficientBridge
      intPolynomialFlatChange

private abbrev targetRequired :=
  ClosedEquationalLawReading.baseChangeOfSemanticCore_requiredClosed coefficientRaw
    coefficientScheme coefficientSemanticCore coefficientBridge
      intPolynomialFlatChange

private abbrev targetLawIdeal : targetScheme.underlying.IdealSheafData :=
  lawGeneratedIdealSheaf targetRaw targetScheme targetReading
    targetReadingValid targetRequired

private abbrev targetLawful : Scheme :=
  lawfulClosedSubscheme targetRaw targetScheme targetReading
    targetReadingValid targetRequired

private abbrev targetImmersion : targetLawful ⟶ targetScheme.underlying :=
  lawfulClosedImmersion targetRaw targetScheme targetReading
    targetReadingValid targetRequired

private def coeffEval (z : ZMod 2) : Polynomial Int →+* ZMod 2 :=
  Polynomial.eval₂RingHom (Int.castRingHom (ZMod 2)) z

private def ambientEval (z : ZMod 2) :
    MvPolynomial Unit (Polynomial Int) →+* ZMod 2 :=
  MvPolynomial.eval₂Hom (coeffEval z) (fun _ => 1)

private theorem target_JStruct_le_ker (z : ZMod 2) :
    (targetRaw.relationFamily finiteBase).JStruct ≤
      RingHom.ker (ambientEval z) := by
  rw [StructuralRelationFamily.JStruct]
  apply Ideal.span_le.mpr
  rintro p ⟨r, rfl⟩
  cases r
  simp [RawAmbientRestrictionSystem.baseChange, ambientEval, coeffEval,
    LawAlgebra.StructuralRelationFamily.baseChange, coefficientRaw,
    LawAlgebra.FiniteExamples.RawPresheaf.system,
    LawAlgebra.FiniteExamples.RawPresheaf.relationFamily]
  have hx := MvPolynomial.eval₂Hom_X'
    (Polynomial.eval₂RingHom (Int.castRingHom (ZMod 2)) z)
    (fun _ : Unit => (1 : ZMod 2)) ()
  apply sub_eq_zero.mpr
  exact hx

private def targetRawEval (z : ZMod 2) :
    targetRaw.rawAlgebra finiteBase →+* ZMod 2 :=
  Ideal.Quotient.lift _ (ambientEval z) (target_JStruct_le_ker z)

private def sourceIndex : coefficientScheme.atlas.Index :=
  StandardArchitectureScheme.singleAffineIndex coefficientRaw finiteBase

private def targetIndex : targetScheme.atlas.Index :=
  cast (coefficientScheme.baseChangedAtlas_Index coefficientRaw
    intPolynomialFlatChange).symm sourceIndex

private noncomputable def changedChartMap :
    (targetScheme.atlas.chart targetIndex).domain ⟶ targetScheme.underlying :=
  (targetScheme.atlas.chart targetIndex).map

private theorem changedChartMap_surjective :
    Function.Surjective changedChartMap := by
  letI : Subsingleton coefficientScheme.atlas.Index :=
    StandardArchitectureScheme.singleAffine_index_subsingleton
      coefficientRaw finiteBase
  letI : Subsingleton targetScheme.atlas.Index := by
    change Subsingleton coefficientScheme.atlas.Index
    infer_instance
  intro x
  rcases targetScheme.atlasValid.covers x with ⟨j, y, hy⟩
  have hj : j = targetIndex := Subsingleton.elim _ _
  subst j
  exact ⟨y, hy⟩

private theorem changedChartMap_isIso : IsIso changedChartMap := by
  letI : IsOpenImmersion changedChartMap :=
    (targetScheme.atlasValid.chart_valid targetIndex).isOpenImmersion
  letI : Epi changedChartMap.base :=
    ConcreteCategory.epi_of_surjective _ changedChartMap_surjective
  apply IsOpenImmersion.isIso

attribute [local instance] changedChartMap_isIso

private local instance targetSchemeIsAffine : IsAffine targetScheme.underlying := by
  letI : IsAffine (targetScheme.atlas.chart targetIndex).domain :=
    (targetScheme.atlas.chart targetIndex).domain_isAffine
  exact IsAffine.of_isIso (inv changedChartMap)

private noncomputable instance coefficientCanonicalIsIso :
    IsIso (coefficientRaw.toRingedSite.canonical.app (op finiteBase)) :=
  coefficientBridge_valid.presentation_stable finiteBase |>.canonical_isIso

private noncomputable def sourceRawEvalInt :
    coefficientRaw.rawAlgebra finiteBase →+* Int :=
  LawAlgebra.FiniteExamples.RawPresheaf.quotientOneEval.comp
    (coefficientRaw.restrictionStable
      LawAlgebra.FiniteExamples.RawPresheaf.leftToBase).quotientDesc

private theorem sourceRawEvalInt_intCast (z : Int) : sourceRawEvalInt z = z := by
  change LawAlgebra.FiniteExamples.RawPresheaf.quotientOneEval
    ((coefficientRaw.restrictionStable
      LawAlgebra.FiniteExamples.RawPresheaf.leftToBase).quotientDesc z) = z
  simp

private noncomputable def sourceRawEvalAlg :
    coefficientRaw.rawAlgebra finiteBase →ₐ[Int] Int where
  __ := sourceRawEvalInt
  commutes' := sourceRawEvalInt_intCast

private noncomputable def sourceEvalAlg :
    SheafifiedSectionRing coefficientRaw finiteBase →ₐ[Int] ZMod 2 :=
  (Algebra.ofId Int (ZMod 2)).comp
    (sourceRawEvalAlg.comp
      (coefficientBridge_valid.presentation_stable finiteBase).comparison.toAlgHom)

private abbrev oldObject :=
  coefficientRaw.toRingedSite.structureSheaf.val.obj (op finiteBase)

private abbrev newObject :=
  targetRaw.toRingedSite.structureSheaf.val.obj (op finiteBase)

private noncomputable def sourceEval :
    oldObject.right ⟶ CommRingCat.of (ZMod 2) :=
  CommRingCat.ofHom sourceEvalAlg.toRingHom

private noncomputable def coeffEvalCat (z : ZMod 2) :
    CommRingCat.of (ULift (Polynomial Int)) ⟶ CommRingCat.of (ZMod 2) :=
  CommRingCat.ofHom ((coeffEval z).comp ULift.ringEquiv.toRingHom)

private theorem actualCompatibility (z : ZMod 2) :
    oldObject.hom ≫ sourceEval =
      CommRingCat.ofHom intPolynomialFlatChange.liftedHom ≫ coeffEvalCat z := by
  apply CommRingCat.hom_ext
  ext x
  rcases x with ⟨x⟩
  change sourceEvalAlg (algebraMap Int
      (SheafifiedSectionRing coefficientRaw finiteBase) x) =
    coeffEval z (Polynomial.C x)
  rw [sourceEvalAlg.commutes]
  simp [coeffEval]

private noncomputable def targetEval (z : ZMod 2) :
    newObject.right ⟶ CommRingCat.of (ZMod 2) :=
  (RawAmbientRestrictionSystem.sheafifiedSectionObjectBaseChangeIso
    coefficientRaw intPolynomialFlatChange finiteBase).inv.right ≫
      pushout.desc sourceEval (coeffEvalCat z) (actualCompatibility z)

private theorem targetEval_source (z : ZMod 2) :
    RawAmbientRestrictionSystem.sheafifiedSectionBaseChangeMap
        coefficientRaw intPolynomialFlatChange finiteBase ≫
      targetEval z = sourceEval := by
  simp [targetEval,
    RawAmbientRestrictionSystem.sheafifiedSectionBaseChangeMap_eq]

private theorem targetEval_coefficient (z : ZMod 2) :
    newObject.hom ≫ targetEval z = coeffEvalCat z := by
  let e := RawAmbientRestrictionSystem.sheafifiedSectionObjectBaseChangeIso
    coefficientRaw intPolynomialFlatChange finiteBase
  rw [targetEval]
  rw [← Category.assoc]
  have hw : newObject.hom ≫ e.inv.right =
      (intPolynomialFlatChange.coefficientExtension.obj oldObject).hom := by
    exact e.inv.w.symm
  rw [hw]
  change pushout.inr oldObject.hom
      (CommRingCat.ofHom intPolynomialFlatChange.liftedHom) ≫
        pushout.desc sourceEval (coeffEvalCat z) (actualCompatibility z) = coeffEvalCat z
  rw [pushout.inr_desc]

private theorem sourceEval_two :
    sourceEval
        ((sheafificationUnitAlgHom coefficientRaw finiteBase)
          (2 : coefficientRaw.rawAlgebra finiteBase)) = 0 := by
  change sourceEvalAlg
      ((sheafificationUnitAlgHom coefficientRaw finiteBase)
        (2 : coefficientRaw.rawAlgebra finiteBase)) = 0
  let P := coefficientBridge_valid.presentation_stable finiteBase
  have hc : P.comparison
      ((sheafificationUnitAlgHom coefficientRaw finiteBase) 2) = 2 := by
    rw [← P.comparison_symm_toAlgHom]
    exact P.comparison.apply_symm_apply _
  change ((Algebra.ofId Int (ZMod 2)).comp
    (sourceRawEvalAlg.comp P.comparison.toAlgHom))
      ((sheafificationUnitAlgHom coefficientRaw finiteBase) 2) = 0
  rw [AlgHom.comp_apply, AlgHom.comp_apply]
  calc
    _ = (Algebra.ofId Int (ZMod 2)) (sourceRawEvalAlg 2) := by
      exact congrArg
        (fun y => (Algebra.ofId Int (ZMod 2)) (sourceRawEvalAlg y)) hc
    _ = 0 := by
      change ((sourceRawEvalInt 2 : Int) : ZMod 2) = 0
      have htwo : (2 : coefficientRaw.rawAlgebra finiteBase) =
          algebraMap Int (coefficientRaw.rawAlgebra finiteBase) 2 := by
        norm_num
      rw [htwo]
      change ((sourceRawEvalInt
        ((2 : Int) : coefficientRaw.rawAlgebra finiteBase) : Int) : ZMod 2) = 0
      rw [sourceRawEvalInt_intCast]
      change (2 : ZMod 2) = 0
      decide

private noncomputable def targetAmbientEval (z : ZMod 2) :
    Γ(targetScheme.underlying, ⊤) →+* ZMod 2 :=
  (changedChartMap.appTop ≫
    (Scheme.ΓSpecIso (SheafifiedSectionRing targetRaw finiteBase)).hom ≫
    targetEval z).hom

private theorem targetInterpretation_chart :
    targetScheme.decoration.interpretation ≫ changedChartMap.appTop ≫
        (Scheme.ΓSpecIso (SheafifiedSectionRing targetRaw finiteBase)).hom =
      𝟙 _ := by
  have h := (targetScheme.atlasValid.chart_valid targetIndex).interpretation_compatible
  change sheafifiedRestriction targetRaw (𝟙 finiteBase) = _ at h
  simpa only [sheafifiedRestriction_id] using h.symm

private theorem targetAmbientEval_baseChanged_interpretation (z : ZMod 2)
    (x : SheafifiedSectionRing coefficientRaw finiteBase) :
    targetAmbientEval z
        ((coefficientScheme.baseChangeMap coefficientRaw intPolynomialFlatChange).appTop
          (coefficientScheme.decoration.interpretation x)) =
      sourceEval x := by
  have hdecor := coefficientScheme.baseChangedDecoration_interpretation
    coefficientRaw intPolynomialFlatChange
  have hcomp :
      coefficientScheme.decoration.interpretation ≫
          (coefficientScheme.baseChangeMap coefficientRaw intPolynomialFlatChange).appTop ≫
          changedChartMap.appTop ≫
          (Scheme.ΓSpecIso (SheafifiedSectionRing targetRaw finiteBase)).hom ≫
          targetEval z =
        sourceEval := by
    have hd := congrArg
      (fun q => q ≫ changedChartMap.appTop ≫
        (Scheme.ΓSpecIso (SheafifiedSectionRing targetRaw finiteBase)).hom ≫
        targetEval z) hdecor
    have hchart := congrArg
      (fun q =>
        RawAmbientRestrictionSystem.sheafifiedSectionBaseChangeMap
            coefficientRaw intPolynomialFlatChange finiteBase ≫ q ≫ targetEval z)
      targetInterpretation_chart
    calc
      _ = RawAmbientRestrictionSystem.sheafifiedSectionBaseChangeMap
              coefficientRaw intPolynomialFlatChange finiteBase ≫
            targetScheme.decoration.interpretation ≫ changedChartMap.appTop ≫
            (Scheme.ΓSpecIso
              (SheafifiedSectionRing targetRaw finiteBase)).hom ≫
            targetEval z := by
              simpa only [Category.assoc] using hd.symm
      _ = RawAmbientRestrictionSystem.sheafifiedSectionBaseChangeMap
              coefficientRaw intPolynomialFlatChange finiteBase ≫ targetEval z := by
              simpa only [Category.assoc, Category.comp_id, Category.id_comp] using hchart
      _ = sourceEval := targetEval_source z
  exact congrArg (fun f => f x) hcomp

private theorem targetEquation_eval_zero (z : ZMod 2)
    (i : finiteSite.lawUniverse.Index) (atom : FiniteModel.FiniteAtom) :
    targetAmbientEval z
      (baseChangedSemanticCoreGlobalEquation coefficientRaw coefficientScheme
      coefficientSemanticCore coefficientBridge intPolynomialFlatChange i atom) = 0 := by
  cases i
  rw [baseChangedSemanticCoreGlobalEquation]
  rw [semanticCoreGlobalEquation]
  rw [targetAmbientEval_baseChanged_interpretation]
  cases atom <;>
    simp [coefficientSemanticCore, coefficientBridge,
      SemanticLawEquationSchemeBridge.toSheafifiedSection] ;
    simpa only using sourceEval_two

private theorem targetLawIdeal_le_ker (z : ZMod 2) :
    targetLawIdeal.ideal ⟨⊤, isAffineOpen_top _⟩ ≤
      RingHom.ker (targetAmbientEval z) := by
  rw [lawGeneratedIdealSheaf_ideal]
  refine iSup_le fun i => ?_
  rw [localLawWitnessIdeal]
  apply Ideal.span_le.mpr
  rintro x ⟨atom, rfl⟩
  change targetAmbientEval z
    ((targetReading.witness i.1 (targetRequired.closed i.1 i.2.1)).coordinate
      ⟨⊤, isAffineOpen_top _⟩ atom) = 0
  simpa [targetReading, ClosedEquationalLawReading.baseChangeOfSemanticCore,
    ClosedEquationalLawWitness.ofGlobalSections_coordinate] using
      targetEquation_eval_zero z i.1 atom


private noncomputable def targetLawfulTopIso :
    Γ(targetLawful, ⊤) ≅ CommRingCat.of
      (Γ(targetScheme.underlying, ⊤) ⧸
        targetLawIdeal.ideal ⟨⊤, isAffineOpen_top _⟩) :=
  targetLawIdeal.subschemeObjIso
    (⟨⊤, isAffineOpen_top _⟩ : targetScheme.underlying.affineOpens)

private theorem targetImmersion_appTop_topIso :
    targetImmersion.appTop ≫ targetLawfulTopIso.hom =
      CommRingCat.ofHom
        (Ideal.Quotient.mk
          (targetLawIdeal.ideal ⟨⊤, isAffineOpen_top targetScheme.underlying⟩)) := by
  let U : targetScheme.underlying.affineOpens :=
    ⟨⊤, isAffineOpen_top targetScheme.underlying⟩
  have h := targetLawIdeal.subschemeι_app U
  have hc := congrArg (fun q => q ≫ targetLawfulTopIso.hom) h
  simpa only [U, targetLawfulTopIso, Category.assoc, Iso.inv_hom_id,
    Category.comp_id] using hc

private noncomputable def targetLawfulQuotientEval (z : ZMod 2) :
    (Γ(targetScheme.underlying, ⊤) ⧸
      targetLawIdeal.ideal ⟨⊤, isAffineOpen_top _⟩) →+* ZMod 2 :=
  Ideal.Quotient.lift _ (targetAmbientEval z) (targetLawIdeal_le_ker z)

private noncomputable def targetLawfulEval (z : ZMod 2) :
    Γ(targetLawful, ⊤) →+* ZMod 2 :=
  (targetLawfulQuotientEval z).comp targetLawfulTopIso.hom.hom

private theorem targetLawfulEval_on_immersion (z : ZMod 2)
    (x : Γ(targetScheme.underlying, ⊤)) :
    targetLawfulEval z (targetImmersion.appTop x) = targetAmbientEval z x := by
  have h := ConcreteCategory.congr_hom targetImmersion_appTop_topIso x
  simpa [targetLawfulEval, targetLawfulQuotientEval] using
    congrArg (targetLawfulQuotientEval z) h

private noncomputable def targetChartSections :
    Γ(targetScheme.underlying, ⊤) ⟶ SheafifiedSectionRing targetRaw finiteBase :=
  changedChartMap.appTop ≫
    (Scheme.ΓSpecIso (SheafifiedSectionRing targetRaw finiteBase)).hom

private noncomputable instance targetChartSectionsIsIso :
    IsIso targetChartSections := by
  dsimp only [targetChartSections]
  infer_instance

private noncomputable def targetAmbientCoefficientX :
    Γ(targetScheme.underlying, ⊤) :=
  inv targetChartSections
    (newObject.hom (ULift.up (Polynomial.X : Polynomial Int)))

private theorem targetAmbientEval_coefficientX (z : ZMod 2) :
    targetAmbientEval z targetAmbientCoefficientX = z := by
  have hsection : targetChartSections targetAmbientCoefficientX =
      newObject.hom (ULift.up (Polynomial.X : Polynomial Int)) := by
    simp [targetAmbientCoefficientX]
  have hcoeff := ConcreteCategory.congr_hom (targetEval_coefficient z)
    (ULift.up (Polynomial.X : Polynomial Int))
  change targetEval z (targetChartSections targetAmbientCoefficientX) = z
  rw [hsection]
  calc
    _ = coeffEvalCat z (ULift.up (Polynomial.X : Polynomial Int)) := by
      simpa only [ConcreteCategory.comp_apply] using hcoeff
    _ = z := by
      change Polynomial.eval₂ (Int.castRingHom (ZMod 2)) z Polynomial.X = z
      simp

private noncomputable def targetLawfulCoefficientX : Γ(targetLawful, ⊤) :=
  targetImmersion.appTop targetAmbientCoefficientX

private theorem targetLawfulEval_coefficientX (z : ZMod 2) :
    targetLawfulEval z targetLawfulCoefficientX = z := by
  rw [targetLawfulCoefficientX, targetLawfulEval_on_immersion,
    targetAmbientEval_coefficientX]

private theorem targetLawfulEval_ne :
    targetLawfulEval 0 ≠ targetLawfulEval 1 := by
  intro h
  have hx := DFunLike.congr_fun h targetLawfulCoefficientX
  rw [targetLawfulEval_coefficientX, targetLawfulEval_coefficientX] at hx
  norm_num at hx

private noncomputable instance sourceInterpretationIsIso :
    IsIso coefficientScheme.decoration.interpretation := by
  change IsIso
    ((Scheme.ΓSpecIso (SheafifiedSectionRing coefficientRaw finiteBase)).inv)
  infer_instance

private theorem targetAmbientEval_agree_on_baseMap
    (x : Γ(coefficientScheme.underlying, ⊤)) :
    targetAmbientEval 0
        ((coefficientScheme.baseChangeMap coefficientRaw intPolynomialFlatChange).appTop x) =
      targetAmbientEval 1
        ((coefficientScheme.baseChangeMap coefficientRaw intPolynomialFlatChange).appTop x) := by
  rcases (ConcreteCategory.bijective_of_isIso
    coefficientScheme.decoration.interpretation).2 x with ⟨y, rfl⟩
  exact (targetAmbientEval_baseChanged_interpretation 0 y).trans
    (targetAmbientEval_baseChanged_interpretation 1 y).symm

private abbrev sourceReading :=
  ClosedEquationalLawReading.ofSemanticCore coefficientRaw coefficientScheme
    coefficientSemanticCore coefficientBridge

private abbrev sourceReadingValid :=
  ClosedEquationalLawReading.ofSemanticCore_valid coefficientRaw coefficientScheme
    coefficientSemanticCore coefficientBridge

private abbrev sourceRequired :=
  ClosedEquationalLawReading.ofSemanticCore_requiredClosed coefficientRaw coefficientScheme
    coefficientSemanticCore coefficientBridge

private abbrev sourceLawful : Scheme :=
  lawfulClosedSubscheme coefficientRaw coefficientScheme sourceReading
    sourceReadingValid sourceRequired

private abbrev sourceImmersion : sourceLawful ⟶ coefficientScheme.underlying :=
  lawfulClosedImmersion coefficientRaw coefficientScheme sourceReading
    sourceReadingValid sourceRequired

private abbrev lawfulComparison : targetLawful ⟶ sourceLawful :=
  lawfulClosedSubschemeBaseChangeMap coefficientRaw coefficientScheme
    coefficientSemanticCore coefficientBridge intPolynomialFlatChange

private local instance sourceSchemeIsAffine :
    IsAffine coefficientScheme.underlying := by
  change IsAffine (Spec (SheafifiedSectionRing coefficientRaw finiteBase))
  infer_instance

private noncomputable local instance sourceImmersionClosed :
    IsClosedImmersion sourceImmersion := by
  dsimp only [sourceImmersion, lawfulClosedImmersion]
  infer_instance

private theorem lawfulComparison_appTop_immersion :
    sourceImmersion.appTop ≫ lawfulComparison.appTop =
      (coefficientScheme.baseChangeMap coefficientRaw intPolynomialFlatChange).appTop ≫
        targetImmersion.appTop := by
  have h := lawfulClosedSubschemeBaseChangeMap_immersion coefficientRaw coefficientScheme
    coefficientSemanticCore coefficientBridge intPolynomialFlatChange
  simpa only [Scheme.Hom.comp_appTop] using congrArg Scheme.Hom.appTop h

private theorem targetLawfulEval_agree_on_comparison
    (x : Γ(sourceLawful, ⊤)) :
    targetLawfulEval 0 (lawfulComparison.appTop x) =
      targetLawfulEval 1 (lawfulComparison.appTop x) := by
  rcases (IsClosedImmersion.isAffine_surjective_of_isAffine sourceImmersion).2 x with
    ⟨y, rfl⟩
  have himm := ConcreteCategory.congr_hom lawfulComparison_appTop_immersion y
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at himm
  rw [himm, targetLawfulEval_on_immersion, targetLawfulEval_on_immersion]
  exact targetAmbientEval_agree_on_baseMap y

private theorem lawfulComparison_not_surjective :
    ¬ Function.Surjective lawfulComparison.appTop := by
  intro hsurj
  apply targetLawfulEval_ne
  apply RingHom.ext
  intro y
  rcases hsurj y with ⟨x, rfl⟩
  exact targetLawfulEval_agree_on_comparison x

private theorem lawfulComparison_not_isIso : ¬ IsIso lawfulComparison := by
  intro h
  letI : IsIso lawfulComparison := h
  exact lawfulComparison_not_surjective
    (ConcreteCategory.bijective_of_isIso lawfulComparison.appTop).2


/-- The realized proper law ideal changes the lawful locus under polynomial coefficient extension. -/
theorem lawfulLocus_baseChange_fires :
    LawAlgebra.SemanticCoreIdealSheafRealized
        coefficientRaw coefficientScheme coefficientSemanticCore coefficientBridge ∧
    ¬ IsIso
      (LawAlgebra.lawfulClosedSubschemeBaseChangeMap
        coefficientRaw coefficientScheme coefficientSemanticCore
        coefficientBridge intPolynomialFlatChange) :=
  ⟨coefficientSemanticCore_realized, lawfulComparison_not_isIso⟩

end AAT.AG.ReadingFunctorialityFinite
