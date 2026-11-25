import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
import Mathlib.RingTheory.Idempotents
import Formal.SHIGURE.Part2.AffineBaseChange
import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Affine constructions over a coefficient ring

The clopen decomposition and universal properties used in SHIGURE, Appendix B.1.

## Implementation notes

The parts in Lemma B.1 have a fixed finite index type. Empty parts keep the same labels as
zero idempotents and are retained by inverse image. The correspondence uses mathlib's
order isomorphism for the spectrum, which is the underlying space of the affine scheme.

The relative statement of Lemma B.2 uses the slice category over the coefficient scheme.
The absolute adjunction is restricted by the slice commutativity condition, which gives
the coefficient-algebra structure on global sections and avoids a separate category of
schemes with a structural morphism.
-/

open scoped BigOperators
open AlgebraicGeometry TopologicalSpace

noncomputable section

namespace SHIGURE

section Clopens

variable {R : Type*} [CommRing R]

/-- Lemma B.1. The clopen corresponding to an idempotent is its basic open in the affine
scheme. The affine scheme and the prime spectrum have the same underlying space. -/
def clopenOfIdempotent :
    {e : R // IsIdempotentElem e} ≃o Clopens (Spec (CommRingCat.of R)) :=
  PrimeSpectrum.isIdempotentElemEquivClopens

/-- The set-level API for Lemma B.1. Simplify the carrier of the clopen to the basic open. -/
@[simp]
theorem coe_clopenOfIdempotent (e : {e : R // IsIdempotentElem e}) :
    (clopenOfIdempotent e : Set (Spec (CommRingCat.of R))) =
      (PrimeSpectrum.basicOpen e.val : Set (PrimeSpectrum R)) :=
  PrimeSpectrum.coe_isIdempotentElemEquivClopens_apply e

/-- The change-of-ring formula for Lemma B.1 under an arbitrary ring map. -/
theorem clopenOfIdempotent_preimage {S : Type*} [CommRing S] (f : R →+* S)
    (e : {e : R // IsIdempotentElem e}) :
    PrimeSpectrum.comap f ⁻¹' (clopenOfIdempotent e : Set (Spec (CommRingCat.of R))) =
      (clopenOfIdempotent ⟨f e.val, e.property.map f⟩ : Set (Spec (CommRingCat.of S))) := by
  simp only [coe_clopenOfIdempotent]
  rfl

/-- The disjointness step of Lemma B.1, using multiplication of idempotents for intersection. -/
private theorem clopens_orthogonal_iff {ι : Type*}
    (e : ι → {e : R // IsIdempotentElem e}) :
    Pairwise (fun i j => Disjoint (clopenOfIdempotent (e i)) (clopenOfIdempotent (e j))) ↔
      Pairwise (fun i j => (e i).val * (e j).val = 0) := by
  unfold Pairwise
  refine forall_congr' fun i => forall_congr' fun j => ?_
  have hbot := PrimeSpectrum.isIdempotentElemEquivClopens_symm_bot (R := R)
  have he : clopenOfIdempotent ⟨_, (e i).property.mul (e j).property⟩ =
      clopenOfIdempotent (e i) ⊓ clopenOfIdempotent (e j) :=
    PrimeSpectrum.isIdempotentElemEquivClopens_mul (e i) (e j)
  have hz : clopenOfIdempotent (⟨(0 : R), .zero⟩) = ⊥ := by
    rw [← hbot]
    exact clopenOfIdempotent.apply_symm_apply ⊥
  constructor <;> intro h hij
  · have key := he.trans (disjoint_iff.mp (h hij))
    rw [← hz] at key
    exact congrArg Subtype.val (clopenOfIdempotent.injective key)
  · rw [disjoint_iff, ← he, ← hz]
    congr 1
    exact Subtype.ext (h hij)

/-- The cover step of Lemma B.1, using the product of the complements of the idempotents. -/
private theorem clopens_cover_iff {ι : Type*} [Fintype ι]
    (e : ι → {e : R // IsIdempotentElem e})
    (he : OrthogonalIdempotents (fun i => (e i).val)) :
    (∀ x : PrimeSpectrum R, ∃ i, x ∈ clopenOfIdempotent (e i)) ↔
      ∑ i, (e i).val = 1 := by
  classical
  let c := ∏ i, (1 - (e i).val)
  have hc : IsIdempotentElem c := by
    dsimp [c]
    rw [he.prod_one_sub]
    exact he.isIdempotentElem_sum.one_sub
  have hzero : PrimeSpectrum.basicOpen c = ⊥ ↔ c = 0 := by
    rw [PrimeSpectrum.basicOpen_eq_bot_iff]
    exact ⟨hc.eq_zero_of_isNilpotent, fun h => h ▸ IsNilpotent.zero⟩
  have hcover (x : PrimeSpectrum R) (i : ι) :
      x ∈ clopenOfIdempotent (e i) ↔ 1 - (e i).val ∈ x.asIdeal := by
    have hcompl : ¬ x ∈ clopenOfIdempotent (e i) ↔
        1 - (e i).val ∉ x.asIdeal := by
      have hp : (clopenOfIdempotent (e i))ᶜ =
          clopenOfIdempotent ⟨1 - (e i).val, (e i).property.one_sub⟩ :=
        (PrimeSpectrum.isIdempotentElemEquivClopens_one_sub (e i)).symm
      change x ∈ ((clopenOfIdempotent (e i))ᶜ : Clopens (Spec (CommRingCat.of R))) ↔ _
      rw [hp]
      rfl
    exact not_iff_not.mp hcompl
  calc
    (∀ x : PrimeSpectrum R, ∃ i, x ∈ clopenOfIdempotent (e i)) ↔
        ∀ x : PrimeSpectrum R, c ∈ x.asIdeal := by
      simp only [hcover, c, Ideal.IsPrime.prod_mem_iff, Finset.mem_univ, true_and]
    _ ↔ PrimeSpectrum.basicOpen c = ⊥ := by
      rw [SetLike.ext_iff]
      simp [PrimeSpectrum.mem_basicOpen]
    _ ↔ c = 0 := hzero
    _ ↔ ∑ i, (e i).val = 1 := by
      dsimp [c]
      rw [he.prod_one_sub, sub_eq_zero, eq_comm]

/-- Lemma B.1. A finite indexed clopen partition of an affine scheme is specified by a complete
orthogonal family of idempotents. Empty parts are allowed. -/
def clopenPartitionEquiv {ι : Type*} [Fintype ι] :
    {e : ι → R // CompleteOrthogonalIdempotents e} ≃
    {U : ι → Clopens (Spec (CommRingCat.of R)) //
      Pairwise (fun i j => Disjoint (U i) (U j)) ∧ ∀ x : PrimeSpectrum R, ∃ i, x ∈ U i} where
  toFun e :=
    let ee : ι → {x : R // IsIdempotentElem x} := fun i => ⟨e.val i, e.property.idem i⟩
    ⟨fun i => clopenOfIdempotent (ee i),
      (clopens_orthogonal_iff ee).mpr e.property.ortho,
      (clopens_cover_iff ee e.property.toOrthogonalIdempotents).mpr e.property.complete⟩
  invFun U :=
    let e := fun i => clopenOfIdempotent.symm (U.val i)
    have ho : OrthogonalIdempotents (fun i => (e i).val) := ⟨fun i => (e i).property,
      (clopens_orthogonal_iff e).mp (by simpa only [e, OrderIso.apply_symm_apply] using U.property.1)⟩
    ⟨fun i => (e i).val, ⟨ho, (clopens_cover_iff e ho).mp
      (by simpa only [e, OrderIso.apply_symm_apply] using U.property.2)⟩⟩
  left_inv e := Subtype.ext <| funext fun i =>
    congrArg Subtype.val (clopenOfIdempotent.symm_apply_apply ⟨e.val i, e.property.idem i⟩)
  right_inv U := Subtype.ext <| funext fun i => clopenOfIdempotent.apply_symm_apply (U.val i)

/-- The component API for the finite-family part of Lemma B.1. Simplify a part to its basic open. -/
@[simp]
theorem coe_clopenPartitionEquiv {ι : Type*} [Fintype ι]
    (e : {e : ι → R // CompleteOrthogonalIdempotents e}) (i : ι) :
    ((clopenPartitionEquiv e).val i : Set (Spec (CommRingCat.of R))) =
      (PrimeSpectrum.basicOpen (e.val i) : Set (PrimeSpectrum R)) :=
  coe_clopenOfIdempotent ⟨e.val i, e.property.idem i⟩

/-- The finite-family change-of-ring formula in Lemma B.1. Pulling back the clopen
partition along any ring map sends its complete orthogonal family to the image family. -/
theorem clopenPartitionEquiv_preimage {S ι : Type*} [CommRing S] [Fintype ι]
    (f : R →+* S) (e : {e : ι → R // CompleteOrthogonalIdempotents e}) :
    (fun i => PrimeSpectrum.comap f ⁻¹'
      ((clopenPartitionEquiv e).val i : Set (Spec (CommRingCat.of R)))) =
    (fun i => ((clopenPartitionEquiv ⟨f ∘ e.val, e.property.map f⟩).val i :
      Set (Spec (CommRingCat.of S)))) := by
  funext i
  exact clopenOfIdempotent_preimage f ⟨e.val i, e.property.idem i⟩

end Clopens

section UniversalProperties

variable {k L Q R S : Type*} [CommRing k]
  [AddCommGroup Q] [Module k Q] [CommRing R] [Algebra k R] [CommRing S] [Algebra k S]

/-- Lemma B.2. Points of the polynomial algebra on an arbitrary small set of variables. -/
def polynomialPointEquiv : (MvPolynomial L k →ₐ[k] R) ≃ (L → R) where
  toFun f i := f (MvPolynomial.X i)
  invFun := MvPolynomial.aeval
  left_inv f := by ext i; exact MvPolynomial.aeval_X _ _
  right_inv p := funext (MvPolynomial.aeval_X p)

/-- The generator API for Lemma B.2. Simplify a polynomial point to the value of its variable. -/
@[simp]
theorem polynomialPointEquiv_apply (f : MvPolynomial L k →ₐ[k] R) (i : L) :
    polynomialPointEquiv f i = f (MvPolynomial.X i) :=
  rfl

/-- Naturality in the target algebra in the polynomial part of Lemma B.2. -/
theorem polynomialPointEquiv_natural (f : MvPolynomial L k →ₐ[k] R) (g : R →ₐ[k] S) :
    polynomialPointEquiv (g.comp f) = g ∘ polynomialPointEquiv f :=
  rfl

/-- Naturality under a map of variable sets in the polynomial part of Lemma B.2. -/
theorem polynomialPointEquiv_rename {L' : Type*} (g : L' → L)
    (f : MvPolynomial L k →ₐ[k] R) :
    polynomialPointEquiv (f.comp (MvPolynomial.rename g)) = polynomialPointEquiv f ∘ g := by
  funext i
  simp

/-- Lemma B.2. The universal property of the symmetric algebra, oriented as a point map. -/
def symmetricPointEquiv : (SymmetricAlgebra k Q →ₐ[k] R) ≃ (Q →ₗ[k] R) :=
  SymmetricAlgebra.lift.symm

/-- The generator API for the symmetric algebra in Lemma B.2. Simplify to evaluation on the generator. -/
@[simp]
theorem symmetricPointEquiv_apply (f : SymmetricAlgebra k Q →ₐ[k] R) (x : Q) :
    symmetricPointEquiv f x = f (SymmetricAlgebra.ι k Q x) := by
  conv_rhs => rw [← SymmetricAlgebra.lift.apply_symm_apply f]
  rw [SymmetricAlgebra.lift_ι_apply]
  rfl

/-- Naturality in the target algebra in the symmetric-algebra part of Lemma B.2. -/
theorem symmetricPointEquiv_natural (f : SymmetricAlgebra k Q →ₐ[k] R) (g : R →ₐ[k] S) :
    symmetricPointEquiv (g.comp f) = g.toLinearMap.comp (symmetricPointEquiv f) := by
  ext x
  simp

/-- Naturality in the module of generators via a linear map in Lemma B.2. -/
theorem symmetricPointEquiv_precomp {Q' : Type*} [AddCommGroup Q'] [Module k Q']
    (g : Q' →ₗ[k] Q) (f : SymmetricAlgebra k Q →ₐ[k] R) :
    symmetricPointEquiv (f.comp (symmetricMap Q' g)) = (symmetricPointEquiv f).comp g := by
  ext x
  simp

end UniversalProperties

section SchemePoints

open CategoryTheory Opposite

universe u

variable {X Y : Scheme.{u}} {B C : CommRingCat.{u}}

/-- The absolute Γ–Spec adjunction written as a map from scheme points to ring homomorphisms. -/
def specGlobalHom : (X ⟶ Spec B) ≃ (B ⟶ Γ(X, ⊤)) :=
  (ΓSpec.adjunction.homEquiv X (op B)).symm.trans
    { toFun := Quiver.Hom.unop
      invFun := Quiver.Hom.op
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- The absolute adjunction formula used in Lemma B.2 to pull back global functions. -/
theorem specGlobalHom_precomp (f : Y ⟶ X) (g : X ⟶ Spec B) :
    specGlobalHom (f ≫ g) = specGlobalHom g ≫ Scheme.Γ.map f.op := by
  exact congrArg Quiver.Hom.unop (ΓSpec.adjunction.homEquiv_naturality_left_symm f g)

/-- The absolute adjunction formula used in Lemma B.2 for a map of affine targets. -/
theorem specGlobalHom_postcomp (f : X ⟶ Spec B) (g : C ⟶ B) :
    specGlobalHom (f ≫ Spec.map g) = g ≫ specGlobalHom f := by
  exact congrArg Quiver.Hom.unop (ΓSpec.adjunction.homEquiv_naturality_right_symm f g.op)

variable {k : Type u} [CommRing k]

/-- The affine scheme of a coefficient algebra, equipped with its structural morphism. -/
def specOver (A : Type u) [CommRing A] [Algebra k A] : Over (Spec (CommRingCat.of k)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k A)))

/-- The structural morphism of the affine target in Lemma B.2. Simplify to the spectrum
of the base algebra map. -/
@[simp]
theorem specOver_hom (A : Type u) [CommRing A] [Algebra k A] :
    (specOver (k := k) A).hom = Spec.map (CommRingCat.ofHom (algebraMap k A)) :=
  rfl

/-- Global sections of a k-scheme as a k-algebra via its structural morphism. -/
def globalSectionsAlgebra (T : Over (Spec (CommRingCat.of k))) : Algebra k Γ(T.left, ⊤) :=
  (specGlobalHom T.hom).hom.toAlgebra

/-- The coefficient map for the global sections in Lemma B.2. Simplify it to the ring
map corresponding to the structural morphism of the test scheme. -/
@[simp]
theorem globalSectionsAlgebra_algebraMap (T : Over (Spec (CommRingCat.of k))) :
    letI := globalSectionsAlgebra T
    algebraMap k Γ(T.left, ⊤) = (specGlobalHom T.hom).hom :=
  rfl

/-- Lemma B.2. Maps from an arbitrary k-scheme to an affine k-scheme correspond to
k-algebra maps into the global sections. -/
def specOverPointEquiv (T : Over (Spec (CommRingCat.of k)))
    (A : Type u) [CommRing A] [Algebra k A] :
    letI := globalSectionsAlgebra T
    (T ⟶ specOver A) ≃ (A →ₐ[k] Γ(T.left, ⊤)) := by
  letI := globalSectionsAlgebra T
  refine
    { toFun := fun f => ⟨(specGlobalHom f.left).hom, ?_⟩
      invFun := fun f => Over.homMk (specGlobalHom.symm (CommRingCat.ofHom f.toRingHom)) ?_
      left_inv := ?_
      right_inv := ?_ }
  · intro a
    have h := congrArg specGlobalHom (Over.w f)
    change specGlobalHom (f.left ≫ Spec.map (CommRingCat.ofHom (algebraMap k A))) =
      specGlobalHom T.hom at h
    rw [specGlobalHom_postcomp] at h
    exact congrArg (fun g : CommRingCat.of k ⟶ Γ(T.left, ⊤) => g.hom a) h
  · apply specGlobalHom.injective
    change specGlobalHom
      (specGlobalHom.symm (CommRingCat.ofHom f.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k A))) = specGlobalHom T.hom
    rw [specGlobalHom_postcomp, Equiv.apply_symm_apply]
    apply CommRingCat.hom_ext
    ext a
    exact f.commutes a
  · intro f
    apply Over.OverMorphism.ext
    exact specGlobalHom.symm_apply_apply f.left
  · intro f
    apply AlgHom.coe_ringHom_injective
    change (specGlobalHom (specGlobalHom.symm (CommRingCat.ofHom f.toRingHom))).hom = f.toRingHom
    rw [Equiv.apply_symm_apply]
    rfl

/-- The relative point API for Lemma B.2. Simplify to the absolute ring map for the underlying morphism. -/
@[simp]
theorem specOverPointEquiv_apply (T : Over (Spec (CommRingCat.of k)))
    {A : Type u} [CommRing A] [Algebra k A] (f : T ⟶ specOver A) (a : A) :
    specOverPointEquiv T A f a = (specGlobalHom f.left).hom a :=
  rfl

/-- An algebra map induces the contravariant map of affine k-schemes. -/
def specOverMap {A D : Type u} [CommRing A] [CommRing D] [Algebra k A] [Algebra k D]
    (f : A →ₐ[k] D) : specOver (k := k) D ⟶ specOver (k := k) A :=
  Over.homMk (Spec.map (CommRingCat.ofHom f.toRingHom)) <| by
    change Spec.map (CommRingCat.ofHom f.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap k A)) =
      Spec.map (CommRingCat.ofHom (algebraMap k D))
    exact (Spec.map_comp _ _).symm.trans <| congrArg Spec.map
      (CommRingCat.hom_ext <| RingHom.ext (f.commutes ·))

/-- The underlying arrow of `specOverMap` for Lemma B.2. Simplify to the absolute
spectrum map of the given algebra homomorphism. -/
@[simp]
theorem specOverMap_left {A D : Type u} [CommRing A] [CommRing D] [Algebra k A] [Algebra k D]
    (f : A →ₐ[k] D) :
    (specOverMap f).left = Spec.map (CommRingCat.ofHom f.toRingHom) :=
  rfl

/-- Naturality of Lemma B.2 with respect to a map of the target algebra over the base ring. -/
theorem specOverPointEquiv_postcomp (T : Over (Spec (CommRingCat.of k)))
    {A D : Type u} [CommRing A] [CommRing D] [Algebra k A] [Algebra k D]
    (f : T ⟶ specOver D) (g : A →ₐ[k] D) :
    letI := globalSectionsAlgebra T
    specOverPointEquiv T A (f ≫ specOverMap g) = (specOverPointEquiv T D f).comp g := by
  letI := globalSectionsAlgebra T
  ext a
  simp only [specOverPointEquiv_apply, Over.comp_left, specOverMap_left, AlgHom.comp_apply,
    specGlobalHom_postcomp]
  rfl

/-- Pullback of global sections along a morphism over the coefficient scheme. -/
def globalSectionsMap {T T' : Over (Spec (CommRingCat.of k))} (f : T' ⟶ T) :
    letI := globalSectionsAlgebra T
    letI := globalSectionsAlgebra T'
    Γ(T.left, ⊤) →ₐ[k] Γ(T'.left, ⊤) := by
  letI := globalSectionsAlgebra T
  letI := globalSectionsAlgebra T'
  refine ⟨(Scheme.Γ.map f.left.op).hom, ?_⟩
  intro a
  have h := specGlobalHom_precomp f.left T.hom
  rw [Over.w f] at h
  exact congrArg (fun g : CommRingCat.of k ⟶ Γ(T'.left, ⊤) => g.hom a) h.symm

/-- The pullback of a global section in Lemma B.2. Simplify the relative algebra map
to the ordinary pullback of the underlying section. -/
@[simp]
theorem globalSectionsMap_apply {T T' : Over (Spec (CommRingCat.of k))} (f : T' ⟶ T)
    (a : Γ(T.left, ⊤)) :
    globalSectionsMap f a = (Scheme.Γ.map f.left.op).hom a :=
  rfl

/-- Naturality of Lemma B.2 with respect to a morphism of test schemes over the base. -/
theorem specOverPointEquiv_precomp {T T' : Over (Spec (CommRingCat.of k))}
    {A : Type u} [CommRing A] [Algebra k A] (f : T' ⟶ T) (g : T ⟶ specOver A) :
    letI := globalSectionsAlgebra T
    letI := globalSectionsAlgebra T'
    specOverPointEquiv T' A (f ≫ g) =
      (globalSectionsMap f).comp (specOverPointEquiv T A g) := by
  letI := globalSectionsAlgebra T
  letI := globalSectionsAlgebra T'
  ext a
  simp only [specOverPointEquiv_apply, Over.comp_left, AlgHom.comp_apply, globalSectionsMap_apply,
    specGlobalHom_precomp]
  rfl

end SchemePoints

end SHIGURE
