import Formal.SHIGURE.Part2.Families.SchemeRealizations
import Formal.SHIGURE.Part2.Marked.Coordinates
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import Mathlib.CategoryTheory.IsomorphismClasses
import Mathlib.CategoryTheory.Discrete.Basic
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.CategoryTheory.Abelian.Subobject

/-! # Markings, their rigid groupoids, and kernel descriptions

Definition 6.3 attaches surjective maps from finite free modules to actual
realizations. The groupoid retains arbitrary carriers; normalized free
charts are compared with it afterwards. Kernel descriptions and scalar
change use the actual marking maps, including nonflat scalar changes.

## Implementation notes

On a scheme the source is mathlib's free sheaf of modules. Epimorphy is a
property separate from the marking data. Isomorphism classes are first
formed in their original universe and then shrunk after proving smallness;
the small set is not postulated as extra input.
-/

universe u v w v' w'

namespace SHIGURE.RealizationFamilies.Marked

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits SchemeDescent Opposite
open scoped TensorProduct

noncomputable section

variable {k R S : Type u} [CommRing k] [CommRing R] [CommRing S]
variable {sig : Signature.{u}} (P : AffineLawPresentation k sig)
variable (generators rank : sig.SortType → ℕ)

/-- The actual free sheaf `𝒪_X^m`, with the finite named generator index. -/
def freeModuleSheaf (X : Scheme.{u}) (m : ℕ) : X.Modules :=
  SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin m))

/-- Markings on an affine realization before testing their surjectivity. -/
structure AffineMarkedData (c : k →+* R) where
  /-- The existing affine realization, with arbitrary finite projective carriers. -/
  realization : AffineRealization P rank c
  /-- The names of the generators specify a genuine linear map. -/
  marking (s : sig.SortType) : (Fin (generators s) → R) →ₗ[R] realization.obj.carrier s

/-- Surjective markings in Definition 6.3 are tested independently on the data. -/
def affineMarkingsSurjective {c : k →+* R} (D : AffineMarkedData P generators rank c) : Prop :=
  ∀ s, Function.Surjective (D.marking s)

/-- Affine marked realizations, retaining their actual carriers. -/
abbrev AffineMarkedRealization (c : k →+* R) :=
  {D : AffineMarkedData P generators rank c // affineMarkingsSurjective P generators rank D}

/-- The actual kernel of a named marking, a submodule of the fixed finite free source. -/
def affineMarkingKernel {c : k →+* R} (D : AffineMarkedRealization P generators rank c)
    (s : sig.SortType) : Submodule R (Fin (generators s) → R) :=
  LinearMap.ker (D.val.marking s)

/-- The kernel quotient recovers the actual carrier and the named marking. -/
def affineMarkedQuotientIso {c : k →+* R} (D : AffineMarkedRealization P generators rank c)
    (s : sig.SortType) :
    ((Fin (generators s) → R) ⧸ affineMarkingKernel P generators rank D s) ≃ₗ[R]
      D.val.realization.obj.carrier s :=
  (D.val.marking s).quotKerEquivOfSurjective (D.property s)

/-- The finite projective target supplies a splitting of the marking map. -/
theorem affineMarking_split {c : k →+* R} (D : AffineMarkedRealization P generators rank c)
    (s : sig.SortType) :
    ∃ splitting : D.val.realization.obj.carrier s →ₗ[R] (Fin (generators s) → R),
      (D.val.marking s).comp splitting = LinearMap.id := by
  letI : Module.Projective R (D.val.realization.obj.carrier s) :=
    (CoefficientDescent.finiteLocallyFree_iff_finite_projective.mp
      (D.val.realization.property.1 s)).2
  exact Module.projective_lifting_property (D.val.marking s) LinearMap.id (D.property s)

/-- Split exactness identifies the actual extended kernel for every scalar
change; flatness of the new algebra is not assumed. -/
theorem affineMarking_kernel_baseChange {c : k →+* R}
    (D : AffineMarkedRealization P generators rank c) (s : sig.SortType) [Algebra R S] :
    Function.Injective ((affineMarkingKernel P generators rank D s).subtype.baseChange S) ∧
      LinearMap.range ((affineMarkingKernel P generators rank D s).subtype.baseChange S) =
        LinearMap.ker ((D.val.marking s).baseChange S) := by
  obtain ⟨t, ht⟩ := affineMarking_split P generators rank D s
  let f := D.val.marking s
  let K := affineMarkingKernel P generators rank D s
  let p : (Fin (generators s) → R) →ₗ[R] K :=
    (LinearMap.id - t.comp f).codRestrict K (fun x => by
      change f (x - t (f x)) = 0
      rw [map_sub, show f (t (f x)) = f x from LinearMap.congr_fun ht (f x), sub_self])
  have hp : p.comp K.subtype = LinearMap.id := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change x.val - t (f x.val) = x.val
    rw [show f x.val = 0 from x.property, map_zero, sub_zero]
  have hsub : K.subtype.comp p = LinearMap.id - t.comp f := rfl
  have hpS : (p.baseChange S).comp (K.subtype.baseChange S) = LinearMap.id := by
    rw [← LinearMap.baseChange_comp, hp, LinearMap.baseChange_id]
  have hsubS : (K.subtype.baseChange S).comp (p.baseChange S) =
      LinearMap.id - (t.baseChange S).comp (f.baseChange S) := by
    rw [← LinearMap.baseChange_comp, hsub, LinearMap.baseChange_sub,
      LinearMap.baseChange_id, LinearMap.baseChange_comp]
  refine ⟨fun x y h => ?_, le_antisymm ?_ ?_⟩
  · have := congrArg (p.baseChange S) h
    change ((p.baseChange S).comp (K.subtype.baseChange S)) x =
      ((p.baseChange S).comp (K.subtype.baseChange S)) y at this
    rwa [hpS] at this
  · rw [LinearMap.range_le_ker_iff, ← LinearMap.baseChange_comp]
    have hf : f.comp K.subtype = 0 := by ext x; exact x.property
    rw [hf, LinearMap.baseChange_zero]
  · intro x hx
    refine ⟨(p.baseChange S) x, ?_⟩
    have h := LinearMap.congr_fun hsubS x
    simpa only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply,
      show (f.baseChange S) x = 0 from hx, map_zero, sub_zero] using h

/-- Quotient recovery commutes with arbitrary scalar extension on actual tensor products. -/
def affineMarkedQuotientBaseChange {c : k →+* R}
    (D : AffineMarkedRealization P generators rank c) (s : sig.SortType) [Algebra R S] :
    (S ⊗[R] ((Fin (generators s) → R) ⧸ affineMarkingKernel P generators rank D s)) ≃ₗ[S]
      (S ⊗[R] D.val.realization.obj.carrier s) :=
  LinearEquiv.baseChange R S _ _ (affineMarkedQuotientIso P generators rank D s)

/-- The small kernel description retains actual multilinear operations on
the fixed quotient modules, rather than only the isomorphism classes of carriers. -/
structure KernelRealizationData (R : Type u) [CommRing R] (generators : sig.SortType → ℕ) where
  /-- Each relation submodule lies in the fixed named free source. -/
  kernel (s : sig.SortType) : Submodule R (Fin (generators s) → R)
  /-- Primitive total maps act on the actual kernel quotient modules. -/
  total (f : sig.Total) :
    TensorOperation R (fun s => ModuleCat.of R ((Fin (generators s) → R) ⧸ kernel s))
      (sig.totalArity f)
  /-- Primitive quantity maps have the same quotient interpretation. -/
  quantity (q : sig.Quantity) :
    TensorOperation R (fun s => ModuleCat.of R ((Fin (generators s) → R) ⧸ kernel s))
      (sig.quantityArity q)

/-- The actual tensor structure associated to a kernel-and-operation description. -/
def KernelRealizationData.toStructure (D : KernelRealizationData (sig := sig) R generators) :
    TensorStructure R sig where
  carrier s := ModuleCat.of R ((Fin (generators s) → R) ⧸ D.kernel s)
  total := D.total
  quantity := D.quantity

/-- Transport the actual operations through the canonical marking quotient isomorphisms. -/
def kernelDataOfMarked {c : k →+* R} (D : AffineMarkedRealization P generators rank c) :
    KernelRealizationData (sig := sig) R generators := by
  let e := affineMarkedQuotientIso P generators rank D
  exact
    { kernel := affineMarkingKernel P generators rank D
      total := fun f => (e _).symm.toLinearMap.compMultilinearMap
        ((D.val.realization.obj.total f).compLinearMap (fun i => (e i.1).toLinearMap))
      quantity := fun q => (e _).symm.toLinearMap.compMultilinearMap
        ((D.val.realization.obj.quantity q).compLinearMap (fun i => (e i.1).toLinearMap)) }

/-- The relation submodules in this description are precisely the original marking kernels. -/
theorem kernelDataOfMarked_kernel {c : k →+* R}
    (D : AffineMarkedRealization P generators rank c) (s : sig.SortType) :
    (kernelDataOfMarked P generators rank D).kernel s = affineMarkingKernel P generators rank D s := by
  rfl

/-- Kernel recovery preserves the actual structure and all named generating vectors. -/
theorem kernelDataOfMarked_comparison {c : k →+* R}
    (D : AffineMarkedRealization P generators rank c) :
    ∃ e : (kernelDataOfMarked P generators rank D).toStructure ≅ D.val.realization.obj,
      ∀ (s : sig.SortType) (x : Fin (generators s) → R),
        e.hom.onSort s (Submodule.Quotient.mk x) = D.val.marking s x := by
  let e := affineMarkedQuotientIso P generators rank D
  refine ⟨{
    hom :=
      { onSort := fun s => (e s).toLinearMap
        preservesTotal := fun f xs => (e _).apply_symm_apply _
        preservesQuantity := fun q xs => (e _).apply_symm_apply _ }
    inv :=
      { onSort := fun s => (e s).symm.toLinearMap
        preservesTotal := fun f xs => by
          change (e _).symm (D.val.realization.obj.total f xs) =
            (e _).symm (D.val.realization.obj.total f (fun i => e i.1 ((e i.1).symm (xs i))))
          simp only [LinearEquiv.apply_symm_apply]
        preservesQuantity := fun q xs => by
          change (e _).symm (D.val.realization.obj.quantity q xs) =
            (e _).symm (D.val.realization.obj.quantity q (fun i => e i.1 ((e i.1).symm (xs i))))
          simp only [LinearEquiv.apply_symm_apply] }
    hom_inv_id := TensorStructure.Hom.ext (funext fun s => by
      apply LinearMap.ext
      intro x
      exact (e s).symm_apply_apply x)
    inv_hom_id := TensorStructure.Hom.ext (funext fun s => by
      apply LinearMap.ext
      intro x
      exact (e s).apply_symm_apply x) }, ?_⟩
  intro s x
  rfl

/-- A comparison of quotient structures that fixes the named quotient generators
identifies their operation data. -/
private theorem kernelData_ext_of_comparison
    (D E : KernelRealizationData (sig := sig) R generators)
    (hK : D.kernel = E.kernel) (e : D.toStructure ≅ E.toStructure)
    (he : ∀ s (x : Fin (generators s) → R),
      e.hom.onSort s (Submodule.Quotient.mk x) = Submodule.Quotient.mk x) : D = E := by
  cases D with
  | mk KD TD QD =>
    cases E with
    | mk KE TE QE =>
      change KD = KE at hK
      subst KE
      have hs (s : sig.SortType) : e.hom.onSort s = LinearMap.id := by
        apply LinearMap.ext
        intro x
        induction x using Submodule.Quotient.induction_on with
        | _ x => exact he s x
      have hT : TD = TE := by
        funext f
        apply MultilinearMap.ext
        intro xs
        have h := e.hom.preservesTotal f xs
        simpa only [hs, LinearMap.id_apply] using h
      have hQ : QD = QE := by
        funext q
        apply MultilinearMap.ext
        intro xs
        have h := e.hom.preservesQuantity q xs
        simpa only [hs, LinearMap.id_apply] using h
      cases hT
      cases hQ
      rfl

/-- Equality of kernel descriptions supplies the identity comparison of all
named quotient vectors, including its dependent kernel types. -/
private theorem kernelData_eq_comparison
    (D E : KernelRealizationData (sig := sig) R generators) (h : D = E) :
    ∃ e : D.toStructure ≅ E.toStructure,
      ∀ s (x : Fin (generators s) → R),
        e.hom.onSort s (Submodule.Quotient.mk x) = Submodule.Quotient.mk x := by
  subst E
  exact ⟨Iso.refl _, fun _ _ => rfl⟩

/-- Equal kernel-and-operation descriptions are exactly marking-preserving
isomorphism classes, establishing the affine statement of Definition 6.3. -/
theorem kernelDataOfMarked_eq_iff {c : k →+* R}
    (D E : AffineMarkedRealization P generators rank c) :
    kernelDataOfMarked P generators rank D = kernelDataOfMarked P generators rank E ↔
      ∃ e : D.val.realization ≅ E.val.realization,
        ∀ s, (e.hom.hom.onSort s).comp (D.val.marking s) = E.val.marking s := by
  obtain ⟨d, hd⟩ := kernelDataOfMarked_comparison P generators rank D
  obtain ⟨e, he⟩ := kernelDataOfMarked_comparison P generators rank E
  constructor
  · intro h
    obtain ⟨a, ha⟩ := kernelData_eq_comparison generators _ _ h
    let z := d.symm ≪≫ a ≪≫ e
    refine ⟨ObjectProperty.isoMk _ z, fun s => ?_⟩
    apply LinearMap.ext
    intro x
    have hinv : d.inv.onSort s (D.val.marking s x) = Submodule.Quotient.mk x := by
      rw [← hd s x]
      exact LinearMap.congr_fun (congrFun
        (congrArg TensorStructure.Hom.onSort d.hom_inv_id) s) _
    change e.hom.onSort s (a.hom.onSort s (d.inv.onSort s (D.val.marking s x))) = _
    rw [hinv, ha, he]
  · rintro ⟨a, ha⟩
    have hK : (kernelDataOfMarked P generators rank D).kernel =
        (kernelDataOfMarked P generators rank E).kernel := by
      funext s
      apply le_antisymm
      · intro x hx
        change D.val.marking s x = 0 at hx
        change E.val.marking s x = 0
        rw [← LinearMap.congr_fun (ha s) x, LinearMap.comp_apply, hx, map_zero]
      · intro x hx
        change E.val.marking s x = 0 at hx
        change D.val.marking s x = 0
        have h := LinearMap.congr_fun (ha s) x
        rw [LinearMap.comp_apply, hx] at h
        have hinv := congrArg (a.inv.hom.onSort s) h
        have hid := LinearMap.congr_fun
          (congrArg (fun m : D.val.realization ⟶ D.val.realization => m.hom.onSort s)
            a.hom_inv_id) (D.val.marking s x)
        simpa only [map_zero] using hid.symm.trans hinv
    apply kernelData_ext_of_comparison generators _ _ hK (d ≪≫
      { hom := a.hom.hom
        inv := a.inv.hom
        hom_inv_id := congrArg (fun m : D.val.realization ⟶ D.val.realization => m.hom) a.hom_inv_id
        inv_hom_id := congrArg (fun m : E.val.realization ⟶ E.val.realization => m.hom) a.inv_hom_id } ≪≫ e.symm)
    intro s x
    change e.inv.onSort s (a.hom.hom.onSort s (d.hom.onSort s (Submodule.Quotient.mk x))) = _
    have h := LinearMap.congr_fun (ha s) x
    rw [LinearMap.comp_apply] at h
    rw [hd, h, ← he s x]
    exact LinearMap.congr_fun (congrFun
      (congrArg TensorStructure.Hom.onSort e.hom_inv_id) s) _

variable {X Y : Scheme.{u}}

/-- Markings on arbitrary finite locally free scheme realizations. -/
structure SchemeMarkedData (b : X ⟶ Spec (CommRingCat.of k)) where
  /-- The existing scheme realization, including its actual sheaf operations. -/
  realization : SchemeRealization P rank b
  /-- A marking is a morphism from the actual finite free module sheaf. -/
  marking (s : sig.SortType) : freeModuleSheaf X (generators s) ⟶ realization.obj.carrier s

namespace SchemeMarkedData

variable {P generators rank} {b : X ⟶ Spec (CommRingCat.of k)}

/-- Actual structure-preserving sheaf morphisms which also preserve every marking. -/
structure Hom (A B : SchemeMarkedData P generators rank b) where
  /-- The underlying map in the full realization category. -/
  realization : A.realization ⟶ B.realization
  /-- Each named generating map commutes with the carrier map. -/
  preserves (s : sig.SortType) : A.marking s ≫ realization.hom.onSort s = B.marking s

/-- The realization map determines a marking-preserving morphism. -/
@[ext]
theorem Hom.ext {A B : SchemeMarkedData P generators rank b} {f g : Hom A B}
    (h : f.realization = g.realization) : f = g := by
  cases f
  cases g
  cases h
  rfl

/-- Marked maps form the ordinary category before restricting to surjective markings. -/
instance : Category (SchemeMarkedData P generators rank b) where
  Hom := Hom
  id A := ⟨𝟙 _, fun _ => by simp⟩
  comp f g := ⟨f.realization ≫ g.realization, fun s => by
    change _ ≫ (f.realization.hom.onSort s ≫ g.realization.hom.onSort s) = _
    rw [← Category.assoc, f.preserves, g.preserves]⟩
  id_comp := by
    intros
    congr 1
  comp_id := by
    intros
    congr 1
  assoc := by
    intros
    congr 1

/-- Surjectivity is epimorphy in the actual module-sheaf category. -/
def IsSurjective (A : SchemeMarkedData P generators rank b) : Prop :=
  ∀ s, Epi (A.marking s)

end SchemeMarkedData

/-- The independent surjectivity predicate as a mathlib object property. -/
def schemeMarkedProperty (b : X ⟶ Spec (CommRingCat.of k)) :
    ObjectProperty (SchemeMarkedData P generators rank b) := fun A => A.IsSurjective

/-- The full category of realizations with surjective markings, Definition 6.3. -/
abbrev SchemeMarkedRealization (b : X ⟶ Spec (CommRingCat.of k)) :=
  (schemeMarkedProperty P generators rank b).FullSubcategory

/-- A based realization uses an actual isomorphism from the finite free
module sheaf, as distinguished from a marking with extra generators. -/
structure SchemeBasedRealization (b : X ⟶ Spec (CommRingCat.of k)) where
  /-- The underlying realization with its actual module sheaves. -/
  realization : SchemeRealization P rank b
  /-- One chosen basis isomorphism per sort. -/
  basis (s : sig.SortType) : freeModuleSheaf X (rank s) ≅ realization.obj.carrier s

/-- The selected columns define a genuine map between finite free sheaves. -/
def selectedGeneratorMap (I : ChartIndex (sig := sig) generators rank) (s : sig.SortType) :
    freeModuleSheaf X (rank s) ⟶ freeModuleSheaf X (generators s) :=
  SheafOfModules.freeMap (R := X.ringCatSheaf) (fun a : ULift.{u} (Fin (rank s)) =>
    (⟨I s a.down⟩ : ULift.{u} (Fin (generators s))))

/-- On a marked realization, the selected columns form a basis precisely
when their actual map of sheaves is invertible. -/
def hasBasisColumns {b : X ⟶ Spec (CommRingCat.of k)}
    (I : ChartIndex (sig := sig) generators rank) :
    ObjectProperty (SchemeMarkedRealization P generators rank b) := fun A =>
  ∀ s, IsIso (selectedGeneratorMap generators rank I s ≫ A.obj.marking s)

/-- The groupoid of marked realizations retains the original isomorphisms. -/
abbrev SchemeMarkedCore (b : X ⟶ Spec (CommRingCat.of k)) :=
  Core (SchemeMarkedRealization P generators rank b)

/-- Surjective markings force uniqueness of every marking-preserving morphism. -/
theorem schemeMarked_hom_subsingleton {b : X ⟶ Spec (CommRingCat.of k)}
    (A B : SchemeMarkedRealization P generators rank b) : Subsingleton (A ⟶ B) := by
  refine ⟨fun f g => ?_⟩
  apply ObjectProperty.hom_ext
  have h : f.hom.realization = g.hom.realization := by
    apply ObjectProperty.hom_ext
    apply SchemeTensorStructure.Hom.ext
    intro s
    letI : Epi (A.obj.marking s) := A.property s
    apply (cancel_epi (A.obj.marking s)).1
    exact (f.hom.preserves s).trans (g.hom.preserves s).symm
  cases f with
  | mk f =>
    cases g with
    | mk g =>
      change f = g
      cases f
      cases g
      cases h
      rfl

/-- In particular, every marking-preserving endomorphism is the identity. -/
theorem schemeMarked_endomorphism_eq_id {b : X ⟶ Spec (CommRingCat.of k)}
    (A : SchemeMarkedRealization P generators rank b) (a : A ⟶ A) : a = 𝟙 A :=
  (schemeMarked_hom_subsingleton P generators rank A A).elim _ _

/-- Carrier isomorphisms whose diagrams commute determine an isomorphism
of the actual scheme tensor structures. -/
private def schemeStructureIsoOfCarrierIso
    (A B : SchemeTensorStructure X sig) (e : ∀ s, A.carrier s ≅ B.carrier s)
    (hTotal : ∀ f, A.total f ≫ (e _).hom =
      tensorModulesMap (fun s => (e s).hom) _ ≫ B.total f)
    (hQuantity : ∀ q, A.quantity q ≫ (e _).hom =
      tensorModulesMap (fun s => (e s).hom) _ ≫ B.quantity q) : A ≅ B where
  hom := { onSort := fun s => (e s).hom
           preservesTotal := hTotal
           preservesQuantity := hQuantity }
  inv :=
    { onSort := fun s => (e s).inv
      preservesTotal := fun f => by
        apply (cancel_mono (e _).hom).1
        rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
        rw [Category.assoc, hTotal, ← Category.assoc, ← tensorModulesMap_comp]
        simp only [Iso.inv_hom_id, tensorModulesMap_id, Category.id_comp]
      preservesQuantity := fun q => by
        apply (cancel_mono (e _).hom).1
        rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
        rw [Category.assoc, hQuantity, ← Category.assoc, ← tensorModulesMap_comp]
        simp only [Iso.inv_hom_id, tensorModulesMap_id, Category.id_comp] }
  hom_inv_id := SchemeTensorStructure.Hom.ext (fun s => (e s).hom_inv_id)
  inv_hom_id := SchemeTensorStructure.Hom.ext (fun s => (e s).inv_hom_id)

/-- Transport the actual primitive sheaf operations along a carrier family
of isomorphisms. The input tensors include the empty tensor. -/
private def schemeStructureTransport (A : SchemeTensorStructure X sig)
    (K : sig.SortType → X.Modules) (e : ∀ s, K s ≅ A.carrier s) :
    SchemeTensorStructure X sig where
  carrier := K
  total f := tensorModulesMap (fun s => (e s).hom) _ ≫ A.total f ≫ (e _).inv
  quantity q := tensorModulesMap (fun s => (e s).hom) _ ≫ A.quantity q ≫ (e _).inv

/-- The transported operations recover the original structure via the
specified carrier isomorphisms. -/
private def schemeStructureTransportIso (A : SchemeTensorStructure X sig)
    (K : sig.SortType → X.Modules) (e : ∀ s, K s ≅ A.carrier s) :
    schemeStructureTransport A K e ≅ A :=
  schemeStructureIsoOfCarrierIso _ _ e
    (fun f => by
      change (tensorModulesMap _ _ ≫ A.total f ≫ (e _).inv) ≫ (e _).hom = _
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id])
    (fun q => by
      change (tensorModulesMap _ _ ≫ A.quantity q ≫ (e _).inv) ≫ (e _).hom = _
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id])

/-- Lift a realization isomorphism preserving a marking to the category
of marked data. The inverse preserves the marking by the inverse identity. -/
private def schemeMarkedDataIsoOfRealizationIso
    {b : X ⟶ Spec (CommRingCat.of k)} (A B : SchemeMarkedData P generators rank b)
    (e : A.realization ≅ B.realization)
    (h : ∀ s, A.marking s ≫ e.hom.hom.onSort s = B.marking s) : A ≅ B where
  hom := ⟨e.hom, h⟩
  inv := ⟨e.inv, fun s => by
    have hz : e.hom.hom.onSort s ≫ e.inv.hom.onSort s = 𝟙 _ :=
      congrArg (fun m : A.realization ⟶ A.realization => m.hom.onSort s) e.hom_inv_id
    have hm := congrArg (fun m => m ≫ e.inv.hom.onSort s) (h s)
    change (A.marking s ≫ e.hom.hom.onSort s) ≫ e.inv.hom.onSort s =
      B.marking s ≫ e.inv.hom.onSort s at hm
    rw [Category.assoc, hz, Category.comp_id] at hm
    exact hm.symm⟩
  hom_inv_id := SchemeMarkedData.Hom.ext e.hom_inv_id
  inv_hom_id := SchemeMarkedData.Hom.ext e.inv_hom_id

/-- A common quotient structure identifies two marked realizations when
its structure isomorphisms preserve every named generator. -/
private theorem schemeMarked_isomorphic_of_normalization
    {b : X ⟶ Spec (CommRingCat.of k)}
    (A B : SchemeMarkedRealization P generators rank b)
    (C : SchemeTensorStructure X sig)
    (p : ∀ s, freeModuleSheaf X (generators s) ⟶ C.carrier s)
    (eA : C ≅ A.obj.realization.obj)
    (eB : C ≅ B.obj.realization.obj)
    (hA : ∀ s, p s ≫ eA.hom.onSort s = A.obj.marking s)
    (hB : ∀ s, p s ≫ eB.hom.onSort s = B.obj.marking s) : Nonempty (A ≅ B) := by
  let z := eA.symm ≪≫ eB
  have hforward (s : sig.SortType) :
      A.obj.marking s ≫ z.hom.onSort s = B.obj.marking s := by
    change A.obj.marking s ≫ (eA.inv.onSort s ≫ eB.hom.onSort s) = _
    have hz : eA.hom.onSort s ≫ eA.inv.onSort s = 𝟙 _ :=
      congrArg (fun m : C ⟶ C => m.onSort s) eA.hom_inv_id
    rw [← hA s, Category.assoc, ← Category.assoc (eA.hom.onSort s),
      hz, Category.id_comp, hB]
  exact ⟨ObjectProperty.isoMk _
    (schemeMarkedDataIsoOfRealizationIso P generators rank A.obj B.obj
      (ObjectProperty.isoMk _ z) hforward)⟩

/-- A mono-preserving functor maps subobjects by applying the functor to their arrows. -/
private def mapSubobjects {C : Type v} [Category.{w} C] {D : Type v'} [Category.{w'} D]
    (F : C ⥤ D) [F.PreservesMonomorphisms] (X : C) :
    Subobject X → Subobject (F.obj X) :=
  Subobject.lift (fun {_} f _ => Subobject.mk (F.map f)) (fun {_} {_} f g _ _ e h =>
    Subobject.mk_eq_mk_of_comm _ _ (F.mapIso e) (by simpa using congrArg F.map h))

/-- A fully faithful functor reflects equality of subobjects. -/
private theorem mapSubobjects_injective {C : Type v} [Category.{w} C]
    {D : Type v'} [Category.{w'} D] (F : C ⥤ D) [F.Full] [F.Faithful]
    [F.PreservesMonomorphisms] (X : C) : Function.Injective (mapSubobjects F X) := by
  intro A B h
  induction A using Subobject.ind with | _ f =>
    induction B using Subobject.ind with | _ g =>
      change Subobject.mk (F.map f) = Subobject.mk (F.map g) at h
      let e := Subobject.isoOfMkEqMk _ _ h
      apply Subobject.mk_eq_mk_of_comm f g (F.preimageIso e)
      apply F.map_injective
      simp [e]

/-- Module sheaves are well-powered by the fully faithful inclusion in module presheaves. -/
private theorem sheafWellPowered (X : Scheme.{u}) : WellPowered.{u} X.Modules := by
  let F := SheafOfModules.forget X.ringCatSheaf
  letI : F.IsRightAdjoint := (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.val)).isRightAdjoint
  exact ⟨fun M => small_of_injective (mapSubobjects_injective F M)⟩


/-- Regard a surjective marking as a quotient object, using the subobject
category of the opposite module-sheaf category. -/
private def quotientFamily {b : X ⟶ Spec (CommRingCat.of k)}
    (A : SchemeMarkedRealization P generators rank b) (s : sig.SortType) :
    Subobject (op (freeModuleSheaf X (generators s))) := by
  letI : Epi (A.obj.marking s) := A.property s
  exact Subobject.mk (A.obj.marking s).op

/-- The chosen carrier of a quotient object in the opposite category. -/
private def quotientCarrier (Q : ∀ s : sig.SortType,
    Subobject (op (freeModuleSheaf X (generators s)))) (s : sig.SortType) : X.Modules :=
  unop (Q s : X.Modulesᵒᵖ)

/-- The canonical quotient-object carrier recovers the original marked carrier. -/
private def quotientIso {b : X ⟶ Spec (CommRingCat.of k)}
    (A : SchemeMarkedRealization P generators rank b) (s : sig.SortType) :
    quotientCarrier generators (quotientFamily P generators rank A) s ≅ A.obj.realization.obj.carrier s := by
  letI : Epi (A.obj.marking s) := A.property s
  exact (Subobject.underlyingIso (A.obj.marking s).op).unop.symm

/-- Quotient objects and their actual primitive morphisms form a small code
for the underlying marked structures. -/
private def markedCodeType :=
  Σ Q : (∀ s : sig.SortType, Subobject (op (freeModuleSheaf X (generators s)))),
    ((∀ f : sig.Total,
      tensorModules (quotientCarrier generators Q) (sig.totalArity f).inputs ⟶
        quotientCarrier generators Q (sig.totalArity f).output) ×
     (∀ q : sig.Quantity,
      tensorModules (quotientCarrier generators Q) (sig.quantityArity q).inputs ⟶
        quotientCarrier generators Q (sig.quantityArity q).output))

/-- Well-poweredness of module sheaves makes the quotient-operation code small. -/
private theorem markedCodeType_small : Small.{u} (markedCodeType (X := X) generators) := by
  letI := sheafWellPowered X
  unfold markedCodeType
  infer_instance

/-- Normalize a marked structure onto its canonical quotient carriers. -/
private def markedCode {b : X ⟶ Spec (CommRingCat.of k)}
    (A : SchemeMarkedRealization P generators rank b) : markedCodeType (X := X) generators :=
  let T := schemeStructureTransport A.obj.realization.obj _ (quotientIso P generators rank A)
  ⟨quotientFamily P generators rank A, T.total, T.quantity⟩

/-- Read the actual quotient sheaf structure represented by a small code. -/
private def codeStructure (c : markedCodeType (X := X) generators) : SchemeTensorStructure X sig :=
  { carrier := quotientCarrier generators c.1, total := c.2.1, quantity := c.2.2 }

/-- Normalizing the quotient carriers preserves the actual structure. -/
private def markedCodeIso {b : X ⟶ Spec (CommRingCat.of k)}
    (A : SchemeMarkedRealization P generators rank b) :
    codeStructure generators (markedCode P generators rank A) ≅ A.obj.realization.obj :=
  schemeStructureTransportIso A.obj.realization.obj _ (quotientIso P generators rank A)

/-- Quotient-object normalization preserves the original surjective map. -/
private theorem quotientIso_marking {b : X ⟶ Spec (CommRingCat.of k)}
    (A : SchemeMarkedRealization P generators rank b) (s : sig.SortType) :
    (quotientFamily P generators rank A s).arrow.unop ≫
      (quotientIso P generators rank A s).hom = A.obj.marking s := by
  letI : Epi (A.obj.marking s) := A.property s
  exact congrArg Quiver.Hom.unop (Subobject.underlyingIso_arrow (A.obj.marking s).op)

/-- The normalized structure isomorphism retains the named marking. -/
private theorem markedCodeIso_marking {b : X ⟶ Spec (CommRingCat.of k)}
    (A : SchemeMarkedRealization P generators rank b) (s : sig.SortType) :
    ((markedCode P generators rank A).1 s).arrow.unop ≫
      (markedCodeIso P generators rank A).hom.onSort s = A.obj.marking s := by
  exact quotientIso_marking P generators rank A s

/-- An equal code supplies the same normalized structure comparison. -/
private def markedCodeIsoOfEq {b : X ⟶ Spec (CommRingCat.of k)}
    (c : markedCodeType (X := X) generators)
    (A : SchemeMarkedRealization P generators rank b) (h : c = markedCode P generators rank A) :
    codeStructure generators c ≅ A.obj.realization.obj :=
  eqToIso (congrArg (codeStructure generators) h) ≪≫ markedCodeIso P generators rank A

/-- Transport of code equality preserves every named quotient map. -/
private theorem markedCodeIsoOfEq_marking {b : X ⟶ Spec (CommRingCat.of k)}
    (c : markedCodeType (X := X) generators)
    (A : SchemeMarkedRealization P generators rank b) (h : c = markedCode P generators rank A)
    (s : sig.SortType) :
    (c.1 s).arrow.unop ≫
      (markedCodeIsoOfEq P generators rank c A h).hom.onSort s = A.obj.marking s := by
  subst c
  exact markedCodeIso_marking P generators rank A s

/-- Equal quotient-operation codes determine marking-preserving isomorphisms. -/
private theorem markedCode_eq_isomorphic {b : X ⟶ Spec (CommRingCat.of k)}
    (A B : SchemeMarkedRealization P generators rank b)
    (h : markedCode P generators rank A = markedCode P generators rank B) : Nonempty (A ≅ B) := by
  exact schemeMarked_isomorphic_of_normalization P generators rank A B
    (codeStructure generators (markedCode P generators rank A))
    (fun s => ((markedCode P generators rank A).1 s).arrow.unop)
    (markedCodeIso P generators rank A)
    (markedCodeIsoOfEq P generators rank _ B h)
    (markedCodeIso_marking P generators rank A)
    (markedCodeIsoOfEq_marking P generators rank _ B h)

/-- The actual isomorphism-class type is small, by quotient-object descriptions
in the well-powered abelian module-sheaf category. Primitive operations remain
actual sheaf morphisms; smallness is proved rather than assumed. -/
instance markedIsoClassesSmall (b : X ⟶ Spec (CommRingCat.of k)) :
    Small.{u} (Quotient (isIsomorphicSetoid (SchemeMarkedRealization P generators rank b))) := by
  letI := markedCodeType_small (X := X) generators
  let encode : Quotient (isIsomorphicSetoid (SchemeMarkedRealization P generators rank b)) →
      markedCodeType (X := X) generators := fun q => markedCode P generators rank q.out
  apply small_of_injective (f := encode)
  intro q r h
  have hi := markedCode_eq_isomorphic P generators rank q.out r.out h
  exact q.out_eq.symm.trans ((Quotient.sound hi).trans r.out_eq)

/-- The small set `Mark_{m,n}(T)` of Definition 6.3. -/
abbrev Mark (b : X ⟶ Spec (CommRingCat.of k)) :=
  Shrink.{u} (Quotient (isIsomorphicSetoid (SchemeMarkedRealization P generators rank b)))

/-- The marked groupoid is equivalent to its small discrete set of isomorphism classes. -/
def markedCoreEquivDiscrete (b : X ⟶ Spec (CommRingCat.of k)) :
    SchemeMarkedCore P generators rank b ≌ Discrete (Mark P generators rank b) := by
  let C := SchemeMarkedRealization P generators rank b
  let q : C → Mark P generators rank b := fun A => (equivShrink _).toFun (Quotient.mk _ A)
  let F : Core C ⥤ Discrete (Mark P generators rank b) :=
    { obj := fun A => Discrete.mk (q A.of)
      map := fun m => Discrete.eqToHom (congrArg (equivShrink _).toFun
        (Quotient.sound (show IsIsomorphic _ _ from ⟨m.iso⟩))) }
  letI : F.Faithful :=
    { map_injective := fun {A B} f g _ => Core.hom_ext
        ((schemeMarked_hom_subsingleton P generators rank A.of B.of).elim _ _) }
  letI : F.Full :=
    { map_surjective := fun {A B} m => by
        have h : q A.of = q B.of := Discrete.eq_of_hom m
        have h' : Quotient.mk (isIsomorphicSetoid C) A.of = Quotient.mk _ B.of :=
          (equivShrink _).injective h
        obtain ⟨e⟩ := Quotient.exact h'
        exact ⟨⟨e⟩, Subsingleton.elim _ _⟩ }
  letI : F.EssSurj :=
    { mem_essImage := fun A => by
        let a := (equivShrink (Quotient (isIsomorphicSetoid C))).symm A.as
        refine ⟨⟨a.out⟩, ⟨eqToIso ?_⟩⟩
        apply Discrete.ext
        change (equivShrink _).toFun (Quotient.mk _ a.out) = A.as
        rw [Quotient.out_eq]
        exact (equivShrink _).apply_symm_apply A.as }
  letI : F.IsEquivalence := {}
  exact F.asEquivalence

/-- The canonical free-sheaf comparison for the named finite generators. -/
private def freeModuleSheafPullbackIso (f : Y ⟶ X) (m : ℕ) :
    (Scheme.Modules.pullback f).obj (freeModuleSheaf X m) ≅ freeModuleSheaf Y m := by
  letI : (TopologicalSpace.Opens.map f.base).Final := ⟨fun U => by
    let T : StructuredArrow U (TopologicalSpace.Opens.map f.base) :=
      StructuredArrow.mk (homOfLE (show U ≤ f ⁻¹ᵁ (⊤ : X.Opens) from by simp))
    exact isConnected_of_isTerminal (StructuredArrow U (TopologicalSpace.Opens.map f.base)) (x := T)
      { lift := fun A => StructuredArrow.homMk (homOfLE le_top)
        uniq := fun A m _ => StructuredArrow.hom_ext _ _ (Subsingleton.elim _ _) }⟩
  exact SheafOfModules.pullbackObjFreeIso f.toRingCatSheafHom (ULift.{u} (Fin m))

/-- Actual pullback of the sheaf realization and its named generating maps. -/
def schemeMarkedPullback (f : Y ⟶ X) (b : X ⟶ Spec (CommRingCat.of k)) :
    SchemeMarkedRealization P generators rank b ⥤
      SchemeMarkedRealization P generators rank (f ≫ b) := by
  refine
    { obj := fun A => ⟨
        { realization := (schemeRealizationPullback P rank b f).obj A.obj.realization
          marking := fun s => (freeModuleSheafPullbackIso f (generators s)).inv ≫
            (Scheme.Modules.pullback f).map (A.obj.marking s) }, ?_⟩
      map := fun m => ObjectProperty.homMk
        { realization := (schemeRealizationPullback P rank b f).map m.hom.realization
          preserves := fun s => ?_ }
      map_id := fun A => ?_
      map_comp := fun m n => ?_ }
  · intro s
    letI : Epi (A.obj.marking s) := A.property s
    change Epi ((freeModuleSheafPullbackIso f (generators s)).inv ≫
      (Scheme.Modules.pullback f).map (A.obj.marking s))
    infer_instance
  · change (_ ≫ (Scheme.Modules.pullback f).map _) ≫
      (Scheme.Modules.pullback f).map _ = _
    rw [Category.assoc, ← Functor.map_comp]
    change (freeModuleSheafPullbackIso f (generators s)).inv ≫
      (Scheme.Modules.pullback f).map (_ ≫ m.hom.realization.hom.onSort s) = _
    rw [m.hom.preserves]
  · exact (schemeMarked_hom_subsingleton P generators rank _ _).elim _ _
  · exact (schemeMarked_hom_subsingleton P generators rank _ _).elim _ _

/-- The carrier of the marked pullback is the actual module-sheaf pullback. -/
def schemeMarkedPullbackCarrierIso (f : Y ⟶ X) (b : X ⟶ Spec (CommRingCat.of k))
    (A : SchemeMarkedRealization P generators rank b) (s : sig.SortType) :
    (Scheme.Modules.pullback f).obj (A.obj.realization.obj.carrier s) ≅
      ((schemeMarkedPullback P generators rank f b).obj A).obj.realization.obj.carrier s := by
  exact Iso.refl _

/-- Pullback on the small isomorphism-class sets, induced by the actual functor. -/
def markPullback (f : Y ⟶ X) (b : X ⟶ Spec (CommRingCat.of k)) :
    Mark P generators rank b → Mark P generators rank (f ≫ b) := by
  let action : Quotient (isIsomorphicSetoid (SchemeMarkedRealization P generators rank b)) →
      Quotient (isIsomorphicSetoid (SchemeMarkedRealization P generators rank (f ≫ b))) :=
    Quotient.map (schemeMarkedPullback P generators rank f b).obj
      (fun _ _ h => ⟨(schemeMarkedPullback P generators rank f b).mapIso h.some⟩)
  exact (equivShrink _).toFun ∘ action ∘ (equivShrink _).invFun

end

end SHIGURE.RealizationFamilies.Marked
