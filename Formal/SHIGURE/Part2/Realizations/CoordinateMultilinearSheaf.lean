import Formal.SHIGURE.Part2.Schemes.ModuleSheafMultilinear
import Formal.SHIGURE.Part2.Realizations.CoordinateModuleSheaf
import Formal.SHIGURE.Part2.Realizations.PrimitiveCoordinates

/-! # Coordinate operations on the actual free sheaves -/

namespace SHIGURE.RealizationFamilies

open AlgebraicGeometry CategoryTheory Opposite SHIGURE.SchemeDescent
open Module

noncomputable section

universe u

variable (X : Scheme.{u}) {I : Type u} [Fintype I] (n : I → ℕ) (r : ℕ)

private abbrev topOpen : X.Opensᵒᵖ := op (⊤ : X.Opens)

private abbrev sectionsRing (U : X.Opensᵒᵖ) := X.sheaf.val.obj U

private def fromTop (U : X.Opensᵒᵖ) : sectionsRing X (topOpen X) →+* sectionsRing X U :=
  (X.sheaf.val.map ((homOfLE (le_top (a := U.unop))).op)).hom

private theorem fromTop_restrict {U V : X.Opensᵒᵖ} (g : U ⟶ V)
    (a : sectionsRing X (topOpen X)) :
    (X.sheaf.val.map g).hom (fromTop X U a) = fromTop X V a := by
  unfold fromTop
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

variable (c : (∀ i, Fin (n i)) → Fin r → sectionsRing X (topOpen X))

/-- The original multilinear map on sections of the chosen open, obtained
by restricting the global operation coefficients. -/
def coordinateMultilinearApp (U : X.Opensᵒᵖ) :
    MultilinearMap (sectionsRing X U) (fun i => (coordinateModuleSheaf X (n i)).val.obj U)
      ((coordinateModuleSheaf X r).val.obj U) := by
  let RU := sectionsRing X U
  let output : (Fin r → RU) →ₗ[RU] (coordinateModuleSheaf X r).val.obj U :=
    (coordinateModuleSectionIso X r U).inv.hom
  let input (i : I) : (coordinateModuleSheaf X (n i)).val.obj U →ₗ[RU] (Fin (n i) → RU) :=
    (coordinateModuleSectionIso X (n i) U).hom.hom
  let operation : MultilinearMap RU (fun i => Fin (n i) → RU) (Fin r → RU) :=
    multilinearOfCoefficients (fun i => Pi.basisFun RU (Fin (n i))) (Pi.basisFun RU (Fin r))
      (fun a j => fromTop X U (c a j))
  exact output.compMultilinearMap (operation.compLinearMap input)

/-- The value in each output row is the standard polynomial in the
local input coordinates and the restricted global coefficients. -/
theorem coordinateMultilinearApp_coordinates (U : X.Opensᵒᵖ)
    (x : ∀ i, (coordinateModuleSheaf X (n i)).val.obj U) (j : Fin r) :
    letI : DecidableEq I := Classical.decEq I
    (coordinateModuleSectionIso X r U).hom (coordinateMultilinearApp X n r c U x) j =
      ∑ a : (∀ i, Fin (n i)), fromTop X U (c a j) *
        ∏ i, (coordinateModuleSectionIso X (n i) U).hom (x i) (a i) := by
  let e := coordinateModuleSectionIso X r U
  let z (i : I) := (coordinateModuleSectionIso X (n i) U).hom (x i)
  let RU := sectionsRing X U
  let y : Fin r → RU := multilinearOfCoefficients (fun i => Pi.basisFun RU (Fin (n i)))
    (Pi.basisFun RU (Fin r))
    (fun a j => fromTop X U (c a j)) z
  have recover : e.hom (e.inv y) = y := congrArg (fun m => m y) e.inv_hom_id
  change e.hom (e.inv y) j = _
  exact (congrFun recover j).trans
    (multilinearOfCoefficients_coordinates (fun a j => fromTop X U (c a j)) z j)

/-- The local maps preserve restriction, yielding the actual compatible family. -/
def coordinateMultilinearFamily :
    MultilinearSectionFamily (R := X.sheaf.val)
      (fun i => (coordinateModuleSheaf X (n i)).val) (coordinateModuleSheaf X r).val where
  app := coordinateMultilinearApp X n r c
  naturality {U V} g x := by
    classical
    let e := coordinateModuleSectionIso X r V
    apply (e.toLinearEquiv).injective
    funext j
    change e.hom ((coordinateModuleSheaf X r).val.map g (coordinateMultilinearApp X n r c U x)) j =
      e.hom (coordinateMultilinearApp X n r c V (fun i => (coordinateModuleSheaf X (n i)).val.map g (x i))) j
    rw [coordinateModuleSectionIso_restrict, coordinateMultilinearApp_coordinates, coordinateMultilinearApp_coordinates]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [map_mul, fromTop_restrict, map_prod]
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    exact (coordinateModuleSectionIso_restrict X (n i) g (x i) (a i)).symm

/-- The reconstructed operation is a morphism of the sheafified tensor of
the actual carrier modules. -/
def coordinateMultilinearOperation :
    moduleMultilinearTensor (fun i => coordinateModuleSheaf X (n i)) ⟶ coordinateModuleSheaf X r :=
  (moduleMultilinearTensorHomEquiv _ _).symm (coordinateMultilinearFamily X n r c)

private def coordinateBasis (m : ℕ) (U : X.Opensᵒᵖ) :
    Basis (Fin m) (sectionsRing X U) ((coordinateModuleSheaf X m).val.obj U) :=
  (Pi.basisFun (sectionsRing X U) (Fin m)).map (coordinateModuleSectionIso X m U).toLinearEquiv.symm

private theorem coordinateBasis_in_coordinates (m : ℕ) (U : X.Opensᵒᵖ) (j : Fin m) :
    (coordinateModuleSectionIso X m U).hom (coordinateBasis X m U j) = Pi.basisFun (sectionsRing X U) _ j :=
  (coordinateModuleSectionIso X m U).toLinearEquiv.apply_symm_apply _

private theorem coordinateBasis_restrict (m : ℕ) {U V : X.Opensᵒᵖ} (g : U ⟶ V)
    (j : Fin m) :
    (coordinateModuleSheaf X m).val.map g (coordinateBasis X m U j) = coordinateBasis X m V j := by
  classical
  apply (coordinateModuleSectionIso X m V).toLinearEquiv.injective
  funext i
  change (coordinateModuleSectionIso X m V).hom
      ((coordinateModuleSheaf X m).val.map g (coordinateBasis X m U j)) i =
    (coordinateModuleSectionIso X m V).hom (coordinateBasis X m V j) i
  rw [coordinateModuleSectionIso_restrict, coordinateBasis_in_coordinates, coordinateBasis_in_coordinates]
  simp [Pi.basisFun_apply, Pi.single_apply]

private theorem coordinateMultilinearApp_onBasis (U : X.Opensᵒᵖ)
    (a : ∀ i, Fin (n i)) (j : Fin r) :
    (coordinateModuleSectionIso X r U).hom
      (coordinateMultilinearApp X n r c U (fun i => coordinateBasis X (n i) U (a i))) j =
        fromTop X U (c a j) := by
  let e := coordinateModuleSectionIso X r U
  let RU := sectionsRing X U
  let basis (i : I) := Pi.basisFun RU (Fin (n i))
  let x (i : I) := (coordinateModuleSectionIso X (n i) U).hom (coordinateBasis X (n i) U (a i))
  let y : Fin r → RU := multilinearOfCoefficients basis (Pi.basisFun RU (Fin r))
    (fun a j => fromTop X U (c a j)) x
  have recover : e.hom (e.inv y) = y := congrArg (fun m => m y) e.inv_hom_id
  change e.hom (e.inv y) j = _
  rw [recover]
  change multilinearOfCoefficients basis (Pi.basisFun RU (Fin r)) (fun b k => fromTop X U (c b k))
    (fun i => (coordinateModuleSectionIso X (n i) U).hom (coordinateBasis X (n i) U (a i))) j = _
  rw [funext (fun i => coordinateBasis_in_coordinates X (n i) U (a i))]
  rw [multilinearOfCoefficients_basis, Pi.basisFun_equivFun, LinearEquiv.refl_symm, LinearEquiv.refl_apply]

variable (h : MultilinearSectionFamily (R := X.sheaf.val)
  (fun i => (coordinateModuleSheaf X (n i)).val) (coordinateModuleSheaf X r).val)

/-- Read the coefficients of the original compatible operation on the
globally chosen unit coordinate vectors. -/
def coordinateMultilinearRead : (∀ i, Fin (n i)) → Fin r → sectionsRing X (topOpen X) :=
  fun a j => (coordinateModuleSectionIso X r (topOpen X)).hom
    (h.app (topOpen X) (fun i => coordinateBasis X (n i) (topOpen X) (a i))) j

private theorem fromTop_self (x : sectionsRing X (topOpen X)) : fromTop X (topOpen X) x = x := by
  unfold fromTop
  let g : topOpen X ⟶ topOpen X := (homOfLE (le_top (a := (⊤ : X.Opens)))).op
  have eq : g = 𝟙 _ := Subsingleton.elim _ _
  change ((X.sheaf.val).map g).hom x = x
  rw [eq]
  exact congrArg (fun k : X.sheaf.val.obj (topOpen X) ⟶ X.sheaf.val.obj (topOpen X) => k.hom x)
    (X.sheaf.val.map_id (topOpen X))

/-- Reading the operation created from global coefficients recovers the exact array. -/
theorem coordinateMultilinearRead_reconstruct :
    coordinateMultilinearRead X n r (coordinateMultilinearFamily X n r c) = c := by
  funext a j
  exact (coordinateMultilinearApp_onBasis X n r c (topOpen X) a j).trans (fromTop_self X _)

private theorem coordinateBasis_repr (m : ℕ) (U : X.Opensᵒᵖ)
    (x : (coordinateModuleSheaf X m).val.obj U) (j : Fin m) :
    (coordinateBasis X m U).repr x j = (coordinateModuleSectionIso X m U).hom x j := by
  change (Pi.basisFun (sectionsRing X U) (Fin m)).repr
    ((coordinateModuleSectionIso X m U).hom x) j = _
  rw [← Basis.equivFun_apply, Pi.basisFun_equivFun]
  rfl

/-- The actual operation is recovered on every open from its global
coefficients, using compatibility with the restriction of each basis vector. -/
theorem coordinateMultilinearFamily_read :
    coordinateMultilinearFamily X n r (coordinateMultilinearRead X n r h) = h := by
  apply MultilinearSectionFamily.ext
  funext U
  apply (multilinearCoefficientsEquiv (fun i => coordinateBasis X (n i) U) (coordinateBasis X r U)).injective
  funext a j
  let x (i : I) := coordinateBasis X (n i) (topOpen X) (a i)
  let g : topOpen X ⟶ U := (homOfLE (le_top (a := U.unop))).op
  have restrict : (fun i => (coordinateModuleSheaf X (n i)).val.map g (x i)) =
      (fun i => coordinateBasis X (n i) U (a i)) := by
    funext i
    exact coordinateBasis_restrict X (n i) g (a i)
  have operation := (h.naturality g x).trans (congrArg (h.app U) restrict)
  change (coordinateBasis X r U).repr
      (coordinateMultilinearApp X n r (coordinateMultilinearRead X n r h) U
        (fun i => coordinateBasis X (n i) U (a i))) j =
    (coordinateBasis X r U).repr (h.app U (fun i => coordinateBasis X (n i) U (a i))) j
  rw [coordinateBasis_repr, coordinateBasis_repr, coordinateMultilinearApp_onBasis]
  exact (coordinateModuleSectionIso_restrict X r g (h.app (topOpen X) x) j).symm.trans
    (congrArg (fun y => (coordinateModuleSectionIso X r U).hom y j) operation)

/-- Actual morphisms from the sheaf tensor of the standard free carriers
are equivalent to global operation coefficients. -/
def coordinateMultilinearOperationEquiv :
    (moduleMultilinearTensor (fun i => coordinateModuleSheaf X (n i)) ⟶ coordinateModuleSheaf X r) ≃
      ((∀ i, Fin (n i)) → Fin r → sectionsRing X (topOpen X)) :=
  (moduleMultilinearTensorHomEquiv _ _).trans
    { toFun := coordinateMultilinearRead X n r
      invFun := coordinateMultilinearFamily X n r
      left_inv := coordinateMultilinearFamily_read X n r
      right_inv := coordinateMultilinearRead_reconstruct X n r }

end

end SHIGURE.RealizationFamilies
