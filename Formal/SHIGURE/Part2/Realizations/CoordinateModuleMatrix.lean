import Formal.SHIGURE.Part2.Realizations.CoordinateModuleSheaf
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.StdBasis

/-! # Matrices of actual sheaf maps between standard free modules -/

namespace SHIGURE.RealizationFamilies

open AlgebraicGeometry CategoryTheory Opposite

noncomputable section

universe u

variable (X : Scheme.{u}) (m n : ℕ)

private abbrev topOpen : X.Opensᵒᵖ := op (⊤ : X.Opens)
private abbrev sectionRing (U : X.Opensᵒᵖ) := X.sheaf.val.obj U

private def coordinateRestriction (U : X.Opensᵒᵖ) : sectionRing X (topOpen X) →+* sectionRing X U :=
  (X.sheaf.val.map ((homOfLE (le_top (a := U.unop))).op)).hom

private theorem coordinateRestriction_comp {U V : X.Opensᵒᵖ} (g : U ⟶ V)
    (x : sectionRing X (topOpen X)) :
    (X.sheaf.val.map g).hom (coordinateRestriction X U x) = coordinateRestriction X V x := by
  unfold coordinateRestriction
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

variable (P : Matrix (Fin n) (Fin m) (sectionRing X (topOpen X)))

/-- Apply the matrix by restricting its entries to an open and using the
actual coordinates of its modules of sections. -/
def coordinateModuleMatrixApp (U : X.Opensᵒᵖ) :
    (coordinateModuleSheaf X m).val.obj U ⟶ (coordinateModuleSheaf X n).val.obj U :=
  (coordinateModuleSectionIso X m U).hom ≫
    ModuleCat.ofHom (P.map (coordinateRestriction X U)).mulVecLin ≫
    (coordinateModuleSectionIso X n U).inv

/-- Reading a coordinate computes the specified row of the actual restricted matrix. -/
theorem coordinateModuleMatrixApp_apply (U : X.Opensᵒᵖ) (v : (coordinateModuleSheaf X m).val.obj U)
    (i : Fin n) :
    (coordinateModuleSectionIso X n U).hom (coordinateModuleMatrixApp X m n P U v) i =
      ∑ j : Fin m, coordinateRestriction X U (P i j) * (coordinateModuleSectionIso X m U).hom v j := by
  let e := coordinateModuleSectionIso X n U
  let x := (coordinateModuleSectionIso X m U).hom v
  let y := (P.map (coordinateRestriction X U)).mulVecLin x
  have inverse : e.hom (e.inv y) = y := congrArg (fun h => h y) e.inv_hom_id
  change e.hom (e.inv y) i = _
  rw [inverse]
  rfl

/-- The restricted matrices define an actual map of the free module sheaves. -/
def coordinateModuleMatrixHom : coordinateModuleSheaf X m ⟶ coordinateModuleSheaf X n where
  val.app := coordinateModuleMatrixApp X m n P
  val.naturality {U V} g := by
    apply ModuleCat.hom_ext
    ext v
    apply (coordinateModuleSectionIso X n V).toLinearEquiv.injective
    funext i
    change (coordinateModuleSectionIso X n V).hom
        (coordinateModuleMatrixApp X m n P V ((coordinateModuleSheaf X m).val.map g v)) i =
      (coordinateModuleSectionIso X n V).hom
        ((coordinateModuleSheaf X n).val.map g (coordinateModuleMatrixApp X m n P U v)) i
    rw [coordinateModuleSectionIso_restrict, coordinateModuleMatrixApp_apply, coordinateModuleMatrixApp_apply,
      map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [map_mul, coordinateRestriction_comp, coordinateModuleSectionIso_restrict]

/-- A unit coordinate vector viewed as a section of the actual free sheaf. -/
def coordinateModuleUnitColumn (U : X.Opensᵒᵖ) (j : Fin m) : (coordinateModuleSheaf X m).val.obj U :=
  (coordinateModuleSectionIso X m U).inv (Pi.single j 1)

/-- The chosen section has the stated unit coordinates. -/
theorem coordinateModuleUnitColumn_coordinates (U : X.Opensᵒᵖ) (j : Fin m) :
    (coordinateModuleSectionIso X m U).hom (coordinateModuleUnitColumn X m U j) = Pi.single j 1 :=
  (coordinateModuleSectionIso X m U).toLinearEquiv.apply_symm_apply _

private theorem coordinateModuleUnitColumn_restrict {U V : X.Opensᵒᵖ} (g : U ⟶ V) (j : Fin m) :
    (coordinateModuleSheaf X m).val.map g (coordinateModuleUnitColumn X m U j) = coordinateModuleUnitColumn X m V j := by
  classical
  apply (coordinateModuleSectionIso X m V).toLinearEquiv.injective
  funext i
  change (coordinateModuleSectionIso X m V).hom
    ((coordinateModuleSheaf X m).val.map g (coordinateModuleUnitColumn X m U j)) i =
      (coordinateModuleSectionIso X m V).hom (coordinateModuleUnitColumn X m V j) i
  rw [coordinateModuleSectionIso_restrict, coordinateModuleUnitColumn_coordinates, coordinateModuleUnitColumn_coordinates]
  simp [Pi.single_apply]

private theorem coordinateRestriction_top (x : sectionRing X (topOpen X)) :
    coordinateRestriction X (topOpen X) x = x := by
  let g : topOpen X ⟶ topOpen X := (homOfLE (le_top (a := (⊤ : X.Opens)))).op
  have eq : g = 𝟙 _ := Subsingleton.elim _ _
  change (X.sheaf.val.map g).hom x = x
  rw [eq]
  exact congrArg (fun k : X.sheaf.val.obj (topOpen X) ⟶ X.sheaf.val.obj (topOpen X) => k.hom x)
    (X.sheaf.val.map_id (topOpen X))

/-- The actual action on each unit column is its restricted matrix column. -/
theorem coordinateModuleMatrixHom_column (U : X.Opensᵒᵖ) (i : Fin n) (j : Fin m) :
    (coordinateModuleSectionIso X n U).hom
      ((coordinateModuleMatrixHom X m n P).val.app U (coordinateModuleUnitColumn X m U j)) i =
      coordinateRestriction X U (P i j) := by
  classical
  change (coordinateModuleSectionIso X n U).hom
    (coordinateModuleMatrixApp X m n P U (coordinateModuleUnitColumn X m U j)) i = _
  rw [coordinateModuleMatrixApp_apply, coordinateModuleUnitColumn_coordinates]
  simp [Pi.single_apply, mul_ite]

variable (G : coordinateModuleSheaf X m ⟶ coordinateModuleSheaf X n)

/-- Read a sheaf map on the globally chosen unit columns. -/
def coordinateModuleMatrixRead : Matrix (Fin n) (Fin m) (sectionRing X (topOpen X)) :=
  fun i j => (coordinateModuleSectionIso X n (topOpen X)).hom
    (G.val.app (topOpen X) (coordinateModuleUnitColumn X m (topOpen X) j)) i

/-- Reading a sheaf constructed from a matrix gives the same matrix. -/
theorem coordinateModuleMatrixRead_hom :
    coordinateModuleMatrixRead X m n (coordinateModuleMatrixHom X m n P) = P := by
  ext i j
  exact (coordinateModuleMatrixHom_column X m n P (topOpen X) i j).trans (coordinateRestriction_top X _)

/-- Every map of the free sheaves is the unique map of its original global matrix. -/
theorem coordinateModuleMatrixHom_read :
    coordinateModuleMatrixHom X m n (coordinateModuleMatrixRead X m n G) = G := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  let RU := sectionRing X U
  let b := (Pi.basisFun RU (Fin m)).map (coordinateModuleSectionIso X m U).toLinearEquiv.symm
  apply b.ext
  intro j
  apply (coordinateModuleSectionIso X n U).toLinearEquiv.injective
  funext i
  have basisColumn : b j = coordinateModuleUnitColumn X m U j := by
    dsimp only [b]
    rw [Module.Basis.map_apply, Pi.basisFun_apply]
    rfl
  rw [basisColumn]
  let g : topOpen X ⟶ U := (homOfLE (le_top (a := U.unop))).op
  let x := coordinateModuleUnitColumn X m (topOpen X) j
  have geom := (PresheafOfModules.naturality_apply G.val g x).symm.trans
    (congrArg (G.val.app U) (coordinateModuleUnitColumn_restrict X m g j))
  change (coordinateModuleSectionIso X n U).hom
    ((coordinateModuleMatrixHom X m n (coordinateModuleMatrixRead X m n G)).val.app U
      (coordinateModuleUnitColumn X m U j)) i = (coordinateModuleSectionIso X n U).hom
      (G.val.app U (coordinateModuleUnitColumn X m U j)) i
  rw [coordinateModuleMatrixHom_column]
  exact (coordinateModuleSectionIso_restrict X n g (G.val.app (topOpen X) x) i).symm.trans
    (congrArg (fun y => (coordinateModuleSectionIso X n U).hom y i) geom)

/-- The sheaf maps of the actual standard free carriers are all matrices. -/
def coordinateModuleMatrixEquiv :
    (coordinateModuleSheaf X m ⟶ coordinateModuleSheaf X n) ≃
      Matrix (Fin n) (Fin m) (sectionRing X (topOpen X)) where
  toFun := coordinateModuleMatrixRead X m n
  invFun := coordinateModuleMatrixHom X m n
  left_inv := coordinateModuleMatrixHom_read X m n
  right_inv := coordinateModuleMatrixRead_hom X m n

end

end SHIGURE.RealizationFamilies
