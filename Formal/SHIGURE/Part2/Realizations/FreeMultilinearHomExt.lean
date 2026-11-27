import Formal.SHIGURE.Part2.Realizations.CoordinateMultilinearSheaf

/-! # Global basis testing of operations into arbitrary target sheaves -/

namespace SHIGURE.RealizationFamilies

open AlgebraicGeometry CategoryTheory Module Opposite SHIGURE.SchemeDescent

noncomputable section

universe u

private theorem multilinearMap_ext_basis {R I : Type u} [CommRing R] [Fintype I]
    {M : I → Type u} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    {P : Type u} [AddCommGroup P] [Module R P] {n : I → ℕ}
    (b : ∀ i, Basis (Fin (n i)) R (M i)) {f g : MultilinearMap R M P}
    (agree : ∀ a : ∀ i, Fin (n i), f (fun i => b i (a i)) = g (fun i => b i (a i))) : f = g := by
  classical
  apply MultilinearMap.ext
  intro x
  let y (i : I) (j : Fin (n i)) : M i := (b i).repr (x i) j • b i j
  have basis : (fun i => ∑ j, y i j) = x := funext fun i => (b i).sum_repr (x i)
  rw [← basis, f.map_sum, g.map_sum]
  apply Finset.sum_congr rfl
  intro a _
  exact ((f.map_smul_univ (fun i => (b i).repr (x i) (a i)) (fun i => b i (a i))).trans
    (congrArg (_ • ·) (agree a))).trans
    (g.map_smul_univ (fun i => (b i).repr (x i) (a i)) (fun i => b i (a i))).symm

variable (X : Scheme.{u}) {I : Type u} [Fintype I] (n : I → ℕ)
  {P : X.Modules}

private abbrev topOpen : X.Opensᵒᵖ := op (⊤ : X.Opens)
private abbrev carrier (i : I) := coordinateModuleSheaf X (n i)

/-- Equal values on every tuple of globally chosen input basis sections
determine the whole map, even for a target without a global basis. -/
theorem freeMultilinearHom_ext {f g : moduleMultilinearTensor (carrier X n) ⟶ P}
    (equal : ∀ a : ∀ i, Fin (n i),
      (moduleMultilinearTensorHomEquiv (carrier X n) P f).app (topOpen X)
        (fun i => coordinateModuleSectionBasis X (n i) (topOpen X) (a i)) =
      (moduleMultilinearTensorHomEquiv (carrier X n) P g).app (topOpen X)
        (fun i => coordinateModuleSectionBasis X (n i) (topOpen X) (a i))) : f = g := by
  let e := moduleMultilinearTensorHomEquiv (carrier X n) P
  apply e.injective
  apply MultilinearSectionFamily.ext
  funext U
  apply multilinearMap_ext_basis (fun i => coordinateModuleSectionBasis X (n i) U)
  intro a
  let b : topOpen X ⟶ U := (homOfLE (le_top (a := U.unop))).op
  let z (i : I) := coordinateModuleSectionBasis X (n i) (topOpen X) (a i)
  have transport : (fun i => (carrier X n i).val.map b (z i)) =
      (fun i => coordinateModuleSectionBasis X (n i) U (a i)) := by
    funext i
    exact coordinateModuleSectionBasis_restrict X (n i) b (a i)
  have h (h : moduleMultilinearTensor (carrier X n) ⟶ P) :=
    ((e h).naturality b z).trans (congrArg ((e h).app U) transport)
  exact (h f).symm.trans ((congrArg (P.val.map b) (equal a)).trans (h g))

end

end SHIGURE.RealizationFamilies
