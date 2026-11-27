import Formal.SHIGURE.Part2.Realizations.CoordinateBasisPullback
import Formal.SHIGURE.Part2.Realizations.FreeMultilinearHomExt
import Formal.SHIGURE.Part2.Schemes.ModuleMultilinearAdjunctRead

/-! # Actual coefficient change of operations on free sheaf carriers -/

namespace SHIGURE.RealizationFamilies

open AlgebraicGeometry CategoryTheory Opposite SHIGURE.SchemeDescent

noncomputable section

universe u

private abbrev topOpen (T : Scheme.{u}) : T.Opensᵒᵖ := op (⊤ : T.Opens)
private abbrev F (T : Scheme.{u}) := coordinateModuleSheaf T

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {I : Type u} [Fintype I] (n : I → ℕ) (r : ℕ)

private theorem coordinateTopValue (T : Scheme.{u})
    (c : (∀ i, Fin (n i)) → Fin r → Γ(T, ⊤)) (a : ∀ i, Fin (n i)) (j : Fin r) :
    (coordinateModuleSectionIso T r (topOpen T)).hom
      ((moduleMultilinearTensorHomEquiv (fun i => F T (n i)) (F T r)
        (coordinateMultilinearOperation T n r c)).app (topOpen T)
          (fun i => coordinateModuleSectionBasis T (n i) (topOpen T) (a i))) j = c a j :=
  congrFun (congrFun ((coordinateMultilinearOperationEquiv T n r).apply_symm_apply c) a) j

/-- The actual pullback of a primitive operation on standard free sheaves
agrees with the operation given by applying the structure-ring map to each coefficient. -/
theorem coordinateMultilinearOperation_pullback
    (c : (∀ i, Fin (n i)) → Fin r → Γ(Y, ⊤)) :
    (Scheme.Modules.pullback f).map (coordinateMultilinearOperation Y n r c) ≫
      (coordinateModulePullbackIso f r).hom =
    moduleMultilinearPullbackComparison f (fun i => F Y (n i)) ≫
      moduleMultilinearTensorMap (fun i => (coordinateModulePullbackIso f (n i)).hom) ≫
        coordinateMultilinearOperation X n r (fun a j => f.appTop.hom (c a j)) := by
  let adj := Scheme.Modules.pullbackPushforwardAdjunction f
  let N (i : I) := F Y (n i)
  let M (i : I) := F X (n i)
  let Yop := coordinateMultilinearOperation Y n r c
  let Xop := coordinateMultilinearOperation X n r (fun a j => f.appTop.hom (c a j))
  let v (i : I) := (coordinateModulePullbackIso f (n i)).hom
  let p := (coordinateModulePullbackIso f r).hom
  apply (adj.homEquiv _ _).injective
  apply freeMultilinearHom_ext Y n
  intro a
  let x (i : I) := coordinateModuleSectionBasis Y (n i) (topOpen Y) (a i)
  let y (i : I) := coordinateModuleSectionBasis X (n i) (topOpen X) (a i)
  have old := moduleMultilinearOriginalBaseChange_read f N (F Y r) (F X r) Yop p (topOpen Y) x
  have new := moduleMultilinearPullbackComparison_read f N M (F X r) v Xop (topOpen Y) x
  have input (i : I) : (adj.homEquiv _ _ (v i)).val.app (topOpen Y) (x i) = y i := by
    classical
    apply (coordinateModuleSectionIso X (n i) (topOpen X)).toLinearEquiv.injective
    funext j
    change (coordinateModuleSectionIso X (n i) (topOpen X)).hom
      ((adj.homEquiv _ _ (v i)).val.app (topOpen Y) (x i)) j =
      (coordinateModuleSectionIso X (n i) (topOpen X)).hom (y i) j
    have g := coordinateAdjunct_top_apply f (n i) (x i) j
    change _ = f.appTop.hom ((coordinateModuleSectionIso Y (n i) (topOpen Y)).hom (x i) j) at g
    rw [g]
    dsimp only [x, y]
    rw [coordinateModuleSectionBasis_in_coordinates, coordinateModuleSectionBasis_in_coordinates]
    simp [Pi.basisFun_apply, Pi.single_apply]
  refine old.trans (Eq.trans ?_ new.symm)
  apply (coordinateModuleSectionIso X r (topOpen X)).toLinearEquiv.injective
  funext j
  let z := (moduleMultilinearTensorHomEquiv N (F Y r) Yop).app (topOpen Y) x
  have first := coordinateAdjunct_top_apply f r z j
  have oldValue := coordinateTopValue n r Y c a j
  have newValue := coordinateTopValue n r X (fun a j => f.appTop.hom (c a j)) a j
  exact first.trans ((congrArg f.appTop.hom oldValue).trans
    (newValue.symm.trans (congrArg (fun t => (coordinateModuleSectionIso X r (topOpen X)).hom
      ((moduleMultilinearTensorHomEquiv M (F X r) Xop).app (topOpen X) t) j) (funext input).symm)))

end

end SHIGURE.RealizationFamilies
