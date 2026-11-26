import Mathlib.LinearAlgebra.TensorProduct.Free
import Formal.SHIGURE.Part2.Descent.ExtensionAlgebraTensor
import Formal.SHIGURE.Part2.Schemes.AffineQuasiCoherentFiber

/-! # Pullback of finite free modules on spectra -/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory SHIGURE.CoefficientDescent

noncomputable section

universe u

variable {R S : CommRingCat.{u}} (f : R ⟶ S) (n : ℕ)

/-- The coordinate module of the rank-`n` trivial affine bundle. -/
def finiteFreeModule (R : CommRingCat.{u}) (n : ℕ) : ModuleCat.{u} R :=
  ModuleCat.of R (Fin n → R)

/-- Extending scalars carries the finite free module, with its chosen basis, to
the finite free module of the same rank over the new coefficient ring. -/
def finiteFreeScalarsIso :
    (ModuleCat.extendScalars f.hom).obj (finiteFreeModule R n) ≅ finiteFreeModule S n := by
  letI : Algebra R S := f.hom.toAlgebra
  let comparison := extendScalarsTensorIso (B := S) (finiteFreeModule R n)
  let coordinates := Algebra.TensorProduct.equivPiOfFiniteBasis S (Pi.basisFun R (Fin n))
  exact comparison ≪≫ coordinates.toModuleIso

/-- The pulled-back sheaf of the trivial affine bundle has its original rank. -/
def affineFiniteFreePullbackIso :
    (affinePullbackFunctor f).obj ((affineTildeFunctor R).obj (finiteFreeModule R n)) ≅
      (affineTildeFunctor S).obj (finiteFreeModule S n) :=
  (affineTildePullbackIso f).app (finiteFreeModule R n) ≪≫
    (affineTildeFunctor S).mapIso (finiteFreeScalarsIso f n)

end

end SHIGURE.SchemeDescent
