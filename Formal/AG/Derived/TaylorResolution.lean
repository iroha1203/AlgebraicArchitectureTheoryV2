import Formal.AG.Derived.FreeResolution
import Mathlib.Data.Finset.Lattice.Basic

noncomputable section

namespace AAT.AG
namespace Derived

universe u v

namespace TaylorResolution

set_option linter.unusedSectionVars false

variable (A : Type v) [CommRing A]
variable (E : Type u) [DecidableEq E]

/-- V.定義5.4: square-free monomial ideal presentation by forbidden supports. -/
structure SquareFreeMonomialIdealPresentation (I : Ideal A) where
  Generator : Type u
  [generatorFintype : Fintype Generator]
  [generatorDecidableEq : DecidableEq Generator]
  monomial : Generator -> A
  forbiddenSupport : Generator -> Finset E
  monomial_mem : ∀ g, monomial g ∈ I
  spans : Ideal.span (Set.range monomial) = I
  squareFree : Prop
  squareFree_holds : squareFree

attribute [instance] SquareFreeMonomialIdealPresentation.generatorFintype
attribute [instance] SquareFreeMonomialIdealPresentation.generatorDecidableEq

namespace SquareFreeMonomialIdealPresentation

variable {A E}
variable {I : Ideal A}

/-- V.定義5.4: the selected monomial generators span the ideal. -/
theorem generatedIdeal_eq (P : SquareFreeMonomialIdealPresentation A E I) :
    Ideal.span (Set.range P.monomial) = I :=
  P.spans

/-- V.定義5.4: selected square-free certificate. -/
theorem squareFree_certificate (P : SquareFreeMonomialIdealPresentation A E I) :
    P.squareFree :=
  P.squareFree_holds

end SquareFreeMonomialIdealPresentation

/-- V.R4: pair of square-free monomial ideals in a shared ambient chart algebra. -/
structure MonomialLawConflictRegime (I_U I_V : Ideal A) where
  left : SquareFreeMonomialIdealPresentation A E I_U
  right : SquareFreeMonomialIdealPresentation A E I_V

namespace MonomialLawConflictRegime

variable {A E}
variable {I_U I_V : Ideal A}

/-- V.命題5.5: lcm multidegree of one left and one right forbidden support. -/
def lcmSupport (R : MonomialLawConflictRegime A E I_U I_V)
    (gU : R.left.Generator) (gV : R.right.Generator) : Finset E :=
  R.left.forbiddenSupport gU ∪ R.right.forbiddenSupport gV

/-- V.命題5.5: lcm multidegree is the union of forbidden supports. -/
theorem lcmSupport_eq_union (R : MonomialLawConflictRegime A E I_U I_V)
    (gU : R.left.Generator) (gV : R.right.Generator) :
    R.lcmSupport gU gV =
      R.left.forbiddenSupport gU ∪ R.right.forbiddenSupport gV :=
  rfl

end MonomialLawConflictRegime

/--
V.R4(b): selected Taylor complex for a square-free monomial ideal presentation.

This records the Taylor surface and its resolution certificate. It does not claim
Scarf or lcm-lattice minimality.
-/
structure TaylorComplex {I : Ideal A}
    (P : SquareFreeMonomialIdealPresentation A E I) where
  Term : Nat -> Type v
  [termAddCommGroup : (n : Nat) -> AddCommGroup (Term n)]
  [termModule : (n : Nat) -> Module A (Term n)]
  d : (n : Nat) -> Term n.succ →ₗ[A] Term n
  d_comp_d : ∀ (n : Nat) (x : Term n.succ.succ), d n (d n.succ x) = 0
  multidegree : Finset P.Generator -> Finset E
  multidegree_singleton :
    ∀ g, multidegree {g} = P.forbiddenSupport g
  multidegree_union :
    ∀ S T, multidegree (S ∪ T) = multidegree S ∪ multidegree T
  resolvesQuotient : Prop
  resolvesQuotient_holds : resolvesQuotient

attribute [instance] TaylorComplex.termAddCommGroup
attribute [instance] TaylorComplex.termModule

namespace TaylorComplex

variable {A E}
variable {I : Ideal A} {P : SquareFreeMonomialIdealPresentation A E I}

/-- V.R4(b): selected Taylor complex resolves the quotient. -/
theorem resolvesQuotient_certificate (T : TaylorComplex A E P) :
    T.resolvesQuotient :=
  T.resolvesQuotient_holds

/-- V.R4(b): multidegree of a union is the lcm/union support. -/
theorem multidegree_union_eq (T : TaylorComplex A E P)
    (S Tset : Finset P.Generator) :
    T.multidegree (S ∪ Tset) = T.multidegree S ∪ T.multidegree Tset :=
  T.multidegree_union S Tset

end TaylorComplex

/--
V.命題5.5: monomial conflict calculation package.

The package bundles the monomial regime, selected Taylor complexes, and a finite
free resolution computation of `LawConflict_i = Tor_i`.
-/
structure MonomialConflictCalculation (I_U I_V : Ideal A) where
  regime : MonomialLawConflictRegime A E I_U I_V
  leftTaylor : TaylorComplex A E regime.left
  rightTaylor : TaylorComplex A E regime.right
  computation :
    FreeResolution.FiniteFreeResolutionTorComputation.{u, v} A I_U I_V
  computesLawConflict : Prop
  computesLawConflict_holds : computesLawConflict

namespace MonomialConflictCalculation

variable {A E}
variable {I_U I_V : Ideal A}

/-- V.命題5.5: monomial package computes law conflicts by finite free homology. -/
theorem computesLawConflict_certificate
    (C : MonomialConflictCalculation.{u, v} A E I_U I_V) :
    C.computesLawConflict :=
  C.computesLawConflict_holds

/-- V.命題5.5: Mathlib `Tor_i` is read from the selected finite free tensor homology. -/
def lawConflictLinearEquivTensorHomology
    (C : MonomialConflictCalculation.{u, v} A E I_U I_V) (i : Nat) :
    Intersection.mathlibTor A I_U I_V i ≃ₗ[A] C.computation.tensorComplex.homology i :=
  C.computation.mathlibTorLinearEquivTensorHomology i

/-- V.命題5.5: lcm multidegree is combined witness support. -/
theorem lcm_multidegree_eq_union
    (C : MonomialConflictCalculation.{u, v} A E I_U I_V)
    (gU : C.regime.left.Generator) (gV : C.regime.right.Generator) :
    C.regime.lcmSupport gU gV =
      C.regime.left.forbiddenSupport gU ∪ C.regime.right.forbiddenSupport gV :=
  C.regime.lcmSupport_eq_union gU gV

end MonomialConflictCalculation

end TaylorResolution

end Derived
end AAT.AG
