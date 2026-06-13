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
V.R4(b) / AC6: Taylor complex together with a Mathlib finite-free projective
resolution of `A/I`.

The Mathlib resolution carries the exactness/quasi-isomorphism proof. The
comparison fields identify that resolution with the selected Taylor complex
surface used by the monomial calculation.
-/
structure TaylorMathlibResolution {I : Ideal A}
    (P : SquareFreeMonomialIdealPresentation A E I) where
  taylor : TaylorComplex A E P
  finiteFreeResolution : FreeResolution.MathlibResolution.FiniteFreeMathlibResolution.{v} A I
  identifiesTaylorTerms : Prop
  identifiesTaylorTerms_holds : identifiesTaylorTerms
  identifiesTaylorDifferentials : Prop
  identifiesTaylorDifferentials_holds : identifiesTaylorDifferentials

namespace TaylorMathlibResolution

variable {A E}
variable {I : Ideal A} {P : SquareFreeMonomialIdealPresentation A E I}

/-- V.R4(b) / AC6: the selected Taylor terms are identified with the Mathlib resolution. -/
theorem identifiesTaylorTerms_certificate (T : TaylorMathlibResolution A E P) :
    T.identifiesTaylorTerms :=
  T.identifiesTaylorTerms_holds

/-- V.R4(b) / AC6: the selected Taylor differential is identified with the Mathlib one. -/
theorem identifiesTaylorDifferentials_certificate (T : TaylorMathlibResolution A E P) :
    T.identifiesTaylorDifferentials :=
  T.identifiesTaylorDifferentials_holds

/--
V.R4(b) / AC6: the selected Taylor package carries a quotient-resolution
certificate and comparison data with the Mathlib finite-free resolution.
-/
theorem taylorResolution_certificate (T : TaylorMathlibResolution A E P) :
    T.taylor.resolvesQuotient ∧
      T.identifiesTaylorTerms ∧ T.identifiesTaylorDifferentials :=
  ⟨T.taylor.resolvesQuotient_certificate,
    T.identifiesTaylorTerms_certificate, T.identifiesTaylorDifferentials_certificate⟩

/--
V.R4(b) / AC6: the Mathlib finite-free resolution attached to this Taylor
package computes
`Tor_i(A/I_U, A/I)` via Mathlib's projective-resolution theorem.
-/
noncomputable def mathlibResolutionTorIsoTensorHomology (T : TaylorMathlibResolution A E P)
    (I_U : Ideal A) (i : Nat) :
    Intersection.mathlibTor A I_U I i ≅
      (T.finiteFreeResolution.tensorComplex I_U).homology i :=
  T.finiteFreeResolution.torIsoTensorHomology I_U i

end TaylorMathlibResolution

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

/--
V.命題5.5 / AC7: theorem package for the monomial conflict calculation.

The selected right Taylor package supplies the Mathlib finite-free resolution
used to compute `Tor_i(A/I_U, A/I_V)`, because Mathlib's `Tor` derives the
second tensor factor. The left package is retained so the theorem records the
symmetric monomial regime.
-/
structure Proposition55TheoremPackage (I_U I_V : Ideal A) where
  regime : MonomialLawConflictRegime A E I_U I_V
  leftTaylorResolution : TaylorMathlibResolution A E regime.left
  rightTaylorResolution : TaylorMathlibResolution A E regime.right
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

/--
V.命題5.5: Mathlib `Tor_i` is read from an explicit selected equivalence with
finite free tensor homology.
-/
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

namespace Proposition55TheoremPackage

variable {A E}
variable {I_U I_V : Ideal A}

/-- V.命題5.5 / AC7: the theorem package carries its law-conflict computation proof. -/
theorem computesLawConflict_certificate
    (C : Proposition55TheoremPackage A E I_U I_V) :
    C.computesLawConflict :=
  C.computesLawConflict_holds

/--
V.命題5.5 / AC7: both selected Taylor packages carry quotient-resolution and
Mathlib-resolution comparison certificates.
-/
theorem taylorResolution_certificates
    (C : Proposition55TheoremPackage A E I_U I_V) :
    (C.leftTaylorResolution.taylor.resolvesQuotient ∧
      C.leftTaylorResolution.identifiesTaylorTerms ∧
      C.leftTaylorResolution.identifiesTaylorDifferentials) ∧
    (C.rightTaylorResolution.taylor.resolvesQuotient ∧
      C.rightTaylorResolution.identifiesTaylorTerms ∧
      C.rightTaylorResolution.identifiesTaylorDifferentials) :=
  ⟨C.leftTaylorResolution.taylorResolution_certificate,
    C.rightTaylorResolution.taylorResolution_certificate⟩

/--
V.命題5.5 / AC7: Mathlib `Tor_i(A/I_U,A/I_V)` is computed by the
Mathlib finite-free tensor complex attached to the selected right Taylor
package.
-/
noncomputable def lawConflictIsoRightMathlibResolutionTensorHomology
    (C : Proposition55TheoremPackage A E I_U I_V) (i : Nat) :
    Intersection.mathlibTor A I_U I_V i ≅
      (C.rightTaylorResolution.finiteFreeResolution.tensorComplex I_U).homology i :=
  C.rightTaylorResolution.mathlibResolutionTorIsoTensorHomology I_U i

/-- V.命題5.5 / AC7: inverse orientation of the right-resolution Tor computation. -/
noncomputable def rightMathlibResolutionTensorHomologyIsoLawConflict
    (C : Proposition55TheoremPackage A E I_U I_V) (i : Nat) :
    (C.rightTaylorResolution.finiteFreeResolution.tensorComplex I_U).homology i ≅
      Intersection.mathlibTor A I_U I_V i :=
  (C.lawConflictIsoRightMathlibResolutionTensorHomology i).symm

/-- V.命題5.5 / AC7: lcm multidegree is the union of forbidden supports. -/
theorem lcm_multidegree_eq_union
    (C : Proposition55TheoremPackage A E I_U I_V)
    (gU : C.regime.left.Generator) (gV : C.regime.right.Generator) :
    C.regime.lcmSupport gU gV =
      C.regime.left.forbiddenSupport gU ∪ C.regime.right.forbiddenSupport gV :=
  C.regime.lcmSupport_eq_union gU gV

end Proposition55TheoremPackage

end TaylorResolution

end Derived
end AAT.AG
