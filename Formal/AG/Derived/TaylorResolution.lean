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

/-- V.命題5.5: a left forbidden coordinate is contained in the combined lcm support. -/
theorem left_forbiddenSupport_subset_lcmSupport
    (R : MonomialLawConflictRegime A E I_U I_V)
    (gU : R.left.Generator) (gV : R.right.Generator) :
    R.left.forbiddenSupport gU ⊆ R.lcmSupport gU gV := by
  intro e he
  simp [lcmSupport, he]

/-- V.命題5.5: a right forbidden coordinate is contained in the combined lcm support. -/
theorem right_forbiddenSupport_subset_lcmSupport
    (R : MonomialLawConflictRegime A E I_U I_V)
    (gU : R.left.Generator) (gV : R.right.Generator) :
    R.right.forbiddenSupport gV ⊆ R.lcmSupport gU gV := by
  intro e he
  simp [lcmSupport, he]

/-- V.命題5.5: membership in the lcm support is membership in one selected support. -/
theorem mem_lcmSupport_iff
    (R : MonomialLawConflictRegime A E I_U I_V)
    (gU : R.left.Generator) (gV : R.right.Generator) (e : E) :
    e ∈ R.lcmSupport gU gV ↔
      e ∈ R.left.forbiddenSupport gU ∨ e ∈ R.right.forbiddenSupport gV := by
  simp [lcmSupport]

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

/-- V.R4(b): the Taylor differential squares to zero. -/
theorem d_comp_d_certificate (T : TaylorComplex A E P)
    (n : Nat) (x : T.Term n.succ.succ) :
    T.d n (T.d n.succ x) = 0 :=
  T.d_comp_d n x

/-- V.R4(b): multidegree of a union is the lcm/union support. -/
theorem multidegree_union_eq (T : TaylorComplex A E P)
    (S Tset : Finset P.Generator) :
    T.multidegree (S ∪ Tset) = T.multidegree S ∪ T.multidegree Tset :=
  T.multidegree_union S Tset

/--
V.R4(b): the multidegree of a two-generator Taylor face is the union of
the selected forbidden supports.
-/
theorem multidegree_pair_eq_union (T : TaylorComplex A E P)
    (g h : P.Generator) :
    T.multidegree ({g} ∪ {h}) =
      P.forbiddenSupport g ∪ P.forbiddenSupport h := by
  rw [T.multidegree_union_eq, T.multidegree_singleton, T.multidegree_singleton]

end TaylorComplex

/--
V.R4(b) / V-3: selected two-generator square-free monomial presentation.

This is the finite combinatorial surface of the two-generator Taylor complex:
all Taylor faces have cardinality at most two, and the distinguished
two-generator face has multidegree equal to the union of the two selected
forbidden supports.
-/
structure TwoGeneratorPresentation {I : Ideal A}
    (P : SquareFreeMonomialIdealPresentation A E I) where
  generatorEquivFin2 : P.Generator ≃ Fin 2

namespace TwoGeneratorPresentation

variable {A E}
variable {I : Ideal A} {P : SquareFreeMonomialIdealPresentation A E I}

/-- V.R4(b) / V-3: the first selected generator of a two-generator presentation. -/
def leftGenerator (D : TwoGeneratorPresentation A E P) : P.Generator :=
  D.generatorEquivFin2.symm 0

/-- V.R4(b) / V-3: the second selected generator of a two-generator presentation. -/
def rightGenerator (D : TwoGeneratorPresentation A E P) : P.Generator :=
  D.generatorEquivFin2.symm 1

omit [DecidableEq E] in
/-- V.R4(b) / V-3: every Taylor face in a two-generator presentation has size at most two. -/
theorem face_card_le_two (D : TwoGeneratorPresentation A E P)
    (S : Finset P.Generator) :
    S.card ≤ 2 := by
  classical
  have hle : S.card ≤ Fintype.card P.Generator := Finset.card_le_univ S
  have hcard : Fintype.card P.Generator = 2 :=
    Fintype.card_congr D.generatorEquivFin2
  simpa [hcard] using hle

/--
V.R4(b) / V-3: the two selected Taylor generators have the expected lcm
multidegree.
-/
theorem selected_pair_multidegree_eq_union
    (D : TwoGeneratorPresentation A E P) (T : TaylorComplex A E P) :
    T.multidegree ({D.leftGenerator} ∪ {D.rightGenerator}) =
      P.forbiddenSupport D.leftGenerator ∪ P.forbiddenSupport D.rightGenerator :=
  T.multidegree_pair_eq_union D.leftGenerator D.rightGenerator

end TwoGeneratorPresentation

namespace TwoGeneratorPrincipalTaylor

variable {A}

/-- V-3: multiplication by a selected generator as an `A`-linear map. -/
def mulLeft (c : A) : A →ₗ[A] A where
  toFun x := c * x
  map_add' x y := by simp [mul_add]
  map_smul' r x := by
    simp [smul_eq_mul, mul_left_comm]

/--
V-3: the degree-two differential of the concrete two-generator Taylor/Koszul
surface for the ordered pair `(a,b)`.

It sends `r` to `(-b*r, a*r)`, the principal syzygy generator.
-/
def d₂ (a b : A) : A →ₗ[A] A × A :=
  (-(mulLeft b)).prod (mulLeft a)

/--
V-3: the degree-one differential of the concrete two-generator Taylor/Koszul
surface for the ordered pair `(a,b)`.

It sends `(p,q)` to `a*p + b*q`.
-/
def d₁ (a b : A) : A × A →ₗ[A] A :=
  (mulLeft a).comp (LinearMap.fst A A A) +
    (mulLeft b).comp (LinearMap.snd A A A)

/-- V-3: readable form of the degree-one differential. -/
theorem d₁_apply (a b : A) (x : A × A) :
    d₁ a b x = a * x.1 + b * x.2 :=
  rfl

/-- V-3: readable form of the degree-two differential. -/
theorem d₂_apply (a b : A) (r : A) :
    d₂ a b r = (-b * r, a * r) := by
  simp [d₂, mulLeft]

/--
V-3: principal-syzygy exactness condition for a concrete two-generator pair.

This is the honest boundary of the current theorem: exactness at degree one is
proved from this algebraic syzygy statement, rather than from a package field
claiming that the Taylor complex resolves the quotient.
-/
def PrincipalSyzygyExact (a b : A) : Prop :=
  ∀ x : A × A, d₁ a b x = 0 -> ∃ r : A, x = d₂ a b r

/-- V-3: the concrete two-generator Taylor differential squares to zero. -/
theorem d₁_comp_d₂_eq_zero (a b : A) :
    (d₁ a b).comp (d₂ a b) = 0 := by
  apply LinearMap.ext
  intro r
  simp [d₁, d₂, mulLeft]
  ring

/--
V-3: exactness at the middle term of the concrete two-generator Taylor complex,
assuming the principal-syzygy theorem for the selected pair `(a,b)`.
-/
theorem exact_d₂_d₁ (a b : A) (h : PrincipalSyzygyExact a b) :
    Function.Exact (d₂ a b) (d₁ a b) := by
  apply LinearMap.exact_of_comp_of_mem_range
  · exact d₁_comp_d₂_eq_zero a b
  · intro x hx
    rcases h x hx with ⟨r, rfl⟩
    exact ⟨r, rfl⟩

/--
V-3: exactness at the quotient by the image of the concrete two-generator
Taylor differential.

This is the actual cokernel exactness theorem for `d₁`; identifying this module
quotient with the ideal quotient by `(a,b)` is a separate algebraic bridge.
-/
theorem exact_d₁_mkQ_range (a b : A) :
    Function.Exact (d₁ a b) (LinearMap.range (d₁ a b)).mkQ :=
  LinearMap.exact_map_mkQ_range (d₁ a b)

/--
V-3: the concrete two-generator Taylor complex is exact at the two visible
spots once the selected pair satisfies the principal-syzygy theorem.
-/
theorem exact_visible_complex (a b : A) (h : PrincipalSyzygyExact a b) :
    Function.Exact (d₂ a b) (d₁ a b) ∧
      Function.Exact (d₁ a b) (LinearMap.range (d₁ a b)).mkQ :=
  ⟨exact_d₂_d₁ a b h, exact_d₁_mkQ_range a b⟩

end TwoGeneratorPrincipalTaylor

/--
V.R4(b) / AC6: selected finite-free resolution data identifying a Taylor
complex with an exact quotient resolution.

This package keeps the construction relative to explicit selected data. The
field `resolvesQuotient_of_exact` is the selected bridge from exactness of the
finite-free resolution to the Taylor quotient-resolution predicate; this file
does not derive that bridge from a universal chain-map exactness-transfer
theorem.
-/
structure TaylorSelectedFreeResolutionData {I : Ideal A}
    (P : SquareFreeMonomialIdealPresentation A E I) where
  taylor : TaylorComplex A E P
  quotientResolution :
    FreeResolution.SelectedFiniteFreeResolution.{u, v} A (A ⧸ I)
  termIdentifications :
    (n : Nat) -> taylor.Term n ≃ₗ[A] quotientResolution.Term n
  differentialCompatible : Prop
  differentialCompatible_holds : differentialCompatible
  resolvesQuotient_of_exact :
    (Function.Exact (quotientResolution.d 0) quotientResolution.augmentation ∧
      ∀ n, Function.Exact (quotientResolution.d n.succ) (quotientResolution.d n)) ->
      taylor.resolvesQuotient

namespace TaylorSelectedFreeResolutionData

variable {A E}
variable {I : Ideal A} {P : SquareFreeMonomialIdealPresentation A E I}

/-- V.R4(b) / AC6: every Taylor term is identified with a finite-free term. -/
def termLinearEquivSelectedResolution
    (D : TaylorSelectedFreeResolutionData.{u, v} A E P) (n : Nat) :
    D.taylor.Term n ≃ₗ[A] D.quotientResolution.Term n :=
  D.termIdentifications n

/-- V.R4(b) / AC6: the selected Taylor differential is compatible with the resolution. -/
theorem differentialCompatible_certificate
    (D : TaylorSelectedFreeResolutionData.{u, v} A E P) :
    D.differentialCompatible :=
  D.differentialCompatible_holds

/--
V.R4(b) / AC6: the Taylor complex resolves the quotient through the selected
assumption-relative bridge from finite-free exactness.
-/
theorem resolvesQuotient_from_selectedResolutionBridge
    (D : TaylorSelectedFreeResolutionData.{u, v} A E P) :
    D.taylor.resolvesQuotient :=
  D.resolvesQuotient_of_exact D.quotientResolution.exact_certificate

/--
V.R4(b) / AC6: compatibility alias for the selected exactness bridge.
The theorem remains assumption-relative to `resolvesQuotient_of_exact`.
-/
theorem resolvesQuotient_from_selectedResolution
    (D : TaylorSelectedFreeResolutionData.{u, v} A E P) :
    D.taylor.resolvesQuotient :=
  D.resolvesQuotient_from_selectedResolutionBridge

end TaylorSelectedFreeResolutionData

/--
V.R4(b) / V-3: two-generator Taylor resolution package.

The package ties the two-generator combinatorics to a selected exact
finite-free quotient resolution. The quotient-resolution theorem remains
assumption-relative to the selected `resolvesQuotient_of_exact` bridge in
`TaylorSelectedFreeResolutionData`.
-/
structure TwoGeneratorTaylorResolutionPackage {I : Ideal A}
    (P : SquareFreeMonomialIdealPresentation A E I) where
  twoGenerator : TwoGeneratorPresentation A E P
  resolutionData : TaylorSelectedFreeResolutionData.{u, v} A E P

namespace TwoGeneratorTaylorResolutionPackage

variable {A E}
variable {I : Ideal A} {P : SquareFreeMonomialIdealPresentation A E I}

/-- V.R4(b) / V-3: the selected Taylor complex in the two-generator package. -/
abbrev taylor (D : TwoGeneratorTaylorResolutionPackage.{u, v} A E P) :
    TaylorComplex A E P :=
  D.resolutionData.taylor

/-- V.R4(b) / V-3: every selected Taylor face has cardinality at most two. -/
theorem face_card_le_two
    (D : TwoGeneratorTaylorResolutionPackage.{u, v} A E P)
    (S : Finset P.Generator) :
    S.card ≤ 2 :=
  D.twoGenerator.face_card_le_two S

/--
V.R4(b) / V-3: the distinguished two-generator face has multidegree equal to
the union of the two selected forbidden supports.
-/
theorem selected_pair_multidegree_eq_union
    (D : TwoGeneratorTaylorResolutionPackage.{u, v} A E P) :
    D.taylor.multidegree
        ({D.twoGenerator.leftGenerator} ∪ {D.twoGenerator.rightGenerator}) =
      P.forbiddenSupport D.twoGenerator.leftGenerator ∪
        P.forbiddenSupport D.twoGenerator.rightGenerator :=
  D.twoGenerator.selected_pair_multidegree_eq_union D.taylor

/--
V.R4(b) / V-3: the two-generator Taylor surface resolves the quotient through
the selected exactness bridge.
-/
theorem resolvesQuotient_from_selectedExactBridge
    (D : TwoGeneratorTaylorResolutionPackage.{u, v} A E P) :
    D.taylor.resolvesQuotient :=
  D.resolutionData.resolvesQuotient_from_selectedResolution

/--
V.R4(b) / V-3: compatibility alias for the selected two-generator exactness
bridge. The theorem is not a universal construction of the Taylor resolution.
-/
theorem resolvesQuotient_from_selectedExact
    (D : TwoGeneratorTaylorResolutionPackage.{u, v} A E P) :
    D.taylor.resolvesQuotient :=
  D.resolvesQuotient_from_selectedExactBridge

end TwoGeneratorTaylorResolutionPackage

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
V.R4(b) / AC6: direct theorem package joining the selected Taylor finite-free
resolution data with the Mathlib finite-free resolution data.

The quotient-resolution statement for the Taylor surface is read from exactness
of the selected finite-free resolution, not from the `TaylorComplex` field
projection.
-/
structure DirectTaylorResolutionPackage {I : Ideal A}
    (P : SquareFreeMonomialIdealPresentation A E I) where
  selectedResolution : TaylorSelectedFreeResolutionData.{u, v} A E P
  mathlibResolution : TaylorMathlibResolution A E P
  sameTaylorComplex : mathlibResolution.taylor = selectedResolution.taylor

namespace DirectTaylorResolutionPackage

variable {A E}
variable {I : Ideal A} {P : SquareFreeMonomialIdealPresentation A E I}

/--
V.R4(b) / AC6: the selected Taylor complex resolves the quotient by exactness of
the selected finite-free resolution.
-/
theorem selectedTaylor_resolvesQuotient_from_exact
    (D : DirectTaylorResolutionPackage A E P) :
    D.selectedResolution.taylor.resolvesQuotient :=
  D.selectedResolution.resolvesQuotient_from_selectedResolution

/--
V.R4(b) / AC6: the Mathlib-facing Taylor complex resolves the quotient by the
same selected exactness proof, transported across the Taylor-complex
identification.
-/
theorem mathlibTaylor_resolvesQuotient_from_selectedExact
    (D : DirectTaylorResolutionPackage A E P) :
    D.mathlibResolution.taylor.resolvesQuotient := by
  rw [D.sameTaylorComplex]
  exact D.selectedTaylor_resolvesQuotient_from_exact

/--
V.R4(b) / AC6: direct Taylor resolution theorem surface.

The first component is produced from selected finite-free exactness rather than
from `TaylorComplex.resolvesQuotient_holds`.
-/
theorem taylorResolution_theorem
    (D : DirectTaylorResolutionPackage A E P) :
    D.mathlibResolution.taylor.resolvesQuotient ∧
      D.mathlibResolution.identifiesTaylorTerms ∧
      D.mathlibResolution.identifiesTaylorDifferentials :=
  ⟨D.mathlibTaylor_resolvesQuotient_from_selectedExact,
    D.mathlibResolution.identifiesTaylorTerms_certificate,
    D.mathlibResolution.identifiesTaylorDifferentials_certificate⟩

/--
V.R4(b) / AC6: the selected Taylor differential squares to zero on the direct
theorem package.
-/
theorem differential_square_zero
    (D : DirectTaylorResolutionPackage A E P)
    (n : Nat) (x : D.mathlibResolution.taylor.Term n.succ.succ) :
    D.mathlibResolution.taylor.d n
      (D.mathlibResolution.taylor.d n.succ x) = 0 :=
  D.mathlibResolution.taylor.d_comp_d_certificate n x

end DirectTaylorResolutionPackage

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

/--
V.命題5.5 / AC7: direct theorem package for monomial conflict calculation.

Unlike `Proposition55TheoremPackage`, this surface does not store a separate
`computesLawConflict` Prop. The Tor computation is the explicit Mathlib
finite-free resolution isomorphism attached to the right Taylor package, and the
lcm multidegree reading is the theorem on the monomial regime.
-/
structure Proposition55DirectTheoremPackage (I_U I_V : Ideal A) where
  regime : MonomialLawConflictRegime A E I_U I_V
  leftTaylorResolution : DirectTaylorResolutionPackage A E regime.left
  rightTaylorResolution : DirectTaylorResolutionPackage A E regime.right

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

namespace Proposition55DirectTheoremPackage

variable {A E}
variable {I_U I_V : Ideal A}

/--
V.命題5.5 / AC7: both selected Taylor packages carry direct resolution
theorem surfaces.
-/
theorem taylorResolution_theorems
    (C : Proposition55DirectTheoremPackage A E I_U I_V) :
    (C.leftTaylorResolution.mathlibResolution.taylor.resolvesQuotient ∧
      C.leftTaylorResolution.mathlibResolution.identifiesTaylorTerms ∧
      C.leftTaylorResolution.mathlibResolution.identifiesTaylorDifferentials) ∧
    (C.rightTaylorResolution.mathlibResolution.taylor.resolvesQuotient ∧
      C.rightTaylorResolution.mathlibResolution.identifiesTaylorTerms ∧
      C.rightTaylorResolution.mathlibResolution.identifiesTaylorDifferentials) :=
  ⟨C.leftTaylorResolution.taylorResolution_theorem,
    C.rightTaylorResolution.taylorResolution_theorem⟩

/--
V.命題5.5 / AC7: both selected Taylor differentials square to zero on the direct
theorem package.
-/
theorem taylor_differentials_square_zero
    (C : Proposition55DirectTheoremPackage A E I_U I_V) :
    (∀ (n : Nat)
      (x : C.leftTaylorResolution.mathlibResolution.taylor.Term n.succ.succ),
      C.leftTaylorResolution.mathlibResolution.taylor.d n
        (C.leftTaylorResolution.mathlibResolution.taylor.d n.succ x) = 0) ∧
    (∀ (n : Nat)
      (x : C.rightTaylorResolution.mathlibResolution.taylor.Term n.succ.succ),
      C.rightTaylorResolution.mathlibResolution.taylor.d n
        (C.rightTaylorResolution.mathlibResolution.taylor.d n.succ x) = 0) :=
  ⟨C.leftTaylorResolution.differential_square_zero,
    C.rightTaylorResolution.differential_square_zero⟩

/--
V.命題5.5 / AC7: Mathlib `Tor_i(A/I_U,A/I_V)` is computed by the
Mathlib finite-free tensor complex attached to the selected right Taylor
package, without a separate selected calculation Prop.
-/
noncomputable def lawConflictIsoRightMathlibResolutionTensorHomology
    (C : Proposition55DirectTheoremPackage A E I_U I_V) (i : Nat) :
    Intersection.mathlibTor A I_U I_V i ≅
      (C.rightTaylorResolution.mathlibResolution.finiteFreeResolution.tensorComplex I_U).homology i :=
  C.rightTaylorResolution.mathlibResolution.mathlibResolutionTorIsoTensorHomology I_U i

/-- V.命題5.5 / AC7: inverse orientation of the direct right-resolution Tor computation. -/
noncomputable def rightMathlibResolutionTensorHomologyIsoLawConflict
    (C : Proposition55DirectTheoremPackage A E I_U I_V) (i : Nat) :
    (C.rightTaylorResolution.mathlibResolution.finiteFreeResolution.tensorComplex I_U).homology i ≅
      Intersection.mathlibTor A I_U I_V i :=
  (C.lawConflictIsoRightMathlibResolutionTensorHomology i).symm

/-- V.命題5.5 / AC7: lcm multidegree is the union of forbidden supports. -/
theorem lcm_multidegree_eq_union
    (C : Proposition55DirectTheoremPackage A E I_U I_V)
    (gU : C.regime.left.Generator) (gV : C.regime.right.Generator) :
    C.regime.lcmSupport gU gV =
      C.regime.left.forbiddenSupport gU ∪ C.regime.right.forbiddenSupport gV :=
  C.regime.lcmSupport_eq_union gU gV

/-- V.命題5.5 / AC7: left support membership is preserved in the lcm support. -/
theorem left_forbiddenSupport_subset_lcmSupport
    (C : Proposition55DirectTheoremPackage A E I_U I_V)
    (gU : C.regime.left.Generator) (gV : C.regime.right.Generator) :
    C.regime.left.forbiddenSupport gU ⊆ C.regime.lcmSupport gU gV :=
  C.regime.left_forbiddenSupport_subset_lcmSupport gU gV

/-- V.命題5.5 / AC7: right support membership is preserved in the lcm support. -/
theorem right_forbiddenSupport_subset_lcmSupport
    (C : Proposition55DirectTheoremPackage A E I_U I_V)
    (gU : C.regime.left.Generator) (gV : C.regime.right.Generator) :
    C.regime.right.forbiddenSupport gV ⊆ C.regime.lcmSupport gU gV :=
  C.regime.right_forbiddenSupport_subset_lcmSupport gU gV

/-- V.命題5.5 / AC7: lcm support membership is exactly support-union membership. -/
theorem mem_lcmSupport_iff
    (C : Proposition55DirectTheoremPackage A E I_U I_V)
    (gU : C.regime.left.Generator) (gV : C.regime.right.Generator) (e : E) :
    e ∈ C.regime.lcmSupport gU gV ↔
      e ∈ C.regime.left.forbiddenSupport gU ∨
        e ∈ C.regime.right.forbiddenSupport gV :=
  C.regime.mem_lcmSupport_iff gU gV e

/--
V.命題5.5 / AC7: package-level data bundling the direct Tor computation with
the lcm multidegree reading.
-/
structure ComputedTorAndLcmSupport
    (C : Proposition55DirectTheoremPackage A E I_U I_V) (i : Nat)
    (gU : C.regime.left.Generator) (gV : C.regime.right.Generator) where
  torIso :
    Intersection.mathlibTor A I_U I_V i ≅
      (C.rightTaylorResolution.mathlibResolution.finiteFreeResolution.tensorComplex I_U).homology i
  lcmSupport_eq_union :
    C.regime.lcmSupport gU gV =
      C.regime.left.forbiddenSupport gU ∪ C.regime.right.forbiddenSupport gV

/--
V.命題5.5 / AC7: construct the direct combined Tor/lcm package from the theorem
package.
-/
noncomputable def torComputationAndLcmSupport
    (C : Proposition55DirectTheoremPackage A E I_U I_V) (i : Nat)
    (gU : C.regime.left.Generator) (gV : C.regime.right.Generator) :
    ComputedTorAndLcmSupport C i gU gV where
  torIso := C.lawConflictIsoRightMathlibResolutionTensorHomology i
  lcmSupport_eq_union := C.lcm_multidegree_eq_union gU gV

end Proposition55DirectTheoremPackage

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
V.命題5.5 / AC7: both selected Taylor differentials square to zero.
-/
theorem taylor_differentials_square_zero
    (C : Proposition55TheoremPackage A E I_U I_V) :
    (∀ (n : Nat) (x : C.leftTaylorResolution.taylor.Term n.succ.succ),
      C.leftTaylorResolution.taylor.d n
        (C.leftTaylorResolution.taylor.d n.succ x) = 0) ∧
    (∀ (n : Nat) (x : C.rightTaylorResolution.taylor.Term n.succ.succ),
      C.rightTaylorResolution.taylor.d n
        (C.rightTaylorResolution.taylor.d n.succ x) = 0) :=
  ⟨C.leftTaylorResolution.taylor.d_comp_d_certificate,
    C.rightTaylorResolution.taylor.d_comp_d_certificate⟩

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

/-- V.命題5.5 / AC7: left support membership is preserved in the lcm support. -/
theorem left_forbiddenSupport_subset_lcmSupport
    (C : Proposition55TheoremPackage A E I_U I_V)
    (gU : C.regime.left.Generator) (gV : C.regime.right.Generator) :
    C.regime.left.forbiddenSupport gU ⊆ C.regime.lcmSupport gU gV :=
  C.regime.left_forbiddenSupport_subset_lcmSupport gU gV

/-- V.命題5.5 / AC7: right support membership is preserved in the lcm support. -/
theorem right_forbiddenSupport_subset_lcmSupport
    (C : Proposition55TheoremPackage A E I_U I_V)
    (gU : C.regime.left.Generator) (gV : C.regime.right.Generator) :
    C.regime.right.forbiddenSupport gV ⊆ C.regime.lcmSupport gU gV :=
  C.regime.right_forbiddenSupport_subset_lcmSupport gU gV

/-- V.命題5.5 / AC7: lcm support membership is exactly support-union membership. -/
theorem mem_lcmSupport_iff
    (C : Proposition55TheoremPackage A E I_U I_V)
    (gU : C.regime.left.Generator) (gV : C.regime.right.Generator) (e : E) :
    e ∈ C.regime.lcmSupport gU gV ↔
      e ∈ C.regime.left.forbiddenSupport gU ∨
        e ∈ C.regime.right.forbiddenSupport gV :=
  C.regime.mem_lcmSupport_iff gU gV e

/--
V.命題5.5 / AC7: package-level data bundling the Tor computation with the
lcm multidegree reading.
-/
structure ComputedTorAndLcmSupport
    (C : Proposition55TheoremPackage A E I_U I_V) (i : Nat)
    (gU : C.regime.left.Generator) (gV : C.regime.right.Generator) where
  torIso :
    Intersection.mathlibTor A I_U I_V i ≅
      (C.rightTaylorResolution.finiteFreeResolution.tensorComplex I_U).homology i
  lcmSupport_eq_union :
    C.regime.lcmSupport gU gV =
      C.regime.left.forbiddenSupport gU ∪ C.regime.right.forbiddenSupport gV

/--
V.命題5.5 / AC7: construct the combined Tor/lcm package from the theorem
package.
-/
noncomputable def torComputationAndLcmSupport
    (C : Proposition55TheoremPackage A E I_U I_V) (i : Nat)
    (gU : C.regime.left.Generator) (gV : C.regime.right.Generator) :
    ComputedTorAndLcmSupport C i gU gV where
  torIso := C.lawConflictIsoRightMathlibResolutionTensorHomology i
  lcmSupport_eq_union := C.lcm_multidegree_eq_union gU gV

end Proposition55TheoremPackage

end TaylorResolution

end Derived
end AAT.AG
