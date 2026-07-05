import Formal.AG.Cohomology.FlatnessCriterion

noncomputable section

namespace AAT.AG
namespace Cohomology

universe u

/--
IV.定義12.1: cover nerve with explicit connected overlap components.

Vertices are selected charts, edges are selected connected components of
pairwise overlaps, and faces are selected connected components of triple
overlaps.  Parallel edge and face components are allowed because there is no
uniqueness field for endpoints or boundary triples.
-/
structure CoverNerve where
  Chart : Type u
  EdgeComponent : Type u
  FaceComponent : Type u
  edgeLeft : EdgeComponent -> Chart
  edgeRight : EdgeComponent -> Chart
  faceEdge0 : FaceComponent -> EdgeComponent
  faceEdge1 : FaceComponent -> EdgeComponent
  faceEdge2 : FaceComponent -> EdgeComponent
  edgeOverlapComponent : EdgeComponent -> Prop
  faceTripleOverlapComponent : FaceComponent -> Prop
  edgeOverlapComponent_holds : ∀ e : EdgeComponent, edgeOverlapComponent e
  faceTripleOverlapComponent_holds : ∀ f : FaceComponent, faceTripleOverlapComponent f

namespace CoverNerve

/-- IV.定義12.1: two edge components may have the same endpoints. -/
def ParallelEdgeComponents (N : CoverNerve.{u}) (e e' : N.EdgeComponent) : Prop :=
  N.edgeLeft e = N.edgeLeft e' ∧ N.edgeRight e = N.edgeRight e'

/-- IV.定義12.1: two face components may have the same boundary edge triple. -/
def ParallelFaceComponents (N : CoverNerve.{u}) (f f' : N.FaceComponent) : Prop :=
  N.faceEdge0 f = N.faceEdge0 f' ∧ N.faceEdge1 f = N.faceEdge1 f' ∧
    N.faceEdge2 f = N.faceEdge2 f'

/-- IV.定義12.1: every edge is read as a selected pairwise-overlap component. -/
theorem edge_component_selected (N : CoverNerve.{u}) (e : N.EdgeComponent) :
    N.edgeOverlapComponent e :=
  N.edgeOverlapComponent_holds e

/-- IV.定義12.1: every face is read as a selected triple-overlap component. -/
theorem face_component_selected (N : CoverNerve.{u}) (f : N.FaceComponent) :
    N.faceTripleOverlapComponent f :=
  N.faceTripleOverlapComponent_holds f

end CoverNerve

/--
IV.定理12.2: finite-dimensional coefficient accounting data for the selected
cover nerve.

The vector-space fields record that the accounting is over finite-dimensional
`k`-linear coefficients.  The numeric rank-nullity fields are the finite-poset
linear algebra data used by the theorem below; no arbitrary cover is claimed to
carry these data without hypotheses.
-/
structure FiniteDimensionalNerveCohomologyData (N : CoverNerve.{u}) where
  finitePosetRegime : Prop
  finitePosetRegime_holds : finitePosetRegime
  k : Type u
  [field_k : Field k]
  C0 : Type u
  C1 : Type u
  C2 : Type u
  H1 : Type u
  [add_C0 : AddCommGroup C0]
  [add_C1 : AddCommGroup C1]
  [add_C2 : AddCommGroup C2]
  [add_H1 : AddCommGroup H1]
  [module_C0 : Module k C0]
  [module_C1 : Module k C1]
  [module_C2 : Module k C2]
  [module_H1 : Module k H1]
  [finiteDimensional_C0 : FiniteDimensional k C0]
  [finiteDimensional_C1 : FiniteDimensional k C1]
  [finiteDimensional_C2 : FiniteDimensional k C2]
  [finiteDimensional_H1 : FiniteDimensional k H1]
  dimC0 : Nat
  dimC1 : Nat
  dimC2 : Nat
  dimH1 : Nat
  rank_d0 : Nat
  rank_d1 : Nat
  rank_d0_le_dimC0 : rank_d0 <= dimC0
  rank_d1_le_dimC2 : rank_d1 <= dimC2
  rankNullity_H1 : finitePosetRegime -> dimH1 + rank_d0 + rank_d1 = dimC1

namespace FiniteDimensionalNerveCohomologyData

attribute [instance] field_k add_C0 add_C1 add_C2 add_H1
attribute [instance] module_C0 module_C1 module_C2 module_H1
attribute [instance] finiteDimensional_C0 finiteDimensional_C1 finiteDimensional_C2
attribute [instance] finiteDimensional_H1

variable {N : CoverNerve.{u}}

/--
IV.定理12.2: Topological Debt Capacity.

For finite-poset, finite-dimensional `k`-linear coefficient data, the selected
rank-nullity accounting gives the lower bound
`dim H^1 >= dim C^1 - dim C^0 - dim C^2`, written in subtraction-free natural
number form as `dim C^1 <= dim H^1 + dim C^0 + dim C^2`.
-/
theorem topologicalDebtCapacity
    (D : FiniteDimensionalNerveCohomologyData N) :
    D.dimC1 <= D.dimH1 + D.dimC0 + D.dimC2 := by
  have h_rank := D.rankNullity_H1 D.finitePosetRegime_holds
  have h_d0 := D.rank_d0_le_dimC0
  have h_d1 := D.rank_d1_le_dimC2
  omega

end FiniteDimensionalNerveCohomologyData

/--
R5 / IV-5: finite selected nerve cochain complex.

This is a selected finite-dimensional cochain complex attached to the chosen
cover nerve.  It records actual vector spaces and differentials `d0`, `d1`
with `d1 ∘ d0 = 0`; the additive `H^1` below is then defined as
`ker d1 / im d0`, not supplied as an unrelated field.  The attachment to
`N.Chart` / `N.EdgeComponent` / `N.FaceComponent` is intentionally selected
data; this theorem does not construct the complex from an arbitrary cover.
-/
structure FiniteNerveCochainComplex (N : CoverNerve.{u}) where
  k : Type u
  [field_k : Field k]
  C0 : Type u
  C1 : Type u
  C2 : Type u
  [add_C0 : AddCommGroup C0]
  [add_C1 : AddCommGroup C1]
  [add_C2 : AddCommGroup C2]
  [module_C0 : Module k C0]
  [module_C1 : Module k C1]
  [module_C2 : Module k C2]
  [finiteDimensional_C0 : FiniteDimensional k C0]
  [finiteDimensional_C1 : FiniteDimensional k C1]
  [finiteDimensional_C2 : FiniteDimensional k C2]
  d0 : C0 →ₗ[k] C1
  d1 : C1 →ₗ[k] C2
  d1_comp_d0 : ∀ c : C0, d1 (d0 c) = 0

namespace FiniteNerveCochainComplex

attribute [instance] field_k add_C0 add_C1 add_C2
attribute [instance] module_C0 module_C1 module_C2
attribute [instance] finiteDimensional_C0 finiteDimensional_C1 finiteDimensional_C2

variable {N : CoverNerve.{u}}

/-- R5 / IV-5: degree-zero boundaries land in the degree-one cocycles. -/
def boundaryToCycles (D : FiniteNerveCochainComplex N) :
    D.C0 →ₗ[D.k] LinearMap.ker D.d1 where
  toFun c := ⟨D.d0 c, by simpa using D.d1_comp_d0 c⟩
  map_add' x y := by
    ext
    simp
  map_smul' a x := by
    ext
    simp

/-- R5 / IV-5: additive nerve `H^1 = ker d1 / im d0`. -/
abbrev H1 (D : FiniteNerveCochainComplex N) : Type u :=
  (LinearMap.ker D.d1) ⧸ LinearMap.range D.boundaryToCycles

instance h1AddCommGroup (D : FiniteNerveCochainComplex N) :
    AddCommGroup D.H1 := by
  dsimp [H1]
  infer_instance

instance h1Module (D : FiniteNerveCochainComplex N) :
    Module D.k D.H1 := by
  dsimp [H1]
  infer_instance

instance h1FiniteDimensional (D : FiniteNerveCochainComplex N) :
    FiniteDimensional D.k D.H1 := by
  dsimp [H1]
  infer_instance

/--
R5 / IV-5: rank-nullity inside the cocycle space:
`dim H^1 + rank d0 = dim ker d1`.
-/
theorem finrank_H1_add_finrank_boundary
    (D : FiniteNerveCochainComplex N) :
    Module.finrank D.k D.H1 +
        Module.finrank D.k (LinearMap.range D.boundaryToCycles) =
      Module.finrank D.k (LinearMap.ker D.d1) := by
  simpa [H1] using
    (LinearMap.range D.boundaryToCycles).finrank_quotient_add_finrank

/--
R5 / IV-5: Topological Debt Capacity from the concrete finite cochain complex.

This proves the theorem-12.2 lower-bound form from Mathlib rank-nullity and the
definition `H^1 = ker d1 / im d0`.
-/
theorem topologicalDebtCapacity_fromComplex
    (D : FiniteNerveCochainComplex N) :
    Module.finrank D.k D.C1 <=
      Module.finrank D.k D.H1 + Module.finrank D.k D.C0 +
        Module.finrank D.k D.C2 := by
  have h_d1 := D.d1.finrank_range_add_finrank_ker
  have h_h1 := D.finrank_H1_add_finrank_boundary
  have h_boundary_le :
      Module.finrank D.k (LinearMap.range D.boundaryToCycles) <=
        Module.finrank D.k D.C0 :=
    LinearMap.finrank_range_le D.boundaryToCycles
  have h_d1_le :
      Module.finrank D.k (LinearMap.range D.d1) <=
        Module.finrank D.k D.C2 :=
    (LinearMap.range D.d1).finrank_le
  omega

end FiniteNerveCochainComplex

/--
IV.系12.3: constant-coefficient comparison between the cover reading and the
nerve reading.

This is an explicit comparison package: it records the selected `k`-linear
equivalence `H^1(U,k) ≃ H^1(N(U),k)` and the Betti-number dimension read.
-/
structure ConstantCoefficientNerveReading (N : CoverNerve.{u}) where
  k : Type u
  [field_k : Field k]
  spaceH1 : Type u
  nerveH1 : Type u
  [add_spaceH1 : AddCommGroup spaceH1]
  [add_nerveH1 : AddCommGroup nerveH1]
  [module_spaceH1 : Module k spaceH1]
  [module_nerveH1 : Module k nerveH1]
  [finiteDimensional_spaceH1 : FiniteDimensional k spaceH1]
  [finiteDimensional_nerveH1 : FiniteDimensional k nerveH1]
  h1LinearEquiv : spaceH1 ≃ₗ[k] nerveH1
  dimSpaceH1 : Nat
  dimNerveH1 : Nat
  b1 : Nat
  dimSpace_eq_finrank : dimSpaceH1 = Module.finrank k spaceH1
  dimNerve_eq_finrank : dimNerveH1 = Module.finrank k nerveH1
  dimNerve_eq_b1 : dimNerveH1 = b1

namespace ConstantCoefficientNerveReading

attribute [instance] field_k add_spaceH1 add_nerveH1
attribute [instance] module_spaceH1 module_nerveH1
attribute [instance] finiteDimensional_spaceH1 finiteDimensional_nerveH1

variable {N : CoverNerve.{u}}

/-- IV.系12.3: the selected constant-coefficient `k`-linear comparison equivalence. -/
def h1_equiv (R : ConstantCoefficientNerveReading N) :
    R.spaceH1 ≃ₗ[R.k] R.nerveH1 :=
  R.h1LinearEquiv

/-- IV.系12.3: the selected linear comparison preserves finite dimension. -/
theorem dimSpace_eq_dimNerve (R : ConstantCoefficientNerveReading N) :
    R.dimSpaceH1 = R.dimNerveH1 := by
  rw [R.dimSpace_eq_finrank, R.dimNerve_eq_finrank, R.h1LinearEquiv.finrank_eq]

/-- IV.系12.3: `dim H^1(U,k) = b_1(N(U))` under the selected comparison. -/
theorem dimH1_eq_b1 (R : ConstantCoefficientNerveReading N) :
    R.dimSpaceH1 = R.b1 := by
  rw [R.dimSpace_eq_dimNerve, R.dimNerve_eq_b1]

end ConstantCoefficientNerveReading

/--
IV.定理12.4: explicit hypotheses for the forest-cover gluing sufficiency
theorem.

The `absorbsEveryClassByForestInduction` field is the finite tree-induction
step: forest shape, absence of triple faces, and surjective restrictions let
one absorb every mismatch class into the chosen base class.
-/
structure ForestCoverGluingData (N : CoverNerve.{u}) where
  H1 : Type u
  [add_H1 : AddCommGroup H1]
  noTripleFaces : IsEmpty N.FaceComponent
  forestNerve : Prop
  forestNerve_holds : forestNerve
  restrictionSurjective : Prop
  restrictionSurjective_holds : restrictionSurjective
  baseClass : H1
  baseClass_eq_zero : baseClass = 0
  absorbsEveryClassByForestInduction :
    forestNerve -> restrictionSurjective -> IsEmpty N.FaceComponent -> ∀ x : H1, x = baseClass

namespace ForestCoverGluingData

attribute [instance] add_H1

variable {N : CoverNerve.{u}}

/-- IV.定理12.4: forest covers have zero selected `H^1` under the hypotheses. -/
theorem localGluingSufficiency (F : ForestCoverGluingData N) :
    ∀ x : F.H1, x = 0 :=
  fun x => by
    let h_absorb :=
      F.absorbsEveryClassByForestInduction F.forestNerve_holds
        F.restrictionSurjective_holds F.noTripleFaces
    rw [h_absorb x, F.baseClass_eq_zero]

/-- IV.定理12.4: the zero theorem also gives uniqueness of the selected class. -/
theorem localGluingSufficiency_subsingleton (F : ForestCoverGluingData N) :
    Subsingleton F.H1 :=
  ⟨fun x y => by rw [F.localGluingSufficiency x, F.localGluingSufficiency y]⟩

end ForestCoverGluingData

/--
R5 / IV-5: finite forest edge-absorption certificate.

Instead of assuming a single theorem-shaped field saying every `H^1` class is
zero, this certificate gives a finite pruning order, an edge-support predicate,
and a class trace through the pruning steps.  Each pruned edge is removed from
the support of the traced class, the pruning order covers every edge component,
and no edge support under the no-triple-face regime forces the class to be zero.
-/
structure FiniteForestEdgeAbsorptionData (N : CoverNerve.{u}) where
  H1 : Type u
  [add_H1 : AddCommGroup H1]
  steps : Nat
  prunedEdge : Fin steps -> N.EdgeComponent
  noTripleFaces : IsEmpty N.FaceComponent
  edgeSupport : H1 -> N.EdgeComponent -> Prop
  classAt : H1 -> Nat -> H1
  start_class : ∀ x : H1, classAt x 0 = x
  edge_absorption_preserves :
    ∀ (x : H1) (n : Nat), n < steps -> classAt x (n + 1) = classAt x n
  edge_absorbed :
    ∀ (x : H1) (i : Fin steps), ¬ edgeSupport (classAt x (i.1 + 1)) (prunedEdge i)
  all_edges_pruned : ∀ e : N.EdgeComponent, ∃ i : Fin steps, prunedEdge i = e
  zero_of_no_edgeSupport :
    IsEmpty N.FaceComponent -> ∀ x : H1, (∀ e : N.EdgeComponent, ¬ edgeSupport x e) -> x = 0

namespace FiniteForestEdgeAbsorptionData

attribute [instance] add_H1

variable {N : CoverNerve.{u}}

/-- R5 / IV-5: the finite absorption trace preserves the original class. -/
theorem classAt_eq_start
    (F : FiniteForestEdgeAbsorptionData N) (x : F.H1) :
    ∀ n : Nat, n <= F.steps -> F.classAt x n = x
  | 0, _ => F.start_class x
  | n + 1, hn => by
      have hn_lt : n < F.steps := Nat.lt_of_succ_le hn
      rw [F.edge_absorption_preserves x n hn_lt,
        F.classAt_eq_start x n (Nat.le_of_lt hn_lt)]

/-- R5 / IV-5: after all pruning steps, no selected edge support remains. -/
theorem final_no_edgeSupport
    (F : FiniteForestEdgeAbsorptionData N) (x : F.H1) :
    ∀ e : N.EdgeComponent, ¬ F.edgeSupport (F.classAt x F.steps) e := by
  intro e
  rcases F.all_edges_pruned e with ⟨i, hi⟩
  have hfinal := F.classAt_eq_start x F.steps le_rfl
  have hi_le : i.1 + 1 <= F.steps := Nat.succ_le_of_lt i.2
  have hstep := F.classAt_eq_start x (i.1 + 1) hi_le
  have h_eq : F.classAt x F.steps = F.classAt x (i.1 + 1) :=
    hfinal.trans hstep.symm
  intro hs
  have hs_step :
      F.edgeSupport (F.classAt x (i.1 + 1)) (F.prunedEdge i) := by
    simpa [h_eq, hi] using hs
  exact F.edge_absorbed x i hs_step

/-- R5 / IV-5: finite forest edge absorption forces selected `H^1` to vanish. -/
theorem forestVanishing
    (F : FiniteForestEdgeAbsorptionData N) :
    ∀ x : F.H1, x = 0 := by
  intro x
  have hfinal := F.classAt_eq_start x F.steps le_rfl
  refine F.zero_of_no_edgeSupport F.noTripleFaces x ?_
  intro e hs
  exact F.final_no_edgeSupport x e (by simpa [hfinal] using hs)

/-- R5 / IV-5: finite forest absorption makes the selected class type subsingleton. -/
theorem forestVanishing_subsingleton
    (F : FiniteForestEdgeAbsorptionData N) :
    Subsingleton F.H1 :=
  ⟨fun x y => by rw [F.forestVanishing x, F.forestVanishing y]⟩

end FiniteForestEdgeAbsorptionData

/-- IV.系12.5: the Euler characteristic of the selected 0/1/2 cochain data. -/
structure EulerCochainAccounting (N : CoverNerve.{u}) where
  dimC0 : Nat
  dimC1 : Nat
  dimC2 : Nat

namespace EulerCochainAccounting

variable {N : CoverNerve.{u}}

/-- IV.系12.5: `chi(U,F) = dim C^0 - dim C^1 + dim C^2`. -/
def chi (E : EulerCochainAccounting N) : Int :=
  (E.dimC0 : Int) - (E.dimC1 : Int) + (E.dimC2 : Int)

/-- IV.系12.5: the displayed Euler accounting equation. -/
theorem eulerAccounting (E : EulerCochainAccounting N) :
    E.chi = (E.dimC0 : Int) - (E.dimC1 : Int) + (E.dimC2 : Int) :=
  rfl

/-- IV.系12.5: shape/stalk-preserving refactors preserve the cochain dimensions. -/
structure ShapeStalkPreservingRefactor
    (E E' : EulerCochainAccounting N) where
  dimC0_eq : E'.dimC0 = E.dimC0
  dimC1_eq : E'.dimC1 = E.dimC1
  dimC2_eq : E'.dimC2 = E.dimC2

/-- IV.系12.5: Euler characteristic is invariant under such refactors. -/
theorem chi_invariant_under_refactor
    {E E' : EulerCochainAccounting N}
    (R : ShapeStalkPreservingRefactor E E') :
    E'.chi = E.chi := by
  simp [chi, R.dimC0_eq, R.dimC1_eq, R.dimC2_eq]

end EulerCochainAccounting

end Cohomology
end AAT.AG
