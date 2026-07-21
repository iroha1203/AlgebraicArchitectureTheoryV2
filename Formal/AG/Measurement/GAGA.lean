import Formal.AG.Cohomology.PeriodStokes
import Formal.AG.Examples.DerivedPart5
import Formal.AG.Measurement.FiniteRegime
import Formal.AG.Measurement.Packet

noncomputable section

namespace AAT.AG
namespace Measurement

universe u v

/-!
Part VIII theorem 12.3: finite AAT-GAGA comparison.

The certified comparison is rooted in a generated finite-poset Čech source.
The source fixes the actual site, adequate cover, obstruction sheaf,
coefficient ring, canonical differential, and its nerve presentation before
any Hodge, period, capacity, or derived reading is formed.
-/

/-- VIII.Theorem 12.3: source data for one selected finite Čech comparison. -/
structure AATGAGAFiniteCechSource (M : MeasurementProfile.{u, v})
    [Field M.Coeff] where
  /-- The selected finite-poset site, adequate cover, coefficient sheaf, and
  canonical Čech differential. -/
  geometry : FiniteMeasurementGeometry M
  /-- Context selected from the actual finite-poset site. -/
  selectedContext : geometry.coverGeometry.ContextIndex
  /-- Cover index selected from the actual adequate cover. -/
  selectedCoverIndex : geometry.coverGeometry.cover.Index
  /-- The selected nerve presented by canonical Čech simplices. -/
  nerve : Cohomology.CoverNerve
  /-- The selected nerve cochain complex, over the profile coefficient field. -/
  nerveComplex : Cohomology.FiniteNerveCochainComplex nerve M.Coeff
  /-- The nerve vertices are the actual generated Čech zero-simplices. -/
  chartToCanonical : nerve.Chart ≃
    Site.FinitePosetCechSimplex geometry.coefficientRegime 0
  /-- The nerve edges are the actual generated Čech one-simplices. -/
  edgeToCanonical : nerve.EdgeComponent ≃
    Site.FinitePosetCechSimplex geometry.coefficientRegime 1
  /-- The nerve faces are the actual generated Čech two-simplices. -/
  faceToCanonical : nerve.FaceComponent ≃
    Site.FinitePosetCechSimplex geometry.coefficientRegime 2
  /-- Degree-zero nerve cochains compare with the generated canonical cochains. -/
  zeroToCanonical : nerveComplex.C0 ≃+ geometry.CechCochain 0
  /-- Degree-one nerve cochains compare with the generated canonical cochains. -/
  oneToCanonical : nerveComplex.C1 ≃+ geometry.CechCochain 1
  /-- Degree-two nerve cochains compare with the generated canonical cochains. -/
  twoToCanonical : nerveComplex.C2 ≃+ geometry.CechCochain 2
  /-- The selected degree-zero differential is the canonical Čech differential. -/
  d0_toCanonical : ∀ c : nerveComplex.C0,
    oneToCanonical (nerveComplex.d0 c) =
      geometry.cechComplex.differential 0 (zeroToCanonical c)
  /-- The selected degree-one differential is the canonical Čech differential. -/
  d1_toCanonical : ∀ c : nerveComplex.C1,
    twoToCanonical (nerveComplex.d1 c) =
      geometry.cechComplex.differential 1 (oneToCanonical c)

namespace AATGAGAFiniteCechSource

/-- The profile site selected through the actual finite-poset realization. -/
def selectedSite {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    (S : AATGAGAFiniteCechSource M) : M.SiteObj :=
  S.geometry.siteObjEquiv.symm S.selectedContext

/-- The profile cover selected through the actual adequate-cover realization. -/
def selectedCover {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    (S : AATGAGAFiniteCechSource M) : M.Cover :=
  S.geometry.coverEquiv.symm S.selectedCoverIndex

/-- Capacity is read from the profile-coefficient nerve complex. -/
def topologicalCapacityStatement {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    (S : AATGAGAFiniteCechSource M) : Prop :=
  Module.finrank M.Coeff S.nerveComplex.C1 <=
    Module.finrank M.Coeff S.nerveComplex.H1 +
      Module.finrank M.Coeff S.nerveComplex.C0 +
        Module.finrank M.Coeff S.nerveComplex.C2

/-- Derive capacity from the selected profile-coefficient nerve complex. -/
theorem topologicalCapacityStatement_holds {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    (S : AATGAGAFiniteCechSource M) : S.topologicalCapacityStatement :=
  S.nerveComplex.topologicalDebtCapacity_fromComplex

end AATGAGAFiniteCechSource

/-- VIII.Theorem 12.3: real Hodge realization of a selected profile Čech complex. -/
structure AATGAGARealCechHodgeInput {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    (S : AATGAGAFiniteCechSource M) where
  /-- Real coordinates for the selected canonical Čech zero-cochains. -/
  RealC0 : Type v
  /-- Real coordinates for the selected canonical Čech one-cochains. -/
  RealC1 : Type v
  /-- Real coordinates for the selected canonical Čech two-cochains. -/
  RealC2 : Type v
  /-- Normed group structure on selected zero-cochain coordinates. -/
  [zeroNormed : NormedAddCommGroup RealC0]
  /-- Inner product on selected zero-cochain coordinates. -/
  [zeroInner : InnerProductSpace ℝ RealC0]
  /-- Finiteness of selected zero-cochain coordinates. -/
  [zeroFinite : @Module.Finite ℝ RealC0 _ _
    ((@InnerProductSpace.toNormedSpace ℝ RealC0 _ _ zeroInner).toModule)]
  /-- Normed group structure on selected one-cochain coordinates. -/
  [oneNormed : NormedAddCommGroup RealC1]
  /-- Inner product on selected one-cochain coordinates. -/
  [oneInner : InnerProductSpace ℝ RealC1]
  /-- Finiteness of selected one-cochain coordinates. -/
  [oneFinite : @Module.Finite ℝ RealC1 _ _
    ((@InnerProductSpace.toNormedSpace ℝ RealC1 _ _ oneInner).toModule)]
  /-- Normed group structure on selected two-cochain coordinates. -/
  [twoNormed : NormedAddCommGroup RealC2]
  /-- Inner product on selected two-cochain coordinates. -/
  [twoInner : InnerProductSpace ℝ RealC2]
  /-- Finiteness of selected two-cochain coordinates. -/
  [twoFinite : @Module.Finite ℝ RealC2 _ _
    ((@InnerProductSpace.toNormedSpace ℝ RealC2 _ _ twoInner).toModule)]
  /-- Explicit coefficient comparison used to form the real Čech reading. -/
  coefficientToReal : M.Coeff ≃+* ℝ
  /-- Additive coordinate identifications for the selected canonical Čech complex. -/
  zeroToReal : S.nerveComplex.C0 ≃+ RealC0
  oneToReal : S.nerveComplex.C1 ≃+ RealC1
  twoToReal : S.nerveComplex.C2 ≃+ RealC2
  /-- The coordinate maps respect the selected profile coefficient comparison. -/
  zeroToReal_smul : ∀ (a : M.Coeff) (c : S.nerveComplex.C0),
    zeroToReal (a • c) = coefficientToReal a • zeroToReal c
  oneToReal_smul : ∀ (a : M.Coeff) (c : S.nerveComplex.C1),
    oneToReal (a • c) = coefficientToReal a • oneToReal c
  twoToReal_smul : ∀ (a : M.Coeff) (c : S.nerveComplex.C2),
    twoToReal (a • c) = coefficientToReal a • twoToReal c
  /-- Real nerve coordinates on the selected charts. -/
  zeroCochainCoordinates : RealC0 → (S.nerve.Chart → ℝ)
  zeroCochainCoordinates_inv : (S.nerve.Chart → ℝ) → RealC0
  zeroCochainCoordinates_left_inv : ∀ c,
    zeroCochainCoordinates_inv (zeroCochainCoordinates c) = c
  zeroCochainCoordinates_right_inv : ∀ c,
    zeroCochainCoordinates (zeroCochainCoordinates_inv c) = c
  zeroCochainCoordinates_add : ∀ c d,
    zeroCochainCoordinates (c + d) = zeroCochainCoordinates c + zeroCochainCoordinates d
  /-- Real nerve coordinates on the selected overlaps. -/
  oneCochainCoordinates : RealC1 → (S.nerve.EdgeComponent → ℝ)
  oneCochainCoordinates_inv : (S.nerve.EdgeComponent → ℝ) → RealC1
  oneCochainCoordinates_left_inv : ∀ c,
    oneCochainCoordinates_inv (oneCochainCoordinates c) = c
  oneCochainCoordinates_right_inv : ∀ c,
    oneCochainCoordinates (oneCochainCoordinates_inv c) = c
  oneCochainCoordinates_add : ∀ c d,
    oneCochainCoordinates (c + d) = oneCochainCoordinates c + oneCochainCoordinates d
  /-- Real nerve coordinates on the selected triple overlaps. -/
  twoCochainCoordinates : RealC2 → (S.nerve.FaceComponent → ℝ)
  twoCochainCoordinates_inv : (S.nerve.FaceComponent → ℝ) → RealC2
  twoCochainCoordinates_left_inv : ∀ c,
    twoCochainCoordinates_inv (twoCochainCoordinates c) = c
  twoCochainCoordinates_right_inv : ∀ c,
    twoCochainCoordinates (twoCochainCoordinates_inv c) = c
  twoCochainCoordinates_add : ∀ c d,
    twoCochainCoordinates (c + d) = twoCochainCoordinates c + twoCochainCoordinates d
  /-- The real chart coordinates preserve scalar multiplication. -/
  zeroCochainCoordinates_smul : ∀ (a : ℝ) (c : RealC0),
    zeroCochainCoordinates (a • c) = a • zeroCochainCoordinates c
  /-- The real overlap coordinates preserve scalar multiplication. -/
  oneCochainCoordinates_smul : ∀ (a : ℝ) (c : RealC1),
    oneCochainCoordinates (a • c) = a • oneCochainCoordinates c
  /-- The real triple-overlap coordinates preserve scalar multiplication. -/
  twoCochainCoordinates_smul : ∀ (a : ℝ) (c : RealC2),
    twoCochainCoordinates (a • c) = a • twoCochainCoordinates c
  /-- The real coordinates are the profile Čech coordinates after coefficient comparison. -/
  zeroCoordinates_eq_source : ∀ (c : S.nerveComplex.C0) (chart : S.nerve.Chart),
    zeroCochainCoordinates (zeroToReal c) chart =
      coefficientToReal (S.nerveComplex.zeroCochainCoordinates c chart)
  oneCoordinates_eq_source : ∀ (c : S.nerveComplex.C1) (edge : S.nerve.EdgeComponent),
    oneCochainCoordinates (oneToReal c) edge =
      coefficientToReal (S.nerveComplex.oneCochainCoordinates c edge)
  twoCoordinates_eq_source : ∀ (c : S.nerveComplex.C2) (face : S.nerve.FaceComponent),
    twoCochainCoordinates (twoToReal c) face =
      coefficientToReal (S.nerveComplex.twoCochainCoordinates c face)
  /-- The real degree-zero map transported from the selected profile Čech complex. -/
  realD0 : RealC0 →ₗ[ℝ] RealC1
  /-- The real degree-one map transported from the selected profile Čech complex. -/
  realD1 : RealC1 →ₗ[ℝ] RealC2
  /-- The selected real Čech maps form a cochain complex. -/
  real_d1_comp_d0 : realD1.comp realD0 = 0
  /-- The real degree-zero map is the selected Čech differential in these coordinates. -/
  realD0_eq_profile : ∀ c,
    realD0 (zeroToReal c) = oneToReal (S.nerveComplex.d0 c)
  /-- The real degree-one map is the selected Čech differential in these coordinates. -/
  realD1_eq_profile : ∀ c,
    realD1 (oneToReal c) = twoToReal (S.nerveComplex.d1 c)
  /-- The real degree-zero map has the selected oriented-edge incidence formula. -/
  d0_eq_edgeIncidence : ∀ (c : RealC0) (e : S.nerve.EdgeComponent),
    oneCochainCoordinates (realD0 c) e =
      zeroCochainCoordinates c (S.nerve.edgeRight e) -
        zeroCochainCoordinates c (S.nerve.edgeLeft e)
  /-- The real degree-one map has the selected-face incidence formula. -/
  d1_eq_faceIncidence : ∀ (c : RealC1) (f : S.nerve.FaceComponent),
    twoCochainCoordinates (realD1 c) f =
      oneCochainCoordinates c (S.nerve.faceEdge0 f) -
        oneCochainCoordinates c (S.nerve.faceEdge1 f) +
          oneCochainCoordinates c (S.nerve.faceEdge2 f)

namespace AATGAGARealCechHodgeInput

/-- The selected real chart coordinate map with its certified scalar law. -/
noncomputable def zeroCochainLinearCoordinates {M : MeasurementProfile.{u, v}}
    [Field M.Coeff] {S : AATGAGAFiniteCechSource M}
    (H : AATGAGARealCechHodgeInput S) : by
  letI := H.zeroNormed
  letI := H.zeroInner
  exact H.RealC0 ≃ₗ[ℝ] (S.nerve.Chart → ℝ) := by
  letI := H.zeroNormed
  letI := H.zeroInner
  exact {
    toFun := H.zeroCochainCoordinates
    invFun := H.zeroCochainCoordinates_inv
    left_inv := H.zeroCochainCoordinates_left_inv
    right_inv := H.zeroCochainCoordinates_right_inv
    map_add' := H.zeroCochainCoordinates_add
    map_smul' := H.zeroCochainCoordinates_smul }

/-- The selected real overlap coordinate map with its certified scalar law. -/
noncomputable def oneCochainLinearCoordinates {M : MeasurementProfile.{u, v}}
    [Field M.Coeff] {S : AATGAGAFiniteCechSource M}
    (H : AATGAGARealCechHodgeInput S) : by
  letI := H.oneNormed
  letI := H.oneInner
  exact H.RealC1 ≃ₗ[ℝ] (S.nerve.EdgeComponent → ℝ) := by
  letI := H.oneNormed
  letI := H.oneInner
  exact {
    toFun := H.oneCochainCoordinates
    invFun := H.oneCochainCoordinates_inv
    left_inv := H.oneCochainCoordinates_left_inv
    right_inv := H.oneCochainCoordinates_right_inv
    map_add' := H.oneCochainCoordinates_add
    map_smul' := H.oneCochainCoordinates_smul }

/-- The selected real triple-overlap coordinate map with its certified scalar law. -/
noncomputable def twoCochainLinearCoordinates {M : MeasurementProfile.{u, v}}
    [Field M.Coeff] {S : AATGAGAFiniteCechSource M}
    (H : AATGAGARealCechHodgeInput S) : by
  letI := H.twoNormed
  letI := H.twoInner
  exact H.RealC2 ≃ₗ[ℝ] (S.nerve.FaceComponent → ℝ) := by
  letI := H.twoNormed
  letI := H.twoInner
  exact {
    toFun := H.twoCochainCoordinates
    invFun := H.twoCochainCoordinates_inv
    left_inv := H.twoCochainCoordinates_left_inv
    right_inv := H.twoCochainCoordinates_right_inv
    map_add' := H.twoCochainCoordinates_add
    map_smul' := H.twoCochainCoordinates_smul }

/-- The selected real Čech complex, built from the profile-realized cochain
coordinates and their transported differentials. -/
noncomputable def realNerveComplex {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    {S : AATGAGAFiniteCechSource M} (H : AATGAGARealCechHodgeInput S) : by
  letI := H.zeroNormed
  letI := H.zeroInner
  letI := H.zeroFinite
  letI := H.oneNormed
  letI := H.oneInner
  letI := H.oneFinite
  letI := H.twoNormed
  letI := H.twoInner
  letI := H.twoFinite
  exact Cohomology.FiniteNerveCochainComplex S.nerve ℝ := by
  letI := H.zeroNormed
  letI := H.zeroInner
  letI := H.zeroFinite
  letI := H.oneNormed
  letI := H.oneInner
  letI := H.oneFinite
  letI := H.twoNormed
  letI := H.twoInner
  letI := H.twoFinite
  exact {
    C0 := H.RealC0
    C1 := H.RealC1
    C2 := H.RealC2
    add_C0 := by infer_instance
    add_C1 := by infer_instance
    add_C2 := by infer_instance
    module_C0 := (@InnerProductSpace.toNormedSpace ℝ H.RealC0 _ _ H.zeroInner).toModule
    module_C1 := (@InnerProductSpace.toNormedSpace ℝ H.RealC1 _ _ H.oneInner).toModule
    module_C2 := (@InnerProductSpace.toNormedSpace ℝ H.RealC2 _ _ H.twoInner).toModule
    finiteDimensional_C0 := H.zeroFinite
    finiteDimensional_C1 := H.oneFinite
    finiteDimensional_C2 := H.twoFinite
    d0 := H.realD0
    d1 := H.realD1
    d1_comp_d0 := by
      intro c
      exact LinearMap.congr_fun H.real_d1_comp_d0 c
    zeroCochainCoordinates := H.zeroCochainLinearCoordinates
    oneCochainCoordinates := H.oneCochainLinearCoordinates
    twoCochainCoordinates := H.twoCochainLinearCoordinates
    d0_eq_edgeIncidence := H.d0_eq_edgeIncidence
    d1_eq_faceIncidence := H.d1_eq_faceIncidence }

/-- The finite Hodge complex is formed from the selected real Čech maps. -/
noncomputable def realFiniteComplex {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    {S : AATGAGAFiniteCechSource M} (H : AATGAGARealCechHodgeInput S) : by
  letI := H.zeroNormed
  letI := H.zeroInner
  letI := H.zeroFinite
  letI := H.oneNormed
  letI := H.oneInner
  letI := H.oneFinite
  letI := H.twoNormed
  letI := H.twoInner
  letI := H.twoFinite
  exact RealFiniteInnerProductComplex H.RealC0 H.RealC1 H.RealC2 := by
  letI := H.zeroNormed
  letI := H.zeroInner
  letI := H.zeroFinite
  letI := H.oneNormed
  letI := H.oneInner
  letI := H.oneFinite
  letI := H.twoNormed
  letI := H.twoInner
  letI := H.twoFinite
  exact {
    dPrev := H.realNerveComplex.d0
    dNext := H.realNerveComplex.d1
    d_comp_d := by
      apply LinearMap.ext
      intro c
      exact H.realNerveComplex.d1_comp_d0 c }

/-- The selected real Čech `H¹` is linearly equivalent to the cohomology of
the Hodge complex formed from the same differentials. -/
noncomputable def h1LinearEquivHodgeCohomology {M : MeasurementProfile.{u, v}}
    [Field M.Coeff] {S : AATGAGAFiniteCechSource M}
    (H : AATGAGARealCechHodgeInput S) : by
  letI := H.zeroNormed
  letI := H.zeroInner
  letI := H.zeroFinite
  letI := H.oneNormed
  letI := H.oneInner
  letI := H.oneFinite
  letI := H.twoNormed
  letI := H.twoInner
  letI := H.twoFinite
  exact H.realNerveComplex.H1 ≃ₗ[ℝ] H.realFiniteComplex.cohomology := by
  letI := H.zeroNormed
  letI := H.zeroInner
  letI := H.zeroFinite
  letI := H.oneNormed
  letI := H.oneInner
  letI := H.oneFinite
  letI := H.twoNormed
  letI := H.twoInner
  letI := H.twoFinite
  let D := H.realNerveComplex
  let K := H.realFiniteComplex
  have hBoundaries : K.boundariesInCycles = LinearMap.range D.boundaryToCycles := by
    change H.realD0.range.comap H.realD1.ker.subtype =
      LinearMap.range D.boundaryToCycles
    ext x
    change (∃ y, H.realD0 y = x.val) ↔
      (∃ y, D.boundaryToCycles y = x)
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨y, ?_⟩
      apply Subtype.ext
      exact hy
    · rintro ⟨y, hy⟩
      refine ⟨y, ?_⟩
      have hy' := congrArg Subtype.val hy
      simpa [Cohomology.FiniteNerveCochainComplex.boundaryToCycles] using hy'
  dsimp only [Cohomology.FiniteNerveCochainComplex.H1,
    RealFiniteInnerProductComplex.cohomology]
  change (D.d1.ker ⧸ D.boundaryToCycles.range) ≃ₗ[ℝ]
    D.d1.ker ⧸ K.boundariesInCycles
  rw [hBoundaries]
  exact LinearEquiv.refl ℝ _

/-- The selected real Čech `H¹` is linearly equivalent to the harmonic
Laplacian kernel. -/
noncomputable def h1LinearEquivLaplacianKernel {M : MeasurementProfile.{u, v}}
    [Field M.Coeff] {S : AATGAGAFiniteCechSource M}
    (H : AATGAGARealCechHodgeInput S) : by
  letI := H.zeroNormed
  letI := H.zeroInner
  letI := H.zeroFinite
  letI := H.oneNormed
  letI := H.oneInner
  letI := H.oneFinite
  letI := H.twoNormed
  letI := H.twoInner
  letI := H.twoFinite
  exact H.realNerveComplex.H1 ≃ₗ[ℝ] H.realFiniteComplex.laplacian.ker :=
  by
    letI := H.zeroNormed
    letI := H.zeroInner
    letI := H.zeroFinite
    letI := H.oneNormed
    letI := H.oneInner
    letI := H.oneFinite
    letI := H.twoNormed
    letI := H.twoInner
    letI := H.twoFinite
    exact H.h1LinearEquivHodgeCohomology.trans
      H.realFiniteComplex.laplacianKernelEquivCohomology.symm

/-- A degree-zero, degree-one, and degree-two additive cochain comparison
that commutes with both differentials descends to additive `H¹` comparison.

Implementation notes: the result is additive because the two complexes may
use different coefficient fields.  The proof restricts the degree-one map to
cocycles and descends it through the image of degree zero; no cohomology
equivalence is accepted as an input. -/
private theorem sourceH1AddEquivOfCochainComparison
    {N : Cohomology.CoverNerve} {k : Type v} [Field k]
    (A : Cohomology.FiniteNerveCochainComplex N k)
    (D : Cohomology.FiniteNerveCochainComplex N ℝ)
    (zeroToReal : A.C0 ≃+ D.C0) (oneToReal : A.C1 ≃+ D.C1)
    (twoToReal : A.C2 ≃+ D.C2)
    (d0_comm : ∀ c, D.d0 (zeroToReal c) = oneToReal (A.d0 c))
    (d1_comm : ∀ c, D.d1 (oneToReal c) = twoToReal (A.d1 c)) :
    Nonempty (A.H1 ≃+ D.H1) := by
  let eCycles : A.d1.ker ≃+ D.d1.ker := {
    toFun := fun x => ⟨oneToReal x, by
      change D.d1 (oneToReal x.val) = 0
      rw [d1_comm]
      rw [x.property, twoToReal.map_zero]⟩
    invFun := fun y => ⟨oneToReal.symm y.val, by
      change A.d1 (oneToReal.symm y.val) = 0
      apply twoToReal.injective
      rw [← d1_comm]
      simp⟩
    left_inv := by
      rintro ⟨x, hx⟩
      apply Subtype.ext
      exact oneToReal.symm_apply_apply x
    right_inv := by
      rintro ⟨y, hy⟩
      apply Subtype.ext
      exact oneToReal.apply_symm_apply y
    map_add' := by
      rintro ⟨x, hx⟩ ⟨y, hy⟩
      apply Subtype.ext
      exact oneToReal.map_add x y }
  let eCyclesInv : D.d1.ker ≃+ A.d1.ker := eCycles.symm
  let qA : AddSubgroup A.d1.ker := A.boundaryToCycles.range.toAddSubgroup
  let qD : AddSubgroup D.d1.ker := D.boundaryToCycles.range.toAddSubgroup
  letI : qA.Normal := AddSubgroup.normal_of_comm qA
  letI : qD.Normal := AddSubgroup.normal_of_comm qD
  letI : AddCommGroup (A.d1.ker ⧸ qA) :=
    QuotientAddGroup.Quotient.addCommGroup qA
  letI : AddCommGroup (D.d1.ker ⧸ qD) :=
    QuotientAddGroup.Quotient.addCommGroup qD
  have h_forward_image : ∀ x, x ∈ qA → eCycles x ∈ qD := by
    rintro x ⟨c, rfl⟩
    refine ⟨zeroToReal c, ?_⟩
    apply Subtype.ext
    exact d0_comm c
  have h_backward_image : ∀ x, x ∈ qD → eCyclesInv x ∈ qA := by
    rintro x ⟨c, rfl⟩
    refine ⟨zeroToReal.symm c, ?_⟩
    apply Subtype.ext
    apply oneToReal.injective
    change oneToReal (A.d0 (zeroToReal.symm c)) =
      oneToReal (oneToReal.symm (D.d0 c))
    rw [oneToReal.apply_symm_apply]
    have hc := d0_comm (zeroToReal.symm c)
    simpa using hc.symm
  let forward : (A.d1.ker ⧸ qA) →+ (D.d1.ker ⧸ qD) :=
    QuotientAddGroup.lift qA ((QuotientAddGroup.mk' qD).comp eCycles.toAddMonoidHom) (by
      intro x hx
      exact (QuotientAddGroup.eq_zero_iff (eCycles x)).mpr (h_forward_image x hx))
  let backward : (D.d1.ker ⧸ qD) →+ (A.d1.ker ⧸ qA) :=
    QuotientAddGroup.lift qD ((QuotientAddGroup.mk' qA).comp eCyclesInv.toAddMonoidHom) (by
      intro x hx
      exact (QuotientAddGroup.eq_zero_iff (eCyclesInv x)).mpr (h_backward_image x hx))
  exact ⟨{
    toFun := forward
    invFun := backward
    left_inv := by
      intro x
      refine Quotient.inductionOn' x ?_
      intro x
      change backward (forward (QuotientAddGroup.mk x)) = QuotientAddGroup.mk x
      simp only [forward, backward, QuotientAddGroup.lift_mk, AddMonoidHom.comp_apply]
      change QuotientAddGroup.mk (eCyclesInv (eCycles x)) = QuotientAddGroup.mk x
      rw [eCycles.symm_apply_apply]
    right_inv := by
      intro x
      refine Quotient.inductionOn' x ?_
      intro x
      change forward (backward (QuotientAddGroup.mk x)) = QuotientAddGroup.mk x
      simp only [forward, backward, QuotientAddGroup.lift_mk, AddMonoidHom.comp_apply]
      change QuotientAddGroup.mk (eCycles (eCyclesInv x)) = QuotientAddGroup.mk x
      rw [eCycles.apply_symm_apply]
    map_add' := forward.map_add }⟩

/-- The real Čech complex is the selected profile complex after the stated
coefficient and cochain realizations. -/
def profileRealificationStatement {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    {S : AATGAGAFiniteCechSource M} (H : AATGAGARealCechHodgeInput S) : by
  letI := H.zeroNormed
  letI := H.zeroInner
  letI := H.oneNormed
  letI := H.oneInner
  letI := H.twoNormed
  letI := H.twoInner
  exact Prop := by
  letI := H.zeroNormed
  letI := H.zeroInner
  letI := H.oneNormed
  letI := H.oneInner
  letI := H.twoNormed
  letI := H.twoInner
  exact (∀ (a : M.Coeff) (c : S.nerveComplex.C0),
    H.zeroToReal (a • c) = H.coefficientToReal a • H.zeroToReal c) ∧
  (∀ (a : M.Coeff) (c : S.nerveComplex.C1),
    H.oneToReal (a • c) = H.coefficientToReal a • H.oneToReal c) ∧
  (∀ (a : M.Coeff) (c : S.nerveComplex.C2),
    H.twoToReal (a • c) = H.coefficientToReal a • H.twoToReal c) ∧
  (∀ c, H.realD0 (H.zeroToReal c) = H.oneToReal (S.nerveComplex.d0 c)) ∧
  (∀ c, H.realD1 (H.oneToReal c) = H.twoToReal (S.nerveComplex.d1 c)) ∧
  (∀ (c : S.nerveComplex.C0) (chart : S.nerve.Chart),
    H.zeroCochainCoordinates (H.zeroToReal c) chart =
      H.coefficientToReal (S.nerveComplex.zeroCochainCoordinates c chart)) ∧
  (∀ (c : S.nerveComplex.C1) (edge : S.nerve.EdgeComponent),
    H.oneCochainCoordinates (H.oneToReal c) edge =
      H.coefficientToReal (S.nerveComplex.oneCochainCoordinates c edge)) ∧
  ∀ (c : S.nerveComplex.C2) (face : S.nerve.FaceComponent),
    H.twoCochainCoordinates (H.twoToReal c) face =
      H.coefficientToReal (S.nerveComplex.twoCochainCoordinates c face)

/-- The source-to-real realization follows from the concrete coordinate and
differential data, rather than from a supplied cohomology conclusion. -/
theorem profileRealificationStatement_holds {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    {S : AATGAGAFiniteCechSource M} (H : AATGAGARealCechHodgeInput S) :
    H.profileRealificationStatement := by
  letI := H.zeroNormed
  letI := H.zeroInner
  letI := H.oneNormed
  letI := H.oneInner
  letI := H.twoNormed
  letI := H.twoInner
  exact
  ⟨H.zeroToReal_smul, H.oneToReal_smul, H.twoToReal_smul,
    H.realD0_eq_profile, H.realD1_eq_profile,
    H.zeroCoordinates_eq_source, H.oneCoordinates_eq_source, H.twoCoordinates_eq_source⟩

/-- Hodge and harmonic/Čech-cohomology conclusions for the selected realified model. -/
def hodgeStatement {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    {S : AATGAGAFiniteCechSource M} (H : AATGAGARealCechHodgeInput S) : Prop := by
  letI := H.zeroNormed
  letI := H.zeroInner
  letI := H.zeroFinite
  letI := H.oneNormed
  letI := H.oneInner
  letI := H.oneFinite
  letI := H.twoNormed
  letI := H.twoInner
  letI := H.twoFinite
  exact H.profileRealificationStatement ∧
    (∀ c, H.realFiniteComplex.exactPart c + H.realFiniteComplex.harmonicPart c +
      H.realFiniteComplex.coexactPart c = c) ∧
      Nonempty (S.nerveComplex.H1 ≃+ H.realFiniteComplex.laplacian.ker)

/-- Derive the selected Hodge and harmonic/cohomology statements.

Implementation notes: the source-to-real maps are restricted to cocycles and
then descend to quotient cohomology through the two differential-compatibility
equalities.  This makes the source Čech `H¹` comparison part of the proof,
rather than an input certificate. -/
theorem hodgeStatement_holds {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    {S : AATGAGAFiniteCechSource M} (H : AATGAGARealCechHodgeInput S) :
    H.hodgeStatement := by
  letI := H.zeroNormed
  letI := H.zeroInner
  letI := H.zeroFinite
  letI := H.oneNormed
  letI := H.oneInner
  letI := H.oneFinite
  letI := H.twoNormed
  letI := H.twoInner
  letI := H.twoFinite
  rcases sourceH1AddEquivOfCochainComparison S.nerveComplex H.realNerveComplex
    H.zeroToReal H.oneToReal H.twoToReal H.realD0_eq_profile H.realD1_eq_profile with ⟨e⟩
  exact ⟨H.profileRealificationStatement_holds,
    H.realFiniteComplex.hodge_decomposition,
    ⟨e.trans H.h1LinearEquivLaplacianKernel.toAddEquiv⟩⟩

/-- Period/Stokes on the selected real Čech differential, its Riesz-dual
selected chains, and their pairing. -/
def periodStokesStatement {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    {S : AATGAGAFiniteCechSource M} (H : AATGAGARealCechHodgeInput S) : Prop := by
  letI := H.zeroNormed
  letI := H.zeroInner
  letI := H.zeroFinite
  letI := H.oneNormed
  letI := H.oneInner
  letI := H.oneFinite
  letI := H.twoNormed
  letI := H.twoInner
  letI := H.twoFinite
  exact ∀ (omega : H.RealC0) (gamma : H.RealC1),
    inner ℝ (H.realD0 omega) gamma =
      inner ℝ omega (H.realFiniteComplex.dPrev.adjoint gamma)

/-- Derive Period/Stokes from the adjoint of the selected real Čech map. -/
theorem periodStokesStatement_holds {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    {S : AATGAGAFiniteCechSource M} (H : AATGAGARealCechHodgeInput S) :
    H.periodStokesStatement := by
  letI := H.zeroNormed
  letI := H.zeroInner
  letI := H.zeroFinite
  letI := H.oneNormed
  letI := H.oneInner
  letI := H.oneFinite
  letI := H.twoNormed
  letI := H.twoInner
  letI := H.twoFinite
  intro omega gamma
  change inner ℝ (H.realFiniteComplex.dPrev omega) gamma = _
  simpa using
    (H.realFiniteComplex.dPrev.adjoint_inner_right omega gamma).symm

end AATGAGARealCechHodgeInput

/-- VIII.Theorem 12.3: finite data shared by every certified comparison. -/
structure AATGAGACommonFiniteData (M : MeasurementProfile.{u, v}) [Field M.Coeff] where
  /-- The finite Čech source shared by all certified axes. -/
  finiteCechSource : AATGAGAFiniteCechSource M
  /-- The measurement-domain element selected for the comparison. -/
  selectedMeasurement : M.Domain
  /-- Evidence that the selected measurement belongs to the measured profile. -/
  measuredSelection : M.Measured_M selectedMeasurement
  /-- The common ambient used for the selected law-ideal reading. -/
  commonAmbient : CommonAmbientPair M
  /-- The left ambient domain is the selected measurement-domain element. -/
  ambientLeftDomain_eq : commonAmbient.leftDomain = selectedMeasurement
  /-- The right ambient domain is the selected measurement-domain element. -/
  ambientRightDomain_eq : commonAmbient.rightDomain = selectedMeasurement

namespace AATGAGACommonFiniteData

/-- The site used by all axes is read from the finite Čech source. -/
def selectedSite {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    (C : AATGAGACommonFiniteData M) : M.SiteObj :=
  C.finiteCechSource.selectedSite

/-- The cover used by all axes is read from the finite Čech source. -/
def selectedCover {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    (C : AATGAGACommonFiniteData M) : M.Cover :=
  C.finiteCechSource.selectedCover

/-- Coherence facts tying every selected datum to its source realization. -/
def coherent {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    (C : AATGAGACommonFiniteData M) : Prop :=
  M.InScope C.selectedMeasurement ∧
    C.commonAmbient.commonRingedSite ∧
      C.commonAmbient.lawIdealsInCommonAmbient ∧
        C.commonAmbient.coefficientsCompatible ∧
          C.commonAmbient.witnessesComparable ∧
            C.commonAmbient.comparisonProfileFixed ∧
              C.commonAmbient.noComparisonWithoutCommonAmbient ∧
                C.commonAmbient.leftDomain = C.selectedMeasurement ∧
                  C.commonAmbient.rightDomain = C.selectedMeasurement

/-- The selected finite data satisfy their direct realization equalities. -/
theorem coherent_holds {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    (C : AATGAGACommonFiniteData M) : C.coherent :=
  ⟨C.measuredSelection.inScope,
    C.commonAmbient.commonRingedSite_cert,
    C.commonAmbient.lawIdealsInCommonAmbient_cert,
    C.commonAmbient.coefficientsCompatible_cert,
    C.commonAmbient.witnessesComparable_cert,
    C.commonAmbient.comparisonProfileFixed_cert,
    C.commonAmbient.noComparisonWithoutCommonAmbient_cert,
    C.ambientLeftDomain_eq, C.ambientRightDomain_eq⟩

end AATGAGACommonFiniteData

/-- VIII.Theorem 12.3: common-ambient reading of the selected monomial conflict. -/
structure SelectedDerivedConflictTheoremPackage {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    (C : AATGAGACommonFiniteData M) where
  /-- Reading of common-ambient law ideals as shared-witness monomial ideals. -/
  readLawIdeal : C.commonAmbient.LawIdeal →
    Ideal (Derived.Counterexample.SharedWitnessCoord.ChartRing M.Coeff)
  /-- The left common-ambient law ideal reads as `idealU`. -/
  leftIdeal_eq : readLawIdeal C.commonAmbient.leftLawIdeal =
    Derived.Counterexample.SharedWitnessCoord.idealU M.Coeff
  /-- The right common-ambient law ideal reads as `idealV`. -/
  rightIdeal_eq : readLawIdeal C.commonAmbient.rightLawIdeal =
    Derived.Counterexample.SharedWitnessCoord.idealV M.Coeff

namespace SelectedDerivedConflictTheoremPackage

/-- The left monomial ideal read from the common ambient. -/
def leftIdeal {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    {C : AATGAGACommonFiniteData M} (P : SelectedDerivedConflictTheoremPackage C) :
    Ideal (Derived.Counterexample.SharedWitnessCoord.ChartRing M.Coeff) :=
  P.readLawIdeal C.commonAmbient.leftLawIdeal

/-- The right monomial ideal read from the common ambient. -/
def rightIdeal {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    {C : AATGAGACommonFiniteData M} (P : SelectedDerivedConflictTheoremPackage C) :
    Ideal (Derived.Counterexample.SharedWitnessCoord.ChartRing M.Coeff) :=
  P.readLawIdeal C.commonAmbient.rightLawIdeal

/-- The degree-one LawConflict object computed by the canonical Tor bridge. -/
abbrev lawConflict {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    {C : AATGAGACommonFiniteData M} (P : SelectedDerivedConflictTheoremPackage C) :=
  (Derived.Intersection.canonicalSelectedTorBridge
    (Derived.Counterexample.SharedWitnessCoord.ChartRing M.Coeff)
    P.leftIdeal P.rightIdeal).LawConflict 1

/-- The canonical degree-one LawConflict/Mathlib Tor equivalence. -/
noncomputable def lawConflictLinearEquivMathlibTor {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    {C : AATGAGACommonFiniteData M} (P : SelectedDerivedConflictTheoremPackage C) :
    P.lawConflict ≃ₗ[Derived.Counterexample.SharedWitnessCoord.ChartRing M.Coeff]
      Derived.Intersection.mathlibTor
        (Derived.Counterexample.SharedWitnessCoord.ChartRing M.Coeff)
        P.leftIdeal P.rightIdeal 1 :=
  (Derived.Intersection.canonicalSelectedTorBridge
    (Derived.Counterexample.SharedWitnessCoord.ChartRing M.Coeff)
    P.leftIdeal P.rightIdeal).lawConflictLinearEquivMathlibTor 1

/-- The selected LawConflict has the canonical Tor reading. -/
theorem lawConflictTorReading_holds {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    {C : AATGAGACommonFiniteData M} (P : SelectedDerivedConflictTheoremPackage C) :
    Nonempty
      (P.lawConflict ≃ₗ[Derived.Counterexample.SharedWitnessCoord.ChartRing M.Coeff]
        Derived.Intersection.mathlibTor
          (Derived.Counterexample.SharedWitnessCoord.ChartRing M.Coeff)
          P.leftIdeal P.rightIdeal 1) :=
  ⟨P.lawConflictLinearEquivMathlibTor⟩

/-- Monomial Hilbert-series accounting over the profile coefficient ring. -/
def profileCoefficientHilbertIdentity (M : MeasurementProfile.{u, v}) [Field M.Coeff] : Prop :=
  let G := FiniteModel.DerivedPart5.sharedWitnessG5IdentityPackage M.Coeff
  G.regime.quotientUHilbertSeries * G.regime.quotientVHilbertSeries =
    G.regime.ambientHilbertSeries * G.conflictAlternatingSum

/-- Monomial Hilbert-series accounting over the profile coefficient ring. -/
def hilbertSeriesAccountingStatement {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    {C : AATGAGACommonFiniteData M} (P : SelectedDerivedConflictTheoremPackage C) : Prop :=
  (P.leftIdeal = Derived.Counterexample.SharedWitnessCoord.idealU M.Coeff) ∧
    (P.rightIdeal = Derived.Counterexample.SharedWitnessCoord.idealV M.Coeff) ∧
      profileCoefficientHilbertIdentity M

/-- Derive selected monomial Hilbert-series accounting. -/
theorem hilbertSeriesAccounting_holds {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    {C : AATGAGACommonFiniteData M} (P : SelectedDerivedConflictTheoremPackage C) :
    P.hilbertSeriesAccountingStatement :=
  ⟨P.leftIdeal_eq, P.rightIdeal_eq, by
    simpa [profileCoefficientHilbertIdentity] using
      (FiniteModel.DerivedPart5.sharedWitnessG5IdentityPackage M.Coeff).denominatorClearedIdentity⟩

end SelectedDerivedConflictTheoremPackage

/-- VIII.Theorem 12.3: theorem inputs over one common selected finite datum. -/
structure AATGAGACertifiedFields {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    (C : AATGAGACommonFiniteData M) where
  /-- The selected real reading of the source Čech complex. -/
  hodgeInput : AATGAGARealCechHodgeInput C.finiteCechSource
  /-- Input from which LawConflict/Tor and Hilbert readings are derived. -/
  derivedConflictInput : SelectedDerivedConflictTheoremPackage C

/-- VIII.Principle 12.4: candidate interfaces remain separate from certified results. -/
structure AATGAGACandidateInterfaces (M : MeasurementProfile.{u, v}) where
  MonotoneWitnessStabilityInterface : Type v
  FiniteCechStabilityInterface : Type v
  FlatBaseChangeInterface : Type v
  SpectralHotspotInterface : Type v
  TransferLowerBoundInterface : Type v
  monotoneWitnessStability : Option MonotoneWitnessStabilityInterface
  finiteCechStability : Option FiniteCechStabilityInterface
  flatBaseChange : Option FlatBaseChangeInterface
  spectralHotspot : Option SpectralHotspotInterface
  transferLowerBound : Option TransferLowerBoundInterface

/-- VIII.Principle 12.4: non-conclusion data retained outside the theorem statement. -/
structure AATGAGANonConclusionData (M : MeasurementProfile.{u, v}) where
  noExternalDataSourceFidelity : Prop
  noExternalDataSourceFidelity_cert : noExternalDataSourceFidelity
  noExternalProcedureCorrectness : Prop
  noExternalProcedureCorrectness_cert : noExternalProcedureCorrectness
  noArbitraryLawUniverseComparison : Prop
  noArbitraryLawUniverseComparison_cert : noArbitraryLawUniverseComparison
  candidateDependentFieldsNotCertified : Prop
  candidateDependentFieldsNotCertified_cert : candidateDependentFieldsNotCertified

/-- VIII.Theorem 12.3: data that enter the certified finite comparison. -/
structure AATGAGAComparisonData (M : MeasurementProfile.{u, v}) [Field M.Coeff] where
  commonData : AATGAGACommonFiniteData M
  certifiedFields : AATGAGACertifiedFields commonData

/-- VIII.Theorem 12.3: certified comparison statement. -/
def aatGAGACertifiedComparisonStatement {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    {C : AATGAGACommonFiniteData M} (F : AATGAGACertifiedFields C) : Prop :=
  C.coherent ∧
    F.hodgeInput.hodgeStatement ∧
      F.hodgeInput.periodStokesStatement ∧
        C.finiteCechSource.topologicalCapacityStatement ∧
          Nonempty
            (F.derivedConflictInput.lawConflict ≃ₗ[
                Derived.Counterexample.SharedWitnessCoord.ChartRing M.Coeff]
              Derived.Intersection.mathlibTor
                (Derived.Counterexample.SharedWitnessCoord.ChartRing M.Coeff)
                F.derivedConflictInput.leftIdeal F.derivedConflictInput.rightIdeal 1) ∧
            F.derivedConflictInput.hilbertSeriesAccountingStatement

/-- Derive every certified comparison conjunct from the selected finite data. -/
theorem aatGAGACertifiedComparisonStatement_holds {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    {C : AATGAGACommonFiniteData M} (F : AATGAGACertifiedFields C) :
    aatGAGACertifiedComparisonStatement F :=
  ⟨C.coherent_holds, F.hodgeInput.hodgeStatement_holds,
    F.hodgeInput.periodStokesStatement_holds,
    C.finiteCechSource.topologicalCapacityStatement_holds,
    F.derivedConflictInput.lawConflictTorReading_holds,
    F.derivedConflictInput.hilbertSeriesAccounting_holds⟩

/-- VIII.Theorem 12.3: selected finite-profile comparison statement. -/
def aatGAGAComparisonStatement {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    (D : AATGAGAComparisonData M) : Prop :=
  aatGAGACertifiedComparisonStatement D.certifiedFields

/-- Derive the comparison statement from common finite data. -/
theorem aatGAGAComparisonStatement_holds {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    (D : AATGAGAComparisonData M) : aatGAGAComparisonStatement D :=
  aatGAGACertifiedComparisonStatement_holds D.certifiedFields

/-- VIII.Theorem 12.3 acceptance statement. -/
abbrev AATGAGAFiniteMeasurementComparison {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    (D : AATGAGAComparisonData M) : Prop :=
  aatGAGAComparisonStatement D

/-- The certified finite comparison is derived from its selected inputs. -/
theorem aatGAGAFiniteMeasurementComparison {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    (D : AATGAGAComparisonData M) : AATGAGAFiniteMeasurementComparison D :=
  aatGAGAComparisonStatement_holds D

end Measurement
end AAT.AG
