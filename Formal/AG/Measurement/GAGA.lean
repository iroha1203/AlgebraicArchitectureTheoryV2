import Formal.AG.Cohomology.PeriodStokes
import Formal.AG.Examples.DerivedPart5
import Formal.AG.Measurement.Computability
import Formal.AG.Measurement.FiniteRegime
import Formal.AG.Measurement.Packet

noncomputable section

namespace AAT.AG
namespace Measurement

universe u v

open AlgebraicGeometry

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

/-- Degree-one cocycles of the generated canonical Čech complex. -/
noncomputable def canonicalCocycles {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    (S : AATGAGAFiniteCechSource M) : by
  letI := S.geometry.cochainAddCommGroup 1
  letI := S.geometry.cochainAddCommGroup 2
  exact AddSubgroup (S.geometry.CechCochain 1) := by
  letI := S.geometry.cochainAddCommGroup 1
  letI := S.geometry.cochainAddCommGroup 2
  exact (S.geometry.differentialHom 1).ker

/-- The actual degree-zero canonical Čech differential, restricted to cocycles. -/
noncomputable def canonicalBoundaryToCycles {M : MeasurementProfile.{u, v}}
    [Field M.Coeff] (S : AATGAGAFiniteCechSource M) : by
  letI := S.geometry.cochainAddCommGroup 0
  letI := S.geometry.cochainAddCommGroup 1
  letI := S.geometry.cochainAddCommGroup 2
  exact S.geometry.CechCochain 0 →+ S.canonicalCocycles := by
  letI := S.geometry.cochainAddCommGroup 0
  letI := S.geometry.cochainAddCommGroup 1
  letI := S.geometry.cochainAddCommGroup 2
  exact {
    toFun := fun c => ⟨S.geometry.differentialHom 0 c, by
      change S.geometry.differentialHom 1 (S.geometry.differentialHom 0 c) = 0
      simpa [FiniteMeasurementGeometry.differentialHom,
        FiniteMeasurementGeometry.cechComplex] using
        Cohomology.StandardFinitePosetCech.canonicalTupleStandardFinitePosetCechComplex_differential_comp
          S.geometry.tupleGeometry S.geometry.obstructionSheaf 0 c⟩
    map_zero' := by
      apply Subtype.ext
      exact (S.geometry.differentialHom 0).map_zero
    map_add' := by
      intro x y
      apply Subtype.ext
      exact (S.geometry.differentialHom 0).map_add x y }

/-- The generated canonical Čech `H¹ = ker d¹ / im d⁰`. -/
noncomputable def canonicalH1 {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    (S : AATGAGAFiniteCechSource M) : Type u := by
  letI := S.geometry.cochainAddCommGroup 0
  letI := S.geometry.cochainAddCommGroup 1
  letI := S.geometry.cochainAddCommGroup 2
  exact S.canonicalCocycles ⧸ S.canonicalBoundaryToCycles.range

/-- Additive group structure on the generated canonical Čech quotient. -/
noncomputable instance canonicalH1AddCommGroup {M : MeasurementProfile.{u, v}}
    [Field M.Coeff] (S : AATGAGAFiniteCechSource M) : AddCommGroup S.canonicalH1 := by
  dsimp [canonicalH1]
  infer_instance

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
  /-- Additive coordinate identifications for the selected canonical Čech complex. -/
  zeroToReal : S.nerveComplex.C0 ≃+ RealC0
  /-- Additive coordinate identification in the selected degree one. -/
  oneToReal : S.nerveComplex.C1 ≃+ RealC1
  /-- Additive coordinate identification in the selected degree two. -/
  twoToReal : S.nerveComplex.C2 ≃+ RealC2
  /-- Real nerve coordinates on the selected charts. -/
  zeroCochainCoordinates : RealC0 → (S.nerve.Chart → ℝ)
  /-- Inverse of the selected chart coordinates. -/
  zeroCochainCoordinates_inv : (S.nerve.Chart → ℝ) → RealC0
  zeroCochainCoordinates_left_inv : ∀ c,
    zeroCochainCoordinates_inv (zeroCochainCoordinates c) = c
  zeroCochainCoordinates_right_inv : ∀ c,
    zeroCochainCoordinates (zeroCochainCoordinates_inv c) = c
  zeroCochainCoordinates_add : ∀ c d,
    zeroCochainCoordinates (c + d) = zeroCochainCoordinates c + zeroCochainCoordinates d
  /-- Real nerve coordinates on the selected overlaps. -/
  oneCochainCoordinates : RealC1 → (S.nerve.EdgeComponent → ℝ)
  /-- Inverse of the selected overlap coordinates. -/
  oneCochainCoordinates_inv : (S.nerve.EdgeComponent → ℝ) → RealC1
  oneCochainCoordinates_left_inv : ∀ c,
    oneCochainCoordinates_inv (oneCochainCoordinates c) = c
  oneCochainCoordinates_right_inv : ∀ c,
    oneCochainCoordinates (oneCochainCoordinates_inv c) = c
  oneCochainCoordinates_add : ∀ c d,
    oneCochainCoordinates (c + d) = oneCochainCoordinates c + oneCochainCoordinates d
  /-- Real nerve coordinates on the selected triple overlaps. -/
  twoCochainCoordinates : RealC2 → (S.nerve.FaceComponent → ℝ)
  /-- Inverse of the selected triple-overlap coordinates. -/
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

/-- The generated canonical Čech quotient compares additively with the selected
nerve quotient by the source cochain maps and the two canonical differential
equalities.  No cohomology equivalence is accepted as an input. -/
private theorem canonicalH1AddEquivNerveH1 {M : MeasurementProfile.{u, v}}
    [Field M.Coeff] (S : AATGAGAFiniteCechSource M) :
    Nonempty (S.canonicalH1 ≃+ S.nerveComplex.H1) := by
  letI := S.geometry.cochainAddCommGroup 0
  letI := S.geometry.cochainAddCommGroup 1
  letI := S.geometry.cochainAddCommGroup 2
  let eCycles : S.canonicalCocycles ≃+ S.nerveComplex.d1.ker := {
    toFun := fun x => ⟨S.oneToCanonical.symm x.val, by
      apply S.twoToCanonical.injective
      rw [S.d1_toCanonical, S.oneToCanonical.apply_symm_apply,
        S.twoToCanonical.map_zero]
      change S.geometry.differentialHom 1 x.val = 0
      exact x.property⟩
    invFun := fun y => ⟨S.oneToCanonical y.val, by
      change S.geometry.cechComplex.differential 1 (S.oneToCanonical y.val) = 0
      rw [← S.d1_toCanonical, y.property, S.twoToCanonical.map_zero]⟩
    left_inv := by
      rintro ⟨x, hx⟩
      apply Subtype.ext
      exact S.oneToCanonical.apply_symm_apply x
    right_inv := by
      rintro ⟨y, hy⟩
      apply Subtype.ext
      exact S.oneToCanonical.symm_apply_apply y
    map_add' := by
      rintro ⟨x, hx⟩ ⟨y, hy⟩
      apply Subtype.ext
      exact S.oneToCanonical.symm.map_add x y }
  let eCyclesInv : S.nerveComplex.d1.ker ≃+ S.canonicalCocycles := eCycles.symm
  let qA : AddSubgroup S.canonicalCocycles := S.canonicalBoundaryToCycles.range
  let qD : AddSubgroup S.nerveComplex.d1.ker :=
    S.nerveComplex.boundaryToCycles.range.toAddSubgroup
  letI : qA.Normal := AddSubgroup.normal_of_comm qA
  letI : qD.Normal := AddSubgroup.normal_of_comm qD
  letI : AddCommGroup (S.canonicalCocycles ⧸ qA) :=
    QuotientAddGroup.Quotient.addCommGroup qA
  letI : AddCommGroup (S.nerveComplex.d1.ker ⧸ qD) :=
    QuotientAddGroup.Quotient.addCommGroup qD
  have h_forward_image : ∀ x, x ∈ qA → eCycles x ∈ qD := by
    rintro x ⟨c, rfl⟩
    refine ⟨S.zeroToCanonical.symm c, ?_⟩
    apply Subtype.ext
    apply S.oneToCanonical.injective
    dsimp [eCycles, AATGAGAFiniteCechSource.canonicalBoundaryToCycles,
      Cohomology.FiniteNerveCochainComplex.boundaryToCycles]
    rw [S.oneToCanonical.apply_symm_apply]
    change S.oneToCanonical (S.nerveComplex.d0 (S.zeroToCanonical.symm c)) =
      S.geometry.differentialHom 0 c
    rw [S.d0_toCanonical, S.zeroToCanonical.apply_symm_apply]
    rfl
  have h_backward_image : ∀ x, x ∈ qD → eCyclesInv x ∈ qA := by
    rintro x ⟨c, rfl⟩
    refine ⟨S.zeroToCanonical c, ?_⟩
    apply Subtype.ext
    dsimp [eCyclesInv, eCycles, AATGAGAFiniteCechSource.canonicalBoundaryToCycles,
      Cohomology.FiniteNerveCochainComplex.boundaryToCycles]
    change S.geometry.differentialHom 0 (S.zeroToCanonical c) =
      S.oneToCanonical (S.nerveComplex.d0 c)
    simpa [FiniteMeasurementGeometry.differentialHom] using (S.d0_toCanonical c).symm
  let forward : (S.canonicalCocycles ⧸ qA) →+
      (S.nerveComplex.d1.ker ⧸ qD) :=
    QuotientAddGroup.lift qA ((QuotientAddGroup.mk' qD).comp eCycles.toAddMonoidHom) (by
      intro x hx
      exact (QuotientAddGroup.eq_zero_iff (eCycles x)).mpr (h_forward_image x hx))
  let backward : (S.nerveComplex.d1.ker ⧸ qD) →+
      (S.canonicalCocycles ⧸ qA) :=
    QuotientAddGroup.lift qD ((QuotientAddGroup.mk' qA).comp eCyclesInv.toAddMonoidHom) (by
      intro x hx
      exact (QuotientAddGroup.eq_zero_iff (eCyclesInv x)).mpr (h_backward_image x hx))
  change Nonempty ((S.canonicalCocycles ⧸ qA) ≃+
    (S.nerveComplex.d1.ker ⧸ qD))
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
  exact (∀ c, H.realFiniteComplex.exactPart c + H.realFiniteComplex.harmonicPart c +
    H.realFiniteComplex.coexactPart c = c) ∧
      Nonempty (S.canonicalH1 ≃+ H.realFiniteComplex.laplacian.ker)

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
  rcases canonicalH1AddEquivNerveH1 S with ⟨canonicalToNerve⟩
  rcases sourceH1AddEquivOfCochainComparison S.nerveComplex H.realNerveComplex
    H.zeroToReal H.oneToReal H.twoToReal H.realD0_eq_profile H.realD1_eq_profile with ⟨nerveToReal⟩
  exact ⟨H.realFiniteComplex.hodge_decomposition,
    ⟨canonicalToNerve.trans
      (nerveToReal.trans H.h1LinearEquivLaplacianKernel.toAddEquiv)⟩⟩

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

/--
VIII.Theorem 8.5 / 12.3: an all-degree real realization of the generated
finite Čech complex.

The first three degrees are also used by `AATGAGARealCechHodgeInput` for the
explicit source `H¹` comparison.  This separate all-degree input prevents the
GAGA package from reading the Hodge theorem only in degree one: every real
differential is transported from the same generated Čech differential.
-/
structure AATGAGAAllDegreeRealCechHodgeInput {M : MeasurementProfile.{u, v}}
    [Field M.Coeff] (S : AATGAGAFiniteCechSource M) where
  /-- Real cochains in every degree of the selected Čech realization. -/
  RealCochain : Nat -> Type v
  /-- Each real cochain carrier is a finite-dimensional inner-product space. -/
  [cochainNormed : (n : Nat) -> NormedAddCommGroup (RealCochain n)]
  [cochainInner : (n : Nat) -> InnerProductSpace ℝ (RealCochain n)]
  [cochainFinite : (n : Nat) -> FiniteDimensional ℝ (RealCochain n)]
  /-- Additive realization of every generated canonical Čech cochain carrier. -/
  sourceToReal : (n : Nat) -> S.geometry.CechCochain n ≃+ RealCochain n
  /-- The real differential in every selected degree. -/
  realD : (n : Nat) -> RealCochain n →ₗ[ℝ] RealCochain (n + 1)
  /-- Every real differential is the transported generated Čech differential. -/
  realD_eq_source : ∀ (n : Nat) (c : S.geometry.CechCochain n),
    realD n (sourceToReal n c) =
      sourceToReal (n + 1) (S.geometry.differentialLinear n c)
  /-- The transported real maps form the selected cochain complex. -/
  real_d_comp : ∀ n, (realD (n + 1)).comp (realD n) = 0

attribute [instance] AATGAGAAllDegreeRealCechHodgeInput.cochainNormed
attribute [instance] AATGAGAAllDegreeRealCechHodgeInput.cochainInner
attribute [instance] AATGAGAAllDegreeRealCechHodgeInput.cochainFinite

namespace AATGAGAAllDegreeRealCechHodgeInput

/-- The degree-zero Hodge complex has zero incoming differential. -/
noncomputable def degreeZeroComplex {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    {S : AATGAGAFiniteCechSource M} (H : AATGAGAAllDegreeRealCechHodgeInput S) :
    RealFiniteInnerProductComplex (H.RealCochain 0) (H.RealCochain 0)
      (H.RealCochain 1) where
  dPrev := 0
  dNext := H.realD 0
  d_comp_d := by simp

/-- The degree `n + 1` Hodge complex uses two consecutive generated Čech maps. -/
noncomputable def successorComplex {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    {S : AATGAGAFiniteCechSource M} (H : AATGAGAAllDegreeRealCechHodgeInput S)
    (n : Nat) :
    RealFiniteInnerProductComplex (H.RealCochain n) (H.RealCochain (n + 1))
      (H.RealCochain (n + 2)) where
  dPrev := H.realD n
  dNext := H.realD (n + 1)
  d_comp_d := H.real_d_comp n

/-- Every generated source cocycle is transported to the kernel of the same
selected real Čech differential. -/
noncomputable def sourceCocycleEquivRealCycles
    {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    {S : AATGAGAFiniteCechSource M} (H : AATGAGAAllDegreeRealCechHodgeInput S)
    (n : Nat) : S.geometry.CechCocycle n ≃ (H.realD n).ker := by
  letI := S.geometry.cochainAddCommGroup n
  letI := S.geometry.cochainAddCommGroup (n + 1)
  exact {
    toFun := fun x => ⟨H.sourceToReal n x.1, by
      change H.realD n (H.sourceToReal n x.1) = 0
      rw [H.realD_eq_source]
      change H.sourceToReal (n + 1)
        (S.geometry.cechComplex.differential n x.1) = 0
      have hzero :
          Site.FinitePosetCechZeroCochain S.geometry.cechComplex.additive (n + 1) =
            (0 : S.geometry.CechCochain (n + 1)) := by
        funext simplex
        rfl
      rw [x.2, hzero]
      exact (H.sourceToReal (n + 1)).map_zero
    ⟩
    invFun := fun y => ⟨(H.sourceToReal n).symm y.1, by
      have hzero :
          Site.FinitePosetCechZeroCochain S.geometry.cechComplex.additive (n + 1) =
            (0 : S.geometry.CechCochain (n + 1)) := by
        funext simplex
        rfl
      apply (H.sourceToReal (n + 1)).injective
      have hy : H.realD n (H.sourceToReal n ((H.sourceToReal n).symm y.1)) = 0 := by
        simp only [AddEquiv.apply_symm_apply]
        exact y.2
      rw [H.realD_eq_source] at hy
      simpa [FiniteMeasurementGeometry.differentialLinear, hzero] using hy
    ⟩
    left_inv := by
      rintro ⟨x, hx⟩
      apply Subtype.ext
      exact (H.sourceToReal n).symm_apply_apply x
    right_inv := by
      rintro ⟨y, hy⟩
      apply Subtype.ext
      exact (H.sourceToReal n).apply_symm_apply y
  }

/-- The degree-zero generated Čech quotient is the degree-zero real Hodge
cohomology quotient, constructed from the source cochain transport. -/
noncomputable def sourceH0EquivRealCohomology
    {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    {S : AATGAGAFiniteCechSource M} (H : AATGAGAAllDegreeRealCechHodgeInput S) :
    S.geometry.CechHn 0 ≃ H.degreeZeroComplex.cohomology := by
  let eCycles := H.sourceCocycleEquivRealCycles 0
  exact @Quotient.congr _ _
    (Site.FinitePosetCechCoboundarySetoid (S.geometry.coboundaryRelation 0))
    (Submodule.quotientRel H.degreeZeroComplex.boundariesInCycles)
    eCycles (by
      intro x y
      change x = y ↔
        (Submodule.quotientRel H.degreeZeroComplex.boundariesInCycles).r
          (eCycles x) (eCycles y)
      constructor
      · intro h
        subst y
        rw [Submodule.quotientRel_def]
        simp only [sub_self]
        exact H.degreeZeroComplex.boundariesInCycles.zero_mem
      · intro h
        rw [Submodule.quotientRel_def] at h
        have hzero : eCycles x - eCycles y = 0 := by
          simpa [degreeZeroComplex, RealFiniteInnerProductComplex.boundariesInCycles] using h
        apply eCycles.injective
        exact sub_eq_zero.mp hzero)

/-- Every positive-degree generated Čech quotient is the corresponding real
Hodge cohomology quotient.  The proof descends the transported differential
to the actual source coboundary relation. -/
noncomputable def sourceHsuccEquivRealCohomology
    {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    {S : AATGAGAFiniteCechSource M} (H : AATGAGAAllDegreeRealCechHodgeInput S)
    (n : Nat) : S.geometry.CechHn (n + 1) ≃ (H.successorComplex n).cohomology := by
  let eCycles := H.sourceCocycleEquivRealCycles (n + 1)
  exact @Quotient.congr _ _
    (Site.FinitePosetCechCoboundarySetoid (S.geometry.coboundaryRelation (n + 1)))
    (Submodule.quotientRel (H.successorComplex n).boundariesInCycles)
    eCycles (by
      intro x y
      change (∃ b : S.geometry.CechCochain n,
        x.1 - y.1 = S.geometry.differentialHom n b) ↔
          (Submodule.quotientRel (H.successorComplex n).boundariesInCycles).r
            (eCycles x) (eCycles y)
      constructor
      · rintro ⟨b, hb⟩
        rw [Submodule.quotientRel_def]
        refine ⟨H.sourceToReal n b, ?_⟩
        change H.realD n (H.sourceToReal n b) =
          (eCycles x - eCycles y).1
        rw [H.realD_eq_source]
        change H.sourceToReal (n + 1)
          (S.geometry.cechComplex.differential n b) = _
        have hdiff : S.geometry.cechComplex.differential n b = x.1 - y.1 := by
          simpa [FiniteMeasurementGeometry.differentialHom] using hb.symm
        rw [hdiff]
        change H.sourceToReal (n + 1) (x.1 - y.1) =
          H.sourceToReal (n + 1) x.1 - H.sourceToReal (n + 1) y.1
        exact (H.sourceToReal (n + 1)).map_sub x.1 y.1
      · intro h
        rw [Submodule.quotientRel_def] at h
        rcases h with ⟨c, hc⟩
        refine ⟨(H.sourceToReal n).symm c, ?_⟩
        apply (H.sourceToReal (n + 1)).injective
        rw [(H.sourceToReal (n + 1)).map_sub]
        change (eCycles x - eCycles y).1 = H.sourceToReal (n + 1)
          (S.geometry.differentialHom n ((H.sourceToReal n).symm c))
        have hreal : H.realD n c = H.sourceToReal (n + 1)
            (S.geometry.differentialHom n ((H.sourceToReal n).symm c)) := by
          simpa [FiniteMeasurementGeometry.differentialLinear] using
            (H.realD_eq_source n ((H.sourceToReal n).symm c))
        rw [← hreal]
        exact hc.symm)

/-- The source degree-zero Čech cohomology is identified with the degree-zero
harmonic kernel of the transported finite Hodge complex. -/
noncomputable def sourceH0EquivLaplacianKernel
    {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    {S : AATGAGAFiniteCechSource M} (H : AATGAGAAllDegreeRealCechHodgeInput S) :
    S.geometry.CechHn 0 ≃ H.degreeZeroComplex.laplacian.ker :=
  H.sourceH0EquivRealCohomology.trans
    H.degreeZeroComplex.laplacianKernelEquivCohomology.symm.toEquiv

/-- The source positive-degree Čech cohomology is identified with the
harmonic kernel in the same degree. -/
noncomputable def sourceHsuccEquivLaplacianKernel
    {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    {S : AATGAGAFiniteCechSource M} (H : AATGAGAAllDegreeRealCechHodgeInput S)
    (n : Nat) : S.geometry.CechHn (n + 1) ≃ (H.successorComplex n).laplacian.ker :=
  (H.sourceHsuccEquivRealCohomology n).trans
    (H.successorComplex n).laplacianKernelEquivCohomology.symm.toEquiv

/-- The generated degree-one cocycle subgroup is transported additively onto
the cycle submodule of the same selected real complex. -/
noncomputable def canonicalCocyclesAddEquivRealCycles
    {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    {S : AATGAGAFiniteCechSource M} (H : AATGAGAAllDegreeRealCechHodgeInput S) :
    S.canonicalCocycles ≃+ (H.successorComplex 0).cycles := by
  letI := S.geometry.cochainAddCommGroup 0
  letI := S.geometry.cochainAddCommGroup 1
  letI := S.geometry.cochainAddCommGroup 2
  exact {
    toFun := fun x => ⟨H.sourceToReal 1 x.1, by
      change H.realD 1 (H.sourceToReal 1 x.1) = 0
      rw [H.realD_eq_source]
      have hx : S.geometry.differentialLinear 1 x.1 = 0 := x.2
      rw [hx]
      exact (H.sourceToReal 2).map_zero⟩
    invFun := fun y => ⟨(H.sourceToReal 1).symm y.1, by
      change S.geometry.differentialHom 1 ((H.sourceToReal 1).symm y.1) = 0
      apply (H.sourceToReal 2).injective
      rw [(H.sourceToReal 2).map_zero]
      have hy : H.realD 1 (H.sourceToReal 1 ((H.sourceToReal 1).symm y.1)) = 0 := by
        simp only [AddEquiv.apply_symm_apply]
        exact y.2
      rw [H.realD_eq_source] at hy
      simpa [FiniteMeasurementGeometry.differentialLinear,
        FiniteMeasurementGeometry.differentialHom] using hy⟩
    left_inv := by
      rintro ⟨x, hx⟩
      apply Subtype.ext
      exact (H.sourceToReal 1).symm_apply_apply x
    right_inv := by
      rintro ⟨y, hy⟩
      apply Subtype.ext
      exact (H.sourceToReal 1).apply_symm_apply y
    map_add' := by
      rintro ⟨x, hx⟩ ⟨y, hy⟩
      apply Subtype.ext
      exact (H.sourceToReal 1).map_add x y }

/-- The transported degree-one cocycle identification carries the generated
boundary subgroup onto the boundary submodule of the same real complex. -/
theorem canonicalBoundaries_map_eq
    {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    {S : AATGAGAFiniteCechSource M} (H : AATGAGAAllDegreeRealCechHodgeInput S) : by
    letI := S.geometry.cochainAddCommGroup 0
    letI := S.geometry.cochainAddCommGroup 1
    letI := S.geometry.cochainAddCommGroup 2
    exact S.canonicalBoundaryToCycles.range.map
        H.canonicalCocyclesAddEquivRealCycles.toAddMonoidHom =
      (H.successorComplex 0).boundariesInCycles.toAddSubgroup := by
  letI := S.geometry.cochainAddCommGroup 0
  letI := S.geometry.cochainAddCommGroup 1
  letI := S.geometry.cochainAddCommGroup 2
  ext z
  constructor
  · rintro ⟨x, ⟨c, hc⟩, hz⟩
    refine ⟨H.sourceToReal 0 c, ?_⟩
    change H.realD 0 (H.sourceToReal 0 c) = (z : (H.successorComplex 0).cycles).1
    rw [H.realD_eq_source]
    rw [← hz, ← hc]
    change H.sourceToReal 1 (S.geometry.differentialLinear 0 c) =
      H.sourceToReal 1 (S.geometry.differentialHom 0 c)
    simp [FiniteMeasurementGeometry.differentialLinear,
      FiniteMeasurementGeometry.differentialHom]
  · rintro ⟨w, hw⟩
    refine ⟨H.canonicalCocyclesAddEquivRealCycles.symm z,
      ⟨(H.sourceToReal 0).symm w, ?_⟩,
      H.canonicalCocyclesAddEquivRealCycles.apply_symm_apply z⟩
    apply Subtype.ext
    apply (H.sourceToReal 1).injective
    have hd : H.realD 0 (H.sourceToReal 0 ((H.sourceToReal 0).symm w)) =
        H.sourceToReal 1
          (S.geometry.differentialLinear 0 ((H.sourceToReal 0).symm w)) :=
      H.realD_eq_source 0 ((H.sourceToReal 0).symm w)
    rw [(H.sourceToReal 0).apply_symm_apply] at hd
    have hw' : H.realD 0 w = (z : H.RealCochain 1) := hw
    have step1 : H.sourceToReal 1
        ((S.canonicalBoundaryToCycles ((H.sourceToReal 0).symm w) :
          S.canonicalCocycles) : S.geometry.CechCochain 1) = H.realD 0 w :=
      hd.symm
    have step2 : H.realD 0 w =
        H.sourceToReal 1
          ((H.canonicalCocyclesAddEquivRealCycles.symm z :
            S.canonicalCocycles) : S.geometry.CechCochain 1) := by
      rw [hw']
      exact ((H.sourceToReal 1).apply_symm_apply _).symm
    exact step1.trans step2

/-- The transported degree-one cocycle identification descends to the quotient
cohomology of the same selected real complex. -/
noncomputable def canonicalH1AddEquivCohomology
    {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    {S : AATGAGAFiniteCechSource M} (H : AATGAGAAllDegreeRealCechHodgeInput S) :
    S.canonicalH1 ≃+ (H.successorComplex 0).cohomology := by
  letI := S.geometry.cochainAddCommGroup 0
  letI := S.geometry.cochainAddCommGroup 1
  letI := S.geometry.cochainAddCommGroup 2
  exact QuotientAddGroup.congr S.canonicalBoundaryToCycles.range
    (H.successorComplex 0).boundariesInCycles.toAddSubgroup
    H.canonicalCocyclesAddEquivRealCycles H.canonicalBoundaries_map_eq

/-- The generated canonical Čech `H¹` is additively identified with the
degree-one harmonic kernel of the same transported complex. -/
noncomputable def canonicalH1AddEquivLaplacianKernel
    {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    {S : AATGAGAFiniteCechSource M} (H : AATGAGAAllDegreeRealCechHodgeInput S) :
    S.canonicalH1 ≃+ (H.successorComplex 0).laplacian.ker :=
  H.canonicalH1AddEquivCohomology.trans
    (H.successorComplex 0).laplacianKernelEquivCohomology.symm.toAddEquiv

/-- The all-degree Hodge statement identifies every source Čech quotient with
the harmonic kernel formed from its transported differential. -/
def allDegreeHodgeStatement {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    {S : AATGAGAFiniteCechSource M} (H : AATGAGAAllDegreeRealCechHodgeInput S) : Prop :=
  Nonempty (S.geometry.CechHn 0 ≃ H.degreeZeroComplex.laplacian.ker) ∧
    (∀ n, Nonempty
      (S.geometry.CechHn (n + 1) ≃ (H.successorComplex n).laplacian.ker))

end AATGAGAAllDegreeRealCechHodgeInput

namespace RealFiniteInnerProductComplex

/-- An orthogonal Hodge decomposition records the three component ranges,
their pairwise orthogonality, and their sum. -/
def orthogonalHodgeDecompositionStatement
    {Cminus C Cplus : Type v} [NormedAddCommGroup Cminus] [InnerProductSpace ℝ Cminus]
    [FiniteDimensional ℝ Cminus] [NormedAddCommGroup C] [InnerProductSpace ℝ C]
    [FiniteDimensional ℝ C] [NormedAddCommGroup Cplus] [InnerProductSpace ℝ Cplus]
    [FiniteDimensional ℝ Cplus] (K : RealFiniteInnerProductComplex Cminus C Cplus) : Prop :=
  (∀ x, K.exactPart x ∈ K.dPrev.range) ∧
    (∀ x, K.harmonicPart x ∈ K.laplacian.ker) ∧
      (∀ x, K.coexactPart x ∈ K.dNextAdjoint.range) ∧
        (∀ x y, inner ℝ (K.exactPart x) (K.harmonicPart y) = 0) ∧
          (∀ x y, inner ℝ (K.exactPart x) (K.coexactPart y) = 0) ∧
            (∀ x y, inner ℝ (K.harmonicPart x) (K.coexactPart y) = 0) ∧
              (∀ x, K.exactPart x + K.harmonicPart x + K.coexactPart x = x)

/-- The finite-dimensional Hodge construction supplies every item of the
orthogonal exact-harmonic-coexact decomposition. -/
theorem orthogonalHodgeDecompositionStatement_holds
    {Cminus C Cplus : Type v} [NormedAddCommGroup Cminus] [InnerProductSpace ℝ Cminus]
    [FiniteDimensional ℝ Cminus] [NormedAddCommGroup C] [InnerProductSpace ℝ C]
    [FiniteDimensional ℝ C] [NormedAddCommGroup Cplus] [InnerProductSpace ℝ Cplus]
    [FiniteDimensional ℝ Cplus] (K : RealFiniteInnerProductComplex Cminus C Cplus) :
    K.orthogonalHodgeDecompositionStatement :=
  ⟨K.exactPart_mem_range, K.harmonicPart_mem_laplacian_kernel,
    K.coexactPart_mem_adjoint_range, K.exact_harmonic_orthogonal,
    K.exact_coexact_orthogonal, K.harmonic_coexact_orthogonal,
    K.hodge_decomposition⟩

end RealFiniteInnerProductComplex

namespace AATGAGAAllDegreeRealCechHodgeInput

/-- The orthogonal exact-harmonic-coexact decomposition in every selected
Čech degree. -/
def allDegreeDecompositionStatement {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    {S : AATGAGAFiniteCechSource M} (H : AATGAGAAllDegreeRealCechHodgeInput S) : Prop :=
  H.degreeZeroComplex.orthogonalHodgeDecompositionStatement ∧
    (∀ n, (H.successorComplex n).orthogonalHodgeDecompositionStatement)

/-- The standard finite-dimensional Hodge theorem yields every selected degree. -/
theorem allDegreeHodgeStatement_holds {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    {S : AATGAGAFiniteCechSource M} (H : AATGAGAAllDegreeRealCechHodgeInput S) :
    H.allDegreeHodgeStatement := by
  refine ⟨⟨H.sourceH0EquivLaplacianKernel⟩, ?_⟩
  intro n
  exact ⟨H.sourceHsuccEquivLaplacianKernel n⟩

/-- The standard finite-dimensional Hodge decomposition yields every selected degree. -/
theorem allDegreeDecompositionStatement_holds {M : MeasurementProfile.{u, v}}
    [Field M.Coeff] {S : AATGAGAFiniteCechSource M}
    (H : AATGAGAAllDegreeRealCechHodgeInput S) : H.allDegreeDecompositionStatement := by
  exact ⟨H.degreeZeroComplex.orthogonalHodgeDecompositionStatement_holds,
    fun n => (H.successorComplex n).orthogonalHodgeDecompositionStatement_holds⟩

/-- The all-degree source comparison is the supplied transported-differential law. -/
theorem realD_eq_source_holds {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    {S : AATGAGAFiniteCechSource M} (H : AATGAGAAllDegreeRealCechHodgeInput S) :
    ∀ (n : Nat) (c : S.geometry.CechCochain n),
      H.realD n (H.sourceToReal n c) =
        H.sourceToReal (n + 1) (S.geometry.differentialLinear n c) :=
  H.realD_eq_source

end AATGAGAAllDegreeRealCechHodgeInput

/--
Exact computation of a coordinate family whose nonzero values are one fixed
principal generator. The active index is part of the computation data, so
equality of generated ideals is derived rather than supplied.
-/
structure PrincipalCoordinatePresentation
    {R : Type v} [CommRing R]
    {ι : Type u}
    (coordinate : ι → R)
    (generator : R) where
  /-- Computed activity marker for every coordinate. -/
  active : ι → Option Unit
  /-- Every coordinate computes to either zero or the principal generator. -/
  coordinate_eq :
    ∀ i, coordinate i =
      match active i with
      | none => 0
      | some _ => generator
  /-- One computed coordinate realizes the principal generator. -/
  generatorIndex : ι
  generatorIndex_active : active generatorIndex = some ()

namespace PrincipalCoordinatePresentation

/-- The exact coordinate computation generates precisely the principal ideal. -/
theorem span_range_eq_span_singleton
    {R : Type v} [CommRing R]
    {ι : Type u}
    {coordinate : ι → R}
    {generator : R}
    (P : PrincipalCoordinatePresentation coordinate generator) :
    Ideal.span (Set.range coordinate) =
      Ideal.span ({generator} : Set R) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro polynomial ⟨i, rfl⟩
    cases hactive : P.active i with
    | none =>
        rw [P.coordinate_eq i, hactive]
        exact Ideal.zero_mem _
    | some marker =>
        rw [P.coordinate_eq i, hactive]
        exact Ideal.subset_span (by rfl)
  · apply Ideal.span_le.mpr
    intro polynomial hpolynomial
    have hgenerator : polynomial = generator := by
      simpa using hpolynomial
    subst polynomial
    apply Ideal.subset_span
    refine ⟨P.generatorIndex, ?_⟩
    rw [P.coordinate_eq P.generatorIndex, P.generatorIndex_active]

end PrincipalCoordinatePresentation

/-- VIII.Theorem 12.3: finite data shared by every certified comparison. -/
structure AATGAGACommonFiniteData (M : MeasurementProfile.{u, v}) [Field M.Coeff] where
  /-- The generated finite Čech source shared by all four packages. -/
  finiteCechSource : AATGAGAFiniteCechSource M
  /-- The profile coefficient selected for this comparison. -/
  selectedCoefficient : M.Coeff
  /-- The measurement-domain element selected for the comparison. -/
  selectedMeasurement : M.Domain
  /-- Evidence that the selected measurement belongs to the measured profile. -/
  measuredSelection : M.Measured_M selectedMeasurement
  /-- Context at which the actual equation coordinates enter the shared chart. -/
  equationContext : M.equationGeometry.site.category
  /-- Actual observable-ring map used for the selected left equation. -/
  leftEquationObservableMap :
    M.equationGeometry.site.equationSystem.Observable equationContext →+*
      Derived.Counterexample.SharedWitnessCoord.ChartRing M.Coeff
  /-- Actual observable-ring map used for the selected right equation. -/
  rightEquationObservableMap :
    M.equationGeometry.site.equationSystem.Observable equationContext →+*
      Derived.Counterexample.SharedWitnessCoord.ChartRing M.Coeff
  /-- The selected left required equation used in the common chart. -/
  selectedLeftProfileEquation :
    M.equationGeometry.site.equationSystem.RequiredIndex
  /-- The selected right required equation used in the common chart. -/
  selectedRightProfileEquation :
    M.equationGeometry.site.equationSystem.RequiredIndex
  /-- Exact coordinate computation for the selected left equation. -/
  leftCoordinatePresentation :
    PrincipalCoordinatePresentation
      (fun atom =>
        leftEquationObservableMap
          (M.equationGeometry.site.equationSystem.violationCoordinate
            equationContext selectedLeftProfileEquation.1 atom))
      (Derived.Counterexample.SharedWitnessCoord.xy M.Coeff)
  /-- Exact coordinate computation for the selected right equation. -/
  rightCoordinatePresentation :
    PrincipalCoordinatePresentation
      (fun atom =>
        rightEquationObservableMap
          (M.equationGeometry.site.equationSystem.violationCoordinate
            equationContext selectedRightProfileEquation.1 atom))
      (Derived.Counterexample.SharedWitnessCoord.xz M.Coeff)

/-- The Hodge data are a real realization of the generated Čech source. -/
structure AATGAGASelectedFiniteHodgeData {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    (C : AATGAGACommonFiniteData M) where
  /-- The unique all-degree real realization of the common Čech source. -/
  allDegreeInput : AATGAGAAllDegreeRealCechHodgeInput C.finiteCechSource

namespace AATGAGASelectedFiniteHodgeData

/-- The generated canonical Čech `H¹` is additively identified with the
degree-one harmonic kernel of the unique selected real cochain model. -/
def harmonicKernelIdentifiesCohomology {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    {C : AATGAGACommonFiniteData M} (D : AATGAGASelectedFiniteHodgeData C) : Prop :=
  Nonempty
    (C.finiteCechSource.canonicalH1 ≃+
      (D.allDegreeInput.successorComplex 0).laplacian.ker)

/-- The degree-one component of the unique selected model has its orthogonal
exact-harmonic-coexact decomposition. -/
def finiteHodgeDecomposition {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    {C : AATGAGACommonFiniteData M} (D : AATGAGASelectedFiniteHodgeData C) : Prop :=
  (D.allDegreeInput.successorComplex 0).orthogonalHodgeDecompositionStatement

/-- Derive the degree-one source/harmonic identification from the selected
all-degree source transport. -/
theorem harmonicKernelIdentifiesCohomology_holds {M : MeasurementProfile.{u, v}}
    [Field M.Coeff] {C : AATGAGACommonFiniteData M}
    (D : AATGAGASelectedFiniteHodgeData C) : D.harmonicKernelIdentifiesCohomology :=
  ⟨D.allDegreeInput.canonicalH1AddEquivLaplacianKernel⟩

/-- Derive the degree-one orthogonal Hodge decomposition from the unique
selected all-degree model. -/
theorem finiteHodgeDecomposition_holds {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    {C : AATGAGACommonFiniteData M} (D : AATGAGASelectedFiniteHodgeData C) :
    D.finiteHodgeDecomposition :=
  (D.allDegreeInput.successorComplex 0).orthogonalHodgeDecompositionStatement_holds

/-- VIII.Theorem 8.5: every selected Čech degree has a harmonic cohomology reading. -/
def allDegreeHodge {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    {C : AATGAGACommonFiniteData M} (D : AATGAGASelectedFiniteHodgeData C) : Prop :=
  D.allDegreeInput.allDegreeHodgeStatement

/-- VIII.Theorem 8.5: every selected Čech degree has the Hodge decomposition. -/
def allDegreeDecomposition {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    {C : AATGAGACommonFiniteData M} (D : AATGAGASelectedFiniteHodgeData C) : Prop :=
  D.allDegreeInput.allDegreeDecompositionStatement

/-- The all-degree harmonic cohomology reading is derived from the selected source maps. -/
theorem allDegreeHodge_holds {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    {C : AATGAGACommonFiniteData M} (D : AATGAGASelectedFiniteHodgeData C) :
    D.allDegreeHodge :=
  D.allDegreeInput.allDegreeHodgeStatement_holds

/-- The all-degree exact-harmonic-coexact decomposition is derived from the selected maps. -/
theorem allDegreeDecomposition_holds {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    {C : AATGAGACommonFiniteData M} (D : AATGAGASelectedFiniteHodgeData C) :
    D.allDegreeDecomposition :=
  D.allDegreeInput.allDegreeDecompositionStatement_holds

/-- Period/Stokes for degree zero and degree one of the unique selected real
Čech realization.  The chain-side map is the Riesz adjoint of that same
transported source differential. -/
def sourcePeriodStokesStatement {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    {C : AATGAGACommonFiniteData M} (D : AATGAGASelectedFiniteHodgeData C) : Prop :=
  ∀ (omega : D.allDegreeInput.RealCochain 0) (gamma : D.allDegreeInput.RealCochain 1),
    inner ℝ (D.allDegreeInput.realD 0 omega) gamma =
      inner ℝ omega ((D.allDegreeInput.successorComplex 0).dPrev.adjoint gamma)

/-- Derive the selected Period/Stokes formula from the adjoint of the same
degree-zero differential used by the all-degree Hodge complex. -/
theorem sourcePeriodStokesStatement_holds {M : MeasurementProfile.{u, v}}
    [Field M.Coeff] {C : AATGAGACommonFiniteData M}
    (D : AATGAGASelectedFiniteHodgeData C) : D.sourcePeriodStokesStatement := by
  intro omega gamma
  change inner ℝ ((D.allDegreeInput.successorComplex 0).dPrev omega) gamma = _
  simpa using
    ((D.allDegreeInput.successorComplex 0).dPrev.adjoint_inner_right omega gamma).symm

/-- Every Hodge differential is the transported generated Čech differential. -/
theorem allDegreeDifferentialFromSource_holds {M : MeasurementProfile.{u, v}}
    [Field M.Coeff] {C : AATGAGACommonFiniteData M}
    (D : AATGAGASelectedFiniteHodgeData C) :
    ∀ (n : Nat) (c : C.finiteCechSource.geometry.CechCochain n),
      D.allDegreeInput.realD n (D.allDegreeInput.sourceToReal n c) =
        D.allDegreeInput.sourceToReal (n + 1)
          (C.finiteCechSource.geometry.differentialLinear n c) :=
  D.allDegreeInput.realD_eq_source_holds

end AATGAGASelectedFiniteHodgeData

/-- VIII.Theorem 12.3: selected finite Hodge theorem package. -/
structure SelectedFiniteHodgeTheoremPackage {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    (C : AATGAGACommonFiniteData M) where
  /-- Hodge data constructed over the common finite Čech source. -/
  hodgeData : AATGAGASelectedFiniteHodgeData C

/-- VIII.Theorem 12.3: selected Period/Stokes theorem package. -/
structure SelectedPeriodStokesTheoremPackage {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    (C : AATGAGACommonFiniteData M) (H : SelectedFiniteHodgeTheoremPackage C) where
  /-- The Period/Stokes source is identified with the Hodge source of this comparison. -/
  sourceHodgeData : AATGAGASelectedFiniteHodgeData C
  /-- Both analytic readings use the same selected finite Čech realization. -/
  sourceHodgeData_eq : sourceHodgeData = H.hodgeData

namespace SelectedPeriodStokesTheoremPackage

/-- The selected Stokes equality is formed from the actual source `d⁰` and its adjoint. -/
def periodStokesStatement {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    {C : AATGAGACommonFiniteData M} {H : SelectedFiniteHodgeTheoremPackage C}
    (P : SelectedPeriodStokesTheoremPackage C H) : Prop :=
  P.sourceHodgeData.sourcePeriodStokesStatement

/-- Derive Stokes from the same real Čech map used by the Hodge package. -/
theorem periodStokesStatement_holds {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    {C : AATGAGACommonFiniteData M} {H : SelectedFiniteHodgeTheoremPackage C}
    (P : SelectedPeriodStokesTheoremPackage C H) : P.periodStokesStatement := by
  change P.sourceHodgeData.sourcePeriodStokesStatement
  rw [P.sourceHodgeData_eq]
  exact H.hodgeData.sourcePeriodStokesStatement_holds

end SelectedPeriodStokesTheoremPackage

/-- VIII.Theorem 12.3: selected finite-nerve capacity package. -/
structure SelectedTopologicalDebtTheoremPackage {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    (C : AATGAGACommonFiniteData M) where
  /-- The capacity calculation uses a source identified with the common Čech source. -/
  source : AATGAGAFiniteCechSource M
  /-- The capacity source is exactly the source shared by all theorem packages. -/
  source_eq_common : source = C.finiteCechSource

namespace SelectedTopologicalDebtTheoremPackage

/-- The finite-nerve capacity inequality for the package's common Čech source. -/
def topologicalCapacityStatement {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    {C : AATGAGACommonFiniteData M} (P : SelectedTopologicalDebtTheoremPackage C) : Prop :=
  P.source.topologicalCapacityStatement

/-- Derive the package capacity inequality from the common finite nerve. -/
theorem topologicalCapacityStatement_holds {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    {C : AATGAGACommonFiniteData M} (P : SelectedTopologicalDebtTheoremPackage C) :
    P.topologicalCapacityStatement := by
  change P.source.topologicalCapacityStatement
  rw [P.source_eq_common]
  exact C.finiteCechSource.topologicalCapacityStatement_holds

end SelectedTopologicalDebtTheoremPackage

namespace AATGAGACommonFiniteData

/-- The left chart ideal is the image of the selected canonical witness ideal. -/
def leftIdeal {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    (C : AATGAGACommonFiniteData M) :
    Ideal (Derived.Counterexample.SharedWitnessCoord.ChartRing M.Coeff) :=
  profileEquationIdeal M C.equationContext C.leftEquationObservableMap
    C.selectedLeftProfileEquation.1

/-- The right chart ideal is the image of the selected canonical witness ideal. -/
def rightIdeal {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    (C : AATGAGACommonFiniteData M) :
    Ideal (Derived.Counterexample.SharedWitnessCoord.ChartRing M.Coeff) :=
  profileEquationIdeal M C.equationContext C.rightEquationObservableMap
    C.selectedRightProfileEquation.1

/-- Actual mapped equation coordinates derive the selected left principal ideal. -/
theorem leftIdeal_eq_sharedWitness {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    (C : AATGAGACommonFiniteData M) :
    C.leftIdeal = Derived.Counterexample.SharedWitnessCoord.idealU M.Coeff := by
  rw [leftIdeal, profileEquationIdeal_eq_span_range]
  exact C.leftCoordinatePresentation.span_range_eq_span_singleton

/-- Actual mapped equation coordinates derive the selected right principal ideal. -/
theorem rightIdeal_eq_sharedWitness {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    (C : AATGAGACommonFiniteData M) :
    C.rightIdeal = Derived.Counterexample.SharedWitnessCoord.idealV M.Coeff := by
  rw [rightIdeal, profileEquationIdeal_eq_span_range]
  exact C.rightCoordinatePresentation.span_range_eq_span_singleton

/-- Canonical affine common ambient derived from the two actual equation
ideals.  The ambient scheme and both ideal sheaves are generated internally. -/
noncomputable def commonAmbient {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    (C : AATGAGACommonFiniteData M) :
    CommonAmbientPair M where
  AmbientSpace := ULift.{u, 0} Unit
  StructureSheaf :=
    ULift.{max u v + 1, v + 1} AffineIdealSheafPair.{v}
  LawIdeal :=
    ULift.{max u v, v}
      (Ideal (Derived.Counterexample.SharedWitnessCoord.ChartRing M.Coeff))
  CoefficientObject := M.Coeff
  WitnessPair := ULift.{u, 0} Derived.Counterexample.SharedWitnessCoord
  ComparisonProfile :=
    M.equationGeometry.site.equationSystem.RequiredIndex ×
      M.equationGeometry.site.equationSystem.RequiredIndex
  SupportCarrier := M.WitnessVariables
  leftDomain := C.selectedMeasurement
  rightDomain := C.selectedMeasurement
  selectedAmbient := ULift.up ()
  selectedStructureSheaf :=
    ULift.up (AffineIdealSheafPair.ofSpec C.leftIdeal C.rightIdeal)
  leftLawIdeal := ULift.up C.leftIdeal
  rightLawIdeal := ULift.up C.rightIdeal
  leftCoefficient := C.selectedCoefficient
  rightCoefficient := C.selectedCoefficient
  selectedWitnessPair := ULift.up .x
  selectedComparisonProfile :=
    (C.selectedLeftProfileEquation, C.selectedRightProfileEquation)
  commonRingedSite :=
    (AffineIdealSheafPair.ofSpec
      C.leftIdeal C.rightIdeal).scheme.toLocallyRingedSpace =
        AlgebraicGeometry.Spec.locallyRingedSpaceObj
          (CommRingCat.of
            (Derived.Counterexample.SharedWitnessCoord.ChartRing
              M.Coeff))
  commonRingedSite_cert := rfl
  lawIdealsInCommonAmbient :=
    let e :=
      (AlgebraicGeometry.Scheme.ΓSpecIso
        (CommRingCat.of
          (Derived.Counterexample.SharedWitnessCoord.ChartRing
            M.Coeff))).commRingCatIsoToRingEquiv
    let pair := AffineIdealSheafPair.ofSpec C.leftIdeal C.rightIdeal
    let _ : IsAffine pair.scheme := pair.schemeIsAffine
    Ideal.map e.toRingHom
        (pair.leftIdealSheaf.ideal
          ⟨⊤, isAffineOpen_top pair.scheme⟩) =
          C.leftIdeal ∧
      Ideal.map e.toRingHom
        (pair.rightIdealSheaf.ideal
          ⟨⊤, isAffineOpen_top pair.scheme⟩) =
          C.rightIdeal
  lawIdealsInCommonAmbient_cert :=
    ⟨AffineIdealSheafPair.ofSpec_leftIdealSheaf_top
        C.leftIdeal C.rightIdeal,
      AffineIdealSheafPair.ofSpec_rightIdealSheaf_top
        C.leftIdeal C.rightIdeal⟩
  coefficientsCompatible := C.selectedCoefficient = C.selectedCoefficient
  coefficientsCompatible_cert := rfl
  witnessesComparable :=
    (ULift.up .x :
      ULift.{u, 0} Derived.Counterexample.SharedWitnessCoord) =
        ULift.up .x
  witnessesComparable_cert := rfl
  comparisonProfileFixed :=
    (C.selectedLeftProfileEquation, C.selectedRightProfileEquation) =
      (C.selectedLeftProfileEquation, C.selectedRightProfileEquation)
  comparisonProfileFixed_cert := rfl
  noComparisonWithoutCommonAmbient :=
    (AffineIdealSheafPair.ofSpec
      C.leftIdeal C.rightIdeal).scheme.toLocallyRingedSpace =
        AlgebraicGeometry.Spec.locallyRingedSpaceObj
          (CommRingCat.of
            (Derived.Counterexample.SharedWitnessCoord.ChartRing
              M.Coeff))
  noComparisonWithoutCommonAmbient_cert := rfl

/-- The actual affine ideal-sheaf pair carried by the universe-lifted common
ambient field. -/
abbrev ambientIdealSheafPair
    {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    (C : AATGAGACommonFiniteData M) :
    AffineIdealSheafPair.{v} :=
  (show ULift.{max u v + 1, v + 1} AffineIdealSheafPair.{v} from
    C.commonAmbient.selectedStructureSheaf).down

/-- The actual left chart ideal carried by the universe-lifted common ambient
field. -/
abbrev ambientLeftIdeal
    {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    (C : AATGAGACommonFiniteData M) :
    Ideal (Derived.Counterexample.SharedWitnessCoord.ChartRing M.Coeff) :=
  (show ULift.{max u v, v}
      (Ideal (Derived.Counterexample.SharedWitnessCoord.ChartRing M.Coeff)) from
    C.commonAmbient.leftLawIdeal).down

/-- The actual right chart ideal carried by the universe-lifted common ambient
field. -/
abbrev ambientRightIdeal
    {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    (C : AATGAGACommonFiniteData M) :
    Ideal (Derived.Counterexample.SharedWitnessCoord.ChartRing M.Coeff) :=
  (show ULift.{max u v, v}
      (Ideal (Derived.Counterexample.SharedWitnessCoord.ChartRing M.Coeff)) from
    C.commonAmbient.rightLawIdeal).down

/-- The left ideal selected by the common ambient is definitionally the
actual left equation ideal. -/
theorem commonAmbient_leftLawIdeal
    {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    (C : AATGAGACommonFiniteData M) :
    C.ambientLeftIdeal =
        C.leftIdeal :=
  rfl

/-- The right ideal selected by the common ambient is definitionally the
actual right equation ideal. -/
theorem commonAmbient_rightLawIdeal
    {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    (C : AATGAGACommonFiniteData M) :
    C.ambientRightIdeal =
        C.rightIdeal :=
  rfl

/-- Both ideal sheaves live on `Spec` of the shared-witness chart ring. -/
theorem commonAmbient_selectedScheme
    {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    (C : AATGAGACommonFiniteData M) :
    C.ambientIdealSheafPair.scheme =
      AlgebraicGeometry.Scheme.Spec.obj
        (Opposite.op
          (CommRingCat.of
            (Derived.Counterexample.SharedWitnessCoord.ChartRing
              M.Coeff))) :=
  rfl

/-- The selected affine scheme carries Mathlib's ring-valued structure
sheaf. -/
theorem commonAmbient_schemeSheaf
    {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    (C : AATGAGACommonFiniteData M) :
    C.ambientIdealSheafPair.scheme.sheaf =
      AlgebraicGeometry.Spec.structureSheaf
        (CommRingCat.of
          (Derived.Counterexample.SharedWitnessCoord.ChartRing
            M.Coeff)) :=
  rfl

/-- The left selected ideal sheaf is induced from the actual left equation
ideal. -/
theorem commonAmbient_leftIdealSheaf
    {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    (C : AATGAGACommonFiniteData M) :
    C.ambientIdealSheafPair.leftIdealSheaf =
      AlgebraicGeometry.Scheme.IdealSheafData.ofIdealTop
        (Ideal.map
          ((AlgebraicGeometry.Scheme.ΓSpecIso
            (CommRingCat.of
              (Derived.Counterexample.SharedWitnessCoord.ChartRing
                M.Coeff))).commRingCatIsoToRingEquiv).symm.toRingHom
          C.leftIdeal) :=
  rfl

/-- The right selected ideal sheaf is induced from the actual right equation
ideal. -/
theorem commonAmbient_rightIdealSheaf
    {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    (C : AATGAGACommonFiniteData M) :
    C.ambientIdealSheafPair.rightIdealSheaf =
      AlgebraicGeometry.Scheme.IdealSheafData.ofIdealTop
        (Ideal.map
          ((AlgebraicGeometry.Scheme.ΓSpecIso
            (CommRingCat.of
              (Derived.Counterexample.SharedWitnessCoord.ChartRing
                M.Coeff))).commRingCatIsoToRingEquiv).symm.toRingHom
          C.rightIdeal) :=
  rfl

/-- The two ideal-sheaf top components recover exactly the equation ideals
used by the selected Tor bridge. -/
theorem commonAmbient_globalSectionsIdeals
    {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    (C : AATGAGACommonFiniteData M) :
    let e :=
      (AlgebraicGeometry.Scheme.ΓSpecIso
        (CommRingCat.of
          (Derived.Counterexample.SharedWitnessCoord.ChartRing
            M.Coeff))).commRingCatIsoToRingEquiv
    let pair := C.ambientIdealSheafPair
    let _ : IsAffine pair.scheme := pair.schemeIsAffine
    Ideal.map e.toRingHom
        (pair.leftIdealSheaf.ideal
          ⟨⊤, isAffineOpen_top pair.scheme⟩) =
          C.leftIdeal ∧
      Ideal.map e.toRingHom
        (pair.rightIdealSheaf.ideal
          ⟨⊤, isAffineOpen_top pair.scheme⟩) =
          C.rightIdeal :=
  C.commonAmbient.lawIdealsInCommonAmbient_cert

/-- The ambient-selected ideals are the two canonical shared-witness
principal ideals. -/
theorem commonAmbient_ideals_eq_sharedWitness
    {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    (C : AATGAGACommonFiniteData M) :
    C.ambientLeftIdeal =
        Derived.Counterexample.SharedWitnessCoord.idealU M.Coeff ∧
      C.ambientRightIdeal =
          Derived.Counterexample.SharedWitnessCoord.idealV M.Coeff :=
  ⟨C.commonAmbient_leftLawIdeal.trans C.leftIdeal_eq_sharedWitness,
    C.commonAmbient_rightLawIdeal.trans C.rightIdeal_eq_sharedWitness⟩

/-- The degree-one LawConflict object of the canonical selected Tor bridge. -/
abbrev lawConflict {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    (C : AATGAGACommonFiniteData M) :=
  (Derived.Intersection.canonicalSelectedTorBridge
    (Derived.Counterexample.SharedWitnessCoord.ChartRing M.Coeff)
    C.ambientLeftIdeal C.ambientRightIdeal).LawConflict 1

/-- The canonical degree-one LawConflict/Mathlib Tor linear equivalence. -/
noncomputable def lawConflictLinearEquivMathlibTor {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    (C : AATGAGACommonFiniteData M) :
    C.lawConflict ≃ₗ[Derived.Counterexample.SharedWitnessCoord.ChartRing M.Coeff]
      Derived.Intersection.mathlibTor
        (Derived.Counterexample.SharedWitnessCoord.ChartRing M.Coeff)
        C.ambientLeftIdeal C.ambientRightIdeal 1 :=
  (Derived.Intersection.canonicalSelectedTorBridge
    (Derived.Counterexample.SharedWitnessCoord.ChartRing M.Coeff)
    C.ambientLeftIdeal
    C.ambientRightIdeal).lawConflictLinearEquivMathlibTor 1

/-- Derive the selected LawConflict/Tor reading from its canonical bridge. -/
theorem lawConflictTorReading_holds {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    (C : AATGAGACommonFiniteData M) :
    Nonempty
      (C.lawConflict ≃ₗ[Derived.Counterexample.SharedWitnessCoord.ChartRing M.Coeff]
        Derived.Intersection.mathlibTor
          (Derived.Counterexample.SharedWitnessCoord.ChartRing M.Coeff)
          C.ambientLeftIdeal C.ambientRightIdeal 1) :=
  ⟨C.lawConflictLinearEquivMathlibTor⟩

/-- The generated ideals are the shared-witness ideals and satisfy the fixed
G5 Hilbert-series identity of the selected regime.

The series are the declared coefficients of `sharedWitnessHilbertRegime`;
identifying them with graded dimensions of the actual `mathlibTor` modules is
Part V Theorem 12.2 provenance work tracked as Issue #3726, not a conjunct of
this statement. -/
def hilbertSeriesConflictStatement {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    (C : AATGAGACommonFiniteData M) : Prop :=
  let regime := FiniteModel.DerivedPart5.sharedWitnessHilbertRegime M.Coeff
  C.leftIdeal = regime.I_U ∧
    C.rightIdeal = regime.I_V ∧
      regime.quotientUHilbertSeries * regime.quotientVHilbertSeries =
        regime.ambientHilbertSeries *
          (regime.lawConflictHilbertSeries 0 - regime.lawConflictHilbertSeries 1)

/-- Derive the all-degree Hilbert-series accounting from the generated law ideals. -/
theorem hilbertSeriesConflictStatement_holds {M : MeasurementProfile.{u, v}}
    [Field M.Coeff] (C : AATGAGACommonFiniteData M) : C.hilbertSeriesConflictStatement := by
  refine ⟨C.leftIdeal_eq_sharedWitness, C.rightIdeal_eq_sharedWitness, ?_⟩
  simpa [FiniteModel.DerivedPart5.sharedWitnessHilbertRegime,
    FiniteModel.DerivedPart5.sharedWitnessConflictAlternatingSeries] using
    FiniteModel.DerivedPart5.sharedWitnessG5_denominatorClearedIdentity

end AATGAGACommonFiniteData

/-- VIII.Theorem 12.3: theorem inputs over one common selected finite datum. -/
structure AATGAGACertifiedFields {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    (C : AATGAGACommonFiniteData M) where
  /-- The finite Hodge theorem package over this common datum. -/
  finiteHodgeTheoremPackage : SelectedFiniteHodgeTheoremPackage C
  /-- The Period/Stokes theorem package over this common datum. -/
  periodStokesTheoremPackage :
    SelectedPeriodStokesTheoremPackage C finiteHodgeTheoremPackage
  /-- The finite-nerve capacity package over this common datum. -/
  topologicalDebtTheoremPackage : SelectedTopologicalDebtTheoremPackage C

/-- VIII.Principle 12.4: candidate interfaces remain separate from certified results. -/
structure AATGAGACandidateInterfaces (M : MeasurementProfile.{u, v}) where
  /-- Interface type for candidate monotone-witness stability readings. -/
  MonotoneWitnessStabilityInterface : Type v
  /-- Interface type for candidate finite-Čech stability readings. -/
  FiniteCechStabilityInterface : Type v
  /-- Interface type for candidate flat base-change readings. -/
  FlatBaseChangeInterface : Type v
  /-- Interface type for candidate spectral-hotspot readings. -/
  SpectralHotspotInterface : Type v
  /-- Interface type for candidate transfer lower-bound readings. -/
  TransferLowerBoundInterface : Type v
  /-- Optional candidate monotone-witness stability reading. -/
  monotoneWitnessStability : Option MonotoneWitnessStabilityInterface
  /-- Optional candidate finite-Čech stability reading. -/
  finiteCechStability : Option FiniteCechStabilityInterface
  /-- Optional candidate flat base-change reading. -/
  flatBaseChange : Option FlatBaseChangeInterface
  /-- Optional candidate spectral-hotspot reading. -/
  spectralHotspot : Option SpectralHotspotInterface
  /-- Optional candidate transfer lower-bound reading. -/
  transferLowerBound : Option TransferLowerBoundInterface

/-- VIII.Principle 12.4: non-conclusion data retained outside the theorem statement. -/
structure AATGAGANonConclusionData (M : MeasurementProfile.{u, v}) where
  /-- Recorded silence: no fidelity claim about unselected external data sources. -/
  noExternalDataSourceFidelity : Prop
  /-- Witness for the recorded external data-source silence. -/
  noExternalDataSourceFidelity_cert : noExternalDataSourceFidelity
  /-- Recorded silence: no correctness claim about external procedures. -/
  noExternalProcedureCorrectness : Prop
  /-- Witness for the recorded external-procedure silence. -/
  noExternalProcedureCorrectness_cert : noExternalProcedureCorrectness
  /-- Recorded silence: no comparison claim over arbitrary law universes. -/
  noArbitraryEquationHandleComparison : Prop
  /-- Witness for the recorded law-universe silence. -/
  noArbitraryEquationHandleComparison_cert :
    noArbitraryEquationHandleComparison
  /-- Recorded silence: candidate-dependent fields carry no certified conclusion. -/
  candidateDependentFieldsNotCertified : Prop
  /-- Witness for the recorded candidate-dependence silence. -/
  candidateDependentFieldsNotCertified_cert : candidateDependentFieldsNotCertified

/-- VIII.Theorem 12.3: data that enter the certified finite comparison. -/
structure AATGAGAComparisonData (M : MeasurementProfile.{u, v}) [Field M.Coeff] where
  /-- The single common finite datum shared by every certified package. -/
  commonData : AATGAGACommonFiniteData M
  /-- The theorem packages indexed by that common finite datum. -/
  certifiedFields : AATGAGACertifiedFields commonData

/-- VIII.Theorem 12.3: certified comparison statement. -/
def aatGAGACertifiedComparisonStatement {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    {C : AATGAGACommonFiniteData M} (F : AATGAGACertifiedFields C) : Prop :=
  F.finiteHodgeTheoremPackage.hodgeData.harmonicKernelIdentifiesCohomology ∧
    Nonempty
      (C.finiteCechSource.geometry.CechHn 0 ≃
        F.finiteHodgeTheoremPackage.hodgeData.allDegreeInput.degreeZeroComplex.laplacian.ker) ∧
      (∀ n, Nonempty
        (C.finiteCechSource.geometry.CechHn (n + 1) ≃
          (F.finiteHodgeTheoremPackage.hodgeData.allDegreeInput.successorComplex n).laplacian.ker)) ∧
      F.finiteHodgeTheoremPackage.hodgeData.allDegreeDecomposition ∧
        (∀ (n : Nat) (c : C.finiteCechSource.geometry.CechCochain n),
          F.finiteHodgeTheoremPackage.hodgeData.allDegreeInput.realD n
            (F.finiteHodgeTheoremPackage.hodgeData.allDegreeInput.sourceToReal n c) =
              F.finiteHodgeTheoremPackage.hodgeData.allDegreeInput.sourceToReal (n + 1)
                (C.finiteCechSource.geometry.differentialLinear n c)) ∧
          F.periodStokesTheoremPackage.periodStokesStatement ∧
            F.topologicalDebtTheoremPackage.topologicalCapacityStatement ∧
              Nonempty
                (C.lawConflict ≃ₗ[
                  Derived.Counterexample.SharedWitnessCoord.ChartRing M.Coeff]
                  Derived.Intersection.mathlibTor
                    (Derived.Counterexample.SharedWitnessCoord.ChartRing M.Coeff)
                    C.ambientLeftIdeal C.ambientRightIdeal 1) ∧
                C.hilbertSeriesConflictStatement

/-- Derive every certified comparison conjunct from the selected finite data. -/
theorem aatGAGACertifiedComparisonStatement_holds {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    {C : AATGAGACommonFiniteData M} (F : AATGAGACertifiedFields C) :
    aatGAGACertifiedComparisonStatement F := by
  refine ⟨F.finiteHodgeTheoremPackage.hodgeData.harmonicKernelIdentifiesCohomology_holds,
    ⟨AATGAGAAllDegreeRealCechHodgeInput.sourceH0EquivLaplacianKernel
      F.finiteHodgeTheoremPackage.hodgeData.allDegreeInput⟩,
    fun n => ⟨AATGAGAAllDegreeRealCechHodgeInput.sourceHsuccEquivLaplacianKernel
      F.finiteHodgeTheoremPackage.hodgeData.allDegreeInput n⟩,
    F.finiteHodgeTheoremPackage.hodgeData.allDegreeDecomposition_holds,
    F.finiteHodgeTheoremPackage.hodgeData.allDegreeDifferentialFromSource_holds,
    F.periodStokesTheoremPackage.periodStokesStatement_holds,
    F.topologicalDebtTheoremPackage.topologicalCapacityStatement_holds,
    C.lawConflictTorReading_holds,
    C.hilbertSeriesConflictStatement_holds⟩

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
