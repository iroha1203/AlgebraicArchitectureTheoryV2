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
  oneToReal : S.nerveComplex.C1 ≃+ RealC1
  twoToReal : S.nerveComplex.C2 ≃+ RealC2
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

/-- The all-degree Hodge statement for the selected finite Čech realization. -/
def allDegreeHodgeStatement {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    {S : AATGAGAFiniteCechSource M} (H : AATGAGAAllDegreeRealCechHodgeInput S) : Prop :=
  Nonempty (H.degreeZeroComplex.laplacian.ker ≃ₗ[ℝ] H.degreeZeroComplex.cohomology) ∧
    (∀ n, Nonempty
      ((H.successorComplex n).laplacian.ker ≃ₗ[ℝ]
        (H.successorComplex n).cohomology))

/-- The exact-harmonic-coexact decomposition in every selected Čech degree. -/
def allDegreeDecompositionStatement {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    {S : AATGAGAFiniteCechSource M} (H : AATGAGAAllDegreeRealCechHodgeInput S) : Prop :=
  (∀ c : H.RealCochain 0,
    H.degreeZeroComplex.exactPart c + H.degreeZeroComplex.harmonicPart c +
      H.degreeZeroComplex.coexactPart c = c) ∧
    (∀ (n : Nat) (c : H.RealCochain (n + 1)),
      (H.successorComplex n).exactPart c +
      (H.successorComplex n).harmonicPart c +
        (H.successorComplex n).coexactPart c = c)

/-- The standard finite-dimensional Hodge theorem yields every selected degree. -/
theorem allDegreeHodgeStatement_holds {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    {S : AATGAGAFiniteCechSource M} (H : AATGAGAAllDegreeRealCechHodgeInput S) :
    H.allDegreeHodgeStatement := by
  refine ⟨⟨H.degreeZeroComplex.laplacianKernelEquivCohomology⟩, ?_⟩
  intro n
  exact ⟨(H.successorComplex n).laplacianKernelEquivCohomology⟩

/-- The standard finite-dimensional Hodge decomposition yields every selected degree. -/
theorem allDegreeDecompositionStatement_holds {M : MeasurementProfile.{u, v}}
    [Field M.Coeff] {S : AATGAGAFiniteCechSource M}
    (H : AATGAGAAllDegreeRealCechHodgeInput S) : H.allDegreeDecompositionStatement := by
  refine ⟨?_, ?_⟩
  · intro c
    exact H.degreeZeroComplex.hodge_decomposition c
  · intro n c
    exact (H.successorComplex n).hodge_decomposition c

/-- The all-degree source comparison is the supplied transported-differential law. -/
theorem realD_eq_source_holds {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    {S : AATGAGAFiniteCechSource M} (H : AATGAGAAllDegreeRealCechHodgeInput S) :
    ∀ (n : Nat) (c : S.geometry.CechCochain n),
      H.realD n (H.sourceToReal n c) =
        H.sourceToReal (n + 1) (S.geometry.differentialLinear n c) :=
  H.realD_eq_source

end AATGAGAAllDegreeRealCechHodgeInput

/-- VIII.Theorem 12.3: finite data shared by every certified comparison. -/
structure AATGAGACommonFiniteData (M : MeasurementProfile.{u, v}) [Field M.Coeff] where
  /-- The generated finite Čech source shared by all four packages. -/
  finiteCechSource : AATGAGAFiniteCechSource M
  /-- The site selected from the generated source. -/
  selectedSite : M.SiteObj
  /-- The adequate-cover member selected from the generated source. -/
  selectedCover : M.Cover
  /-- The profile coefficient selected for this comparison. -/
  selectedCoefficient : M.Coeff
  /-- The measurement-domain element selected for the comparison. -/
  selectedMeasurement : M.Domain
  /-- Evidence that the selected measurement belongs to the measured profile. -/
  measuredSelection : M.Measured_M selectedMeasurement
  /-- The common ambient used for the selected law-ideal reading. -/
  commonAmbient : CommonAmbientPair M
  /-- The common ambient has the atom carrier selected by the Čech source. -/
  ambientAtomType_eq_source : commonAmbient.AmbientSpace = finiteCechSource.geometry.U.Atom
  /-- The profile obstruction-object handle is read in the common ambient. -/
  ambientStructureSheafFromProfile : M.ObstructionObject → commonAmbient.StructureSheaf
  /-- The selected ambient sheaf is the reading of the selected profile handle. -/
  selectedObstructionObject : M.ObstructionObject
  selectedStructureSheaf_eq_profile : commonAmbient.selectedStructureSheaf =
    ambientStructureSheafFromProfile selectedObstructionObject
  /-- Interpret the selected ambient structure sheaf on the actual Čech site. -/
  ambientStructureSheafToSource : commonAmbient.StructureSheaf →
    Cohomology.ObstructionSheaf finiteCechSource.geometry.site
  /-- The selected common-ambient sheaf is exactly the source coefficient sheaf. -/
  selectedStructureSheaf_realizes_source :
    ambientStructureSheafToSource commonAmbient.selectedStructureSheaf =
      finiteCechSource.geometry.obstructionSheaf
  /-- The ambient coefficient object is the profile coefficient type. -/
  ambientCoefficientObject_eq_profile : commonAmbient.CoefficientObject = M.Coeff
  /-- The left ambient coefficient is the selected profile coefficient. -/
  leftCoefficient_eq_selected :
    cast ambientCoefficientObject_eq_profile commonAmbient.leftCoefficient = selectedCoefficient
  /-- The right ambient coefficient is the selected profile coefficient. -/
  rightCoefficient_eq_selected :
    cast ambientCoefficientObject_eq_profile commonAmbient.rightCoefficient = selectedCoefficient
  /-- The selected site is the finite Čech source site. -/
  selectedSite_eq_source : selectedSite = finiteCechSource.selectedSite
  /-- The selected cover is the finite Čech source cover. -/
  selectedCover_eq_source : selectedCover = finiteCechSource.selectedCover
  /-- The left ambient domain is the selected measurement-domain element. -/
  ambientLeftDomain_eq : commonAmbient.leftDomain = selectedMeasurement
  /-- The right ambient domain is the selected measurement-domain element. -/
  ambientRightDomain_eq : commonAmbient.rightDomain = selectedMeasurement

/-- The Hodge data are a real realization of the generated Čech source. -/
structure AATGAGASelectedFiniteHodgeData {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    (C : AATGAGACommonFiniteData M) where
  /-- The real finite cochain realization of this common Čech source. -/
  realInput : AATGAGARealCechHodgeInput C.finiteCechSource
  /-- The all-degree real realization of the same generated Čech source. -/
  allDegreeInput : AATGAGAAllDegreeRealCechHodgeInput C.finiteCechSource

namespace AATGAGASelectedFiniteHodgeData

/-- The canonical source `H¹` is identified with the harmonic kernel. -/
def harmonicKernelIdentifiesCohomology {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    {C : AATGAGACommonFiniteData M} (D : AATGAGASelectedFiniteHodgeData C) : by
  letI := D.realInput.zeroNormed
  letI := D.realInput.zeroInner
  letI := D.realInput.zeroFinite
  letI := D.realInput.oneNormed
  letI := D.realInput.oneInner
  letI := D.realInput.oneFinite
  letI := D.realInput.twoNormed
  letI := D.realInput.twoInner
  letI := D.realInput.twoFinite
  exact Prop := by
  letI := D.realInput.zeroNormed
  letI := D.realInput.zeroInner
  letI := D.realInput.zeroFinite
  letI := D.realInput.oneNormed
  letI := D.realInput.oneInner
  letI := D.realInput.oneFinite
  letI := D.realInput.twoNormed
  letI := D.realInput.twoInner
  letI := D.realInput.twoFinite
  exact Nonempty
    (C.finiteCechSource.canonicalH1 ≃+ D.realInput.realFiniteComplex.laplacian.ker)

/-- The selected real finite complex has its exact-harmonic-coexact decomposition. -/
def finiteHodgeDecomposition {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    {C : AATGAGACommonFiniteData M} (D : AATGAGASelectedFiniteHodgeData C) : by
  letI := D.realInput.zeroNormed
  letI := D.realInput.zeroInner
  letI := D.realInput.zeroFinite
  letI := D.realInput.oneNormed
  letI := D.realInput.oneInner
  letI := D.realInput.oneFinite
  letI := D.realInput.twoNormed
  letI := D.realInput.twoInner
  letI := D.realInput.twoFinite
  exact Prop := by
  letI := D.realInput.zeroNormed
  letI := D.realInput.zeroInner
  letI := D.realInput.zeroFinite
  letI := D.realInput.oneNormed
  letI := D.realInput.oneInner
  letI := D.realInput.oneFinite
  letI := D.realInput.twoNormed
  letI := D.realInput.twoInner
  letI := D.realInput.twoFinite
  exact ∀ c, D.realInput.realFiniteComplex.exactPart c +
    D.realInput.realFiniteComplex.harmonicPart c +
      D.realInput.realFiniteComplex.coexactPart c = c

/-- Derive the harmonic-kernel identification from the generated source maps. -/
theorem harmonicKernelIdentifiesCohomology_holds {M : MeasurementProfile.{u, v}}
    [Field M.Coeff] {C : AATGAGACommonFiniteData M}
    (D : AATGAGASelectedFiniteHodgeData C) : D.harmonicKernelIdentifiesCohomology := by
  letI := D.realInput.zeroNormed
  letI := D.realInput.zeroInner
  letI := D.realInput.zeroFinite
  letI := D.realInput.oneNormed
  letI := D.realInput.oneInner
  letI := D.realInput.oneFinite
  letI := D.realInput.twoNormed
  letI := D.realInput.twoInner
  letI := D.realInput.twoFinite
  exact D.realInput.hodgeStatement_holds.2

/-- Derive the finite Hodge decomposition from the selected real complex. -/
theorem finiteHodgeDecomposition_holds {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    {C : AATGAGACommonFiniteData M} (D : AATGAGASelectedFiniteHodgeData C) :
    D.finiteHodgeDecomposition := by
  letI := D.realInput.zeroNormed
  letI := D.realInput.zeroInner
  letI := D.realInput.zeroFinite
  letI := D.realInput.oneNormed
  letI := D.realInput.oneInner
  letI := D.realInput.oneFinite
  letI := D.realInput.twoNormed
  letI := D.realInput.twoInner
  letI := D.realInput.twoFinite
  exact D.realInput.hodgeStatement_holds.1

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
  P.sourceHodgeData.realInput.periodStokesStatement

/-- Derive Stokes from the same real Čech map used by the Hodge package. -/
theorem periodStokesStatement_holds {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    {C : AATGAGACommonFiniteData M} {H : SelectedFiniteHodgeTheoremPackage C}
    (P : SelectedPeriodStokesTheoremPackage C H) : P.periodStokesStatement := by
  change P.sourceHodgeData.realInput.periodStokesStatement
  rw [P.sourceHodgeData_eq]
  exact H.hodgeData.realInput.periodStokesStatement_holds

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

/-- VIII.Theorem 12.3: common-ambient reading of the selected derived conflict. -/
structure SelectedDerivedConflictTheoremPackage {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    (C : AATGAGACommonFiniteData M) where
  /-- The selected common-ambient law ideal is evaluated as a chart ideal. -/
  generatedLawIdeal : C.commonAmbient.LawIdeal →
    Ideal (Derived.Counterexample.SharedWitnessCoord.ChartRing M.Coeff)
  /-- The selected left ambient law generates the fixed `xy` chart ideal. -/
  leftGeneratedIdeal_eq :
    generatedLawIdeal C.commonAmbient.leftLawIdeal =
      Derived.Counterexample.SharedWitnessCoord.idealU M.Coeff
  /-- The selected right ambient law generates the fixed `xz` chart ideal. -/
  rightGeneratedIdeal_eq :
    generatedLawIdeal C.commonAmbient.rightLawIdeal =
      Derived.Counterexample.SharedWitnessCoord.idealV M.Coeff

namespace SelectedDerivedConflictTheoremPackage

/-- The left chart ideal generated by the selected common-ambient law. -/
def leftIdeal {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    {C : AATGAGACommonFiniteData M} (P : SelectedDerivedConflictTheoremPackage C) :
    Ideal (Derived.Counterexample.SharedWitnessCoord.ChartRing M.Coeff) :=
  P.generatedLawIdeal C.commonAmbient.leftLawIdeal

/-- The right chart ideal generated by the selected common-ambient law. -/
def rightIdeal {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    {C : AATGAGACommonFiniteData M} (P : SelectedDerivedConflictTheoremPackage C) :
    Ideal (Derived.Counterexample.SharedWitnessCoord.ChartRing M.Coeff) :=
  P.generatedLawIdeal C.commonAmbient.rightLawIdeal

/-- The degree-one LawConflict object of the canonical selected Tor bridge. -/
abbrev lawConflict {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    {C : AATGAGACommonFiniteData M} (P : SelectedDerivedConflictTheoremPackage C) :=
  (Derived.Intersection.canonicalSelectedTorBridge
    (Derived.Counterexample.SharedWitnessCoord.ChartRing M.Coeff)
    P.leftIdeal P.rightIdeal).LawConflict 1

/-- The canonical degree-one LawConflict/Mathlib Tor linear equivalence. -/
noncomputable def lawConflictLinearEquivMathlibTor {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    {C : AATGAGACommonFiniteData M} (P : SelectedDerivedConflictTheoremPackage C) :
    P.lawConflict ≃ₗ[Derived.Counterexample.SharedWitnessCoord.ChartRing M.Coeff]
      Derived.Intersection.mathlibTor
        (Derived.Counterexample.SharedWitnessCoord.ChartRing M.Coeff)
        P.leftIdeal P.rightIdeal 1 :=
  (Derived.Intersection.canonicalSelectedTorBridge
    (Derived.Counterexample.SharedWitnessCoord.ChartRing M.Coeff)
    P.leftIdeal P.rightIdeal).lawConflictLinearEquivMathlibTor 1

/-- Derive the selected LawConflict/Tor reading from its canonical bridge. -/
theorem lawConflictTorReading_holds {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    {C : AATGAGACommonFiniteData M} (P : SelectedDerivedConflictTheoremPackage C) :
    Nonempty
      (P.lawConflict ≃ₗ[Derived.Counterexample.SharedWitnessCoord.ChartRing M.Coeff]
        Derived.Intersection.mathlibTor
          (Derived.Counterexample.SharedWitnessCoord.ChartRing M.Coeff)
          P.leftIdeal P.rightIdeal 1) :=
  ⟨P.lawConflictLinearEquivMathlibTor⟩

/-- The selected law generators are the two ideals used by the fixed Hilbert calculation. -/
def hilbertSeriesConflictStatement {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    {C : AATGAGACommonFiniteData M} (P : SelectedDerivedConflictTheoremPackage C) : Prop :=
  let regime := FiniteModel.DerivedPart5.sharedWitnessHilbertRegime M.Coeff
  P.leftIdeal = regime.I_U ∧
    P.rightIdeal = regime.I_V ∧
      regime.quotientUHilbertSeries * regime.quotientVHilbertSeries =
        regime.ambientHilbertSeries *
          (regime.lawConflictHilbertSeries 0 - regime.lawConflictHilbertSeries 1)

/-- Derive the all-degree Hilbert-series accounting from the generated law ideals. -/
theorem hilbertSeriesConflictStatement_holds {M : MeasurementProfile.{u, v}}
    [Field M.Coeff] {C : AATGAGACommonFiniteData M}
    (P : SelectedDerivedConflictTheoremPackage C) : P.hilbertSeriesConflictStatement := by
  refine ⟨P.leftGeneratedIdeal_eq, P.rightGeneratedIdeal_eq, ?_⟩
  simpa [FiniteModel.DerivedPart5.sharedWitnessHilbertRegime,
    FiniteModel.DerivedPart5.sharedWitnessConflictAlternatingSeries] using
    FiniteModel.DerivedPart5.sharedWitnessG5_denominatorClearedIdentity

end SelectedDerivedConflictTheoremPackage

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
  /-- The derived LawConflict package over this common datum. -/
  derivedConflictTheoremPackage : SelectedDerivedConflictTheoremPackage C

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
  (C.ambientStructureSheafToSource C.commonAmbient.selectedStructureSheaf =
    C.finiteCechSource.geometry.obstructionSheaf) ∧
    F.finiteHodgeTheoremPackage.hodgeData.harmonicKernelIdentifiesCohomology ∧
      F.finiteHodgeTheoremPackage.hodgeData.allDegreeHodge ∧
        F.finiteHodgeTheoremPackage.hodgeData.allDegreeDecomposition ∧
          (∀ (n : Nat) (c : C.finiteCechSource.geometry.CechCochain n),
            F.finiteHodgeTheoremPackage.hodgeData.allDegreeInput.realD n
              (F.finiteHodgeTheoremPackage.hodgeData.allDegreeInput.sourceToReal n c) =
                F.finiteHodgeTheoremPackage.hodgeData.allDegreeInput.sourceToReal (n + 1)
                  (C.finiteCechSource.geometry.differentialLinear n c)) ∧
            F.periodStokesTheoremPackage.periodStokesStatement ∧
              F.topologicalDebtTheoremPackage.topologicalCapacityStatement ∧
                Nonempty
                  (F.derivedConflictTheoremPackage.lawConflict ≃ₗ[
                    Derived.Counterexample.SharedWitnessCoord.ChartRing M.Coeff]
                    Derived.Intersection.mathlibTor
                      (Derived.Counterexample.SharedWitnessCoord.ChartRing M.Coeff)
                      F.derivedConflictTheoremPackage.leftIdeal
                      F.derivedConflictTheoremPackage.rightIdeal 1) ∧
                  F.derivedConflictTheoremPackage.hilbertSeriesConflictStatement

/-- Derive every certified comparison conjunct from the selected finite data. -/
theorem aatGAGACertifiedComparisonStatement_holds {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    {C : AATGAGACommonFiniteData M} (F : AATGAGACertifiedFields C) :
    aatGAGACertifiedComparisonStatement F := by
  refine ⟨C.selectedStructureSheaf_realizes_source,
    F.finiteHodgeTheoremPackage.hodgeData.harmonicKernelIdentifiesCohomology_holds,
    F.finiteHodgeTheoremPackage.hodgeData.allDegreeHodge_holds,
    F.finiteHodgeTheoremPackage.hodgeData.allDegreeDecomposition_holds,
    F.finiteHodgeTheoremPackage.hodgeData.allDegreeDifferentialFromSource_holds,
    F.periodStokesTheoremPackage.periodStokesStatement_holds,
    F.topologicalDebtTheoremPackage.topologicalCapacityStatement_holds,
    F.derivedConflictTheoremPackage.lawConflictTorReading_holds,
    F.derivedConflictTheoremPackage.hilbertSeriesConflictStatement_holds⟩

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
