import ResearchLean.AG.UniformInvariance.UniformityReduction
import ResearchLean.AG.ResolutionInvariance.AdequateConditionCFailure
import ResearchLean.AG.ResolutionInvariance.ResolutionInvarianceFiringWitness
import Formal.Util.AssertStandardAxioms

/-!
# Instance pairs for uniform invariance

This module supplies the positive and negative instances required for the two
new predicates introduced by the G-107 uniformity reduction.  The positive
instance is the identity supported-nerve comparison on the nontrivial G-104
firing geometry; its actual comparison map is proved to be the identity on
every selected A-subnerve.  The negative instance is the reviewed adequate
G-104 failure whose actual generated H¹ map is not bijective.

The positive proof constructs the identity comparison from incidence and
support data.  Neither instance stores uniformity, bijectivity, an inverse, or
an H¹ certificate as a field.
-/

noncomputable section

namespace AAT.AG.ResolutionInvariance

open CanonicalResolution TwoPhase

universe u

variable {Source : Type u}

namespace TargetSupportedNerveMorphism

/-! ## Identity comparison on a supported nerve -/

/-- The canonical comparison factor of a reading with itself is the identity. -/
@[simp]
theorem comparisonFactor_refl_apply (q : Reading Source)
    (target : q.Target) :
    comparisonFactor q q q.coarserThan_refl target = target := by
  have hfactor := comparisonFactor_unique q q q.coarserThan_refl id
    (fun _ => rfl)
  exact (congrFun hfactor target).symm

/-- The canonical self-comparison preserves every selected target subset. -/
def identitySubsetMapsTo (q : Reading Source) (A : Set q.Target) :
    ∀ target, target ∈ A →
      comparisonFactor q q q.coarserThan_refl target ∈ A := by
  intro target htarget
  simpa using htarget

/-- The hereditary identity morphism of one target-supported nerve. -/
def identityMorphism (q : Reading Source) (D : TargetSupportedNerve q) :
    TargetSupportedNerveMorphism q q q.coarserThan_refl D D where
  chartMap := id
  edgeMap := some
  faceMap := some
  edge_some_left := by
    intro fineEdge coarseEdge hmap
    exact congrArg D.nerve.edgeLeft (Option.some.inj hmap)
  edge_some_right := by
    intro fineEdge coarseEdge hmap
    exact congrArg D.nerve.edgeRight (Option.some.inj hmap)
  edge_none_fiber := by
    intro fineEdge hmap
    simp at hmap
  face_some_edge0 := by
    intro fineFace coarseFace hmap
    exact congrArg (fun face => some (D.nerve.faceEdge0 face))
      (Option.some.inj hmap)
  face_some_edge1 := by
    intro fineFace coarseFace hmap
    exact congrArg (fun face => some (D.nerve.faceEdge1 face))
      (Option.some.inj hmap)
  face_some_edge2 := by
    intro fineFace coarseFace hmap
    exact congrArg (fun face => some (D.nerve.faceEdge2 face))
      (Option.some.inj hmap)
  face_none_edge0 := by
    intro fineFace hmap
    simp at hmap
  face_none_edge1 := by
    intro fineFace hmap
    simp at hmap
  face_none_edge2 := by
    intro fineFace hmap
    simp at hmap
  chartSupport_compatible := by
    intro fineChart fineTarget htarget
    simpa using htarget

variable {q : Reading Source}
variable {D : TargetSupportedNerve q}

/-- Identity subset transport fixes every selected chart. -/
@[simp]
theorem identityMorphism_targetSubsetChartMap
    (A : Set q.Target) (chart : D.ChartInTargetSubset A) :
    (identityMorphism q D).targetSubsetChartMap A A
        (identitySubsetMapsTo q A) chart = chart := by
  apply Subtype.ext
  rfl

/-- Identity subset transport maps every selected edge to itself. -/
@[simp]
theorem identityMorphism_targetSubsetEdgeMapOption
    (A : Set q.Target) (edge : D.EdgeInTargetSubset A) :
    (identityMorphism q D).targetSubsetEdgeMapOption A A
        (identitySubsetMapsTo q A) edge = some edge := by
  rw [(identityMorphism q D).targetSubsetEdgeMapOption_eq_some A A
    (identitySubsetMapsTo q A) edge edge rfl]
  congr 1

/-- Identity subset transport maps every selected face to itself. -/
@[simp]
theorem identityMorphism_targetSubsetFaceMapOption
    (A : Set q.Target) (face : D.FaceInTargetSubset A) :
    (identityMorphism q D).targetSubsetFaceMapOption A A
        (identitySubsetMapsTo q A) face = some face := by
  rw [(identityMorphism q D).targetSubsetFaceMapOption_eq_some A A
    (identitySubsetMapsTo q A) face face rfl]
  congr 1

/-- Degree-zero identity-subset pullback is the identity. -/
theorem identityMorphism_targetSubsetComparisonHom_f0
    (A : Set q.Target)
    (cochain : (D.targetSubsetComplex A).C0) :
    ((identityMorphism q D).targetSubsetComparisonHom A A
      (identitySubsetMapsTo q A)).f0 cochain = cochain := by
  funext chart
  change cochain ((identityMorphism q D).targetSubsetChartMap A A
    (identitySubsetMapsTo q A) chart) = cochain chart
  rw [identityMorphism_targetSubsetChartMap]

/-- Degree-one identity-subset pullback is the identity. -/
theorem identityMorphism_targetSubsetComparisonHom_f1
    (A : Set q.Target)
    (cochain : (D.targetSubsetComplex A).C1) :
    ((identityMorphism q D).targetSubsetComparisonHom A A
      (identitySubsetMapsTo q A)).f1 cochain = cochain := by
  funext edge
  change ((identityMorphism q D).targetSubsetEdgeMapOption A A
    (identitySubsetMapsTo q A) edge).elim 0 cochain = cochain edge
  rw [identityMorphism_targetSubsetEdgeMapOption]
  rfl

/-- Degree-two identity-subset pullback is the identity. -/
theorem identityMorphism_targetSubsetComparisonHom_f2
    (A : Set q.Target)
    (cochain : (D.targetSubsetComplex A).C2) :
    ((identityMorphism q D).targetSubsetComparisonHom A A
      (identitySubsetMapsTo q A)).f2 cochain = cochain := by
  funext face
  change ((identityMorphism q D).targetSubsetFaceMapOption A A
    (identitySubsetMapsTo q A) face).elim 0 cochain = cochain face
  rw [identityMorphism_targetSubsetFaceMapOption]
  rfl

/-- The actual H¹ map of the identity comparison on the same selected subset
is the identity. -/
@[simp]
theorem identityMorphism_targetSubsetComparisonHom_h1Map
    (A : Set q.Target)
    (cohomologyClass : (D.targetSubsetComplex A).H1) :
    ((identityMorphism q D).targetSubsetComparisonHom A A
      (identitySubsetMapsTo q A)).h1Map cohomologyClass = cohomologyClass := by
  obtain ⟨cycle, rfl⟩ :=
    (LinearMap.range (D.targetSubsetComplex A).boundaryToCycles).mkQ_surjective
      cohomologyClass
  rw [ThreeCochainComplex.Hom.h1Map_mk]
  apply congrArg
    (LinearMap.range (D.targetSubsetComplex A).boundaryToCycles).mkQ
  apply Subtype.ext
  exact identityMorphism_targetSubsetComparisonHom_f1 A cycle.1

/-- The actual H¹ map of the identity comparison on the same selected subset
is bijective. -/
theorem identityMorphism_targetSubsetComparisonHom_h1Map_bijective
    (A : Set q.Target) :
    Function.Bijective
      ((identityMorphism q D).targetSubsetComparisonHom A A
        (identitySubsetMapsTo q A)).h1Map := by
  constructor
  · intro left right hequal
    simpa using hequal
  · intro cohomologyClass
    exact ⟨cohomologyClass, by simp⟩

/-- The canonical self-factor preimage of a subset is that subset. -/
theorem comparisonFactor_refl_preimage (q : Reading Source)
    (A : Set q.Target) :
    comparisonFactor q q q.coarserThan_refl ⁻¹' A = A := by
  ext target
  simp

/-- Every nonempty A-subnerve comparison of the hereditary identity morphism
is bijective on actual H¹. -/
theorem identityMorphism_allNonemptyASubnerveH1Bijective [Fintype Source]
    (q : Reading Source) (D : TargetSupportedNerve q) :
    (identityMorphism q D).AllNonemptyASubnerveH1Bijective := by
  intro A _hA
  change Function.Bijective
    ((identityMorphism q D).targetSubsetComparisonHom A
      (comparisonFactor q q q.coarserThan_refl ⁻¹' A)
      (fun _ htarget => htarget)).h1Map
  exact ((identityMorphism q D).targetSubsetComparisonH1Map_bijective_congr
    A A
    (comparisonFactor q q q.coarserThan_refl ⁻¹' A) A
    rfl (comparisonFactor_refl_preimage q A)
    (fun _ htarget => htarget) (identitySubsetMapsTo q A)).2
      (identityMorphism_targetSubsetComparisonHom_h1Map_bijective A)

/-- The hereditary identity morphism is uniformly invariant for every law
family and every pair of adequacy proofs. -/
theorem identityMorphism_uniformInvariance [Fintype Source]
    (q : Reading Source) (D : TargetSupportedNerve q) :
    (identityMorphism q D).UniformInvariance :=
  ((identityMorphism q D).uniformInvariance_iff_allNonemptyASubnerveH1Bijective).2
    (identityMorphism_allNonemptyASubnerveH1Bijective q D)

end TargetSupportedNerveMorphism

/-! ## Concrete positive and negative instances -/

namespace UniformInvarianceInstancePairs

/-- Identity comparison on the nontrivial G-104 firing supported nerve. -/
abbrev positiveMorphism :=
  TargetSupportedNerveMorphism.identityMorphism
    ResolutionInvarianceFiringWitness.coarseReading
    ResolutionInvarianceFiringWitness.coarseSupported

/-- The positive comparison is uniformly invariant. -/
theorem positive_uniformInvariance : positiveMorphism.UniformInvariance :=
  TargetSupportedNerveMorphism.identityMorphism_uniformInvariance
    ResolutionInvarianceFiringWitness.coarseReading
    ResolutionInvarianceFiringWitness.coarseSupported

/-- The positive identity comparison lives on a geometry whose actual
law-generated H¹ is nonzero, so the firing is not a zero-H¹ artifact. -/
theorem positive_uniformInvariance_nontrivial :
    positiveMorphism.UniformInvariance ∧
      ResolutionInvarianceFiringWitness.coarseFiringClass ≠ 0 :=
  ⟨positive_uniformInvariance,
    ResolutionInvarianceFiringWitness.coarseFiringClass_ne_zero⟩

/-- The actual positive comparison sends the reviewed nonzero firing class to
a nonzero class. -/
theorem positive_generatedComparisonH1Map_nonzero :
    positiveMorphism.generatedComparisonH1Map
        ResolutionInvarianceFiringWitness.laws
        ResolutionInvarianceFiringWitness.coarse_adequate
        ResolutionInvarianceFiringWitness.coarse_adequate
        ResolutionInvarianceFiringWitness.coarseFiringClass ≠ 0 := by
  intro hzero
  apply ResolutionInvarianceFiringWitness.coarseFiringClass_ne_zero
  apply (positive_uniformInvariance
    ResolutionInvarianceFiringWitness.laws
    ResolutionInvarianceFiringWitness.coarse_adequate
    ResolutionInvarianceFiringWitness.coarse_adequate).1
  simpa only [map_zero] using hzero

/-- The positive comparison also satisfies the all-nonempty-A formulation. -/
theorem positive_allNonemptyASubnerveH1Bijective :
    positiveMorphism.AllNonemptyASubnerveH1Bijective :=
  positiveMorphism.uniformInvariance_iff_allNonemptyASubnerveH1Bijective.mp
    positive_uniformInvariance

/-- The reviewed adequate G-104 failure is not uniformly invariant because
one actual generated comparison H¹ map is not bijective. -/
theorem negative_not_uniformInvariance :
    ¬ CanonicalInadequateHiddenClass.nerveMorphism.UniformInvariance := by
  intro huniform
  exact AdequateConditionCFailure.generatedComparisonH1Map_not_bijective
    (huniform CanonicalInadequateHiddenClass.retainedLaws
      CanonicalInadequateHiddenClass.coarseRetainedAdequate
      CanonicalInadequateHiddenClass.retainedLawsFineAdequate)

/-- The negative comparison fails the equivalent all-nonempty-A formulation. -/
theorem negative_not_allNonemptyASubnerveH1Bijective :
    ¬ TargetSupportedNerveMorphism.AllNonemptyASubnerveH1Bijective
      CanonicalInadequateHiddenClass.nerveMorphism := by
  intro hall
  exact negative_not_uniformInvariance
    ((TargetSupportedNerveMorphism.uniformInvariance_iff_allNonemptyASubnerveH1Bijective
        CanonicalInadequateHiddenClass.nerveMorphism).mpr hall)

/-- The negative comparison has a concrete semantic failure mode: some
nonempty selected target subset has a nonbijective actual A-subnerve H¹ map. -/
theorem negative_exists_nonbijective_aSubnerveH1Map :
    ∃ A : Set CanonicalInadequateHiddenClass.coarseReading.Target,
      A.Nonempty ∧
        ¬ Function.Bijective
          (TargetSupportedNerveMorphism.aSubnerveComparisonHom
            CanonicalInadequateHiddenClass.nerveMorphism A).h1Map := by
  classical
  by_contra hno
  apply negative_not_allNonemptyASubnerveH1Bijective
  intro A hA
  by_contra hnot
  exact hno ⟨A, hA, hnot⟩

end UniformInvarianceInstancePairs

end AAT.AG.ResolutionInvariance

#assert_standard_axioms_only AAT.AG.ResolutionInvariance
