import Formal.AG.SemanticRepair.SiteCech

noncomputable section

namespace AAT.AG
namespace SemanticRepair

open CategoryTheory

universe u v w x y z r

/-! ## X.§7 theorem 7.2 semantic additive H1 / cover-relative H1 comparison -/

/--
X.定義7.1: finite-free additive semantic H1 surface used by theorem 7.2.

This is the comparison-level quotient surface.  It deliberately does not
require chart finiteness, cochain finiteness, finite-dimensionality, or a
semantic repair cover.  Finite cover data belongs to the bounded §4 surface
and concrete instances, not to the general H1 comparison theorem.
-/
structure SemanticRepairAdditiveH1Surface where
  C0 : Type y
  C1 : Type x
  C2 : Type z
  zero1 : C1
  zero2 : C2
  delta0 : C0 -> C1
  delta1 : C1 -> C2
  residual : C1
  [c0AddCommGroup : AddCommGroup C0]
  [c1AddCommGroup : AddCommGroup C1]
  zero1_eq_zero : zero1 = 0
  delta0_zero : delta0 0 = 0
  delta0_add : forall left right, delta0 (left + right) = delta0 left + delta0 right
  delta0_neg : forall primitive, delta0 (-primitive) = -delta0 primitive
  zero1_cocycle : delta1 zero1 = zero2
  delta1_delta0_eq_zero : forall primitive, delta1 (delta0 primitive) = zero2
  residual_cocycle : delta1 residual = zero2

namespace SemanticRepairAdditiveH1Surface

attribute [instance] c0AddCommGroup c1AddCommGroup

/-- X.定理7.2: finite-free semantic 1-cocycles. -/
def Cocycle (data : SemanticRepairAdditiveH1Surface) :=
  { cochain : data.C1 // data.delta1 cochain = data.zero2 }

/-- X.定理7.2: finite-free semantic same-class relation. -/
def Cohomologous
    (data : SemanticRepairAdditiveH1Surface)
    (left right : data.Cocycle) : Prop :=
  letI := data.c1AddCommGroup
  exists primitive, left.1 - right.1 = data.delta0 primitive

/-- X.定理7.2: semantic same-class is reflexive. -/
theorem cohomologous_refl
    (data : SemanticRepairAdditiveH1Surface)
    (cochain : data.Cocycle) :
    data.Cohomologous cochain cochain := by
  letI := data.c0AddCommGroup
  letI := data.c1AddCommGroup
  refine ⟨0, ?_⟩
  change cochain.1 - cochain.1 = data.delta0 0
  rw [data.delta0_zero]
  simp

/-- X.定理7.2: semantic same-class is symmetric. -/
theorem cohomologous_symm
    (data : SemanticRepairAdditiveH1Surface)
    {left right : data.Cocycle} :
    data.Cohomologous left right -> data.Cohomologous right left := by
  letI := data.c0AddCommGroup
  letI := data.c1AddCommGroup
  intro h
  rcases h with ⟨primitive, hprimitive⟩
  refine ⟨-primitive, ?_⟩
  calc
    right.1 - left.1 = -(left.1 - right.1) := by abel
    _ = -(data.delta0 primitive) := by rw [hprimitive]
    _ = data.delta0 (-primitive) := by rw [← data.delta0_neg primitive]

/-- X.定理7.2: semantic same-class is transitive. -/
theorem cohomologous_trans
    (data : SemanticRepairAdditiveH1Surface)
    {left middle right : data.Cocycle} :
    data.Cohomologous left middle ->
      data.Cohomologous middle right ->
        data.Cohomologous left right := by
  letI := data.c0AddCommGroup
  letI := data.c1AddCommGroup
  intro hleft hright
  rcases hleft with ⟨leftPrimitive, hleftPrimitive⟩
  rcases hright with ⟨rightPrimitive, hrightPrimitive⟩
  refine ⟨leftPrimitive + rightPrimitive, ?_⟩
  calc
    left.1 - right.1 =
        (left.1 - middle.1) + (middle.1 - right.1) := by abel
    _ = data.delta0 leftPrimitive + data.delta0 rightPrimitive := by
      rw [hleftPrimitive, hrightPrimitive]
    _ = data.delta0 (leftPrimitive + rightPrimitive) := by
      rw [← data.delta0_add leftPrimitive rightPrimitive]

/-- X.定理7.2: setoid for the finite-free semantic additive H1 quotient. -/
def setoid (data : SemanticRepairAdditiveH1Surface) :
    Setoid data.Cocycle where
  r := data.Cohomologous
  iseqv := ⟨data.cohomologous_refl, data.cohomologous_symm,
    data.cohomologous_trans⟩

/-- X.定理7.2: finite-free semantic additive H1 quotient. -/
def H1 (data : SemanticRepairAdditiveH1Surface) :=
  Quotient data.setoid

/-- X.定理7.2: selected residual class in semantic additive H1. -/
def residualClass (data : SemanticRepairAdditiveH1Surface) :
    data.H1 :=
  Quotient.mk data.setoid ⟨data.residual, data.residual_cocycle⟩

/-- X.定理7.2: zero class in semantic additive H1. -/
def zeroClass (data : SemanticRepairAdditiveH1Surface) :
    data.H1 :=
  Quotient.mk data.setoid ⟨data.zero1, data.zero1_cocycle⟩

/-- X.定理7.2: selected residual class vanishes in semantic additive H1. -/
def H1Zero (data : SemanticRepairAdditiveH1Surface) : Prop :=
  data.residualClass = data.zeroClass

end SemanticRepairAdditiveH1Surface

/--
X.定義7.1: cochain-level comparison between semantic additive Cech data and a
selected cover-relative Cech complex.

The fields are degree-wise carrier equivalences and differential
compatibility.  The structure does not store quotient-level `H1` maps,
zero-class equality, global coherence, sheaf descent, or later law-grounded
conclusions.
-/
structure SemanticRepairCoverRelativeH1Comparison
    (additive : SemanticRepairAdditiveH1Surface.{y, x, z})
    {U : AtomCarrier.{r}} {A : ArchitectureObject U}
    {S : Site.AATSite A}
    {cover : Cohomology.CoverRelativeCechCover S}
    {Ob : Cohomology.ObstructionSheaf S}
    (K : Cohomology.CoverRelativeCechComplex cover Ob) where
  c0Equiv :
    letI := additive.c0AddCommGroup
    letI := K.cochainAddCommGroup 0
    additive.C0 ≃+ K.Cn 0
  c1Equiv :
    letI := additive.c1AddCommGroup
    letI := K.cochainAddCommGroup 1
    additive.C1 ≃+ K.Cn 1
  c2Equiv : additive.C2 ≃ K.Cn 2
  c2Equiv_zero :
    letI := K.cochainAddCommGroup 2
    c2Equiv additive.zero2 = 0
  c2Equiv_symm_zero :
    letI := K.cochainAddCommGroup 2
    c2Equiv.symm 0 = additive.zero2
  d0_to :
    letI := additive.c0AddCommGroup
    letI := additive.c1AddCommGroup
    letI := K.cochainAddCommGroup 0
    letI := K.cochainAddCommGroup 1
    forall primitive : additive.C0,
      K.d 0 (c0Equiv primitive) = c1Equiv (additive.delta0 primitive)
  d0_from :
    letI := additive.c0AddCommGroup
    letI := additive.c1AddCommGroup
    letI := K.cochainAddCommGroup 0
    letI := K.cochainAddCommGroup 1
    forall primitive : K.Cn 0,
      additive.delta0 (c0Equiv.symm primitive) =
        c1Equiv.symm (K.d 0 primitive)
  d1_to :
    letI := additive.c1AddCommGroup
    letI := K.cochainAddCommGroup 1
    forall cochain : additive.C1,
      K.d 1 (c1Equiv cochain) = c2Equiv (additive.delta1 cochain)
  d1_from :
    letI := additive.c1AddCommGroup
    letI := K.cochainAddCommGroup 1
    forall cochain : K.Cn 1,
      additive.delta1 (c1Equiv.symm cochain) =
        c2Equiv.symm (K.d 1 cochain)

/--
X.定義7.1: stronger cochain-realization provenance for the selected
semantic/cover-relative comparison.

This is lower than the `H1` comparison surface: it records only degree-wise
carrier realization and differential compatibility.  The `toH1Comparison`
definition below generates the theorem-level comparison; no quotient result is
stored in this structure.
-/
structure SemanticRepairCoverRelativeCochainRealization
    (additive : SemanticRepairAdditiveH1Surface.{y, x, z})
    {U : AtomCarrier.{r}} {A : ArchitectureObject U}
    {S : Site.AATSite A}
    {cover : Cohomology.CoverRelativeCechCover S}
    {Ob : Cohomology.ObstructionSheaf S}
    (K : Cohomology.CoverRelativeCechComplex cover Ob) where
  c0Equiv :
    letI := additive.c0AddCommGroup
    letI := K.cochainAddCommGroup 0
    additive.C0 ≃+ K.Cn 0
  c1Equiv :
    letI := additive.c1AddCommGroup
    letI := K.cochainAddCommGroup 1
    additive.C1 ≃+ K.Cn 1
  c2Equiv : additive.C2 ≃ K.Cn 2
  c2Equiv_zero :
    letI := K.cochainAddCommGroup 2
    c2Equiv additive.zero2 = 0
  c2Equiv_symm_zero :
    letI := K.cochainAddCommGroup 2
    c2Equiv.symm 0 = additive.zero2
  d0_to :
    letI := additive.c0AddCommGroup
    letI := additive.c1AddCommGroup
    letI := K.cochainAddCommGroup 0
    letI := K.cochainAddCommGroup 1
    forall primitive : additive.C0,
      K.d 0 (c0Equiv primitive) = c1Equiv (additive.delta0 primitive)
  d0_from :
    letI := additive.c0AddCommGroup
    letI := additive.c1AddCommGroup
    letI := K.cochainAddCommGroup 0
    letI := K.cochainAddCommGroup 1
    forall primitive : K.Cn 0,
      additive.delta0 (c0Equiv.symm primitive) =
        c1Equiv.symm (K.d 0 primitive)
  d1_to :
    letI := additive.c1AddCommGroup
    letI := K.cochainAddCommGroup 1
    forall cochain : additive.C1,
      K.d 1 (c1Equiv cochain) = c2Equiv (additive.delta1 cochain)
  d1_from :
    letI := additive.c1AddCommGroup
    letI := K.cochainAddCommGroup 1
    forall cochain : K.Cn 1,
      additive.delta1 (c1Equiv.symm cochain) =
        c2Equiv.symm (K.d 1 cochain)

namespace SemanticRepairCoverRelativeCochainRealization

variable {additive : SemanticRepairAdditiveH1Surface.{y, x, z}}
variable {U : AtomCarrier.{r}} {A : ArchitectureObject U}
variable {S : Site.AATSite A}
variable {cover : Cohomology.CoverRelativeCechCover S}
variable {Ob : Cohomology.ObstructionSheaf S}
variable {K : Cohomology.CoverRelativeCechComplex cover Ob}

/-- X.定義7.1: generate the H1 comparison surface from cochain realization. -/
def toH1Comparison
    (realization : SemanticRepairCoverRelativeCochainRealization additive K) :
    SemanticRepairCoverRelativeH1Comparison additive K where
  c0Equiv := realization.c0Equiv
  c1Equiv := realization.c1Equiv
  c2Equiv := realization.c2Equiv
  c2Equiv_zero := realization.c2Equiv_zero
  c2Equiv_symm_zero := realization.c2Equiv_symm_zero
  d0_to := realization.d0_to
  d0_from := realization.d0_from
  d1_to := realization.d1_to
  d1_from := realization.d1_from

end SemanticRepairCoverRelativeCochainRealization

namespace SemanticRepairCoverRelativeH1Comparison

variable {additive : SemanticRepairAdditiveH1Surface.{y, x, z}}
variable {U : AtomCarrier.{r}} {A : ArchitectureObject U}
variable {S : Site.AATSite A}
variable {cover : Cohomology.CoverRelativeCechCover S}
variable {Ob : Cohomology.ObstructionSheaf S}
variable {K : Cohomology.CoverRelativeCechComplex cover Ob}

/-- X.定理7.2: semantic cocycles map to cover-relative degree-one cocycles. -/
def toCoverRelativeCocycle
    (comparison : SemanticRepairCoverRelativeH1Comparison additive K)
    (cocycle : additive.Cocycle) :
    K.CechCocycle 1 := by
  refine ⟨comparison.c1Equiv cocycle.1, ?_⟩
  rw [comparison.d1_to cocycle.1, cocycle.2, comparison.c2Equiv_zero]

/-- X.定理7.2: cover-relative degree-one cocycles map back to semantic cocycles. -/
def fromCoverRelativeCocycle
    (comparison : SemanticRepairCoverRelativeH1Comparison additive K)
    (cocycle : K.CechCocycle 1) :
    additive.Cocycle := by
  letI := additive.c1AddCommGroup
  refine ⟨comparison.c1Equiv.symm cocycle.1, ?_⟩
  change additive.delta1 (comparison.c1Equiv.symm cocycle.1) = additive.zero2
  rw [comparison.d1_from cocycle.1, cocycle.2, comparison.c2Equiv_symm_zero]

/--
X.定理7.2: semantic same-class is equivalent to the selected cover-relative
coboundary relation in degree one.
-/
theorem semantic_sameClass_iff_coverRelative_sameClass
    (comparison : SemanticRepairCoverRelativeH1Comparison additive K)
    (left right : additive.Cocycle) :
    additive.Cohomologous left right <->
      (K.CechCoboundarySetoidSucc 0).r
        (comparison.toCoverRelativeCocycle left)
        (comparison.toCoverRelativeCocycle right) := by
  letI := additive.c0AddCommGroup
  letI := additive.c1AddCommGroup
  letI := K.cochainAddCommGroup 0
  letI := K.cochainAddCommGroup 1
  constructor
  · intro hsame
    rcases hsame with ⟨primitive, hprimitive⟩
    refine ⟨comparison.c0Equiv primitive, ?_⟩
    calc
      comparison.c1Equiv left.1 - comparison.c1Equiv right.1 =
          comparison.c1Equiv (left.1 - right.1) := by
            rw [map_sub]
      _ = comparison.c1Equiv (additive.delta0 primitive) := by
            rw [hprimitive]
      _ = K.d 0 (comparison.c0Equiv primitive) := by
            rw [comparison.d0_to]
  · intro hcover
    rcases hcover with ⟨primitive, hprimitive⟩
    refine ⟨comparison.c0Equiv.symm primitive, ?_⟩
    apply comparison.c1Equiv.injective
    calc
      comparison.c1Equiv (left.1 - right.1) =
          comparison.c1Equiv left.1 - comparison.c1Equiv right.1 := by
            rw [map_sub]
      _ = K.d 0 primitive := hprimitive
      _ = comparison.c1Equiv
            (comparison.c1Equiv.symm (K.d 0 primitive)) := by
            rw [comparison.c1Equiv.apply_symm_apply]
      _ = comparison.c1Equiv
            (additive.delta0 (comparison.c0Equiv.symm primitive)) := by
            rw [comparison.d0_from]

/-- X.定理7.2: generated map from semantic additive H1 to cover-relative H1. -/
def toCoverRelativeH1
    (comparison : SemanticRepairCoverRelativeH1Comparison additive K) :
    additive.H1 -> K.CechCohomologySucc 0 :=
  Quotient.lift
    (fun cocycle =>
      K.cohomologyClassSucc 0 (comparison.toCoverRelativeCocycle cocycle))
    (by
      intro left right hsame
      exact
        Quotient.sound
          ((comparison.semantic_sameClass_iff_coverRelative_sameClass
            left right).1 hsame))

/-- X.定理7.2: generated map from cover-relative H1 back to semantic additive H1. -/
def fromCoverRelativeH1
    (comparison : SemanticRepairCoverRelativeH1Comparison additive K) :
    K.CechCohomologySucc 0 -> additive.H1 :=
  Quotient.lift
    (fun cocycle =>
      letI := additive.c1AddCommGroup
      Quotient.mk additive.setoid (comparison.fromCoverRelativeCocycle cocycle))
    (by
      intro left right hsame
      letI := additive.c1AddCommGroup
      have hcover :
          (K.CechCoboundarySetoidSucc 0).r
            (comparison.toCoverRelativeCocycle
              (comparison.fromCoverRelativeCocycle left))
            (comparison.toCoverRelativeCocycle
              (comparison.fromCoverRelativeCocycle right)) := by
        letI := K.cochainAddCommGroup 1
        rcases hsame with ⟨primitive, hprimitive⟩
        refine ⟨primitive, ?_⟩
        change
          comparison.c1Equiv (comparison.c1Equiv.symm left.1) -
              comparison.c1Equiv (comparison.c1Equiv.symm right.1) =
            K.d 0 primitive
        rw [comparison.c1Equiv.apply_symm_apply left.1,
          comparison.c1Equiv.apply_symm_apply right.1]
        exact hprimitive
      exact
        Quotient.sound
          ((comparison.semantic_sameClass_iff_coverRelative_sameClass
            (comparison.fromCoverRelativeCocycle left)
            (comparison.fromCoverRelativeCocycle right)).2 hcover))

/--
X.定理7.2: the generated maps are inverse on the semantic additive H1 quotient.
-/
theorem from_to_semanticH1
    (comparison : SemanticRepairCoverRelativeH1Comparison additive K)
    (h : additive.H1) :
    comparison.fromCoverRelativeH1 (comparison.toCoverRelativeH1 h) = h := by
  refine Quotient.inductionOn h ?_
  intro cocycle
  letI := additive.c0AddCommGroup
  letI := additive.c1AddCommGroup
  apply Quotient.sound
  refine ⟨(0 : additive.C0), ?_⟩
  change
    comparison.c1Equiv.symm (comparison.c1Equiv cocycle.1) - cocycle.1 =
      additive.delta0 0
  rw [comparison.c1Equiv.symm_apply_apply, sub_self, additive.delta0_zero]

/--
X.定理7.2: the generated maps are inverse on the cover-relative H1 quotient.
-/
theorem to_from_coverRelativeH1
    (comparison : SemanticRepairCoverRelativeH1Comparison additive K)
    (h : K.CechCohomologySucc 0) :
    comparison.toCoverRelativeH1 (comparison.fromCoverRelativeH1 h) = h := by
  refine Quotient.inductionOn h ?_
  intro cocycle
  letI := additive.c1AddCommGroup
  apply Quotient.sound
  letI := K.cochainAddCommGroup 0
  letI := K.cochainAddCommGroup 1
  refine ⟨0, ?_⟩
  change
    comparison.c1Equiv (comparison.c1Equiv.symm cocycle.1) - cocycle.1 =
      K.d 0 0
  rw [comparison.c1Equiv.apply_symm_apply cocycle.1]
  simp

/--
X.定理7.2: generated equivalence between semantic additive H1 and
cover-relative Cech H1.
-/
def semanticRepairAdditiveH1_equiv_coverRelativeH1
    (comparison : SemanticRepairCoverRelativeH1Comparison additive K) :
    additive.H1 ≃ K.CechCohomologySucc 0 where
  toFun := comparison.toCoverRelativeH1
  invFun := comparison.fromCoverRelativeH1
  left_inv := comparison.from_to_semanticH1
  right_inv := comparison.to_from_coverRelativeH1

/-- X.定理7.2: selected residual zero predicate in cover-relative H1. -/
def CoverRelativeResidualH1Zero
    (comparison : SemanticRepairCoverRelativeH1Comparison additive K) : Prop :=
  comparison.toCoverRelativeH1 additive.residualClass =
    comparison.toCoverRelativeH1 additive.zeroClass

/--
X.定理7.2: semantic additive H1 zero is equivalent to selected
cover-relative residual H1 zero.
-/
theorem semanticRepairAdditiveH1Zero_iff_coverRelativeH1Zero
    (comparison : SemanticRepairCoverRelativeH1Comparison additive K) :
    additive.H1Zero <-> comparison.CoverRelativeResidualH1Zero := by
  constructor
  · intro hzero
    exact congrArg comparison.toCoverRelativeH1 hzero
  · intro hzero
    calc
      additive.residualClass =
          comparison.fromCoverRelativeH1
            (comparison.toCoverRelativeH1 additive.residualClass) := by
            rw [comparison.from_to_semanticH1 additive.residualClass]
      _ = comparison.fromCoverRelativeH1
            (comparison.toCoverRelativeH1 additive.zeroClass) := by
            rw [hzero]
      _ = additive.zeroClass := comparison.from_to_semanticH1 additive.zeroClass

/--
X.定理7.2 package: the generated comparison maps, H1 equivalence, same-class
equivalence, and zero-predicate equivalence.
-/
structure SemanticRepairAdditiveH1CoverRelativeH1ComparisonPackage
    (comparison : SemanticRepairCoverRelativeH1Comparison additive K) :
    Type (max u v w x y z r) where
  toCoverRelativeH1 : additive.H1 -> K.CechCohomologySucc 0
  fromCoverRelativeH1 : K.CechCohomologySucc 0 -> additive.H1
  h1Equiv : additive.H1 ≃ K.CechCohomologySucc 0
  sameClass_iff_coverRelative :
    forall left right : additive.Cocycle,
      additive.Cohomologous left right <->
        (K.CechCoboundarySetoidSucc 0).r
          (comparison.toCoverRelativeCocycle left)
          (comparison.toCoverRelativeCocycle right)
  zero_iff_coverRelativeZero :
    additive.H1Zero <-> comparison.CoverRelativeResidualH1Zero

/-- X.定理7.2: construct the comparison package from cochain-level data. -/
def semanticRepairAdditiveH1_coverRelativeH1_comparison_packageData
    (comparison : SemanticRepairCoverRelativeH1Comparison additive K) :
    SemanticRepairAdditiveH1CoverRelativeH1ComparisonPackage comparison where
  toCoverRelativeH1 := comparison.toCoverRelativeH1
  fromCoverRelativeH1 := comparison.fromCoverRelativeH1
  h1Equiv := comparison.semanticRepairAdditiveH1_equiv_coverRelativeH1
  sameClass_iff_coverRelative := by
    intro left right
    exact comparison.semantic_sameClass_iff_coverRelative_sameClass left right
  zero_iff_coverRelativeZero :=
    comparison.semanticRepairAdditiveH1Zero_iff_coverRelativeH1Zero

/--
X.定理7.2: semantic additive H1 and cover-relative H1 agree under the selected
cochain-level comparison.
-/
theorem semanticRepairAdditiveH1_coverRelativeH1_comparison_package
    (comparison : SemanticRepairCoverRelativeH1Comparison additive K) :
    Nonempty (SemanticRepairAdditiveH1CoverRelativeH1ComparisonPackage comparison) :=
  ⟨comparison.semanticRepairAdditiveH1_coverRelativeH1_comparison_packageData⟩

end SemanticRepairCoverRelativeH1Comparison

end SemanticRepair
end AAT.AG
