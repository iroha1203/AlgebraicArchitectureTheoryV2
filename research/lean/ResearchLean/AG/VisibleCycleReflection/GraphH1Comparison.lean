import ResearchLean.AG.VisibleCycleReflection.CechGraphComparison
import ResearchLean.AG.ResolutionInvariance.LawValueBlockCohomology
import Formal.Util.AssertStandardAxioms

/-! # Quotient-level normalization of the actual integral and visible rational H1 -/
noncomputable section
namespace AAT.AG.VisibleCycleReflection
open CanonicalResolution ResolutionInvariance ObstructionDiagnosticBridge Cohomology TwoPhase DirectSum
universe u
variable {Source : Type u} [Fintype Source] {laws : FiniteLawFamily Source} {q : Reading Source}

/-- A: ordinary integral graph H1, as all edge cochains modulo vertex differences. -/
abbrev IntegralGraphH1 (N : CoverNerve.{u}) (Label : Type u) :=
  (N.EdgeComponent → Label → ℤ) ⧸ (integralGraphD0 N Label).range

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U} {S : Site.AATSite A}
variable {D : TargetSupportedNerve q} {G : ContextOpenSupport S}
variable [IsEmpty D.nerve.FaceComponent]
variable (P : GeneratorPresentation laws) (C : GeneratorPresentation.FaceEmptyAATCechCover D G)

/-- A: all actual edge cochains are cycles, and their coordinates are integral graph cochains. -/
def actualIntegralCyclesEquiv (hR : P.ReflectionCondition) :
    (P.faceEmptyCechComplex C).CechCocycleSubgroup 1 ≃+
      (D.nerve.EdgeComponent → LawValueLabel laws → ℤ) where
  toFun z := actualIntegralCochain1Equiv P C hR z.1
  invFun z := ⟨(actualIntegralCochain1Equiv P C hR).symm z, by
    change (P.faceEmptyCechComplex C).d 1 _ = 0
    rw [P.faceEmptyCech_d1_eq_zero C]
    rfl⟩
  left_inv z := by
    apply Subtype.ext
    exact (actualIntegralCochain1Equiv P C hR).left_inv z.1
  right_inv z := (actualIntegralCochain1Equiv P C hR).right_inv z
  map_add' _ _ := map_add _ _ _

/-- Public evaluation of the actual cycle coordinate equivalence. -/
@[simp]
theorem actualIntegralCyclesEquiv_apply (hR : P.ReflectionCondition)
    (z : (P.faceEmptyCechComplex C).CechCocycleSubgroup 1) :
    actualIntegralCyclesEquiv P C hR z = actualIntegralCochain1Equiv P C hR z.1 := rfl

/-- A: actual coboundaries map exactly, in both directions, to ordinary vertex differences. -/
theorem actualIntegral_range (hR : P.ReflectionCondition) :
    ((P.faceEmptyCechComplex C).CechCoboundarySubgroupSucc 0).map
      (actualIntegralCyclesEquiv P C hR).toAddMonoidHom =
      (integralGraphD0 D.nerve (LawValueLabel laws)).range := by
  ext z
  constructor
  · rintro ⟨cycle, ⟨cochain, rfl⟩, rfl⟩
    exact ⟨actualIntegralCochain0Equiv P C hR cochain, (actualIntegral_d0 P C hR cochain).symm⟩
  · rintro ⟨cochain, rfl⟩
    let actual := (actualIntegralCochain0Equiv P C hR).symm cochain
    refine ⟨(P.faceEmptyCechComplex C).coboundaryCocycle 0 actual, ⟨actual, rfl⟩, ?_⟩
    change actualIntegralCochain1Equiv P C hR ((P.faceEmptyCechComplex C).d 0 actual) = _
    rw [actualIntegral_d0]
    rw [(actualIntegralCochain0Equiv P C hR).apply_symm_apply]

/-- A: the actual Cech H1 is the ordinary graph H1 with integral label coefficients. -/
def actualIntegralH1Equiv (hR : P.ReflectionCondition) :
    (P.faceEmptyCechComplex C).AdditiveCechH1 ≃+
      IntegralGraphH1 D.nerve (LawValueLabel laws) :=
  QuotientAddGroup.congr _ _ (actualIntegralCyclesEquiv P C hR) (actualIntegral_range P C hR)

/-- A: the H1 equivalence sends every actual quotient representative to its graph cochain. -/
@[simp]
theorem actualIntegralH1Equiv_mk (hR : P.ReflectionCondition)
    (z : (P.faceEmptyCechComplex C).CechCocycle 1) :
    actualIntegralH1Equiv P C hR ((P.faceEmptyCechComplex C).additiveH1Class z) =
      (QuotientAddGroup.mk (actualIntegralCochain1Equiv P C hR z.1) :
        IntegralGraphH1 D.nerve (LawValueLabel laws)) := rfl

/-- A: the transported existing descent class has exactly the specified graph mismatch representative. -/
theorem existingDescent_graph_representative (hR : P.ReflectionCondition)
    (x : GeneratorPresentation.ActualCechAffineLocalData P C) :
    actualIntegralH1Equiv P C hR x.existingDescentAdditiveClass =
      (QuotientAddGroup.mk (actualIntegralCochain1Equiv P C hR x.actualMismatch) :
        IntegralGraphH1 D.nerve (LawValueLabel laws)) := by
  rw [x.existingDescentAdditiveClass_eq_actualClass]
  exact actualIntegralH1Equiv_mk P C hR x.actualCocycle

variable (D) (hadequate : laws.Adequate q) (label : LawValueLabel laws)

/-- A: the ordinary rational H1 of the specified visible graph. -/
abbrev VisibleGraphH1 := (VisibleEdge D hadequate label → ℚ) ⧸
  LinearMap.range (visibleD0 D hadequate label)

/-- All block face coordinates are empty because the complete actual face type is empty. -/
instance visibleBlockFaceIsEmpty : IsEmpty (D.FaceBlockCoordinate laws hadequate label) where
  false face := isEmptyElim face.1.cell

omit [Fintype Source] in
/-- A: the existing block degree-one differential is zero for the complete face-empty nerve. -/
theorem visibleBlockD1_eq_zero : D.lawValueBlockD1 laws hadequate label = 0 := by
  ext c face
  exact isEmptyElim face

/-- A: degree-two block cochains identify with the empty ordinary graph product. -/
def visibleCochain2Equiv : (D.FaceBlockCoordinate laws hadequate label → ℚ) ≃ₗ[ℚ]
    (PEmpty.{u + 1} → ℚ) where
  toFun _ point := isEmptyElim point
  invFun _ face := isEmptyElim face
  left_inv _ := by ext face; exact isEmptyElim face
  right_inv _ := by ext point; exact isEmptyElim point
  map_add' _ _ := by ext point; exact isEmptyElim point
  map_smul' _ _ := by ext point; exact isEmptyElim point

/-- A: the ordinary finite visible graph complex has its usual vertex difference and no faces. -/
def visibleGraphComplex : ThreeCochainComplex ℚ := by
  classical
  letI : Fintype (VisibleVertex D hadequate label) := Fintype.ofFinite _
  letI : Fintype (VisibleEdge D hadequate label) := Fintype.ofFinite _
  exact {
    C0 := VisibleVertex D hadequate label → ℚ
    C1 := VisibleEdge D hadequate label → ℚ
    C2 := PEmpty.{u + 1} → ℚ
    d0 := visibleD0 D hadequate label
    d1 := 0
    d1_comp_d0 := fun _ => rfl }

omit [Fintype Source] in
/-- A: the degree-one differential square is the unique empty-product square. -/
theorem visibleD1_intertwining (c : D.EdgeBlockCoordinate laws hadequate label → ℚ) :
    visibleCochain2Equiv D hadequate label (D.lawValueBlockD1 laws hadequate label c) =
      (visibleGraphComplex D hadequate label).d1 (visibleCochain1Equiv D hadequate label c) := by
  ext point
  exact isEmptyElim point

/-- A: block cycles are exactly all rational edge cochains of the visible graph. -/
def visibleBlockCyclesEquiv :
    LinearMap.ker (D.lawValueBlockComplex laws hadequate label).d1 ≃ₗ[ℚ]
      (VisibleEdge D hadequate label → ℚ) where
  toFun z := visibleCochain1Equiv D hadequate label z.1
  invFun z := ⟨(visibleCochain1Equiv D hadequate label).symm z, by
    change D.lawValueBlockD1 laws hadequate label _ = 0
    rw [visibleBlockD1_eq_zero]
    rfl⟩
  left_inv z := by
    apply Subtype.ext
    exact (visibleCochain1Equiv D hadequate label).left_inv z.1
  right_inv z := (visibleCochain1Equiv D hadequate label).right_inv z
  map_add' _ _ := map_add _ _ _
  map_smul' _ _ := map_smul _ _ _

/-- Public evaluation of the block cycle equivalence. -/
@[simp]
theorem visibleBlockCyclesEquiv_apply
    (z : LinearMap.ker (D.lawValueBlockComplex laws hadequate label).d1) :
    visibleBlockCyclesEquiv D hadequate label z = visibleCochain1Equiv D hadequate label z.1 := rfl

/-- A: block coboundaries map exactly to visible graph vertex differences. -/
theorem visibleBlock_range :
    (LinearMap.range (D.lawValueBlockComplex laws hadequate label).boundaryToCycles).map
      (visibleBlockCyclesEquiv D hadequate label).toLinearMap =
      LinearMap.range (visibleD0 D hadequate label) := by
  ext z
  constructor
  · rintro ⟨cycle, ⟨cochain, rfl⟩, rfl⟩
    exact ⟨visibleCochain0Equiv D hadequate label cochain,
      (visibleD0_intertwining D hadequate label cochain).symm⟩
  · rintro ⟨cochain, rfl⟩
    let block := (visibleCochain0Equiv D hadequate label).symm cochain
    refine ⟨(D.lawValueBlockComplex laws hadequate label).boundaryToCycles block,
      ⟨block, rfl⟩, ?_⟩
    change visibleCochain1Equiv D hadequate label
      (D.lawValueBlockD0 laws hadequate label block) = _
    rw [visibleD0_intertwining]
    rw [(visibleCochain0Equiv D hadequate label).apply_symm_apply]

/-- A: the existing rational block H1 is the ordinary H1 of the visible graph. -/
def visibleBlockH1Equiv : (D.lawValueBlockComplex laws hadequate label).H1 ≃ₗ[ℚ]
    VisibleGraphH1 D hadequate label :=
  Submodule.Quotient.equiv _ _ (visibleBlockCyclesEquiv D hadequate label)
    (visibleBlock_range D hadequate label)

/-- A: the block H1 equivalence is the exact map on quotient representatives. -/
@[simp]
theorem visibleBlockH1Equiv_mk
    (z : LinearMap.ker (D.lawValueBlockComplex laws hadequate label).d1) :
    visibleBlockH1Equiv D hadequate label
      ((LinearMap.range (D.lawValueBlockComplex laws hadequate label).boundaryToCycles).mkQ z) =
      (LinearMap.range (visibleD0 D hadequate label)).mkQ
        (visibleCochain1Equiv D hadequate label z.1) := rfl


/-- A: the ordinary graph differential after rational coefficient change. -/
def rationalGraphD0 (N : CoverNerve.{u}) (Label : Type u) :
    (N.Chart → Label → ℚ) →ₗ[ℚ] (N.EdgeComponent → Label → ℚ) where
  toFun c edge current := c (N.edgeRight edge) current - c (N.edgeLeft edge) current
  map_add' _ _ := by ext; simp; ring
  map_smul' _ _ := by ext; simp; ring

/-- Public evaluation of the full rational graph differential. -/
@[simp]
theorem rationalGraphD0_apply (N : CoverNerve.{u}) (Label : Type u)
    (c : N.Chart → Label → ℚ) (edge : N.EdgeComponent) (current : Label) :
    rationalGraphD0 N Label c edge current =
      c (N.edgeRight edge) current - c (N.edgeLeft edge) current := rfl

/-- A: full rational graph H1 before restricting any visible component. -/
abbrev RationalGraphH1 (N : CoverNerve.{u}) (Label : Type u) :=
  (N.EdgeComponent → Label → ℚ) ⧸ LinearMap.range (rationalGraphD0 N Label)

/-- Integer-to-rational coefficient change on all graph edge cochains. -/
def graphCoefficientCast (N : CoverNerve.{u}) (Label : Type u) :
    (N.EdgeComponent → Label → ℤ) →+ (N.EdgeComponent → Label → ℚ) where
  toFun c edge current := (c edge current : ℚ)
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp

/-- Public evaluation of coefficient change. -/
@[simp]
theorem graphCoefficientCast_apply (N : CoverNerve.{u}) (Label : Type u)
    (c : N.EdgeComponent → Label → ℤ) (edge : N.EdgeComponent) (current : Label) :
    graphCoefficientCast N Label c edge current = (c edge current : ℚ) := rfl

/-- A: coefficient change sends every integral vertex difference to a rational one. -/
theorem graphCoefficientCast_d0 (N : CoverNerve.{u}) (Label : Type u)
    (c : N.Chart → Label → ℤ) :
    graphCoefficientCast N Label (integralGraphD0 N Label c) =
      rationalGraphD0 N Label (fun vertex current => (c vertex current : ℚ)) := by
  ext edge current
  simp

/-- A: the additive H1 map induced by ordinary coefficient change. -/
def integerToRationalH1 (N : CoverNerve.{u}) (Label : Type u) :
    IntegralGraphH1 N Label →+ RationalGraphH1 N Label :=
  QuotientAddGroup.lift (integralGraphD0 N Label).range
    ((LinearMap.range (rationalGraphD0 N Label)).mkQ.toAddMonoidHom.comp
      (graphCoefficientCast N Label)) (by
        rintro _ ⟨cochain, rfl⟩
        apply (Submodule.Quotient.mk_eq_zero _).mpr
        exact ⟨fun vertex current => (cochain vertex current : ℚ),
          (graphCoefficientCast_d0 N Label cochain).symm⟩)

/-- A: coefficient change has its prescribed action on every H1 representative. -/
@[simp]
theorem integerToRationalH1_mk (N : CoverNerve.{u}) (Label : Type u)
    (c : N.EdgeComponent → Label → ℤ) :
    integerToRationalH1 N Label (QuotientAddGroup.mk c) =
      (LinearMap.range (rationalGraphD0 N Label)).mkQ (graphCoefficientCast N Label c) := rfl

/-- A: rational edge cochains restricted to one specified visible label. -/
def rationalRestriction1 : (D.nerve.EdgeComponent → LawValueLabel laws → ℚ) →ₗ[ℚ]
    (VisibleEdge D hadequate label → ℚ) where
  toFun c edge := c edge.1 label
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Fintype Source] [IsEmpty D.nerve.FaceComponent] in
/-- Public evaluation of the visible edge restriction. -/
@[simp]
theorem rationalRestriction1_apply (c : D.nerve.EdgeComponent → LawValueLabel laws → ℚ)
    (edge : VisibleEdge D hadequate label) :
    rationalRestriction1 D hadequate label c edge = c edge.1 label := rfl

omit [Fintype Source] [IsEmpty D.nerve.FaceComponent] in
/-- A: the visible restriction preserves ordinary vertex differences. -/
theorem rationalRestriction_d0 (c : D.nerve.Chart → LawValueLabel laws → ℚ) :
    rationalRestriction1 D hadequate label (rationalGraphD0 D.nerve (LawValueLabel laws) c) =
      visibleD0 D hadequate label (fun vertex => c vertex.1 label) := rfl

/-- A: the standard H1 restriction of the full rational graph to its visible part. -/
def rationalRestrictionH1 : RationalGraphH1 D.nerve (LawValueLabel laws) →ₗ[ℚ]
    VisibleGraphH1 D hadequate label :=
  Submodule.mapQ (LinearMap.range (rationalGraphD0 D.nerve (LawValueLabel laws)))
    (LinearMap.range (visibleD0 D hadequate label))
    (rationalRestriction1 D hadequate label) (by
      rintro _ ⟨cochain, rfl⟩
      exact ⟨fun vertex => cochain vertex.1 label,
        (rationalRestriction_d0 D hadequate label cochain).symm⟩)

omit [Fintype Source] [IsEmpty D.nerve.FaceComponent] in
/-- A: restriction has the prescribed action on every rational H1 representative. -/
@[simp]
theorem rationalRestrictionH1_mk (c : D.nerve.EdgeComponent → LawValueLabel laws → ℚ) :
    rationalRestrictionH1 D hadequate label
      ((LinearMap.range (rationalGraphD0 D.nerve (LawValueLabel laws))).mkQ c) =
      (LinearMap.range (visibleD0 D hadequate label)).mkQ
        (rationalRestriction1 D hadequate label c) := rfl

/-- A: the existing diagnostic H1 identified with the finite direct sum of visible graph H1. -/
def diagnosticVisibleH1Equiv : (D.lawGeneratedComplex laws hadequate).H1 ≃ₗ[ℚ]
    ⨁ current : LawValueLabel laws, VisibleGraphH1 D hadequate current :=
  (D.lawGeneratedH1BlockEquiv laws hadequate) ≪≫ₗ
    DirectSum.linearEquivFunOnFintype ℚ (LawValueLabel laws)
      (fun current => (D.lawValueBlockComplex laws hadequate current).H1) ≪≫ₗ
    LinearEquiv.piCongrRight (fun current => visibleBlockH1Equiv D hadequate current) ≪≫ₗ
    (DirectSum.linearEquivFunOnFintype ℚ (LawValueLabel laws)
      (fun current => VisibleGraphH1 D hadequate current)).symm

/-- Public component evaluation of the diagnostic quotient equivalence. -/
@[simp]
theorem diagnosticVisibleH1Equiv_component
    (h : (D.lawGeneratedComplex laws hadequate).H1) (current : LawValueLabel laws) :
    (DirectSum.linearEquivFunOnFintype ℚ (LawValueLabel laws)
      (fun l => VisibleGraphH1 D hadequate l)
      (diagnosticVisibleH1Equiv D hadequate h)) current =
      visibleBlockH1Equiv D hadequate current
        ((DirectSum.linearEquivFunOnFintype ℚ (LawValueLabel laws)
          (fun l => (D.lawValueBlockComplex laws hadequate l).H1)
          (D.lawGeneratedH1BlockEquiv laws hadequate h)) current) := by
  let E := DirectSum.linearEquivFunOnFintype ℚ (LawValueLabel laws)
    (fun l => VisibleGraphH1 D hadequate l)
  change (E (E.symm _)) current = _
  rw [E.apply_symm_apply]
  rfl

/-- A: diagnostic quotient transport preserves the exact visible cochain representative. -/
theorem diagnosticVisibleH1Equiv_mk_component
    (z : LinearMap.ker (D.lawGeneratedComplex laws hadequate).d1)
    (current : LawValueLabel laws) :
    (DirectSum.linearEquivFunOnFintype ℚ (LawValueLabel laws)
      (fun l => VisibleGraphH1 D hadequate l)
      (diagnosticVisibleH1Equiv D hadequate
        ((LinearMap.range (D.lawGeneratedComplex laws hadequate).boundaryToCycles).mkQ z))) current =
      (LinearMap.range (visibleD0 D hadequate current)).mkQ
        (visibleCochain1Equiv D hadequate current (fun coordinate => z.1 coordinate.1)) := by
  rw [diagnosticVisibleH1Equiv_component, D.lawGeneratedH1BlockEquiv_mk_component,
    visibleBlockH1Equiv_mk]
  rfl

/-- A: every component of the existing actual comparison factors through coefficient change
and the standard visible restriction, on every actual cohomology class. -/
theorem actualCechDiagnosticH1Map_factorization (hR : P.ReflectionCondition)
    (h : (P.faceEmptyCechComplex C).AdditiveCechH1) :
    (DirectSum.linearEquivFunOnFintype ℚ (LawValueLabel laws)
      (fun l => VisibleGraphH1 D hadequate l)
      (diagnosticVisibleH1Equiv D hadequate (P.actualCechDiagnosticH1Map C hadequate h))) label =
      rationalRestrictionH1 D hadequate label
        (integerToRationalH1 D.nerve (LawValueLabel laws) (actualIntegralH1Equiv P C hR h)) := by
  induction h using QuotientAddGroup.induction_on with
  | H z =>
    change _ = _
    rw [show P.actualCechDiagnosticH1Map C hadequate (QuotientAddGroup.mk z) =
      (LinearMap.range (D.lawGeneratedComplex laws hadequate).boundaryToCycles).mkQ
        (P.actualCechDiagnosticCyclesMap C hadequate z) by rfl]
    rw [diagnosticVisibleH1Equiv_mk_component]
    change _ = rationalRestrictionH1 D hadequate label
      (integerToRationalH1 D.nerve (LawValueLabel laws)
        (QuotientAddGroup.mk (actualIntegralCochain1Equiv P C hR z.1)))
    rw [integerToRationalH1_mk, rationalRestrictionH1_mk]
    congr 1
    ext edge
    exact actualCoefficient1_visible P C hR hadequate label z.1 edge


namespace GeometricCover
variable {X I : Type u} [TopologicalSpace X] [LinearOrder I] [Fintype I]

/-- A: the full comparison factorization for every local affine input on the constructed
point/generator AAT cover, using the independent diagnostic and the existing descent class. -/
theorem input_local_data_factorization (K : GeometricCover X I)
    (target : I → Set q.Target) (hne : ∀ i, (target i).Nonempty)
    (hR : P.ReflectionCondition)
    (hadequate : laws.Adequate q)
    (x : GeneratorPresentation.ActualCechAffineLocalData P (K.actualCechCover P target hne))
    (current : LawValueLabel laws) :
    (DirectSum.linearEquivFunOnFintype ℚ (LawValueLabel laws)
      (fun l => VisibleGraphH1 (K.supportedNerve target hne) hadequate l)
      (diagnosticVisibleH1Equiv (K.supportedNerve target hne) hadequate
        (x.diagnosticClass hadequate))) current =
      rationalRestrictionH1 (K.supportedNerve target hne) hadequate current
        (integerToRationalH1 (K.supportedNerve target hne).nerve (LawValueLabel laws)
          (actualIntegralH1Equiv P (K.actualCechCover P target hne) hR
            x.existingDescentAdditiveClass)) := by
  have h := actualCechDiagnosticH1Map_factorization
    (P := P) (C := K.actualCechCover P target hne) (D := K.supportedNerve target hne)
    (hadequate := hadequate) (label := current) hR x.existingDescentAdditiveClass
  rw [existingDescent_comparison P (K.actualCechCover P target hne) hadequate x] at h
  exact h

end GeometricCover
end AAT.AG.VisibleCycleReflection
#assert_standard_axioms_only AAT.AG.VisibleCycleReflection
