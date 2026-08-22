import ResearchLean.AG.DoctrineFiberProduct.DoctrinePullbackFiniteCode
import ResearchLean.AG.DoctrineFiberProduct.SchemaWitnesses

/-!
# Proper finite witnesses for doctrine pullbacks

This module fires the arbitrary `Doct_U` pullback producer on a symmetric
finite-code cospan.  Both three-cell source tables send cells zero and one to
base cell zero and cell two to base cell one.  The resulting compatible-pair
source contains independent collisions for both projections, while the pair
of cells zero and two does not lie in the canonical component-pair image.

The public conclusions use `Nonempty`, failure of surjectivity, categorical
`IsIso`, and the representation-invariant `ProperDoctrineFiber` predicate.
Concrete first-order cell calculations occur only in the named fixture lemmas.
No pullback certificate or properness conclusion is supplied as input.
-/

namespace AAT.AG.DoctrineFiberProduct

open CategoryTheory CategoryTheory.Limits
open AtomFoundation

/-- Executable Atom equality for the concrete finite carrier. -/
local instance doctrinePullbackWitnessAtomDecidableEq :
    DecidableEq FiniteModel.carrier.Atom := by
  change DecidableEq FiniteModel.FiniteAtom
  infer_instance

/-! ## A symmetric three-to-two finite cospan -/

/-- Cell zero of the three-source all-admitting doctrine. -/
def finiteThreeSourceZero : (finiteAllDoctrineCode 3).Source :=
  ULift.up ⟨0, by decide⟩

/-- Cell one of the three-source all-admitting doctrine. -/
def finiteThreeSourceOne : (finiteAllDoctrineCode 3).Source :=
  ULift.up ⟨1, by decide⟩

/-- Cell two of the three-source all-admitting doctrine. -/
def finiteThreeSourceTwo : (finiteAllDoctrineCode 3).Source :=
  ULift.up ⟨2, by decide⟩

/-- The first two cells of the three-source fixture are distinct. -/
theorem finiteThreeSourceZero_ne_one :
    finiteThreeSourceZero ≠ finiteThreeSourceOne := by
  intro heq
  have hdown := congrArg
    (fun source : (finiteAllDoctrineCode 3).Source => source.down.val) heq
  norm_num [finiteThreeSourceZero, finiteThreeSourceOne,
    finiteAllDoctrineCode] at hdown

/-- Cells zero and two of the three-source fixture are distinct. -/
theorem finiteThreeSourceZero_ne_two :
    finiteThreeSourceZero ≠ finiteThreeSourceTwo := by
  intro heq
  have hdown := congrArg
    (fun source : (finiteAllDoctrineCode 3).Source => source.down.val) heq
  norm_num [finiteThreeSourceZero, finiteThreeSourceTwo,
    finiteAllDoctrineCode] at hdown

/-- The two named cells of the existing two-source base are distinct. -/
theorem finiteTwoSourceZero_ne_one :
    finiteTwoSourceZero ≠ finiteTwoSourceOne := by
  intro heq
  have hdown := congrArg
    (fun source : (finiteAllDoctrineCode 2).Source => source.down.val) heq
  norm_num [finiteTwoSourceZero, finiteTwoSourceOne,
    finiteAllDoctrineCode] at hdown

/-- Pointed three-source finite doctrine used on both sides of the cospan. -/
def finiteThreeSourceInstance : FiniteInstanceCode FiniteModel.carrier where
  doctrine := finiteAllDoctrineCode 3
  point := finiteThreeSourceZero

/-- The symmetric source table `[0, 0, 1]` from three cells to two cells. -/
def finiteThreeToTwoSourceMap :
    finiteThreeSourceInstance.doctrine.Source →
      finiteTwoSourceInstance.doctrine.Source :=
  fun source =>
    if source.down.val = 2 then finiteTwoSourceOne else finiteTwoSourceZero

/-- The symmetric source table sends cell zero to base cell zero. -/
@[simp]
theorem finiteThreeToTwoSourceMap_zero :
    finiteThreeToTwoSourceMap finiteThreeSourceZero = finiteTwoSourceZero := by
  simp [finiteThreeToTwoSourceMap, finiteThreeSourceZero]

/-- The symmetric source table also sends cell one to base cell zero. -/
@[simp]
theorem finiteThreeToTwoSourceMap_one :
    finiteThreeToTwoSourceMap finiteThreeSourceOne = finiteTwoSourceZero := by
  simp [finiteThreeToTwoSourceMap, finiteThreeSourceOne,
    finiteThreeSourceInstance, finiteAllDoctrineCode]

/-- The symmetric source table sends cell two to base cell one. -/
@[simp]
theorem finiteThreeToTwoSourceMap_two :
    finiteThreeToTwoSourceMap finiteThreeSourceTwo = finiteTwoSourceOne := by
  simp [finiteThreeToTwoSourceMap, finiteThreeSourceTwo]

/-- Validated finite-code presentation of the symmetric three-to-two leg. -/
def finiteThreeToTwoPresentation :
    CartPresentationBetween finiteThreeSourceInstance finiteTwoSourceInstance where
  sourceMap := finiteThreeToTwoSourceMap
  atomEquiv := AtomPermutationCode.refl
  normalize_eq _ := rfl
  extraction_eq source := by
    change finiteAllAtomPredicate =
      finiteAllAtomPredicate.transport AtomPermutationCode.refl.toEquiv
    rw [AtomPermutationCode.toEquiv_refl]
    simp
  source_eq := finiteThreeToTwoSourceMap_zero

/-- Decoded exact doctrine leg of the symmetric finite cospan. -/
def finiteThreeToTwoDoctrineHom :
    finiteThreeSourceInstance.doctrine.toDoctrine ⟶
      finiteTwoSourceInstance.doctrine.toDoctrine :=
  (typedPresentationToSemantic finiteThreeToTwoPresentation).doctrineHom

/-- The decoded doctrine leg sends cell zero to base cell zero. -/
@[simp]
theorem finiteThreeToTwoDoctrineHom_zero :
    finiteThreeToTwoDoctrineHom.sourceMap finiteThreeSourceZero =
      finiteTwoSourceZero :=
  finiteThreeToTwoSourceMap_zero

/-- The decoded doctrine leg sends cell one to base cell zero. -/
@[simp]
theorem finiteThreeToTwoDoctrineHom_one :
    finiteThreeToTwoDoctrineHom.sourceMap finiteThreeSourceOne =
      finiteTwoSourceZero :=
  finiteThreeToTwoSourceMap_one

/-- The decoded doctrine leg sends cell two to base cell one. -/
@[simp]
theorem finiteThreeToTwoDoctrineHom_two :
    finiteThreeToTwoDoctrineHom.sourceMap finiteThreeSourceTwo =
      finiteTwoSourceOne :=
  finiteThreeToTwoSourceMap_two

/-! ## Internally generated compatible and incompatible pairs -/

/-- Compatible pair `(0, 0)` in the symmetric doctrine pullback. -/
def finiteProperFiberCompatible00 :
    DoctrinePullbackSource finiteThreeToTwoDoctrineHom
      finiteThreeToTwoDoctrineHom :=
  ⟨(finiteThreeSourceZero, finiteThreeSourceZero), rfl⟩

/-- Compatible pair `(0, 1)`, used for the first-projection collision. -/
def finiteProperFiberCompatible01 :
    DoctrinePullbackSource finiteThreeToTwoDoctrineHom
      finiteThreeToTwoDoctrineHom :=
  ⟨(finiteThreeSourceZero, finiteThreeSourceOne), by simp⟩

/-- Compatible pair `(1, 0)`, used for the second-projection collision. -/
def finiteProperFiberCompatible10 :
    DoctrinePullbackSource finiteThreeToTwoDoctrineHom
      finiteThreeToTwoDoctrineHom :=
  ⟨(finiteThreeSourceOne, finiteThreeSourceZero), by simp⟩

/-- The two sources used for the first-projection collision are distinct. -/
theorem finiteProperFiberCompatible00_ne_01 :
    finiteProperFiberCompatible00 ≠ finiteProperFiberCompatible01 := by
  intro heq
  exact finiteThreeSourceZero_ne_one
    (congrArg (fun source => source.val.2) heq)

/-- The two sources used for the second-projection collision are distinct. -/
theorem finiteProperFiberCompatible00_ne_10 :
    finiteProperFiberCompatible00 ≠ finiteProperFiberCompatible10 := by
  intro heq
  exact finiteThreeSourceZero_ne_one
    (congrArg (fun source => source.val.1) heq)

/-- Product pair `(0, 2)` whose two images differ in the common base source. -/
def finiteProperFiberIncompatible02 :
    finiteThreeSourceInstance.doctrine.Source ×
      finiteThreeSourceInstance.doctrine.Source :=
  (finiteThreeSourceZero, finiteThreeSourceTwo)

/-- The pair `(0, 2)` is incompatible by a typed inequality in the common base. -/
theorem finiteProperFiberIncompatible02_commonBase_ne :
    finiteThreeToTwoDoctrineHom.sourceMap
        finiteProperFiberIncompatible02.1 ≠
      finiteThreeToTwoDoctrineHom.sourceMap
        finiteProperFiberIncompatible02.2 := by
  simpa [finiteProperFiberIncompatible02] using finiteTwoSourceZero_ne_one

/-- The generated doctrine pullback source is inhabited by the compatible pair `(0, 0)`. -/
theorem finiteProperDoctrinePullback_source_nonempty :
    Nonempty
      (doctrinePullback finiteThreeToTwoDoctrineHom
        finiteThreeToTwoDoctrineHom).Source :=
  ⟨finiteProperFiberCompatible00⟩

/-- The incompatible pair `(0, 2)` is outside the canonical component-pair image. -/
theorem finiteProperFiberIncompatible02_not_in_range :
    finiteProperFiberIncompatible02 ∉ Set.range
      (doctrineSourcePairMap
        (doctrinePullbackFst finiteThreeToTwoDoctrineHom
          finiteThreeToTwoDoctrineHom)
        (doctrinePullbackSnd finiteThreeToTwoDoctrineHom
          finiteThreeToTwoDoctrineHom)) := by
  rintro ⟨source, hsource⟩
  have hpair : source.val = finiteProperFiberIncompatible02 := by
    simpa [doctrineSourcePairMap, doctrinePullbackFst,
      doctrinePullbackSnd] using hsource
  have hcompatible := source.property
  rw [hpair] at hcompatible
  exact finiteProperFiberIncompatible02_commonBase_ne hcompatible

/-- The canonical map from the pullback source to the component product is not surjective. -/
theorem finiteProperDoctrinePullback_pairMap_not_surjective :
    ¬ Function.Surjective
      (doctrineSourcePairMap
        (doctrinePullbackFst finiteThreeToTwoDoctrineHom
          finiteThreeToTwoDoctrineHom)
        (doctrinePullbackSnd finiteThreeToTwoDoctrineHom
          finiteThreeToTwoDoctrineHom)) := by
  intro hsurjective
  exact finiteProperFiberIncompatible02_not_in_range
    (hsurjective finiteProperFiberIncompatible02)

/-- The pairs `(0, 0)` and `(0, 1)` collide under the first projection. -/
theorem finiteProperDoctrinePullback_fst_collision :
    (doctrinePullbackFst finiteThreeToTwoDoctrineHom
        finiteThreeToTwoDoctrineHom).sourceMap finiteProperFiberCompatible00 =
      (doctrinePullbackFst finiteThreeToTwoDoctrineHom
        finiteThreeToTwoDoctrineHom).sourceMap finiteProperFiberCompatible01 :=
  rfl

/-- The pairs `(0, 0)` and `(1, 0)` collide under the second projection. -/
theorem finiteProperDoctrinePullback_snd_collision :
    (doctrinePullbackSnd finiteThreeToTwoDoctrineHom
        finiteThreeToTwoDoctrineHom).sourceMap finiteProperFiberCompatible00 =
      (doctrinePullbackSnd finiteThreeToTwoDoctrineHom
        finiteThreeToTwoDoctrineHom).sourceMap finiteProperFiberCompatible10 :=
  rfl

/-- The first projection of the symmetric doctrine pullback is not an isomorphism. -/
theorem finiteProperDoctrinePullback_fst_not_isIso :
    ¬ IsIso
      (doctrinePullbackFst finiteThreeToTwoDoctrineHom
        finiteThreeToTwoDoctrineHom) := by
  intro hIso
  letI : IsIso
      (doctrinePullbackFst finiteThreeToTwoDoctrineHom
        finiteThreeToTwoDoctrineHom) := hIso
  have hinjective := exactDoctrineHom_sourceMap_injective_of_isIso
    (doctrinePullbackFst finiteThreeToTwoDoctrineHom
      finiteThreeToTwoDoctrineHom)
  exact finiteProperFiberCompatible00_ne_01
    (hinjective finiteProperDoctrinePullback_fst_collision)

/-- The second projection of the symmetric doctrine pullback is not an isomorphism. -/
theorem finiteProperDoctrinePullback_snd_not_isIso :
    ¬ IsIso
      (doctrinePullbackSnd finiteThreeToTwoDoctrineHom
        finiteThreeToTwoDoctrineHom) := by
  intro hIso
  letI : IsIso
      (doctrinePullbackSnd finiteThreeToTwoDoctrineHom
        finiteThreeToTwoDoctrineHom) := hIso
  have hinjective := exactDoctrineHom_sourceMap_injective_of_isIso
    (doctrinePullbackSnd finiteThreeToTwoDoctrineHom
      finiteThreeToTwoDoctrineHom)
  exact finiteProperFiberCompatible00_ne_10
    (hinjective finiteProperDoctrinePullback_snd_collision)

/-- The symmetric semantic producer output is a proper doctrine fiber. -/
theorem finiteProperDoctrineFiber :
    ProperDoctrineFiber
      (doctrinePullbackFst finiteThreeToTwoDoctrineHom
        finiteThreeToTwoDoctrineHom)
      (doctrinePullbackSnd finiteThreeToTwoDoctrineHom
        finiteThreeToTwoDoctrineHom) :=
  ⟨finiteProperDoctrinePullback_source_nonempty,
    finiteProperDoctrinePullback_pairMap_not_surjective,
    finiteProperDoctrinePullback_fst_not_isIso,
    finiteProperDoctrinePullback_snd_not_isIso⟩

/-! ## Finite-code realization and doctrine pullback firing -/

/-- Concrete finite-code realization isomorphism to the semantic doctrine pullback. -/
noncomputable def finiteProperFiberRealizationIso :
    (pullbackDoctrineCode finiteThreeToTwoPresentation
        finiteThreeToTwoPresentation).toDoctrine ≅
      doctrinePullback finiteThreeToTwoDoctrineHom
        finiteThreeToTwoDoctrineHom :=
  doctrinePullbackFiniteCodeIso finiteThreeToTwoPresentation
    finiteThreeToTwoPresentation

/-- The concrete realization isomorphism preserves the first projection. -/
theorem finiteProperFiberRealizationIso_hom_fst :
    finiteProperFiberRealizationIso.hom ≫
        doctrinePullbackFst finiteThreeToTwoDoctrineHom
          finiteThreeToTwoDoctrineHom =
      (typedPresentationToSemantic
        (pullbackFstPresentation finiteThreeToTwoPresentation
          finiteThreeToTwoPresentation)).doctrineHom := by
  simpa [finiteProperFiberRealizationIso, finiteThreeToTwoDoctrineHom] using
    doctrinePullbackFiniteCodeIso_hom_fst finiteThreeToTwoPresentation
      finiteThreeToTwoPresentation

/-- The concrete realization isomorphism preserves the second projection. -/
theorem finiteProperFiberRealizationIso_hom_snd :
    finiteProperFiberRealizationIso.hom ≫
        doctrinePullbackSnd finiteThreeToTwoDoctrineHom
          finiteThreeToTwoDoctrineHom =
      (typedPresentationToSemantic
        (pullbackSndPresentation finiteThreeToTwoPresentation
          finiteThreeToTwoPresentation)).doctrineHom := by
  simpa [finiteProperFiberRealizationIso, finiteThreeToTwoDoctrineHom] using
    doctrinePullbackFiniteCodeIso_hom_snd finiteThreeToTwoPresentation
      finiteThreeToTwoPresentation

/-- Properness transports to the two decoded finite-code projections. -/
theorem finiteProperFiberFiniteCode_proper :
    ProperDoctrineFiber
      (typedPresentationToSemantic
        (pullbackFstPresentation finiteThreeToTwoPresentation
          finiteThreeToTwoPresentation)).doctrineHom
      (typedPresentationToSemantic
        (pullbackSndPresentation finiteThreeToTwoPresentation
          finiteThreeToTwoPresentation)).doctrineHom := by
  apply (properDoctrineFiber_iff_of_iso
    finiteProperFiberRealizationIso (Iso.refl _) (Iso.refl _)
    (typedPresentationToSemantic
      (pullbackFstPresentation finiteThreeToTwoPresentation
        finiteThreeToTwoPresentation)).doctrineHom
    (typedPresentationToSemantic
      (pullbackSndPresentation finiteThreeToTwoPresentation
        finiteThreeToTwoPresentation)).doctrineHom
    (doctrinePullbackFst finiteThreeToTwoDoctrineHom
      finiteThreeToTwoDoctrineHom)
    (doctrinePullbackSnd finiteThreeToTwoDoctrineHom
      finiteThreeToTwoDoctrineHom)
    (by simpa using finiteProperFiberRealizationIso_hom_fst.symm)
    (by simpa using finiteProperFiberRealizationIso_hom_snd.symm)).mpr
  exact finiteProperDoctrineFiber

/-- The two decoded finite-code projections form the concrete pullback in `Doct_U`. -/
theorem finiteProperFiberFiniteCode_isPullback :
    IsPullback
      (typedPresentationToSemantic
        (pullbackFstPresentation finiteThreeToTwoPresentation
          finiteThreeToTwoPresentation)).doctrineHom
      (typedPresentationToSemantic
        (pullbackSndPresentation finiteThreeToTwoPresentation
          finiteThreeToTwoPresentation)).doctrineHom
      finiteThreeToTwoDoctrineHom finiteThreeToTwoDoctrineHom := by
  simpa [finiteThreeToTwoDoctrineHom] using
    pullbackPresentation_doctrine_isPullback finiteThreeToTwoPresentation
      finiteThreeToTwoPresentation

/-! ## A nonidentity-Atom cone and its generated lift -/

/-- Three-source identity table with the existing nonidentity finite Atom swap. -/
noncomputable def finiteThreeSwapPresentation :
    CartPresentationBetween finiteThreeSourceInstance finiteThreeSourceInstance where
  sourceMap := id
  atomEquiv := finiteSwapPermutationCode
  normalize_eq _ := rfl
  extraction_eq source := by
    change finiteAllAtomPredicate =
      finiteAllAtomPredicate.transport finiteSwapPermutationCode.toEquiv
    simp [finiteAllAtomPredicate, AtomPredicateCode.transport]
  source_eq := rfl

/-- Decoded three-source doctrine automorphism with a nonidentity Atom component. -/
noncomputable def finiteThreeSwapDoctrineHom :
    finiteThreeSourceInstance.doctrine.toDoctrine ⟶
      finiteThreeSourceInstance.doctrine.toDoctrine :=
  (typedPresentationToSemantic finiteThreeSwapPresentation).doctrineHom

/-- Symmetric cone whose two legs use the actual nonidentity Atom swap. -/
noncomputable def finiteProperFiberSwapCone :
    PullbackCone finiteThreeToTwoDoctrineHom finiteThreeToTwoDoctrineHom :=
  PullbackCone.mk finiteThreeSwapDoctrineHom finiteThreeSwapDoctrineHom rfl

/-- The first cone leg moves `componentC` to `dependsAB`. -/
theorem finiteProperFiberSwapCone_fst_componentC :
    finiteProperFiberSwapCone.fst.atomEquiv
        FiniteModel.FiniteAtom.componentC =
      FiniteModel.FiniteAtom.dependsAB := by
  change finiteSwapPermutationCode.toEquiv
      FiniteModel.FiniteAtom.componentC =
    FiniteModel.FiniteAtom.dependsAB
  exact finiteSwapPermutationCode_componentC

/-- The generated universal lift preserves the cone's nonidentity Atom graph. -/
theorem finiteProperFiberSwapLift_componentC :
    (doctrinePullbackLift finiteThreeToTwoDoctrineHom
        finiteThreeToTwoDoctrineHom finiteProperFiberSwapCone).atomEquiv
          FiniteModel.FiniteAtom.componentC =
      FiniteModel.FiniteAtom.dependsAB := by
  rw [doctrinePullbackLift_atomEquiv]
  exact finiteProperFiberSwapCone_fst_componentC

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
