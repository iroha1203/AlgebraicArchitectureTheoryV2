import ResearchLean.AG.RealizationReconstruction.FiniteAxisFoldNormalizedSignatureFiberProjection
import Formal.Util.AssertStandardAxioms

/-!
# Source presentation for the normalized signature-fiber section

The axis-table presentation is extended by one finite primitive carrying a
fiberwise permutation of the three signature coordinates.  Evaluation builds
the southwest geometry action and follows the fixed exact pull/top-transport
route.  A separate syntax operation applies canonical normalization and its
independently constructed raw section.

No constructor accepts a completed geometry morphism, automorphism, kernel
element, or coverage certificate.  The final equivalence preserves the
universal quantifier on the Cycle 69 axis kernel and reduces source coverage
exactly to the remaining signature-trivial kernel; it does not assert that
residual coverage holds.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory AtomFoundation DoctrineFiberProduct GeometryTransport
open CrossStageCoherence TransportCoherence FullGeometryNormalization

noncomputable section

local instance finiteAxisFoldSignatureFiberPresentationAtomDecidableEq :
    DecidableEq FiniteModel.carrier.Atom := by
  change DecidableEq FiniteModel.FiniteAtom
  infer_instance

/-- Retain every previous term and add a primitive finite signature-fiber
table plus a general normalization-section operation. -/
inductive FiniteAxisFoldSignatureFiberSyntax :
    G122GeneratedGeometryObject finiteAxisFoldG122FamilyInput →
      G122GeneratedGeometryObject finiteAxisFoldG122FamilyInput → Type 2
  | base {X Y} (term : FiniteAxisFoldAxisSwapSyntax X Y) :
      FiniteAxisFoldSignatureFiberSyntax X Y
  | signatureFiberDirect
      (permutation : FiniteAxisFoldSignatureFiberPermutation) :
      FiniteAxisFoldSignatureFiberSyntax
        (.direct finiteAxisFoldG122CellInput)
        (.direct finiteAxisFoldG122CellInput)
  | normalizeSectionDirect
      (term : FiniteAxisFoldSignatureFiberSyntax
        (.direct finiteAxisFoldG122CellInput)
        (.direct finiteAxisFoldG122CellInput)) :
      FiniteAxisFoldSignatureFiberSyntax
        (.direct finiteAxisFoldG122CellInput)
        (.direct finiteAxisFoldG122CellInput)
  | compose {X Y Z} (first : FiniteAxisFoldSignatureFiberSyntax X Y)
      (second : FiniteAxisFoldSignatureFiberSyntax Y Z) :
      FiniteAxisFoldSignatureFiberSyntax X Z

namespace FiniteAxisFoldSignatureFiberSyntax

/-- Evaluation of the new leaf uses only the Cycle 70 construction from the
original finite table. -/
noncomputable def evaluate {X Y} :
    FiniteAxisFoldSignatureFiberSyntax X Y →
      G122GeneratedGeometryObject.Hom finiteAxisFoldG122FamilyInput X Y
  | .base term => term.evaluate
  | .signatureFiberDirect permutation =>
      (finiteAxisFoldActualDirectSignatureFiberSectionHom permutation).hom.1
  | .normalizeSectionDirect term =>
      canonicalNormalizationGeometrySection
        finiteAxisFoldActualDirectAdmissibleGeometry.obj
        finiteAxisFoldActualDirectAdmissibleGeometry.property
        (((geometryNormalizationFunctor.{0, 0} FiniteModel.carrier).map
          (ObjectProperty.homMk term.evaluate)).f.hom)
  | .compose first second =>
      G122GeneratedGeometryObject.comp finiteAxisFoldG122FamilyInput
        first.evaluate second.evaluate

def size {X Y} : FiniteAxisFoldSignatureFiberSyntax X Y → Nat
  | .base term => term.size + 1
  | .signatureFiberDirect _ => 1
  | .normalizeSectionDirect term => term.size + 1
  | .compose first second => first.size + second.size + 1

theorem size_pos {X Y} (term : FiniteAxisFoldSignatureFiberSyntax X Y) :
    0 < term.size := by
  induction term with
  | base term => simp [size]
  | signatureFiberDirect permutation => simp [size]
  | normalizeSectionDirect term positive => simp [size]
  | compose first second firstPositive secondPositive =>
      simp only [size]
      omega

/-- Source and category laws only; decoder equality is not a constructor. -/
inductive Congruent : {X Y :
    G122GeneratedGeometryObject finiteAxisFoldG122FamilyInput} →
    FiniteAxisFoldSignatureFiberSyntax X Y →
    FiniteAxisFoldSignatureFiberSyntax X Y → Prop
  | refl {X Y} (term : FiniteAxisFoldSignatureFiberSyntax X Y) :
      Congruent term term
  | symm {X Y} {first second : FiniteAxisFoldSignatureFiberSyntax X Y} :
      Congruent first second → Congruent second first
  | trans {X Y} {first second third : FiniteAxisFoldSignatureFiberSyntax X Y} :
      Congruent first second → Congruent second third →
        Congruent first third
  | comp {W X Y} {first first' : FiniteAxisFoldSignatureFiberSyntax W X}
      {second second' : FiniteAxisFoldSignatureFiberSyntax X Y} :
      Congruent first first' → Congruent second second' →
        Congruent (.compose first second) (.compose first' second')
  | base {X Y} {first second : FiniteAxisFoldAxisSwapSyntax X Y} :
      FiniteAxisFoldAxisSwapSyntax.Congruent first second →
        Congruent (.base first) (.base second)
  | base_comp {X Y Z} (first : FiniteAxisFoldAxisSwapSyntax X Y)
      (second : FiniteAxisFoldAxisSwapSyntax Y Z) :
      Congruent (.compose (.base first) (.base second))
        (.base (.compose first second))
  | normalizeSectionDirect {first second : FiniteAxisFoldSignatureFiberSyntax
      (.direct finiteAxisFoldG122CellInput)
      (.direct finiteAxisFoldG122CellInput)} :
      Congruent first second →
        Congruent (.normalizeSectionDirect first)
          (.normalizeSectionDirect second)
  | id_comp {X Y} (term : FiniteAxisFoldSignatureFiberSyntax X Y) :
      Congruent
        (.compose (.base (.base (.base (.identity X)))) term) term
  | comp_id {X Y} (term : FiniteAxisFoldSignatureFiberSyntax X Y) :
      Congruent
        (.compose term (.base (.base (.base (.identity Y))))) term
  | assoc {W X Y Z} (first : FiniteAxisFoldSignatureFiberSyntax W X)
      (second : FiniteAxisFoldSignatureFiberSyntax X Y)
      (third : FiniteAxisFoldSignatureFiberSyntax Y Z) :
      Congruent (.compose (.compose first second) third)
        (.compose first (.compose second third))
  | signatureFiberDirect_inv
      (permutation : FiniteAxisFoldSignatureFiberPermutation) :
      Congruent
        (.compose (.signatureFiberDirect permutation)
          (.signatureFiberDirect permutation⁻¹))
        (.base (.base (.base
          (.identity (.direct finiteAxisFoldG122CellInput)))))
  | normalizedSignatureFiberDirect_inv
      (permutation : FiniteAxisFoldSignatureFiberPermutation) :
      Congruent
        (.compose
          (.normalizeSectionDirect (.signatureFiberDirect permutation))
          (.normalizeSectionDirect (.signatureFiberDirect permutation⁻¹)))
        (.base (.base (.base
          (.identity (.direct finiteAxisFoldG122CellInput)))))

theorem signatureFiberDirect_evaluate_comp_inverse
    (permutation : FiniteAxisFoldSignatureFiberPermutation) :
    G122GeneratedGeometryObject.comp finiteAxisFoldG122FamilyInput
        (evaluate (.signatureFiberDirect permutation))
        (evaluate (.signatureFiberDirect permutation⁻¹)) =
      G122GeneratedGeometryObject.id finiteAxisFoldG122FamilyInput
        (.direct finiteAxisFoldG122CellInput) := by
  change (finiteAxisFoldActualDirectSignatureFiberSectionHom permutation).hom.1 ≫
      (finiteAxisFoldActualDirectSignatureFiberSectionHom permutation⁻¹).hom.1 =
    𝟙 _
  exact congrArg Subtype.val
    (finiteAxisFoldActualDirectSignatureFiberSectionHom permutation).hom_inv_id

theorem normalizedSignatureFiberDirect_evaluate_comp_inverse
    (permutation : FiniteAxisFoldSignatureFiberPermutation) :
    G122GeneratedGeometryObject.comp finiteAxisFoldG122FamilyInput
        (evaluate (.normalizeSectionDirect
          (.signatureFiberDirect permutation)))
        (evaluate (.normalizeSectionDirect
          (.signatureFiberDirect permutation⁻¹))) =
      G122GeneratedGeometryObject.id finiteAxisFoldG122FamilyInput
        (.direct finiteAxisFoldG122CellInput) := by
  change (canonicalNormalizationAutomorphismSectionHom
      finiteAxisFoldActualDirectAdmissibleGeometry
      (finiteAxisFoldNormalizedSignatureFiberSectionHom permutation)).hom.hom ≫
    (canonicalNormalizationAutomorphismSectionHom
      finiteAxisFoldActualDirectAdmissibleGeometry
      (finiteAxisFoldNormalizedSignatureFiberSectionHom permutation)).inv.hom =
    𝟙 _
  exact congrArg
    (fun f : finiteAxisFoldActualDirectAdmissibleGeometry ⟶
      finiteAxisFoldActualDirectAdmissibleGeometry => f.hom)
    (canonicalNormalizationAutomorphismSectionHom
      finiteAxisFoldActualDirectAdmissibleGeometry
      (finiteAxisFoldNormalizedSignatureFiberSectionHom permutation)).hom_inv_id

theorem evaluate_eq_of_congruent {X Y}
    {first second : FiniteAxisFoldSignatureFiberSyntax X Y}
    (relation : Congruent first second) : first.evaluate = second.evaluate := by
  induction relation with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ firstIH secondIH => exact firstIH.trans secondIH
  | comp _ _ firstIH secondIH => simp only [evaluate]; rw [firstIH, secondIH]
  | base relation =>
      exact FiniteAxisFoldAxisSwapSyntax.evaluate_eq_of_congruent relation
  | base_comp first second => rfl
  | normalizeSectionDirect relation ih => simp only [evaluate]; rw [ih]
  | id_comp term => exact G122GeneratedGeometryObject.id_comp _ term.evaluate
  | comp_id term => exact G122GeneratedGeometryObject.comp_id _ term.evaluate
  | assoc first second third =>
      exact G122GeneratedGeometryObject.comp_assoc _ first.evaluate
        second.evaluate third.evaluate
  | signatureFiberDirect_inv permutation =>
      exact signatureFiberDirect_evaluate_comp_inverse permutation
  | normalizedSignatureFiberDirect_inv permutation =>
      exact normalizedSignatureFiberDirect_evaluate_comp_inverse permutation

end FiniteAxisFoldSignatureFiberSyntax

structure FiniteAxisFoldSignatureFiberPresentation where
  object : G122GeneratedGeometryObject finiteAxisFoldG122FamilyInput

namespace FiniteAxisFoldSignatureFiberPresentation

def ofObject (X : G122GeneratedGeometryObject finiteAxisFoldG122FamilyInput) :
    FiniteAxisFoldSignatureFiberPresentation := ⟨X⟩

def congruentSetoid (X Y :
    G122GeneratedGeometryObject finiteAxisFoldG122FamilyInput) :
    Setoid (FiniteAxisFoldSignatureFiberSyntax X Y) where
  r := FiniteAxisFoldSignatureFiberSyntax.Congruent
  iseqv :=
    { refl := FiniteAxisFoldSignatureFiberSyntax.Congruent.refl
      symm := FiniteAxisFoldSignatureFiberSyntax.Congruent.symm
      trans := FiniteAxisFoldSignatureFiberSyntax.Congruent.trans }

abbrev Hom (P Q : FiniteAxisFoldSignatureFiberPresentation) :=
  Quotient (congruentSetoid P.object Q.object)

def classOf {X Y} (term : FiniteAxisFoldSignatureFiberSyntax X Y) :
    Hom (ofObject X) (ofObject Y) := Quotient.mk _ term

def comp {P Q R : FiniteAxisFoldSignatureFiberPresentation}
    (first : Hom P Q) (second : Hom Q R) : Hom P R :=
  Quotient.liftOn₂ first second
    (fun firstTerm secondTerm => Quotient.mk _ (.compose firstTerm secondTerm))
    (by
      intro first first' second second' firstRelation secondRelation
      exact Quotient.sound (FiniteAxisFoldSignatureFiberSyntax.Congruent.comp
        firstRelation secondRelation))

instance : Category FiniteAxisFoldSignatureFiberPresentation where
  Hom := Hom
  id P := classOf (.base (.base (.base (.identity P.object))))
  comp := comp
  id_comp := by
    intro P Q f
    induction f using Quotient.inductionOn with
    | _ term =>
        exact Quotient.sound
          (FiniteAxisFoldSignatureFiberSyntax.Congruent.id_comp term)
  comp_id := by
    intro P Q f
    induction f using Quotient.inductionOn with
    | _ term =>
        exact Quotient.sound
          (FiniteAxisFoldSignatureFiberSyntax.Congruent.comp_id term)
  assoc := by
    intro W X Y Z f g h
    induction f using Quotient.inductionOn with
    | _ first =>
      induction g using Quotient.inductionOn with
      | _ second =>
        induction h using Quotient.inductionOn with
        | _ third =>
            exact Quotient.sound
              (FiniteAxisFoldSignatureFiberSyntax.Congruent.assoc
                first second third)

noncomputable def decoder : FiniteAxisFoldSignatureFiberPresentation ⥤
    G122GeneratedGeometryObject finiteAxisFoldG122FamilyInput where
  obj P := P.object
  map f := Quotient.liftOn f FiniteAxisFoldSignatureFiberSyntax.evaluate
    (fun _ _ relation =>
      FiniteAxisFoldSignatureFiberSyntax.evaluate_eq_of_congruent relation)
  map_id _ := rfl
  map_comp f g := by
    induction f using Quotient.inductionOn with
    | _ first =>
      induction g using Quotient.inductionOn with
      | _ second => rfl

noncomputable def directSignatureFiberAut
    (permutation : FiniteAxisFoldSignatureFiberPermutation) :
    Aut (ofObject (.direct finiteAxisFoldG122CellInput)) where
  hom := classOf (.signatureFiberDirect permutation)
  inv := classOf (.signatureFiberDirect permutation⁻¹)
  hom_inv_id := Quotient.sound
    (FiniteAxisFoldSignatureFiberSyntax.Congruent.signatureFiberDirect_inv
      permutation)
  inv_hom_id := by
    simpa using Quotient.sound
      (FiniteAxisFoldSignatureFiberSyntax.Congruent.signatureFiberDirect_inv
        permutation⁻¹)

noncomputable def sectionedDirectSignatureFiberAut
    (permutation : FiniteAxisFoldSignatureFiberPermutation) :
    Aut (ofObject (.direct finiteAxisFoldG122CellInput)) where
  hom := classOf
    (.normalizeSectionDirect (.signatureFiberDirect permutation))
  inv := classOf
    (.normalizeSectionDirect (.signatureFiberDirect permutation⁻¹))
  hom_inv_id := Quotient.sound
    (FiniteAxisFoldSignatureFiberSyntax.Congruent.normalizedSignatureFiberDirect_inv
      permutation)
  inv_hom_id := by
    simpa using Quotient.sound
      (FiniteAxisFoldSignatureFiberSyntax.Congruent.normalizedSignatureFiberDirect_inv
        permutation⁻¹)

/-- The outer presentation retains the previously constructed normalized
finite-axis source term for every primitive axis table. -/
noncomputable def sectionedDirectAxisPermutationAut
    (permutation : Equiv.Perm (Fin 3)) :
    Aut (ofObject (.direct finiteAxisFoldG122CellInput)) where
  hom := classOf (.base (.normalizeSectionDirect (.axisDirect permutation)))
  inv := classOf (.base (.normalizeSectionDirect (.axisDirect permutation.symm)))
  hom_inv_id := Quotient.sound
    (FiniteAxisFoldSignatureFiberSyntax.Congruent.trans
      (FiniteAxisFoldSignatureFiberSyntax.Congruent.base_comp _ _)
      (FiniteAxisFoldSignatureFiberSyntax.Congruent.base
        (FiniteAxisFoldAxisSwapSyntax.Congruent.normalizedAxisDirect_inv
          permutation)))
  inv_hom_id := by
    simpa using Quotient.sound
      (FiniteAxisFoldSignatureFiberSyntax.Congruent.trans
        (FiniteAxisFoldSignatureFiberSyntax.Congruent.base_comp _ _)
        (FiniteAxisFoldSignatureFiberSyntax.Congruent.base
          (FiniteAxisFoldAxisSwapSyntax.Congruent.normalizedAxisDirect_inv
            permutation.symm)))

theorem decoder_map_directSignatureFiberAut_hom
    (permutation : FiniteAxisFoldSignatureFiberPermutation) :
    decoder.map (directSignatureFiberAut permutation).hom =
      (finiteAxisFoldActualDirectSignatureFiberSectionHom permutation).hom.1 :=
  rfl

noncomputable def directAutomorphismEvaluationHom :
    Aut (ofObject (.direct finiteAxisFoldG122CellInput)) →*
      Aut finiteAxisFoldActualDirectAdmissibleGeometry where
  toFun automorphism :=
    { hom := ObjectProperty.homMk (decoder.map automorphism.hom)
      inv := ObjectProperty.homMk (decoder.map automorphism.inv)
      hom_inv_id := by
        apply ObjectProperty.hom_ext
        exact (decoder.mapIso automorphism).hom_inv_id
      inv_hom_id := by
        apply ObjectProperty.hom_ext
        exact (decoder.mapIso automorphism).inv_hom_id }
  map_one' := by
    apply Iso.ext
    apply ObjectProperty.hom_ext
    exact decoder.map_id _
  map_mul' first second := by
    apply Iso.ext
    apply ObjectProperty.hom_ext
    exact decoder.map_comp second.hom first.hom

theorem directSignatureFiberAut_evaluation
    (permutation : FiniteAxisFoldSignatureFiberPermutation) :
    directAutomorphismEvaluationHom (directSignatureFiberAut permutation) =
      finiteAxisFoldActualDirectAdmissibleAutomorphismHom
        (finiteAxisFoldActualDirectSignatureFiberSectionHom permutation) := by
  apply Iso.ext
  apply ObjectProperty.hom_ext
  rfl

theorem sectionedDirectSignatureFiberAut_evaluation
    (permutation : FiniteAxisFoldSignatureFiberPermutation) :
    directAutomorphismEvaluationHom
        (sectionedDirectSignatureFiberAut permutation) =
      canonicalNormalizationAutomorphismSectionHom
        finiteAxisFoldActualDirectAdmissibleGeometry
        (finiteAxisFoldNormalizedSignatureFiberSectionHom permutation) := by
  apply Iso.ext
  apply ObjectProperty.hom_ext
  rfl

/-- Evaluation of the retained axis term is the independently constructed
canonical normalization section of the corresponding primitive axis action. -/
theorem sectionedDirectAxisPermutationAut_evaluation
    (permutation : Equiv.Perm (Fin 3)) :
    directAutomorphismEvaluationHom
        (sectionedDirectAxisPermutationAut permutation) =
      canonicalNormalizationAutomorphismSectionHom
        finiteAxisFoldActualDirectAdmissibleGeometry
        (finiteAxisFoldNormalizedAxisSectionHom permutation) := by
  apply Iso.ext
  apply ObjectProperty.hom_ext
  rfl

def SignatureFiberSourceCovered
    (automorphism : Aut FiniteAxisFoldNormalizedDirectGeometry) : Prop :=
  ∃ sourceAutomorphism :
      Aut (ofObject (.direct finiteAxisFoldG122CellInput)),
    directAutomorphismEvaluationHom sourceAutomorphism =
      canonicalNormalizationAutomorphismSectionHom
        finiteAxisFoldActualDirectAdmissibleGeometry automorphism

theorem finiteAxisFoldSignatureFiber_canonicalSection_sourceCovered
    (permutation : FiniteAxisFoldSignatureFiberPermutation) :
    SignatureFiberSourceCovered
      (finiteAxisFoldNormalizedSignatureFiberSectionHom permutation) :=
  ⟨sectionedDirectSignatureFiberAut permutation,
    sectionedDirectSignatureFiberAut_evaluation permutation⟩

/-- Universal axis-kernel coverage is exactly residual signature-kernel
coverage.  The latter remains an explicit obligation. -/
theorem finiteAxisFoldAxisKernel_sourceCovered_all_iff_signatureKernel :
    (∀ remainder : FiniteAxisFoldNormalizedAxisKernel,
      SignatureFiberSourceCovered remainder.1) ↔
    (∀ remainder : FiniteAxisFoldNormalizedAxisSignatureKernel,
      SignatureFiberSourceCovered remainder.1.1) := by
  constructor
  · intro coverage remainder
    exact coverage remainder.1
  · intro kernelCoverage remainder
    obtain ⟨kernelSource, kernelSource_evaluation⟩ :=
      kernelCoverage
        (finiteAxisFoldNormalizedAxisSignatureKernelRemainder remainder)
    let permutation :=
      finiteAxisFoldNormalizedAxisKernelSignatureProjection remainder
    refine ⟨kernelSource * sectionedDirectSignatureFiberAut permutation, ?_⟩
    rw [map_mul, kernelSource_evaluation,
      sectionedDirectSignatureFiberAut_evaluation]
    rw [← map_mul]
    apply congrArg
      (canonicalNormalizationAutomorphismSectionHom
        finiteAxisFoldActualDirectAdmissibleGeometry)
    exact congrArg Subtype.val
      (finiteAxisFoldNormalizedAxisSignatureKernelRemainder_mul_section
        remainder)

/-- Combining the retained axis terms with the signature-fiber terms reduces
source coverage of every normalized endpoint automorphism exactly to coverage
of the residual axis-and-signature-trivial kernel. -/
theorem finiteAxisFoldAll_sourceCovered_iff_signatureKernel :
    (∀ automorphism : Aut FiniteAxisFoldNormalizedDirectGeometry,
      SignatureFiberSourceCovered automorphism) ↔
    (∀ remainder : FiniteAxisFoldNormalizedAxisSignatureKernel,
      SignatureFiberSourceCovered remainder.1.1) := by
  constructor
  · intro coverage remainder
    exact coverage remainder.1.1
  · intro kernelCoverage automorphism
    have axisKernelCoverage :
        ∀ remainder : FiniteAxisFoldNormalizedAxisKernel,
          SignatureFiberSourceCovered remainder.1 :=
      finiteAxisFoldAxisKernel_sourceCovered_all_iff_signatureKernel.mpr
        kernelCoverage
    obtain ⟨kernelSource, kernelSource_evaluation⟩ :=
      axisKernelCoverage
        (finiteAxisFoldNormalizedAxisKernelRemainder automorphism)
    let permutation := finiteAxisFoldNormalizedAxisProjection automorphism
    refine ⟨kernelSource * sectionedDirectAxisPermutationAut permutation, ?_⟩
    rw [map_mul, kernelSource_evaluation,
      sectionedDirectAxisPermutationAut_evaluation]
    rw [← map_mul]
    apply congrArg
      (canonicalNormalizationAutomorphismSectionHom
        finiteAxisFoldActualDirectAdmissibleGeometry)
    exact finiteAxisFoldNormalizedAxisKernelRemainder_mul_section automorphism

end FiniteAxisFoldSignatureFiberPresentation

end

end AAT.AG.RealizationReconstruction

#assert_standard_axioms_only AAT.AG.RealizationReconstruction
