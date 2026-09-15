import ResearchLean.AG.RealizationReconstruction.G122GeneratedComparisonGroup
import Formal.Util.AssertStandardAxioms

/-!
# Adding the fixed ambient generators to the finite-axis-fold presentation

The source-law comparison syntax does not yet contain the ambient endpoint
involutions constructed in Cycle 56.  This file extends that syntax for the
mandated finite axis-fold input with two nullary, endpoint-typed leaves.  The
new leaves carry neither completed automorphisms nor group elements; their
evaluation is the previously constructed two-tag ambient recipe.

The congruence is generated from the earlier source laws, the category laws,
and the two source-proved involution laws.  It is not defined by equality after
evaluation.  Its quotient therefore supplies actual displayed automorphisms.
The direct one is nonidentity by decoder reflection of equality.  Conjugating
it across the displayed `barAlpha` gives a nontrivial element of the displayed
comparison group, whose decoder is an actual raw comparison-preserving pair.

This proves concrete nonvacuity and adds a source presentation for one lost
endpoint change.  It does not show that this extended syntax covers every
semantic automorphism, normalized comparison, restriction-kernel element, or
lift fiber.

## Implementation notes

The extension is specialized to the mandated finite-axis-fold input.  The
`base` constructor retains every term of the earlier syntax, while the two new
nullary leaves evaluate the already constructed Cycle 56 recipes.  No claim is
made that the induced map from the earlier quotient is faithful: the result
used here is the new quotient's sound decoder and its explicit ambient
automorphism.  Raw comparison membership is constructed only after the
presentation-side conjugation section has produced the displayed pair.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory AtomFoundation DoctrineFiberProduct GeometryTransport
open TransportCoherence FullGeometryNormalization

noncomputable section

/-- Decidable atom equality for the fixed finite-axis-fold input. -/
local instance finiteAxisFoldKernelExtendedAtomDecidableEq :
    DecidableEq FiniteModel.carrier.Atom := by
  change DecidableEq FiniteModel.FiniteAtom
  infer_instance

/-- Fixed source syntax extended by the two Cycle 56 endpoint recipes. -/
inductive FiniteAxisFoldKernelExtendedSyntax :
    G122GeneratedGeometryObject finiteAxisFoldG122FamilyInput →
      G122GeneratedGeometryObject finiteAxisFoldG122FamilyInput → Type 2
  | base {X Y}
      (term : G122GeneratedComparisonSyntax finiteAxisFoldG122FamilyInput X Y) :
      FiniteAxisFoldKernelExtendedSyntax X Y
  | ambientDirect : FiniteAxisFoldKernelExtendedSyntax
      (.direct finiteAxisFoldG122CellInput)
      (.direct finiteAxisFoldG122CellInput)
  | ambientViaBase : FiniteAxisFoldKernelExtendedSyntax
      (.viaBase finiteAxisFoldG122CellInput)
      (.viaBase finiteAxisFoldG122CellInput)
  | compose {X Y Z}
      (first : FiniteAxisFoldKernelExtendedSyntax X Y)
      (second : FiniteAxisFoldKernelExtendedSyntax Y Z) :
      FiniteAxisFoldKernelExtendedSyntax X Z

namespace FiniteAxisFoldKernelExtendedSyntax

/-- Evaluate the extended finite syntax in the independently defined category
of all complete-geometry morphisms between the fixed generated objects. -/
noncomputable def evaluate {X Y} :
    FiniteAxisFoldKernelExtendedSyntax X Y →
      G122GeneratedGeometryObject.Hom finiteAxisFoldG122FamilyInput X Y
  | .base term => term.evaluate
  | .ambientDirect => FiniteAxisFoldAmbientKernelCode.direct.evaluate
  | .ambientViaBase => FiniteAxisFoldAmbientKernelCode.viaBase.evaluate
  | .compose first second =>
      G122GeneratedGeometryObject.comp finiteAxisFoldG122FamilyInput
        first.evaluate second.evaluate

/-- Every extended expression remains a finite syntax tree. -/
def size {X Y} : FiniteAxisFoldKernelExtendedSyntax X Y → Nat
  | .base term => term.size + 1
  | .ambientDirect => 1
  | .ambientViaBase => 1
  | .compose first second => first.size + second.size + 1

/-- Every extended syntax term has at least one node. -/
theorem size_pos {X Y} (term : FiniteAxisFoldKernelExtendedSyntax X Y) :
    0 < term.size := by
  induction term with
  | base term => simp [size]
  | ambientDirect => simp [size]
  | ambientViaBase => simp [size]
  | compose first second firstPositive secondPositive =>
      simp only [size]
      omega

/-- Source-generated congruence for the extension.  Semantic equality is not
a constructor. -/
inductive Congruent : {X Y :
    G122GeneratedGeometryObject finiteAxisFoldG122FamilyInput} →
    FiniteAxisFoldKernelExtendedSyntax X Y →
    FiniteAxisFoldKernelExtendedSyntax X Y → Prop
  | refl {X Y} (term : FiniteAxisFoldKernelExtendedSyntax X Y) :
      Congruent term term
  | symm {X Y} {first second : FiniteAxisFoldKernelExtendedSyntax X Y} :
      Congruent first second → Congruent second first
  | trans {X Y} {first second third : FiniteAxisFoldKernelExtendedSyntax X Y} :
      Congruent first second → Congruent second third → Congruent first third
  | comp {W X Y} {first first' : FiniteAxisFoldKernelExtendedSyntax W X}
      {second second' : FiniteAxisFoldKernelExtendedSyntax X Y} :
      Congruent first first' → Congruent second second' →
        Congruent (.compose first second) (.compose first' second')
  | base {X Y} {first second :
      G122GeneratedComparisonSyntax finiteAxisFoldG122FamilyInput X Y} :
      G122GeneratedComparisonSyntax.Congruent first second →
        Congruent (.base first) (.base second)
  | base_comp {X Y Z}
      (first : G122GeneratedComparisonSyntax
        finiteAxisFoldG122FamilyInput X Y)
      (second : G122GeneratedComparisonSyntax
        finiteAxisFoldG122FamilyInput Y Z) :
      Congruent (.compose (.base first) (.base second))
        (.base (.compose first second))
  | id_comp {X Y} (term : FiniteAxisFoldKernelExtendedSyntax X Y) :
      Congruent (.compose (.base (.identity X)) term) term
  | comp_id {X Y} (term : FiniteAxisFoldKernelExtendedSyntax X Y) :
      Congruent (.compose term (.base (.identity Y))) term
  | assoc {W X Y Z}
      (first : FiniteAxisFoldKernelExtendedSyntax W X)
      (second : FiniteAxisFoldKernelExtendedSyntax X Y)
      (third : FiniteAxisFoldKernelExtendedSyntax Y Z) :
      Congruent (.compose (.compose first second) third)
        (.compose first (.compose second third))
  | ambientDirect_sq :
      Congruent (.compose .ambientDirect .ambientDirect)
        (.base (.identity (.direct finiteAxisFoldG122CellInput)))
  | ambientViaBase_sq :
      Congruent (.compose .ambientViaBase .ambientViaBase)
        (.base (.identity (.viaBase finiteAxisFoldG122CellInput)))

/-- Every source-generated extended congruence is sound for evaluation. -/
theorem evaluate_eq_of_congruent {X Y}
    {first second : FiniteAxisFoldKernelExtendedSyntax X Y}
    (relation : Congruent first second) : first.evaluate = second.evaluate := by
  induction relation with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ firstIH secondIH => exact firstIH.trans secondIH
  | comp _ _ firstIH secondIH =>
      simp only [evaluate]
      rw [firstIH, secondIH]
  | base relation =>
      exact G122GeneratedComparisonSyntax.evaluate_eq_of_congruent relation
  | base_comp first second => rfl
  | id_comp term => exact G122GeneratedGeometryObject.id_comp _ term.evaluate
  | comp_id term => exact G122GeneratedGeometryObject.comp_id _ term.evaluate
  | assoc first second third =>
      exact G122GeneratedGeometryObject.comp_assoc _ first.evaluate
        second.evaluate third.evaluate
  | ambientDirect_sq =>
      exact FiniteAxisFoldAmbientKernelCode.direct.evaluate_comp_self
  | ambientViaBase_sq =>
      exact FiniteAxisFoldAmbientKernelCode.viaBase.evaluate_comp_self

/-- The new direct ambient leaf is not source-congruent to the retained
identity term.  This is a fixed negative instance for the generated
congruence, obtained from semantic soundness and the independently proved
Cycle 56 nonidentity result. -/
theorem ambientDirect_not_congruent_identity :
    ¬ Congruent (.ambientDirect)
      (.base (.identity (.direct finiteAxisFoldG122CellInput))) := by
  intro relation
  exact FiniteAxisFoldAmbientKernelCode.direct.evaluate_ne_identity (by
    simpa using evaluate_eq_of_congruent relation)

end FiniteAxisFoldKernelExtendedSyntax

/-- Objects of the extended presentation retain the original generated G-122
objects; the extension changes only the available finite arrows. -/
structure FiniteAxisFoldKernelExtendedPresentation where
  /-- The retained generated G-122 object represented by this display object. -/
  object : G122GeneratedGeometryObject finiteAxisFoldG122FamilyInput

namespace FiniteAxisFoldKernelExtendedPresentation

/-- Regard a fixed generated G-122 object as an object of the extension. -/
def ofObject (X : G122GeneratedGeometryObject finiteAxisFoldG122FamilyInput) :
    FiniteAxisFoldKernelExtendedPresentation := ⟨X⟩

/-- The source-generated equivalence relation used on each extended Hom type. -/
def congruentSetoid (X Y :
    G122GeneratedGeometryObject finiteAxisFoldG122FamilyInput) :
    Setoid (FiniteAxisFoldKernelExtendedSyntax X Y) where
  r := FiniteAxisFoldKernelExtendedSyntax.Congruent
  iseqv :=
    { refl := FiniteAxisFoldKernelExtendedSyntax.Congruent.refl
      symm := FiniteAxisFoldKernelExtendedSyntax.Congruent.symm
      trans := FiniteAxisFoldKernelExtendedSyntax.Congruent.trans }

/-- Morphisms are extended syntax terms modulo the source-generated laws. -/
abbrev Hom (P Q : FiniteAxisFoldKernelExtendedPresentation) :=
  Quotient (congruentSetoid P.object Q.object)

/-- Insert an extended syntax term into its quotient Hom type. -/
def classOf {X Y} (term : FiniteAxisFoldKernelExtendedSyntax X Y) :
    Hom (ofObject X) (ofObject Y) := Quotient.mk _ term

/-- Compose quotient morphisms by composing representatives. -/
def comp {P Q R : FiniteAxisFoldKernelExtendedPresentation}
    (first : Hom P Q) (second : Hom Q R) : Hom P R :=
  Quotient.liftOn₂ first second
    (fun firstTerm secondTerm => Quotient.mk _ (.compose firstTerm secondTerm))
    (by
      intro first first' second second' firstRelation secondRelation
      exact Quotient.sound
        (FiniteAxisFoldKernelExtendedSyntax.Congruent.comp firstRelation
          secondRelation))

/-- Category structure induced by the explicit category-law constructors of
the source congruence. -/
instance : Category FiniteAxisFoldKernelExtendedPresentation where
  Hom := Hom
  id P := classOf (.base (.identity P.object))
  comp := comp
  id_comp := by
    intro P Q f
    induction f using Quotient.inductionOn with
    | _ term =>
        exact Quotient.sound
          (FiniteAxisFoldKernelExtendedSyntax.Congruent.id_comp term)
  comp_id := by
    intro P Q f
    induction f using Quotient.inductionOn with
    | _ term =>
        exact Quotient.sound
          (FiniteAxisFoldKernelExtendedSyntax.Congruent.comp_id term)
  assoc := by
    intro P Q R S f g h
    induction f using Quotient.inductionOn with
    | _ first =>
      induction g using Quotient.inductionOn with
      | _ second =>
        induction h using Quotient.inductionOn with
        | _ third =>
          exact Quotient.sound
            (FiniteAxisFoldKernelExtendedSyntax.Congruent.assoc
              first second third)

/-- Decode the extended quotient without using semantic equality to define
its congruence. -/
noncomputable def decoder : FiniteAxisFoldKernelExtendedPresentation ⥤
    G122GeneratedGeometryObject finiteAxisFoldG122FamilyInput where
  obj P := P.object
  map f := Quotient.liftOn f FiniteAxisFoldKernelExtendedSyntax.evaluate
    (fun _ _ relation =>
      FiniteAxisFoldKernelExtendedSyntax.evaluate_eq_of_congruent relation)
  map_id _ := rfl
  map_comp f g := by
    induction f using Quotient.inductionOn with
    | _ first =>
      induction g using Quotient.inductionOn with
      | _ second => rfl

/-- The fixed source-constructed comparison remains an isomorphism in the
extended quotient. -/
noncomputable def barAlphaIso :
    ofObject (.direct finiteAxisFoldG122CellInput) ≅
      ofObject (.viaBase finiteAxisFoldG122CellInput) where
  hom := classOf (.base (.barAlpha finiteAxisFoldG122CellInput))
  inv := classOf (.base (.barAlphaInv finiteAxisFoldG122CellInput))
  hom_inv_id := Quotient.sound
    (FiniteAxisFoldKernelExtendedSyntax.Congruent.trans
      (FiniteAxisFoldKernelExtendedSyntax.Congruent.base_comp
        (.barAlpha finiteAxisFoldG122CellInput)
        (.barAlphaInv finiteAxisFoldG122CellInput))
      (FiniteAxisFoldKernelExtendedSyntax.Congruent.base
        (G122GeneratedComparisonSyntax.Congruent.barAlpha_hom_inv
          finiteAxisFoldG122CellInput)))
  inv_hom_id := Quotient.sound
    (FiniteAxisFoldKernelExtendedSyntax.Congruent.trans
      (FiniteAxisFoldKernelExtendedSyntax.Congruent.base_comp
        (.barAlphaInv finiteAxisFoldG122CellInput)
        (.barAlpha finiteAxisFoldG122CellInput))
      (FiniteAxisFoldKernelExtendedSyntax.Congruent.base
        (G122GeneratedComparisonSyntax.Congruent.barAlpha_inv_hom
          finiteAxisFoldG122CellInput)))

/-- The direct ambient recipe is an actual automorphism in the extended
presentation. -/
noncomputable def directAmbientAut :
    Aut (ofObject (.direct finiteAxisFoldG122CellInput)) where
  hom := classOf .ambientDirect
  inv := classOf .ambientDirect
  hom_inv_id := Quotient.sound
    FiniteAxisFoldKernelExtendedSyntax.Congruent.ambientDirect_sq
  inv_hom_id := Quotient.sound
    FiniteAxisFoldKernelExtendedSyntax.Congruent.ambientDirect_sq

/-- The via-base ambient recipe is likewise represented as an involution. -/
noncomputable def viaBaseAmbientAut :
    Aut (ofObject (.viaBase finiteAxisFoldG122CellInput)) where
  hom := classOf .ambientViaBase
  inv := classOf .ambientViaBase
  hom_inv_id := Quotient.sound
    FiniteAxisFoldKernelExtendedSyntax.Congruent.ambientViaBase_sq
  inv_hom_id := Quotient.sound
    FiniteAxisFoldKernelExtendedSyntax.Congruent.ambientViaBase_sq

/-- The new direct displayed automorphism is not the identity.  Otherwise its
decoder would identify the nontrivial Cycle 56 evaluation with identity. -/
theorem directAmbientAut_ne_one : directAmbientAut ≠ 1 := by
  intro equality
  have homEquality := congrArg Iso.hom equality
  have mapped := congrArg (fun f => decoder.map f) homEquality
  exact FiniteAxisFoldAmbientKernelCode.direct.evaluate_ne_identity (by
    simpa [directAmbientAut] using mapped)

/-- The extended displayed comparison group for the same fixed `barAlpha`. -/
noncomputable abbrev ComparisonSubgroup :=
  GeneratedArrowComparisonSubgroup barAlphaIso.hom

/-- A nontrivial displayed comparison element obtained from the direct
ambient recipe by the all-elements source-conjugation section. -/
noncomputable def ambientComparisonElement : ComparisonSubgroup :=
  generatedArrowComparisonSectionHom barAlphaIso directAmbientAut

/-- The source component of the selected displayed comparison is nonidentity. -/
theorem ambientComparisonElement_source_ne_one :
    ambientComparisonElement.1.1 ≠ 1 :=
  directAmbientAut_ne_one

/-- Decode every extended direct-endpoint automorphism into the exact
admissible direct endpoint. -/
noncomputable def directAutomorphismEvaluationHom :
    Aut (ofObject (.direct finiteAxisFoldG122CellInput)) →*
      Aut (authoredExactDirectAdmissibleGeometryAt
        finiteAxisFoldBCDatumSquare
        (Discrete.mk DoubleDiamondTwoCell.second)
        Int
        (finiteAxisFoldFixedCoefficientGeometryFamily
          (Discrete.mk DoubleDiamondTwoCell.second))
        finiteCanonicalObjectNormalization_admissible) where
  toFun a :=
    { hom := ObjectProperty.homMk (decoder.map a.hom)
      inv := ObjectProperty.homMk (decoder.map a.inv)
      hom_inv_id := by
        apply ObjectProperty.hom_ext
        exact (decoder.mapIso a).hom_inv_id
      inv_hom_id := by
        apply ObjectProperty.hom_ext
        exact (decoder.mapIso a).inv_hom_id }
  map_one' := by
    apply Iso.ext
    apply ObjectProperty.hom_ext
    exact decoder.map_id _
  map_mul' a b := by
    apply Iso.ext
    apply ObjectProperty.hom_ext
    exact decoder.map_comp b.hom a.hom

/-- Decode every extended via-base-endpoint automorphism into the exact
admissible via-base endpoint. -/
noncomputable def viaBaseAutomorphismEvaluationHom :
    Aut (ofObject (.viaBase finiteAxisFoldG122CellInput)) →*
      Aut (authoredExactViaBaseAdmissibleGeometryAt
        finiteAxisFoldBCDatumSquare
        (Discrete.mk DoubleDiamondTwoCell.second)
        Int
        (finiteAxisFoldFixedCoefficientGeometryFamily
          (Discrete.mk DoubleDiamondTwoCell.second))
        finiteCanonicalObjectNormalization_admissible) where
  toFun a :=
    { hom := ObjectProperty.homMk (decoder.map a.hom)
      inv := ObjectProperty.homMk (decoder.map a.inv)
      hom_inv_id := by
        apply ObjectProperty.hom_ext
        exact (decoder.mapIso a).hom_inv_id
      inv_hom_id := by
        apply ObjectProperty.hom_ext
        exact (decoder.mapIso a).inv_hom_id }
  map_one' := by
    apply Iso.ext
    apply ObjectProperty.hom_ext
    exact decoder.map_id _
  map_mul' a b := by
    apply Iso.ext
    apply ObjectProperty.hom_ext
    exact decoder.map_comp b.hom a.hom

/-- Every commuting square in the extended presentation decodes to a square
preserving the actual fixed `barAlpha`. -/
theorem endpointAutomorphisms_preserve_actualBarAlpha
    (pair : Aut (ofObject (.direct finiteAxisFoldG122CellInput)) ×
      Aut (ofObject (.viaBase finiteAxisFoldG122CellInput)))
    (preserves : pair ∈ ComparisonSubgroup) :
    (directAutomorphismEvaluationHom pair.1,
        viaBaseAutomorphismEvaluationHom pair.2) ∈
      rawGeometryNormalizationComparisonSubgroup
        (authoredExactBarAlphaAdmissibleIsoAt
          finiteAxisFoldBCDatumSquare
          (Discrete.mk DoubleDiamondTwoCell.second)
          Int
          (finiteAxisFoldFixedCoefficientGeometryFamily
            (Discrete.mk DoubleDiamondTwoCell.second))
          finiteCanonicalObjectNormalization_admissible).hom := by
  change (directAutomorphismEvaluationHom pair.1).hom ≫ _ =
    _ ≫ (viaBaseAutomorphismEvaluationHom pair.2).hom
  apply ObjectProperty.hom_ext
  have mapped := congrArg (fun f => decoder.map f) preserves
  simpa [directAutomorphismEvaluationHom,
    viaBaseAutomorphismEvaluationHom] using mapped

/-- Evaluate the entire extended displayed comparison group in the actual
raw G-122 comparison group. -/
noncomputable def comparisonEvaluationHom : ComparisonSubgroup →*
    rawGeometryNormalizationComparisonSubgroup
      (authoredExactBarAlphaAdmissibleIsoAt
        finiteAxisFoldBCDatumSquare
        (Discrete.mk DoubleDiamondTwoCell.second)
        Int
        (finiteAxisFoldFixedCoefficientGeometryFamily
          (Discrete.mk DoubleDiamondTwoCell.second))
        finiteCanonicalObjectNormalization_admissible).hom where
  toFun pair :=
    ⟨(directAutomorphismEvaluationHom pair.1.1,
        viaBaseAutomorphismEvaluationHom pair.1.2),
      endpointAutomorphisms_preserve_actualBarAlpha pair.1 pair.2⟩
  map_one' := by
    apply Subtype.ext
    apply Prod.ext
    · exact map_one directAutomorphismEvaluationHom
    · exact map_one viaBaseAutomorphismEvaluationHom
  map_mul' a b := by
    apply Subtype.ext
    apply Prod.ext
    · exact map_mul directAutomorphismEvaluationHom a.1.1 b.1.1
    · exact map_mul viaBaseAutomorphismEvaluationHom a.1.2 b.1.2

/-- The chosen nontrivial displayed group element evaluates at its source to
the exact Cycle 56 ambient recipe. -/
theorem ambientComparisonElement_evaluation_source :
    (comparisonEvaluationHom ambientComparisonElement).1.1 =
      FiniteAxisFoldAmbientKernelCode.direct.admissibleEvaluateAut := by
  apply Iso.ext
  apply ObjectProperty.hom_ext
  rfl

/-- Hence the displayed nontrivial element remains nontrivial in the actual
raw comparison group; it is not a merely syntactic distinction. -/
theorem ambientComparisonElement_evaluation_source_ne_one :
    (comparisonEvaluationHom ambientComparisonElement).1.1 ≠ 1 := by
  rw [ambientComparisonElement_evaluation_source]
  exact FiniteAxisFoldAmbientKernelCode.direct.admissibleEvaluateAut_ne_one

/-- Raw comparison preservation forces the conjugated target component to be
nonidentity as well. -/
theorem ambientComparisonElement_evaluation_target_ne_one :
    (comparisonEvaluationHom ambientComparisonElement).1.2 ≠ 1 := by
  intro targetIdentity
  have preserves := (comparisonEvaluationHom ambientComparisonElement).2
  have targetHomIdentity :
      (comparisonEvaluationHom ambientComparisonElement).1.2.hom = 𝟙 _ :=
    congrArg Iso.hom targetIdentity
  have preservesWithIdentity :
      (comparisonEvaluationHom ambientComparisonElement).1.1.hom ≫
          (authoredExactBarAlphaAdmissibleIsoAt
            finiteAxisFoldBCDatumSquare
            (Discrete.mk DoubleDiamondTwoCell.second)
            Int
            (finiteAxisFoldFixedCoefficientGeometryFamily
              (Discrete.mk DoubleDiamondTwoCell.second))
            finiteCanonicalObjectNormalization_admissible).hom =
        (authoredExactBarAlphaAdmissibleIsoAt
          finiteAxisFoldBCDatumSquare
          (Discrete.mk DoubleDiamondTwoCell.second)
          Int
          (finiteAxisFoldFixedCoefficientGeometryFamily
            (Discrete.mk DoubleDiamondTwoCell.second))
          finiteCanonicalObjectNormalization_admissible).hom := by
    calc
      _ = (authoredExactBarAlphaAdmissibleIsoAt
            finiteAxisFoldBCDatumSquare
            (Discrete.mk DoubleDiamondTwoCell.second)
            Int
            (finiteAxisFoldFixedCoefficientGeometryFamily
              (Discrete.mk DoubleDiamondTwoCell.second))
            finiteCanonicalObjectNormalization_admissible).hom ≫
          (comparisonEvaluationHom ambientComparisonElement).1.2.hom :=
        preserves
      _ = _ := by rw [targetHomIdentity, Category.comp_id]
  have sourceHomIdentity :
      (comparisonEvaluationHom ambientComparisonElement).1.1.hom = 𝟙 _ := by
    apply (cancel_mono (authoredExactBarAlphaAdmissibleIsoAt
      finiteAxisFoldBCDatumSquare
      (Discrete.mk DoubleDiamondTwoCell.second)
      Int
      (finiteAxisFoldFixedCoefficientGeometryFamily
        (Discrete.mk DoubleDiamondTwoCell.second))
      finiteCanonicalObjectNormalization_admissible).hom).1
    simpa using preservesWithIdentity
  have sourceIdentity :
      (comparisonEvaluationHom ambientComparisonElement).1.1 = 1 := by
    apply Iso.ext
    exact sourceHomIdentity
  exact ambientComparisonElement_evaluation_source_ne_one sourceIdentity

/-- The comparison-preserving pair uses the same ambient source involution as
Cycle 57 but a forced nonidentity target conjugate, so it is not the ambient
pair with trivial target that failed raw comparison preservation. -/
theorem ambientComparisonElement_evaluation_ne_ambientPair :
    (comparisonEvaluationHom ambientComparisonElement).1 ≠
      finiteAxisFoldDisplayedAmbientKernelComparisonPair := by
  intro pairEquality
  have targetEquality := congrArg Prod.snd pairEquality
  exact ambientComparisonElement_evaluation_target_ne_one (by
    simpa [finiteAxisFoldDisplayedAmbientKernelComparisonPair] using
      targetEquality)

end FiniteAxisFoldKernelExtendedPresentation

end


end AAT.AG.RealizationReconstruction

#assert_standard_axioms_only AAT.AG.RealizationReconstruction
