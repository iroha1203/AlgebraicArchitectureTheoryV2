import ResearchLean.AG.RealizationReconstruction.G122GeneratedComparisonCongruence
import Formal.Util.AssertStandardAxioms

/-!
# Quotient category for source-generated G-122 comparisons

This module forms the typed quotient of the Cycle 51 comparison syntax by the
Cycle 52 source-law congruence.  The relation was generated independently of
semantic evaluation; semantic soundness is used afterwards to descend the
decoder to the quotient and to certify the fixed negative instance.

The quotient category keeps the exact generated G-122 objects as object data.
Its arrows are finite syntax classes, composition is induced by typed syntax
composition, and the category laws follow from the corresponding source-law
congruence constructors.  The decoder lands in the independently defined
category containing every complete geometry morphism between those objects.

## Implementation notes

The object wrapper prevents this finite-presentation category from replacing
the pre-existing complete-Hom category on `G122GeneratedGeometryObject`.
Neither quotient equality nor a syntax constructor accepts equality of decoded
morphisms.  The fixed positive and negative instances show respectively that a
source law is imposed and that semantic soundness does not collapse the target
projector to the identity.  No fullness, faithfulness, or completeness of the
source-law congruence is asserted.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory

universe u v

/-- An object of the generated-comparison presentation.  It retains the exact
source-generated object rather than replacing it by a decoded image object. -/
structure G122GeneratedComparisonPresentation
    (Θ : G122FamilyInput.{u, v}) where
  /-- The original generated G-122 object represented by this syntax object. -/
  object : G122GeneratedGeometryObject Θ

namespace G122GeneratedComparisonPresentation

/-- Embed an exact generated G-122 object as a presentation object. -/
def ofObject {Θ : G122FamilyInput.{u, v}}
    (X : G122GeneratedGeometryObject Θ) :
    G122GeneratedComparisonPresentation Θ :=
  ⟨X⟩

/-- The source-law congruence as a setoid on one fixed typed syntax Hom. -/
def congruentSetoid {Θ : G122FamilyInput.{u, v}}
    (X Y : G122GeneratedGeometryObject Θ) :
    Setoid (G122GeneratedComparisonSyntax Θ X Y) where
  r := G122GeneratedComparisonSyntax.Congruent
  iseqv :=
    { refl := G122GeneratedComparisonSyntax.Congruent.refl
      symm := G122GeneratedComparisonSyntax.Congruent.symm
      trans := G122GeneratedComparisonSyntax.Congruent.trans }

/-- Finite generated-comparison terms modulo only the source-law congruence. -/
abbrev Hom {Θ : G122FamilyInput.{u, v}}
    (P Q : G122GeneratedComparisonPresentation Θ) :=
  Quotient (congruentSetoid P.object Q.object)

/-- Insert a typed source-provenanced term into the quotient Hom. -/
def classOf {Θ : G122FamilyInput.{u, v}}
    {X Y : G122GeneratedGeometryObject Θ}
    (term : G122GeneratedComparisonSyntax Θ X Y) :
    Hom (ofObject X) (ofObject Y) :=
  Quotient.mk _ term

/-- Quotient composition induced by finite typed syntax composition. -/
def comp {Θ : G122FamilyInput.{u, v}}
    {P Q R : G122GeneratedComparisonPresentation Θ}
    (first : Hom P Q) (second : Hom Q R) : Hom P R :=
  Quotient.liftOn₂ first second
    (fun firstTerm secondTerm =>
      Quotient.mk _ (.compose firstTerm secondTerm))
    (by
      intro firstTerm firstTerm' secondTerm secondTerm' firstRelation
        secondRelation
      exact Quotient.sound
        (G122GeneratedComparisonSyntax.Congruent.comp firstRelation
          secondRelation))

/-- The source-generated syntax quotient forms a category. -/
instance {Θ : G122FamilyInput.{u, v}} :
    Category (G122GeneratedComparisonPresentation Θ) where
  Hom := Hom
  id P := classOf (.identity P.object)
  comp := comp
  id_comp := by
    intro P Q f
    induction f using Quotient.inductionOn with
    | _ term =>
        exact Quotient.sound
          (G122GeneratedComparisonSyntax.Congruent.id_comp term)
  comp_id := by
    intro P Q f
    induction f using Quotient.inductionOn with
    | _ term =>
        exact Quotient.sound
          (G122GeneratedComparisonSyntax.Congruent.comp_id term)
  assoc := by
    intro P Q R S f g h
    induction f using Quotient.inductionOn with
    | _ first =>
      induction g using Quotient.inductionOn with
      | _ second =>
        induction h using Quotient.inductionOn with
        | _ third =>
          exact Quotient.sound
            (G122GeneratedComparisonSyntax.Congruent.assoc first second third)

/-- Decode a quotient class to its complete geometry morphism.  Soundness of
the independently generated relation is precisely the well-definedness proof. -/
noncomputable def decoder {Θ : G122FamilyInput.{u, v}} :
    G122GeneratedComparisonPresentation Θ ⥤
      G122GeneratedGeometryObject Θ where
  obj P := P.object
  map {P Q} f := Quotient.liftOn f
    G122GeneratedComparisonSyntax.evaluate
    (fun _ _ relation =>
      G122GeneratedComparisonSyntax.evaluate_eq_of_congruent relation)
  map_id _ := rfl
  map_comp f g := by
    induction f using Quotient.inductionOn with
    | _ first =>
      induction g using Quotient.inductionOn with
      | _ second => rfl

/-- Decoding a represented term is exactly its independently defined semantic
evaluation. -/
@[simp] theorem decoder_map_classOf {Θ : G122FamilyInput.{u, v}}
    {X Y : G122GeneratedGeometryObject Θ}
    (term : G122GeneratedComparisonSyntax Θ X Y) :
    decoder.map (classOf term) = term.evaluate :=
  rfl

/-- The fixed generated comparison equals its source-derived factorization in
the quotient category. -/
theorem finiteAxisFold_barBeta_factor_class_eq :
    classOf (.barBeta finiteAxisFoldG122CellInput) =
      classOf (.compose (.barAlpha finiteAxisFoldG122CellInput)
        (.barD finiteAxisFoldG122CellInput)) :=
  Quotient.sound
    G122GeneratedComparisonSyntax.finiteAxisFold_barBeta_factor_congruent

/-- The fixed generated target projector remains distinct from identity in the
source-law quotient. -/
theorem finiteAxisFold_barD_class_ne_identity_class :
    classOf (.barD finiteAxisFoldG122CellInput) ≠
      classOf (.identity
        (.viaBase finiteAxisFoldG122CellInput)) := by
  intro equality
  exact G122GeneratedComparisonSyntax.finiteAxisFold_barD_not_congruent_identity
    (Quotient.exact equality)

/-- Decoding the fixed target-projector quotient class gives the independently
constructed complete geometry projector. -/
@[simp] theorem decoder_map_finiteAxisFold_barD :
    decoder.map (classOf (.barD finiteAxisFoldG122CellInput)) =
      G122GeneratedGeometryObject.barD finiteAxisFoldG122FamilyInput
        finiteAxisFoldG122CellInput :=
  rfl

end G122GeneratedComparisonPresentation

end AAT.AG.RealizationReconstruction

#assert_standard_axioms_only AAT.AG.RealizationReconstruction
