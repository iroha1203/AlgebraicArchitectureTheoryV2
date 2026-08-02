import Formal.AG.ReadingFunctoriality.Core
import Formal.Util.AssertStandardAxioms
import Mathlib.CategoryTheory.Category.Basic

/-!
# Exact and refinement extraction-doctrine morphisms

This module constructs the category `Doct_U` from the exact source and Atom
transport data fixed by `G-101-aat-atom-foundation`.

## Implementation notes

An exact morphism stores only the source map, the Atom equivalence, normalization
compatibility, and preservation/reflection of extraction.  Canonical Atom-family
transport and the upper reading lift are derived in later modules.  Storing either
of them here would make the lower category depend on the desired lift.

A refinement morphism is deliberately separate from that category.  It stores
only a bijective Atom map and forward extraction preservation.  In particular,
reflection and an upper reading lift are not part of its data.
-/

namespace AAT.AG.AtomFoundation

universe u

open CategoryTheory

/-- The object type of the extraction-doctrine category `Doct_U`. -/
abbrev DoctrineCategory (U : AtomCarrier.{u}) := ExtractionDoctrine U

/--
An exact morphism between extraction doctrines on one fixed Atom carrier.

The material inputs are precisely the source map, the Atom equivalence,
normalization compatibility, and preservation/reflection of extraction required
by the G-101 target statement.
-/
structure ExactDoctrineHom {U : AtomCarrier.{u}}
    (D E : ExtractionDoctrine U) where
  /-- Map between the source types of the two doctrines. -/
  sourceMap : D.Source → E.Source
  /-- Equivalence of the fixed carrier's primitive Atoms. -/
  atomEquiv : U.Atom ≃ U.Atom
  /-- Source normalization commutes with the source map. -/
  normalize_eq :
    ∀ source, E.normalize (sourceMap source) = sourceMap (D.normalize source)
  /-- Extraction is preserved and reflected along the source and Atom maps. -/
  extraction_iff :
    ∀ source atom,
      D.extracts source atom ↔ E.extracts (sourceMap source) (atomEquiv atom)

namespace ExactDoctrineHom

/-- Exact doctrine morphisms are determined by their two computational maps. -/
@[ext]
theorem ext {U : AtomCarrier.{u}} {D E : ExtractionDoctrine U}
    {f g : ExactDoctrineHom D E}
    (hsourceMap : f.sourceMap = g.sourceMap)
    (hatomEquiv : f.atomEquiv = g.atomEquiv) :
    f = g := by
  cases f
  cases g
  cases hsourceMap
  cases hatomEquiv
  rfl

/-- The identity exact doctrine morphism. -/
def id {U : AtomCarrier.{u}} (D : ExtractionDoctrine U) :
    ExactDoctrineHom D D where
  sourceMap := _root_.id
  atomEquiv := Equiv.refl U.Atom
  normalize_eq _ := rfl
  extraction_iff _ _ := Iff.rfl

/-- Composition of exact doctrine morphisms. -/
def comp {U : AtomCarrier.{u}} {D E F : ExtractionDoctrine U}
    (f : ExactDoctrineHom D E) (g : ExactDoctrineHom E F) :
    ExactDoctrineHom D F where
  sourceMap := g.sourceMap ∘ f.sourceMap
  atomEquiv := f.atomEquiv.trans g.atomEquiv
  normalize_eq source := by
    calc
      F.normalize (g.sourceMap (f.sourceMap source)) =
          g.sourceMap (E.normalize (f.sourceMap source)) :=
        g.normalize_eq (f.sourceMap source)
      _ = g.sourceMap (f.sourceMap (D.normalize source)) :=
        congrArg g.sourceMap (f.normalize_eq source)
  extraction_iff source atom :=
    (f.extraction_iff source atom).trans
      (g.extraction_iff (f.sourceMap source) (f.atomEquiv atom))

/--
Canonical atomization commutes with every exact doctrine morphism.

This is the G-101 family-transport bridge.  Both directions are derived from
extraction exactness; the inverse Atom equivalence supplies the canonical
preimage needed by direct-image family transport.
-/
theorem atomize_naturality {U : AtomCarrier.{u}}
    {D E : ExtractionDoctrine U} (f : ExactDoctrineHom D E)
    (source : D.Source) :
    E.atomize (f.sourceMap source) =
      (D.atomize source).transport f.atomEquiv := by
  apply AtomFamily.ext
  intro target
  constructor
  · intro htarget
    change E.extracts (f.sourceMap source) target at htarget
    let sourceAtom := f.atomEquiv.symm target
    have hsource : D.extracts source sourceAtom :=
      (f.extraction_iff source sourceAtom).mpr (by
        simpa [sourceAtom] using htarget)
    exact ⟨sourceAtom, hsource, f.atomEquiv.apply_symm_apply target⟩
  · rintro ⟨sourceAtom, hsource, rfl⟩
    change D.extracts source sourceAtom at hsource
    change E.extracts (f.sourceMap source) (f.atomEquiv sourceAtom)
    exact (f.extraction_iff source sourceAtom).mp hsource

/-- Exact extraction doctrines form the category `Doct_U`. -/
instance extractionDoctrineCategory (U : AtomCarrier.{u}) :
    Category.{u} (ExtractionDoctrine U) where
  Hom := ExactDoctrineHom
  id := id
  comp f g := f.comp g
  id_comp := by
    intro D E f
    apply ExactDoctrineHom.ext
    · rfl
    · apply Equiv.ext
      intro atom
      rfl
  comp_id := by
    intro D E f
    apply ExactDoctrineHom.ext
    · rfl
    · apply Equiv.ext
      intro atom
      rfl
  assoc := by
    intro A B C D f g h
    apply ExactDoctrineHom.ext
    · rfl
    · apply Equiv.ext
      intro atom
      rfl

/-- The identity in `Doct_U` has the identity source map. -/
@[simp]
theorem id_sourceMap {U : AtomCarrier.{u}} (D : ExtractionDoctrine U) :
    (𝟙 D : D ⟶ D).sourceMap = _root_.id :=
  rfl

/-- The identity in `Doct_U` has the identity Atom equivalence. -/
@[simp]
theorem id_atomEquiv {U : AtomCarrier.{u}} (D : ExtractionDoctrine U) :
    (𝟙 D : D ⟶ D).atomEquiv = Equiv.refl U.Atom :=
  rfl

/-- Categorical composition computes as source-map composition. -/
@[simp]
theorem comp_sourceMap {U : AtomCarrier.{u}}
    {D E F : ExtractionDoctrine U} (f : D ⟶ E) (g : E ⟶ F) :
    (f ≫ g).sourceMap = g.sourceMap ∘ f.sourceMap :=
  rfl

/-- Categorical composition computes as transitivity of Atom equivalences. -/
@[simp]
theorem comp_atomEquiv {U : AtomCarrier.{u}}
    {D E F : ExtractionDoctrine U} (f : D ⟶ E) (g : E ⟶ F) :
    (f ≫ g).atomEquiv = f.atomEquiv.trans g.atomEquiv :=
  rfl

end ExactDoctrineHom

/--
A one-way refinement between extraction doctrines on one fixed Atom carrier.

Unlike an exact doctrine morphism, a refinement preserves extraction only in
the forward direction.  Bijectivity is retained as primary evidence about the
specified `atomMap`; the corresponding equivalence is derived below rather
than stored as an independent choice.
-/
structure RefinementDoctrineHom {U : AtomCarrier.{u}}
    (D E : ExtractionDoctrine U) where
  /-- Map between the source types of the two doctrines. -/
  sourceMap : D.Source → E.Source
  /-- The specified map between primitive Atoms. -/
  atomMap : U.Atom → U.Atom
  /-- The specified Atom map is bijective. -/
  atomMap_bijective : Function.Bijective atomMap
  /-- Source normalization commutes with the source map. -/
  normalize_eq :
    ∀ source, E.normalize (sourceMap source) = sourceMap (D.normalize source)
  /-- Extraction is preserved in the refinement direction. -/
  extraction_forward :
    ∀ source atom,
      D.extracts source atom → E.extracts (sourceMap source) (atomMap atom)

namespace RefinementDoctrineHom

/-- Refinement morphisms are determined by their two computational maps. -/
@[ext]
theorem ext {U : AtomCarrier.{u}} {D E : ExtractionDoctrine U}
    {f g : RefinementDoctrineHom D E}
    (hsourceMap : f.sourceMap = g.sourceMap)
    (hatomMap : f.atomMap = g.atomMap) :
    f = g := by
  cases f
  cases g
  cases hsourceMap
  cases hatomMap
  rfl

/-- The equivalence canonically packaged from the specified bijective Atom map. -/
noncomputable def atomEquiv {U : AtomCarrier.{u}}
    {D E : ExtractionDoctrine U} (f : RefinementDoctrineHom D E) :
    U.Atom ≃ U.Atom :=
  Equiv.ofBijective f.atomMap f.atomMap_bijective

/-- The derived equivalence has exactly the specified Atom map as its function. -/
@[simp]
theorem atomEquiv_apply {U : AtomCarrier.{u}}
    {D E : ExtractionDoctrine U} (f : RefinementDoctrineHom D E)
    (atom : U.Atom) :
    f.atomEquiv atom = f.atomMap atom :=
  rfl

end RefinementDoctrineHom

end AAT.AG.AtomFoundation

#assert_standard_axioms_only AAT.AG.AtomFoundation
