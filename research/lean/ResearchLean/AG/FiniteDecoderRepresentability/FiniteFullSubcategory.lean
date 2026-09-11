import ResearchLean.AG.FiniteDecoderRepresentability.FixedArrowConsequences
import Formal.Util.AssertStandardAxioms

/-!
# The finite-carrier full subcategory

This module begins G-121(D).  It selects exactly the finite instance codes whose
normalized extraction tables have authored default `false`, retains every
finite-code morphism between them, and proves that semantic realization
restricted to this full subcategory is full and faithful on a finite Atom
carrier.

## Implementation notes

The object predicate is imposed only after normalization, as required by the
fixed target; extraction tables at other source positions are unrestricted.
Fullness is not stored in a presentation certificate: carrier finiteness proves
finite support of the actual semantic permutation, while the two endpoint
properties prove the default equation in Cycle 10's exact classification.
-/

namespace AAT.AG.FiniteDecoderRepresentability

universe u

open CategoryTheory AtomFoundation DoctrineFiberProduct

variable {U : AtomCarrier.{u}}

/--
G-121(D) object condition: every normalized extraction table has authored
default `false`.  No condition is imposed on unnormalized table positions.
-/
def falseDefaultFiniteCodeProperty [DecidableEq U.Atom] :
    ObjectProperty (FiniteCodeCartCategory U) :=
  fun code => ∀ input : code.doctrine.Source,
    (normalizedExtractionCode code input).defaultValue = false

/-- G-121(D)'s full subcategory `P₀⁰` on the false-default objects. -/
abbrev FalseDefaultFiniteCodeCategory
    (U : AtomCarrier.{u}) [DecidableEq U.Atom] :=
  (falseDefaultFiniteCodeProperty (U := U)).FullSubcategory

/--
G-121(D)'s restricted decoder `D₀⁰`; it forgets only the proof of the
object condition and then applies the existing finite-code realization.
-/
def falseDefaultFiniteCodeRealization [DecidableEq U.Atom] :
    FalseDefaultFiniteCodeCategory U ⥤ ExtractionInstance U :=
  (falseDefaultFiniteCodeProperty (U := U)).ι ⋙
    finiteCodeCartRealization

/-- The restricted decoder retains the underlying semantic object literally. -/
@[simp]
theorem falseDefaultFiniteCodeRealization_obj
    [DecidableEq U.Atom] (code : FalseDefaultFiniteCodeCategory U) :
    falseDefaultFiniteCodeRealization.obj code = code.obj.toSemantic :=
  rfl

/-- The restricted decoder maps the underlying full-subcategory morphism by `D₀`. -/
@[simp]
theorem falseDefaultFiniteCodeRealization_map
    [DecidableEq U.Atom]
    {source target : FalseDefaultFiniteCodeCategory U}
    (hom : source ⟶ target) :
    falseDefaultFiniteCodeRealization.map hom =
      finiteCodeCartRealization.map hom.hom :=
  rfl

/--
G-121(D) faithfulness of `D₀⁰`: the full-subcategory wrapper adds no
morphism data, and Cycle 11 proves that `D₀` reflects equality on every carrier.
-/
instance falseDefaultFiniteCodeRealization_faithful [DecidableEq U.Atom] :
    (falseDefaultFiniteCodeRealization (U := U)).Faithful where
  map_injective {source target} first second hmap := by
    apply ObjectProperty.hom_ext
    apply finiteCodeCartRealization_map_injective
    simpa only [falseDefaultFiniteCodeRealization_map] using hmap

/--
G-121(D) fullness of `D₀⁰` on a finite Atom carrier.  Carrier finiteness
supplies finite actual support, and the endpoint object properties supply the
two sides of the normalized default equation; Cycle 10 constructs the preimage.
-/
noncomputable instance falseDefaultFiniteCodeRealization_full
    [DecidableEq U.Atom] [Finite U.Atom] :
    (falseDefaultFiniteCodeRealization (U := U)).Full where
  map_surjective {source target} hom := by
    have hsupport :
        (atomPermutationSupport hom.doctrineHom.atomEquiv).Finite :=
      Set.toFinite _
    have hdefault : ∀ input : source.obj.doctrine.Source,
        (normalizedExtractionCode target.obj
          (hom.doctrineHom.sourceMap input)).defaultValue =
        (normalizedExtractionCode source.obj input).defaultValue := by
      intro input
      rw [target.property (hom.doctrineHom.sourceMap input),
        source.property input]
    obtain ⟨codeHom, hdecode⟩ :=
      (exists_finiteCodeCartHom_map_iff hom).2 ⟨hsupport, hdefault⟩
    exact ⟨ObjectProperty.homMk codeHom, by
      simpa only [falseDefaultFiniteCodeRealization_map] using hdecode⟩

#assert_standard_axioms_only AAT.AG.FiniteDecoderRepresentability

end AAT.AG.FiniteDecoderRepresentability
