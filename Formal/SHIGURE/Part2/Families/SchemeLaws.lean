import Formal.SHIGURE.Part2.Families.SchemeSections
import Formal.SHIGURE.Part2.Families.AffineRealizations
import Formal.SHIGURE.Part2.Schemes.ConstantRank
import Formal.SHIGURE.Part2.Schemes.AffineModuleSections

/-! # Written Laws and finite locally free realizations on schemes

Definition 6.1: the base map supplies the coefficients of every written
Law. The carrier data and primitive maps are the actual module sheaves
of `SchemeTensorStructure`; Law satisfaction is tested on affine opens
using their canonical section interpretations.

## Implementation notes

Coefficients are obtained from `ΓSpecIso`, the actual map on global
sections, and actual restriction to the chosen open. They are not an
independent family of ring maps. The existing polynomial `Holds` tests
all scalar extensions, so this construction uses the universal
polynomial semantics rather than equality on just the original points.
Finite local freeness and rank remain separate from Law satisfaction.
The full subcategory retains all actual structure-preserving sheaf maps
over the fixed base map. No equivalence between testing on affine opens
and testing on all opens is included as a defining assumption.
-/

namespace SHIGURE.RealizationFamilies

open AlgebraicGeometry CategoryTheory Opposite SchemeDescent TensorRealization

noncomputable section

universe u

variable {k : Type u} [CommRing k] {X : Scheme.{u}} {sig : Signature.{u}}

/-- The coefficient map on an open of a test `k`-scheme in Definition 6.1.
Implementation notes: this is the composite from the spectrum's global
sections through the actual scheme map and restriction; no coefficient
compatibility certificate is requested. -/
def sectionBaseMap (b : X ⟶ Spec (CommRingCat.of k)) (U : X.Opens) :
    k →+* Γ(X, U) :=
  (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op).hom.comp
    (b.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom)

/-- API for the coefficient map: restriction between opens commutes with
the map from the base ring. -/
theorem sectionBaseMap_restrict (b : X ⟶ Spec (CommRingCat.of k))
    {U V : X.Opens} (inside : V ≤ U) :
    (X.presheaf.map (homOfLE inside).op).hom.comp (sectionBaseMap b U) =
      sectionBaseMap b V := by
  ext r
  change X.presheaf.map (homOfLE inside).op
    (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op
      (b.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv r))) = _
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

/-- The tensor and universal polynomial Laws of Definition 6.1 hold on
every affine open, interpreted by actual sections of the module sheaves.
Implementation notes: this is a property of the already constructed
section structures, separate from the finite locally free condition. -/
def SatisfiesSchemeLaws (P : AffineLawPresentation k sig)
    (b : X ⟶ Spec (CommRingCat.of k)) (A : SchemeTensorStructure X sig) : Prop :=
  ∀ U : X.affineOpens,
    (∀ i, ((P.tensorLaw i).mapScalars (sectionBaseMap b U.1)).holds
      (sectionsStructure A U.1)) ∧
    (∀ i, (P.polynomialLaw i).Holds (sectionBaseMap b U.1) (sectionsStructure A U.1))

/-- API for scheme Law satisfaction: obtain a tensor Law on an affine open. -/
theorem SatisfiesSchemeLaws.tensor {P : AffineLawPresentation k sig}
    {b : X ⟶ Spec (CommRingCat.of k)} {A : SchemeTensorStructure X sig}
    (h : SatisfiesSchemeLaws P b A) (U : X.affineOpens) (i : P.tensorIndex) :
    ((P.tensorLaw i).mapScalars (sectionBaseMap b U.1)).holds (sectionsStructure A U.1) :=
  (h U).1 i

/-- API for scheme Law satisfaction: obtain a universal polynomial Law
on an affine open, including all coefficient extensions in `Holds`. -/
theorem SatisfiesSchemeLaws.polynomial {P : AffineLawPresentation k sig}
    {b : X ⟶ Spec (CommRingCat.of k)} {A : SchemeTensorStructure X sig}
    (h : SatisfiesSchemeLaws P b A) (U : X.affineOpens) (i : P.polynomialIndex) :
    (P.polynomialLaw i).Holds (sectionBaseMap b U.1) (sectionsStructure A U.1) :=
  (h U).2 i

/-- The property defining the realization category of Definition 6.1.
Implementation notes: finite local freeness of specified rank is the
existing geometric sheaf property; it is combined with written Laws only
when taking the full subcategory, never built into the primitive data. -/
def schemeRealizationProperty (P : AffineLawPresentation k sig)
    (rank : sig.SortType → ℕ) (b : X ⟶ Spec (CommRingCat.of k)) :
    ObjectProperty (SchemeTensorStructure X sig) := fun A =>
  (∀ s, IsFiniteLocallyFreeOfRank (A.carrier s) (rank s)) ∧ SatisfiesSchemeLaws P b A

/-- All finite locally free realizations of the prescribed rank and their
structure-preserving sheaf maps, over the same fixed base map.
Implementation notes: use mathlib's full subcategory of the actual sheaf
data category, retaining noninvertible morphisms. -/
abbrev SchemeRealization (P : AffineLawPresentation k sig)
    (rank : sig.SortType → ℕ) (b : X ⟶ Spec (CommRingCat.of k)) :=
  (schemeRealizationProperty P rank b).FullSubcategory

/-- The maximal subgroupoid `Real_n` in Definition 6.1.
Implementation notes: mathlib's `Core` selects the isomorphisms of the
full realization category; invertibility is not extra primitive data. -/
abbrev SchemeRealizationCore (P : AffineLawPresentation k sig)
    (rank : sig.SortType → ℕ) (b : X ⟶ Spec (CommRingCat.of k)) :=
  Core (SchemeRealization P rank b)

/-- API for the realization property: each actual carrier sheaf has the
specified finite locally free rank. -/
theorem schemeRealizationProperty_carrier {P : AffineLawPresentation k sig}
    {rank : sig.SortType → ℕ} {b : X ⟶ Spec (CommRingCat.of k)}
    {A : SchemeTensorStructure X sig} (h : schemeRealizationProperty P rank b A)
    (s : sig.SortType) : IsFiniteLocallyFreeOfRank (A.carrier s) (rank s) :=
  h.1 s

/-- API for the realization property: the primitive sheaf structure
satisfies the written tensor and universal polynomial Laws. -/
theorem schemeRealizationProperty_laws {P : AffineLawPresentation k sig}
    {rank : sig.SortType → ℕ} {b : X ⟶ Spec (CommRingCat.of k)}
    {A : SchemeTensorStructure X sig} (h : schemeRealizationProperty P rank b A) :
    SatisfiesSchemeLaws P b A := h.2

/-- The affine-section comparison needed to connect the geometric rank
property to the coefficient realization category of Definition 6.1.
Its hypotheses are precisely the existing finite locally free sheaf
property and an affine open. The comparison must identify actual sections
with a tilde presentation's coefficient module, preserving scalar actions. -/
theorem affineSections_finiteLocallyFreeOfRank (M : X.Modules) {n : ℕ}
    (h : IsFiniteLocallyFreeOfRank M n) (U : X.affineOpens) :
    CoefficientDescent.FiniteLocallyFree Γ(X, U.1) (M.val.obj (op U.1)) ∧
      ∀ p : PrimeSpectrum Γ(X, U.1), Module.rankAtStalk (M.val.obj (op U.1)) p = n := by
  obtain ⟨N, finite, ⟨e⟩⟩ := isFiniteLocallyFreeModule_iff_on_affineOpens.mp h.1 U
  let comparison := affinePresentationSectionsIso U.property M N e
  refine ⟨SchemeDescent.finiteLocallyFree_of_moduleIso comparison finite, fun p => ?_⟩
  exact (congrFun (Module.rankAtStalk_eq_of_equiv comparison.toLinearEquiv) p).symm.trans
    ((h.2 U).rank N e p)

/-- Reading a scheme realization on an affine open gives the existing
affine realization property with the actual coefficient map from the base.
This is the property comparison for Definition 6.1; its finite-rank input
is discharged by the affine-section comparison above. -/
theorem schemeRealizationProperty_affine {P : AffineLawPresentation k sig}
    {rank : sig.SortType → ℕ} {b : X ⟶ Spec (CommRingCat.of k)}
    {A : SchemeTensorStructure X sig} (h : schemeRealizationProperty P rank b A)
    (U : X.affineOpens) :
    affineProperty P rank (sectionBaseMap b U.1) (sectionsStructure A U.1) := by
  refine ⟨fun s => ?_, fun s p => ?_, (h.2 U).1, (h.2 U).2⟩
  · exact (affineSections_finiteLocallyFreeOfRank (A.carrier s) (h.1 s) U).1
  · exact (affineSections_finiteLocallyFreeOfRank (A.carrier s) (h.1 s) U).2 p

end

end SHIGURE.RealizationFamilies
