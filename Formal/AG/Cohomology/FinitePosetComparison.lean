import Formal.AG.Cohomology.CechComplex
import Formal.AG.Site.FinitePoset

noncomputable section

namespace AAT.AG
namespace Cohomology

universe u

open CategoryTheory

/--
IV.R2 / AC4: the cover-relative general Čech cover induced by a PRD-2 finite
poset Čech complex.

This construction only transports the selected finite-poset cover, simplices,
overlap objects, faces, and face-overlap morphisms.  Coefficient comparison and
additive Čech differential data are recorded separately, because the PRD-2
surface is Type-valued while the PRD-4 obstruction surface is additive.
-/
def finitePosetCoverRelativeCover {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {K : Site.FinitePosetAATSiteRegime S}
    (C : Site.FinitePosetCechComplex K) :
    CoverRelativeCechCover S where
  base := K.base
  Index := K.cover.Index
  chart i := Site.ContextCategoryObject.of S.contextPreorder (K.cover.patch i)
  inclusion i := homOfLE (K.cover.inclusion i)
  simplex n := Site.FinitePosetCechSimplex K n
  overlap n σ := Site.FinitePosetCechOverlapObject K n σ
  face n i σ := C.faces.face n σ i
  faceRestriction n i σ := homOfLE (C.faces.faceOverlap_le n σ i)

/--
IV.R2 / AC4: explicit data comparing the PRD-4 general cover-relative complex
with the PRD-2 finite-poset Čech complex.

The comparison is intentionally assumption-explicit: the finite-poset
coefficient presheaf, the additive structure on the section products, and the
maps between PRD-4 cochains and PRD-2 cochains are supplied by the selected
finite regime.  The resulting theorem package below does not assert that every
AAT site or every coefficient sheaf admits such a comparison.
-/
structure FinitePosetCechComparisonData {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {K : Site.FinitePosetAATSiteRegime S}
    (C : Site.FinitePosetCechComplex K)
    (Ob : ObstructionSheaf S) where
  cochainAddCommGroup :
    ∀ n : Nat,
      AddCommGroup (CoverRelativeCechCochain (finitePosetCoverRelativeCover C) Ob n)
  alternatingFaceCombination :
    ∀ n : Nat,
      ((σ : (finitePosetCoverRelativeCover C).simplex (n + 1)) -> Fin (n + 2) ->
        Ob.carrier.toPresheaf.obj
          (Opposite.op ((finitePosetCoverRelativeCover C).overlap (n + 1) σ))) ->
      CoverRelativeCechCochain (finitePosetCoverRelativeCover C) Ob (n + 1)
  differential :
    ∀ n : Nat,
      CoverRelativeCechCochain (finitePosetCoverRelativeCover C) Ob n →+
        CoverRelativeCechCochain (finitePosetCoverRelativeCover C) Ob (n + 1)
  differential_eq_alternatingFaceCombination :
    ∀ (n : Nat) (c : CoverRelativeCechCochain (finitePosetCoverRelativeCover C) Ob n),
      differential n c =
        alternatingFaceCombination n
          (fun σ i =>
            Ob.carrier.toPresheaf.map
              ((finitePosetCoverRelativeCover C).faceRestriction n i σ).op
              (c ((finitePosetCoverRelativeCover C).face n i σ)))
  differential_comp :
    ∀ (n : Nat) (c : CoverRelativeCechCochain (finitePosetCoverRelativeCover C) Ob n),
      differential (n + 1) (differential n c) = 0
  toFinitePosetCochain :
    ∀ n : Nat,
      CoverRelativeCechCochain (finitePosetCoverRelativeCover C) Ob n ->
        Site.FinitePosetCechCochain K n
  fromFinitePosetCochain :
    ∀ n : Nat,
      Site.FinitePosetCechCochain K n ->
        CoverRelativeCechCochain (finitePosetCoverRelativeCover C) Ob n
  to_from_finitePosetCochain :
    ∀ (n : Nat) (c : Site.FinitePosetCechCochain K n),
      toFinitePosetCochain n (fromFinitePosetCochain n c) = c
  from_to_finitePosetCochain :
    ∀ (n : Nat) (c : CoverRelativeCechCochain (finitePosetCoverRelativeCover C) Ob n),
      fromFinitePosetCochain n (toFinitePosetCochain n c) = c
  differential_compat_toFinitePoset :
    ∀ (n : Nat) (c : CoverRelativeCechCochain (finitePosetCoverRelativeCover C) Ob n),
      toFinitePosetCochain (n + 1) (differential n c) =
        C.differential n (toFinitePosetCochain n c)
  finitePosetCoboundaryRelation :
    ∀ n : Nat, Site.FinitePosetCechCoboundaryRelation C n
  toFinitePosetCohomology :
    ∀ n : Nat,
      (comparisonComplex : CoverRelativeCechComplex (finitePosetCoverRelativeCover C) Ob) ->
        comparisonComplex.CoverRelativeHn n ->
          Site.FinitePosetCechCohomology C n (finitePosetCoboundaryRelation n)
  fromFinitePosetCohomology :
    ∀ n : Nat,
      (comparisonComplex : CoverRelativeCechComplex (finitePosetCoverRelativeCover C) Ob) ->
        Site.FinitePosetCechCohomology C n (finitePosetCoboundaryRelation n) ->
          comparisonComplex.CoverRelativeHn n
  to_from_finitePosetCohomology :
    ∀ (n : Nat)
      (comparisonComplex : CoverRelativeCechComplex (finitePosetCoverRelativeCover C) Ob)
      (h : Site.FinitePosetCechCohomology C n (finitePosetCoboundaryRelation n)),
      toFinitePosetCohomology n comparisonComplex
        (fromFinitePosetCohomology n comparisonComplex h) = h
  from_to_finitePosetCohomology :
    ∀ (n : Nat)
      (comparisonComplex : CoverRelativeCechComplex (finitePosetCoverRelativeCover C) Ob)
      (h : comparisonComplex.CoverRelativeHn n),
      fromFinitePosetCohomology n comparisonComplex
        (toFinitePosetCohomology n comparisonComplex h) = h

namespace FinitePosetCechComparisonData

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {K : Site.FinitePosetAATSiteRegime S}
variable {C : Site.FinitePosetCechComplex K} {Ob : ObstructionSheaf S}

/-- IV.R2 / AC4: build the PRD-4 general complex selected by the comparison data. -/
def generalComplex (D : FinitePosetCechComparisonData C Ob) :
    CoverRelativeCechComplex (finitePosetCoverRelativeCover C) Ob where
  cochainAddCommGroup := D.cochainAddCommGroup
  alternatingFaceCombination := D.alternatingFaceCombination
  differential := D.differential
  differential_eq_alternatingFaceCombination := D.differential_eq_alternatingFaceCombination
  differential_comp := D.differential_comp

/--
IV.R2 / AC4: the PRD-2 finite-poset complex is a comparison target for the
selected PRD-4 general complex.
-/
def comparisonTarget (D : FinitePosetCechComparisonData C Ob) :
    D.generalComplex.FinitePosetComparisonTarget where
  finitePosetCochain := Site.FinitePosetCechCochain K
  finitePosetDifferential := C.differential
  toFinitePosetCochain := D.toFinitePosetCochain
  fromFinitePosetCochain := D.fromFinitePosetCochain
  to_from_finitePosetCochain := D.to_from_finitePosetCochain
  from_to_finitePosetCochain := D.from_to_finitePosetCochain
  differential_compat_toFinitePoset := D.differential_compat_toFinitePoset
  finitePosetCohomology := fun n =>
    Site.FinitePosetCechCohomology C n (D.finitePosetCoboundaryRelation n)
  toFinitePosetCohomology := fun n => D.toFinitePosetCohomology n D.generalComplex
  fromFinitePosetCohomology := fun n => D.fromFinitePosetCohomology n D.generalComplex
  to_from_finitePosetCohomology := fun n =>
    D.to_from_finitePosetCohomology n D.generalComplex
  from_to_finitePosetCohomology := fun n =>
    D.from_to_finitePosetCohomology n D.generalComplex

/-- IV.R2 / AC4: cochains are identified with the PRD-2 finite-poset cochains. -/
theorem cochain_to_from (D : FinitePosetCechComparisonData C Ob)
    (n : Nat) (c : Site.FinitePosetCechCochain K n) :
    D.comparisonTarget.toFinitePosetCochain n
      (D.comparisonTarget.fromFinitePosetCochain n c) = c :=
  D.to_from_finitePosetCochain n c

/-- IV.R2 / AC4: the comparison respects the selected Čech differentials. -/
theorem differential_compatible (D : FinitePosetCechComparisonData C Ob)
    (n : Nat) (c : D.generalComplex.Cn n) :
    D.comparisonTarget.toFinitePosetCochain (n + 1) (D.generalComplex.d n c) =
      C.differential n (D.comparisonTarget.toFinitePosetCochain n c) :=
  D.differential_compat_toFinitePoset n c

/--
IV.R2 / AC4: finite-poset cohomology is the cohomology target selected for the
comparison package.
-/
theorem cohomology_target_eq (D : FinitePosetCechComparisonData C Ob) (n : Nat) :
    D.comparisonTarget.finitePosetCohomology n =
      Site.FinitePosetCechCohomology C n (D.finitePosetCoboundaryRelation n) :=
  rfl

/--
IV.R2 / AC4: the selected cohomology maps are a left inverse on finite-poset
cohomology.
-/
theorem cohomology_to_from (D : FinitePosetCechComparisonData C Ob)
    (n : Nat)
    (h : Site.FinitePosetCechCohomology C n (D.finitePosetCoboundaryRelation n)) :
    D.comparisonTarget.toFinitePosetCohomology n
      (D.comparisonTarget.fromFinitePosetCohomology n h) = h :=
  D.to_from_finitePosetCohomology n D.generalComplex h

/--
IV.R2 / AC4: the selected cohomology maps are a right inverse on PRD-4
cover-relative cohomology.
-/
theorem cohomology_from_to (D : FinitePosetCechComparisonData C Ob)
    (n : Nat) (h : D.generalComplex.CoverRelativeHn n) :
    D.comparisonTarget.fromFinitePosetCohomology n
      (D.comparisonTarget.toFinitePosetCohomology n h) = h :=
  D.from_to_finitePosetCohomology n D.generalComplex h

end FinitePosetCechComparisonData

end Cohomology
end AAT.AG
