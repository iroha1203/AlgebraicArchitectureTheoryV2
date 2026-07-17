import Formal.AG.ReadingFunctoriality.StandardSchemeCoefficient
import Formal.AG.LawAlgebra.ClosedEquationalGeometry
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!
# Closed-equational geometry under coefficient change

This module implements the six fixed declarations of PRD SD7 / AC31.  Its input is a source raw
system `raw`, a source standard scheme `X`, a semantic equation core `G` with its source
presentation bridge `B`, and a flat coefficient change `f`.  Source and target `HasSheafify`
instances type the two standard schemes; the explicit site-dependent `HasSheafCompose` instance
supplies the coefficient-change compatibility already required by the canonical scheme pullback.

The fixed definition sends each source global equation through the actual
`StandardArchitectureScheme.baseChangeMap.appTop`.  The target geometric predicate and its
closed-equational witness are then reconstructed from that same transported family by
`ClosedEquationalLawWitness.ofGlobalSections`.  The characterization theorem compares target
vanishing with source vanishing after the actual projection, while the validity theorem derives
restriction compatibility from the global-section constructor.

No target raw bridge, caller-supplied target reading, comparison map, or witness certificate is
accepted.  The source bridge validity premise `hB` is intentionally absent here: it is first used
by the source chart-ideal realization fixed in R7 / AC32, whereas these six declarations only
transport global equations and construct the target reading.
-/

namespace AAT.AG

open CategoryTheory
open AlgebraicGeometry

universe u v

noncomputable section

namespace LawAlgebra

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {k k' : Type v}
variable [CommRing k] [CommRing k']
variable (raw : RawAmbientRestrictionSystem S k)
variable [HasSheafify S.topology (AATCommAlgCat k)]
variable [HasSheafify S.topology (AATCommAlgCat k')]
variable (X : StandardArchitectureScheme raw)

/-- The AC31 fixed definition that sends one source semantic-core equation through the actual
coefficient-change projection.  The source bridge `B` creates the source global section; no
target bridge or caller-supplied comparison morphism is accepted. -/
noncomputable def baseChangedSemanticCoreGlobalEquation
    (G : SemanticLawEquationWitnessIdealCore S)
    (B : SemanticLawEquationSchemeBridge raw G)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')]
    (i : S.lawUniverse.Index) (a : U.Atom) :
    Γ((X.baseChange raw f).underlying, ⊤) :=
  (X.baseChangeMap raw f).appTop
    (semanticCoreGlobalEquation raw X G B i a)

/-- The AC31 target reading generated from the transported global equations.  Its geometric
predicate and witness use the same section family, and `ofGlobalSections` supplies canonical
coordinates instead of accepting a target reading or witness certificate from the caller. -/
noncomputable def ClosedEquationalLawReading.baseChangeOfSemanticCore
    (G : SemanticLawEquationWitnessIdealCore S)
    (B : SemanticLawEquationSchemeBridge raw G)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')] :
    ClosedEquationalLawReading
      (raw.baseChange f.hom) (X.baseChange raw f) where
  geometric := {
    HoldsOn := fun s i =>
      GlobalEquationsVanishAlong
        (raw.baseChange f.hom) (X.baseChange raw f)
        (baseChangedSemanticCoreGlobalEquation raw X G B f i) s
  }
  closed := Set.univ
  selected := fun _ => Set.univ
  witness := fun i _ =>
    ClosedEquationalLawWitness.ofGlobalSections
      (raw.baseChange f.hom) (X.baseChange raw f) i
      (baseChangedSemanticCoreGlobalEquation raw X G B f i)

/-- The AC31 characterization API: transported vanishing is exactly source vanishing after the
actual coefficient-change projection.  This records the defining `appTop` composition and does
not introduce an auxiliary comparison map. -/
theorem ClosedEquationalLawReading.baseChangeOfSemanticCore_geometric_iff
    (G : SemanticLawEquationWitnessIdealCore S)
    (B : SemanticLawEquationSchemeBridge raw G)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')]
    {T : AlgebraicGeometry.Scheme}
    (s : T ⟶ (X.baseChange raw f).underlying)
    (i : S.lawUniverse.Index) :
    (ClosedEquationalLawReading.baseChangeOfSemanticCore
      raw X G B f).geometric.HoldsOn s i ↔
      (ClosedEquationalLawReading.ofSemanticCore
        raw X G B).geometric.HoldsOn
          (s ≫ X.baseChangeMap raw f) i := by
  rfl

/-- The AC31 principal validity theorem.  Geometric stability follows from composition of Scheme
global-section maps, while witness compatibility is derived from
`ClosedEquationalLawWitness.ofGlobalSections_valid`; neither conclusion is supplied as a
premise. -/
theorem ClosedEquationalLawReading.baseChangeOfSemanticCore_valid
    (G : SemanticLawEquationWitnessIdealCore S)
    (B : SemanticLawEquationSchemeBridge raw G)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')] :
    IsClosedEquationalLawReading
      (raw.baseChange f.hom) (X.baseChange raw f)
      (ClosedEquationalLawReading.baseChangeOfSemanticCore
        raw X G B f) where
  geometric_stable := by
    intro T T' s g i hs a
    rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, hs a, map_zero]
  witness_compatible := by
    intro i hi
    exact ClosedEquationalLawWitness.ofGlobalSections_valid
      (raw.baseChange f.hom) (X.baseChange raw f) i _
  selected_closed := fun _ i _ => Set.mem_univ i
  selected_basicOpen := fun _ _ i =>
    iff_of_true (Set.mem_univ i) (Set.mem_univ i)

/-- The required-law selection consequence of the AC31 fixed reading.  It reads the constructed
`Set.univ` closed and selected fields and makes no semantic-truth claim. -/
theorem ClosedEquationalLawReading.baseChangeOfSemanticCore_requiredClosed
    (G : SemanticLawEquationWitnessIdealCore S)
    (B : SemanticLawEquationSchemeBridge raw G)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')] :
    RequiredClosed
      (raw.baseChange f.hom) (X.baseChange raw f)
      (ClosedEquationalLawReading.baseChangeOfSemanticCore
        raw X G B f) where
  closed := fun i _ => Set.mem_univ i
  selected := fun _ i _ => Set.mem_univ i

/-- The all-law selection consequence of the AC31 fixed reading.  It reads the constructed
`Set.univ` fields; source chart realization remains the separate R7 / AC32 obligation using
`hB`. -/
theorem ClosedEquationalLawReading.baseChangeOfSemanticCore_allLawsSelected
    (G : SemanticLawEquationWitnessIdealCore S)
    (B : SemanticLawEquationSchemeBridge raw G)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')] :
    AllLawsSelected
      (raw.baseChange f.hom) (X.baseChange raw f)
      (ClosedEquationalLawReading.baseChangeOfSemanticCore
        raw X G B f) where
  closed := fun i => Set.mem_univ i
  selected := fun _ i => Set.mem_univ i

end LawAlgebra

end

end AAT.AG
