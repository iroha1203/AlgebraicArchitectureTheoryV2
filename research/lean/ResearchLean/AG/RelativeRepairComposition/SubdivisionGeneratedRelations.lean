import ResearchLean.AG.RelativeRepairComposition.SubdivisionPrivateDifferential
import ResearchLean.AG.RelativeRepairComposition.SubdivisionFiniteEnumerations
import ResearchLean.AG.RelativeRepairComposition.FiniteNativeArbitraryEquation

/-!
# Independently generated local public relations and restoration

## Implementation notes

Each side applies the same finite generator to its own actual full local D/F,
its own complete bases and its own original-coordinate enumeration. The new
edge list and membership decisions are computed from the original inputs.
No section equality is assumed: full solution coordinates connect the two
independent outputs. Arbitrary right-hand sides and every public value remain.
-/
namespace AAT.AG.RelativeRepairComposition.Subdivision.GeneratedRelations
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
universe uk uG uI uE uB uD vE vB vD
variable {k : Type uk} [Field k]
variable {K : FiniteTransportPresentation.{uG}}
variable {E : Type uE} {B : Type uB} {D : Type uD}
variable [Category.{vE} E] [Category.{vB} B] [Category.{vD} D]
variable {p : E ⥤ B} {q : B ⥤ D}
variable (T : OriginalTowerPresentation K p q) (chosen : EdgeName (K := K))
variable (factor : Factorization T chosen)
variable [∀ v, Module k (T.toTower.localCoefficients.A v)]
attribute [local instance] LinearCoefficients.coefficientModules
variable (bases : FiniteFamily.Bases (k := k) T.toTower.localCoefficients.A)
variable {I : Type uI} [Fintype I] [DecidableEq I]
variable (U : I → ClosedRegion K) (P : ClosedRegion K)
variable [∀ j, DecidablePred (· ∈ (U j).edges)] [DecidablePred (· ∈ P.edges)]
variable (candidates : Set (EdgeName (K := K))) [DecidablePred (· ∈ candidates)]
variable (i : I) (hi : chosen ∈ ClosedRegion.privateAlwaysEdges U P candidates i) (j : I)
variable (hlinear : ∀ {s t : K.Vertex} (e : K.Edge s t) (a : k)
  (x : T.toTower.localCoefficients.A s),
  T.toTower.localCoefficients.edge e (a • x) = a • T.toTower.localCoefficients.edge e x)

local notation "Mo" => (T.toTower.localCoefficients)
local notation "Mn" => (TowerPresentation.localCoefficients (OriginalTowerPresentation.toTower (originalTower T chosen factor)))
local notation "Bn" => FiniteBases.expandedBases T chosen factor bases
local notation "Un" => expandedRegion K chosen (U j)
local notation "Pn" => expandedRegion K chosen P
local notation "Io" => ClosedRegion.privateAlwaysEdges U P candidates j
local notation "In" => ClosedRegion.privateAlwaysEdges (fun l => expandedRegion K chosen (U l))
  Pn (oldEdgeSet K chosen candidates) j
local notation "Xo" => (FiniteNative.XIndex Mo bases (U j) P Io → k)
local notation "Zo" => (FiniteNative.ZIndex Mo bases (U j) P Io → k)
local notation "Xn" => (FiniteNative.XIndex Mn Bn Un Pn In → k)
local notation "Zn" => (FiniteNative.ZIndex Mn Bn Un Pn In → k)
local notation "R" => localSupplement T chosen factor (U j)


variable [Fintype k] [DecidableEq k]
variable [Fintype (EdgeName (K := K))] [DecidableEq (EdgeName (K := K))]
variable [Fintype K.TwoCell] [DecidableEq K.TwoCell]
variable [∀ l, DecidablePred (· ∈ (U l).vertices)] [∀ l, DecidablePred (· ∈ (U l).faces)]
variable [DecidablePred (· ∈ P.faces)]
variable (enumK : FiniteElimination.Enumeration k)
variable (enumEdges : FiniteElimination.Enumeration (EdgeName (K := K)))
variable (enumFaces : FiniteElimination.Enumeration K.TwoCell)
local notation "en" => FiniteEnumerations.edgeEnumeration K chosen enumEdges

/-- Generate the whole new interface independently from its actual local differential. -/
noncomputable def newGeneratedObjects (value : RelativeCover.C2 Mo (U j) P) : Type (max uk uG) := by
  letI := GeneratedPublicReadings.retainedCandidatesDecidable chosen U P candidates i hi
  letI : ∀ l, DecidablePred (· ∈ (expandedRegion K chosen (U l)).edges) :=
    fun l => FiniteIncidence.expandedEdgesDecidable K chosen (U l)
  letI : DecidablePred (· ∈ (Pn).edges) := FiniteIncidence.expandedEdgesDecidable K chosen P
  letI : DecidablePred (· ∈ (Un).vertices) := FiniteIncidence.expandedVerticesDecidable K chosen (U j)
  letI : DecidablePred (· ∈ (Un).faces) := FiniteIncidence.expandedFacesDecidable K chosen (U j)
  letI : Fintype (EdgeName (K := presentation K chosen)) := FiniteEnumerations.edgeFintype K chosen enumEdges
  letI : Fintype (presentation K chosen).TwoCell := inferInstanceAs (Fintype K.TwoCell)
  letI : DecidableEq (presentation K chosen).TwoCell := inferInstanceAs (DecidableEq K.TwoCell)
  exact FiniteNative.GeneratedRelativeObjects Mn Bn Un Pn In (LinearCoefficients.edge_linear T chosen factor hlinear) ((local2Equiv T chosen factor (U j) P).symm value) enumK en enumFaces

/-- Independently generate the full new public relation using its actual matrix section. -/
noncomputable def newRelation (value : RelativeCover.C2 Mo (U j) P) : Set Zn := by
  letI := GeneratedPublicReadings.retainedCandidatesDecidable chosen U P candidates i hi
  letI : ∀ l, DecidablePred (· ∈ (expandedRegion K chosen (U l)).edges) :=
    fun l => FiniteIncidence.expandedEdgesDecidable K chosen (U l)
  letI : DecidablePred (· ∈ (Pn).edges) := FiniteIncidence.expandedEdgesDecidable K chosen P
  letI : DecidablePred (· ∈ (Un).faces) := FiniteIncidence.expandedFacesDecidable K chosen (U j)
  letI : Fintype (EdgeName (K := presentation K chosen)) := FiniteEnumerations.edgeFintype K chosen enumEdges
  letI : Fintype (presentation K chosen).TwoCell := inferInstanceAs (Fintype K.TwoCell)
  letI : DecidableEq (presentation K chosen).TwoCell := inferInstanceAs (DecidableEq K.TwoCell)
  exact FiniteNative.generatedRelation Mn Bn Un Pn In (LinearCoefficients.edge_linear T chosen factor hlinear) ((local2Equiv T chosen factor (U j) P).symm value) enumK en enumFaces

/-- All independently generated new objects have full inverse restoration to original new solutions. -/
noncomputable def newGeneratedEquiv (value : RelativeCover.C2 Mo (U j) P) : FiniteNative.RelativeEquation Mn Un Pn ((local2Equiv T chosen factor (U j) P).symm value) ≃
    newGeneratedObjects T chosen factor bases U P candidates i hi j hlinear enumK enumEdges enumFaces (value := value) := by
  letI := GeneratedPublicReadings.retainedCandidatesDecidable chosen U P candidates i hi
  letI : ∀ l, DecidablePred (· ∈ (expandedRegion K chosen (U l)).edges) :=
    fun l => FiniteIncidence.expandedEdgesDecidable K chosen (U l)
  letI : DecidablePred (· ∈ (Pn).edges) := FiniteIncidence.expandedEdgesDecidable K chosen P
  letI : DecidablePred (· ∈ (Un).vertices) := FiniteIncidence.expandedVerticesDecidable K chosen (U j)
  letI : DecidablePred (· ∈ (Un).faces) := FiniteIncidence.expandedFacesDecidable K chosen (U j)
  letI : Fintype (EdgeName (K := presentation K chosen)) := FiniteEnumerations.edgeFintype K chosen enumEdges
  letI : Fintype (presentation K chosen).TwoCell := inferInstanceAs (Fintype K.TwoCell)
  letI : DecidableEq (presentation K chosen).TwoCell := inferInstanceAs (DecidableEq K.TwoCell)
  exact FiniteNative.generatedRelativeEquiv Mn Bn Un Pn In (LinearCoefficients.edge_linear T chosen factor hlinear) ((local2Equiv T chosen factor (U j) P).symm value) enumK en enumFaces

omit [Fintype (EdgeName (K := K))] in
/-- Independent extraction followed by restoration returns the whole original new solution. -/
theorem newGeneratedEquiv_inverse_apply (value : RelativeCover.C2 Mo (U j) P)
    (h : FiniteNative.RelativeEquation Mn Un Pn ((local2Equiv T chosen factor (U j) P).symm value)) :
    (newGeneratedEquiv T chosen factor bases U P candidates i hi j hlinear enumK enumEdges enumFaces
      (value := value)).symm
      (newGeneratedEquiv T chosen factor bases U P candidates i hi j hlinear enumK enumEdges enumFaces
        (value := value) h) = h :=
  (newGeneratedEquiv T chosen factor bases U P candidates i hi j hlinear enumK enumEdges enumFaces
    (value := value)).symm_apply_apply h

omit [Fintype (EdgeName (K := K))] in
/-- Independent new extraction keeps every public basis value read from the actual new correction. -/
theorem newGeneratedEquiv_public (value : RelativeCover.C2 Mo (U j) P) (h : FiniteNative.RelativeEquation Mn Un Pn ((local2Equiv T chosen factor (U j) P).symm value)) :
    (newGeneratedEquiv T chosen factor bases U P candidates i hi j hlinear enumK enumEdges enumFaces (value := value) h).1.1 =
      (GeneratedPrivate.newSplit T chosen factor bases U P candidates i hi j h.1).2 := rfl

omit [Fintype (EdgeName (K := K))] in
/-- Independent new restoration recovers every generated public value without choosing its kernel freedom. -/
theorem newGeneratedEquiv_inverse_public (value : RelativeCover.C2 Mo (U j) P)
    (y : newGeneratedObjects T chosen factor bases U P candidates i hi j hlinear enumK enumEdges enumFaces (value := value)) :
    (GeneratedPrivate.newSplit T chosen factor bases U P candidates i hi j
      ((newGeneratedEquiv T chosen factor bases U P candidates i hi j hlinear enumK enumEdges enumFaces (value := value)).symm y).1).2 =
      y.1.1 := by
  rw [← newGeneratedEquiv_public]
  exact congrArg (fun y => y.1.1)
    ((newGeneratedEquiv T chosen factor bases U P candidates i hi j hlinear enumK enumEdges enumFaces (value := value)).apply_symm_apply y)

omit [Fintype (EdgeName (K := K))] in
/-- A new generated public relation holds exactly for a full actual new local solution with that value. -/
theorem new_relation_iff_relative (value : RelativeCover.C2 Mo (U j) P) (z : Zn) :
    z ∈ newRelation T chosen factor bases U P candidates i hi j hlinear enumK enumEdges enumFaces (value := value) ↔
      ∃ h : FiniteNative.RelativeEquation Mn Un Pn ((local2Equiv T chosen factor (U j) P).symm value),
        (GeneratedPrivate.newSplit T chosen factor bases U P candidates i hi j h.1).2 = z := by
  letI := GeneratedPublicReadings.retainedCandidatesDecidable chosen U P candidates i hi
  letI : ∀ l, DecidablePred (· ∈ (expandedRegion K chosen (U l)).edges) :=
    fun l => FiniteIncidence.expandedEdgesDecidable K chosen (U l)
  letI : DecidablePred (· ∈ (Pn).edges) := FiniteIncidence.expandedEdgesDecidable K chosen P
  letI : DecidablePred (· ∈ (Un).vertices) := FiniteIncidence.expandedVerticesDecidable K chosen (U j)
  letI : DecidablePred (· ∈ (Un).faces) := FiniteIncidence.expandedFacesDecidable K chosen (U j)
  letI : Fintype (EdgeName (K := presentation K chosen)) := FiniteEnumerations.edgeFintype K chosen enumEdges
  letI : Fintype (presentation K chosen).TwoCell := inferInstanceAs (Fintype K.TwoCell)
  letI : DecidableEq (presentation K chosen).TwoCell := inferInstanceAs (DecidableEq K.TwoCell)
  exact FiniteNative.generated_relation_iff_relative Mn Bn Un Pn In (LinearCoefficients.edge_linear T chosen factor hlinear) ((local2Equiv T chosen factor (U j) P).symm value) enumK en enumFaces z

/-- Both independently generated relations have identical membership for every full public value and rhs. -/
theorem relation_iff (value : RelativeCover.C2 Mo (U j) P) (z : Zn) :
    z ∈ newRelation T chosen factor bases U P candidates i hi j hlinear enumK enumEdges enumFaces (value := value) ↔
      GeneratedPublic.publicCoordinateEquiv T chosen factor bases U P candidates i hi j z ∈
        FiniteNative.generatedRelation Mo bases (U j) P Io hlinear value enumK enumEdges enumFaces := by
  rw [new_relation_iff_relative,FiniteNative.generated_relation_iff_relative]
  constructor
  · rintro ⟨h,hh⟩
    refine ⟨(localEquationEquiv T chosen factor (U j) P hi.2.1 value h).1,?_⟩
    have ho := congrArg Prod.fst
      (localEquationEquiv_coordinates T chosen factor (U j) P hi.2.1 value h)
    change (localEquationEquiv T chosen factor (U j) P hi.2.1 value h).1.1 =
      (local1Equiv T chosen factor (U j) P hi.2.1 h.1).1 at ho
    rw [ho]
    have hc := GeneratedPublicReadings.public_reading_collapse T chosen factor bases U P candidates i hi j h.1
    rw [← GeneratedPrivate.newSplit_public,hh] at hc
    exact hc.symm
  · rintro ⟨h,hh⟩
    let newh := (localEquationEquiv T chosen factor (U j) P hi.2.1 value).symm (h,0)
    refine ⟨newh,?_⟩
    apply (GeneratedPublic.publicCoordinateEquiv T chosen factor bases U P candidates i hi j).injective
    have hc := GeneratedPublicReadings.public_reading_collapse T chosen factor bases U P candidates i hi j newh.1
    rw [← GeneratedPrivate.newSplit_public] at hc
    have hs := localEquationEquiv_inverse_coordinates T chosen factor (U j) P hi.2.1 value h 0
    change local1Equiv T chosen factor (U j) P hi.2.1 newh.1 = (h.1,0) at hs
    rw [hs] at hc
    exact hc.trans hh

end AAT.AG.RelativeRepairComposition.Subdivision.GeneratedRelations
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.Subdivision.GeneratedRelations
