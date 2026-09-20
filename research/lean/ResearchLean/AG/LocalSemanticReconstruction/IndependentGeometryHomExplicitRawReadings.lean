import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomExplicitRawAssembly
import Formal.Util.AssertStandardAxioms

/-!
# Native explicit raw maps on all primitive candidate rows

Implementation notes: each reader returns a Boolean inverse graph on the
original candidate carriers. The inverse context, coordinate carriers, and
coordinate image determine whether a row is active. All other rows are false;
reading only the selected fibers would lose this part of exact table recovery.
The native raw map is a reader input, never a primitive local value.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.ExplicitRaw

noncomputable section

universe u v

open Site CategoryTheory AtomFoundation GeometryTransport LawAlgebra RealizationReconstruction

variable {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
variable {f : PackageTotalHom G.core H.core} {a : G.Coefficient →+* H.Coefficient}
variable (R : RawAmbientRestrictionSystemExactMapAgainst G.site H.site (coreContextInverse f) a G.raw H.raw)

/-- Read the two coordinate directions at every candidate inverse-context pair. -/
def readCoordinate (W : ArchCtx G.core.object) (V : ArchCtx H.core.object) :
    IndependentInverseGraph.Table.{u, u} := by
  classical
  exact if inverse f V = W then
    IndependentInverseGraph.read _ _ (R.coordinate ⟨V⟩).coordinateEquiv else fun _ => false

/-- Read both relation-generator directions with the same context activation rule. -/
def readRelation (W : ArchCtx G.core.object) (V : ArchCtx H.core.object) :
    IndependentInverseGraph.Table.{u, u} := by
  classical
  exact if inverse f V = W then
    IndependentInverseGraph.read _ _ (R.relation ⟨V⟩).relationEquiv else fun _ => false

/-- Read dependent local-data directions only at the actual carrier pair and coordinate image. -/
def readLocalData (W : ArchCtx G.core.object) (V : ArchCtx H.core.object)
    (C D : Type u) (c : C) (d : D) : IndependentInverseGraph.Table.{u, u} := by
  classical
  exact if inverse f V = W then
    if hC : C = (G.raw.coordFamily ((coreContextInverse f).obj ⟨V⟩)).Coord then
      if hD : D = (H.raw.coordFamily ⟨V⟩).Coord then
        if hd : (R.coordinate ⟨V⟩).coordinateEquiv (hC ▸ c) = hD ▸ d then
          IndependentInverseGraph.read _ _ ((R.coordinate ⟨V⟩).localDataEquiv (hC ▸ c))
        else fun _ => false
      else fun _ => false
    else fun _ => false
  else fun _ => false

/-- At the native inverse context, the coordinate reader is precisely the full inverse graph. -/
theorem readCoordinate_active (V : ArchCtx H.core.object) :
    readCoordinate R (inverse f V) V =
      IndependentInverseGraph.read _ _ (R.coordinate ⟨V⟩).coordinateEquiv := by
  simp [readCoordinate]

/-- Every coordinate cell is false at a mismatching inverse context. -/
theorem readCoordinate_inactive (W : ArchCtx G.core.object) (V : ArchCtx H.core.object)
    (hW : inverse f V ≠ W) : readCoordinate R W V = fun _ => false := by
  simp [readCoordinate, hW]

/-- At the native inverse context, relation reading retains all generator graph cells. -/
theorem readRelation_active (V : ArchCtx H.core.object) :
    readRelation R (inverse f V) V =
      IndependentInverseGraph.read _ _ (R.relation ⟨V⟩).relationEquiv := by
  simp [readRelation]

/-- Every relation cell is false at a mismatching inverse context. -/
theorem readRelation_inactive (W : ArchCtx G.core.object) (V : ArchCtx H.core.object)
    (hW : inverse f V ≠ W) : readRelation R W V = fun _ => false := by
  simp [readRelation, hW]

/-- The selected local-data row reads the entire native equivalence, including inactive value carriers. -/
theorem readLocalData_active (V : ArchCtx H.core.object)
    (c : (G.raw.coordFamily ((coreContextInverse f).obj ⟨V⟩)).Coord) :
    readLocalData R (inverse f V) V _ _ c ((R.coordinate ⟨V⟩).coordinateEquiv c) =
      IndependentInverseGraph.read _ _ ((R.coordinate ⟨V⟩).localDataEquiv c) := by
  simp [readLocalData]

/-- An inactive inverse context also removes every dependent local-data cell. -/
theorem readLocalData_inactive_context (W : ArchCtx G.core.object) (V : ArchCtx H.core.object)
    (C D : Type u) (c : C) (d : D) (hW : inverse f V ≠ W) :
    readLocalData R W V C D c d = fun _ => false := by
  simp [readLocalData, hW]

/-- A false coordinate graph point forces all dependent local-data cells to be false. -/
theorem readLocalData_inactive_coordinate (W : ArchCtx G.core.object) (V : ArchCtx H.core.object)
    (C D : Type u) (c : C) (d : D)
    (hc : readCoordinate R W V (.forward (.edge C D c d)) = false) :
    readLocalData R W V C D c d = fun _ => false := by
  classical
  by_cases hW : inverse f V = W
  · subst W
    by_cases hC : C = (G.raw.coordFamily ((coreContextInverse f).obj ⟨V⟩)).Coord
    · subst C
      by_cases hD : D = (H.raw.coordFamily ⟨V⟩).Coord
      · subst D
        have hd : (R.coordinate ⟨V⟩).coordinateEquiv c ≠ d := by
          intro he
          have ht := (IndependentCarrierGraph.read_edge _ _ (R.coordinate ⟨V⟩).coordinateEquiv c d).2 he
          rw [readCoordinate_active] at hc
          exact Bool.noConfusion (hc.symm.trans ht)
        simp [readLocalData, hd]
      · simp [readLocalData, hD]
    · simp [readLocalData, hC]
  · exact readLocalData_inactive_context R W V C D c d hW

end

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.ExplicitRaw

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.ExplicitRaw
