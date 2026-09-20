import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomSignatureComposition
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomObservableComposition
import ResearchLean.AG.LocalSemanticReconstruction.IndependentIndexedInverseCompositionFinite
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomFullSeparation
import Formal.Util.AssertStandardAxioms

/-!
# Finite fragments for common signature and observable composition

Each coordinate or observable output uses one first-index flag, one second-index
flag, and at most two inverse-fiber points. The embeddings below use the original
common Hom query constructors, including their backward pair order. The final
statements concern actual finite fragments after invariant witness erasure.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive

noncomputable section

universe u v

open Site AtomFoundation GeometryTransport IndependentGeometryTableAssembly

namespace InvariantWitness

/-- Equality of actual finite fragments is exactly equality of the retained common points on that finite set. -/
theorem fragment_eq_iff_points {U : AtomCarrier.{u}} {mode : Mode} (I J : InvariantFamily U)
    (p q : Local.{u, v} I J mode) (S : Finset (IndependentGeometryHomPrimitive.Query.{u, v} U mode)) :
    fragment I J p S = fragment I J q S ↔ ∀ a ∈ S, (retained I J p).table a = (retained I J q).table a := by
  constructor
  · intro he a ha
    exact (NativeReader.local_fragment_point I J p S ⟨a, ha⟩).symm.trans
      ((congrFun he ⟨a, ha⟩).trans (NativeReader.local_fragment_point I J q S ⟨a, ha⟩))
  · intro he
    funext a
    exact (NativeReader.local_fragment_point I J p S a).trans
      ((he a.val a.property).trans (NativeReader.local_fragment_point I J q S a).symm)

end InvariantWitness

namespace Composition

variable {U : AtomCarrier.{u}} {mode : Mode} (s t r : ObjectData.{u, v} U)
variable (p : InvariantWitness.Local.{u, v}
  (assemble s).core.reading.invariantReading (assemble t).core.reading.invariantReading mode)
variable (hp : PackageAssembly.PointLaws s.1 t.1 (PackageAssembly.retained s.1 t.1 p).table)
variable (q : InvariantWitness.Local.{u, v}
  (assemble t).core.reading.invariantReading (assemble r).core.reading.invariantReading mode)
variable (hq : PackageAssembly.PointLaws t.1 r.1 (PackageAssembly.retained t.1 r.1 q).table)

/-- Every signature-composition output is fixed by at most four original common query cells. -/
theorem signatureRows_finite_support (a : IndependentCandidateIndexedInverseGraph.Query.{u, u, u, u}) :
    ∃ (D E : Finset (Query.{u, v} U mode)), D.card + E.card ≤ 4 ∧
      ∀ (p' : InvariantWitness.Local.{u, v}
          (assemble s).core.reading.invariantReading (assemble t).core.reading.invariantReading mode)
        (hp' : PackageAssembly.PointLaws s.1 t.1 (PackageAssembly.retained s.1 t.1 p').table)
        (q' : InvariantWitness.Local.{u, v}
          (assemble t).core.reading.invariantReading (assemble r).core.reading.invariantReading mode)
        (hq' : PackageAssembly.PointLaws t.1 r.1 (PackageAssembly.retained t.1 r.1 q').table),
        (∀ a ∈ D, (PackageAssembly.retained s.1 t.1 p).table a = (PackageAssembly.retained s.1 t.1 p').table a) →
        (∀ a ∈ E, (PackageAssembly.retained t.1 r.1 q).table a = (PackageAssembly.retained t.1 r.1 q').table a) →
        signatureRows s t r p hp q hq a = signatureRows s t r p' hp' q' hq' a := by
  classical
  let I := (assemble s).core.algebra.signatureReading.Axis
  let J := (assemble t).core.algebra.signatureReading.Axis
  let K := (assemble r).core.algebra.signatureReading.Axis
  cases a with
  | edge X Y i l a =>
    by_cases hX : X = I
    · subst X
      by_cases hY : Y = K
      · subst Y
        let leftIndex : I × J → Query.{u, v} U mode := fun ij => .signatureAxis (.edge I J ij.1 ij.2)
        let rightIndex : J × K → Query.{u, v} U mode := fun jl => .signatureAxis (.edge J K jl.1 jl.2)
        let leftRow : IndependentIndexedInverseGraph.Query.{u, u, u, u} I J → Query.{u, v} U mode
          | .edge i j (.forward a) => .signatureCoordinate .forward I J i j a
          | .edge i j (.backward a) => .signatureCoordinate .backward I J i j (InverseRows.reverse a)
        let rightRow : IndependentIndexedInverseGraph.Query.{u, u, u, u} J K → Query.{u, v} U mode
          | .edge j l (.forward a) => .signatureCoordinate .forward J K j l a
          | .edge j l (.backward a) => .signatureCoordinate .backward J K j l (InverseRows.reverse a)
        obtain ⟨D, E, hcard, hs⟩ := IndependentIndexedInverseGraph.composeRows_lifted_finite_support
          leftIndex rightIndex leftRow rightRow
          (fun h => IndependentCandidateIndexedInverseGraph.project (Signature.points h) I J)
          (fun k => IndependentCandidateIndexedInverseGraph.project (Signature.points k) J K)
          (by intro h a; cases a with | edge i j a => cases a <;> rfl)
          (by intro k a; cases a with | edge j l a => cases a <;> rfl)
          (assemble s).core.algebra.signatureReading.Coordinate (assemble t).core.algebra.signatureReading.Coordinate
          (assemble r).core.algebra.signatureReading.Coordinate
          (PackageAssembly.retained s.1 t.1 p).table (PackageAssembly.retained t.1 r.1 q).table
          hp.axisRows.2 hp.coordinateRows.selected hq.coordinateRows.selected (.edge i l a)
        refine ⟨D, E, hcard, ?_⟩
        intro p' hp' q' hq' hD hE
        have hv := hs (PackageAssembly.retained s.1 t.1 p').table (PackageAssembly.retained t.1 r.1 q').table
          hp'.axisRows.2 hp'.coordinateRows.selected hq'.coordinateRows.selected hD hE
        exact (congrFun (IndependentCandidateIndexedInverseGraph.project_extend I K _) (.edge i l a)).trans
          (hv.trans (congrFun (IndependentCandidateIndexedInverseGraph.project_extend I K _) (.edge i l a)).symm)
      · refine ⟨∅, ∅, by simp, ?_⟩
        intro p' hp' q' hq' _ _
        exact (IndependentCandidateIndexedInverseGraph.extend_inactive I K _ I Y i l a (Or.inr hY)).trans
          (IndependentCandidateIndexedInverseGraph.extend_inactive I K _ I Y i l a (Or.inr hY)).symm
    · refine ⟨∅, ∅, by simp, ?_⟩
      intro p' hp' q' hq' _ _
      exact (IndependentCandidateIndexedInverseGraph.extend_inactive I K _ X Y i l a (Or.inl hX)).trans
        (IndependentCandidateIndexedInverseGraph.extend_inactive I K _ X Y i l a (Or.inl hX)).symm

/-- Signature composition is determined by actual finite fragments after witness erasure, using at most four cells. -/
theorem signatureRows_finite_fragment (a : IndependentCandidateIndexedInverseGraph.Query.{u, u, u, u}) :
    ∃ (D E : Finset (Query.{u, v} U mode)), D.card + E.card ≤ 4 ∧
      ∀ (p' : InvariantWitness.Local.{u, v}
          (assemble s).core.reading.invariantReading (assemble t).core.reading.invariantReading mode)
        (hp' : PackageAssembly.PointLaws s.1 t.1 (PackageAssembly.retained s.1 t.1 p').table)
        (q' : InvariantWitness.Local.{u, v}
          (assemble t).core.reading.invariantReading (assemble r).core.reading.invariantReading mode)
        (hq' : PackageAssembly.PointLaws t.1 r.1 (PackageAssembly.retained t.1 r.1 q').table),
        InvariantWitness.fragment _ _ p D = InvariantWitness.fragment _ _ p' D →
        InvariantWitness.fragment _ _ q E = InvariantWitness.fragment _ _ q' E →
        signatureRows s t r p hp q hq a = signatureRows s t r p' hp' q' hq' a := by
  obtain ⟨D, E, hcard, hs⟩ := signatureRows_finite_support s t r p hp q hq a
  refine ⟨D, E, hcard, ?_⟩
  intro p' hp' q' hq' hD hE
  exact hs p' hp' q' hq' ((InvariantWitness.fragment_eq_iff_points _ _ p p' D).1 hD)
    ((InvariantWitness.fragment_eq_iff_points _ _ q q' E).1 hE)

/-- Every observable-composition output is fixed by at most four original context and inverse-value cells. -/
theorem observableRows_finite_support
    (a : IndependentIndexedInverseGraph.Query.{u + 1, u + 1, u, u}
      (ArchCtx (assemble s).core.object) (ArchCtx (assemble r).core.object)) :
    ∃ (D E : Finset (Query.{u, v} U mode)), D.card + E.card ≤ 4 ∧
      ∀ (p' : InvariantWitness.Local.{u, v}
          (assemble s).core.reading.invariantReading (assemble t).core.reading.invariantReading mode)
        (hp' : PackageAssembly.PointLaws s.1 t.1 (PackageAssembly.retained s.1 t.1 p').table)
        (q' : InvariantWitness.Local.{u, v}
          (assemble t).core.reading.invariantReading (assemble r).core.reading.invariantReading mode)
        (hq' : PackageAssembly.PointLaws t.1 r.1 (PackageAssembly.retained t.1 r.1 q').table),
        (∀ a ∈ D, (PackageAssembly.retained s.1 t.1 p).table a = (PackageAssembly.retained s.1 t.1 p').table a) →
        (∀ a ∈ E, (PackageAssembly.retained t.1 r.1 q).table a = (PackageAssembly.retained t.1 r.1 q').table a) →
        observableRows s t r p hp q hq a = observableRows s t r p' hp' q' hq' a := by
  letI := ObservableNatural.rings (s.1.val.2.2.1.val) (s.1.val.2.2.1.property.choose) (s.1.val.2.2.1.property.choose_spec)
  letI := ObservableNatural.rings (t.1.val.2.2.1.val) (t.1.val.2.2.1.property.choose) (t.1.val.2.2.1.property.choose_spec)
  letI := ObservableNatural.rings (r.1.val.2.2.1.val) (r.1.val.2.2.1.property.choose) (r.1.val.2.2.1.property.choose_spec)
  let A := (assemble s).core.object
  let B := (assemble t).core.object
  let C := (assemble r).core.object
  let leftIndex : ArchCtx A × ArchCtx B → Query.{u, v} U mode := fun ij => .atObjects A B (.context .forward ij.1 ij.2)
  let rightIndex : ArchCtx B × ArchCtx C → Query.{u, v} U mode := fun jl => .atObjects B C (.context .forward jl.1 jl.2)
  let leftRow : IndependentIndexedInverseGraph.Query.{u + 1, u + 1, u, u} (ArchCtx A) (ArchCtx B) → Query.{u, v} U mode
    | .edge i j (.forward a) => .atObjects A B (.observable .forward i j a)
    | .edge i j (.backward a) => .atObjects A B (.observable .backward i j (InverseRows.reverse a))
  let rightRow : IndependentIndexedInverseGraph.Query.{u + 1, u + 1, u, u} (ArchCtx B) (ArchCtx C) → Query.{u, v} U mode
    | .edge j l (.forward a) => .atObjects B C (.observable .forward j l a)
    | .edge j l (.backward a) => .atObjects B C (.observable .backward j l (InverseRows.reverse a))
  obtain ⟨D, E, hcard, hs⟩ := IndependentIndexedInverseGraph.composeRows_lifted_finite_support
    leftIndex rightIndex leftRow rightRow
    (fun h => Observable.points h A B) (fun k => Observable.points k B C)
    (by intro h a; cases a with | edge i j a => cases a <;> rfl)
    (by intro k a; cases a with | edge j l a => cases a <;> rfl)
    (fun W => (assemble s).core.equationSystem.Observable ⟨W⟩)
    (fun V => (assemble t).core.equationSystem.Observable ⟨V⟩)
    (fun Z => (assemble r).core.equationSystem.Observable ⟨Z⟩)
    (PackageAssembly.retained s.1 t.1 p).table (PackageAssembly.retained t.1 r.1 q).table
    hp.contextRows.forward hp.observableRows.graphs hq.observableRows.graphs a
  refine ⟨D, E, hcard, ?_⟩
  intro p' hp' q' hq' hD hE
  exact hs (PackageAssembly.retained s.1 t.1 p').table (PackageAssembly.retained t.1 r.1 q').table
    hp'.contextRows.forward hp'.observableRows.graphs hq'.observableRows.graphs hD hE

/-- Observable composition is determined by actual finite quotient fragments, using at most four cells. -/
theorem observableRows_finite_fragment
    (a : IndependentIndexedInverseGraph.Query.{u + 1, u + 1, u, u}
      (ArchCtx (assemble s).core.object) (ArchCtx (assemble r).core.object)) :
    ∃ (D E : Finset (Query.{u, v} U mode)), D.card + E.card ≤ 4 ∧
      ∀ (p' : InvariantWitness.Local.{u, v}
          (assemble s).core.reading.invariantReading (assemble t).core.reading.invariantReading mode)
        (hp' : PackageAssembly.PointLaws s.1 t.1 (PackageAssembly.retained s.1 t.1 p').table)
        (q' : InvariantWitness.Local.{u, v}
          (assemble t).core.reading.invariantReading (assemble r).core.reading.invariantReading mode)
        (hq' : PackageAssembly.PointLaws t.1 r.1 (PackageAssembly.retained t.1 r.1 q').table),
        InvariantWitness.fragment _ _ p D = InvariantWitness.fragment _ _ p' D →
        InvariantWitness.fragment _ _ q E = InvariantWitness.fragment _ _ q' E →
        observableRows s t r p hp q hq a = observableRows s t r p' hp' q' hq' a := by
  obtain ⟨D, E, hcard, hs⟩ := observableRows_finite_support s t r p hp q hq a
  refine ⟨D, E, hcard, ?_⟩
  intro p' hp' q' hq' hD hE
  exact hs p' hp' q' hq' ((InvariantWitness.fragment_eq_iff_points _ _ p p' D).1 hD)
    ((InvariantWitness.fragment_eq_iff_points _ _ q q' E).1 hE)

end Composition

end

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.InvariantWitness
#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.Composition
