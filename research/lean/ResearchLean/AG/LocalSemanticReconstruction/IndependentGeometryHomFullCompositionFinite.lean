import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomFullTableComposition
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomOperationCompositionFinite
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomAlgebraicCompositionFinite
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomRepresentativeRealizationCompositionFinite
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomExplicitRealizationCompositionFinite
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomRawLocalDataCompositionFinite
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomFullLocalComposition
import Formal.Util.AssertStandardAxioms

/-!
# Finite support for complete local Hom composition

Every common query output, every finite output set, and the corresponding
fragment of the completed local composite are reduced to two finite input
fragments in both Hom modes.

Implementation notes: candidates bundle the existing point-law proofs because
dependent intermediate types vary with the retained tables. Supports may
depend on the input and output query; no finite determination of an entire Hom
or of a quantified law family is asserted.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.Composition

noncomputable section

universe u v

open Site AtomFoundation GeometryTransport IndependentGeometryTableAssembly

variable {U : AtomCarrier.{u}} {mode : Mode} (s t r : ObjectData.{u, v} U)

/-- One lawful pair of local Hom presentations, bundled so finite-support
arguments can vary every law proof together with the two retained tables. -/
structure FiniteCandidate where
  /-- First local quotient class. -/
  p : InvariantWitness.Local.{u, v}
    (assemble s).core.reading.invariantReading (assemble t).core.reading.invariantReading mode
  /-- Package point laws for the first class. -/
  hp : PackageAssembly.PointLaws s.1 t.1 (PackageAssembly.retained s.1 t.1 p).table
  /-- Second local quotient class. -/
  q : InvariantWitness.Local.{u, v}
    (assemble t).core.reading.invariantReading (assemble r).core.reading.invariantReading mode
  /-- Package point laws for the second class. -/
  hq : PackageAssembly.PointLaws t.1 r.1 (PackageAssembly.retained t.1 r.1 q).table
  /-- Directed coefficient points for the first class. -/
  cp : GeometryComponents.CoefficientPoints s t p

/-- The first retained common table of a composition candidate. -/
abbrev FiniteCandidate.left (c : FiniteCandidate (mode := mode) s t r) : Table.{u, v} U mode :=
  (PackageAssembly.retained s.1 t.1 c.p).table

/-- The second retained common table of a composition candidate. -/
abbrev FiniteCandidate.right (c : FiniteCandidate (mode := mode) s t r) : Table.{u, v} U mode :=
  (PackageAssembly.retained t.1 r.1 c.q).table

variable {s t r}

/-- A composed equation-index point is fixed by at most two equation cells in
the original retained declarations. -/
theorem equation_finite_support (c : FiniteCandidate (mode := mode) s t r)
    (d : Direction) (a : IndependentCarrierGraph.Query.{u, u}) :
    ∃ (D E : Finset (Query.{u, v} U mode)),
      ∀ c' : FiniteCandidate (mode := mode) s t r,
        (∀ q ∈ D, (FiniteCandidate.left (s := s) (t := t) (r := r) c) q = (FiniteCandidate.left (s := s) (t := t) (r := r) c') q) →
        (∀ q ∈ E, (FiniteCandidate.right (s := s) (t := t) (r := r) c) q = (FiniteCandidate.right (s := s) (t := t) (r := r) c') q) →
        dependentIndices s t r c.p c.hp c.q c.hq (.equation d a) =
          dependentIndices s t r c'.p c'.hp c'.q c'.hq (.equation d a) := by
  classical
  let leftQuery : IndependentInverseGraph.Query.{u, u} → Query.{u, v} U mode
    | .forward q => .atObjects (assemble s).core.object (assemble t).core.object
        (.equation .forward q)
    | .backward q => .atObjects (assemble s).core.object (assemble t).core.object
        (.equation .backward (InverseRows.reverse q))
  let rightQuery : IndependentInverseGraph.Query.{u, u} → Query.{u, v} U mode
    | .forward q => .atObjects (assemble t).core.object (assemble r).core.object
        (.equation .forward q)
    | .backward q => .atObjects (assemble t).core.object (assemble r).core.object
        (.equation .backward (InverseRows.reverse q))
  let z : IndependentInverseGraph.Query.{u, u} := match d with
    | .forward => .forward a
    | .backward => .backward (InverseRows.reverse a)
  obtain ⟨L, R, _, hs⟩ := IndependentInverseGraph.compose_finite_support
    (assemble s).core.equationSystem.Index (assemble t).core.equationSystem.Index
    (assemble r).core.equationSystem.Index
    (InverseRows.equation (FiniteCandidate.left (s := s) (t := t) (r := r) c) (assemble s).core.object (assemble t).core.object)
    c.hp.equationRows
    (InverseRows.equation (FiniteCandidate.right (s := s) (t := t) (r := r) c) (assemble t).core.object (assemble r).core.object)
    c.hq.equationRows z
  refine ⟨L.image leftQuery, R.image rightQuery, ?_⟩
  intro c' hL hR
  have hv := hs
    (InverseRows.equation (FiniteCandidate.left (s := s) (t := t) (r := r) c') (assemble s).core.object (assemble t).core.object)
    c'.hp.equationRows
    (InverseRows.equation (FiniteCandidate.right (s := s) (t := t) (r := r) c') (assemble t).core.object (assemble r).core.object)
    c'.hq.equationRows
    (by
      intro q hq
      cases q with
      | forward q => exact hL _ (Finset.mem_image_of_mem _ hq)
      | backward q => exact hL _ (Finset.mem_image_of_mem _ hq))
    (by
      intro q hq
      cases q with
      | forward q => exact hR _ (Finset.mem_image_of_mem _ hq)
      | backward q => exact hR _ (Finset.mem_image_of_mem _ hq))
  cases d with
  | forward => exact hv
  | backward => exact hv

/-- One composed context point is fixed by two original context cells. -/
theorem context_finite_support (c : FiniteCandidate (mode := mode) s t r)
    (d : Direction) (W : ArchCtx (assemble s).core.object)
    (Z : ArchCtx (assemble r).core.object) :
    ∃ (D E : Finset (Query.{u, v} U mode)),
      ∀ c' : FiniteCandidate (mode := mode) s t r,
        (∀ q ∈ D, (FiniteCandidate.left (s := s) (t := t) (r := r) c) q = (FiniteCandidate.left (s := s) (t := t) (r := r) c') q) →
        (∀ q ∈ E, (FiniteCandidate.right (s := s) (t := t) (r := r) c) q = (FiniteCandidate.right (s := s) (t := t) (r := r) c') q) →
        dependentIndices s t r c.p c.hp c.q c.hq (.context d W Z) =
          dependentIndices s t r c'.p c'.hp c'.q c'.hq (.context d W Z) := by
  classical
  cases d with
  | forward =>
    let V := IndependentIndexedCarrierGraph.index
      (Context.points (FiniteCandidate.left (s := s) (t := t) (r := r) c) (assemble s).core.object (assemble t).core.object .forward)
      c.hp.contextRows.forward W
    refine ⟨{.atObjects (assemble s).core.object (assemble t).core.object
        (.context .forward W V)},
      {.atObjects (assemble t).core.object (assemble r).core.object
        (.context .forward V Z)}, ?_⟩
    intro c' hD hE
    exact Context.compose_forward_support _ _ _
      (Context.points (FiniteCandidate.left (s := s) (t := t) (r := r) c) (assemble s).core.object (assemble t).core.object)
      (Context.points (FiniteCandidate.left (s := s) (t := t) (r := r) c') (assemble s).core.object (assemble t).core.object)
      c.hp.contextRows c'.hp.contextRows
      (Context.points (FiniteCandidate.right (s := s) (t := t) (r := r) c) (assemble t).core.object (assemble r).core.object)
      (Context.points (FiniteCandidate.right (s := s) (t := t) (r := r) c') (assemble t).core.object (assemble r).core.object)
      c.hq.contextRows c'.hq.contextRows W Z
      (hD _ (by simp [V])) (hE _ (by simp [V]))
  | backward =>
    let V := IndependentIndexedCarrierGraph.index
      (fun Z V => Context.points (FiniteCandidate.right (s := s) (t := t) (r := r) c) (assemble t).core.object
        (assemble r).core.object .backward V Z)
      c.hq.contextRows.backward Z
    refine ⟨{.atObjects (assemble s).core.object (assemble t).core.object
        (.context .backward W V)},
      {.atObjects (assemble t).core.object (assemble r).core.object
        (.context .backward V Z)}, ?_⟩
    intro c' hD hE
    exact Context.compose_backward_support _ _ _
      (Context.points (FiniteCandidate.left (s := s) (t := t) (r := r) c) (assemble s).core.object (assemble t).core.object)
      (Context.points (FiniteCandidate.left (s := s) (t := t) (r := r) c') (assemble s).core.object (assemble t).core.object)
      c.hp.contextRows c'.hp.contextRows
      (Context.points (FiniteCandidate.right (s := s) (t := t) (r := r) c) (assemble t).core.object (assemble r).core.object)
      (Context.points (FiniteCandidate.right (s := s) (t := t) (r := r) c') (assemble t).core.object (assemble r).core.object)
      c.hq.contextRows c'.hq.contextRows W Z
      (hE _ (by simp [V])) (hD _ (by simp [V]))

/-- Every scalar or index output used by the complete composition table has a
finite support in the two retained common declarations. -/
theorem indices_finite_support (c : FiniteCandidate (mode := mode) s t r)
    (a : Query.{u, v} U mode) :
    ∃ (D E : Finset (Query.{u, v} U mode)),
      ∀ c' : FiniteCandidate (mode := mode) s t r,
        (∀ q ∈ D, (FiniteCandidate.left (s := s) (t := t) (r := r) c) q =
          (FiniteCandidate.left (s := s) (t := t) (r := r) c') q) →
        (∀ q ∈ E, (FiniteCandidate.right (s := s) (t := t) (r := r) c) q =
          (FiniteCandidate.right (s := s) (t := t) (r := r) c') q) →
        indices s t r c.p c.hp c.q c.hq c.cp a =
          indices s t r c'.p c'.hp c'.q c'.hq c'.cp a := by
  classical
  let h := FiniteCandidate.left (s := s) (t := t) (r := r) c
  let k := FiniteCandidate.right (s := s) (t := t) (r := r) c
  cases a with
  | source a =>
    obtain ⟨D, E, _, hs⟩ := IndependentCarrierGraph.compose_finite_support
      (assemble s).core.reading.doctrine.Source (assemble t).core.reading.doctrine.Source
      (assemble r).core.reading.doctrine.Source (source h) c.hp.extraction.source (source k) a
    refine ⟨D.image Query.source, E.image Query.source, ?_⟩
    intro c' hD hE
    exact hs (source (FiniteCandidate.left (s := s) (t := t) (r := r) c'))
      c'.hp.extraction.source (source (FiniteCandidate.right (s := s) (t := t) (r := r) c'))
      (fun q hq => hD _ (Finset.mem_image_of_mem _ hq))
      (fun q hq => hE _ (Finset.mem_image_of_mem _ hq))
  | pointedAtom d a z =>
    cases d with
    | forward =>
      let b := Atom.assemble (Atom.pointed h) c.hp.atom.pointed a
      refine ⟨{.pointedAtom .forward a b}, {.pointedAtom .forward b z}, ?_⟩
      intro c' hD hE
      exact Atom.compose_forward_support (Atom.pointed h)
        (Atom.pointed (FiniteCandidate.left (s := s) (t := t) (r := r) c'))
        c.hp.atom.pointed c'.hp.atom.pointed (Atom.pointed k)
        (Atom.pointed (FiniteCandidate.right (s := s) (t := t) (r := r) c'))
        c.hq.atom.pointed c'.hq.atom.pointed a z
        (hD _ (by simp [b])) (hE _ (by simp [b]))
    | backward =>
      let b := (Atom.assemble (Atom.pointed k) c.hq.atom.pointed).symm z
      refine ⟨{.pointedAtom .backward a b}, {.pointedAtom .backward b z}, ?_⟩
      intro c' hD hE
      exact Atom.compose_backward_support (Atom.pointed h)
        (Atom.pointed (FiniteCandidate.left (s := s) (t := t) (r := r) c'))
        c.hp.atom.pointed c'.hp.atom.pointed (Atom.pointed k)
        (Atom.pointed (FiniteCandidate.right (s := s) (t := t) (r := r) c'))
        c.hq.atom.pointed c'.hq.atom.pointed a z
        (hE _ (by simp [b])) (hD _ (by simp [b]))
  | atom d a z =>
    cases d with
    | forward =>
      let b := Atom.assemble (Atom.upper h) c.hp.atom.upper a
      refine ⟨{.atom .forward a b}, {.atom .forward b z}, ?_⟩
      intro c' hD hE
      exact Atom.compose_forward_support (Atom.upper h)
        (Atom.upper (FiniteCandidate.left (s := s) (t := t) (r := r) c'))
        c.hp.atom.upper c'.hp.atom.upper (Atom.upper k)
        (Atom.upper (FiniteCandidate.right (s := s) (t := t) (r := r) c'))
        c.hq.atom.upper c'.hq.atom.upper a z
        (hD _ (by simp [b])) (hE _ (by simp [b]))
    | backward =>
      let b := (Atom.assemble (Atom.upper k) c.hq.atom.upper).symm z
      refine ⟨{.atom .backward a b}, {.atom .backward b z}, ?_⟩
      intro c' hD hE
      exact Atom.compose_backward_support (Atom.upper h)
        (Atom.upper (FiniteCandidate.left (s := s) (t := t) (r := r) c'))
        c.hp.atom.upper c'.hp.atom.upper (Atom.upper k)
        (Atom.upper (FiniteCandidate.right (s := s) (t := t) (r := r) c'))
        c.hq.atom.upper c'.hq.atom.upper a z
        (hE _ (by simp [b])) (hD _ (by simp [b]))
  | object A C =>
    let B := CoreLaws.objectMap h (PackageAssembly.retained s.1 t.1 c.p).objectRows A
    have hAB : h (.object A B) = true :=
      (CoreLaws.objectGraph h (PackageAssembly.retained s.1 t.1 c.p).objectRows).edge_target A
    refine ⟨{.object A B}, {.object B C}, ?_⟩
    intro c' hD hE
    have hAB' : (FiniteCandidate.left (s := s) (t := t) (r := r) c') (.object A B) = true :=
      (hD _ (by simp)).symm.trans hAB
    have hB : CoreLaws.objectMap
        (FiniteCandidate.left (s := s) (t := t) (r := r) c')
        (PackageAssembly.retained s.1 t.1 c'.p).objectRows A = B :=
      (CoreLaws.objectGraph _ (PackageAssembly.retained s.1 t.1 c'.p).objectRows).target_eq_of_edge hAB'
    change k (.object B C) =
      (FiniteCandidate.right (s := s) (t := t) (r := r) c') (.object _ C)
    rw [hB]
    exact hE _ (by simp)
  | invariant a =>
    obtain ⟨D, E, _, hs⟩ := IndependentCarrierGraph.compose_finite_support
      (assemble s).core.reading.invariantReading.Index
      (assemble t).core.reading.invariantReading.Index
      (assemble r).core.reading.invariantReading.Index
      (invariant h) (PackageAssembly.retained s.1 t.1 c.p).indexRows (invariant k) a
    refine ⟨D.image Query.invariant, E.image Query.invariant, ?_⟩
    intro c' hD hE
    exact hs (invariant (FiniteCandidate.left (s := s) (t := t) (r := r) c'))
      (PackageAssembly.retained s.1 t.1 c'.p).indexRows
      (invariant (FiniteCandidate.right (s := s) (t := t) (r := r) c'))
      (fun q hq => hD _ (Finset.mem_image_of_mem _ hq))
      (fun q hq => hE _ (Finset.mem_image_of_mem _ hq))
  | signatureAxis a =>
    obtain ⟨D, E, _, hs⟩ := IndependentCarrierGraph.compose_finite_support
      (assemble s).core.algebra.signatureReading.Axis
      (assemble t).core.algebra.signatureReading.Axis
      (assemble r).core.algebra.signatureReading.Axis
      (signatureAxis h) c.hp.axisRows (signatureAxis k) a
    refine ⟨D.image Query.signatureAxis, E.image Query.signatureAxis, ?_⟩
    intro c' hD hE
    exact hs (signatureAxis (FiniteCandidate.left (s := s) (t := t) (r := r) c')) c'.hp.axisRows
      (signatureAxis (FiniteCandidate.right (s := s) (t := t) (r := r) c'))
      (fun q hq => hD _ (Finset.mem_image_of_mem _ hq))
      (fun q hq => hE _ (Finset.mem_image_of_mem _ hq))
  | coefficient a =>
    obtain ⟨D, E, _, hs⟩ := IndependentCarrierGraph.compose_finite_support
      (assemble s).Coefficient (assemble t).Coefficient (assemble r).Coefficient
      (coefficient h) c.cp.1 (coefficient k) a
    refine ⟨D.image Query.coefficient, E.image Query.coefficient, ?_⟩
    intro c' hD hE
    exact hs (coefficient (FiniteCandidate.left (s := s) (t := t) (r := r) c')) c'.cp.1
      (coefficient (FiniteCandidate.right (s := s) (t := t) (r := r) c'))
      (fun q hq => hD _ (Finset.mem_image_of_mem _ hq))
      (fun q hq => hE _ (Finset.mem_image_of_mem _ hq))
  | familyTransport F F' =>
    let M := F.transport (Atom.assemble (Atom.upper h) c.hp.atom.upper)
    have hFM : h (.familyTransport F M) = true :=
      (TransportMatch.family_iff h c.hp.atom.upper c.hp.matching F M).2 rfl
    refine ⟨{.familyTransport F M}, {.familyTransport M F'}, ?_⟩
    intro c' hD hE
    have hFM' : (FiniteCandidate.left (s := s) (t := t) (r := r) c')
        (.familyTransport F M) = true := (hD _ (by simp)).symm.trans hFM
    have hM := (TransportMatch.family_iff
      (FiniteCandidate.left (s := s) (t := t) (r := r) c')
      c'.hp.atom.upper c'.hp.matching F M).1 hFM'
    change M = F.transport (Atom.assemble
      (Atom.upper (FiniteCandidate.left (s := s) (t := t) (r := r) c'))
      c'.hp.atom.upper) at hM
    change k (.familyTransport M F') =
      (FiniteCandidate.right (s := s) (t := t) (r := r) c')
        (.familyTransport (F.transport _) F')
    rw [← hM]
    exact hE _ (by simp)
  | configurationTransport C C' =>
    let M := C.transport (Atom.assemble (Atom.upper h) c.hp.atom.upper)
    have hCM : h (.configurationTransport C M) = true :=
      (TransportMatch.configuration_iff h c.hp.atom.upper c.hp.matching C M).2 rfl
    refine ⟨{.configurationTransport C M}, {.configurationTransport M C'}, ?_⟩
    intro c' hD hE
    have hCM' : (FiniteCandidate.left (s := s) (t := t) (r := r) c')
        (.configurationTransport C M) = true := (hD _ (by simp)).symm.trans hCM
    have hM := (TransportMatch.configuration_iff
      (FiniteCandidate.left (s := s) (t := t) (r := r) c')
      c'.hp.atom.upper c'.hp.matching C M).1 hCM'
    change M = C.transport (Atom.assemble
      (Atom.upper (FiniteCandidate.left (s := s) (t := t) (r := r) c'))
      c'.hp.atom.upper) at hM
    change k (.configurationTransport M C') =
      (FiniteCandidate.right (s := s) (t := t) (r := r) c')
        (.configurationTransport (C.transport _) C')
    rw [← hM]
    exact hE _ (by simp)
  | atObjects A C z =>
    by_cases hA : A = (assemble s).core.object
    · subst A
      by_cases hC : C = (assemble r).core.object
      · subst C
        cases z with
        | equation d a =>
          obtain ⟨D, E, hs⟩ := equation_finite_support c d a
          refine ⟨D, E, ?_⟩
          intro c' hD hE
          simpa [indices, NativeReader.liftDependent] using hs c' hD hE
        | context d W Z =>
          obtain ⟨D, E, hs⟩ := context_finite_support c d W Z
          refine ⟨D, E, ?_⟩
          intro c' hD hE
          simpa [indices, NativeReader.liftDependent] using hs c' hD hE
        | observable | raw | realization =>
          refine ⟨∅, ∅, ?_⟩
          intro c' _ _
          rfl
      · refine ⟨∅, ∅, ?_⟩
        intro c' _ _
        simp [indices, NativeReader.liftDependent, hC]
    · refine ⟨∅, ∅, ?_⟩
      intro c' _ _
      simp [indices, NativeReader.liftDependent, hA]
  | operation A B A' B' a =>
    refine ⟨∅, ∅, ?_⟩
    intro c' _ _
    rfl
  | signatureCoordinate d I J i j a =>
    refine ⟨∅, ∅, ?_⟩
    intro c' _ _
    rfl

/-- One output of the complete common composition table has finite support,
provided the two mode-specific extension rows do. -/
theorem composeWith_finite_support
    {P : Type*} (core : P → FiniteCandidate (mode := mode) s t r) (c : P)
    (raw : P →
      RawQuery (assemble s).core.object (assemble r).core.object mode → Bool)
    (realization : P →
      RealizationQuery (assemble s).core.object (assemble r).core.object mode → Bool)
    (rawSupport : ∀ a, ∃ (D E : Finset (Query.{u, v} U mode)),
      ∀ c' : P,
        (∀ q ∈ D, (FiniteCandidate.left (s := s) (t := t) (r := r) (core c)) q =
          (FiniteCandidate.left (s := s) (t := t) (r := r) (core c')) q) →
        (∀ q ∈ E, (FiniteCandidate.right (s := s) (t := t) (r := r) (core c)) q =
          (FiniteCandidate.right (s := s) (t := t) (r := r) (core c')) q) →
        raw c a = raw c' a)
    (realizationSupport : ∀ a, ∃ (D E : Finset (Query.{u, v} U mode)),
      ∀ c' : P,
        (∀ q ∈ D, (FiniteCandidate.left (s := s) (t := t) (r := r) (core c)) q =
          (FiniteCandidate.left (s := s) (t := t) (r := r) (core c')) q) →
        (∀ q ∈ E, (FiniteCandidate.right (s := s) (t := t) (r := r) (core c)) q =
          (FiniteCandidate.right (s := s) (t := t) (r := r) (core c')) q) →
        realization c a = realization c' a)
    (a : Query.{u, v} U mode) :
    ∃ (D E : Finset (Query.{u, v} U mode)),
      ∀ c' : P,
        (∀ q ∈ D, (FiniteCandidate.left (s := s) (t := t) (r := r) (core c)) q =
          (FiniteCandidate.left (s := s) (t := t) (r := r) (core c')) q) →
        (∀ q ∈ E, (FiniteCandidate.right (s := s) (t := t) (r := r) (core c)) q =
          (FiniteCandidate.right (s := s) (t := t) (r := r) (core c')) q) →
        composeWith s t r (core c).p (core c).hp (core c).q (core c).hq (raw c) (realization c) (core c).cp a =
          composeWith s t r (core c').p (core c').hp (core c').q (core c').hq (raw c') (realization c') (core c').cp a := by
  classical
  cases a with
  | source a =>
    obtain ⟨D, E, hs⟩ := indices_finite_support (core c) (.source a)
    exact ⟨D, E, fun c' hD hE => hs (core c') hD hE⟩
  | pointedAtom d a z =>
    obtain ⟨D, E, hs⟩ := indices_finite_support (core c) (.pointedAtom d a z)
    exact ⟨D, E, fun c' hD hE => hs (core c') hD hE⟩
  | atom d a z =>
    obtain ⟨D, E, hs⟩ := indices_finite_support (core c) (.atom d a z)
    exact ⟨D, E, fun c' hD hE => hs (core c') hD hE⟩
  | object A C =>
    obtain ⟨D, E, hs⟩ := indices_finite_support (core c) (.object A C)
    exact ⟨D, E, fun c' hD hE => hs (core c') hD hE⟩
  | invariant a =>
    obtain ⟨D, E, hs⟩ := indices_finite_support (core c) (.invariant a)
    exact ⟨D, E, fun c' hD hE => hs (core c') hD hE⟩
  | signatureAxis a =>
    obtain ⟨D, E, hs⟩ := indices_finite_support (core c) (.signatureAxis a)
    exact ⟨D, E, fun c' hD hE => hs (core c') hD hE⟩
  | coefficient a =>
    obtain ⟨D, E, hs⟩ := indices_finite_support (core c) (.coefficient a)
    exact ⟨D, E, fun c' hD hE => hs (core c') hD hE⟩
  | familyTransport F F' =>
    obtain ⟨D, E, hs⟩ := indices_finite_support (core c) (.familyTransport F F')
    exact ⟨D, E, fun c' hD hE => hs (core c') hD hE⟩
  | configurationTransport C C' =>
    obtain ⟨D, E, hs⟩ := indices_finite_support (core c) (.configurationTransport C C')
    exact ⟨D, E, fun c' hD hE => hs (core c') hD hE⟩
  | operation A B A' B' a =>
    obtain ⟨D, E, _, hs⟩ := operationRows_finite_support s t r (core c).p (core c).hp (core c).q
      (.edge (A, B) (A', B') a)
    refine ⟨D, E, ?_⟩
    intro c' hD hE
    exact hs (core c').p (core c').hp (core c').q hD hE
  | signatureCoordinate d I J i j a =>
    let z : IndependentInverseGraph.Query.{u, u} := match d with
      | .forward => .forward a
      | .backward => .backward (InverseRows.reverse a)
    obtain ⟨D, E, _, hs⟩ := signatureRows_finite_support s t r (core c).p (core c).hp (core c).q (core c).hq
      (.edge I J i j z)
    refine ⟨D, E, ?_⟩
    intro c' hD hE
    cases d with
    | forward => exact hs (core c').p (core c').hp (core c').q (core c').hq hD hE
    | backward => exact hs (core c').p (core c').hp (core c').q (core c').hq hD hE
  | atObjects A C z =>
    by_cases hA : A = (assemble s).core.object
    · subst A
      by_cases hC : C = (assemble r).core.object
      · subst C
        cases z with
        | equation d a =>
          obtain ⟨D, E, hs⟩ := equation_finite_support (core c) d a
          refine ⟨D, E, ?_⟩
          intro c' hD hE
          simpa [composeWith, dependentWith, NativeReader.liftDependent] using hs (core c') hD hE
        | context d W Z =>
          obtain ⟨D, E, hs⟩ := context_finite_support (core c) d W Z
          refine ⟨D, E, ?_⟩
          intro c' hD hE
          simpa [composeWith, dependentWith, NativeReader.liftDependent] using hs (core c') hD hE
        | observable d W Z a =>
          let z : IndependentInverseGraph.Query.{u, u} := match d with
            | .forward => .forward a
            | .backward => .backward (InverseRows.reverse a)
          obtain ⟨D, E, _, hs⟩ := observableRows_finite_support s t r (core c).p (core c).hp (core c).q (core c).hq
            (.edge W Z z)
          refine ⟨D, E, ?_⟩
          intro c' hD hE
          cases d with
          | forward =>
            simpa [composeWith, dependentWith, NativeReader.liftDependent,
              InverseRows.fromInverse] using hs (core c').p (core c').hp (core c').q (core c').hq hD hE
          | backward =>
            simpa [composeWith, dependentWith, NativeReader.liftDependent,
              InverseRows.fromInverse, InverseRows.reverse_reverse] using
              hs (core c').p (core c').hp (core c').q (core c').hq hD hE
        | raw a =>
          obtain ⟨D, E, hs⟩ := rawSupport a
          refine ⟨D, E, ?_⟩
          intro c' hD hE
          simpa [composeWith, dependentWith, NativeReader.liftDependent] using hs c' hD hE
        | realization a =>
          obtain ⟨D, E, hs⟩ := realizationSupport a
          refine ⟨D, E, ?_⟩
          intro c' hD hE
          simpa [composeWith, dependentWith, NativeReader.liftDependent] using hs c' hD hE
      · refine ⟨∅, ∅, ?_⟩
        intro c' _ _
        simp [composeWith, NativeReader.liftDependent, hC]
    · refine ⟨∅, ∅, ?_⟩
      intro c' _ _
      simp [composeWith, NativeReader.liftDependent, hA]

/-- Mode-specific data needed to evaluate one representative composition
table, over the shared lawful core candidate. -/
structure RepresentativeFiniteCandidate where
  /-- Shared package and coefficient data. -/
  core : FiniteCandidate (mode := .representative) s t r
  /-- Representative realization points of the first class. -/
  realizationPoints : GeometryComponents.RepresentativePoints s t core.p

/-- Every representative realization callback has finite support in the two
retained common declarations. -/
theorem representative_callback_finite_support
    (c : RepresentativeFiniteCandidate (s := s) (t := t) (r := r))
    (a : RealizationQuery (assemble s).core.object (assemble r).core.object .representative) :
    ∃ (D E : Finset (Query.{u, v} U .representative)),
      ∀ c' : RepresentativeFiniteCandidate (s := s) (t := t) (r := r),
        (∀ q ∈ D, (FiniteCandidate.left (s := s) (t := t) (r := r) c.core) q =
          (FiniteCandidate.left (s := s) (t := t) (r := r) c'.core) q) →
        (∀ q ∈ E, (FiniteCandidate.right (s := s) (t := t) (r := r) c.core) q =
          (FiniteCandidate.right (s := s) (t := t) (r := r) c'.core) q) →
        representativeRealizationRows s t r c.core.p c.core.hp c.core.q c.realizationPoints a =
          representativeRealizationRows s t r c'.core.p c'.core.hp c'.core.q
            c'.realizationPoints a := by
  obtain ⟨D, E, _, hs⟩ := RepresentativeRealization.composeRealization_finite_support
    s.1.val.2.1.val t.1.val.2.1.val
    (FiniteCandidate.left (s := s) (t := t) (r := r) c.core)
    c.realizationPoints c.core.hp.contextRows.forward
    (FiniteCandidate.right (s := s) (t := t) (r := r) c.core) a
  refine ⟨D, E, ?_⟩
  intro c' hD hE
  exact hs (FiniteCandidate.left (s := s) (t := t) (r := r) c'.core)
    c'.realizationPoints c'.core.hp.contextRows.forward
    (FiniteCandidate.right (s := s) (t := t) (r := r) c'.core) hD hE

/-- One output of the complete representative composition table is fixed by
two actual finite quotient fragments. -/
theorem composeRepresentative_finite_fragment
    (c : RepresentativeFiniteCandidate (s := s) (t := t) (r := r)) (a : Query.{u, v} U .representative) :
    ∃ (D E : Finset (Query.{u, v} U .representative)),
      ∀ c' : RepresentativeFiniteCandidate (s := s) (t := t) (r := r),
        InvariantWitness.fragment _ _ c.core.p D =
          InvariantWitness.fragment _ _ c'.core.p D →
        InvariantWitness.fragment _ _ c.core.q E =
          InvariantWitness.fragment _ _ c'.core.q E →
        composeRepresentative s t r c.core.p c.core.hp c.core.q c.core.hq
            c.realizationPoints c.core.cp a =
          composeRepresentative s t r c'.core.p c'.core.hp c'.core.q c'.core.hq
            c'.realizationPoints c'.core.cp a := by
  let raw : RepresentativeFiniteCandidate (s := s) (t := t) (r := r) →
      RawQuery (assemble s).core.object (assemble r).core.object .representative → Bool :=
    fun _ a => nomatch a
  let realization : RepresentativeFiniteCandidate (s := s) (t := t) (r := r) →
      RealizationQuery (assemble s).core.object (assemble r).core.object .representative → Bool :=
    fun c => representativeRealizationRows s t r c.core.p c.core.hp c.core.q c.realizationPoints
  have rawSupport : ∀ a, ∃ (D E : Finset (Query.{u, v} U .representative)),
      ∀ c' : RepresentativeFiniteCandidate (s := s) (t := t) (r := r),
        (∀ q ∈ D, (FiniteCandidate.left (s := s) (t := t) (r := r) c.core) q =
          (FiniteCandidate.left (s := s) (t := t) (r := r) c'.core) q) →
        (∀ q ∈ E, (FiniteCandidate.right (s := s) (t := t) (r := r) c.core) q =
          (FiniteCandidate.right (s := s) (t := t) (r := r) c'.core) q) →
        raw c a = raw c' a := by intro a; cases a
  obtain ⟨D, E, hs⟩ := composeWith_finite_support (fun c => c.core) c raw realization
    rawSupport (representative_callback_finite_support c) a
  refine ⟨D, E, ?_⟩
  intro c' hD hE
  exact hs c'
    ((InvariantWitness.fragment_eq_iff_points _ _ c.core.p c'.core.p D).1 hD)
    ((InvariantWitness.fragment_eq_iff_points _ _ c.core.q c'.core.q E).1 hE)

/-- Mode-specific raw and realization point laws needed to evaluate one
complete explicit composition table. -/
structure ExplicitFiniteCandidate where
  /-- Shared package and coefficient data. -/
  core : FiniteCandidate (mode := .explicit) s t r
  /-- Explicit raw points of the first class. -/
  rawLeft : GeometryComponents.ExplicitRawPoints s t core.p
  /-- Explicit raw points of the second class. -/
  rawRight : GeometryComponents.ExplicitRawPoints t r core.q
  /-- Explicit realization points of the first class. -/
  realizationLeft : GeometryComponents.ExplicitPoints s t core.p
  /-- Explicit realization points of the second class. -/
  realizationRight : GeometryComponents.ExplicitPoints t r core.q

/-- Every explicit raw callback has finite support, including dependent
local-data rows. -/
theorem explicit_raw_callback_finite_support
    (c : ExplicitFiniteCandidate (s := s) (t := t) (r := r))
    (a : RawQuery (assemble s).core.object (assemble r).core.object .explicit) :
    ∃ (D E : Finset (Query.{u, v} U .explicit)),
      ∀ c' : ExplicitFiniteCandidate (s := s) (t := t) (r := r),
        (∀ q ∈ D, (FiniteCandidate.left (s := s) (t := t) (r := r) c.core) q =
          (FiniteCandidate.left (s := s) (t := t) (r := r) c'.core) q) →
        (∀ q ∈ E, (FiniteCandidate.right (s := s) (t := t) (r := r) c.core) q =
          (FiniteCandidate.right (s := s) (t := t) (r := r) c'.core) q) →
        explicitRawRows s t r c.core.p c.core.q c.core.hq c.rawLeft c.rawRight a =
          explicitRawRows s t r c'.core.p c'.core.q c'.core.hq c'.rawLeft c'.rawRight a := by
  obtain ⟨D, E, hs⟩ := ExplicitRaw.composeRaw_finite_support
    s.2.2.2.val t.2.2.2.val r.2.2.2.val
    (FiniteCandidate.left (s := s) (t := t) (r := r) c.core) c.rawLeft
    (FiniteCandidate.right (s := s) (t := t) (r := r) c.core)
    c.core.hq.contextRows.backward c.rawRight a
  refine ⟨D, E, ?_⟩
  intro c' hD hE
  exact hs (FiniteCandidate.left (s := s) (t := t) (r := r) c'.core) c'.rawLeft
    (FiniteCandidate.right (s := s) (t := t) (r := r) c'.core)
    c'.core.hq.contextRows.backward c'.rawRight hD hE

/-- Every explicit realization callback, including actual actions, has finite
support in the two retained declarations. -/
theorem explicit_realization_callback_finite_support
    (c : ExplicitFiniteCandidate (s := s) (t := t) (r := r))
    (a : RealizationQuery (assemble s).core.object (assemble r).core.object .explicit) :
    ∃ (D E : Finset (Query.{u, v} U .explicit)),
      ∀ c' : ExplicitFiniteCandidate (s := s) (t := t) (r := r),
        (∀ q ∈ D, (FiniteCandidate.left (s := s) (t := t) (r := r) c.core) q =
          (FiniteCandidate.left (s := s) (t := t) (r := r) c'.core) q) →
        (∀ q ∈ E, (FiniteCandidate.right (s := s) (t := t) (r := r) c.core) q =
          (FiniteCandidate.right (s := s) (t := t) (r := r) c'.core) q) →
        explicitRealizationRows s t r c.core.p c.core.hp c.core.q
            c.realizationLeft c.realizationRight a =
          explicitRealizationRows s t r c'.core.p c'.core.hp c'.core.q
            c'.realizationLeft c'.realizationRight a := by
  obtain ⟨D, E, hs⟩ := ExplicitRealization.composeRealization_finite_support
    (FiniteCandidate.left (s := s) (t := t) (r := r) c.core) c.realizationLeft
    c.core.hp.contextRows.forward
    (FiniteCandidate.right (s := s) (t := t) (r := r) c.core) c.realizationRight a
  refine ⟨D, E, ?_⟩
  intro c' hD hE
  exact hs (FiniteCandidate.left (s := s) (t := t) (r := r) c'.core)
    c'.realizationLeft c'.core.hp.contextRows.forward
    (FiniteCandidate.right (s := s) (t := t) (r := r) c'.core)
    c'.realizationRight hD hE

/-- One output of the complete explicit composition table is fixed by two
actual finite quotient fragments. -/
theorem composeExplicit_finite_fragment
    (c : ExplicitFiniteCandidate (s := s) (t := t) (r := r)) (a : Query.{u, v} U .explicit) :
    ∃ (D E : Finset (Query.{u, v} U .explicit)),
      ∀ c' : ExplicitFiniteCandidate (s := s) (t := t) (r := r),
        InvariantWitness.fragment _ _ c.core.p D =
          InvariantWitness.fragment _ _ c'.core.p D →
        InvariantWitness.fragment _ _ c.core.q E =
          InvariantWitness.fragment _ _ c'.core.q E →
        composeExplicit s t r c.core.p c.core.hp c.core.q c.core.hq
            c.rawLeft c.rawRight c.realizationLeft c.realizationRight c.core.cp a =
          composeExplicit s t r c'.core.p c'.core.hp c'.core.q c'.core.hq
            c'.rawLeft c'.rawRight c'.realizationLeft c'.realizationRight c'.core.cp a := by
  let raw : ExplicitFiniteCandidate (s := s) (t := t) (r := r) →
      RawQuery (assemble s).core.object (assemble r).core.object .explicit → Bool :=
    fun c => explicitRawRows s t r c.core.p c.core.q c.core.hq c.rawLeft c.rawRight
  let realization : ExplicitFiniteCandidate (s := s) (t := t) (r := r) →
      RealizationQuery (assemble s).core.object (assemble r).core.object .explicit → Bool :=
    fun c => explicitRealizationRows s t r c.core.p c.core.hp c.core.q
      c.realizationLeft c.realizationRight
  obtain ⟨D, E, hs⟩ := composeWith_finite_support (fun c => c.core) c raw realization
    (explicit_raw_callback_finite_support c)
    (explicit_realization_callback_finite_support c) a
  refine ⟨D, E, ?_⟩
  intro c' hD hE
  exact hs c'
    ((InvariantWitness.fragment_eq_iff_points _ _ c.core.p c'.core.p D).1 hD)
    ((InvariantWitness.fragment_eq_iff_points _ _ c.core.q c'.core.q E).1 hE)

/-- Every finite family of outputs of the representative composition table is
fixed by two finite input quotient fragments. -/
theorem composeRepresentative_finite_fragment_set
    (c : RepresentativeFiniteCandidate (s := s) (t := t) (r := r))
    (S : Finset (Query.{u, v} U .representative)) :
    ∃ (D E : Finset (Query.{u, v} U .representative)),
      ∀ c' : RepresentativeFiniteCandidate (s := s) (t := t) (r := r),
        InvariantWitness.fragment _ _ c.core.p D =
          InvariantWitness.fragment _ _ c'.core.p D →
        InvariantWitness.fragment _ _ c.core.q E =
          InvariantWitness.fragment _ _ c'.core.q E →
        TagChange.LocalTagTable.read
            (composeRepresentative s t r c.core.p c.core.hp c.core.q c.core.hq
              c.realizationPoints c.core.cp) S =
          TagChange.LocalTagTable.read
            (composeRepresentative s t r c'.core.p c'.core.hp c'.core.q c'.core.hq
              c'.realizationPoints c'.core.cp) S := by
  classical
  choose leftSupport rightSupport hsupport using
    fun a => composeRepresentative_finite_fragment c a
  refine ⟨S.biUnion leftSupport, S.biUnion rightSupport, ?_⟩
  intro c' hD hE
  have hDpoints := (InvariantWitness.fragment_eq_iff_points _ _
    c.core.p c'.core.p (S.biUnion leftSupport)).1 hD
  have hEpoints := (InvariantWitness.fragment_eq_iff_points _ _
    c.core.q c'.core.q (S.biUnion rightSupport)).1 hE
  funext a
  change composeRepresentative s t r c.core.p c.core.hp c.core.q c.core.hq
      c.realizationPoints c.core.cp a.1 =
    composeRepresentative s t r c'.core.p c'.core.hp c'.core.q c'.core.hq
      c'.realizationPoints c'.core.cp a.1
  exact hsupport a.1 c'
    ((InvariantWitness.fragment_eq_iff_points _ _ c.core.p c'.core.p
      (leftSupport a.1)).2 (fun q hq =>
        hDpoints q (Finset.mem_biUnion.mpr ⟨a.1, a.2, hq⟩)))
    ((InvariantWitness.fragment_eq_iff_points _ _ c.core.q c'.core.q
      (rightSupport a.1)).2 (fun q hq =>
        hEpoints q (Finset.mem_biUnion.mpr ⟨a.1, a.2, hq⟩)))

/-- Every finite family of outputs of the explicit composition table is fixed
by two finite input quotient fragments. -/
theorem composeExplicit_finite_fragment_set
    (c : ExplicitFiniteCandidate (s := s) (t := t) (r := r))
    (S : Finset (Query.{u, v} U .explicit)) :
    ∃ (D E : Finset (Query.{u, v} U .explicit)),
      ∀ c' : ExplicitFiniteCandidate (s := s) (t := t) (r := r),
        InvariantWitness.fragment _ _ c.core.p D =
          InvariantWitness.fragment _ _ c'.core.p D →
        InvariantWitness.fragment _ _ c.core.q E =
          InvariantWitness.fragment _ _ c'.core.q E →
        TagChange.LocalTagTable.read
            (composeExplicit s t r c.core.p c.core.hp c.core.q c.core.hq
              c.rawLeft c.rawRight c.realizationLeft c.realizationRight c.core.cp) S =
          TagChange.LocalTagTable.read
            (composeExplicit s t r c'.core.p c'.core.hp c'.core.q c'.core.hq
              c'.rawLeft c'.rawRight c'.realizationLeft c'.realizationRight c'.core.cp) S := by
  classical
  choose leftSupport rightSupport hsupport using
    fun a => composeExplicit_finite_fragment c a
  refine ⟨S.biUnion leftSupport, S.biUnion rightSupport, ?_⟩
  intro c' hD hE
  have hDpoints := (InvariantWitness.fragment_eq_iff_points _ _
    c.core.p c'.core.p (S.biUnion leftSupport)).1 hD
  have hEpoints := (InvariantWitness.fragment_eq_iff_points _ _
    c.core.q c'.core.q (S.biUnion rightSupport)).1 hE
  funext a
  change composeExplicit s t r c.core.p c.core.hp c.core.q c.core.hq
      c.rawLeft c.rawRight c.realizationLeft c.realizationRight c.core.cp a.1 =
    composeExplicit s t r c'.core.p c'.core.hp c'.core.q c'.core.hq
      c'.rawLeft c'.rawRight c'.realizationLeft c'.realizationRight c'.core.cp a.1
  exact hsupport a.1 c'
    ((InvariantWitness.fragment_eq_iff_points _ _ c.core.p c'.core.p
      (leftSupport a.1)).2 (fun q hq =>
        hDpoints q (Finset.mem_biUnion.mpr ⟨a.1, a.2, hq⟩)))
    ((InvariantWitness.fragment_eq_iff_points _ _ c.core.q c'.core.q
      (rightSupport a.1)).2 (fun q hq =>
        hEpoints q (Finset.mem_biUnion.mpr ⟨a.1, a.2, hq⟩)))

/-- Complete representative point laws bundled for finite-fragment
composition of the actual local quotient classes. -/
structure RepresentativeLocalFiniteCandidate where
  /-- First complete representative local class. -/
  p : InvariantWitness.Local.{u, v}
    (assemble s).core.reading.invariantReading (assemble t).core.reading.invariantReading
      .representative
  /-- Complete point laws for the first class. -/
  hp : FullRepresentative.PointLaws s t p
  /-- Second complete representative local class. -/
  q : InvariantWitness.Local.{u, v}
    (assemble t).core.reading.invariantReading (assemble r).core.reading.invariantReading
      .representative
  /-- Complete point laws for the second class. -/
  hq : FullRepresentative.PointLaws t r q

/-- Forget the laws unused by evaluation of the representative composition
table while retaining the complete input local classes. -/
def RepresentativeLocalFiniteCandidate.finite
    (c : RepresentativeLocalFiniteCandidate (s := s) (t := t) (r := r)) :
    RepresentativeFiniteCandidate (s := s) (t := t) (r := r) where
  core := {
    p := c.p
    hp := c.hp.package
    q := c.q
    hq := c.hq.package
    cp := c.hp.coefficient }
  realizationPoints := c.hp.realization

/-- A finite fragment of the actual representative local composite is fixed
by two finite fragments of the actual input quotient classes. -/
theorem representativeLocal_finite_fragment_support
    (c : RepresentativeLocalFiniteCandidate (s := s) (t := t) (r := r))
    (S : Finset (Query.{u, v} U .representative)) :
    ∃ (D E : Finset (Query.{u, v} U .representative)),
      ∀ c' : RepresentativeLocalFiniteCandidate (s := s) (t := t) (r := r),
        InvariantWitness.fragment _ _ c.p D =
          InvariantWitness.fragment _ _ c'.p D →
        InvariantWitness.fragment _ _ c.q E =
          InvariantWitness.fragment _ _ c'.q E →
        InvariantWitness.fragment _ _
            (representativeLocal s t r c.p c.hp c.q c.hq) S =
          InvariantWitness.fragment _ _
            (representativeLocal s t r c'.p c'.hp c'.q c'.hq) S := by
  obtain ⟨D, E, hs⟩ := composeRepresentative_finite_fragment_set c.finite S
  refine ⟨D, E, ?_⟩
  intro c' hD hE
  exact (representativeLocal_fragment s t r c.p c.hp c.q c.hq S).trans
    ((hs c'.finite hD hE).trans
      (representativeLocal_fragment s t r c'.p c'.hp c'.q c'.hq S).symm)

/-- Complete explicit point laws bundled for finite-fragment composition of
the actual local quotient classes. -/
structure ExplicitLocalFiniteCandidate where
  /-- First complete explicit local class. -/
  p : InvariantWitness.Local.{u, v}
    (assemble s).core.reading.invariantReading (assemble t).core.reading.invariantReading
      .explicit
  /-- Complete point laws for the first class. -/
  hp : FullExplicit.PointLaws s t p
  /-- Second complete explicit local class. -/
  q : InvariantWitness.Local.{u, v}
    (assemble t).core.reading.invariantReading (assemble r).core.reading.invariantReading
      .explicit
  /-- Complete point laws for the second class. -/
  hq : FullExplicit.PointLaws t r q

/-- Forget the laws unused by evaluation of the explicit composition table
while retaining the complete input local classes. -/
def ExplicitLocalFiniteCandidate.finite
    (c : ExplicitLocalFiniteCandidate (s := s) (t := t) (r := r)) :
    ExplicitFiniteCandidate (s := s) (t := t) (r := r) where
  core := {
    p := c.p
    hp := c.hp.package
    q := c.q
    hq := c.hq.package
    cp := c.hp.coefficient }
  rawLeft := c.hp.raw
  rawRight := c.hq.raw
  realizationLeft := c.hp.realization
  realizationRight := c.hq.realization

/-- A finite fragment of the actual explicit local composite is fixed by two
finite fragments of the actual input quotient classes. -/
theorem explicitLocal_finite_fragment_support
    (c : ExplicitLocalFiniteCandidate (s := s) (t := t) (r := r))
    (S : Finset (Query.{u, v} U .explicit)) :
    ∃ (D E : Finset (Query.{u, v} U .explicit)),
      ∀ c' : ExplicitLocalFiniteCandidate (s := s) (t := t) (r := r),
        InvariantWitness.fragment _ _ c.p D =
          InvariantWitness.fragment _ _ c'.p D →
        InvariantWitness.fragment _ _ c.q E =
          InvariantWitness.fragment _ _ c'.q E →
        InvariantWitness.fragment _ _
            (explicitLocal s t r c.p c.hp c.q c.hq) S =
          InvariantWitness.fragment _ _
            (explicitLocal s t r c'.p c'.hp c'.q c'.hq) S := by
  obtain ⟨D, E, hs⟩ := composeExplicit_finite_fragment_set c.finite S
  refine ⟨D, E, ?_⟩
  intro c' hD hE
  exact (explicitLocal_fragment s t r c.p c.hp c.q c.hq S).trans
    ((hs c'.finite hD hE).trans
      (explicitLocal_fragment s t r c'.p c'.hp c'.q c'.hq S).symm)

end

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.Composition

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.Composition
