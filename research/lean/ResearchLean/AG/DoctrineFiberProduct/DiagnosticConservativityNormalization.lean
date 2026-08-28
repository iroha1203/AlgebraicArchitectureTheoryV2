import ResearchLean.AG.DoctrineFiberProduct.DiagnosticConservativitySchema

/-!
# Normalization for the diagnostic-conservativity condition language

This module discharges the G-113 K0 completeness obligation for the closed
two-atom conjunction language.  The normalizer records which of the two atoms
occur; conjunction is therefore associative, commutative, and idempotent at
the evaluation level without adding equations or callbacks to the syntax.

## Implementation notes

The three normal forms are represented by a separate closed inductive type.
Quotienting `DiagnosticClassTerm` was rejected because downstream class heads
must remain the card-fixed terms, while a Boolean decision procedure was
rejected because the fixed evaluator is proposition-valued.
-/

namespace AAT.AG.DoctrineFiberProduct

open CategoryTheory
open AtomFoundation

universe u

/-- The three nonempty ACI normal forms of the two-atom condition language. -/
inductive DiagnosticClassNormalForm
  | vertexwiseSourceMapInjective
  | injectiveAndPullback
  | edgewiseSquarePullback
  deriving DecidableEq

namespace DiagnosticClassNormalForm

/-- Re-embed a normal form as the corresponding card-fixed condition term. -/
def toTerm : DiagnosticClassNormalForm → DiagnosticClassTerm
  | .vertexwiseSourceMapInjective => .vertexwiseSourceMapInjective
  | .injectiveAndPullback =>
      .conjunction .vertexwiseSourceMapInjective .edgewiseSquarePullback
  | .edgewiseSquarePullback => .edgewiseSquarePullback

/-- ACI union of the atoms occurring in two normal forms. -/
def merge : DiagnosticClassNormalForm → DiagnosticClassNormalForm →
    DiagnosticClassNormalForm
  | .vertexwiseSourceMapInjective, .vertexwiseSourceMapInjective =>
      .vertexwiseSourceMapInjective
  | .edgewiseSquarePullback, .edgewiseSquarePullback =>
      .edgewiseSquarePullback
  | _, _ => .injectiveAndPullback

/-- Merging normal forms preserves exactly conjunction of their evaluations. -/
theorem eval_merge_iff (left right : DiagnosticClassNormalForm)
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E) :
    (merge left right).toTerm.eval hom ↔
      left.toTerm.eval hom ∧ right.toTerm.eval hom := by
  cases left <;> cases right <;>
    simp [merge, toTerm, DiagnosticClassTerm.eval_conjunction_iff,
      and_comm, and_left_comm]

end DiagnosticClassNormalForm

namespace DiagnosticClassTerm

/-- Compute the ACI normal form of an arbitrary closed condition term. -/
def normalizeForm : DiagnosticClassTerm → DiagnosticClassNormalForm
  | .vertexwiseSourceMapInjective =>
      .vertexwiseSourceMapInjective
  | .edgewiseSquarePullback =>
      .edgewiseSquarePullback
  | .conjunction left right =>
      DiagnosticClassNormalForm.merge left.normalizeForm right.normalizeForm

/-- Normalize into one of the three card-fixed condition terms. -/
def normalize (term : DiagnosticClassTerm) : DiagnosticClassTerm :=
  term.normalizeForm.toTerm

/-- Normalization preserves the evaluator for every diagram hom. -/
theorem eval_normalize_iff (term : DiagnosticClassTerm)
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E) :
    term.eval hom ↔ term.normalize.eval hom := by
  induction term with
  | vertexwiseSourceMapInjective => rfl
  | edgewiseSquarePullback => rfl
  | conjunction left right left_ih right_ih =>
      rw [eval_conjunction_iff, left_ih, right_ih]
      exact (DiagnosticClassNormalForm.eval_merge_iff
        left.normalizeForm right.normalizeForm hom).symm

/-- Every normalized term is exactly one of the three fixed registry entries. -/
theorem normalize_eq_one_of_fixed_terms (term : DiagnosticClassTerm) :
    term.normalize = .vertexwiseSourceMapInjective ∨
      term.normalize =
        .conjunction .vertexwiseSourceMapInjective .edgewiseSquarePullback ∨
      term.normalize = .edgewiseSquarePullback := by
  unfold normalize
  cases term.normalizeForm <;> simp [DiagnosticClassNormalForm.toTerm]

/-- Normalization lands in the card-fixed ordered registry. -/
theorem normalize_mem_candidates (term : DiagnosticClassTerm) :
    term.normalize ∈ diagnosticClassTermCandidates := by
  rw [mem_diagnosticClassTermCandidates_iff]
  exact normalize_eq_one_of_fixed_terms term

/-- Every condition term is extensionally represented by a registered term. -/
theorem exists_candidate_eval_iff (term : DiagnosticClassTerm)
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E) :
    ∃ candidate ∈ diagnosticClassTermCandidates,
      (term.eval hom ↔ candidate.eval hom) := by
  exact ⟨term.normalize, normalize_mem_candidates term,
    eval_normalize_iff term hom⟩

end DiagnosticClassTerm

/-! ## Categorical mono versus source-table injectivity -/

/-- Source-table injectivity makes an `ExtInst_U` arrow categorical monic. -/
theorem extInstHom_mono_of_sourceMap_injective
    {U : AtomCarrier.{u}} {X Y : ExtractionInstance U}
    (hom : X ⟶ Y) (injective : Function.Injective hom.doctrineHom.sourceMap) :
    Mono hom := by
  constructor
  intro Z first second equality
  apply ExtInstHom.ext
  apply ExactDoctrineHom.ext
  · funext source
    apply injective
    exact congrArg (fun arrow => arrow.doctrineHom.sourceMap source) equality
  · apply Equiv.ext
    intro atom
    apply hom.doctrineHom.atomEquiv.injective
    exact congrArg (fun arrow => arrow.doctrineHom.atomEquiv atom) equality

/-- The two tracks used to probe arbitrary source-table entries categorically. -/
inductive ExtInstMonoProbeTrack
  | selected
  | disputed
  deriving DecidableEq

/-- Iterated normalization in an extraction doctrine. -/
def iterateDoctrineNormalize {U : AtomCarrier.{u}} (D : ExtractionDoctrine U) :
    Nat → D.Source → D.Source
  | 0, source => source
  | n + 1, source => D.normalize (iterateDoctrineNormalize D n source)

/-- Exact doctrine morphisms commute with every finite normalization iterate. -/
theorem exactDoctrineHom_map_iterateNormalize
    {U : AtomCarrier.{u}} {D E : ExtractionDoctrine U}
    (hom : ExactDoctrineHom D E) (n : Nat) (source : D.Source) :
    hom.sourceMap (iterateDoctrineNormalize D n source) =
      iterateDoctrineNormalize E n (hom.sourceMap source) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change hom.sourceMap
          (D.normalize (iterateDoctrineNormalize D n source)) = _
      rw [← hom.normalize_eq, ih]
      rfl

/-- Equality after an exact map persists through all normalization iterates. -/
theorem exactDoctrineHom_map_iterateNormalize_eq
    {U : AtomCarrier.{u}} {D E : ExtractionDoctrine U}
    (hom : ExactDoctrineHom D E) {first second : D.Source}
    (equality : hom.sourceMap first = hom.sourceMap second) (n : Nat) :
    hom.sourceMap (iterateDoctrineNormalize D n first) =
      hom.sourceMap (iterateDoctrineNormalize D n second) := by
  rw [exactDoctrineHom_map_iterateNormalize,
    exactDoctrineHom_map_iterateNormalize, equality]

/-- Source table of the first categorical probe. -/
def extInstMonoProbeFirstMap {U : AtomCarrier.{u}}
    (X : ExtractionInstance U) (first : X.doctrine.Source) :
    ULift.{u} (ExtInstMonoProbeTrack × Nat) → X.doctrine.Source
  | ⟨(.selected, n)⟩ => iterateDoctrineNormalize X.doctrine n X.source
  | ⟨(.disputed, n)⟩ => iterateDoctrineNormalize X.doctrine n first

/-- Source table of the second categorical probe. -/
def extInstMonoProbeSecondMap {U : AtomCarrier.{u}}
    (X : ExtractionInstance U) (second : X.doctrine.Source) :
    ULift.{u} (ExtInstMonoProbeTrack × Nat) → X.doctrine.Source
  | ⟨(.selected, n)⟩ => iterateDoctrineNormalize X.doctrine n X.source
  | ⟨(.disputed, n)⟩ => iterateDoctrineNormalize X.doctrine n second

/--
The free two-track probe doctrine exposes every source entry while retaining
the selected point.  Successor normalization leaves room for the source
semantics to record the extraction profile before normalization.
-/
def extInstMonoProbeDoctrine {U : AtomCarrier.{u}}
    (X : ExtractionInstance U) (first : X.doctrine.Source) :
    ExtractionDoctrine U where
  Source := ULift.{u} (ExtInstMonoProbeTrack × Nat)
  Vocabulary := ULift.{u} PUnit
  SemanticReading := ULift.{u} PUnit
  Resolution := ULift.{u} PUnit
  vocabulary := ⟨PUnit.unit⟩
  semanticReading := ⟨PUnit.unit⟩
  resolution := ⟨PUnit.unit⟩
  vocabularyAllows := fun _ _ => True
  semanticAllows := fun _ _ _ => True
  resolutionAllows := fun _ _ _ => True
  sourceSemantics := fun source atom =>
    match source.down.2 with
    | 0 => True
    | n + 1 => X.doctrine.extracts
        (extInstMonoProbeFirstMap X first ⟨(source.down.1, n)⟩) atom
  normalize := fun source => ⟨(source.down.1, source.down.2 + 1)⟩

/-- The first probe is exact by construction. -/
def extInstMonoProbeFirstDoctrineHom {U : AtomCarrier.{u}}
    (X : ExtractionInstance U) (first : X.doctrine.Source) :
    ExactDoctrineHom (extInstMonoProbeDoctrine X first) X.doctrine where
  sourceMap := extInstMonoProbeFirstMap X first
  atomEquiv := Equiv.refl U.Atom
  normalize_eq := by
    rintro ⟨⟨track, n⟩⟩
    cases track <;> rfl
  extraction_iff := by
    rintro ⟨⟨track, n⟩⟩ atom
    simp [ExtractionDoctrine.extracts, extInstMonoProbeDoctrine,
      extInstMonoProbeFirstMap]

/-- The second probe is exact whenever the tested entries agree after `hom`. -/
def extInstMonoProbeSecondDoctrineHom
    {U : AtomCarrier.{u}} {X Y : ExtractionInstance U}
    (hom : X ⟶ Y) (first second : X.doctrine.Source)
    (equality : hom.doctrineHom.sourceMap first =
      hom.doctrineHom.sourceMap second) :
    ExactDoctrineHom (extInstMonoProbeDoctrine X first) X.doctrine where
  sourceMap := extInstMonoProbeSecondMap X second
  atomEquiv := Equiv.refl U.Atom
  normalize_eq := by
    rintro ⟨⟨track, n⟩⟩
    cases track <;> rfl
  extraction_iff := by
    rintro ⟨⟨track, n⟩⟩ atom
    cases track with
    | selected =>
        simp [ExtractionDoctrine.extracts, extInstMonoProbeDoctrine,
          extInstMonoProbeFirstMap, extInstMonoProbeSecondMap]
    | disputed =>
        simp only [ExtractionDoctrine.extracts, extInstMonoProbeDoctrine,
          extInstMonoProbeFirstMap, extInstMonoProbeSecondMap, true_and]
        constructor
        · intro hfirst
          apply (hom.doctrineHom.extraction_iff _ atom).mpr
          rw [← exactDoctrineHom_map_iterateNormalize_eq
            hom.doctrineHom equality n]
          exact (hom.doctrineHom.extraction_iff _ atom).mp hfirst
        · intro hsecond
          apply (hom.doctrineHom.extraction_iff _ atom).mpr
          rw [exactDoctrineHom_map_iterateNormalize_eq
            hom.doctrineHom equality n]
          exact (hom.doctrineHom.extraction_iff _ atom).mp hsecond

/-- Pointed source object for the two categorical probes. -/
def extInstMonoProbeInstance {U : AtomCarrier.{u}}
    (X : ExtractionInstance U) (first : X.doctrine.Source) :
    ExtractionInstance U where
  doctrine := extInstMonoProbeDoctrine X first
  source := ⟨(ExtInstMonoProbeTrack.selected, 0)⟩

/-- First pointed probe into `X`. -/
def extInstMonoProbeFirstHom {U : AtomCarrier.{u}}
    (X : ExtractionInstance U) (first : X.doctrine.Source) :
    extInstMonoProbeInstance X first ⟶ X where
  doctrineHom := extInstMonoProbeFirstDoctrineHom X first
  source_eq := rfl

/-- Second pointed probe into `X`. -/
def extInstMonoProbeSecondHom
    {U : AtomCarrier.{u}} {X Y : ExtractionInstance U}
    (hom : X ⟶ Y) (first second : X.doctrine.Source)
    (equality : hom.doctrineHom.sourceMap first =
      hom.doctrineHom.sourceMap second) :
    extInstMonoProbeInstance X first ⟶ X where
  doctrineHom :=
    extInstMonoProbeSecondDoctrineHom hom first second equality
  source_eq := rfl

/-- A categorical mono in `ExtInst_U` has an injective source table. -/
theorem extInstHom_sourceMap_injective_of_mono
    {U : AtomCarrier.{u}} {X Y : ExtractionInstance U}
    (hom : X ⟶ Y) [Mono hom] :
    Function.Injective hom.doctrineHom.sourceMap := by
  intro first second equality
  let firstProbe := extInstMonoProbeFirstHom X first
  let secondProbe := extInstMonoProbeSecondHom hom first second equality
  have compositeEquality : firstProbe ≫ hom = secondProbe ≫ hom := by
    apply ExtInstHom.ext
    apply ExactDoctrineHom.ext
    · funext source
      rcases source with ⟨⟨track, n⟩⟩
      cases track with
      | selected => rfl
      | disputed =>
          exact exactDoctrineHom_map_iterateNormalize_eq
            hom.doctrineHom equality n
    · apply Equiv.ext
      intro atom
      change hom.doctrineHom.atomEquiv atom =
        hom.doctrineHom.atomEquiv atom
      rfl
  have probeEquality : firstProbe = secondProbe :=
    (cancel_mono hom).mp compositeEquality
  have sourceMapEquality := congrArg
    (fun arrow => arrow.doctrineHom.sourceMap
      ⟨(ExtInstMonoProbeTrack.disputed, 0)⟩) probeEquality
  exact sourceMapEquality

/-- In `ExtInst_U`, categorical monicity is exactly source-table injectivity. -/
theorem extInstHom_mono_iff_sourceMap_injective
    {U : AtomCarrier.{u}} {X Y : ExtractionInstance U} (hom : X ⟶ Y) :
    Mono hom ↔ Function.Injective hom.doctrineHom.sourceMap := by
  constructor
  · intro mono
    letI : Mono hom := mono
    exact extInstHom_sourceMap_injective_of_mono hom
  · exact extInstHom_mono_of_sourceMap_injective hom

/-! ## Qualification: invariance under diagram-hom isomorphism -/

/-- Reverse a diagram-hom isomorphism witness without weakening naturality. -/
def IndexedBaseDiagramHomIsoWitness.symm
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E D' E' : IndexedBaseDiagram G U}
    {first : IndexedBaseDiagramHom D E}
    {second : IndexedBaseDiagramHom D' E'}
    (witness : IndexedBaseDiagramHomIsoWitness first second) :
    IndexedBaseDiagramHomIsoWitness second first where
  sourceIso := witness.sourceIso.symm
  targetIso := witness.targetIso.symm
  forward_commutes := witness.backward_commutes
  backward_commutes := witness.forward_commutes

/-- Evaluate an indexed-diagram isomorphism at one vertex. -/
def indexedBaseDiagramIsoApp
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (iso : IndexedBaseDiagramIso D E)
    (vertex : G.Vertex) : D.vertex vertex ≅ E.vertex vertex where
  hom := iso.hom.app vertex
  inv := iso.inv.app vertex
  hom_inv_id := by
    have equality := congrArg
      (fun hom : D ⟶ D => hom.app vertex) iso.hom_inv_id
    simpa only [IndexedBaseDiagramHom.comp_app,
      IndexedBaseDiagramHom.id_app] using equality
  inv_hom_id := by
    have equality := congrArg
      (fun hom : E ⟶ E => hom.app vertex) iso.inv_hom_id
    simpa only [IndexedBaseDiagramHom.comp_app,
      IndexedBaseDiagramHom.id_app] using equality

/-- Vertexwise source-table injectivity is preserved by a diagram-hom iso. -/
theorem vertexwiseSourceMapInjective_of_isoWitness
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E D' E' : IndexedBaseDiagram G U}
    {first : IndexedBaseDiagramHom D E}
    {second : IndexedBaseDiagramHom D' E'}
    (witness : IndexedBaseDiagramHomIsoWitness first second)
    (injective : DiagnosticClassTerm.eval
      .vertexwiseSourceMapInjective first) :
    DiagnosticClassTerm.eval .vertexwiseSourceMapInjective second := by
  intro vertex left right equality
  have mapped :
      (first.app vertex).doctrineHom.sourceMap
          ((witness.sourceIso.inv.app vertex).doctrineHom.sourceMap left) =
        (first.app vertex).doctrineHom.sourceMap
          ((witness.sourceIso.inv.app vertex).doctrineHom.sourceMap right) := by
    calc
      _ = (witness.targetIso.inv.app vertex).doctrineHom.sourceMap
            ((second.app vertex).doctrineHom.sourceMap left) := by
          exact congrArg (fun arrow => arrow.doctrineHom.sourceMap left)
            (witness.backward_commutes vertex).symm
      _ = (witness.targetIso.inv.app vertex).doctrineHom.sourceMap
            ((second.app vertex).doctrineHom.sourceMap right) :=
          congrArg _ equality
      _ = _ := by
          exact congrArg (fun arrow => arrow.doctrineHom.sourceMap right)
            (witness.backward_commutes vertex)
  have sourceInvEquality := injective vertex mapped
  exact extInstHom_sourceMap_injective_of_mono
    (indexedBaseDiagramIsoApp witness.sourceIso vertex).inv sourceInvEquality

/-- Edge-square pullback is preserved by the full diagram-isomorphism witness. -/
theorem edgewiseSquarePullback_of_isoWitness
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E D' E' : IndexedBaseDiagram G U}
    {first : IndexedBaseDiagramHom D E}
    {second : IndexedBaseDiagramHom D' E'}
    (witness : IndexedBaseDiagramHomIsoWitness first second)
    (pullback : DiagnosticClassTerm.eval .edgewiseSquarePullback first) :
    DiagnosticClassTerm.eval .edgewiseSquarePullback second := by
  intro i j edge
  exact (pullback edge).of_iso
    (indexedBaseDiagramIsoApp witness.sourceIso i)
    (indexedBaseDiagramIsoApp witness.targetIso i)
    (indexedBaseDiagramIsoApp witness.sourceIso j)
    (indexedBaseDiagramIsoApp witness.targetIso j)
    (witness.forward_commutes i)
    (witness.sourceIso.hom.naturality edge).symm
    (witness.targetIso.hom.naturality edge).symm
    (witness.forward_commutes j)

/-- Every closed condition term is preserved by a diagram-hom iso witness. -/
theorem DiagnosticClassTerm.eval_of_isoWitness
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E D' E' : IndexedBaseDiagram G U}
    {first : IndexedBaseDiagramHom D E}
    {second : IndexedBaseDiagramHom D' E'}
    (term : DiagnosticClassTerm)
    (witness : IndexedBaseDiagramHomIsoWitness first second)
    (evaluation : term.eval first) : term.eval second := by
  induction term with
  | vertexwiseSourceMapInjective =>
      exact vertexwiseSourceMapInjective_of_isoWitness witness evaluation
  | edgewiseSquarePullback =>
      exact edgewiseSquarePullback_of_isoWitness witness evaluation
  | conjunction left right left_ih right_ih =>
      exact ⟨left_ih evaluation.1, right_ih evaluation.2⟩

/-- Evaluation of every closed term is invariant under diagram-hom isomorphism. -/
theorem DiagnosticClassTerm.eval_iff_of_isoWitness
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E D' E' : IndexedBaseDiagram G U}
    {first : IndexedBaseDiagramHom D E}
    {second : IndexedBaseDiagramHom D' E'}
    (term : DiagnosticClassTerm)
    (witness : IndexedBaseDiagramHomIsoWitness first second) :
    term.eval first ↔ term.eval second :=
  ⟨term.eval_of_isoWitness witness,
    term.eval_of_isoWitness witness.symm⟩

/-- Generated-class membership is invariant under the fixed diagram-iso reading. -/
theorem generatedDiagnosticClass_iff_of_isoWitness
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E D' E' : IndexedBaseDiagram G U}
    {first : IndexedBaseDiagramHom D E}
    {second : IndexedBaseDiagramHom D' E'}
    (term : DiagnosticClassTerm)
    (witness : IndexedBaseDiagramHomIsoWitness first second) :
    GeneratedDiagnosticClass term first ↔
      GeneratedDiagnosticClass term second :=
  term.eval_iff_of_isoWitness witness

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
