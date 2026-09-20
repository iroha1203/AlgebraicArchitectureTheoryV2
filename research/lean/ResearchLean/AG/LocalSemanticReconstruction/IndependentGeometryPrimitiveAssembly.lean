import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryPrimitiveDeclaration
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryTableAssembly
import Formal.Util.AssertStandardAxioms

/-!
# Assembly from the common complete-geometry primitive declaration

The common query and value types are fixed before the table is chosen. The
conditions below check its primitive field projections. Candidate object rows
are activated by the independently derived matching flags. Native stages are
constructed only after these conditions have been checked.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryPrimitive

noncomputable section

universe u v

open Site IndependentCorePrimitive

variable {U : AtomCarrier.{u}}

/-- The original primitive foundation and coefficient conditions, without completed native fields. -/
structure FoundationLaws (t : Table.{u, v} U) : Prop where
  /-- Exact candidate-carrier activation for extraction points. -/
  extraction : Extraction.IsTyped (IndependentGeometryPrimitive.extraction t)
  /-- The original finite extracted-family requirement. -/
  finite : (Generation.family (IndependentGeometryPrimitive.extraction t) extraction).ListFinite
  /-- The native pointwise composition conditions. -/
  composition : Composition.IsLawful (IndependentGeometryPrimitive.composition t)
  /-- Invariant response tags and carrier activation. -/
  invariant : IndependentInvariantSignaturePrimitive.Invariants.IsTyped (IndependentGeometryPrimitive.invariant t)
  /-- Signature carrier activation. -/
  signature : IndependentInvariantSignaturePrimitive.Signature.IsTyped (IndependentGeometryPrimitive.signature t)
  /-- Operation response typing and the native point laws. -/
  operation : ∃ ht : Operations.IsTyped (IndependentGeometryPrimitive.operation t),
    Operations.IsLawful (IndependentGeometryPrimitive.operation t) ht
  /-- The original two Atom laws on the fixed input carrier. -/
  atom : IndependentCoreTableAssembly.AtomLaws U
  /-- Coefficient carrier activation and primitive ring equations. -/
  coefficient : ∃ ht : IndependentRingPrimitive.Carrier.IsTyped (IndependentGeometryPrimitive.coefficient t),
    IndependentRingPrimitive.Carrier.IsLawful (IndependentGeometryPrimitive.coefficient t) ht

/-- Collect foundation stages directly from the common table's primitive cells. -/
def foundation (t : Table.{u, v} U) (h : FoundationLaws t) : IndependentCoreTableAssembly.FoundationData U :=
  ⟨⟨⟨extraction t, h.extraction⟩, h.finite⟩, ⟨composition t, h.composition⟩, formation t,
    ⟨invariant t, h.invariant⟩, ⟨signature t, h.signature⟩, ⟨operation t, h.operation⟩⟩

/-- The generated reference is an output of the primitive extraction/composition/formation stages. -/
def generated (t : Table.{u, v} U) (h : FoundationLaws t) : ArchitectureObject U :=
  IndependentCoreTableAssembly.generatedObject (foundation t h)

/-- The coefficient stage contains exactly the common table's primitive ring rows. -/
def coefficientData (t : Table.{u, v} U) (h : FoundationLaws t) :
    IndependentGeometryTableAssembly.CoefficientData.{v} := ⟨coefficient t, h.coefficient⟩

/-- Context conditions are propositions on the primitive context cells. -/
abbrev ContextLaws {A : ArchitectureObject U} (d : DependentTable.{u, v} A) :=
  ∃ ht : IndependentContextPrimitive.IsTyped (contextTable d),
    IndependentContextPrimitive.IsLawful (contextTable d) ht

/-- Collect the context stage from primitive rows and their point laws. -/
def contextData {A : ArchitectureObject U} (d : DependentTable.{u, v} A) (h : ContextLaws d) :
    IndependentCoreTableAssembly.ContextData A := ⟨contextTable d, h⟩

/-- Equation conditions are checked after constructing the primitive context preorder. -/
abbrev EquationLaws {A : ArchitectureObject U} (d : DependentTable.{u, v} A) (hc : ContextLaws d) :=
  ∃ ht : IndependentEquationPrimitive.IsTyped (IndependentCoreTableAssembly.context (contextData d hc))
    (equationTable d), IndependentEquationPrimitive.IsLawful (equationTable d) ht

/-- Collect the equation stage from its ring-operation and coordinate rows. -/
def equationData {A : ArchitectureObject U} (d : DependentTable.{u, v} A) (hc : ContextLaws d)
    (he : EquationLaws d hc) :
    IndependentCoreTableAssembly.EquationData (IndependentCoreTableAssembly.context (contextData d hc)) :=
  ⟨equationTable d, he⟩

/-- The signature is constructed from its primitive common rows. -/
def assembledSignature (t : Table.{u, v} U) (h : FoundationLaws t) : ArchitectureSignature U :=
  IndependentInvariantSignaturePrimitive.Signature.assemble (signature t) h.signature

/-- Coverage laws refer only to the selected equation and signature roles. -/
abbrev CoverageLaws (t : Table.{u, v} U) (h : FoundationLaws t) {A : ArchitectureObject U}
    (d : DependentTable.{u, v} A) (hc : ContextLaws d) (he : EquationLaws d hc) :=
  IndependentCoveragePrimitive.IsTyped (IndependentCoreTableAssembly.equation (equationData d hc he))
    (assembledSignature t h) (coverageTable d)

/-- Overlap conditions retain primitive context fields and the four native order requirements. -/
abbrev OverlapLaws {A : ArchitectureObject U} (d : DependentTable.{u, v} A) (hc : ContextLaws d) :=
  IndependentOverlapCandidate.IsTyped (overlapTable d) ∧
    IndependentOverlapCandidate.IsLawful
      (IndependentCoreTableAssembly.context (contextData d hc)) (overlapTable d)

/-- Construct the site from primitive context/equation/signature/coverage/overlap rows. -/
def assembledSite (t : Table.{u, v} U) (h : FoundationLaws t) {A : ArchitectureObject U}
    (d : DependentTable.{u, v} A) (hc : ContextLaws d) (he : EquationLaws d hc)
    (_hv : CoverageLaws t h d hc he) (ho : OverlapLaws d hc) : AATSite A where
  contextPreorder := IndependentCoreTableAssembly.context (contextData d hc)
  equationSystem := IndependentCoreTableAssembly.equation (equationData d hc he)
  signature := assembledSignature t h
  requirements := IndependentCoveragePrimitive.assemble _ _ (coverageTable d)
  overlap := IndependentOverlapCandidate.assemble _ (overlapTable d) ho.1 ho.2

/-- All dependent field conditions, on primitive point rows at one active candidate reference. -/
structure DependentLaws (t : Table.{u, v} U) (h : FoundationLaws t)
    {A : ArchitectureObject U} (d : DependentTable.{u, v} A) : Prop where
  /-- Context carrier activation and pointwise preorder/restriction equations. -/
  context : ContextLaws d
  /-- Equation carrier activation and primitive ring/restriction equations. -/
  equation : EquationLaws d context
  /-- Finite circuit syntax has exactly its original local nonzero witnesses. -/
  circuit : ∃ ht : IndependentEquationPrimitive.Circuit.IsTyped
      (IndependentEquationPrimitive.index (equationTable d)) (IndependentGeometryPrimitive.circuit t),
    IndependentEquationPrimitive.Circuit.IsLawful (equationTable d) equation.choose
      (IndependentGeometryPrimitive.circuit t) ht
  /-- Exact coverage-role activation. -/
  coverage : CoverageLaws t h d context equation
  /-- The four overlap comparisons and their primitive context support laws. -/
  overlap : OverlapLaws d context
  /-- Raw carrier activation and independent polynomial identity/composition conditions. -/
  raw : let r := IndependentGeometryTableAssembly.coefficient (coefficientData t h)
    letI := r.2
    ∃ ht : IndependentRawCandidate.IsTyped (assembledSite t h d context equation coverage overlap)
        r.1 (rawTable d),
      IndependentRawCandidate.IsLawful (assembledSite t h d context equation coverage overlap)
        r.1 (rawTable d) ht

/-- Lawfulness of the common table is specified without a completed object or an extension witness. -/
structure IsLawful (t : Table.{u, v} U) : Prop where
  /-- All foundation and coefficient primitive conditions. -/
  foundation : FoundationLaws t
  /-- Pointwise matching and finite point refutations determine the candidate-reference flags. -/
  matching : IndependentGeneratedObjectMatching.IsLawful (extraction t) foundation.extraction
    (composition t) (formation t) (IndependentGeometryPrimitive.matching t)
  /-- Object-indexed primitive response presence agrees exactly with the matching flag. -/
  active : IsActiveTyped t
  /-- Each active candidate's rows satisfy the native dependent point conditions. -/
  dependent : ∀ A (ha : IndependentGeometryPrimitive.matching t (.object A) = true),
    DependentLaws t foundation (IndependentGeometryPrimitive.dependent t active A ha)

/-- Every lawful table activates its own primitively generated architecture reference. -/
theorem generated_active (t : Table.{u, v} U) (h : IsLawful t) :
    matching t (.object (generated t h.foundation)) = true :=
  IndependentGeneratedObjectMatching.generated_object_active (extraction t) h.foundation.extraction
    (composition t) (formation t) h.foundation.composition h.foundation.finite (matching t) h.matching

/-- A lawful active reference is exactly the one generated from the primitive foundation. -/
theorem active_iff_generated (t : Table.{u, v} U) (h : IsLawful t) (A : ArchitectureObject U) :
    matching t (.object A) = true ↔ A = generated t h.foundation :=
  IndependentGeneratedObjectMatching.object_iff (extraction t) h.foundation.extraction
    (composition t) (formation t) h.foundation.composition h.foundation.finite (matching t) h.matching A

/-- The active primitive row family used by native stage assembly. -/
def selected (t : Table.{u, v} U) (h : IsLawful t) : DependentTable.{u, v} (generated t h.foundation) :=
  dependent t h.active (generated t h.foundation) (generated_active t h)

/-- The selected row family inherits every dependent local condition. -/
theorem selected_lawful (t : Table.{u, v} U) (h : IsLawful t) :
    DependentLaws t h.foundation (selected t h) := h.dependent _ (generated_active t h)

/-- Collect stages from one generated-reference row family and its independent local conditions. -/
def stagesFrom (t : Table.{u, v} U) (h : FoundationLaws t)
    (d : DependentTable.{u, v} (generated t h)) (hd : DependentLaws t h d) :
    IndependentGeometryTableAssembly.ObjectData.{u, v} U :=
  ⟨⟨⟨foundation t h, contextData d hd.context,
      equationData d hd.context hd.equation, ⟨circuit t, hd.circuit⟩⟩, h.atom⟩,
    ⟨⟨coverageTable d, hd.coverage⟩, ⟨overlapTable d, hd.overlap⟩⟩,
    coefficientData t h, ⟨rawTable d, hd.raw⟩⟩

/-- Construct all native primitive stages directly from the lawful common table. -/
def stages (t : Table.{u, v} U) (h : IsLawful t) :
    IndependentGeometryTableAssembly.ObjectData.{u, v} U :=
  stagesFrom t h.foundation (selected t h) (selected_lawful t h)

/-- Assemble all native complete-geometry fields, including raw, from the common primitive table. -/
def assemble (t : Table.{u, v} U) (h : IsLawful t) : ReadingCore.{u, v} U :=
  IndependentGeometryTableAssembly.assemble (stages t h)


/-- Read a single dependent primitive row from the established stage presentation. -/
def flattenDependent (d : IndependentGeometryTableAssembly.ObjectData.{u, v} U) :
    DependentTable.{u, v} (IndependentCoreTableAssembly.generatedObject d.1.val.1)
  | .context q => ⟨d.1.val.2.1.val q⟩
  | .equation q => ⟨d.1.val.2.2.1.val q⟩
  | .overlap q => ⟨d.2.1.2.val q⟩
  | .coverage q => ⟨d.2.1.1.val q⟩
  | .raw q => d.2.2.2.val q

/-- Flatten primitive stages onto the single declaration; inactive candidate rows are absent. -/
def flatten (d : IndependentGeometryTableAssembly.ObjectData.{u, v} U) : Table.{u, v} U := by
  classical
  intro q
  let f := d.1.val.1
  cases q with
  | extraction q => exact ⟨f.1.val.val q⟩
  | composition q => exact ⟨f.2.1.val q⟩
  | formation q => exact ⟨f.2.2.1 q⟩
  | invariant q => exact ⟨f.2.2.2.1.val q⟩
  | signature q => exact ⟨f.2.2.2.2.1.val q⟩
  | operation q => exact ⟨f.2.2.2.2.2.val q⟩
  | circuit q => exact ⟨d.1.val.2.2.2.val q⟩
  | coefficient q => exact ⟨d.2.2.1.val q⟩
  | matching q => exact ⟨IndependentGeneratedObjectMatching.read f.1.val.val f.1.val.property
      f.2.1.val f.2.2.1 f.2.1.property f.1.property q⟩
  | atObject A q => exact (if h : A = IndependentCoreTableAssembly.generatedObject f
      then some ((h.symm ▸ flattenDependent d) q) else none)

/-- Flattening preserves every primitive foundation condition. -/
theorem flatten_foundation (d : IndependentGeometryTableAssembly.ObjectData.{u, v} U) :
    FoundationLaws (flatten d) where
  extraction := d.1.val.1.1.val.property
  finite := d.1.val.1.1.property
  composition := d.1.val.1.2.1.property
  invariant := d.1.val.1.2.2.2.1.property
  signature := d.1.val.1.2.2.2.2.1.property
  operation := d.1.val.1.2.2.2.2.2.property
  atom := d.1.property
  coefficient := d.2.2.1.property

/-- The primitive foundation reconstructed from flattened rows is the original foundation. -/
theorem foundation_flatten (d : IndependentGeometryTableAssembly.ObjectData.{u, v} U) :
    foundation (flatten d) (flatten_foundation d) = d.1.val.1 := rfl

/-- The coefficient primitive stage also survives flattening exactly. -/
theorem coefficientData_flatten (d : IndependentGeometryTableAssembly.ObjectData.{u, v} U) :
    coefficientData (flatten d) (flatten_foundation d) = d.2.2.1 := rfl

/-- Flattened object-candidate flags are exact activation guards. -/
theorem flatten_active (d : IndependentGeometryTableAssembly.ObjectData.{u, v} U) :
    IsActiveTyped (flatten d) := by
  classical
  intro A q
  by_cases hA : A = IndependentCoreTableAssembly.generatedObject d.1.val.1
  · subst A
    simp [flatten, matching, IndependentGeneratedObjectMatching.read,
      IndependentCoreTableAssembly.generatedObject_eq]
  · have hn := hA
    rw [IndependentCoreTableAssembly.generatedObject_eq] at hn
    simp [flatten, matching, IndependentGeneratedObjectMatching.read, hA, hn]

/-- Each active flattened response is exactly its original primitive stage cell. -/
theorem dependent_flatten (d : IndependentGeometryTableAssembly.ObjectData.{u, v} U)
    (ha : matching (flatten d) (.object (IndependentCoreTableAssembly.generatedObject d.1.val.1)) = true) :
    dependent (flatten d) (flatten_active d) _ ha = flattenDependent d := by
  classical
  funext q
  simp [dependent, flatten]

/-- The dependent primitive stages supply all conditions on their flattened active rows. -/
theorem flattenDependent_lawful (d : IndependentGeometryTableAssembly.ObjectData.{u, v} U) :
    DependentLaws (flatten d) (flatten_foundation d) (flattenDependent d) where
  context := d.1.val.2.1.property
  equation := d.1.val.2.2.1.property
  circuit := d.1.val.2.2.2.property
  coverage := d.2.1.1.property
  overlap := d.2.1.2.property
  raw := d.2.2.2.property

/-- All native stage tables flatten to lawful common tables with unique derived matching metadata. -/
theorem flatten_lawful (d : IndependentGeometryTableAssembly.ObjectData.{u, v} U) :
    IsLawful (flatten d) where
  foundation := flatten_foundation d
  matching := IndependentGeneratedObjectMatching.read_isLawful d.1.val.1.1.val.val
    d.1.val.1.1.val.property d.1.val.1.2.1.val d.1.val.1.2.2.1
    d.1.val.1.2.1.property d.1.val.1.1.property
  active := flatten_active d
  dependent A ha := by
    classical
    have hA : A = IndependentCoreTableAssembly.generatedObject d.1.val.1 := by
      simpa [matching, flatten, IndependentGeneratedObjectMatching.read,
        IndependentCoreTableAssembly.generatedObject_eq] using ha
    subst A
    rw [dependent_flatten]
    exact flattenDependent_lawful d

/-- The selected dependent rows of a flattened presentation are its original primitive cells. -/
theorem selected_flatten (d : IndependentGeometryTableAssembly.ObjectData.{u, v} U) :
    selected (flatten d) (flatten_lawful d) = flattenDependent d :=
  dependent_flatten d _

/-- Flattening then collecting stages restores every dependent stage, including raw. -/
theorem stages_flatten (d : IndependentGeometryTableAssembly.ObjectData.{u, v} U) :
    stages (flatten d) (flatten_lawful d) = d := by
  simp only [stages, selected_flatten]
  rfl

/-- The generated-reference branch contains exactly one original dependent point. -/
theorem flatten_at_generated (d : IndependentGeometryTableAssembly.ObjectData.{u, v} U)
    (q : DependentQuery.{u, v} (IndependentCoreTableAssembly.generatedObject d.1.val.1)) :
    flatten d (.atObject _ q) = some (flattenDependent d q) := by
  classical
  simp [flatten]

/-- Every other candidate branch has the unique absent response. -/
theorem flatten_at_inactive (d : IndependentGeometryTableAssembly.ObjectData.{u, v} U)
    (A : ArchitectureObject U) (hA : A ≠ IndependentCoreTableAssembly.generatedObject d.1.val.1)
    (q : DependentQuery.{u, v} A) : flatten d (.atObject A q) = none := by
  classical
  simp [flatten, hA]

/-- Every primitive response in the selected stages is exactly the selected common row. -/
theorem flattenDependent_stages (t : Table.{u, v} U) (h : IsLawful t) :
    flattenDependent (stages t h) = selected t h := by
  funext q
  cases q <;> rfl

/-- Collecting and flattening stages restores every common primitive cell and every inactive row. -/
theorem flatten_stages (t : Table.{u, v} U) (h : IsLawful t) : flatten (stages t h) = t := by
  classical
  funext q
  cases q with
  | extraction q => rfl
  | composition q => rfl
  | formation q => rfl
  | invariant q => rfl
  | signature q => rfl
  | operation q => rfl
  | circuit q => rfl
  | coefficient q => rfl
  | matching q =>
      have he := IndependentGeneratedObjectMatching.eq_read (extraction t) h.foundation.extraction
        (composition t) (formation t) h.foundation.composition h.foundation.finite
        (matching t) h.matching
      exact congrArg ULift.up (congrFun he q).symm
  | atObject A q =>
      by_cases hA : A = generated t h.foundation
      · subst A
        have he := congrFun (flattenDependent_stages t h) q
        exact (flatten_at_generated (stages t h) q).trans
          ((congrArg some he).trans (some_dependent t h.active _ (generated_active t h) q))
      · have hn : matching t (.object A) = false := by
          cases hm : matching t (.object A) with
          | false => rfl
          | true => exact False.elim (hA ((active_iff_generated t h A).1 hm))
        have hz := inactive_eq_none t h.active A hn q
        exact (flatten_at_inactive (stages t h) A hA q).trans hz.symm

/-- Lawful common primitive tables have an exact equivalence with the verified dependent stages. -/
def stageEquiv : IndependentGeometryTableAssembly.ObjectData.{u, v} U ≃
    {t : Table.{u, v} U // IsLawful t} where
  toFun d := ⟨flatten d, flatten_lawful d⟩
  invFun t := stages t.val t.property
  left_inv := stages_flatten
  right_inv t := Subtype.ext (flatten_stages t.val t.property)

/-- Every complete native geometry object has one lawful table on the common primitive declaration. -/
def objectEquiv : ReadingCore.{u, v} U ≃ {t : Table.{u, v} U // IsLawful t} :=
  IndependentGeometryTableAssembly.objectEquiv.trans stageEquiv

/-- Read all native fields into the single realization-independent dependent query table. -/
def read (G : ReadingCore.{u, v} U) : Table.{u, v} U := (objectEquiv G).val

/-- Native readings satisfy the common primitive conditions. -/
theorem read_isLawful (G : ReadingCore.{u, v} U) : IsLawful (read G) := (objectEquiv G).property

/-- Native assembly after primitive reading restores the complete original geometry object. -/
theorem assemble_read (G : ReadingCore.{u, v} U) : assemble (read G) (read_isLawful G) = G :=
  objectEquiv.left_inv G

/-- Primitive reading after native assembly restores every lawful common cell. -/
theorem read_assemble (t : Table.{u, v} U) (h : IsLawful t) : read (assemble t h) = t :=
  congrArg Subtype.val (objectEquiv.right_inv ⟨t, h⟩)

/-- The common primitive reading separates every native complete-geometry field. -/
theorem read_injective : Function.Injective (read.{u, v} (U := U)) := by
  intro G H h
  exact objectEquiv.injective (Subtype.ext h)

end

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryPrimitive

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryPrimitive
