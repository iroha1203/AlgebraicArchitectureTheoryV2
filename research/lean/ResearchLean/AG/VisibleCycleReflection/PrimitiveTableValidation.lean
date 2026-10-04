import ResearchLean.AG.VisibleCycleReflection.FiniteInputTable
import Formal.Util.AssertStandardAxioms

/-!
# Decoding checked primitive Laws, reading, and raw relations

## Implementation notes

The same Boolean relation is decoded into the original GeneratorPresentation.
The generated graph's reachability equals its reflexive symmetric transitive
relation closure. The finite Rq test therefore generates ReflectionCondition;
it never replaces the original relation by equality of labels. Adequacy is
proved from the independently checked reading fibers.
-/

namespace AAT.AG.VisibleCycleReflection.FiniteInputTable
open CanonicalResolution ResolutionInvariance ObstructionDiagnosticBridge
variable (T : FiniteInputTable)

/-- Actual source-generated labels are exactly the generated dependent raw value codes. -/
def generatedLabelEquiv : LawValueLabel T.laws ≃
    {r : T.RawLabel // ∃ s : T.Source, T.eval r.1 s = r.2} where
  toFun l := ⟨⟨l.law,l.value⟩,l.generated⟩
  invFun l := ⟨l.1.1,l.1.2,l.2⟩
  left_inv l := by cases l; rfl
  right_inv l := by cases l with | mk r hr => cases r; rfl

/-- The actual label equivalence retains the declared Law, value, and source generation. -/
theorem generatedLabelEquiv_apply (l : LawValueLabel T.laws) :
    (T.generatedLabelEquiv l).1 = ⟨l.law,l.value⟩ := rfl

/-- On an original primitive generator the actual label is exactly the raw evaluation code. -/
theorem generatedLabelEquiv_primitive (g : T.Generator) :
    (T.generatedLabelEquiv (PrimitiveGenerator.label T.laws g)).1 = T.rawLabel g := rfl

/-- Equality of actual primitive labels is precisely equality of raw Law-dependent codes. -/
theorem primitive_label_eq_iff (g h : T.Generator) :
    PrimitiveGenerator.label T.laws g = PrimitiveGenerator.label T.laws h ↔
      T.rawLabel g = T.rawLabel h := by
  constructor
  · intro he
    exact congrArg (fun l => (T.generatedLabelEquiv l).1) he
  · intro he
    apply T.generatedLabelEquiv.injective
    exact Subtype.ext he

/-- Decode the same finite reading after the source search confirms surjectivity. -/
def reading (h : T.SurjectiveReading) : Reading T.Source where
  Target := Fin T.targetCount
  read := T.read
  surjective := h

/-- The decoded reading map is precisely the supplied finite reading table. -/
@[simp] theorem reading_read (h : T.SurjectiveReading) (s : T.Source) :
    (T.reading h).read s = T.read s := rfl

/-- The finite fiber adequacy check is equivalent to actual Law adequacy. -/
theorem adequate_iff (h : T.SurjectiveReading) :
    T.AdequateReading ↔ T.laws.Adequate (T.reading h) := by
  rw [T.laws.adequate_iff_kernel]
  rfl

/-- Decode the same Boolean primitive relation, with its checked label preservation proof. -/
def presentation (h : T.LabelPreserving) : GeneratorPresentation T.laws where
  relation g k := T.relation g k = true
  relation_preserves_label := by
    intro g k hr
    exact (T.primitive_label_eq_iff g k).mpr (h g k hr)

/-- Public relation formula retains every supplied primitive relation and no others. -/
theorem presentation_relation (h : T.LabelPreserving) (g k : T.Generator) :
    (T.presentation h).relation g k ↔ T.relation g k = true := Iff.rfl

/-- Raw symmetric finite reachability is exactly the generated equivalence closure of raw R. -/
theorem relationGraph_reachable_iff (g k : T.Generator) :
    T.relationGraph.Reachable g k ↔ Relation.EqvGen (fun a b => T.relation a b = true) g k := by
  constructor
  · rintro ⟨p⟩
    induction p with
    | nil => exact Relation.EqvGen.refl _
    | @cons a b c hab p ih =>
      have he : Relation.EqvGen (fun a b => T.relation a b = true) a b := by
        rcases (T.relationGraph_adj a b).mp hab with ⟨_,hr | hr⟩
        · exact Relation.EqvGen.rel a b hr
        · exact Relation.EqvGen.symm b a (Relation.EqvGen.rel b a hr)
      exact Relation.EqvGen.trans a b c he ih
  · intro h
    induction h with
    | rel a b hr =>
      by_cases he : a = b
      · subst b
        exact SimpleGraph.Reachable.refl _
      · apply SimpleGraph.Adj.reachable
        exact (T.relationGraph_adj a b).mpr ⟨he,Or.inl hr⟩
    | refl a => exact SimpleGraph.Reachable.refl _
    | symm a b _ ih => exact ih.symm
    | trans a b c _ _ ih ih' => exact ih.trans ih'

/-- The actual presentation's relatedness is computed by the same raw relation graph. -/
theorem presentation_related_iff (h : T.LabelPreserving) (g k : T.Generator) :
    (T.presentation h).Related g k ↔ T.relationGraph.Reachable g k :=
  (T.relationGraph_reachable_iff g k).symm

/-- The finite Rq test is equivalent to the original actual ReflectionCondition. -/
theorem reflectionCondition_iff (h : T.LabelPreserving) :
    T.RelationReflecting ↔ (T.presentation h).ReflectionCondition := by
  constructor
  · intro hr g k he
    exact (T.presentation_related_iff h g k).mpr (hr g k ((T.primitive_label_eq_iff g k).mp he))
  · intro hr g k he
    exact (T.presentation_related_iff h g k).mp (hr g k ((T.primitive_label_eq_iff g k).mpr he))

end AAT.AG.VisibleCycleReflection.FiniteInputTable
#assert_standard_axioms_only AAT.AG.VisibleCycleReflection
