import ResearchLean.AG.ObstructionDiagnosticBridge.GeneratorPresentation
import Formal.AG.Atom.ArchitectureObject
import Formal.Util.AssertStandardAxioms

/-!
# G-132: point and generator Atoms for arbitrary primitive input

The carrier retains every geometric point and every declared Law occurrence.
Its architecture relation on generator Atoms is the primitive presentation R.

## Implementation notes

The tagged sum preserves geometric and Law provenance. The dependent payload
retains the declared Law's actual value type; no common value type is assumed.
All inputs are T0 data, without reflection or cohomological assumptions.
-/

noncomputable section

namespace AAT.AG.VisibleCycleReflection

open CanonicalResolution ObstructionDiagnosticBridge

universe u

variable {Source X : Type u} {laws : FiniteLawFamily Source}

/-- T0 Atom kinds distinguish geometric points and primitive generators. -/
inductive AtomKind where
  | point
  | generator

/-- T0 carrier generated from points and the declared Law occurrences. -/
def atomCarrier (X : Type u) (laws : FiniteLawFamily Source) : AtomCarrier.{u} where
  AtomKind := ULift.{u} AtomKind
  Axis := PUnit
  Subject := X ⊕ Source
  Predicate := Option laws.Law
  Payload := Unit ⊕ (Σ law, laws.Value law)
  Atom := X ⊕ PrimitiveGenerator laws
  kind
    | .inl _ => ⟨.point⟩
    | .inr _ => ⟨.generator⟩
  axis := fun _ => PUnit.unit
  subject
    | .inl point => .inl point
    | .inr generator => .inr generator.2
  predicate
    | .inl _ => none
    | .inr generator => some generator.1
  payload
    | .inl _ => .inl ()
    | .inr generator => .inr ⟨generator.1, laws.eval generator.1 generator.2⟩

/-- T0 architecture relation is exactly R on the generator summand. -/
def architectureObject (X : Type u) (P : GeneratorPresentation laws) :
    ArchitectureObject (atomCarrier X laws) where
  configuration := {
    family := ⟨fun _ => True⟩
    relation := fun left right =>
      match left, right with
      | .inr leftGenerator, .inr rightGenerator => P.relation leftGenerator rightGenerator
      | _, _ => False
    identification := fun _ _ => False
  }
  StructureMaps := PUnit
  SelectedQuantities := PUnit
  structureMaps := PUnit.unit
  selectedQuantities := PUnit.unit

/-- Atom relation API: the construction retains the supplied primitive relation. -/
@[simp]
theorem generator_relation_iff (P : GeneratorPresentation laws)
    (left right : PrimitiveGenerator laws) :
    (architectureObject X P).configuration.relation (.inr left) (.inr right) ↔
      P.relation left right := Iff.rfl

/-- Atom API: the carrier retains each generator's declared Law and value. -/
@[simp]
theorem generator_payload (g : PrimitiveGenerator laws) :
    (atomCarrier X laws).payload (.inr g) =
      .inr ⟨g.1, laws.eval g.1 g.2⟩ := rfl

/-- Geometry API: a point has no outgoing primitive-generator relation. -/
@[simp]
theorem point_not_related (P : GeneratorPresentation laws) (x : X)
    (a : (atomCarrier X laws).Atom) :
    ¬ (architectureObject X P).configuration.relation (.inl x) a := by
  cases a <;> simp [architectureObject]

end AAT.AG.VisibleCycleReflection

#assert_standard_axioms_only AAT.AG.VisibleCycleReflection
