import Formal.SHIGURE.Part1.Models
import Mathlib.Data.Set.Finite.Basic

/-! # Value fragments from finite queries

Definition 3.8 specifies sample names and typed queries over an ordinary
signature. The resulting table has an entry at each declared query index.
Its type is defined independently of whether a model realizes the table.

## Implementation notes

A finite dependent sum counts the whole sample even when the signature has
infinitely many sorts. Per-sort finiteness alone permits infinitely many
named states. The name types retain their sort through every query, and a
dependent answer family gives a value at exactly the declared index type.

The positive policy records a witness marker or leaves the entry empty. A
Bool is used when both truth values need explicit records. Raw outputs keep
their full carrier type. Sampled outputs distinguish an outside value from a
nonempty finite set of all matching names, since a single chosen name loses
aliases. The outer option for value queries tracks definedness separately.
ULift places these typed answers in the common universe of the table.
-/

universe u v

namespace SHIGURE.ValueFragment

/-- A truth query may record only a positive fact, or record either truth value. -/
inductive TruthRecording where
  | positive
  | both

/-- A value query can retain its output directly or report its sample names. -/
inductive OutputRecording where
  | raw
  | sampled

/-- A defined output recorded by all of its sample names, or as outside the sample. -/
inductive SampledValue (Name : Type v) where
  | outside
  | named (names : Finset Name) (nonempty : names.Nonempty)

/-- The shape of the record for a truth query. -/
def TruthRecording.Answer : TruthRecording → Type
  | .positive => Option Unit
  | .both => Bool

/-- Read an atomic fact under the selected truth-recording policy. -/
noncomputable def TruthRecording.record : (mode : TruthRecording) → Prop → mode.Answer := by
  classical
  exact fun mode p => match mode with
    | .positive => if p then some () else none
    | .both => decide p

/-- A two-sided query answers true exactly when its atomic fact holds. -/
@[simp] theorem TruthRecording.record_both_eq_true (p : Prop) :
    TruthRecording.record .both p = true ↔ p := by
  classical
  change decide p = true ↔ p
  simp

/-- A positive-only answer records a fact exactly when the fact holds. -/
@[simp] theorem TruthRecording.record_positive_eq_some (p : Prop) :
    TruthRecording.record .positive p = some () ↔ p := by
  classical
  change (if p then some () else none) = some () ↔ p
  simp

/-- A two-sided query answers false exactly when its atomic fact fails. -/
@[simp] theorem TruthRecording.record_both_eq_false (p : Prop) :
    TruthRecording.record .both p = false ↔ ¬ p := by
  classical
  change decide p = false ↔ ¬ p
  simp

/-- An atomic query uses sample names at the declared input and output sorts. -/
inductive AtomicQuery (sig : Signature.{u}) (Name : sig.SortType → Type v) where
  | eq {s : sig.SortType} (left right : Name s)
  | graph (op : Operation sig) (inputs : Assignment Name op.arity.inputs)
      (output : Name op.arity.output)
  | relation (r : sig.Rel) (inputs : Assignment Name (sig.relInputs r))
  | domain (p : sig.Partial) (inputs : Assignment Name (sig.partialArity p).inputs)

/-- A truth or value query together with its answer policy. -/
inductive Query (sig : Signature.{u}) (Name : sig.SortType → Type v) where
  | truth (mode : TruthRecording) (atom : AtomicQuery sig Name)
  | value (op : Operation sig) (inputs : Assignment Name op.arity.inputs) (mode : OutputRecording)

/-- Finite sample names per sort and a finite collection of named queries. -/
structure Schema (sig : Signature.{u}) where
  /-- The available sample names at each sort. -/
  Name : sig.SortType → Type v
  /-- The total collection of sample names is finite. -/
  finiteNames : Finite (Σ s, Name s)
  /-- The names of the queries. -/
  Index : Type v
  /-- There are finitely many queries. -/
  finiteIndices : Finite Index
  /-- The typed query specified at each name. -/
  query : Index → Query sig Name

variable {sig : Signature.{u}} {Name : sig.SortType → Type v}

/-- The states designated by the typed sample names. -/
abbrev Samples (Name : sig.SortType → Type v) (Carrier : sig.SortType → Type u) :=
  ∀ s, Name s → Carrier s

/-- Read a tuple of states from a tuple of sample names. -/
def Samples.tuple {Carrier : sig.SortType → Type u} (sample : Samples Name Carrier)
    {Γ : List sig.SortType} (inputs : Assignment Name Γ) : Assignment Carrier Γ :=
  ⟨fun {s} i => sample s (inputs i)⟩

/-- The names at each fixed sort sit inside the finite collection of all names. -/
theorem Samples.finiteNamesAt (Name : sig.SortType → Type v) [Finite (Σ s, Name s)]
    (s : sig.SortType) : Finite (Name s) :=
  Finite.of_injective (fun n => (⟨s, n⟩ : Σ t, Name t))
    (fun _ _ h => by cases h; rfl)

/-- Read equality or the corresponding graph, relation, or domain membership from a structure. -/
def AtomicQuery.holds (A : Structure sig) (sample : Samples Name A.carrier) :
    AtomicQuery sig Name → Prop
  | .eq (s := s) left right => sample s left = sample s right
  | .graph op inputs output => A.Graph op (sample.tuple inputs) (sample _ output)
  | .relation r inputs => sample.tuple inputs ∈ A.relation r
  | .domain p inputs => sample.tuple inputs ∈ A.partialDomain p

/-- The record for a defined result, with the output type determined by the policy. -/
def OutputRecording.Answer (Name : Type v) (Value : Type u) : OutputRecording → Type (max u v)
  | .raw => ULift.{v} Value
  | .sampled => ULift.{u} (SampledValue Name)

/-- Represent a defined output according to the selected output policy. -/
noncomputable def OutputRecording.record {State : Type u} {Name : Type v} [Finite Name]
    (sample : Name → State) (state : State) :
    (mode : OutputRecording) → mode.Answer Name State
  | .raw => ⟨state⟩
  | .sampled => by
    classical
    let names := Set.toFinite {n | sample n = state}
    exact ⟨if h : names.toFinset.Nonempty then .named names.toFinset h else .outside⟩

/-- Sampled recording reports either every matching name or the lack of any matching name. -/
theorem OutputRecording.record_sampled_spec {State : Type u} {Name : Type v} [Finite Name]
    (sample : Name → State) (value : State) :
    match (OutputRecording.record sample value .sampled).down with
    | .outside => ∀ n, sample n ≠ value
    | .named names _ => ∀ n, n ∈ names ↔ sample n = value := by
  classical
  by_cases h : (Set.toFinite {n | sample n = value}).toFinset.Nonempty
  · simp only [OutputRecording.record, dif_pos h]
    intro n
    exact Set.Finite.mem_toFinset _
  · simp only [OutputRecording.record, dif_neg h]
    intro n matchesValue
    exact h ⟨n, (Set.Finite.mem_toFinset _).2 matchesValue⟩

/-- The typed answer to one query. A value query can have an undefined result. -/
def Query.Answer (Carrier : sig.SortType → Type u) : Query sig Name → Type (max u v)
  | .truth mode _ => ULift.{max u v} mode.Answer
  | .value op _ mode => Option (mode.Answer (Name op.arity.output) (Carrier op.arity.output))

/-- Evaluate one query on the ordinary structure using only its named tuple. -/
noncomputable def Query.read (A : Structure sig) (sample : Samples Name A.carrier)
    [Finite (Σ s, Name s)] : (query : Query sig Name) → query.Answer A.carrier
  | .truth mode atom => ⟨mode.record (atom.holds A sample)⟩
  | .value op inputs mode => by
    classical
    letI := Samples.finiteNamesAt Name op.arity.output
    exact (A.applyOp op (sample.tuple inputs)).toOption.map
      (fun value => mode.record (sample _) value)

/-- Truth queries record the named atomic fact under the chosen policy. -/
theorem Query.read_truth {A : Structure sig} (sample : Samples Name A.carrier)
    [Finite (Σ s, Name s)] (mode : TruthRecording) (atom : AtomicQuery sig Name) :
    (Query.truth mode atom).read A sample = ⟨mode.record (atom.holds A sample)⟩ :=
  rfl

/-- Two-sided equality records truth exactly when both names designate the same state. -/
theorem Query.read_equality_true_iff {A : Structure sig} (sample : Samples Name A.carrier)
    [Finite (Σ s, Name s)] {s : sig.SortType} (left right : Name s) :
    ((Query.truth .both (.eq left right)).read A sample).down = true ↔
      sample s left = sample s right := by
  rw [read_truth]
  exact TruthRecording.record_both_eq_true _

/-- A defined value query reports the graph's value under the selected output policy. -/
theorem Query.read_value_of_graph {A : Structure sig} (sample : Samples Name A.carrier)
    [Finite (Σ s, Name s)] (op : Operation sig) (inputs : Assignment Name op.arity.inputs)
    (mode : OutputRecording) {value : A.carrier op.arity.output}
    (graph : A.Graph op (sample.tuple inputs) value) :
    letI := Samples.finiteNamesAt Name op.arity.output
    (Query.value op inputs mode).read A sample = some (mode.record (sample _) value) := by
  classical
  simp only [Query.read, Part.toOption_eq_some_iff.mpr graph, Option.map_some]

/-- A raw value query returns the full carrier value on the ordinary graph. -/
theorem Query.read_value_raw {A : Structure sig} (sample : Samples Name A.carrier)
    [Finite (Σ s, Name s)] (op : Operation sig) (inputs : Assignment Name op.arity.inputs)
    {value : A.carrier op.arity.output} (graph : A.Graph op (sample.tuple inputs) value) :
    (Query.value op inputs .raw).read A sample = some ⟨value⟩ :=
  read_value_of_graph sample op inputs .raw graph

/-- A query at an undefined input has no value under either output policy. -/
theorem Query.read_value_undefined {A : Structure sig} (sample : Samples Name A.carrier)
    [Finite (Σ s, Name s)] (op : Operation sig) (inputs : Assignment Name op.arity.inputs)
    (mode : OutputRecording) (undefined : ¬ (A.applyOp op (sample.tuple inputs)).Dom) :
    (Query.value op inputs mode).read A sample = none := by
  classical
  simp only [Query.read, (Part.toOption_eq_none _).mpr undefined, Option.map_none]

/-- Sample states and the answers indexed by one finite schema. -/
structure Fragment (schema : Schema.{u,v} sig) (Carrier : sig.SortType → Type u) where
  /-- The states named by the chosen samples. -/
  sample : Samples schema.Name Carrier
  /-- The observations for the declared queries. -/
  answer : (i : schema.Index) → (schema.query i).Answer Carrier

/-- Restrict an ordinary structure and its chosen sample states to a value fragment. -/
noncomputable def Schema.read (schema : Schema.{u,v} sig) (A : Structure sig)
    (sample : Samples schema.Name A.carrier) : Fragment schema A.carrier where
  sample := sample
  answer i :=
    letI := schema.finiteNames
    (schema.query i).read A sample

/-- Restrict a model using the values in its ordinary structure. -/
noncomputable def Schema.readModel {T : Theory.{u}} (schema : Schema.{u,v} T.signature)
    (A : Model T) (sample : Samples schema.Name A.obj.carrier) : Fragment schema A.obj.carrier :=
  schema.read A.obj sample

/-- The samples in the observed table are exactly the original designated states. -/
@[simp] theorem Schema.read_sample (schema : Schema.{u,v} sig) (A : Structure sig)
    (sample : Samples schema.Name A.carrier) : (schema.read A sample).sample = sample :=
  rfl

/-- Each answer in the table comes from reading the query at that declared index. -/
theorem Schema.read_answer (schema : Schema.{u,v} sig) (A : Structure sig)
    (sample : Samples schema.Name A.carrier) (i : schema.Index) :
    (schema.read A sample).answer i =
      (letI := schema.finiteNames; (schema.query i).read A sample) :=
  rfl

end SHIGURE.ValueFragment
