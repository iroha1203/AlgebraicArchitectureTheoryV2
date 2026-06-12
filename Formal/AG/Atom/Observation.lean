import Formal.AG.Atom.Axioms

namespace AAT.AG

universe u

/-- I.命題A9: an observation map from a family carrier to observations. -/
structure ObservationModel (Family Observation : Type u) where
  observe : Family -> Observation

namespace ObservationModel

/-- I.命題A9: observations can collapse distinct families. -/
def NonInjective {Family Observation : Type u}
    (M : ObservationModel Family Observation) : Prop :=
  ∃ F G, F ≠ G ∧ M.observe F = M.observe G

end ObservationModel

/-- I.命題A9: a coarse projection used by an observation reading. -/
structure ObservationProjection (Family CoarseFamily : Type u) where
  project : Family -> CoarseFamily

/-- I.命題A9: a reconstruction attempt from observations back to families. -/
structure ReconstructionAttempt (Observation Family : Type u) where
  reconstruct : Observation -> Family

/--
I.命題A9: a non-injective observation map admits no exact reconstruction for
all families.
-/
theorem no_exact_reconstruction_of_nonInjective {Family Observation : Type u}
    (M : ObservationModel Family Observation)
    (R : ReconstructionAttempt Observation Family)
    (hM : M.NonInjective) :
    ¬ ∀ F, R.reconstruct (M.observe F) = F := by
  intro hExact
  rcases hM with ⟨F, G, hne, hobs⟩
  apply hne
  calc
    F = R.reconstruct (M.observe F) := (hExact F).symm
    _ = R.reconstruct (M.observe G) := by rw [hobs]
    _ = G := hExact G

namespace A9Example

inductive Atom where
  | observed
  | hidden
  deriving DecidableEq

inductive Family where
  | canonical
  | alternative
  deriving DecidableEq

inductive Source where
  | source

inductive Observation where
  | collapsed
  deriving DecidableEq

/-- I.命題A9: a tiny carrier with one observed atom and one hidden atom. -/
def carrier : AtomCarrier where
  AtomKind := Unit
  Axis := Unit
  Subject := Unit
  Predicate := Unit
  Payload := Unit
  Atom := Atom
  kind := fun _ => ()
  axis := fun _ => ()
  subject := fun _ => ()
  predicate := fun _ => ()
  payload := fun _ => ()

/-- I.命題A9: a constant observation collapses all example atoms. -/
def observeAtom (_atom : Atom) : Observation := Observation.collapsed

/-- I.命題A9: the selected atom read from a collapsed observation. -/
def observedAtom? : Observation -> Option Atom
  | Observation.collapsed => some Atom.observed

/-- I.命題A9: a constant observation collapses two different atoms. -/
theorem noninjective_atom_observation :
    ∃ a b : Atom, a ≠ b ∧ observeAtom a = observeAtom b := by
  refine ⟨Atom.observed, Atom.hidden, ?_, rfl⟩
  intro h
  cases h

/-- I.命題A9: which atoms are recovered from the selected observation surface. -/
def AppearsInObservation (atom : Atom) : Prop :=
  observedAtom? (observeAtom atom) = some atom

/-- I.命題A9: an atom can exist without appearing in the observation surface. -/
theorem unobserved_atom_exists :
    ∃ atom : Atom, ¬ AppearsInObservation atom := by
  exact ⟨Atom.hidden, by simp [AppearsInObservation, observedAtom?]⟩

/-- I.命題A9: the example family observation collapses all families. -/
def familyObservation : ObservationModel Family Observation where
  observe := fun _ => Observation.collapsed

/-- I.命題A9: the family observation is non-injective. -/
theorem noninjective_family_observation :
    familyObservation.NonInjective := by
  refine ⟨Family.canonical, Family.alternative, ?_, rfl⟩
  intro h
  cases h

/-- I.命題A9: the associated coarse projection. -/
def projection : ObservationProjection Family Observation where
  project := familyObservation.observe

/-- I.命題A9: a reconstruction attempt that chooses the canonical family. -/
def reconstruction : ReconstructionAttempt Observation Family where
  reconstruct := fun _ => Family.canonical

/-- I.命題A9: the non-injective example has no exact reconstruction. -/
theorem reconstruction_not_exact :
    ¬ ∀ F, reconstruction.reconstruct (familyObservation.observe F) = F :=
  no_exact_reconstruction_of_nonInjective familyObservation reconstruction
    noninjective_family_observation

/-- I.命題A9 / A8: a doctrine whose canonical family is independent of observation. -/
def doctrine : ExtractionDoctrine carrier Family where
  Source := Source
  Vocabulary := Unit
  SemanticReading := Unit
  Resolution := Unit
  sourceSemantics := fun _ => Unit
  normalize := fun src => src
  atomize := fun _ => Family.canonical

/-- I.命題A9 / A8: canonical family uniqueness follows from the doctrine. -/
theorem canonical_family_unique {F G : Family}
    (hF : F = doctrine.atomize Source.source)
    (hG : G = doctrine.atomize Source.source) : F = G :=
  ExtractionDoctrine.atomize_unique doctrine Source.source hF hG

/--
I.命題A9: observation incompleteness and A8 canonical-family uniqueness are
separate facts in the same finite example.
-/
theorem observation_incompleteness_coexists_with_a8 :
    familyObservation.NonInjective ∧
      (∀ {F G : Family},
        F = doctrine.atomize Source.source ->
        G = doctrine.atomize Source.source ->
        F = G) := by
  constructor
  · exact noninjective_family_observation
  · intro F G hF hG
    exact canonical_family_unique hF hG

end A9Example

end AAT.AG
