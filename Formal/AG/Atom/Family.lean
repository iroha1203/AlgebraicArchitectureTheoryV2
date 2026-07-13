import Formal.AG.Atom.Atom

namespace AAT.AG

universe u

/-- I.定義3.1: an Atom family is a predicate selecting atoms of a carrier. -/
structure AtomFamily (U : AtomCarrier.{u}) where
  mem : U.Atom -> Prop

namespace AtomFamily

/-- Extensionality of Atom families by pointwise membership. -/
@[ext] theorem ext {U : AtomCarrier.{u}} {F G : AtomFamily U}
    (h : ∀ atom, F.mem atom ↔ G.mem atom) : F = G := by
  cases F with
  | mk f =>
      cases G with
      | mk g =>
          congr 1
          funext atom
          exact propext (h atom)

/-- Inclusion of Atom families. -/
def Subset {U : AtomCarrier.{u}} (F G : AtomFamily U) : Prop :=
  ∀ {atom}, F.mem atom -> G.mem atom

/--
I.定義3.1 / peer-review hardening I-3: concrete finite-support reading for an Atom family.

Unlike the legacy `finite : Prop` markers on packages that consume families,
this predicate is load-bearing: it supplies an explicit list that covers every
selected atom.
-/
def ListFinite {U : AtomCarrier.{u}} (F : AtomFamily U) : Prop :=
  ∃ atoms : List U.Atom, ∀ atom, F.mem atom -> atom ∈ atoms

/-- I.定義3.2: the subject support of an Atom family. -/
def support {U : AtomCarrier.{u}} (F : AtomFamily U) (subject : U.Subject) :
    Prop :=
  ∃ atom, F.mem atom ∧ U.subject atom = subject

/-- I.定義3.3: restrict an Atom family to a selected axis. -/
def restrictAxis {U : AtomCarrier.{u}} (F : AtomFamily U) (axis : U.Axis) :
    AtomFamily U where
  mem atom := F.mem atom ∧ U.axis atom = axis

/--
I.定義3.4: compatibility is relative to a selected payload compatibility
relation for atoms with the same subject and predicate inside a family.
-/
def Compatible {U : AtomCarrier.{u}} (payloadCompatible : U.Payload -> U.Payload -> Prop)
    (F : AtomFamily U) : Prop :=
  ∀ {a b}, F.mem a -> F.mem b ->
    U.subject a = U.subject b -> U.predicate a = U.predicate b ->
      payloadCompatible (U.payload a) (U.payload b)

/-- I.定義3.4: equality is the strict compatibility reading. -/
def EqCompatible {U : AtomCarrier.{u}} (F : AtomFamily U) : Prop :=
  Compatible Eq F

/-- I.定義3.5: primitive and derived origin markers for family membership. -/
inductive AtomOrigin where
  | primitive
  | derived
  deriving DecidableEq

/-- I.定義3.5: an Atom family equipped with origin markers. -/
structure OriginMarked (U : AtomCarrier.{u}) extends AtomFamily U where
  origin : ∀ atom, mem atom -> AtomOrigin

/-- I.定義3.5: a monotone inference rule family used to close Atom families. -/
structure InferenceSystem (U : AtomCarrier.{u}) where
  derives : AtomFamily U -> U.Atom -> Prop
  monotone : ∀ {F G : AtomFamily U}, F.Subset G ->
    ∀ {atom}, derives F atom -> derives G atom

/-- I.定義3.5: a family is closed under an inference system. -/
def IsClosed {U : AtomCarrier.{u}} (R : InferenceSystem U)
    (F : AtomFamily U) : Prop :=
  ∀ {atom}, R.derives F atom -> F.mem atom

/--
I.定義3.5: closure is the least closed family containing `F`, represented as
the intersection of all closed supersets.
-/
def closure {U : AtomCarrier.{u}} (R : InferenceSystem U)
    (F : AtomFamily U) : AtomFamily U where
  mem atom := ∀ G : AtomFamily U, F.Subset G -> IsClosed R G -> G.mem atom

/-- I.定義3.2: membership witnesses support. -/
theorem support_of_mem {U : AtomCarrier.{u}} {F : AtomFamily U}
    {atom : U.Atom} (h : F.mem atom) :
    F.support (U.subject atom) :=
  ⟨atom, h, rfl⟩

/-- I.定義3.3: axis restriction is a subfamily. -/
theorem restrictAxis_subset {U : AtomCarrier.{u}} (F : AtomFamily U)
    (axis : U.Axis) :
    (F.restrictAxis axis).Subset F := by
  intro atom h
  exact h.1

/-- I.定義3.3: every restricted atom lies on the selected axis. -/
theorem restrictAxis_axis {U : AtomCarrier.{u}} (F : AtomFamily U)
    (axis : U.Axis) {atom : U.Atom}
    (h : (F.restrictAxis axis).mem atom) :
    U.axis atom = axis :=
  h.2

/-- I.定義3.5(a): every original atom is in its closure. -/
theorem subset_closure {U : AtomCarrier.{u}} (R : InferenceSystem U)
    (F : AtomFamily U) :
    F.Subset (closure R F) := by
  intro atom hAtom G hFG _hClosed
  exact hFG hAtom

/-- I.定義3.5(b): the closure is closed under the inference system. -/
theorem closure_isClosed {U : AtomCarrier.{u}} (R : InferenceSystem U)
    (F : AtomFamily U) :
    IsClosed R (closure R F) := by
  intro atom hDerives G hFG hClosed
  apply hClosed
  exact R.monotone (F := closure R F) (G := G)
    (by
      intro candidate hCandidate
      exact hCandidate G hFG hClosed)
    hDerives

/-- I.定義3.5(c): closure is the smallest closed family containing `F`. -/
theorem closure_minimal {U : AtomCarrier.{u}} (R : InferenceSystem U)
    (F G : AtomFamily U) (hFG : F.Subset G) (hClosed : IsClosed R G) :
    (closure R F).Subset G := by
  intro atom hAtom
  exact hAtom G hFG hClosed

end AtomFamily

end AAT.AG
