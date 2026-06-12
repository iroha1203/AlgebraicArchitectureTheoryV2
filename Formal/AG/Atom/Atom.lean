namespace AAT.AG

universe u

/--
I.定義1.1 Atom.

An `AtomRecord` is the five-coordinate typed fact used by AG AAT Part I:
kind, axis, subject, predicate, and payload. This bootstrap declaration only
introduces the carrier shape; the A0-A8 package lives in
`Formal.AG.Atom.Axioms`.
-/
structure AtomRecord
    (AtomKind Axis Subject Predicate Payload : Type u) where
  kind : AtomKind
  axis : Axis
  subject : Subject
  predicate : Predicate
  payload : Payload

/--
I.定義1.1 Atom carrier.

`AtomCarrier` keeps the universe-level atom type and its five coordinate
projections together. It is intentionally independent of `Formal/Arch`, so the
AG formalization can grow from the Part I text rather than from Classic AAT.
-/
structure AtomCarrier where
  AtomKind : Type u
  Axis : Type u
  Subject : Type u
  Predicate : Type u
  Payload : Type u
  Atom : Type u
  kind : Atom -> AtomKind
  axis : Atom -> Axis
  subject : Atom -> Subject
  predicate : Atom -> Predicate
  payload : Atom -> Payload

namespace AtomCarrier

/-- I.定義1.1: read an atom of a carrier as its five-coordinate record. -/
def record (U : AtomCarrier.{u}) (a : U.Atom) :
    AtomRecord U.AtomKind U.Axis U.Subject U.Predicate U.Payload where
  kind := U.kind a
  axis := U.axis a
  subject := U.subject a
  predicate := U.predicate a
  payload := U.payload a

end AtomCarrier

end AAT.AG
