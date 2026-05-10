---
title: "When Lean Proved My Durability Definition Too Easily"
published: false
description: "A small formalization experiment about invariants, missing boundaries, and what it means for architecture to preserve something."
tags: architecture, databases, lean, computerscience
---

> **TL;DR**
>
> I tried to formalize a small ACID-like model in Lean 4.
>
> Consistency became invariant preservation.
> Isolation became a deliberately strong commutation law.
> Durability exposed a missing model boundary.
>
> The result was not a proof that databases are correct.
> It was a reminder that architecture claims only make sense inside explicit boundaries.

ACID is familiar enough that it is easy to stop thinking about it.

Atomicity. Consistency. Isolation. Durability.

In ordinary database terms, the rough meanings are:

```text
Atomicity
  A transaction is all-or-nothing. It commits as a unit or has no effect.

Consistency
  A transaction takes the database from one valid state to another valid state.

Isolation
  Concurrent transactions behave as if they were controlled by some serial order.

Durability
  Once a transaction commits, its effect survives failures and recovery.
```

Most engineers learn the four words early. They are usually explained with examples: bank transfers, integrity constraints, concurrent transactions, crashes, logs, commits, and recovery.

Those examples are useful. But they leave a deeper question open:

```text
What kind of structure is ACID preserving?
```

When we relax one of the properties, what exactly is lost? When we keep one property and drop another, what remains true? Are the four properties one package, or are they different axes of structure?

I wanted to answer that question in a small formal model. So I tried to write the model in Lean.

The result was not a proof that real database systems are correct. It was something more modest, and more useful:

```text
Lean forced the boundary of each claim to become explicit.
```

In one case, it even showed that my definition was too weak because the theorem I wanted became trivial.

The most interesting moment was not when Lean proved something.

It was when Lean proved something too easily.

That is the part worth sharing.

## A Minimal Model

Start with the smallest model that still has something architectural in it.

There is a state space `S`. There are transactions. Each transaction acts on the state. There is also an invariant, a predicate that says which states are valid.

The snippets below are simplified Lean-shaped pseudocode. They are meant to show the shape of the model, not to be copied as a complete Lean file.

```lean
abbrev Endo (S : Type u) := S -> S

structure Model (S : Type u) where
  Txn   : Type v
  apply : Txn -> Endo S
  inv   : S -> Prop
```

This is intentionally abstract.

`S` might be a relational database state. It might be an event-sourced aggregate. It might be a key-value store, an in-memory domain model, or a deliberately simplified toy system.

The point is not to model every detail of a database. The point is to ask what can already be said if we only know this:

```text
transaction = operation on state
invariant   = property we want valid states to preserve
```

This small model already gives a useful reading of ACID.

## Histories Are Composition

Transactions rarely appear alone. They appear in histories.

A history is a list of transactions. Replaying a history means composing the corresponding state transformations.

```lean
def Model.replay (M : Model S) : List M.Txn -> Endo S
  | []      => id
  | t :: hs => fun s => M.replay hs (M.apply t s)
```

The empty history is the identity function. A non-empty history applies the first transaction, then replays the rest.

The important lemma is that replaying appended histories corresponds to composing their replays:

```lean
theorem replay_append
    (h1 h2 : List M.Txn) :
    M.replay (h1 ++ h2) = fun s => M.replay h2 (M.replay h1 s)
```

In plain English:

```text
append histories
  corresponds to
compose state transformations
```

This is already algebraic. The list of transactions has a monoid structure under append. State endomorphisms have a monoid structure under composition. Replay connects the two.

This is the first useful reframing:

```text
a transaction log is not just a list;
it is a way to build larger state transformations from smaller ones.
```

## Consistency Is Invariant Preservation

The easiest ACID property to read in this model is consistency: a transaction should take a valid state to another valid state.

```lean
def Consistency (M : Model S) : Prop :=
  forall t : M.Txn, forall s : S,
    M.inv s -> M.inv (M.apply t s)
```

This is invariant preservation. The set of valid states is closed under every transaction.

```text
valid state
  -- transaction -->
valid state
```

Once written this way, a small theorem becomes immediate:

```lean
theorem consistency_comp
    (hC : Consistency M)
    (t1 t2 : M.Txn)
    (s : S)
    (hs : M.inv s) :
    M.inv (M.apply t2 (M.apply t1 s))
```

If `t1` preserves the invariant and `t2` preserves the invariant, then their composition preserves the invariant.

The same idea extends from two transactions to any history:

```lean
theorem consistency_replay
    (hC : Consistency M) :
    forall h : List M.Txn, forall s : S,
      M.inv s -> M.inv (M.replay h s)
```

This is the cleanest part of the story. Consistency is simply:

```text
the invariant survives every selected operation.
```

That sentence is also the bridge to software architecture, but we will come back to that at the end.

## An Algebraic Shadow of Atomicity

Atomicity is trickier.

The textbook explanation says that a transaction happens all at once or not at all. There should be no externally visible half-transaction.

In a pure state-transition model, one algebraic approximation is closure under composition:

```lean
def Atomicity (M : Model S) : Prop :=
  forall t1 t2 : M.Txn,
    exists t3 : M.Txn,
      M.apply t3 = fun s => M.apply t2 (M.apply t1 s)
```

This says that if two transactions are executed in sequence, the combined effect can be represented as one transaction.

```text
transaction followed by transaction
  can be treated as
one transaction
```

That is a useful shadow of atomicity. It captures the idea that a compound effect can be packaged as one selected operation.

But it is not the whole database meaning of atomicity.

It does not model abort, rollback, partial execution under failure, write-ahead logging, recovery protocols, or the machinery that makes all-or-nothing behavior real.

So this definition must carry a theorem boundary:

```text
This is algebraic atomicity as closure of selected operations.
It is not a full crash/failure semantics for transactions.
```

This boundary prevents a small theorem from being advertised as a larger theorem.

## Isolation as Commutation, Also With a Warning

Isolation is also subtle.

A common intuition is that concurrent transactions should behave as if they had run one at a time.

One strong algebraic approximation is commutation:

```lean
def Isolation (M : Model S) : Prop :=
  forall t1 t2 : M.Txn, forall s : S,
    M.inv s ->
      M.apply t2 (M.apply t1 s)
        =
      M.apply t1 (M.apply t2 s)
```

This says that on valid states, swapping the order of two transactions does not change the result.

```text
t1 then t2
  =
t2 then t1
```

If the result is the same either way, then the order is not observable at the level of final state.

This is mathematically clean, but deliberately strong.

Real isolation levels are more nuanced. Read Committed, Repeatable Read, Snapshot Isolation, Serializable, and the phenomena studied in transaction theory are not all captured by this single predicate.

So again, the theorem boundary matters:

```text
This definition captures a strong commutation-style isolation property.
It is not a taxonomy of real-world isolation levels.
```

The formal model is valuable because it makes the approximation visible. Without it, it is easy to slide from "this resembles isolation" to "this is isolation."

Lean does not let that slide happen quietly.

## Durability Found a Bad Definition

Durability was the most interesting part.

My first attempt was to define durability as monotonicity of history. If one history is a prefix of another, then the longer history should replay as the shorter history followed by some suffix.

In pseudocode:

```lean
def Durability (M : Model S) : Prop :=
  forall h1 h2 : List M.Txn,
    Prefix h1 h2 ->
      exists k : List M.Txn,
        M.replay h2 = fun s => M.replay k (M.replay h1 s)
```

This sounds plausible.

If `h1` is already committed and `h2` extends it, then `h2` should contain `h1` as a stable prefix. The past should not be rewritten.

But then something happened:

```text
the theorem was provable with no real assumptions.
```

That was the moment the model started to teach me something.

Why?

Because if `h1` is a prefix of `h2`, then by definition there is some suffix `k` such that:

```text
h2 = h1 ++ k
```

And `replay_append` already gives:

```text
replay (h1 ++ k) = replay k . replay h1
```

So the durability theorem follows almost for free.

At first, that feels like success. A theorem was proved. The code type-checked. The definition seemed to behave.

But it is actually a warning.

The definition was too weak to capture what durability is supposed to mean.

If a property that should depend on storage, crashes, and recovery can be proved from list concatenation alone, then the property is not talking about storage, crashes, or recovery.

The real concern of durability is not just that a mathematical list has a prefix. It is that committed effects survive crashes, storage failures, recovery, and restart.

A pure state-transition model does not contain storage.

It does not contain crashes.

It does not contain a recovery function.

So it cannot express the full property.

To talk about durability seriously, the model needs another layer:

```text
volatile state
persistent state
write
crash
recover
```

Only after adding that layer can we ask for a non-trivial law such as:

```text
recover after write preserves the committed effect
```

This was the most valuable lesson from the exercise.

Lean did not merely help prove a theorem. It helped detect that a proposed definition was too weak to express the intended claim.

In other words:

```text
Lean did not reject the definition.
It accepted it so easily that the definition became suspicious.
```

## What Lean Actually Gave Me

The most valuable result was not:

```text
ACID has been proved correct.
```

That would be far too strong.

The valuable result was:

```text
Each claim now has a visible model boundary.
```

Within a pure state-transition model, consistency as invariant preservation is clean.

Atomicity as closure is useful, but incomplete.

Isolation as commutation is clear, but strong.

Durability cannot be fully expressed without modeling persistence and recovery.

That is the real payoff of formalization.

It forces the question:

```text
What exactly did we model?
What exactly did we prove?
What did we not model?
What must remain a non-conclusion?
```

For software engineering, this discipline matters more than the notation.

Many architecture discussions fail because claims move between levels without being noticed.

For example:

```text
"We use Event Sourcing"
  quietly becomes
"we can always replay and recover correctly."

"We use Clean Architecture"
  quietly becomes
"dependencies cannot violate our boundary."

"We have tests"
  quietly becomes
"the behavior is preserved."
```

Each of those moves may be valid under additional assumptions. But the assumptions need to be stated.

Formalization is a way to make those assumptions visible.

## From ACID to Architecture

The ACID example suggests a more general way to read software design.

A design rule is not just a slogan.

It is a claim that some operation should preserve some invariant.

In ACID, the operations were transactions. One invariant was database consistency.

In software architecture, the same pattern appears in a less obvious form.

```text
ApplicationService -> SqlPaymentRepository
```

Suppose the intended architecture says that application code should depend on a payment port, not on the SQL implementation directly.

Then the issue is not simply that the design "looks bad."

There is an invariant:

```text
application logic depends on declared abstractions,
not on infrastructure details directly
```

There is an operation:

```text
a feature addition or refactoring introduced a new dependency edge
```

And there is a witness:

```text
the concrete edge ApplicationService -> SqlPaymentRepository
```

That is the same shape as the ACID model:

```text
operation acts on a structure
invariant is expected to survive
failure should have a concrete witness
claim only holds inside a stated boundary
```

This line of thought eventually became one of the entry points into what I now call Algebraic Architecture Theory, or AAT.

AAT is my attempt to read software architecture through a small set of recurring objects:

```text
operations
invariants
witnesses
signatures
boundaries
```

The important word is not "algebra" for its own sake. The important word is **invariant**.

When we say a design is good, we should be able to ask:

```text
Which invariant is being preserved?
By which operation?
Under which observation boundary?
If it fails, what is the witness?
```

For example:

```text
Layered Architecture
  preserves dependency direction and acyclicity.

DIP
  preserves abstraction boundaries through projection.

LSP
  preserves selected observations under substitution.

Event Sourcing
  preserves replay laws.

Saga
  preserves weak recovery or compensation laws.

Circuit Breaker
  preserves failure locality under runtime interaction.
```

When an invariant fails, we should not merely say "the design is bad."

We should ask for a witness:

```text
a cycle
a forbidden dependency edge
an abstraction leak
an observation mismatch
a failed compensation case
a non-commuting semantic diagram
a runtime exposure path
```

Those witnesses can then be summarized in an Architecture Signature.

The signature is not a single quality score. It is a multi-axis diagnosis.

One change might reduce cycles while increasing runtime exposure. Another might improve abstraction boundaries while leaving compensation laws untested. A single number would hide that structure.

The lesson from ACID carries over:

```text
do not ask whether the architecture is "good" in general;
ask which invariants are preserved, which witnesses remain,
and which axes were not measured.
```

In that sense, formalization is not only a tool for proving.

It is a tool for discovering what your words were secretly assuming.

## Conclusion

ACID was not the destination.

It was a small, familiar example showing that software design can be read as invariant preservation under operations, with explicit witnesses when preservation fails.

Lean did not turn a simplified model into a real database.

It did something more useful:

```text
it made the boundary of the claim impossible to ignore.
```

That is the habit I want to bring from formal methods into everyday architecture work.

Not every design discussion needs a proof assistant.

But every serious design claim benefits from the same discipline:

```text
name the operation;
name the invariant;
name the witness;
name the boundary.
```

The working research repository for this project is here:

https://github.com/iroha1203/AlgebraicArchitectureTheoryV2
