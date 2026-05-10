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
> Durability exposed that my model had no persistence boundary.
>
> The result was not a proof that databases are correct.
> It was a reminder that every design claim depends on what the model can actually see.

The suspicious part was not that Lean failed to prove durability.

The suspicious part was that Lean proved it with almost no assumptions.

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

Most engineers learn these words through examples: bank transfers, constraints, concurrent transactions, crashes, logs, commits, and recovery.

But I wanted to ask a slightly different question:

```text
What kind of structure is ACID preserving?
```

So I tried to write a small ACID-like model in Lean 4.

The result was not a proof that real databases are correct.

That is the part worth sharing.

## A Minimal Model

Start with the smallest model that still has something architectural in it.

There is a state space `S`. There are transactions. Each transaction acts on the state. There is also an invariant, a predicate that says which states are valid.

This is not a formalization of real database ACID.

It is a deliberately lossy projection: keep the state-transformer shape, and drop many operational details.

In simplified Lean-shaped notation, the model looks like this:

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

This small model already gives a useful reading of some ACID-shaped claims.

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

In less mathematical terms, replay is the bridge between a log and the effect that log has on the system.

This is the first useful reframing:

```text
a transaction log is not just a list;
it is a way to build larger state transformations from smaller ones.
```

## Consistency as Invariant Preservation

For this model, the part of ACID consistency we keep is invariant preservation: a transaction should take a valid state to another valid state.

```lean
def PreservesInvariant (M : Model S) : Prop :=
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
theorem preservesInvariant_comp
    (hC : PreservesInvariant M)
    (t1 t2 : M.Txn)
    (s : S)
    (hs : M.inv s) :
    M.inv (M.apply t2 (M.apply t1 s))
```

If `t1` preserves the invariant and `t2` preserves the invariant, then their composition preserves the invariant.

The same idea extends from two transactions to any history:

```lean
theorem preservesInvariant_replay
    (hC : PreservesInvariant M) :
    forall h : List M.Txn, forall s : S,
      M.inv s -> M.inv (M.replay h s)
```

This is the cleanest part of the story. In this projection, consistency becomes:

```text
the invariant survives every selected operation.
```

That sentence is also the bridge to software architecture, but we will come back to that at the end.

## An Algebraic Shadow of Atomicity

Atomicity is trickier.

In this model, I cannot express all-or-nothing execution.

There is no partial execution, no abort, no crash, and no visibility boundary.

The closest algebraic property I can write is closure under sequencing:

```lean
def ClosedUnderSequence (M : Model S) : Prop :=
  forall t1 t2 : M.Txn,
    exists t3 : M.Txn,
      M.apply t3 = fun s => M.apply t2 (M.apply t1 s)
```

This says that if two selected operations are executed in sequence, their combined effect can be represented as one selected operation.

```text
transaction followed by transaction
  can be treated as
one transaction
```

That is not database atomicity. It is only an atomicity-shaped shadow.

So this definition needs a boundary:

```text
This is algebraic atomicity as closure of selected operations.
It is not a full crash/failure semantics for transactions.
```

This boundary prevents a small theorem from being advertised as a larger theorem.

## Isolation as Commutation, Also With a Warning

Isolation is also subtle.

A common intuition is that concurrent transactions should behave as if they had run one at a time. In database terms, serializability asks whether a concurrent execution is equivalent to some serial order.

Commutation asks for something stronger: the two serial orders are indistinguishable at the level of final state.

```lean
def CommutesOnValidStates (M : Model S) : Prop :=
  forall t1 t2 : M.Txn, forall s : S,
    M.inv s ->
      M.apply t2 (M.apply t1 s)
        =
      M.apply t1 (M.apply t2 s)
```

This says that on valid states, swapping the order of two selected operations does not change the result.

```text
t1 then t2
  =
t2 then t1
```

This is mathematically clean, but it is stronger than serializability. It removes order from the observable final state rather than merely finding some serial order.

So this definition also needs a boundary:

```text
This definition captures a strong commutation-style isolation property.
It is not a taxonomy of real-world isolation levels.
```

The formal model is valuable because it makes the approximation visible. Without it, it is easy to slide from "this resembles isolation" to "this is isolation."

Lean does not let that slide happen quietly.

## Durability Exposed a Missing Boundary

Durability was the most interesting part.

My first attempt was to define durability as monotonicity of history. If one history is a prefix of another, then the longer history should replay as the shorter history followed by some suffix.

In pseudocode:

```lean
def WrongDurabilityAttempt (M : Model S) : Prop :=
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

So the attempted durability theorem follows almost for free.

At first, that feels like success: the theorem was proved, the code type-checked, and the definition seemed to behave.

But that was the warning.

This was the bug: I had not defined durability.

I had defined a replay decomposition property of append-only histories.

If a property that should depend on storage, crashes, and recovery can be proved from list concatenation alone, then the property is not talking about storage, crashes, or recovery.

Durability is not just "the log has a prefix." It is a recovery guarantee under an explicit failure model.

Committed effects should survive the crashes and recoveries the system promises to handle.

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

The result was not:

```text
ACID has been proved correct.
```

That would be far too strong.

What Lean gave me was a way to notice when a claim had silently moved outside its model.

```text
Within a pure state-transition model:

Consistency-shaped claims can be read as invariant preservation.
The atomicity-shaped fragment becomes closure under sequencing.
The isolation-shaped fragment becomes commutation on valid states.
Durability cannot be expressed without persistence, recovery, and a fault model.
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
```

Here, the "state" is not a database state. It is a dependency graph.

The operation is not a transaction. It is a code change that adds or removes edges.

The invariant is not a database constraint. It is an architectural rule about allowed dependencies.

The witness is not a bad row. It is a forbidden edge.

I use the name Algebraic Architecture Theory (AAT) for this broader lens, but the name matters less than the discipline: state the operation, the invariant, the witness, and the boundary.

The important word is not "algebra" for its own sake. The important word is **invariant**.

When we say a design is good, we should be able to ask:

```text
Which invariant is being preserved?
By which operation?
Under which observation boundary?
If it fails, what is the witness?
```

The same question can be asked for dependency direction, abstraction boundaries, substitutability, replay laws, compensation laws, and failure locality.

When an invariant fails, we should not merely say "the design is bad." We should identify the concrete witness: a forbidden dependency edge, a cycle, an abstraction leak, an observation mismatch, or a failed compensation case.

Different invariants can fail in different ways, and each failure should have a witness.

The lesson from ACID carries over:

```text
do not ask whether the architecture is "good" in general;
ask which invariants are preserved, which witnesses remain,
and which axes were not measured.
```

## Conclusion

ACID was not the destination.

It was a small, familiar example showing that software design can be read as invariant preservation under operations, with explicit witnesses when preservation fails.

Lean did not turn a simplified model into a real database.

It did something more useful.

It showed that a definition can be wrong not because Lean rejects it, but because Lean accepts it for the wrong reason.

In that sense, formalization is not only a tool for proving.

It is a tool for discovering what your words were secretly assuming.

That is the habit I want to bring from formal methods into everyday architecture work.

Not every design discussion needs a proof assistant.

But every serious design claim benefits from the same discipline:

```text
name the operation;
name the invariant;
name the witness;
name the boundary.
```

The working Lean repository for this line of thought is here:

https://github.com/iroha1203/AlgebraicArchitectureTheoryV2
