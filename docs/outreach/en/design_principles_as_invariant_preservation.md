---
title: "Design Principles as Invariant Preservation"
published: false
description: "A practical way to read architecture advice: ask what operation is being performed, what invariant should survive, what failure would look like, and where the claim stops."
tags: architecture, softwareengineering, computerscience, design
---

> **TL;DR**
>
> A design principle is not just a label.
>
> It is a claim that some class of operations should preserve some class of invariants.
>
> If the invariant fails, we should be able to point to a witness.
>
> If the claim depends on a selected graph, policy, observation, or failure model, we should name that boundary.

Architecture advice is useful, but it is easy to use as a label instead of a diagnosis.

In reviews, we often hear sentences like these:

```text
This violates Clean Architecture.
This is not SOLID.
This should be Event Sourcing.
This needs a Circuit Breaker.
```

Sometimes those statements are right.

But they are not yet precise.

They do not say what changed, what was supposed to remain true, what evidence shows the failure, or what assumptions the claim depends on.

The question I want to ask is:

```text
What does this design principle preserve?
```

That question is the smallest useful entry point into the way I think about Algebraic Architecture Theory (AAT).

The name matters less than the discipline. When we make a design claim, we should be able to name four things:

```text
operation
invariant
witness
boundary
```

This article is about that vocabulary.

## The Four Words

An **operation** is a change applied to the architecture.

It might be a feature addition, refactoring, interface extraction, layer split, migration, repair, runtime protection, or protocol change.

An **invariant** is a property expected to survive the operation.

It might be dependency direction, boundary policy, abstraction soundness, substitutability, replay behavior, compensation behavior, or failure locality.

A **witness** is concrete evidence that preservation failed.

It might be a forbidden dependency edge, a cycle, an abstraction leak, an observation mismatch, a failed compensation path, or a runtime exposure path.

A **boundary** is the scope in which the claim is meaningful.

It might be a selected dependency graph, a declared port policy, a set of observations, a finite event schema, or an explicit failure model.

The point is simple:

```text
Do not ask only whether a design principle was used.
Ask what it preserved.
```

## A Small Example

Suppose we have a payment feature.

The intended dependency structure is:

```text
ApplicationService -> PaymentPort
SqlPaymentRepository -> PaymentPort
```

The application service talks to a declared port. The SQL repository implements that port.

Now a feature change introduces this direct dependency:

```text
ApplicationService -> SqlPaymentRepository
```

People might say:

```text
This violates Clean Architecture.
This violates DIP.
This couples application logic to infrastructure.
```

All of those may be reasonable descriptions.

But the more useful diagnosis is:

```text
operation:
  a feature addition introduced a new dependency edge

invariant:
  application logic depends on declared abstractions,
  not on infrastructure details directly

witness:
  ApplicationService -> SqlPaymentRepository

boundary:
  selected dependency graph and declared port policy
```

The violation is not a mood.

It is an edge.

That edge is a witness that a selected boundary invariant failed.

This is the shift I care about. Design review becomes sharper when a principle is translated into a claim about operations and invariants.

## Clean Architecture Preserves Boundary Invariants

Clean Architecture is often explained with circles, layers, arrows, and dependencies pointing inward.

Those diagrams are useful. But the important object is not the diagram itself.

The important object is the invariant the diagram is trying to express.

In a simplified dependency graph, one such invariant might be:

```text
application code does not depend directly on infrastructure details
```

A change operation adds or removes edges from that graph.

If the operation adds:

```text
ApplicationService -> SqlPaymentRepository
```

then the invariant fails.

The witness is the forbidden edge.

This way of reading Clean Architecture avoids two common mistakes.

First, it avoids treating the pattern name as the diagnosis.

Saying "this violates Clean Architecture" is less useful than saying which edge violates which boundary rule.

Second, it avoids overclaiming.

A selected dependency graph and port policy can show a boundary violation. It does not automatically prove that all runtime behavior, framework coupling, ownership boundaries, or effect leakage have been captured.

That is the boundary of the claim.

## SOLID Is Local

SOLID principles are useful, but they do not all preserve the same kind of structure.

They are mostly about local contracts, responsibilities, abstractions, and substitutability.

For example, DIP can be read as a projection-shaped invariant:

```text
concrete dependencies should factor through declared abstractions
```

A witness of failure might be a concrete dependency that bypasses the abstraction.

LSP can be read as an observation-shaped invariant:

```text
implementations exposed through the same abstraction preserve selected observations
```

A witness of failure might be two implementations that should be substitutable but produce different observed behavior in a selected context.

SRP can be read as a responsibility-boundary invariant:

```text
selected responsibilities remain coherent under expected changes
```

A witness of failure might be a change reason that crosses the chosen responsibility boundary.

None of these readings says that the natural-language meaning of SOLID has been completely formalized.

That would be too strong.

The point is narrower: when a SOLID-style claim matters in a review, we should say which local invariant it is supposed to preserve.

This also explains why SOLID does not automatically prove the global architecture is clean.

Local contracts are not the same thing as global dependency structure.

You can have well-named classes, reasonable interfaces, and local substitutability, while still having cycles, forbidden layer crossings, or runtime propagation paths.

Those are different invariants.

## State Transition Patterns Preserve Different Laws

Not every design principle is about dependencies.

Event Sourcing, Saga, and related patterns are better read as state-transition claims.

For Event Sourcing, the operation might be:

```text
append an event
replay an event history
project events into a read model
```

The invariant might be:

```text
replay gives a stable interpretation of history
projection agrees with the selected event semantics
```

A witness of failure might be:

```text
the same event history produces inconsistent projection results
```

The boundary matters. The claim depends on the selected event schema, projection, replay semantics, and migration assumptions.

Saga has a different shape.

The operation might be:

```text
execute a step
observe a failure
run compensation
```

The invariant might be weak recovery under a selected failure model.

A witness of failure might be a failure path for which no valid compensation exists.

Again, this does not say that every real Saga implementation is correct. It says that a Saga-style design claim should name the recovery law it expects to preserve.

## Runtime Protection Has Its Own Invariants

Circuit Breaker is different again.

It is not primarily about static dependency direction or replay semantics.

It is about runtime interaction and failure locality.

The operation might be:

```text
protect a runtime call
isolate a dependency
stop retry amplification
```

The invariant might be:

```text
failure does not propagate beyond a selected runtime boundary
```

A witness of failure might be a runtime exposure path that crosses the boundary.

The boundary is crucial: selected runtime graph, telemetry coverage, timeout policy, retry policy, and failure model.

This is why design principles should not be flattened into one list of good ideas.

They preserve different things.

## A Review Checklist

When someone makes a design claim, try asking these questions:

```text
1. What operation are we discussing?
2. What invariant is supposed to be preserved?
3. What would count as a witness of failure?
4. What boundary makes the claim meaningful?
5. What is not being claimed?
```

These questions are useful because they separate diagnosis from vocabulary.

"This is not Clean Architecture" becomes:

```text
this operation added a forbidden dependency edge
under this boundary policy
```

"This is not LSP" becomes:

```text
these two implementations disagree under this selected observation
```

"This needs a Circuit Breaker" becomes:

```text
this runtime path allows failure to propagate beyond this boundary
```

The design principle is still useful.

But now it points to a specific invariant and a possible witness.

## Where AAT Enters

I use Algebraic Architecture Theory (AAT) as a name for this broader lens.

The compact version is:

```text
architecture
  = objects
  + operations
  + invariants
  + witnesses
  + boundaries
```

This is not meant to turn every architecture discussion into formal mathematics.

It is meant to make informal design claims more inspectable.

The important move is not to ask:

```text
Did we use the design principle?
```

The important move is to ask:

```text
What did the principle claim to preserve?
```

Different invariants can fail in different ways, and each failure should have a witness.

That is why architecture should not be reduced to a single score.

## Conclusion

Design principles become sharper when we stop treating them as labels.

Clean Architecture, SOLID, Event Sourcing, Saga, and Circuit Breaker are not the same kind of advice.

They preserve different invariants under different operations and boundaries.

A good review should not stop at:

```text
this follows the pattern
```

It should ask:

```text
what changed
what was supposed to remain true
what would count as failure
what the claim does not cover
```

A design principle is useful only when it tells us what must remain true after change.

The working Lean repository for this line of thought is here:

https://github.com/iroha1203/AlgebraicArchitectureTheoryV2

