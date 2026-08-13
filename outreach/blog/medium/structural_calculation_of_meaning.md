# Buildings Calculate Forces. Software Must Calculate Meaning.

*Design principles gave us readable software. Where is its structural engineering?*

I was raised on the idea that software development is like constructing a building.
Lay a solid foundation.
Design before you build.
Bolt on features without thinking, and you end up with a rambling old inn, extended wing by wing.
Let a spec change reach the foundations, and you are in for a major rebuild.
All of it is true.
But I had a question.
Buildings have structural engineering. Loads, stresses, material properties, safety factors — all calculated mathematically.
Software architecture, on the other hand, has little theory for the structural engineering of the whole.

## The Architect's Design, and the Age of AI

I have worked as a software engineer for more than ten years, and I have learned a great deal about architecture along the way.
MVC, MVP, Clean Architecture, design patterns, DDD.
These matter. But in the world of buildings, I suspect they correspond to the architect's design — not the engineer's structural calculations.

Give things clear names.
Separate responsibilities.
Divide into layers.
Keep dependencies pointing one way.
Use known patterns.

These exist to help humans understand.
But being readable and being semantically unbreakable are different things.
No one claims a building will stand because its design is magnificent.
So how has software been doing its structural engineering?
Human review carried the load — knowledge and experience.
If the architect's design is easy to understand, a human can read through it and run the "structural calculation of meaning" in their head.
Design principles built around human comprehension worked because human review could keep up.

Now that AI agents write most of the code, human review is falling behind code generated at breakneck speed.
What software architecture needs is a theory that can do the structural calculation of meaning.

## The Category-Theoretic Approach

As a naive approach, consider category theory.
It already does real work in the denotational semantics of programs.
Take components as objects and dependencies as morphisms, and the structure of an architecture can be seen as a category.
At first glance it looked promising. But there were problems — several of them.

First, **it is not obvious what the objects and morphisms should be**.

- classes
- services
- APIs
- permissions
- data
- semantic roles

The unit changes depending on what you want to observe.

Second, **knowing the structure does not mean knowing the meaning**.

A morphism `BillingService -> User` does not tell you whether User is the paying customer, the authenticated identity, or simply a member.

Third, **global correctness does not follow from local correctness**.

Even if meaning holds in each part, it does not follow that the parts glue into one meaning for the whole.

Fourth, architecture has not only structure but **constraints**:

- authority
- contract
- state transition
- semantic consistency
- relation

Category theory did not fail. **Category theory alone could not reach what I wanted.**
Category theory is, in the end, a language: it can describe an architecture, but it cannot solve one.

## The Danger of Building a Theory from Scratch

Since category theory alone was not enough, I tried building a theory of my own.

I gave it a name.
AAT — Algebraic Architecture Theory.

It was a precarious venture.
First, the cost is enormous.
Definitions, theorems, proofs — you must invent everything yourself.
Homemade vocabulary multiplies on its own.
To explain anything, you must first ask people to memorize a pile of private words.

And even if a measurement tool built on it runs, you cannot tell whether it runs on

- luck
- mathematics
- or metaphor.

It might produce some kind of analysis. But the danger is not that it fails to run. The danger is that it runs anyway.
Without theoretical grounding, when it hits, you cannot tell a lucky hit from a right answer.

A homemade theory takes on mathematical debt and linguistic debt.
I decided not to borrow what I could not repay.

## Onto Grothendieck's Shoulders

Category theory describes, but falls short.
A homemade theory cannot repay its debts.

What, then, to do?

Through trial and error, AAT had found two concepts: Atom and Law.

An Atom is a primitive architectural fact — an atom of structure that can be found by observing source code.
A Law is an abstraction of a specification or a design pattern, taking the form of an algebraic constraint acting on Atoms.

In the homemade days, what sat on top of Atom and Law was a mysterious invariant called the Architecture Signature.

The theory back then was so incoherent I would rather not remember it. But there was one intuition.
That to describe architecture, geometry might be the right fit.

So I made up my mind.
Climb onto the shoulders of Alexander Grothendieck.
Into the world of algebraic geometry.

## Raising the Water Level of Abstraction

Algebraic geometry is a strange mathematics.
It calls itself "geometry," yet it does not demand classical points, lines, or shapes.
It was born to solve equations. But after Grothendieck, algebraic geometry builds spaces out of the equations themselves — and solving them became just one application.

What is geometry?
Geometry is not merely the study of shapes.
**It is a way of treating an object as a space and studying its structure, its invariants, and the relation between its local and global behavior.**

What matters is not whether software resembles a shape.
**What matters is whether the meaning of software has enough structure to be studied as a space.**

Perhaps the Atom and Law that AAT already had could connect it to algebraic geometry.
Make the connection, and you inherit an arsenal built up over more than a century.

Sheaves, cohomology, schemes, moduli, stacks.

In the spirit of the Rising Sea, you raise the water level of abstraction — and instead of cracking problems one by one, a single theory dissolves them naturally.

### Software Architecture Is a Vast System of Equations

It is closer to the truth to see an architecture not as an "arrangement of parts" but as a **vast system of semantic constraints**.
Take a single concept like Order:

- Who may create one?
- What becomes permitted when payment succeeds?
- Can Cancelled and Shipped coexist?
- How must Inventory and Order state stay consistent?
- Does User mean the same thing in every service?

Many constraints tangle around a single concept.

In the code they are scattered across separate files and services; semantically, they form one system of equations.

A good architecture, then, can be read not as adherence to a particular pattern, but as **the existence of a realization of meaning that satisfies all the required Laws at once**.
MVC and Clean Architecture are not the equations themselves; they can be reread as **design techniques for arranging the equations so that they are easier to solve**.

And so the questions AAT asks become:

- Does a solution exist?
- Is the solution unique?
- What kind of space do the solutions form?
- Do local solutions glue into a global one?

### Geometry Appears

Algebraic geometry does not merely solve equations. **It sees the set of all solutions as a space.**
So a flow arises naturally:

Architecture Laws
↓
space of semantic realizations

This solution space — precisely this — is Semantic Geometry.

The question widens from

Does a solution exist?

to

How is the space of solutions shaped?

### Rereading the SAGA Theorem

The SAGA theorem, AAT's first main theorem, is not the end of the road called fault detection.
It was the first result to show that nontrivial mathematical structure lies between local meaning and global meaning.
The first theorem to ask whether local solutions of meaning glue into a global one.

Using cohomology raised a question: cohomology of what space?
From there the road leads to schemes, representability, moduli.

SAGA
↓
Semantic Geometry

is not a change of theme. It is a natural extension.

### AAT, Redefined

AAT can be understood as
a geometric study of software architecture and its meaning.

Faults are only one phenomenon.
The real objects of study are:

- existence of meaning
- non-uniqueness
- gluing
- invariance
- deformation
- moduli
- representability
- intrinsic semantic space

**A new research area of computer science that re-sees software architecture as geometry.**

AAT becomes an attempt to reconceive software architecture as a geometry of meaning.
What I found is a space that has not yet been properly surveyed.

## Closing

By standing on Grothendieck's shoulders, AAT at last gained a ship that could sail far.
The water level of abstraction rose, individual problems sank beneath it, and the peak still to be climbed came into view.

The road is still long.
There is a mountain of work to do.

But if we can reach the summit of schemes, then, for the first time, a "structural design of meaning" for architecture may be born.

Software architecture is a vast system of equations; its solutions form a space; and a geometry of meaning rises.

Semantic Geometry of Architecture.

The voyage has just begun.
