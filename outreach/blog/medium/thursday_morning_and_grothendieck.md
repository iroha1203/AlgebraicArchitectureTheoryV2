# Thursday Morning and Grothendieck

## Thursday morning, an ER diagram with more than twenty tables

When I saw the design document and the ER diagram my AI agent had delivered, I held my head in my hands.
Several tables with nearly identical names, wired together in a tangle of relations — spaghetti.
What does this table do? How is it different from that one?
I asked the agent question after question.
What I learned: the original requirements were genuinely complex.
To satisfy them, the agent had created tables with subtly different roles inside the same domain.
And rounds of adversarial review had piled intricate constraints and tests on top.

I could see the AI's point.
To satisfy those requirements completely, you really do need a number of "gimmicks" — snapshots for restoring state, staging tables to protect data on failure — and then check constraints and trigger functions to guarantee them.
But locally optimal is one thing. What about globally?
A schema where twenty-plus tables tangle together, with trigger functions planted here and there, is plainly hard for a human being to understand.
The day a spec change or a new feature arrives, it will not be a pretty sight.

I gave the agent the following instructions.

- Redesign around event sourcing and CQRS.
- Design the events to form a free monoid — and, where possible, an abelian group.

Event sourcing is a scheme that records the "events" occurring in a system as the source of truth.
CQRS separates Commands (operations that add, change, or delete data) from Queries (data retrieval), managing them as distinct models.
Combining the two, you get an architecture where events are recorded in tables as command history, and query tables are generated from the events.
In this architecture, as long as the events are recorded correctly, the query side can add as many tables as the requirements call for, and rollbacks and historical aggregation can be handled flexibly.

"A free monoid, an abelian group if possible" means making the events — the foundation of everything — data with good properties.
If the application of events forms a genuine abelian group, you get:

- Commutativity: reorder the events, and the result stays the same.
- Inverses: any event can be canceled by issuing its inverse event.

With these properties, events become dramatically easier to work with.
Of course, among the things we ordinarily program with, only something like the integers actually forms an abelian group, so perfection is out of reach — but by decomposing large events into small operations, you can get surprisingly close.

And so the schema was rewritten: the twenty-plus tables were reorganized into two event tables and ten query tables.

## Interlude

How wonderful it would be if every event could be an abelian group.
In reality, once logic gets involved — events that depend on state, deletions and updates, saturation and clamping — it becomes hard.

For deletions and updates, mathematics has a universal construction that forcibly adjoins formal inverses to a commutative monoid, turning it into a group.
Its name: the Grothendieck group.

## Mathematics in the age of AI

Right now, in the world of mathematics, AI is solving open problems one after another.
Famous conjectures that stood unresolved for decades are falling — a counterexample here, a proof there — and it feels as if the singularity is just around the corner.
Deep reasoning, broad knowledge, and a persistence that never gives up as long as the tokens keep burning.
An "inflation of intelligence" unlike anything in human history has begun.

But this may be local optimization.

There are two kinds of work in mathematics.
Solving individual problems — and infrastructure work, building an entire field from the ground up.
Alexander Grothendieck remade algebraic geometry, from "the study of the zeros of polynomials" into a vast theoretical edifice treating rings, categories, and cohomology in a unified way.
What is a point?
What is a space?
What is a mathematically natural object?
By rewriting a whole field from its footings, individual problems became local solutions, and a scaffold appeared for solving larger ones.

This is global work.

To see the common essence hidden in individual problems, to pose the question, to make the natural definitions, to raise the water level of abstraction, to build a new tower on the mathematical landscape.
For a while yet, I suspect, this kind of work will remain a human's role.

## The idea of AAT

This is also why I work on AAT (Algebraic Architecture Theory).
AI may be able to produce optimal solutions to individual problems, but writing a software architecture that holds together as a whole is still difficult for it.

Software engineering does have a proven approach here: formal verification.
Formalize the specification before implementing, confirm that it is consistent, and only then move to implementation — TLA+ and Alloy are examples.
A useful approach, but it has weaknesses.
The implementation cost of formalizing up front.
The problem that every spec change or addition sends you back to redo the formalization.
And the problem of assurance: the implementation has to follow what was formalized.

In an era when AI agents write code at full speed, perhaps software engineering, too, needs a new field.

Take the code that already exists as the source of truth; abstract the implementation; turn the specification into equations.
Treat architecture as geometry, and analyze it with the weapons of algebraic geometry.
That is the idea of AAT.
The foundations are still being laid. But once the natural definitions at the base are established, the water level of abstraction will rise, individual problems will become local solutions, and we will be able to speak about software architecture in one unified theory.

If that day comes, episodes like that Thursday morning may become, at least, a little rarer.
