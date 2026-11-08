# ArchSig: A Tool That Asks Why, Not How

Formal methods, testing techniques, type checking: there are plenty of good ways to check software. If that is what you need, those are good places to start.

This article asks why rather than how. What makes it possible for software to satisfy a particular property? I am building a tool called ArchSig to investigate that question.

## Understanding why properties hold

I am developing **Algebraic Architecture Theory (AAT)** to study these questions mathematically. AAT represents facts about software, operations, and properties we want to preserve. It studies the conditions under which those properties hold and the relationships between parts and wholes.

ArchSig is a tool based on this theory. Given properties we want to preserve and facts observed in source code, it identifies candidate changes that satisfy the requirements and examines how those candidates relate to one another.

Finding one implementation that works leaves questions open. Which choices were essential? Could another choice work? If we cannot change a particular part, what becomes impossible? Comparing candidates gives us a way to investigate those questions.

## Asking why with ArchSig

We explored what ArchSig could tell us about why a design works through an experiment with Saleor, an e-commerce system.

We wanted to release funds left behind when a checkout never becomes an order. Release should occur only after more than six hours have passed since the last activity on the checkout and on every related transaction. Normal order processing must continue to work.

Checking elapsed time sounds simple. But an order can progress while the release process is waiting. A request to a payment service may also leave us uncertain about the outcome. Deciding whether to release funds requires information about orders and payments as well as time.

A **Law** expresses a property we want to preserve. It generalizes specifications, conventions, and rules. An **Atom** is a typed fact visible through that Law. “Typed” means we distinguish what the fact is about and what kind of fact it is, as well as its value.

For example, suppose checkout C has one related transaction T. Choose the Law “more than six hours must have passed since the last update to each,” and read the following facts as Atoms:

| Fact read as an Atom | Type and subject of the fact |
| --- | --- |
| Transaction T belongs to checkout C | Relationship between a transaction and a checkout |
| Checkout C was last updated at 11 a.m. | Checkout update time |
| Transaction T was last updated at 1 p.m. | Transaction update time |

At 6 p.m. that day, seven hours have passed since the checkout update, but only five since the transaction update. The time condition does not yet permit release. With no further updates, it becomes satisfied after 7 p.m., not at exactly 7 p.m.

The values “11 a.m.” and “1 p.m.” alone cannot tell us this. We also need to know what was updated and which transaction belongs to which checkout. The property we care about determines which facts we need to examine.

In the experiment, agents responsible for observation and design read the code and prepared the Atoms, Laws, and candidate changes, including alternatives such as row locking. ArchSig calculated which combinations satisfied the Laws, what information was sufficient for evaluation, and how local choices corresponded to whole designs. The solution counts below refer to those declared candidates and Laws.

## Why does a wider change scope admit a solution?

Suppose the release process checks that funds have not yet been used for an order. Immediately afterward, the order completes. If the release process acts on its stale decision, it can interfere with that order.

Preventing this race requires both sides to coordinate their decisions and updates. With row locking, they lock the same checkout row. With version checking, both participate in checking and advancing the version. Our candidate family did not include bridges between different protocols. We therefore expressed the requirement as a Law: the release, order, and payment processes use the same concurrency protocol.

We used ArchSig to find which parts had to be open to change to satisfy these Laws, and which design choices would remain.

First, we allowed changes only to the periodic job that checks the deadline and initiates release, called `task`. With order and payment processing fixed, no candidate satisfied the requirements.

Next, we also allowed changes to the payment processing code, called `payment`. There were still no solutions.

When we allowed changes to the boundary shared with order processing, eight solutions remained.

They differed in three choices:

| Design choice | Option 1 | Option 2 |
| --- | --- | --- |
| Coordinate orders, payments, and release | Lock the same checkout row | Check a version and commit a change only when it matches |
| Store release requests and outcomes | Extend the existing event journal | Use a dedicated record |
| Handle a checkout with unresolved funds | Retain it without deleting it | Save the information needed for recovery before deleting it |

Two options for each choice give $2\times2\times2=8$ combinations. Both “row lock, dedicated record, retain the checkout” and “version check, event journal, save recovery information and delete” survived. We chose the former for implementation simplicity and ease of handling recovery information. That was an engineering choice among the eight solutions.

The eight designs also shared requirements: use a common concurrency protocol, record the update time when changes are received, and hold off on retrying an uncertain request until evidence of its outcome is available. The experiment did not assume that the external service would process repeated requests exactly once.

**Some choices are fixed by the requirements. Others remain open while satisfying them. That remaining freedom appeared as eight designs.**

## Do the parts determine the whole?

Can we design each part separately and combine the results into a whole?

Call a design for one part a *local design*. In this candidate family, the checkout side chose a concurrency protocol and a deletion policy. The payment side chose a concurrency protocol and a storage representation. Each side had four valid local designs.

Pairing them freely would give sixteen combinations. But a checkout using row locks and a payment process using version checks would violate the shared-protocol Law.

Requiring agreement left four combinations using row locks and four using version checks. Each of those eight compatible pairs corresponded to exactly one whole design.

The result also showed how compatible choices for the parts determined the whole.

How do change scope, the information needed for a decision, and the relationship between parts and wholes connect? To answer that, we turn to the mathematics.

## The mathematics behind the answers

Why did solutions appear when we widened the scope of change? Why did local choices determine a whole design? Starting from the eight solutions, we can examine the shape imposed by the Laws and what can prevent a whole from existing.

### What does a Law constrain, and what does it leave free?

Let *r* be the release process's concurrency protocol and *c* the order process's protocol. The conditions we imposed include:

$$
r\ne\text{uncoordinated},\qquad c=r.
$$

If the order side is fixed as uncoordinated, matching its protocol forces the release side to be uncoordinated too. That contradicts the first condition. This explains why changing only the task or payment code produced no solution.

View the two protocols as coordinates. The points satisfying $c=r$ lie on the diagonal. Excluding the uncoordinated choice leaves two points: “both use row locks” and “both use version checks.” Neither lies where the order side remains uncoordinated.

**The region allowed by the Laws does not intersect the region allowed by the change scope.** This distinguishes two situations: the Laws have no solution at all, or solutions exist but lie outside the changes we permit.

Once we can change the order side too, we can choose a common protocol. The Law turns two independently selectable protocols into one shared choice. It narrows the set of candidates by tying two choices together.

My AAT paper, [*Rising Sea*](https://arxiv.org/abs/2609.27638), illustrates this relationship with two synchronized values. Start with independent values *u* and *v*, then impose the Law $v-u=0$. Choosing *u* now determines *v*. Algebraically, imposing this relation on a polynomial ring in two variables gives the same structure as a polynomial ring in one variable:

$$
k[u,v]/(v-u)\cong k[u].
$$

Here *k* is the field of coefficients, and “$/(v-u)$” imposes the relation that $v-u$ is zero. The symbol $\cong$ means the two rings have the same algebraic structure. Geometrically, we move from a plane with two freely chosen coordinates to a line with one shared value.

Saleor's protocols are not numerical values, but the relationship between choices follows the same pattern. Choose one common protocol, then choose storage and deletion behavior independently. Those three binary choices leave eight designs.

More generally, we express Laws as equations and study the space where they vanish together. To connect this space to software, evaluating an equation must give the corresponding Law's residual. In the synchronization example, that residual is the difference between the two values. The paper provides this correspondence and conditions for gluing local presentations together, connecting Law satisfaction to a space of solutions.

Which choices must agree, and which remain free? The shape of the solution space tells us why.

### What prevents the parts from forming a whole?

All eight designs satisfy the Laws, but they make different choices of protocol and storage. If the checkout and payment sides each report only “my local Laws hold,” we still do not know whether they chose the same protocol.

To assemble the whole, we need to know which protocol each side chose so that we can compare them. Information sufficient to evaluate a Law is not necessarily sufficient to assemble a design.

In Saleor, once the protocols agreed, the checkout side contributed its deletion policy and the payment side its storage choice. Together they determined one whole design. Building a whole from compatible local designs is called *gluing*.

Can we resolve disagreements by correcting each part, then glue the results?

Following the paper's cycle example, consider three services A, B, and C with conversion rules between their reference levels. We compare them on pairwise connections, with no common region where all three are compared. Suppose the A-to-B rule adds 1, while B-to-C and C-to-A leave the value unchanged. Going around the cycle increases the original value by 1.

Changing one service's reference level changes the offsets on its incoming and outgoing connections. But what we add to one is subtracted from the other. The sum around the cycle stays the same. No choice of local reference levels can make all three offsets zero.

**The offsets on individual connections can change while the offset around the cycle remains.** We group mismatches into equivalence classes when local corrections can transform one into another. Such a class is an *obstruction class*. In this example, the sum around the cycle distinguishes the classes. Mathematically, these are elements of the first Čech cohomology group.

This separates mismatches we can remove by local corrections from those the permitted corrections cannot remove. The reason a whole fails to exist can lie in the connections, even when the individual parts work.

### Why does a vanishing obstruction allow a repair?

A vanishing obstruction guarantees a global state under conditions on corrections and gluing.

The paper treats cases where differences between local states and their corrections are described by abelian groups. Within each local region, a unique correction takes any state to any other. Applying a correction and then restricting to a smaller part must give the same result as restricting first and applying the restricted correction. We also require local states that agree on overlaps to glue into a unique whole. This is the *sheaf condition*.

Let [*g*] be the obstruction class determined by the differences on overlaps. Under these conditions, the local states can be corrected and glued into a global state if and only if:

$$
[g]=0.
$$

Return to the three services, but now use conversion offsets of +1 from A to B, 0 from B to C, and −1 from C to A. The sum around the cycle is zero. Subtracting 1 from the values recorded by both B and C makes the values agree across all three connections. Here the zero obstruction leads to an explicit correction.

Afterward, adding the same number to the values at A, B, and C preserves agreement. The differences between reference levels are determined, but their common reference level remains free. **A repair can exist without being the only repair.** Gluing gives a unique whole once the corrected local states have been fixed.

To turn an algebraic correction into a software repair, we establish how corrections correspond to permitted changes. The paper builds a system for calculating differences and corrections from allowed repair operations and relations identifying operations with the same effect. It gives conditions under which this system corresponds to the equation side, preserving composition, restriction, and the obstruction classes. When the actual repair states also form a sheaf, a zero obstruction on the equation side is equivalent to the existence of a global repair.

If we simply stop examining one of the three connections, the cycle's offset becomes invisible while the mismatch remains. Did a repair eliminate the obstruction, or did we lose sight of it by reading less information? The same result, “nothing detected,” can have different reasons.

We can therefore ask whether changing how we read the system preserves the obstruction. In one example in the paper, a part is split into two. Correcting the new internal offset lets us return to the original description while preserving the sum around the cycle. Atlas diagnostic invariance gives conditions on Law evaluations, overlaps, and the correspondence of differences and corrections that preserve such a diagnosis. A more detailed description can still reveal the same reason the whole fails to exist.

### Three whys, one common structure

In our candidate family, widening the scope of change made solutions possible because we could choose the common protocol required by the Law on the order side too. Eight designs remained because there were two choices each for the common protocol, storage, and deletion behavior. Local designs determined the whole because, once the shared protocol agreed, the remaining choices imposed no further constraints on each other and specified one whole design.

All three answers come from the same relationship between candidates and Laws. Fixing what lies outside the change scope tells us whether any solution remains available. Examining the solutions reveals which choices remain free. Restricting solutions to parts and comparing their overlaps shows how the parts can form a whole.

**Change scope, freedom of choice, and the relationship between parts and wholes are different ways of reading one structure.** This connection is what I want to study with ArchSig. Beyond individual pass-or-fail results, how does the same condition answer several different questions about why a design works? That is what “why” means in this article.

## Where AAT meets formal methods

[Alloy](https://alloytools.org/spec.html) explores examples and counterexamples using relations and constraints. [TLA+](https://lamport.azurewebsites.net/tla/book.html) checks and proves behavior through states and their transitions. Counterexamples and proofs also help us understand why properties hold.

With ArchSig, I want to study the relationships among candidates. Here, the requirement to agree on a concurrency protocol connected change scope, shared information, and combinations of local designs. Studying those connections as a common structure is the focus of this work.

To connect AAT to an implementation, we read facts relevant to the Laws from code as Atoms. ArchSig's observation inputs retain source references so that we can check the correspondence between model and code. Extracting those facts depends on the implementation; AAT's theory is independent of programming languages and frameworks. When the shared structure satisfies a theorem's conditions, we can apply the same theorem to different implementations. What we reuse across languages is the reason a property holds.

This research connects to Goguen and Burstall's [institutions](https://courses.grainger.illinois.edu/cs522/sp2016/InstitutionsAbstractModelTheory.pdf), which study relationships between specifications and models, and Goguen's [sheaf semantics](https://ncatlab.org/nlab/files/Goguen-SheafSemantics.pdf), which relates local descriptions to global behavior. The AAT paper also discusses these connections.

## Continuing to ask why

We found eight designs satisfying the requirements. From there, we examined how the solutions depended on the change scope, what information was needed to decide, and how local designs corresponded to whole designs. Using Laws and Atoms to understand the conditions that separate success from failure is what I want to pursue with ArchSig.

What mathematical structures exist in the software we build? What can those structures tell us? Laws and Atoms give me a way to pursue those questions. That is why I am building ArchSig.

## References

- [AAT repository](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2)
- [My AAT paper, *Rising Sea*](https://arxiv.org/abs/2609.27638)
