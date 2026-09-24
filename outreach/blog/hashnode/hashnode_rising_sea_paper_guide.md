# What Does a Software Change Preserve? A Guide to the Rising Sea Paper

What should software engineering provide in an age when AI writes code?

We divide design work across teams, implement features, and migrate systems that are already running. Throughout that work, we need to make judgments: Will this update break another feature's assumptions? Will the same operations still work after the data migration? Will the designs for these services fit together? As AI accelerates development, we need clearer accounts of what must stay intact, what may change, and why we can trust the system to remain consistent.

**Algebraic Architecture Theory (AAT)** is the theory I am developing to make these questions mathematical. It provides a way to state what must be preserved and describe, in a form that can be checked, how parts fit together and how structures relate before and after a change.

I have published a paper laying out its foundations:

> [Foundations of Algebraic Architecture Theory: A Rising Sea of Geometry, Transport, Comparison, and Reconstruction](https://arxiv.org/abs/2609.27638)

The paper runs to 285 pages. AAT is a new theory I am building, so presenting individual results also requires establishing the objects they concern and the definitions and assumptions behind them. I chose to develop the foundations and the main theorems together as a coherent whole.

I also wanted a mathematical reference for future papers: a place to look up definitions, theorems, and proofs, rather than rebuilding the foundations every time I address a particular problem or application.

## Five questions that recur in software development

Change a data representation. Extract shared functionality. Split a system into services. Across different technologies and projects, the same questions return: What survives the change, and how do the parts remain consistent? The paper organizes these concerns around five questions.

**1. Can individually correct parts form a consistent whole?**

Each part may satisfy its own requirements while disagreeing with another part about shared data or assumptions. What conditions and corrections would let us assemble a whole? (Chapter 2)

**2. Can a summary reveal the same inconsistencies?**

When we summarize a complex system or examine it at a different level of detail, which information and relationships must remain for the diagnosis to stay the same? (Chapter 3)

**3. Can different migration paths and task orders preserve the same behavior?**

We might migrate in one step or in stages. We might select the relevant design documents before transporting a model, or transport it first and then select the corresponding documents. When do these routes preserve the operations and conditions we care about? (Chapters 4–5)

**4. If changes look the same, can we tell which ones preserve the required behavior?**

Two changes may produce the same visible output but behave differently when we perform an operation. What would we need to enumerate every candidate that preserves the required behavior? And when can we judge a candidate from visible output alone? (Chapters 6–7)

**5. Can separate teams' designs determine the overall design and migration?**

When teams divide up the work, what must each team specify, and what must agree where their responsibilities meet? Can their specifications determine a unique migration of the whole system? (Chapter 8)

## A running example: migrating an e-commerce system

Consider an e-commerce system with three services:

| Service | Responsibility |
| --- | --- |
| Orders | Manage orders and shipping addresses; accept address changes and cancellations |
| Payments | Manage payment status; process payments and refunds |
| Inventory | Reserve items for orders; release reservations when orders are canceled |

All three services refer to the same order by its ID. Canceling a paid order requires an order status change, a refund, and the release of its inventory reservation.

Take order 42: it ships to the customer's home, costs \$12.33, has been paid for, and has inventory reserved. As the teams revise their data formats and divide up the processing differently, we still need to be able to change its shipping address and cancel it with the appropriate refund and reservation release. We will follow this order through the article.

## Chapter 1: Decide what to preserve, then build the model

Do we only need to preserve the displayed shipping address? Or must we also preserve how address updates behave and how they interact with payment information? We cannot judge a change until we decide. AAT starts by making the model's contents, operations, and required conditions explicit.

For our example, we include a state containing a shipping address and payment information, an operation that reads the address, and an operation that updates it.

AAT calls a typed basic fact—such as the existence of a component or a named operation—an **Atom**. Here are some Atoms we could describe:

| Kind | Example fact |
| --- | --- |
| Component | There is a component for order states |
| Component | There is a component for shipping addresses |
| Operation | There is a `read` operation that takes an order state and returns its shipping address |
| Operation | There is an `update` operation that takes an order state and an address, and returns the updated order state |

We also specify how those operations must behave. A requirement expressed as an equation is called a **Law**.

Let $s$ be an order state and $a$ a shipping address. Then `read(s)` is the current address, and `update(s, a)` is the state after setting the address to $a$.

Reading the address after an update should return the address we just supplied:

$$
\operatorname{read}(\operatorname{update}(s, a)) = a
$$

If we change an order from a home address to a work address, reading it should return the work address. This is the familiar expectation that a getter returns the value supplied to a setter.

We can also require that writing back the current address leaves the order unchanged:

$$
\operatorname{update}(s, \operatorname{read}(s)) = s
$$

The right-hand side is the **entire order state**, not just the address. An operation that changes payment information when we set an already home-bound order to “home” again would violate this Law. These equations must hold for every order state $s$ and every address $a$ to which they apply.

Expressing the structure and conditions we want to analyze through Atoms and Laws makes the analysis independent of a particular programming language or framework. Different implementations can be described in a common language: which components and operations exist, and what they must satisfy.

### From software requirements to geometry

Let $x$ be the refund expected by the order service and $y$ the refund recorded by the payment service. The requirement that they agree is $x-y=0$. The pairs $(x,y)$ satisfying that equation form a line in the plane. We have moved from checking one order to studying the space of states the requirement permits.

The idea extends to more values and more conditions: represent states with variables, express requirements as equations, and study their solutions. This is the entry point from software descriptions to algebraic geometry. AAT makes explicit both this interpretation and how operations act on states.

No single service holds the entire state of our e-commerce system. Orders holds cancellation status and the expected refund; Payments holds the refund amount; Inventory holds the reservation status. We treat these as parts, linked through shared order IDs and amounts. Now we can ask: **Is there a state that satisfies all their conditions at once?** Studying solutions lets us move from checking individual orders to asking whether the requirements themselves can coexist.

Chapter 1 establishes the foundations for moving from facts to models equipped with operations, Laws, and relationships between parts. Later chapters use that geometry to study consistency and migrations.

## Chapter 2: Can the records fit together?

Suppose an order cancellation triggers a refund. What happens if the order service and the payment service handle the amount differently?

For this example, a cancellation refunds 80% of the purchase price. For order 42:

```text
12.33 × 0.8 = 9.864 dollars
```

The actual payment must be rounded to cents. But suppose the revised processes follow these rules:

| Process | Rule | Value for order 42 |
| --- | --- | --- |
| Order storage | Store the purchase price | \$12.33 |
| Cancellation in Orders | Calculate 80% and round to two decimal places | \$9.86 |
| Refund reconciliation in Payments | Calculate exactly 80% using decimal arithmetic | \$9.864 |

Both processes follow their own rules, yet they disagree by \$0.004 about the same refund. The discrepancy is **a rounding difference smaller than one cent**.

What changes would reconcile them?

| Allowed change | Result for order 42 |
| --- | --- |
| Leave both amounts and reconciliation rules unchanged | `9.86 ≠ 9.864` |
| Apply the same rounding rule during reconciliation | Both sides use `9.86` |
| Record the rounding adjustment and include it in reconciliation | `9.86 + 0.004 = 9.864` |

The last approach retains the difference but accounts for it. Whether reconciliation is possible depends on which repairs we allow.

Shared information about orders and amounts forms an *overlap* between processes. Combining partial data according to the agreed relationships on those overlaps is what mathematics calls **gluing**. A **sheaf** captures the relationship between reading parts of a whole and uniquely assembling a whole from compatible partial data.

### Each pair can be reconciled, but all three cannot

Now apply the second repair: Payments also uses the rounded amount, \$9.86. Orders and Payments agree. Then introduce a reconciliation ledger on the payment side, so that we compare the cancellation record, the refund record, and the ledger.

Assign one adjustment to each record. Every comparison involving that record must use the same adjustment.

Suppose two comparisons use rounded amounts, while the third requires the ledger to account for the difference from the unrounded amount. They impose the following requirements:

| Records being compared | Required relationship between adjustments |
| --- | --- |
| Orders and Payments | Payments adjustment − Orders adjustment = 0 |
| Payments and Ledger | Ledger adjustment − Payments adjustment = 0 |
| Orders and Ledger | Ledger adjustment − Orders adjustment = \$0.004 |

Any one requirement can be satisfied on its own. But adding the first two gives “Ledger adjustment − Orders adjustment = 0,” contradicting the third. **We can choose adjustments for each pair separately, but no single choice satisfies all three pairs.**

Follow the comparisons around the loop: Orders → Payments → Ledger → Orders. The last step traverses the Orders–Ledger comparison backward, so we subtract its required difference. The total is `0 + 0 − 0.004 = −0.004` dollars. Changing the adjustment at any record cannot change this total: its contributions cancel around the loop.

Examples 2.19 and 2.27 in the paper study this kind of residual around a loop. In this model, adjustments may take any value, and the comparison data consists of the three pairs in the table. We do not add a separate three-way comparison.

**Cohomology** treats differences removable by the allowed adjustments as equivalent, and records what remains. Here, the loop total is an obstruction that those adjustments cannot remove. If we revise the third comparison to use the rounded amount as well, the loop total becomes zero, and setting every adjustment to zero works. That repair changes a reconciliation rule; it does more than choose new adjustments under the existing rules.

Chapter 2 states conditions connecting such an obstruction to the existence of a whole. For example, adjusting an order record and then reading its shared refund amount must give the same result as applying that adjustment directly to the shared amount. When adjustments are compatible with reading partial data in this way, and states form a sheaf, the following are equivalent (Theorem 2.22):

- The obstruction is zero.
- The local states can be adjusted in the allowed ways and glued into a global state.

A nonzero obstruction means there is no such global state within the fixed model and allowed adjustments. When corrections are possible, the corrected partial data determines a unique whole. The choice of corrections itself need not be unique.

## Chapter 3: Can a summary preserve the diagnosis?

Suppose we summarize service records to review a change to cancellation processing. Omitting a full street address and rounding a refund amount have different consequences. Displaying both refund values for order 42 as “\$9.86” would hide the discrepancy we started with. Which information must survive the summary?

### Preserving Law values is not yet preserving the diagnosis

Chapter 3 begins by fixing the Laws we want to examine and their evaluation values—for example, the difference between the two sides of an equation. Put states in the same group exactly when all the selected Laws evaluate to the same values. Keep states with different values in separate groups. This retains precisely the distinctions needed to preserve those evaluations (Theorem 3.4).

But evaluating a Law within each part and diagnosing disagreement between parts are different tasks. Keeping `9.86` and `9.864` is not enough if we accidentally compare amounts from different orders. We also need to know that these are the expected and recorded refunds for order 42.

The paper therefore gives conditions relating which records we read, which pairs we compare, and how we calculate differences before and after summarization. In the three-record example, this includes the comparison loop and the treatment of adjustments, as well as the values in the records. Under these conditions, the diagnoses correspond one-to-one, and one is zero exactly when the other is (Theorem 3.17). Summarizing neither hides an existing obstruction nor invents a new one.

When the necessary values and comparison relationships can be enumerated and computed as finite data, the preservation condition can itself be decided by a finite computation. This concerns Laws evaluable from both summaries: the criterion determines whether diagnosis is preserved for every finite selection of those Laws (Theorem 3.22 and Proposition 3.23).

For code review in the age of AI, this suggests a concrete research question: What must a reviewer retain to reduce the reading burden without overlooking inconsistencies? Turning the mathematical preservation conditions into practical review methods remains future work.

## Chapters 4–5: Comparing migration paths and task order

Next, change the order data format. The old version stores the address in a top-level `shipping_address` field. The new version groups shipping information in a `shipping` object, with the address in `shipping.address`. An intermediate version that merely renamed the field to `shippingAddress` is already in use.

We can migrate directly, or chain existing migrations through the intermediate version:

| Route | Where the address is stored |
| --- | --- |
| Direct | `shipping_address → shipping.address` |
| Via the intermediate version | `shipping_address → shippingAddress → shipping.address` |

Order 42 should retain the same address along either route. Address updates must also move to the new field, and must continue to leave payment information unchanged.

### The rest of the migration is not a free choice

Chapter 4 constructs **transport**: a way to carry operations, Laws, and relationships between parts together along a change that satisfies conditions including a one-to-one correspondence between extracted Atoms.

Fix the overall migration from old to new, and fix the underlying schema mappings from old to intermediate to new. Transport the old structure to the intermediate version. Then **there is exactly one migration from that transported model to the new model that realizes the overall migration we specified** (Theorems 4.5 and 4.11).

Adding an intermediate version seems as though it should introduce more choices. But when we construct it by this transport, there is no further choice of a continuation compatible with the overall migration. The factorization preserves the modeled update operations and Laws, not just the location of the address field. The uniqueness concerns the migration between mathematical models; it does not mean there is only one way to write the implementing program.

We can also compare a model transported directly to `shipping.address` with one transported through `shippingAddress`. The paper constructs a correspondence that lets us move between the two while preserving operations and Laws. Adding more intermediate versions does not introduce ambiguity: comparing one stage at a time or grouping stages together produces the same final correspondence (Theorem 4.15).

Independently specified migrations can still disagree. If one swaps the shipping and billing addresses, the route changes the resulting address. For a finite collection of paths, the paper shows that the transformations can be reselected to satisfy all the specified comparisons exactly when the obstruction to their agreement vanishes (Theorem 4.23).

### Combining documents need not lose the structure they describe

Now choose which design documents to review. Suppose the old web and mobile app cancellation specifications both map to a shared cancellation specification in the new design.

| Old document | Corresponding new document |
| --- | --- |
| Web cancellation specification | Shared cancellation specification |
| App cancellation specification | Shared cancellation specification |
| Address-change specification | Address-change specification |

Once two documents map to one, the new document's name cannot tell us whether we started from the web or app specification. Must the model derived from those documents also become impossible to recover?

Suppose both cancellation specifications yield the same Atoms and are equipped with the same operations and Laws. Losing the distinction between their origins need not lose those structures. The paper shows that **even when the mapping of source documents is not invertible, models built from a selected document can still be related by a reversible, structure-preserving correspondence** (Proposition 5.8 and Example 5.9). What we recover is the structure of types, operations, and Laws, rather than the history of the documents.

If we select the shared cancellation specification in the new version, we must therefore pick up both the web and app specifications on the old side. Picking only one would give us a mismatched scope.

A model is built by reading types, operations, and Laws from the documents. Chapter 5 constructs pairs of corresponding sources and gives a way to read model structure over the selected sources.

It compares two routes:

- Select the old web and app cancellation specifications, then transport the model built from them to the new version.
- Transport the old structure to the new version, then read the structure over the shared cancellation specification.

Under the specified conditions on source mappings, extracted Atoms, operations, and Laws, these routes yield models connected by a reversible, structure-preserving correspondence (Theorem 5.11). Separating how documents are consolidated from which model structure is preserved lets us explain why different task orders can still retain the same operations and Laws.

## Chapters 6–7: What remains after we leave information out?

### The remaining structure can still correspond

So far, we have transported structure while preserving it. Now, to focus on addresses and their updates, set every payment code in the comparison data to “unset.” We can still read and update addresses, but we cannot recover whether the payment code was originally 1 or 2.

Running this process twice has the same effect as running it once. That property is called **idempotence**. The paper uses **normalization** for a process that puts objects into a standard form while preserving the required structure. This is a different use of the word from database normalization.

For order 42, set payment information to “unset” and match the old `shipping_address` with the new `shipping.address`. Changing the old address to work corresponds to changing the new address to work. The payment information cannot be recovered, but the address and its update behavior can still be related in both directions.

Chapter 6 constructs an idempotent normalization of the full structure under conditions that preserve operations, Law evaluation values, and other required data (Theorem 6.14). The comparison studied here can be understood as a composition of transporting structure and then normalizing it to leave information out.

The interesting result is that **losing information irreversibly can still leave a reversible correspondence between the structures that remain** (Theorem 6.12). Starting from an invertible correspondence, define the normalizations so that both sides retain matching structure. The remaining parts are then isomorphic: we can move between them in both directions while preserving structure.

By contrast, the comparison constructed here is invertible on the original full structures if and only if normalization changes nothing (Theorem 6.16). The distinction makes explicit how much of the original structure the comparison preserves.

### The same display does not imply the same update behavior

Chapter 7 returns to migrations of the complete order. Even if addresses and updates correspond after excluding payment information from the comparison, the migration of the full order may still be unsuitable.

Write the addresses as “home” and “work,” and focus on the internal payment code. In both the old and new systems, editing the address leaves payment information unchanged. But suppose the migration converts payment codes differently depending on the address:

| Before migration | After migration |
| --- | --- |
| Address: home; payment code: 1 | Address: home; payment code: 1 |
| Address: work; payment code: 1 | Address: work; payment code: **2** |

Start from the same order: home, payment code 1. Now compare when we change the address to work.

1. **Migrate, then update.** The home order migrates with code 1. Updating only its address leaves us with **work, code 1**.
2. **Update, then migrate.** We first change the old order's address to work. It then migrates as a work order, giving **work, code 2**.

The displayed address agrees, but the payment information does not. What we want is **the same order state whether we migrate before or after the update**.

### Four candidates become two

Restrict addresses to home and work, and payment codes to 0, 1, and 2. Keep 0 fixed as the “unset” value used in Chapter 6. For codes 1 and 2, either keep them as they are or swap them. The mapping between old and new codes is itself a design choice.

| Candidate | Home orders | Work orders | Preserves address updates? |
| --- | --- | --- | --- |
| A | Keep codes unchanged | Keep codes unchanged | Yes |
| B | Keep codes unchanged | Swap 1 and 2 | No |
| C | Swap 1 and 2 | Keep codes unchanged | No |
| D | Swap 1 and 2 | Swap 1 and 2 | Yes |

All four preserve the displayed address and the unset value. Only A and D preserve updates. Because an update can take us between home and work, both must use the same code mapping. D is valid because it relabels the codes consistently. If code 1 must literally remain code 1, we must state that as an additional requirement.

Chapter 7 generalizes this for systems whose operations preserve internal state. With the visible state fixed and internal states relabeled bijectively, view visible states as vertices and operation-induced connections as edges. Each connected component must use one consistent relabeling; different components can choose independently. **These choices describe all changes of this kind that preserve the operations** (Theorem 7.24). In the finite case, we can also count them. The four-candidate example is based on Example 7.28 in the paper.

### Judging a candidate and constructing one are different tasks

The display cannot distinguish A from B. Add “swap codes 1 and 2 only for work orders” to A, and we get B. The displayed address stays the same, but preservation of updates is lost.

More generally, if an invisible modification can change whether a candidate is acceptable, observation alone cannot decide the question. The paper proves a necessary and sufficient condition: adding changes invisible to the observation must leave acceptability unchanged (Theorem 7.9).

To construct an acceptable candidate, however, we can start with A. Add “swap codes 1 and 2 for both home and work,” and we get D. An invisible modification that preserves updates gives us another acceptable candidate.

The paper provides a way to start with a migration of normalized models and supply mappings for the information that was left out. Here, that means adding a payment-code mapping to an address-only migration to obtain a migration of the complete order. It constructs one migration satisfying the requirements and describes all the other candidates from there (Theorems 7.19 and 7.21).

This requires the original models to be related by an invertible, structure-preserving comparison. It also requires the normalization—which determines what is retained and what is hidden—and its associated data to admit a common representation on both sides.

Constructing an acceptable candidate with this information is a different problem from judging a supplied candidate by its display alone.

## Chapter 8: Building the whole from separate teams' designs

Finally, divide the design and migration work among three teams.

| Team | What it designs | What must agree with other teams |
| --- | --- | --- |
| Orders | Order types and states, cancellation operations, old-to-new mappings | Order IDs and the conditions for completed cancellation |
| Payments | Payment and refund types and amounts, refund operations, old-to-new mappings | References to the same order, refund amounts, rounding rules |
| Inventory | Product and reservation types and states, release operations, old-to-new mappings | References to the same order and reservation release on cancellation |

Agreeing on order IDs is not enough. Adopt the Law that a cancellation is complete only when the required refund has been made and the inventory reservation released. All three teams might map order 42 to the same new order, yet map its states to “cancellation complete,” “refunded,” and “still reserved.” That migration would not preserve the Law.

Operations need to correspond too. Releasing a reservation in the old system and then migrating must agree with migrating first and performing the corresponding release in the new system. Each team specifies its types, values, operations, and Laws, together with how shared information is mapped.

The paper's main result, the **local reconstruction theorem**, shows that **we can assemble the whole from descriptions of its parts without assuming a completed whole in advance**. Give the parts' descriptions separately, and check their compatibility on shared data, operations, Laws, and the other required structure. Two results follow.

First, **the whole structure can be recovered up to isomorphism**. Names or representations may differ, but the objects, operations, and other structure correspond in both directions.

Second, **once the old and new structures are fixed, compatible local migrations determine a unique structure-preserving migration of the whole**. With the required descriptions in place, there is no room for two different global migrations that look identical on every specified part.

Chapter 2 asked whether amounts and their comparison rules fit together into a consistent whole. Here, the things we assemble include data types, operations, and the migration itself.

This conclusion requires a complete description of the model's data: types, values, operations, Laws, which values are read from which parts, and the rest of the specified structure. The descriptions must agree where they overlap. The main result is Theorem 8.18; Section 8.6 applies it to design work divided among teams.

## Returning to the five questions

What answers did we get by following the e-commerce example?

**1. Can individually correct parts form a consistent whole?**

Following each process's own rules did not make order 42's refund records agree. Under the theorem's conditions, the existence of allowed corrections that reconcile the whole is equivalent to the gluing obstruction being zero.

**2. Can a summary reveal the same inconsistencies?**

Rounding away digits can hide a refund discrepancy. Losing the link to the order can lose the comparison partner. The paper provides conditions for preserving diagnosis across changes in values and relationships, along with a decision criterion for the finite setting.

**3. Can different migration paths and task orders preserve the same behavior?**

We compared direct and staged migrations, and selecting cancellation specifications before or after transport. Under the conditions that preserve structure and the mappings between sources, these routes can be compared coherently. Disagreements among specified paths can also be studied as obstructions.

**4. If changes look the same, can we tell which ones preserve the required behavior?**

The address display could not distinguish the four payment-code mappings. Examining updates reduced them to two. The paper separates classification and construction of acceptable changes from the conditions for judging them by observation.

**5. Can separate teams' designs determine the overall design and migration?**

Orders, Payments, and Inventory supplied types, operations, shared order references, and completion conditions. With all the required design data and compatibility conditions, the whole structure is recoverable up to isomorphism, and a migration between fixed old and new structures is uniquely determined.

## Beyond the Rising Sea

The title *Rising Sea* expresses an approach: develop a common theory broad enough to bring individual problems within reach. This paper establishes foundations for studying consistency, migration comparisons, and reconstruction within the same mathematics.

The next step is research on extracting structures and Laws from real code and specifications, working at the scale of software development, and testing whether this helps engineering judgment in practice. As AI produces changes faster, I want to give us stronger grounds for taking responsibility for them.

**What does this change preserve—and how can we establish that?**

## Finding your way through the paper

The [paper's arXiv page](https://arxiv.org/abs/2609.27638) provides PDF and HTML versions. Chapter numbers in this article refer to the paper; Chapters 4–5 and 6–7 are grouped here. The theorem references lead to the precise assumptions and proofs.

The four address-update candidates appear in Example 7.28 in Section 7.8. The application of reconstruction to designs developed by separate teams is in Section 8.6. Appendices A and B document the correspondence with Lean declarations and the verification procedures.
