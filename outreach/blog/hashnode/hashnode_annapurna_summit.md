# The Goddess of Plenty Smiles at the Summit: 16 Theorems, 2 Refutations, and the Structure of Software Design

Every test passes. Every metric looks the same. Is that enough to judge whether a design change is sound?

There are pairs of changes that the observations of AAT (Algebraic Architecture Theory) cannot tell apart — even though one keeps the system coherent and the other breaks it. And the difference cannot be recovered by any post-processing of the same observed values. This summer, that limit became a theorem, machine-checked in Lean 4.

In five weeks starting August 2, 2026, we proved sixteen theorems and refuted two claims. An AI agent loop did the implementation; I set the goals, reviewed the proofs, and made the calls. This article is a record of what we found, and of the road that led there.

## 1. AAT: Algebraic Architecture Theory

AAT is a research program that analyzes software architecture with the tools of algebraic geometry. It starts from observing source code. Implementations are abstracted into components called Atoms; the specification is written as a family of equations called laws. Design coherence then becomes a mathematical question: does local correctness glue into a consistent whole?

A running example from earlier articles is the one-cent drift. Three modules of a commerce service — checkout, payment, and ledger — each pick a rounding rule that passes review on its own, and the card gets charged one cent more than the screen displays. Each module follows its own rules. The whole still doesn't add up.

In this example, each module's implementation is an Atom, and an equation like "the amount displayed equals the amount charged" is a law. A quantity that aggregates the local mismatches into a global one, like that one cent, is a cohomology class, and reading it off to point at the inconsistency is what we call diagnosis. The earlier work — the SAGA and Atlas theorems, each with its own article — made all of this measurable.

A view is the result of reading the code at a particular resolution and from a particular angle; a service-level view and a module-level view are different views. Carrying an analysis result from one view to another is transport, and swapping out the base the analysis stands on is base change. In the one-cent example, adding settlement as a new context changes the very ground of the analysis; that is one instance of base change. When an operation survives such a swap, we say it is closed under the swap.

Every theorem in this article is machine-checked in Lean 4, a proof assistant that mechanically verifies whether a proof establishes the statement written down.

The question of these five weeks: when you change how you look, or the ground you stand on, how much of your analysis and your comparisons survives the move?

## 2. Five things we can now say about software design

**1. Observation alone cannot always tell a sound change from a breaking one.**

Take two candidate changes. Test results, metrics, every value in AAT's observations: identical. Yet one preserves global coherence and the other destroys it. Such an example has been constructed, and no aggregation or post-processing of the observed values can distinguish the two (Section 5). The practitioner's intuition — "you can't manage architecture by numbers alone; you have to look at the structure" — is now a theorem inside the model.

The information you need lives not in the numbers but in the correspondence that connects the before and after of a change. So the next move is not to inspect change proposals after the fact; it is to derive the required companion change directly from that correspondence.

**2. The degrees of freedom in a fix are now known exactly.**

You change one side of an interface. How can the other side be fixed so the two still agree? The theorem describes the full space of compatible fixes (Section 5). Find one, and every other fix can be derived from it — none missing. A design review can move on from "is this fix acceptable?" to "how much freedom does this fix have, and does the choice matter?"

**3. Harmless-looking normalization stays in your design.**

Some formatting and normalization passes are not supposed to change meaning, and as far as observation goes, they don't. Even so, there are cases where the local normalizations scattered across a system cannot, in principle, be merged into one globally consistent operation (Section 4). Fixing a convention for "what counts as the same meaning" does not end the design question; which operations remain sound under that convention is itself part of the design. So normal forms deserve to be first-class citizens of the design, not an afterthought.

**4. We now know exactly when divide and conquer is honest.**

Analyze each module, then combine the results into a conclusion about the whole. The condition for this to be sound is now a theorem, in necessary-and-sufficient form (Section 3). We also proved that analysis results do not depend on how the code happens to be written down. Together, the two mean analysis need not start over on every change: there are precise conditions under which re-checking only the changed part and its overlaps is enough. That matters at scale — for large codebases, and for fleets of AI agents developing in parallel.

**5. A change of meaning cannot pass through the label layer.**

On a fixed base, relabeling alone — types, tags, and other metadata — cannot move observable meaning. A change of meaning can live only on the side where the base itself moves. This, too, is a theorem (Section 8). There is now a structural reason why metadata edits preserve meaning.

The one-cent drift connects here as well. That example showed that the failure of locally correct modules to glue can be measured. The new results establish where the limits of that measurement lie. The boundary between what can be measured and what in principle cannot is now drawn as a theorem.

## 3. Three layers of theorems

The sixteen theorems answer three questions.

**Can analysis results be carried between views of different resolution and level?** Yes, and by any route: the result of a service-level analysis and the result of a module-level analysis can be traded back and forth without loss, and moving across levels loses nothing either. Catch the one-cent drift at service granularity or at module granularity; either way, it can be matched up as the same inconsistency.

**When the base of the analysis is swapped, which operations survive as theorems?** The answer is a table of conditions, direction by direction: classifying the operations that vary with the base; base change along refinements that carve the base finer; and lifting, which extends a partial result one level up. Each stands as a theorem with its scope pinned down. The point is that not every direction holds unconditionally. That dividing line — which direction holds under which condition — is what this layer establishes.

**When may a conclusion about the whole be drawn from finitely many parts?** A necessary and sufficient condition is now settled for when partwise analysis lifts to the whole, and for how far diagnosis survives transport. The negative side is proved as well: an arbitrary choice of covering can change the diagnosis of the very same system (Section 7). Unconditional divide and conquer fails, which is exactly why a condition is needed — and the condition is exact, nothing extra and nothing missing.

All three are classifications, not conjectures. The boundary — which operations are closed, and where closure fails — is drawn with proofs.

## 4. The normalization factor that cannot be removed

The strangest finding is an invisible factor lodged inside comparisons.

AAT generates comparison morphisms between two views: before and after a change, a fine view and a coarse view. Ideally a comparison is invertible; then the two views can be traded back and forth without losing information.

A comparison is a family of maps, one per object. For the comparison \(\beta\) that the system actually generates, each component provably factors as

$$
\beta = E \circ \alpha
$$

first through \(\alpha\), then through \(E\). Here \(\alpha\) is the ideal comparison prescribed by the theory, and it is provably invertible. And \(\beta\) is the concrete comparison assembled from actual input. How does the concrete deviate from the ideal? The deviation is exactly \(E\), and this factor has three properties at once.

First, it is idempotent:

$$
E \circ E = E
$$

Applying it twice is the same as applying it once, like running a code formatter twice.

Second, it is invisible to observation. \(E\) moves no observable quantity; under the observations considered here, it cannot be told apart from a map that does nothing.

Third, it is nevertheless not invertible. Wherever \(E\) actually fires, it cannot be undone, and therefore \(\beta\) as a whole is not invertible either.

So what breaks the invertibility of comparisons is a normalization factor that appears, to observation, to do nothing at all. And invertibility does recover — if you restrict where you stand. In the raw world, \(\beta\) is not invertible. Restricted to the image — the values that actually remain after \(E\) — it becomes invertible. And on observable quantities, \(\beta\) and \(\alpha\) agree exactly. The failure is not monolithic; it splits into these three stages. That recovery on the image will matter later: it is the doorway to the next stage of the research (Conjecture A, Section 11).

Then why not simply remove \(E\)? Bundle it into one natural operation running through every object, and subtract it from the system uniformly.

That is impossible, and this too is a theorem. From the same starting point, compare normalizing at A and then moving to B, against moving to B first and normalizing there. A concrete counterexample exists where the two disagree. Compatibility with movement between objects is what mathematics calls naturality: \(E\) is a perfectly usable normalization at each object, yet it cannot be bundled into one natural operation compatible with movement.

**A structure invisible to the observations at hand, one that decides whether comparisons succeed, and that cannot be removed: it was there all along.**

## 5. Degrees of freedom, and the limits of observation

The strongest result is a classification of the freedom in changes. The subject is compatibility of changes across an interface.

The setup: two sides joined by a single comparison, and a change applied to each side. We consider reversible changes here. Which pairs of changes preserve the comparison? In other words, when you change one side, which companion changes on the other side keep the whole consistent?

"Preserve" means this: changing one side and then comparing gives the same result as comparing first and then changing the other side. When that holds, the pair of changes is compatible with the comparison.

The theorem settles four things at once.

First, the compatible pairs of changes form a group: operations that can be chained and undone, with "do nothing" as a member. Integer addition is the model case.

Moreover, once one compatible companion change is found, every other one can be expressed as a difference from it. Any of them could serve as the reference; none is privileged from the start. This structure is called a torsor. The space of compatible companion changes has exactly that shape.

Second, for the comparisons the system actually generates, source-side changes can always be carried across, and the companion options on the other side form a coset: one solution multiplied by the elements of a subgroup. That subgroup is characterized by concrete conditions on the input data.

Third, the classification does not depend on presentation. The same design can be written in many forms: different file splits, different orders of definition. Rewrite first and then generate the comparison, or generate and then transport: the classification lands in the same place. What this analysis measures is not the style of the writing but the structure of the meaning — and that is what the proof establishes.

Fourth, **observation cannot decide this classification.** In a fixed example, compare two options.

| In the fixed example | Option A | Option B |
| --- | --- | --- |
| Change applied to the source side | the same change | the same change |
| Response on the other side | the required companion change | nothing |
| Result under the observations considered here | same as B | same as A |
| Compatibility with the comparison | preserved | broken |

The correct companion change is uniquely determined. Yet from the observations alone there is no telling whether that change was made or nothing was done — and provably, no post-processing recovers the difference. **The information that singles out the one required companion change is lost by observation.**

## 6. The plan: turning a metaphor into theorems in five stages

The rest of this article is the record of the five weeks that led there. In hindsight, it was a climb up a mountain whose map was wrong.

The early theory notes described AAT's construction as "Grothendieck-like." Grothendieck rebuilt algebraic geometry in the twentieth century; much of the machinery connecting the local and the global goes back to him. But "Grothendieck-like" was only a metaphor. How far does analysis survive moving between views and swapping bases? The road from metaphor to theorem was laid out as a five-stage plan:

```text
Gr0 Metaphor: said, not shown
Gr1 Formalization: the claims written as mathematical statements
Gr2 Constructed instance: an object that actually satisfies them
Gr3 Pseudofunctorial coherence: transport between views agrees along any route
Gr4 Base-change completeness: every operation closes, base swaps included
```

The first two stages were already done in the theory notes. To climb the rest with theorems, eighteen research cards were issued starting August 2. A card is a document that pins down the theorem to prove, its scope, and its completion criteria.

## 7. The climb: from the foothills to Gr4

The first summit fell on day one. On August 2, the construction of Atom transport was proved: Gr2 reached. On August 8, the Atlas theorem. On August 18, transport across levels of views was proved to agree along any route: Gr3 reached. Four of the five stages, in under three weeks.

On the way, on August 11, came the first refutation. The plausible claim "changing the structural covering (a way of covering the whole with finitely many parts) does not change the diagnosis" turned out to be false. The refutation was not wasted. Its counterexample revealed where the residual — the quantity measuring a failure to glue — can appear and where it never can, and that distinction fed straight into the design of later counterexamples. A refutation becomes reconnaissance for the next route. That pattern would repeat for all five weeks.

Only Gr4 remained, and this was the real mountain. The foundation is a construction that takes two bases and builds a new one from the pairs that agree over a common base (the fiber product; call it crossing bases). The foundation theorem was proved on August 25, but it took 111 cycles (a cycle is one loop iteration: the agent adds one step of proof and records evidence and an audit trail). Most earlier cards had finished in a few to a few dozen cycles. That is the gradient of this mountain.

Standing on the foundation, we could finally see the terrain: this mountain has no single route, because it has no single summit. The work was split into six cards, one responsibility each, and between August 26 and September 4 all six were settled by proof, one of them taking 84 cycles and nine revisions of its card. The full record of all eighteen cards is in the appendix.

## 8. The mountain in the plan did not exist

All six cards were settled by proof. And yet Gr4 itself — the original goal: swap the base, analyze there, carry the results home, every step of the round trip a theorem — turned out to be false as stated. The content of the proved theorems itself showed that the mountain in the definition does not exist. On September 4, we decided not to write a completion record for Gr4. You do not file a summit report for a mountain that was never there.

What failed comes down to two things.

First, **vertical rigidity**. Call vertical the direction in which only extra labels are swapped while the base stays fixed. No meaning-moving transformation can be placed in that direction; such transformations have to be handled horizontally, where the base itself moves.

Second, **the comparisons the system generates are not invertible**, because, as Section 4 explained, the invisible factor \(E\) sits inside them.

So where did this conclusion come from?

## 9. The turning point: refutations became the harvest

The turning point came right after the hardest pitch, the lift to the upper level (84 cycles, nine revisions). That climb left behind not only its summit theorem but a pile of counterexamples, because every revision had deposited refutation theorems in Lean — each one saying, in effect, "not in this form."

Surveying the pile after the pitch, we noticed the counterexamples fell into three families.

- Attempts to place a meaning-moving transformation in the vertical direction had failed independently on two cards, and both were resolved by moving the transformation to the horizontal side.
- Lossy collapses were never going to yield invertibility. Identify two objects that differ only in decoration, and the map sends different things to the same place — no longer one-to-one, and a correspondence that is not one-to-one can never serve as part of an invertible comparison.
- Fix all the route data and swap only the comparison component joining the two sides, and glueability flips, while to observation nothing appears to change at all.

Line the three up and a common trait appears: something observation cannot see, yet which decides the strict properties — invertibility, glueability — and lurks in both the vertical and the horizontal directions. And none of these refutations had been designed to show this. They are the traces of the structure pushing back in the middle of proofs aimed elsewhere. If so, one structure must be behind them all. That structure was exactly the normalization factor \(E\) of Section 4.

So the sixth card, originally the summit card that was to close out Gr4, was redesigned into the card that would hunt down the structure behind the counterexamples. The redesigned card was settled by proof on September 4 (the 9/4 row in the appendix): the identification of \(E\). The counterexamples had not been wrecking the mountain. They had been teaching us that there was a mountain that no one-dimensional map — no single yes-or-no ruler — could capture.

Beyond that identification, the refutation of September 5 (Section 4: the impossibility of bundling) turned \(E\) from something to erase into something to classify, and that decision shaped the final theorem of September 6 (the classification of Section 5). In hindsight, this change of course led to the highest summit of the five weeks.

The same pattern runs through all five weeks. The August 11 refutation supplied the method for designing counterexamples; on the cards of August 28 and 29, the content of a refutation directly became the design of the next revision, which was then proved. Individual refutations shaped the next card, and their accumulation rewrote the plan itself. In the Atlas article, I wrote that the four refutations were the best part of the climb. This time the same thing happened not inside one theorem but across the whole series. The map being wrong about the mountain: that itself was the harvest.

## 10. The descent was the real test

The work after standing on a summit was the real test, because declaring a proof complete and being able to trust that declaration are two different things.

Here is how the loop runs. The agent works cycle by cycle toward the claim and completion criteria fixed on the card, recording evidence and an audit trail as it goes. Completion requires, in order: a full completion report, four independent reviews of the same proof target (two mathematical, two Lean), and a cross-check of the evidence records. Only then is a card settled.

Over the five weeks, the procedure stopped exactly where it should have.

- Two cards halted at the first step (writing the claim down in rigorous types) when defects in the claims surfaced; I revised the cards before the loops resumed.
- One card halted at the provenance check of its evidence.
- Two cards had "proof complete" declared, after which the audit found defects in the records and rolled the state back; completion was then redone. In both cases the defect was in the evidence records, never in the theorem itself.

Those last two matter most. The summit had been declared, and the descent checks rejected it. Checking the evidence with the same rigor as the theorems is what makes the declarations trustworthy.

Over the five weeks, the Lean code grew to 791 files and roughly 300,000 lines, and the agent loop consumed about 24 billion tokens. Through all that volume, the policy of stopping on doubt was never relaxed — and I believe it is precisely because the system was built to stop that sixteen theorems in five weeks could be delivered without burning trust. Mathematics aside, the speed itself is an empirical result: a formalization that starts from observing source code can run this fast.

## 11. Higher peaks beyond

From a summit, you see the next mountains. The harvest of the traverse includes three conjectures. None are proved, but for each, the object to construct next is already in view.

**Conjecture A (making normal forms first-class).** Section 4 noted that invertibility recovers on the image, the world of values that remain after \(E\). The next construction promotes that world to a first-class citizen of the analysis. There, the founding claim of the theory — that AAT's conclusions factor through the layer of Atoms — is expected to become a theorem of the form "the two worlds carry essentially the same analysis." Mathematics calls the construction a Karoubi envelope, and this kind of equivalence a Morita equivalence.

**Conjecture B (an invariant finer than the cohomology class).** Swap the base, and the obstruction's cohomology class stays fixed; yet glueability can change. So there are differences the cohomology class cannot see. The next construction defines a finer invariant — a quantity that stays fixed no matter how things are presented — that captures those differences. The torsor classification of Section 5 is constructive evidence that such a quantity exists.

**Conjecture C (capturing the whole in finitely many parts).** The condition of Section 3 for concluding from finitely many parts looks like an instance of what topology calls compactness. The next construction carries the covering classification into topological language.

And beyond the three conjectures stands the summit theorem of the whole program: that the space of meanings is representable as what algebraic geometry calls a scheme, a space glued together from solution sets of equations. The calculus settled over these five weeks tells us what can be carried, which changes preserve comparisons, and what observation loses. The route to that summit will be drawn on this map.

## 12. Why "the Goddess of Plenty"

We named this family of theorems Annapurna.

On June 3, 1950, a French expedition led by Maurice Herzog stood on the summit of Annapurna in the Himalayas: the first ascent of an 8,000-meter peak in history. But Annapurna was not the mountain the expedition had set out to climb. That was Dhaulagiri, next door. After long reconnaissance, the team concluded there was no route up Dhaulagiri and switched objectives. The maps of the day were wrong; even the glaciers were misplaced. They had to begin by searching for the mountain they would climb. The price was paid on the way down, where severe frostbite cost the climbers fingers and toes. And Annapurna, in Sanskrit, means "she who is filled with food": the goddess of plenty, of harvests.

The mountain drawn on our map did not exist either. We navigated by the actual terrain instead, and turned refutations into the harvest. For these five weeks, no name could fit better.

Five weeks ago, the goal stood on the map. Now it is the map that has been redrawn, and the mountain actually climbed bears the name. The goddess smiled, not because the climb went according to plan, but because the map's mistake was turned into a harvest.

---

## Appendix: the full five-week record

| When | What was settled | Verdict | Cycles |
| --- | --- | --- | --- |
| 8/2 | Constructed instance of Atom transport (Gr2 reached) | proved | 16 |
| 8/2–8 | Locating where obstructions appear | proved | 5 |
| 8/2–8 | Constructibility of finite canonical resolutions | proved | 6 |
| 8/8 | Atlas theorem (resolution invariance) | proved | 31 |
| 8/11 | Structural covering invariance | **refuted** | 7 |
| 8/11 | Characterizing where uniform invariance fails | proved | 27 |
| 8/15 | Transport coherence | proved | 5 |
| 8/16 | Transport of geometric views | proved | 7 |
| 8/18 | Cross-level transport (Gr3 reached) | proved | 22 |
| 8/25 | The foundation: crossing bases and base change | proved | 111 |
| 8/26 | Classifying base-indexed operations | proved | 20 |
| 8/27 | Conditions for lifting from finitely many parts | proved | 8 |
| 8/28 | Conditions for diagnosis to survive transport | proved | 28 |
| 8/29 | Base change along refinements | proved | 4 |
| 9/1 | Lift to the upper level | proved | 84 |
| 9/4 | Gluing of disconnected configurations (the redesigned sixth card) | proved | 21 |
| 9/5 | Can normalization be bundled into one natural operation? | **refuted** | 4 |
| 9/6 | Transport of comparisons, and the information observation loses (the final theorem) | proved | 30 |

*Cycles* is the number of loop iterations to completion.

---

**Related**: [Atlas Theorem: How Far Can You Zoom Out?](https://blog.iroha1203.dev/atlas-theorem-how-far-can-you-zoom-out) / [The SAGA Theorem](https://blog.iroha1203.dev/the-saga-theorem)

**Repository**: [AlgebraicArchitectureTheoryV2](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2)
