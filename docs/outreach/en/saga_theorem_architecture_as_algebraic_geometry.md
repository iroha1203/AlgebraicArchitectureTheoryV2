# The SAGA Theorem: The Day Software Architecture Became Genuine Algebraic Geometry

## TL;DR

- **Every module passes review, yet the system as a whole is broken.** This "locally correct, globally inconsistent" phenomenon has a name in mathematics: cohomology, specifically `H^1`.
- AAT (Algebraic Architecture Theory) treats software architecture as a geometric object: generated from axiomatized facts called Atoms, cut out by laws, with obstructions appearing as cohomology classes.
- Within AAT, the **SAGA theorem** (SAGA Grounding Theorem) has now been proved in Lean 4. It is a comparison theorem: the `H^1` grown on the architecture-semantics side coincides with the genuine Čech `H^1` of the site generated from Atoms.
- The proof took 352 cycles. For 347 of them, an automated AI loop accumulated impossibility theorems saying "this vocabulary cannot prove it" — until a single vocabulary shift, **laws are equations, not predicates**, broke the rock face in the final 5 cycles.
- This article assumes no prior knowledge of AAT. We start from what AAT is, walk through the Atom axioms and the algebraic-geometry dictionary, and end with what the SAGA theorem says, how it was proved, and why it matters for computer science.

## 1. Locally correct, globally broken

You have probably seen this before.

- Every team's code satisfies its own review standards. Integrated, the system fails.
- Each microservice honors its contract. The system-wide invariant is still violated.
- Every refactoring step was safe. Stacked together, the original design intent is gone.

Linters, static analysis, and dependency graphs are good at finding *local* violations. But none of the situations above contain one. The problem lives not in any individual part but in how the parts are *glued together*.

Mathematics has studied exactly this phenomenon — locally consistent data that fails to glue globally — for the better part of a century. The theory of sheaves and cohomology. The obstruction to gluing a family of local data into global data appears as an element of a cohomology group called `H^1`. If the class is zero, the pieces glue. If it is nonzero, you are facing the kind of failure **whose cause cannot be found by inspecting any single part**.

AAT is a theory that takes this mathematics and runs it, seriously, on software architecture.

## 2. What is AAT? Architecture as relative geometry

The starting point of AAT (Algebraic Architecture Theory) is its choice of object. AAT does not study the raw codebase itself.

```text
C : Codebase
V : AtomVocabulary   (which facts you choose to observe)
U : LawUniverse      (which laws you choose to impose)
J : CoverageTopology (how you cover the architecture with local views)
k : coefficient ring (what you measure obstructions in)

X_C^{V,U,J,k} : AAT geometry   (this is the object of the theory)
```

Instead of asking "is this codebase good?", AAT asks: **given this observation vocabulary, these laws, and this way of covering the system with local views, what geometry arises?** The vocabulary and the laws are explicit, and all mathematics is relative to them. This relativization is also where AAT's discipline of boundaries comes from — internally the project calls it "silence about what cannot be spoken": the theory does not make claims outside its declared inputs.

## 3. The Atom axioms — the minimal facts of architecture

The smallest unit of AAT is the **Atom**: a typed architectural fact that we choose not to decompose further. An Atom has five components:

```text
a = (kind, axis, subject, predicate, payload)
```

- `kind`: what species of fact this is (component, relation, contract, semantic fact, ...)
- `axis`: which structural axis it concerns
- `subject`: what it is about
- `predicate`: what holds
- `payload`: the content — values, names, types, evidence

"Service A depends on service B." "This module owns the compensation logic for payments." "This API requires authentication." All of these are Atoms. Syntactic facts and semantic responsibilities live on the same footing.

Atoms are governed by an axiom system (A0–A8). The most important ones:

- **A0 Primitive Existence**: the type of Atoms exists; everything is generated from it.
- **A2 Single Fact**: one Atom states one fact. Compound claims are families (configurations) of Atoms.
- **A3 Predicate Stability**: Atom identity is determined by the five components.
- **A4 Composition**: finite families of Atoms generate configurations, from which architecture objects arise.
- **A5 Law Non-Generation**: **laws do not generate Atoms.** A law is a constraint over facts, never a source of facts.

A5 is quietly crucial. It separates "what should be" (laws) from "what was observed" (Atoms) at the axiom level, so wishful thinking can never leak into observation.

## 4. Making laws into equations — the algebraic-geometry dictionary

On top of Atom families we impose **laws**: "no dependency cycles," "every compensation handler must be paired," and so on.

Naively, a law is a predicate — it holds or it does not. And indeed, Part I of AAT first defines laws exactly that way.

But algebraic geometry discovered a better viewpoint 150 years ago: treat constraints not as *predicates* but as **equations**.

The basic dictionary of algebraic geometry:

```text
a set of equations        →  an ideal (the algebraic object the equations generate)
points satisfying them    →  the zero locus V(I) (the geometric object)
functions visible under
the constraints           →  the quotient ring O/I
```

The key point: **a predicate (satisfied / not satisfied) cannot recover the equations.** As Hilbert's Nullstellensatz made precise, the equation side (the ideal) carries strictly more structure than the solution set — multiplicities, infinitesimals, deformations. And **that extra structure is exactly what you need to compute cohomology.** No coefficients, no cohomology; predicates have no coefficients.

AAT transplants this dictionary to architecture:

```text
a law                      →  the witness ideal I_L generated by its violation coordinates
the failure of all laws    →  the obstruction ideal I_Ob = Σ I_L
readings under the laws    →  the quotient O/I_Ob (the coefficients of the obstruction sheaf)
the law holds              ⟺  pulling the reading back kills the ideal (s*I_Ob = 0)
```

Note that the last line has exactly the shape of Hilbert's Nullstellensatz: the semantic fact "the law holds" becomes equivalent to the algebraic fact "the ideal vanishes." This is why AAT is algebraic geometry, not merely algebraic-geometry-*flavored*.

Then we add coverings. Cover the architecture with a family of contexts and observe locally in each. A Grothendieck topology is generated from the Atoms on the category of contexts, giving a **site**. Sheaves live on it, and Čech cohomology. The obstruction to gluing a family of local repair certificates into a global one appears as a class in `H^1`.

## 5. Before SAGA — the lower floors of the tower

The AAT research program has been turning this picture into Lean 4 theorems, one floor at a time.

- **The finite descent theorem (G-02)**: a family of local repairs glues into a global repair exactly when a finite obstruction class vanishes. The first theorem ever attached to "local-pass / global-fail."
- **The true H¹ theorem (G-05)**: that obstruction class is not an `H^1` in name only, but a genuine quotient `H^1 = Z^1/B^1` — cocycles modulo coboundaries.

At this point AAT was a theory that measures architectural gluing failures with `H^1`. But one fundamental weakness remained.

That `H^1` was a **purpose-built finite construction**. The general theory of sites and sheaves was formalized in the very same repository — yet the semantic-repair `H^1` stood next to it as a separately grafted tower. The claim "AAT is doing algebraic geometry" rested on "AAT owns a construction shaped like algebraic geometry." In principle, that is indistinguishable from calling any ad hoc finite quotient an `H^1`.

## 6. The SAGA theorem — two worlds coincide

This is what goal G-06 — later named the **SAGA theorem** — set out to fix. In one sentence:

> **The semantic repair `H^1`, grown on the architecture-semantics side, is an instance of the general theory's cover-relative Čech `H^1`, on the site generated from Atoms, with coefficients generated from laws. The two zero-tests are equivalent.**

The name honors Serre's **GAGA** (*Géométrie Algébrique et Géométrie Analytique*), the landmark comparison theorem showing that the cohomologies of two worlds — algebraic and analytic geometry — coincide. SAGA (**S**émantique **A**rchitecturale, **G**éométrie **A**lgébrique) is a comparison theorem in that tradition, for architectural semantics and algebraic geometry. And the name carries a second meaning: the proof was, quite literally, a *saga*.

With SAGA proved, the whole chain connects:

```text
Atoms (axiomatized facts)
  → laws as equations (witness ideals)
  → obstruction coefficients as the quotient O/I_Ob
  → the site and covers generated from Atoms
  → the general theory's Čech H^1
  = the semantic repair H^1 (G-05)
```

**AAT's cohomology grows out of AAT's own axioms.** No grafting.

## 7. The story of the proof — 347 impossibility theorems and one decision

The proof of SAGA is a research record worth telling in its own right.

It ran for 352 cycles. An automated AI agent loop discharged small proof obligations in Lean, one per cycle. Every cycle passed adversarial audits designed to reject the classic cheat of formalization: smuggling a conclusion-equivalent premise into the assumptions.

### Compression and blockade

The first hundred or so cycles built the comparison skeleton. Then, for roughly 250 cycles, something strange happened: instead of advancing, the loop began **sealing off every detour, with counterexamples**. "This input surface cannot prove it." "Adding this auxiliary data does not help either." Thirty-six families of impossibility boundaries accumulated as theorems, until the entire goal had been compressed into a single proposition. And in cycles 320–347, the loop proved that this one point was **underivable, in principle, from the current vocabulary**.

The cause was fundamental. Laws had been formalized as `holds : Prop` — an opaque predicate. Predicates do not determine equations. Cohomology does not grow where there are no coefficients. The algebraic-geometry lesson of Section 4 had come back as a family of impossibility theorems in Lean.

Were those 347 cycles wasted? The opposite. **The theory established the limits of its own vocabulary, as theorems, before extending it.** The fix was narrowed from "somewhere" to "exactly here." There are not many formalization projects that have done this.

### The vocabulary decision

At this point a human made the call: **"Laws are equations. That is precisely why AAT can become algebraic geometry."**

Remarkably, the mathematics needed for the extension already existed in the repository. Part III of the AAT canon (law algebra) had contained the theory of violation coordinates, witness ideals, and the lawful locus all along — the formalized research surface simply had not used it. The decision was not the invention of new mathematics; it was **letting the formalization catch up with the editorial intent of the text**.

Once the vocabulary changed, things moved fast. Generate the obstruction coefficients as the quotient by the ideal; generate each local reading as the quotient class of its defect. Then the proposition that had been sealed for 347 cycles — *if the required laws hold locally, the restrictions of the readings agree on common refinements* — **fell as a theorem**. Five cycles later, everything was in place: the comparison, the equivalence of zero-tests, and a concrete instance where a nonzero class demonstrably lives on both sides.

### A review that produced theorems

The final act was the review. Just before completion, one of the four adversarial review lanes vetoed: "the `H^1`-zero part of this composed theorem is constructively trivial, and the law semantics only acts at cohomological degree 0 — the statement invites over-reading." The objection was correct.

The response was not to weaken the claim but to prove **new theorems**: a positive boundary theorem ("the law semantics contributes exactly degree-0 vanishing") and a negative one ("the higher conclusions hold independently of the laws"). The theory deepened its knowledge of itself through the review. The re-review lifted the veto, and the theorem was accepted.

## 8. Why this matters for computer science

This looks like a mathematics story, but SAGA has several CS implications.

**(1) A class of analysis beyond linting.** Detecting local violations (lint, static analysis, contract checking) and detecting global gluing failures are mathematically different classes of problems. After SAGA, AAT owns, for the second class, an obstruction with a *proved-sound detector*: a nonzero `H^1` class certifies which law fails over which observed facts, with traceability back to the displayed law support. It is a principled path toward detecting the failure mode where "no file contains a bug, and yet the system is broken."

**(2) A methodology for vocabulary evolution in formalization.** Every large formalization eventually hits the "our original definitions were wrong" problem. The SAGA proof demonstrates one pattern: first pin down the limits of the old vocabulary as a family of impossibility theorems, so that the extension becomes a *forced, minimal move* — and afterwards, the old no-go theorems keep serving as audit machinery. Definition change becomes accretion, not restart.

**(3) A working example of human–AI division of labor.** 347 cycles of automated exploration and blockade; one human vocabulary decision; adversarial multi-agent review with a veto and a re-review. Remove any one of the three and this theorem does not exist in this form. As a template for doing mathematics with AI, the record is arguably as valuable as the theorem.

**(4) Everything is machine-checked.** Every theorem in this story — the comparison, the impossibility boundaries, the nonzero-class instance — compiles in Lean 4 and depends only on Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`). There are no `sorry`s.

## 9. Honest boundaries

Following AAT's own discipline, here is what the SAGA theorem does **not** claim.

- The theorem is relativized to finite or small sites, selected covers, and vocabularies equipped with an equational realization of their laws. No unconditional generalization to arbitrary Grothendieck sites is claimed.
- No unconditional identification of cover-relative Čech `H^1` with full sheaf cohomology is claimed — in fact, "this cannot be said unconditionally" is itself a boundary theorem with a counterexample.
- The completeness of extracting Atoms from a codebase, and "quality judgments about real code as a whole," are outside the theory. AAT does mathematics relative to observed Atoms and selected laws.

Not saying what cannot be said is a design principle of the theory, so an outreach article should honor it too.

## 10. Closing

Anyone can say "let's apply algebraic geometry to software architecture" as a metaphor. What the SAGA theorem did was stop it being a metaphor. From the Atom axioms, through laws as equations, obstruction coefficients as quotients, sites, sheaves, and up to `H^1` — everything is connected by a single chain of machine-checked theorems.

That old phenomenon — locally correct, globally broken — now has mathematics that grows out of axioms.

## References

- Repository: [AlgebraicArchitectureTheoryV2](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2) (MIT license)
- Proof record of the SAGA theorem: `docs/note/aat_saga_theorem_proof_record.md`
- The AAT mathematical canon: `docs/aat/algebraic_geometric_theory/`
- Research goal ledger: `research/GOALS.md`; proof-state ledger: `research/reports/G-aat-quality-surface-06.md`
- Lean artifacts: `Formal/AG/Research/QualitySurface/` (for SAGA, see `SemanticRepairCechGrounding.lean` and `SemanticRepairLawEquation*.lean`)
