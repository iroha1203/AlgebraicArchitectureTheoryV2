# Atlas Theorem: How Far Can You Zoom Out?

*Four refutations, 13,000 lines of Lean, and a proof that resolution doesn't change the diagnosis*

## TL;DR

- **Every time you analyze an architecture — at service, module, or method granularity — you are implicitly betting that the choice doesn't change what you find.** This article is about proving exactly when that bet is safe.
- AAT (Algebraic Architecture Theory) treats source code as the source of truth, abstracts implementations into Atoms, turns specifications into equations called laws, and analyzes architecture with the weapons of algebraic geometry. Defects appear as cohomology classes — algebraic fingerprints.
- Within AAT, an AI agent loop proved in Lean 4 what we call the **Atlas theorem**: for two adequate readings, one a coarsening of the other, satisfying a calibration condition C, the diagnostic fingerprints coincide exactly — zooming out loses no defects, zooming in fabricates none. Break the conditions and both failure modes really occur, with finite counterexamples.
- The agent **refuted its own target statement four times** before the summit. A no-go argument then showed that no shape-only condition can ever suffice, forcing the coefficient definition itself to be rebuilt. Five working days, 31 modules / 13,028 lines of Lean, four-lane adversarial review.
- The article walks from pixel art and the sampling theorem, through the four refutations and the discovered condition C, to what this means for code review in the era of AI-written code.

A photorealistic portrait and a 16×16 pixel-art sprite can show you the same face. Comics theorist Scott McCloud called this **amplification through simplification**: removing lines doesn't discard information, it sharpens the essence.

Can we say the same about software architecture diagnostics? **Look at your system at service granularity or at module granularity, and the same bugs show up in the same places** — not as a feeling, but as a proven guarantee.

This article is the record of proving that guarantee — we call it the **Atlas theorem** — in Lean 4. The AI agent that set out to prove it **refuted its own target statement four times**. Those four refutations turned out to be the best part. The protagonist here is not any proof technique. It is the discipline that accumulated refutations as results instead of writing them off as failures.

Everything below happened between August 4 and 8, 2026 — **five working days**.

| Round | What happened | What remained |
| --- | --- | --- |
| Refutation 1 | A forgotten "filling" lift | One new condition and a finite counterexample (937 lines of Lean) |
| Refutation 2 | Parallel lifts, overlooked | One more condition and a counterexample (622 lines) |
| Refutation 3 | A loop lifted to the wrong endpoints | Yet another condition and a counterexample (903 lines) |
| Pivot | **A no-go**: adding clauses can never be enough | A rebuilt definition of the coefficients |
| Refutation 4 | A spec hole in the revised requirements | A repaired declaration rule and a counterexample (433 lines) |
| Summit | Claims (i)–(v) all proved in 24 cycles | **31 modules / 13,028 lines** |

## The project

The subject is [AlgebraicArchitectureTheoryV2](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2). Take the source code as the source of truth; abstract the implementation into parts called Atoms; turn the specification into equations called laws. Treat architecture as geometry, and analyze it with the weapons of algebraic geometry. That is AAT (Algebraic Architecture Theory), and this monorepo is its formal verification in Lean 4.

The theory had a weak point that everyone had been politely ignoring: **granularity**.

Whenever you analyze an architecture, you implicitly choose a resolution. Services? Modules? Methods? If the diagnosis changes with that choice, then what is the diagnosis actually measuring — a property of the architecture, or **a convenience of the observer**?

There is a precedent for this problem: the Nyquist–Shannon sampling theorem. Sample too coarsely for the signal's bandwidth and **frequencies that don't exist appear** (aliasing) while **signals that do exist vanish**. The moiré stripes in a photograph are the visible face of the former. The granularity problem is the sampling problem of architecture diagnostics.

## Glossary

| Term | What it is |
| --- | --- |
| **reading** | The choice of resolution at which source code is cut into parts (Atoms). The equivalent of choosing the pixel count of a sprite |
| **diagnostic class** | The algebraic fingerprint of a defect. It is computed not inside any single file but as a **twist in how the parts glue together** (mathematically, a cohomology class `H¹`, defined below in "The stage"). Zero means consistent; nonzero means a defect |
| **adequate** | "The laws you want to state are expressible at this resolution." The formalization of the pixel artist's skill: keep exactly the distinctions the face needs |
| **comparison map** | The bridge that matches the diagnostics of the fine reading against the coarse one. If this bridge is an isomorphism (a one-to-one correspondence), diagnosis does not depend on resolution |
| **witness** | A claim's example or counterexample pinned down in Lean as **finite, concrete data**, not abstract argument |

## The claim — the Atlas theorem

**If a coarsening preserves enough information, then looking finely and looking coarsely detect exactly the same defect fingerprints — nothing appears, nothing disappears.**

> **The Atlas Theorem** (formally: the Diagnostic Resolution Invariance Theorem)
> Given two adequate readings, one a coarsening of the other, satisfying the calibration condition C, the comparison map is an isomorphism. **The choice of resolution does not change the diagnosis.** Measuring finer adds no diagnostics (the No-New-Diagnostics corollary); measuring coarser loses none.
> The counterpart: a coarsening that violates the conditions really does produce **defects that don't exist** or hide **defects that do** — with finite counterexamples.

In Lean, this is pinned down as a bundle of five claims: (i) the construction of the comparison map, (ii) its bijectivity, (iii) the corollary (measuring finer creates no new diagnostics), (iv) three counterexamples for broken conditions, and (v) a firing witness where all conditions hold and a nonzero diagnostic actually flows across the map. "Claims (i)–(v)" in the table above are these five.

### The stage — nerves, readings, coefficients

An observation of an architecture is represented as a **nerve**, a finite combinatorial structure. The vertices are **charts**: a part together with a declaration of the region it covers (its **support**). A dependency or overlap between two charts is an **edge**; a declaration that three charts have been checked consistent is a **face** (a triangle). The axioms demanded of a nerve are minimal: each face's three edges (its boundary triple) must meet at matching endpoints — for some charts `A, B, C` they line up as `e₀ : A → B`, `e₁ : A → C`, `e₂ : B → C`. That is all.

The choice of resolution is a **reading**. When one reading is a coarsening of another, a **factor map `π`** sending fine values to coarse values exists uniquely (the coarseness order and this factorization are imported wholesale from a theorem proved earlier in the same repository). The fine and coarse nerves are connected by a **nerve morphism `φ`** whose chart / edge / face correspondences commute with endpoints and boundaries. This is the formalization of "the sprite corresponds to the original portrait."

Coefficients are generated from laws. Each law in the law family is pushed through the reading (**descended**), and from the descended evaluation values, a generation contract called K0 / K1 (given in full below) builds a coefficient space over each cell, assembling a three-term complex:

```
C⁰ (on charts) --d₀--> C¹ (on edges) --d₁--> C² (on faces)
```

`d₀` takes "the difference of values at an edge's two endpoints"; `d₁` takes "the alternating sum over a face's three edges, `e₀ − e₁ + e₂`." Since `d₁ ∘ d₀ = 0` (this too is a theorem derived from the endpoint matching of faces, not an axiom), the **first cohomology**

```
H¹ = (1-cochains killed by d₁) / (image of d₀)
```

is defined. This is what "diagnostic class (fingerprint)" means. The intuition: every pair of adjacent parts is locally consistent, yet **going around a loop, the books don't balance**. Only that "twist" survives the quotient into `H¹`. That is why a defect's fingerprint lives not inside any single file but in the gluing structure.

Finally, the **comparison map**. From the nerve morphism `φ` and the descent-compatibility of the coefficients, a map of complexes (a cochain map) arises, inducing a map between the `H¹`s. The core claim (ii) of the Atlas theorem says: **under condition C, this induced map is a bijection**. Surjectivity means "coarsening hides no diagnostics"; injectivity means "coarsening fabricates no diagnostics."

The pixel-art metaphor from the opening is not decoration. It matches this structure part for part.

| Theorem side | Perception side |
| --- | --- |
| The invariance theorem | The sprite shows the same face |
| adequacy | The pixel artist's skill (keep only the distinctions that matter) |
| False-positive counterexample | Pareidolia (a face in the clouds) |
| Hidden-defect counterexample | The expression lost at too low a resolution |
| Violating calibration condition C | Moiré / aliasing |
| Law-relativity | A sprite good enough for face recognition, but not for reading small print |

The art historian Ernst Gombrich argued that a picture is only half drawn — the viewer supplies the rest — and called that contribution **the beholder's share**. Translated into AAT: what stays invariant across resolutions is not the picture (the code) itself, but **what the beholder evaluates from it** — formalized, the law family. That is exactly why the invariance is law-relative.

And you have met this "beholder" before: **a veteran engineer doing code review**. An experienced reviewer does not read every line at the same magnification. Checking API compatibility, they read at interface granularity; hunting a race condition, they drop to individual lines. **They switch reading resolution according to the property they are checking.** Choosing the right review granularity is, today, a skill that lives in experience and intuition. The Atlas theorem is a first step toward making that granularity mathematically tractable: it gives the question "how coarsely can I read without losing information about this property?" a rigorous footing for the first time.

But the human eye — and the veteran's intuition — does all of this **without a guarantee**. That is why clouds have faces in them, and why reviews miss things. The question this theorem asked was: under what conditions does the guarantee hold? And the identity of that condition — calibration condition C — **was unknown to everyone at the start**. The requirements document (the research card that froze the proof target) said so from day one: "If C holds trivially, the theorem is a restatement. If C is too strong, the theorem is empty. **The identity of C is the substance of the theorem.**"

So it proved. Four times.

## Refutation rounds 1–3: whack-a-mole

The proof ran as an autonomous AI agent loop. The human (me) froze the requirements document and did nothing but adjudicate. The agent does not stop until it has pinned either a proof or a refutation in Lean. The three rounds below are what the loop brought back early on. All three are refutations.

### Refutation 1: the forgotten filling

The first candidate conditions, C0–C3 (the original four), looked only at the correspondence of points (charts) and lines (dependencies). The counterexample the agent found: on the coarse map, some loop is a **filled-in triangle** — a face declaring "checked, no problem" has been glued over it. Lift it to the fine map, and there is only the outline. No filling. **A defect fingerprint that vanishes on the coarse side survives on the fine side.** The comparison map has no way to be an isomorphism.

The counterexample was pinned as 937 lines of Lean, and a condition was added: fillings must lift too (C4).

> **Condition gained, C4 (plain form)**: every coarse face has at least one fine face mapping to it under the nerve morphism's face correspondence.

### Refutation 2: parallel lifts

C0–C4, with the new C4, was broken next. A single road on the coarse map can correspond to **two parallel roads** on the fine map. All of C0–C4 hold, yet the thin loop between the two parallel roads leaves a new fingerprint that exists only on the fine side. Nothing constrained **multiple lifts landing on the same coarse road**. Uniqueness of lifts (C5) was added.

> **Condition gained, C5 (plain form)**: at most one fine edge maps to each coarse edge (together with the existing existence clause C2: exactly one).

### Refutation 3: the displaced loop

C0–C5 fell as well. This time, a **loop** on the coarse map — a road that returns to its own starting point. Its unique lift connected **two different intersections** on the fine map. A nonzero fingerprint on the coarse side then vanishes on the fine side. Refutations 1 and 2 broke surjectivity (the coarse side misses diagnostics); this one breaks injectivity (the coarse side alone sees a phantom diagnostic). What was needed: a road that returns to itself must lift to a road that returns to itself (candidate C6).

> **Condition gained, C6 (plain form)**: every fine edge mapping to a coarse self-loop (an edge whose two endpoints are the same chart) is itself a self-loop.

Three rounds in, a bad feeling was taking shape. **Every added clause exposed another hole.** Would this ever converge?

One decision made at the very start was paying off. Every refutation is pinned as a **finite counterexample in a Lean file**, not spent as a one-off rebuttal. These files would later be incorporated into the theorem's counterexample part — the proof that "break the conditions and this is how it fails." Not one refutation was wasted.

## The pivot — a no-go that stopped the loop

Here the human's turn came. The ruling: **stop the clause-adding loop.** Instead, dispatch a separate computational search (a "hunt") to test candidate conditions exhaustively — with three stopping conditions fixed in advance.

- **A (success)**: a condition is found that excludes the three known counterexamples and admits no new ones within the search range
- **B (structural negation)**: it is shown that **no such condition can exist in principle**
- **C (stall)**: progress stops in either direction

The result was **B**. And not as a product of the search itself, but through a single argument discovered while designing it. **The conditions were not lacking. The language for writing conditions was.** That is what came to light.

The argument is called **two-point separation**. On one and the same shape (the same configuration of points, lines, and faces — the same incidence), you can build three worlds that differ only in their coefficient data.

| World | Comparison map |
| --- | --- |
| Every coefficient dimension is 1 | Isomorphism ✅ |
| Some coefficients zeroed out (a support hole) | Not injective ❌ |
| Fine-side coefficients doubled | Not surjective ❌ |

But every condition candidate considered so far — C0–C5, C6, even candidates imported from category-theory textbooks — was a predicate **computed from the shape alone**. Same shape, no way to distinguish. So any shape-only condition that accepts even one genuine positive example must also accept its impostors with the same face. **No matter how cleverly you keep adding clauses, the answer is not in this language.**

In sampling-theorem terms: arrange your sampling grid however ingeniously you like — **without declaring the signal's bandwidth (the coefficients), no guarantee against aliasing can even be written down**.

From this point, a **coefficient generation contract (K0/K1)** was introduced — coefficients must be generated from law evaluation values by a unique rule — and condition C was relativized to per-coordinate sub-maps (subnerves) of the coefficients. What matters is that this redefinition was not a matter of taste. Given the no-go, **there was no other way**. The definition was not designed. It was discovered.

### The discovered language — the coefficient contract K0 / K1 and condition C in full

The coefficient side first.

**K1 (derived supports)**. Only charts may declare a support (a covered region). An edge's support is derived as the intersection of its two endpoint charts' supports; a face's support as the intersection of its three boundary edges'. Allow independent support declarations per cell, and the no-go's "support hole" — zeroing out just one edge's coefficients by hand — becomes constructible. So the freedom to declare is itself removed.

**K0 (generated coefficients)**. The coefficient field is fixed to `ℚ`. Each cell's coefficient coordinates are pairs `(law, value)`, where the values are the **distinct** values the descended law evaluation takes on the cell's support, each with multiplicity one. Indexing by occurrence counts or support sizes is not permitted — this kills the no-go's "duplication." The spaces in each degree are

```
C⁰ = ℚ-valued functions on {(chart, law, value)}
C¹ = ℚ-valued functions on {(edge, law, value)}
C² = ℚ-valued functions on {(face, law, value)}
```

and the differentials are generated coordinate-wise: the `(edge, law, value)` component of `d₀` is the difference of the two endpoint charts' matching `(law, value)` components; the `(face, law, value)` component of `d₁` is the alternating sum `e₀ − e₁ + e₂` over the boundary triple. Matching labels correspond identically; absent labels give zero. **No other coordinate correspondence is generated.** `d₁ ∘ d₀ = 0` is derived as a theorem by per-label computation from the endpoint matching of faces, never assumed. The comparison map's coefficient part is likewise not declared but generated, as the identity on `(law, value)` from the `π`-compatibility of descent. Adding, duplicating, or omitting coordinates is forbidden across the board. The word "contract" is meant literally: the substance of this language is how little it lets you declare.

**Coordinate subnerves and relativization**. For each coefficient coordinate `(law, value)`, the cells carrying that coordinate (the cells on whose derived support the descended evaluation takes that value) form a sub-nerve, the **coordinate subnerve**. Under K0/K1, `H¹` and the comparison map **decompose as direct sums** over coordinates, and each block reduces to a one-dimensional constant-coefficient comparison over its subnerve. This decomposition is the mathematical justification for relativizing: the geometric conditions C1–C4 need only be imposed per coordinate subnerve, while the global C0, C5, C6 are imposed on the whole nerve.

With that, condition C in full:

- **C0 (cover-image agreement)**: each coarse chart's support equals the union of the `π`-images of the supports of the fine charts in its fiber
- **C1 (fiber connectivity)**: in each coordinate subnerve, each coarse chart's fiber graph (the fine charts mapping to it, plus the fine edges staying within the fiber) is nonempty and connected
- **C2 (edge-lift existence)**: in each coordinate subnerve, every coarse edge has a lift within the subnerve
- **C3 (local fiber acyclicity)**: in each coordinate subnerve, every rational 1-cycle on a fiber graph is spanned by `ℚ`-linear combinations of boundaries of fine faces whose boundary edges all lie in the fiber. A local condition, equivalent to the vanishing of the fiber's first homology
- **C4 (coarse-face lift)**: in each coordinate subnerve, every coarse face has at least one fine face mapping to it — **the spoils of refutation 1**
- **C5 (unique coarse-edge lift)**: each coarse edge's `φ`-fiber has at most one element; with C2, exactly one — **the spoils of refutation 2**
- **C6 (self-loop endpoint reflection)**: every fine edge mapping to a coarse self-loop is itself a self-loop — **the spoils of refutation 3**

Finally, the condition list carries a **prohibition rule**. C may not contain any clause equivalent — or close to equivalent, even one-directionally — to "the comparison map is an isomorphism" or "one side's `H¹` vanishes." That would smuggle the conclusion into the hypotheses. The single explicit exception is C3, a local condition that sees only the internal data of individual fibers, the analogue of the Leray-type local acyclicity assumptions imposed on covers in classical Čech theory. The boundary between legitimate assumption and smuggling is itself fixed as part of the condition list — because the prover is an AI agent. Escape routes are closed at the specification.

## Refutation 4, and the summit

The loop restarted on the revised specification and, after a few cycles of groundwork, the agent attacked **a spec hole in the revision itself** (refutation 4). A nerve morphism may declare fine edges and faces with no coarse counterpart as "unmapped (degenerate)." The declaration rule had a hole: the condition for declaring a face unmapped did not require the same declaration of the three edges around it. In the counterexample exploiting the hole, the construction of the comparison map (claim (i)) itself fails. Pinned in 433 lines, repaired by making the declaration **hereditary**: a face may be declared unmapped only if its three boundary edges are already declared unmapped.

From there it was a straight run. Restarted once more after the repair, the loop reached the top in 24 iterations (cycles).

### The route to the top — structure of the proof

**Stage one: block decomposition.** Under the K0/K1 generation rules, prove as theorems that the complexes, `H¹`, and the comparison map decompose as direct sums over the coefficient coordinates `(law, value)`. Each block reduces to a **one-dimensional constant-coefficient** comparison over its coordinate subnerve. The global problem splits into a direct sum of the simplest possible pieces. From here on, attack block by block.

**Stage two: injectivity.** Analyze the kernel of the block comparison map and show that a nonzero coarse diagnostic class cannot die on the fine side. This is where C6 earns its keep — it closes the accident path found by refutation 3, where a nonzero coarse class evaporates below. (Refutation 4's hereditarity works earlier still, underwriting the very constructibility of the comparison map.)

**Stage three: surjectivity (the crux).** Show every fine diagnostic class comes from a coarse one. Four moves:

1. A **discrete Stokes theorem** translating C3 into "the vanishing of periods around fiber loops." Local face-filling becomes an analysis-flavored statement about loop integrals vanishing
2. From vanishing periods, construct a **primitive** on each fiber — the finite-graph version of "a curl-free field has a potential"
3. Express the primitive-normalized residue as a coarse 1-cochain, using the "exactly one lift" channel provided by C2 / C5 (**descent**)
4. Use C4's face lifts to check the 1-cochain is a cocycle on the coarse side, and promote it. Surjectivity closes

**Stage four: main theorem and corollary.** Bundle the block bijections along the direct-sum decomposition into the global bijection — claim (ii). As a consequence, measuring finer creates no new diagnostic classes: the No-New-Diagnostics corollary, claim (iii).

**Stage five: counterexamples and firing.** The three counterexamples of inadequate coarsening — fabricated diagnostics, hidden diagnostics, and broken condition C (claim (iv); the legacy of the refutation rounds becomes the material here) — plus a single firing witness where every condition holds simultaneously and a nonzero diagnostic class actually flows across the comparison map (claim (v)). Without (v), the theorem could be hollow — "no example satisfying condition C actually exists" — and the concrete Lean data forecloses that.

The division of labor among the conditions is clean. **C3 kills local loops; C2 / C5 provide the unique communication channel for lifts; C4 carries the consistency of faces; C6 and hereditarity prevent the self-loop and degenerate-declaration accidents; C0 / C1 lay the ground.** Every clause won through refutation is used at a specific step of the injectivity or surjectivity proof. There are no ornamental clauses.

The final artifact: **31 Lean modules, 13,028 lines**. Every new declaration depends on standard axioms only — no `sorry`, no added axioms. Acceptance ran through an **independent adversarial review** in four lanes (two mathematics, two Lean), all reporting "no major findings," plus a separate completion audit that includes checks for proof cheat-routes.

## Operating discipline for AI agents

This project's operating principle for AI has been constant: **give the AI no cheap way out**. For mathematical research, it became this division of roles: **the human only adjudicates** (freezing the spec, approving revisions, designing stopping conditions); **an implementation agent runs the proof loop; a review agent runs adversarial review**.

Six rules carried those five days.

1. **Refutations are first-class.** "A refutation is a legitimate result" was written into the requirements document in advance. So four refutations became accumulation rather than demoralization, and the counterexamples were incorporated into the theorem itself
2. **Declare the crux up front.** "The identity of C is the substance of the theorem" was written at the start — so each refutation read as "one more piece of the substance unearthed," not as failure
3. **Freeze the specification.** The requirements document does not change while the loop runs; revisions go through human adjudication and independent review. Because the goalposts cannot move, a refutation means what it says
4. **Pair every clause with a firing requirement.** Each added condition brings a matching witness requirement that the condition actually does work somewhere. This closes the path where a theorem hollows out under layers of protective clauses
5. **Switch to diagnosing the language.** After three rounds of clause-adding, the question changed from "which clause is missing?" to "can this language express the answer at all?" The no-go is the product of that switch
6. **Multi-lane adversarial review.** Agents other than the implementer review the work in independent mathematics and Lean lanes, structurally removing the incentive to declare victory

We stepped on every one of these traps, repeatedly. The rules are what came out.

## Honest limits

- The result stands at **machine verification in Lean plus internal multi-lane review**. External peer review (journal submission) is ahead; a paper is in preparation
- The theorem is a statement about finite models over a fixed coefficient field. Condition C is sufficient; a general characterization of necessity is explicitly left open
- "The diagnosis is invariant," not "the observation is invariant." A coarse reading does not make the raw observations look the same; the claim is that the fingerprints of what the laws evaluate coincide

## Why "Atlas"

An atlas is a book of maps drawing the same world at different scales. Open any page and the same country is there. That is what this theorem says.

The name comes from inside the theory, not from marketing. AAT's canonical text has long had the vocabulary **chart atlas** — a cover as a collection of charts — including the very phrase "when the chart atlas changes." The Atlas theorem is, literally, the invariance of diagnosis under change of chart atlas. There is a mathematical coincidence too: that a manifold's identity does not depend on the choice of atlas is the first invariance principle you meet in differential geometry.

The next step is already fixed. Re-measure a real microservice system at three granularities — service, module, method — and observe that diagnostics stay stable within the adequate range, and that fabricated and hidden defects really appear when adequacy breaks. A **resolution sweep**: the theorem and its counterexample pairs replayed on real data. The guarantee that the sprite shows the same face as the portrait — this time on a production codebase.

One last thing: why this theorem, now. In the era of AI-written code, the bottleneck of development has moved from generation to review. AI agents write faster than humans can review line by line, and **"how coarsely can we afford to read?" has become the question that sets the throughput of a development pipeline.** The only way review scales is to read at coarser resolution — and until now there was no guarantee that coarseness doesn't distort the diagnosis. The Atlas theorem is a first step toward that guarantee, asked and answered as a theorem. And not by coincidence, the theorem itself was proved in the middle of the same problem — "how do humans accept AI output produced at full speed?" — held up by the operational answer of multi-lane review and audits. Operations and mathematics are digging at the same bottleneck from opposite sides.

The full history — theory, proofs, counterexamples, audits — is in the public repository: [AlgebraicArchitectureTheoryV2](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2)

---

*As of this writing, the theorem's Lean proofs, counterexamples, and completion audits are all reproducible from the repository. Questions and objections welcome.*
