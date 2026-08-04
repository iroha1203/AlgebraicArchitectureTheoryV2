# SAGA's Cape of Good Hope: The One Cent That Cohomology Caught

## TL;DR

- This is the sequel to [the SAGA theorem article](https://blog.iroha1203.dev/the-saga-theorem). Last time, I gave the "locally correct, globally broken" phenomenon a theorem, proved in Lean 4. This time I took that theorem out into the real world.
- In a real microservice system that nobody wrote with the theory in mind — the research benchmark [train-ticket](https://github.com/FudanSELab/train-ticket) — the exact structure required by the theorem's hypotheses turned out to exist.
- Every service follows its own money convention perfectly. Yet a sub-cent refund remainder vanishes without being booked anywhere in the system. The measurement returns both verdicts at once, and a repair plan flips the CI gate from BLOCKED to PASS.
- The find itself is almost comically mundane. But the value was never the find. It is the confirmation that the sea route exists.

## 0. The story so far

For readers new to the series: the goal of this project is to move software architecture from something discussed with diagrams, folklore, and review-time taste to a mathematical object studied with definitions, theorems, counterexamples, and certificates.

| Name | What it is |
| --- | --- |
| **AAT** (Algebraic Architecture Theory) | An algebraic-geometric theory of software architecture. On top of typed minimal facts read from code (**Atoms**), it imposes the conventions that should hold as equations (**laws**), and treats an architecture as the geometry of the solutions |
| **The SAGA theorem** | AAT's central result. A comparison theorem establishing that the question "do the local repairs glue into one global repair?" is computable as the vanishing of a quantity called cohomology `H^1`. Machine-verified in Lean 4. The name is an homage to the GAGA theorem in algebraic geometry — it has nothing to do with the distributed-transaction Saga pattern |
| **ArchSig** | A Rust measurement tool built on AAT. Given observation data (an ArchMap) and laws, it decides gluing obstructions by finite computation and returns certificate-backed conclusions. An instrument, not a grader |
| **Lean** | A theorem prover. AAT's theorems are machine-checked here |

The previous article ended with the proof of the SAGA theorem. The theorem is true. One question remained: does the structure its hypotheses describe exist in real code? This article is that report. If you have been following the series, feel free to skip ahead.

## 1. The Lean proof is done. But does it apply to real software?

The SAGA theorem is proved in Lean 4. No `sorry` (Lean's placeholder for an unfinished proof), and the only axioms are Lean's standard ones. Whether the theorem is *correct* is no longer a question.

The question that remained is this one: **does the structure its hypotheses require exist in real software?**

However correctly proved, a theorem whose hypotheses are satisfied only inside mathematics quietly swings at nothing in the real world. Here is the bundle of hypotheses, in plain words. From now on I will call each service a "chart" and the convention a service imposes on itself its "law". Every chart obeys its own law. Values are handed between charts. And yet, when you follow the handoffs around a closed loop, a discrepancy remains that has nowhere to be reconciled. The quantity that counts this "discrepancy that survives a full loop" is the cohomology `H^1` that starred in the previous article.

This bundle could, in the worst case, have been a structure that only assembles in artificial examples. The one-cent demo I published — a small Rust sample deliberately engineered so that a one-cent rounding discrepancy goes missing between modules — demonstrates that *this structure produces the obstruction*. It does not demonstrate that *this structure occurs in reality*. Only real data can show that. So I measured an external OSS codebase end to end, using exactly the workflow a real user would. Dogfooding.

What the discovery of the Cape of Good Hope meant was not "we reached India". It meant "the sea route exists". That is precisely what this experiment set out to check. Is AAT a sea that exists only inside mathematics, or does it connect to the sea of real code? Hence the name of this report: SAGA's Cape of Good Hope.

## 2. The experiment: measuring an external OSS the regular way

The target is [FudanSELab/train-ticket](https://github.com/FudanSELab/train-ticket), a standard benchmark for microservice research, built from surveys of industrial systems. It consists of 40-plus Java microservices with ordering, payment, refund, and consignment flows. The repository is roughly 500,000 lines including frontend assets; the measured target is the Java implementation proper, about 28.5 kLOC. What mattered was that this codebase knows nothing about my theory.

The measurement had two stages.

**Stage 1 (a full build of the observation data).** From the Java sources of 42 services plus a shared module, I built an ArchMap — the map of minimal observed facts (Atoms) read from the code — through the regular workflow: two independent reading passes, full adjudication of every disagreement, then an audit. The result: 2,118 Atoms across 43 observation units (contexts). All reading was done by lightweight-model subagents (Claude Sonnet), at a measured supply cost of about 4.1 minutes/kLOC (wall clock, parallel runs included).

Already at this stage, the map showed 8 distinct styles of carrying money coexisting across the 24 services observed for that convention: double fields, strings passed through untouched, BigDecimal parsed at the point of use, string concatenation. Each works fine on its own.

**Stage 2 (SAGA).** On top of the full build, I extended the laws to the full SAGA diagnostic stack and walked the staircase end to end. This is the main act.

## 3. The discovery: the vanishing-cent structure exists in real code

Digging through the real call graph of the full build, this structure emerged.

**Three services — cancel (refunds), inside-payment, and order — form a triangle of actual calls, and the money convention disagrees on all three edges.**

The three conventions can be confirmed in the sources (commit `313886e9`).

First, order. The price is stored as a raw string.

```java
// ts-order-service: Order.java
private String price;
```

Next, inside-payment. Balance arithmetic parses that string into BigDecimal and computes exactly.

```java
// ts-inside-payment-service: InsidePaymentServiceImpl.java
totalExpand = totalExpand.add(new BigDecimal(order.getPrice()));
```

And cancel. The refund computation parses the same string into a double, multiplies by 0.8, rounds to two decimals, and stringifies again.

```java
// ts-cancel-service: CancelServiceImpl.calculateRefund
double totalPrice = Double.parseDouble(order.getPrice());
double price = totalPrice * 0.8;
DecimalFormat priceFormat = new java.text.DecimalFormat("0.00");
String str = priceFormat.format(price);
```

So one and the same "order price" travels through three different worlds: untouched string / exact decimal arithmetic / floating point plus rounding. Whenever 0.8 × price does not land on two decimal places (say 91.33 × 0.8 = 73.064), the sub-cent remainder created by rounding appears in no service's books.

And here is the decisive part. **Nowhere in the measured Java sources is there code that reconciles the three services' money at once.** The pairwise handoffs exist: cancel reads the price from order, cancel sends the refund to inside-payment, inside-payment reads the price from order. But there is no place where all three are checked together.

In the language of the previous article: the three mismatched edges form a closed loop, and the face that would fill it — the membrane sealing the inside of the triangle, i.e. a site where the three are reconciled simultaneously — is missing. This is the SAGA theorem's bundle of hypotheses, verbatim. I did not plant it. Ordinary developers, each making reasonable implementation choices, produced this shape.

## 4. The measurement: the diagnostic staircase fires end to end

The diagnostic staircase is a series of diagnoses stacked from simple to strong. At the bottom, the raw mismatch measurement (Čech); above it, grounding (does each chart obey its own law?), descent (does the discrepancy survive a full loop?), comparison (is the before/after comparison mathematically legitimate?), and finally the CI gate. I assembled the laws over this structure and ran the staircase. Here are the results (monospace tokens are the instrument's verbatim output).

| Act | Result |
| --- | --- |
| Measuring head (pre-repair) | `MEASURED_NONGLUING_RESIDUAL_CLASS` |
| ├ grounding (does each chart obey its law?) | `measured_zero` — it does |
| ├ descent (does the discrepancy survive the loop?) | `measured_nonzero` — it does |
| └ comparison (legitimacy of before/after comparison) | `established` |
| Gate decision | `BLOCKED_BY_GATE_POLICY` |
| Measuring the repaired state | `REPAIR_GLUES_WITHIN_SELECTED_COMPLEX` |
| Comparing head → repaired | `MEASURED_OBSTRUCTION_NO_LONGER_RECORDED_AFTER_CHANGE` |
| Gate decision after repair | `PASS_WITHIN_GATE_POLICY` |

Reading it in order:

**grounding = measured_zero.** This is the trap part of SAGA. cancel, inside-payment, and order each follow their own money convention perfectly. A per-service review — human or AI — has no grounds to reject the mismatch as *that service's* violation. Locally, everything is lawful.

**descent = measured_nonzero.** And yet the discrepancy around the triangle is not zero. Moreover it is the kind of discrepancy that no service can eliminate by re-choosing its own convention: re-labeling one chart only shifts the mismatch along its adjacent edges, and one loop's worth of discrepancy survives. That is what the computation returned. Eliminating it requires a structural change — creating a place where the remainder is booked — not a re-labeling. This is "no file contains a bug, yet the system is broken", as a measurement.

**Gate = BLOCKED.** Placed in CI, this PR stops. Even if every module's tests are green, the state "the system can drift by a cent" gets stopped from inside the sea of green — the live version of what the previous article called "a class of analysis beyond linting".

**Repair → gluing restored → PASS.** Supply a hypothetical repair — "unify the three services' shared reading on scale-2 BigDecimal and book the rounding remainder explicitly" — and, within the selected complex, the discrepancy becomes zero, the comparison reports the obstruction is no longer recorded, and the gate flips to PASS. The repair can be verified to glue *before anyone implements it*.

The story designed into the one-cent demo (nonzero obstruction → BLOCKED → repair → PASS) replayed in the same order, on a real codebase instead of a synthetic one. That the minimal failure the theory predicts showed up at its minimal size — under one cent — reads to me as evidence that the theory's resolution matches reality.

## 5. What was established

First, the hypotheses are inhabited. The SAGA theorem moved from "proved, with synthetic examples only" to "proved, with an instance reproduced in real code". The risk of vacuity died with this one example.

Second — and this is the real prize — the faithfulness contract survived. Between the theory and the instrument stands a contract: the instrument speaks only where the theorem can speak. This was the instrument's first contact with adversarial real data, and the chain of implications (locally lawful → loop discrepancy nonzero → repair glues) fired in the same order, under the same conditions, as the theorem chain on the Lean side. The contract never broke. Every refusal was legitimate too: declare, falsely, that the drifting triangle has a reconciling face, and the bookkeeping arithmetic rejects the contradiction.

## 6. Couldn't static analysis or LLM review find this?

A fair question. "Show three files to an LLM that can read whole codebases — surely it would flag this?"

Honestly: finding this particular instance is probably within an LLM's reach. In fact, in this very pipeline, the money conventions were read by LLM subagents (Claude Sonnet). The difference lies in the form of the output after the finding.

- **Non-locality as a verdict.** An LLM can say "these three are inconsistent". The measurement returns "this is the kind of discrepancy no service can remove by re-choosing its convention" — as a computation. Narration carries no such guarantee.
- **Separating benign from structural.** In the full build, mismatches were measured on 5 of the 6 observed handoffs — and the verdict was zero: benign drift that glues after local re-labeling. Nonzero stood only on the triangle. A flood of findings versus one structural point: in the age of review fatigue, that difference is the practical value.
- **Zero as a statement, and reproducibility.** An LLM cannot assert "no problems found" with a warranty, and its findings shift run to run (our own two independent passes agreed mechanically on only 9.4% of raw observations — see §8). The measurement returns the same verdict from the same input, with provenance traceable to the sources.
- **Pre-verification of repairs.** Both can propose fixes. Only the measurement can decide, before implementation, "this repair glues".

The cost structure differs too. Whole-codebase review loads the entire codebase into context at every review: you pay O(codebase) every time, and both token cost and misses grow with size.

Building the ArchMap is paid once, and a lightweight model sufficed. Afterwards only diffs need updating (the reproducibility engineering that underwrites this is in progress — §8), and the obstruction computation itself runs on the Rust side at effectively no cost. Pay O(codebase) once, then O(diff). The bigger and longer-lived the codebase, the wider the gap.

So the true relationship is division of labor, not rivalry. The LLM does local observation (reading per-file facts — the shape LLMs are good at); the mathematics does globalization (gluing observations and computing obstructions on loops — the shape that collapses if you lean on long-context attention). ArchSig is best described as an apparatus that gives LLM observations a mathematical spine.

The grounding = measured_zero result is itself the demonstration: within what per-service review can see, everything was lawful. The obstruction lived outside the unit of review, on the overlaps.

One more fair question: "couldn't type systems or static analysis catch it?"

This is where the difference in kind shows most clearly. In this triangle, the price order stores and the refund cancel returns are both typed `String`. **To a type system or a static analyzer, they look identical.** What disagreed was not the types but the semantic conventions: "this string is an unparsed money amount" versus "this string is an already-rounded refund". The obstruction lived where neither syntax nor types can see.

This is why ArchSig's input is not an AST or type information but Atoms — typed minimal observed facts abstracted away from code and language. Atoms treat structural facts (dependencies, calls) and semantic facts (conventions, responsibilities, state, authority) as the same basic unit. Observing a money convention is the job of a semantic atom: an analysis outside the vocabulary of static analysis.

Putting Atoms in the middle has one more consequence: independence from language and framework. The one-cent demo is Rust; train-ticket is Java; the instrument, the law vocabulary, and the diagnostic staircase are exactly the same. For polyglot systems — which microservices usually are — one map suffices.

## 7. What this report does not claim

Per series custom, the section for not saying what cannot be said.

- **The instrument did not find this on its own.** The raw mismatch was captured by the bottom stair, and "which handoffs the discrepancy appears on" is observation data I supplied after reading the sources. The staircase's contribution is not discovery but the diagnostic procedure: certifying that each service is lawful, certifying that the discrepancy survives the loop, verifying the repair in advance, stopping CI — as one machine-decided chain.
- **The repair is not implemented.** PASS states a pre-verification result — "this fix would restore consistency" — not that fixed code exists.
- **No damage figure was measured.** That the rounding remainder is booked nowhere is certain from the code; how much and how often it actually drifts requires running the system. Not quoting numbers we did not measure is also part of the discipline.
- **No criticism of train-ticket is intended.** It is a research benchmark, not a production system. Read this as an observation that an everyday mix of coding styles realizes the theorem's hypotheses — which also suggests the structure is not rare in real code.

## 8. The sea beyond the cape: a chart of the headroom

Incidentally, the Cape of Good Hope was first named the Cape of Storms by its discoverer, Dias, and later renamed for the hope of the route. Discovery sites being unglamorous is apparently a tradition. And from the cape to the opening of the India route took ten more years; the hardest part lay beyond the cape, where crossing the Indian Ocean demanded techniques coastal navigation could not provide.

This research stands at the same point. The route exists; what lies ahead is not theory but supply engineering. The headroom comes in three parts.

**First, reproducibility of observation.** This is ArchMap's lifeline. When two independent LLM passes read the same code, only 9.4% of raw observations matched mechanically. The breakdown matters: of 2,819 adjudicated disagreements (full source re-reads by subagents), only 29 were rejected as wrong. Correctness reproduced; what diverged was mostly naming (about nine tenths), then granularity, plus observations only one pass caught. With convergence conventions for naming, granularity, and notation plus a normalized matching key, re-extraction experiments raised key convergence from 0.32 to 0.74. The target is 0.8. Until then, the heavy safety net of dual passes plus full adjudication guarantees quality; once reached, the diff-update economics of §6 kick in properly. I will keep reporting these numbers as they move.

**Second, abstraction of supply.** To satisfy SAGA's supply contract this time, I read the evaluator's source code. That is not a procedure real users can be asked to follow. The goal is to give SAGA supply the same abstraction ArchMap supply already has — point at the loop you want repaired, and the required observations assemble.

**Third, the next measurements.** Runtime measurement to speak about damage (money-weighted analysis), and a second and third external OSS.

The flag is planted on the cape. "Locally correct, globally broken" is observed — as a measurement — in a real OSS codebase. The mathematics grown from axioms, as the previous article ended, connects to the sea of real code.

## References

- Repository: [AlgebraicArchitectureTheoryV2](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2) (MIT license)
- Result note: `docs/note/saga_cape_of_good_hope_dogfooding.md`
- Primary measurement record: Issue #3545 (full-build measurements, supply cost, findings)
- The one-cent demo (synthetic, reproducible): `tools/archsig/examples/practical-rust-service/`
- Proof record of the SAGA theorem: `docs/note/aat_saga_theorem_proof_record.md`
- Target codebase: [FudanSELab/train-ticket](https://github.com/FudanSELab/train-ticket) (commit `313886e9`)
