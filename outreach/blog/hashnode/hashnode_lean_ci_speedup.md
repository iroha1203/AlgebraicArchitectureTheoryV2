# Taming a 40-Minute Lean CI: Three Rounds, Three Wrong Suspects

Our Lean 4 + mathlib project used to spend 41 minutes in CI on every single PR. Today, the worst case — rebuilding the heaviest files from scratch — takes 12 minutes, and an ordinary PR finishes in a few minutes on an incremental build.

| What we fixed | Before | After |
| --- | --- | --- |
| Kernel axiom audit | 7m 11s | **11s** |
| An ordinary PR | 41m (full rebuild, always) | **a few minutes (incremental)** |
| Worst case (heaviest files fully rebuilt) | 41m (same) | **12m** |

This article records the improvement in three rounds, each written in the same shape: **problem → hypothesis → verification → fix**. Spoiler up front: all three times, the first hypothesis — the culprit our intuition pointed at — turned out to be innocent. The hero of this story is not any individual trick. It is the profiling that kept calmly rejecting our hypotheses.

Lean-specific concepts are explained as they appear, so you should be able to follow without knowing Lean.

One more thing. Nearly all of the measurement and implementation in these three rounds was done by AI agents (Rounds 1 and 2 in interactive sessions with a human present; Round 3 by an autonomous loop driven by a requirements document). The human — me — did two things: approve the numeric targets and accept the results. The second half of the article covers that operation, in particular the machinery that keeps an AI from converging on cheap solutions.

## Background: the project

The subject is [AlgebraicArchitectureTheoryV2](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2), the same monorepo my previous articles have covered — a formal verification of a theory of software architecture in Lean 4.

Here is the complete list of Lean machinery this article needs — five items:

| Term | What it is |
| --- | --- |
| **Lean 4** | A proof assistant: a programming language in which mathematical proofs are machine-checked. Think of it as a language where "the proof compiles" is the acceptance test |
| **mathlib** | Lean's enormous mathematics library — over 1.5 million lines of community-maintained code at the time of writing. Depending on it gives you a "standard library of mathematics," at the cost of build sizes to match |
| **lake** | Lean's build tool, the equivalent of cargo for Rust or npm for JS. It builds per file (module) and emits `.olean` artifacts |
| **elaboration** | Lean's equivalent of "compilation": type inference, implicit-argument resolution, and proof checking, all in one. **Almost all Lean build time is elaboration** |
| **declaration** | A single definition or theorem. When this article says "4,000+ audited declarations," this is the unit being counted |

For scale: the audit covers 4,000+ declarations, and among them sits one heavyweight file — a construction of schemes from algebraic geometry — that took 38 minutes to build on its own.

CI runs on GitHub Actions. Alongside `lake build`, every PR runs a **kernel axiom audit** — a machine check that every theorem is genuinely proved, with no cheating in the proofs. That gate is non-negotiable; Round 1 explains what it actually does.

## Round 1: The axiom audit, 7m 11s → 11s

### Problem

In Lean, every theorem is derived from axioms, and the derivation is machine-checked by the kernel (a small, trusted checker). "The proof went through" means it passed this check. The important wrinkle is that Lean has an escape hatch called `sorry`. Writing `sorry` means "I'll prove this part later," and it does not fail on the spot (your editor does show a warning). Internally, it silently assumes an axiom called `sorryAx`. Users can also add arbitrary unproven propositions as axioms with the `axiom` keyword.

In other words, "CI is green" alone cannot distinguish "everything is proved" from "someone plugged the gaps with axioms." So for each declaration, we walk its dependencies all the way down and compute **the set of axioms it reaches**, then check that this set stays within the three standard axioms accepted across Lean and mathlib — `propext`, `Quot.sound`, and `Classical.choice` (the axiom of choice is that last one). This is the axiom audit. A hidden `sorry` or a smuggled-in axiom cannot survive it. If you call yourself a formal verification project, you don't get to skip this gate.

Lean exposes this walk-and-collect operation as a function called `collectAxioms` (it is the same machinery that runs when you type `#print axioms my_theorem`). Our CI ran it over every declaration — 1,207 at the time, over 4,300 today — and that step took 7 minutes 11 seconds on every run. The audit was heavier than the build itself.

### Hypothesis

The audit's entry point is a giant file, 5,000+ lines, listing every audited declaration. Intuition speaks up: "A file this big must be expensive to elaborate. Split it and it'll get faster."

### Verification

Before splitting anything, we measured where the time went. The result flatly contradicted the intuition:

- Resolving imports: ~10 seconds
- Elaborating the 5,000-line listing: **zero difference** (changing the line count substantially didn't move the audit time)
- `collectAxioms` × 1,207 declarations: **~5 minutes**

The culprit was not the big file. It was how the audit was being called. To find the axioms a declaration reaches, you must walk the dependency graph to its roots — the theorems it uses, the theorems *those* use, and so on. `collectAxioms` performs this walk **from scratch for every declaration**. But every declaration in the project shares the same enormous foundation, mathlib — so 1,207 declarations were walking essentially the same graph 1,207 times. In complexity terms: O(declarations × graph). Splitting the file touches neither factor of that product. It was ineffective even on paper, but having the measurement in hand is what let us reject it in one line and move on.

### Fix

We made the audit two-phase:

1. **Success path**: share a visited set — "never walk the same node twice" — across all declarations, and traverse the graph **exactly once**. Since the question is "does the union of reached axioms stay within the standard three?", one shared walk gives the same verdict as per-declaration walks
2. **Failure path**: only when a non-standard axiom shows up, fall back to the classic per-declaration walk to attribute *which* declaration is guilty, with error messages in exactly the original format

That collapses O(declarations × graph) to O(graph) on the success path without giving up any error quality. It is the textbook visited-set move from graph traversal — no Lean-specific magic anywhere. Measured in CI, the audit went from 7m 11s to 11s, and the whole `lake build` job at the time went from about 9.5 minutes to 2m 12s.

**Round 1's lesson**: suspect "heavy operation × repetition count" before "heavy file." And record the rejected hypothesis (file splitting: no effect) as a result in its own right — so nobody after you re-digs the same hole with the same intuition.

## Round 2: Every PR took 41 minutes — the cache was saved *before* the build

### Problem

Round 1 happened in mid-July, when the `lake build` job had shrunk to a bit over two minutes. Over the following two weeks, a series of heavyweight algebraic-geometry implementations landed (Round 3's protagonist grew fat in this period), and at some point every PR — even one touching a single file — was running a full cold build of the entire tree: about 41 minutes.

Lean builds are incremental, in the same spirit as C++ or Rust. If the build artifacts (`.olean` files, stored per module under `.lake/build`) are still around, only the changed files and their downstream need rebuilding. For that to work in CI, the previous run's artifacts have to be carried over as a cache. The cache was configured. It just wasn't working.

### Hypothesis

When a cache "doesn't work," the usual suspects are a key mismatch or eviction. Is the toolchain hash off? Are old generations being evicted?

### Verification

Before auditing keys, we read the CI log timestamps top to bottom. Two lines sat one second apart:

```
23:19:35  Cache save   (final internal step of lean-action)
23:19:36  lake build +Formal.AG starts
```

The cache *was* being saved. **Before the project was built.**

We set up Lean with lean-action — a composite action (a reusable bundle of steps) — configured with `build: false`, running the build ourselves in a later step. But lean-action saves `.lake` (the build artifact directory) to the cache in its own final internal step, and a composite action's internal steps always run before your subsequent steps. So the 2.15 GiB being saved contained only dependency artifacts (mathlib); the project's own `.olean` files **had never been cached at all**. No wonder every PR took 41 minutes — each one rebuilt all of our own code from a blank slate.

There was a bonus discovery. mathlib is too big for individual users to build, so the community distributes prebuilt artifacts from Azure (`lake exe cache get`; about 15 seconds in our measurements, environment-dependent). The cached 2.15 GiB was therefore something you could fetch in 15 seconds anyway — worthless in the GitHub cache. Worse, at 2.15 GiB × 4 generations, it was nearly exhausting the repository's 10 GiB cache quota. A useless cache was crowding out the useful one.

### Fix

We separated the cache responsibilities:

- Disable lean-action's GitHub cache (`use-github-cache: false`); mathlib artifacts keep coming from the Azure cache
- Explicitly restore (before build) and save (**right after build**) only the project's own `.lake/build`
- Prefix the key with a hash of `lean-toolchain` + `lake-manifest.json`, so toolchain or mathlib bumps fall back to a proper cold build
- Save with `always()`, so failed builds still persist partial artifacts — every push to a red PR reuses everything built up to the failure point, making iteration fast

The actual workflow looks like this (excerpt). The one thing that matters: put the save *after* the build yourself.

```yaml
- name: Restore Formal build cache
  uses: actions/cache/restore@v5
  with:
    path: .lake/build
    key: formal-build-${{ runner.os }}-${{ hashFiles('lean-toolchain', 'lake-manifest.json') }}-${{ github.sha }}
    restore-keys: |
      formal-build-${{ runner.os }}-${{ hashFiles('lean-toolchain', 'lake-manifest.json') }}-

- name: Build
  run: lake build +Formal.AG

- name: Save Formal build cache
  if: always()
  uses: actions/cache/save@v5
  with:
    path: .lake/build
    key: formal-build-${{ runner.os }}-${{ hashFiles('lean-toolchain', 'lake-manifest.json') }}-${{ github.sha }}
```

With this, PRs that don't touch the heavyweight geometry files settle into cache hit + incremental build: a few minutes.

In fairness to [lean-action](https://github.com/leanprover/lean-action): its cache works correctly in the standard usage where you let the action run the build too. It was our configuration — `build: false` with the build held outside — that stepped on the trap.

**Round 2's lesson**: when "the cache isn't working," read the timestamps before you audit the keys. Composite actions are convenient, but their internal step order is orthogonal to your workflow's step order. "Is the save actually after the build?" is worth checking with your own eyes.

## Round 3: The 38-minute Geometry.lean — splitting it didn't make it faster

### Problem

The largest remaining bottleneck was a single file: `Geometry.lean`, 5,129 lines, 108 declarations. It constructs actual schemes — the central objects of algebraic geometry, heavyweight abstractions even by modern mathematics standards — on top of mathlib, and it alone took 38.3 minutes in CI, 46% of the project's total CPU time. Even with Round 2's cache, any PR touching this file's upstream paid the full 38 minutes.

This time we fixed numeric targets before starting: **longest module ≤ 600 seconds, total across the target modules ≤ 1,800 seconds**, judged by the module times reported in one and the same GitHub Actions full build. Measurement method included, approved by the human before implementation began.

### Hypothesis

It's a giant 38-minute file — split it into modules along its dependency structure and rebuilds will shrink and speed up. This is the "splitting makes it faster" hypothesis that Round 1 already rejected once, now in its build-time incarnation. Since elaboration runs per declaration, this time the reasoning looks sound.

### Verification

First, a per-declaration profile. Lean ships with a built-in profiler; one command tells you which processing step of which declaration took how many seconds. Here is what we used:

```bash
lake env lean --profile --json \
  -Dprofiler.threshold=10 \
  -Dtrace.profiler=true -Dtrace.profiler.threshold=10 \
  -Dtrace.profiler.output=geometry-before-trace.json \
  Formal/AG/Examples/StandardGeometryReference/Geometry.lean
```

The breakdown: kernel type checking 57%, defeq (deciding whether two terms are definitionally equal) 39%, with the time massively concentrated in a dozen or so declarations. Following that center of gravity and the dependencies, we split the file into a 7-module DAG:

```
RawGeometry
└─ SectionRings
   ├─ LeftRestriction
   ├─ RightRestriction
   ├─ OverlapLeftRestriction
   └─ OverlapRightRestriction   * these four import nothing from each other → build in parallel
      └─ Scheme
```

We proved mechanically that the split broke nothing. Lean's `#check` prints a declaration's statement — the theorem's actual claim. We took the `#check` output for all 168 public declarations of the old file (794 lines), before and after the split, under the same toolchain and the same printing settings, and confirmed the SHA-256 hashes match. Not one character of any theorem statement changed. Being able to certify "the mathematical content is preserved" with a hash instead of eyeballs, even for a mechanical refactor, is one of the quiet joys of a formal verification project.

Then we measured the *after* in CI — and **missed the targets**. Longest module 770 seconds (target 600), total 2,483 seconds (target 1,800). Splitting shrinks rebuild scope and buys parallelism, but it does not remove a single second of elaboration. With module-boundary overhead, the total actually grew.

Digging deeper into the profile exposed the real culprit. The time was not spread thinly in proportion to line count. It was concentrated in the **cost of definitional unfolding** around specific definitions.

A short detour on definitional unfolding. In Lean, a definition is a pair of a name and a body, and the body can be unfolded in place when needed — much like a compiler inlining, except Lean does it **during type checking**. When deciding "do these two expressions have the same type?", Lean matches two superficially different terms by peeling definitions open (unification). Normally this is what lets proofs stay short. But when large-bodied definitions get involved, each peel exposes more definitions, and the terms balloon.

In our file, that ballooning happened while checking the functions that actually compute the scheme's components (large-bodied definitions) and the lemmas stating those computations are correct. The 96% of profile time in kernel checking and defeq was exactly the cost of checking these bloated terms: individual operations of 15–104 seconds each, stacked up inside single commands.

Line count was never the crime — the same shape as Round 1. The file wasn't heavy because it had 5,129 lines; it was heavy because of **how specific definitions were being referenced**.

For the record, we also tried two pieces of "standard-issue optimization" at this stage (switching to `CommRingCat.hom_ext`; using `congrArg CommRingCat.ofHom` — both established mathlib idioms). Neither improved the measurements; both were rejected. An idiom failing to help is also a data point, once you have a profile.

### Fix

Surgery at the one point the profile indicated. The policy was uniform: **rewrite so that the type checker never needs to peel the definitions.**

- Separate a value's definition from the proofs about that value. When they are entangled, checking the proof part drags in unfolding of the value's entire body
- Pin lemma statements to named functions rather than unfolded expressions. If the match succeeds on the name, unification has no reason to open the body
- Consolidate the proof pattern duplicated across four theorems into a shared lemma, so the same expensive check isn't paid four times

The effect was dramatic. In a focused build (measuring just the one file), the heaviest module, `RawGeometry`, went from **291 seconds to 11**. The operations that used to top the chart at 15–104 seconds max out at 57.5 milliseconds after.

The final CI measurement (full build of the merge commit): total across the 7 modules **1,750 seconds (29.2 min) ≤ target 1,800**, longest module **468 seconds ≤ target 600**. Both targets met. Done.

And that merge commit's CI run is a group photo of all three rounds. From the log:

| Step | Time |
| --- | --- |
| Restore Formal build cache | 3s (cache hit — Round 2) |
| Build (incl. full rebuild of all 7 modules) | 9m 29s (parallel DAG + lighter modules — Round 3) |
| Kernel axiom audit | 26s (shared traversal — Round 1) |
| **Whole job** | **11m 57s** |

Twelve minutes with the heaviest files fully rebuilt. That is the current worst case.

**Round 3's lesson**: splitting is not a tool for making things faster; it is a tool for parallelism and smaller rebuild scope. What reduces the total is surgery at the one point the profile indicates. And since these are two different improvements, measure them separately and judge them separately.

## The improvements were driven by AI agents

As mentioned at the start, nearly all measurement and implementation across the three rounds was agent work. Rounds 1 and 2 ran inside interactive sessions, from measurement through implementation; Round 3 was an autonomous loop that took a requirements document (PRD) and drove everything from profiling to PR authoring to review response. During implementation, the human had exactly two jobs:

1. **Approve the numeric targets and the measurement method up front** (for Round 3: "longest ≤ 600s, total ≤ 1,800s, judged by module times in one and the same GHA full build")
2. **Accept or reject based on measured CI values**

To be honest, there is a third job upstream: writing the PRD. But that too is a collaboration with another AI; the human's actual work is choosing the direction and reviewing.

### The PRD Loop

We call the autonomous loop from Round 3 the **PRD Loop**. It is handed to the agent (Codex) as a SKILL — an instruction document for agents. The skeleton:

- The input is a single PRD, with a guiding question and numeric Acceptance Criteria at the top. A human starts it with one command (`$prd-loop <path-to-PRD>`)
- One iteration is "gap analysis → file an issue → implementation PR → adversarial review → merge → ledger sync." It runs in small units: **one iteration = one issue = one PR** (one goal spanning several iterations is normal operation)
- A **separate review gate** (also an AI) judges each PR — never the implementer itself. After two rounds of "needs changes," the third escalates to a stricter, specialized gate (for Lean, a dedicated mathematical review gate); if that still fails, the item is marked `stalled` and returned to the human
- Loop state lives in GitHub issues, not in the agent's memory. If the session dies, the next session resumes from the same spot
- When every condition looks satisfied, an **independent completion audit** re-reads the PRD from scratch and verifies everything against reality. Until it passes, nothing gets to call itself "done"

Round 3's "profile → split → miss → dig deeper → hit" ran on this wheel as three PRs (split / reduction / closeout). Start to finish took just under a day. Human intervention along the way: approving the targets and confirming the measurement standard — a handful of GitHub comments.

Incidentally, our convention is that a completed PRD is **deleted** from the repository. A requirements document starts drifting from reality the moment implementation ends, so the permanent record is pinned to issues, PRs, and CI logs — and the document itself goes.

### Closing off the cheap paths

Run such a loop naively, though, and one thing reliably happens. Agents are faithful to the incentives you give them, so left alone they converge on **the cheapest path to a merged PR**. Change the documentation instead of the implementation. Satisfy an unsatisfiable condition by "interpreting" it. Quietly defer the hard items. None of these is exactly a lie — but compounded, they settle into an equilibrium where "done" can be claimed at minimum effort. Call it the corner-cutting equilibrium.

So our SKILL reads less like a procedure and more like **mechanism design**: a set of rules that seals off the cheap paths one by one.

- **No docs-only check-offs**: a condition that demands implementation or verification can never be marked satisfied by a PR that only edits documents or ledgers
- **No reinterpretation, no downgrading**: a condition the agent cannot meet is escalated to the human as `blocked`, not read more weakly. The SKILL states it in so many words: "stopping is not failure; stopping is part of the loop's specification"
- **The PRD is invariant during the loop**: the agent cannot rewrite its own passing bar. If it finds a defect in the PRD, it stops and reports rather than fixing it (you don't get to edit the exam paper mid-exam)
- **Checklists are not evidence**: a checkmark means only "a past iteration claimed this." The final audit re-extracts the conditions from the PRD independently and verifies them against reality — code, tests, CI logs
- **No self-grading**: the completion auditor receives only the PRD path and issue numbers — never the loop's own "I believe everything is satisfied." If a review gate cannot run, the main agent does not stand in for it; the loop fails closed

These rules were not designed at a whiteboard, by the way. Each one was added after actually observing early loops try the corresponding move — settling a condition with a ledger entry, quietly shrinking scope in the name of safety. We were never smart enough to write all the guardrails in advance.

There is one design principle underneath all of it: **make stopping honestly cheaper than pushing through dishonestly.** Don't count on the agent's good will; move the equilibrium itself.

### The best moment: the miss report

The best moment of this whole operation was Round 3's **miss report**. At the split PR, the agent wrote, in its own PR description: "Longest 770 seconds, total 2,483. **Targets missed; this PR does not claim completion.** Profile-driven reduction continues in the next PR." No human issued any instruction in response. The loop filed the reduction issue itself on the next iteration and merged the PR that met the targets the same day.

Declaring "done" and walking away is the cheapest move available at exactly that point, and the agent instead wrote *missed* and kept going. I credit that less to the agent's honesty than to the structure around it. When the passing bar is fixed in advance, reinterpretation is banned, and an independent audit will check every claim against measured values, then whenever declaration and measurement disagree, it is the declaration that has to move. Set the bar afterwards instead, and the temptation to fit the bar to the result appears — on the human side too.

If you are planning to hand optimization work to an AI, the most practical thing to take from this article is probably this: **hand over the passing bar and the measurement method before you hand over the code. And make honest stopping the cheapest move on the board.**

## Conclusion

- Axiom audit, 7m 11s → 11s. The culprit was not the giant file but the unshared traversal walking the graph once per declaration
- Every PR at 41 minutes → incremental builds in minutes. The culprit was not the cache key but a cache save running *before* the build
- One 38-minute file → 29 minutes total, 8 minutes longest, 12-minute worst-case run. Splitting removed nothing; the culprit was definitional unfolding cost

All three first hypotheses were wrong. Progress happened anyway, because each wrong hypothesis was rejected by measurement and the rejection itself was passed forward as a result. "No effect" is a finding. File splitting rejected (Round 1), two standard idioms rejected (Round 3) — without those records, someone, human or AI, would have dug the same holes again.

On the AI side: Round 3's loop ran start to finish in under a day, across three PRs, with human intervention limited to a handful of GitHub comments.

Don't guess, measure. It's an old maxim, but in the era of AI-written code I think it needs a sequel — **let the AI measure, and hand it the passing bar first.**
