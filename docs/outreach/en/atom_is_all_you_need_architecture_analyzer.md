---
title: "Atom Is All You Need: Read a Codebase as an Atom Map, Not a Dependency Graph"
published: false
description: "Introducing ArchSig: an MIT-licensed architecture analysis tool that reads codebases through Atom observations, ArchMap, LawPolicy, and AAT."
tags: softwarearchitecture, ai, softwareengineering, opensource
---

> **TL;DR**
>
> In the AI era, architecture analysis cannot stop at reading code as files, functions, imports, and dependency graphs.
>
> We need to observe the smallest units that carry architectural meaning. I call those units `Atom`s.
>
> By extracting Atoms from a codebase and reading the algebraic structure they generate, we can analyze architecture beyond ordinary dependency relationships.
>
> The workflow looks like this:
>
> ```text
> codebase
>   -> Atom observations
>   -> ArchMap
>   + LawPolicy
>   -> ArchSig analysis packet
>   -> architecture reading
> ```
>
> This lets us see design pressure, semantic coupling, missing evidence, and review focus that ordinary linting, static analysis, and dependency graphs often miss.
>
> We built a new tool for this workflow: [ArchSig](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/tree/main/tools/archsig).
>
> The repository is public and MIT licensed, so you can try it on your own codebases.
>
> The key idea is simple:
>
> > Architecture analysis does not need a bigger natural-language summary.
> >
> > It needs the right unit of observation.

## Why We Need an Architecture Analyzer

AI agents can write code fast.

But writing code fast is not the same thing as evolving a system well.

For an AI agent, the codebase is the largest prompt.

If the existing codebase contains shortcuts, those shortcuts become examples.
If boundaries are vague, new code naturally lands in vague places.
If responsibilities are mixed, that mixing becomes part of the next implementation context.

Traditional tools often look at the current shape of code:

- import graphs
- dependency cycles
- layer violations
- lint rules
- complexity metrics
- test coverage
- security rules

All of these matter.

But in AI-era architecture review, we often want to ask deeper questions.

Imagine a business backend where users select input data, run automated processing or generation, persist the result, receive events from external systems, run async jobs, call external providers, and save generated artifacts back into business state.

The important questions are not only:

> Are the dependencies pointing in the right direction?

We also want to know:

- Who is allowed to use which input for which operation?
- Through which validation path does generated output become persisted state?
- Where is an external provider failure recorded as durable state?
- Do two workflows that produce the same artifact actually have the same effect order?
- Do entrypoint-level permissions match the intended business scope?
- Are privileged operations separated from ordinary workflow authority?

These are difficult to read from a dependency graph alone.

We need to read code not only as a collection of files and functions, but as a set of observations that carry architectural meaning.

That unit is the `Atom`.

## Atom: The Smallest Unit of Architectural Meaning

An Atom is the smallest observation unit I want to use when reading architecture.

It is not necessarily a function, class, module, or file.

In practice, it is the thing you point at during review and say:

> This is a boundary.
>
> This is state.
>
> This is an effect.
>
> This is a contract.
>
> This is where trust changes.

Examples of Atom families include:

- `component atom`: an architectural unit exists
- `relation atom`: two units or atoms are related
- `capability atom`: a unit provides a specific capability
- `state atom`: something is persisted or held as state
- `effect atom`: an external call or side effect occurs
- `authority atom`: someone is allowed to do something
- `trust relation atom`: some output or provider is trusted up to a boundary
- `contract atom`: inputs, outputs, preconditions, or failure behavior are promised
- `semantic atom`: something has architectural meaning beyond its code location

The important point is that an Atom is not small in the syntactic sense.

It is small in the architectural sense.

For example, the observation:

> Only an authorized actor may update this resource.

may cross multiple files.

The observation:

> Generated output must pass through a service-level contract before persistence.

may cross a route, service, validation layer, job state, and repository.

Still, each observation is one meaningful unit in architecture review.

That is what an Atom records.

## A Small Code Example

Even a tiny function can contain multiple Atoms.

```python
def publish_artifact(actor, artifact_id, repository, gateway):
    artifact = repository.load_for_actor(actor.id, artifact_id)
    gateway.publish(artifact.payload)
    artifact.mark_published()
    repository.save(artifact)
```

If we only say "this is one function," we miss most of the architectural content.

Read as Atoms, we can observe at least:

- `component`: `repository` and `gateway` are architectural units
- `relation`: the handler flows into both the repository and the gateway
- `capability`: the repository provides load/save, while the gateway provides publish
- `state`: the artifact's published state is persisted
- `effect`: `gateway.publish` changes external state
- `authority`: the actor must be allowed to publish this artifact
- `trust_relation`: the gateway response and failure behavior must be trusted only through a boundary
- `contract`: publish success, save failure, and retry behavior need explicit promises
- `semantic`: published is not only a flag; it means externally visible

These nine Atom schemas are the basic vocabulary for treating primitive architectural facts as generators of an architecture object.

## ArchMap: Turning a Codebase into an Atom Map

An `ArchMap` is a map of these observations.

It is not a full copy of the codebase.
It is not an AST dump.
It is not only a dependency graph.

It is a source-grounded map of architectural observations.

```text
source code
  observed as
Atom / Molecule / Semantic observations
  recorded as
ArchMap
```

If an Atom is one observation, a Molecule is a finite composition of Atoms that acts as one responsibility boundary.

For example, an ArchMap of a backend might contain Molecules such as:

- authenticated request boundary
- credential lifecycle
- repository transaction boundary
- interactive processing workflow
- input-to-artifact pipeline
- external integration ingress
- job-managed generation surface
- input-backed artifact boundary
- edge policy and observability boundary
- privileged governance boundary

The important point is not that the codebase has folders such as `api`, `services`, `repositories`, and `models`.

The important point is that architectural meaning sits on top of those folders:

- authority
- generation
- external effect
- durable state
- artifact lifecycle
- semantic contract

ArchMap records that meaning in a machine-readable form.

## AAT: Reading Structure from an Atom Map

Once we have an ArchMap, we can ask a different kind of question:

> Under which laws does this architecture object have pressure?

AAT, Algebraic Architecture Theory, reads software architecture as an algebraic structure generated from Atoms.

It studies architecture through objects, operations, laws, invariants, obstructions, and signature axes.

I will leave the detailed theory to [Algebraic Architecture Theory](https://iroha1203.dev/aat/).

For this article, the intuition is enough:

- `law`: a design property we want to preserve
- `witness`: observed evidence related to that property
- `obstruction`: a structure that blocks the law
- `signature axis`: the direction in which pressure appears
- `operation`: a design operation such as split, move, protect, or refactor
- `path / homotopy`: whether two change paths preserve the same structure
- `curvature / holonomy`: when something looks locally natural but becomes inconsistent around a loop

In ordinary review, engineers often process these ideas in their heads:

> This responsibility is mixed.
>
> This external call should not be inside the transaction.
>
> These two job statuses look the same, but the failure paths differ.
>
> This generated output must be validated before it becomes domain state.

AAT tries to move this review vocabulary toward something we can compute.

The important step is to treat Atoms not as labels, but as primitive facts that generate architecture objects.

Once Atoms carry relation, state, effect, contract, and semantic axes, we can see things a dependency graph cannot show:

- a locally natural change that changes effect order through another path
- a split that moves complexity to another boundary
- two workflows that look statically similar but differ under a semantic contract

These are non-trivial architecture readings.

They should not live only in a senior engineer's intuition.

They should be tied to a selected law universe and a selected set of witnesses.

That is the role of AAT.

## ArchSig: Reading Structure from ArchMap + LawPolicy

ArchSig takes an ArchMap and a LawPolicy, then produces an AAT-style analysis packet.

```text
ArchMap
  + LawPolicy
  -> ArchSig
  -> analysis packet
```

`LawPolicy` is the interpretation profile.

It selects the law universe, witness rules, signature axes, measurement policy, and coverage requirements for the analysis.

The same ArchMap can be read in different ways depending on what you care about:

- authority boundaries
- state/effect consistency
- generated output mediation
- domain cohesion
- permission coverage
- repair preconditions

ArchSig does not collapse all of this into one "good / bad" score.

It reports pressure and semantic coupling along different axes.

The output can include readings such as:

- nonzero pressure by law axis
- workflow risk
- transfer bridge pressure
- state/effect reconciliation pressure
- operation squares
- axis-wise monodromy defects
- architectural holes
- boundary holonomy
- repair precondition blockers
- review focus

This is not a code quality score.

It is a measurement surface for reading where design pressure and semantic coupling appear.

## Case Study: Analyzing a Backend Repository

So far, the discussion has been conceptual.

Now let us look at the shape of one backend repository through ArchSig.

This repository has multiple users, authority boundaries, business data, external effects, async jobs, and generated outputs.

Users select input data and run analysis, generation, extraction, or transformation workflows.
External systems send events.
Async jobs call providers.
Results are persisted as business artifacts.

From the ArchMap, ArchSig could read structures like:

- a backend split into API, service, repository, model, schema, and task layers
- authority boundaries across users, organizations, and resources
- a domain model where multiple artifacts derive from input data
- generated output mediated by service contracts and job state
- external provider effects paired with durable job state
- privileged operations separated from ordinary workflows

This is already different from a dependency graph.

ArchSig reads the repository as a business backend with authority boundaries, generated outputs, external effects, and durable state.

## The Design Pressure It Found

The strongest pressure appeared at the intersection of authority and generation.

The system is not merely saying:

> An authenticated actor can run generation.

The real architectural question is:

> Who can use which resource as input, and which generated output can become which domain state?

That is a central boundary.

Reviewing only authorization is not enough.
Reviewing only the generation job is not enough.
The two boundaries are bridged.

The next large pressure was state/effect reconciliation.

The repository has external providers, async jobs, event handlers, retries, roundtrips, and compensation paths.

In this kind of system, not everything can live inside one transaction.

The architecture needs durable intermediate state, external effect recovery, explicit failure finalization, and retryable paths.

ArchSig reads this through the relation between state atoms and effect atoms.

The third pressure was generated output mediation.

Generated output is useful, but it should not become domain state without mediation.

You need input construction, structured output, filtering, validation, job failure handling, and persistence gates.

In this repository, the mediation appeared across multiple workflows:

- interactive workflows
- analysis execution
- content extraction
- generated artifact creation

So the design question is not:

> Does the system use generation?

The real question is:

> Through which contract does generated output pass before it becomes domain state?

This is not just dependency analysis.

It is a reading of where authority, state, effect, contract, and semantic meaning overlap.

## Same Destination, Different Path

One of the most interesting ArchSig readings is the monodromy defect.

The intuition is:

> Two paths may appear to arrive at the same place.
>
> But do they preserve the same structure?

In the repository, several workflows looked similar from the outside.

They produced artifacts or updated state.

But the order of provider calls, repository commits, job state transitions, and status finalization could differ.

A dependency graph may not show that.

Even if the static dependencies point in the same direction, the workflow path can change failure behavior.

Does the system create state before calling the provider?
Does it call the provider first?
Where is failure finalized?
Does retry use the same idempotency key?

ArchSig reads this kind of path difference as operation squares and axis-wise defects.

This is practical in review.

When someone says:

> This follows the existing pattern.

ArchSig helps ask:

> Does it really?

It may look like the same endpoint.
It may create the same kind of artifact.

But if the effect order differs, the operational behavior differs.

That difference often becomes incident cost or future refactoring cost.

## Architectural Holes: Loops That Do Not Close

Another important result was the architectural hole.

ArchSig found holes around paths such as:

- API -> service -> repository
- async provider jobs
- generated output -> domain state promotion
- semantic contracts

This does not mean "there is a bug."

It means the evidence is not enough to say the architectural loop is closed.

For example, the path from generated output to domain state may involve:

- input data
- context construction
- structured output
- validation
- job state
- repository persistence

To say this loop is closed, source reading alone is not enough.

You may need test evidence, runtime traces, provider logs, and entrypoint-by-entrypoint permission audits.

ArchSig does not treat missing evidence as zero.

It preserves it as a hole.

That matters because one of the dangerous failure modes in architecture review is to read "unknown" as "fine."

ArchSig keeps the gap visible.

And the gap becomes a review proposal.

```text
gap:
  - permission evidence is incomplete
  - runtime trace is missing
  - provider failure path is not covered

review proposal:
  - human reviewer: check authority boundary and failure handling
  - LLM reviewer: compare the generated output path with the declared contract
  - test reviewer: add evidence for retry and finalization behavior
```

In other words, ArchSig does not hide uncertainty.

It turns uncertainty into review focus.

## Spectral Analysis: Where Pressure Comes Back

One of the most interesting parts of ArchSig is `ArchitectureSpectrumReport`.

Ordinary review often ends with a list of issues.

But in architecture, pressure does not always appear once and disappear.

An authority mismatch can show up in generated output persistence.
From there it can move into job state.
Then it can come back through retry behavior or provider failure handling.

Spectral analysis reads this recurrence.

```text
curvature support
  -> transfer edge
  -> recurrent mode
  -> hotspot / witness cluster
  -> review focus
```

Again, the point is not a single score.

The interesting questions are:

- Where does pressure concentrate?
- Which obstructions recur?
- Which witness clusters cross multiple law axes?
- Which coverage gaps block a zero reading?
- Which boundary should be reviewed before a repair candidate is trusted?

From a dependency graph, a workflow may look cleanly separated.

But spectral analysis may show remaining transfer between effect order, semantic contract, job state, and authority boundary.

That is not simply "there is a cycle."

It is a more structural reading:

> Locally separate pressures return to the same support inside the architecture object.

ArchSig can surface that as a hotspot.

## Repair Candidates Are Not Automatic Fixes

ArchSig can also produce repair candidates.

In this repository, many candidates were stopped by precondition blockers.

That is important.

Seeing pressure does not mean the system should immediately be split or rewritten.

If you cut one boundary, complexity may move somewhere else.
Fixing authority may increase runtime effect pressure.
Strengthening generated output mediation may change job state and retry paths.

ArchSig does not treat repair as an automatic safe edit.

It checks preconditions, witnesses, coverage, and transfer risk.

This is close to how experienced engineers review architecture:

> This looks risky.
>
> But before fixing it, we need this evidence.

That difference matters.

## How This Differs from Existing Tools

So what exactly is different?

Existing tools are good at reading the current shape of code:

- Does a dependency cycle exist?
- Is there a layer violation?
- Is test coverage missing?
- Is a security rule violated?
- Is complexity too high?

ArchSig is trying to read something else:

- Where are responsibility boundaries composed?
- On which law axis does pressure appear?
- Do two paths with the same destination preserve the same effect order?
- Where do generated output, external providers, authority, and durable state intersect?
- Would a repair candidate move complexity to another boundary?
- Which evidence is missing, and therefore should become review focus?

This is not a code quality metric.

It is an instrument for reading architectural state.

Another important point is that review can happen around the ArchMap artifact.

The source-grounded observation still has to be produced from real code.

But after that, sharing, reviewing, and comparing can happen around ArchMap and the analysis packet.

That matters for teams and companies that cannot freely share full codebases.

There is also an AI angle.

If you simply ask an LLM to review a large codebase, the full context will not fit.

Even if it does fit, it is hard to make the model consistently focus on:

- the right boundary
- the missing evidence
- the relevant law axis
- the path where effect order differs

ArchMap and ArchSig change the shape of the context.

Instead of handing the model all code and asking for a huge summary, you hand it Atoms, Molecules, law axes, holes, and review focus.

Then the model can reason around the architecture boundary that actually matters.

## Atom Is All You Need

Trying to understand a large codebase all at once breaks down quickly.

There are too many files.
Too many functions.
Too many dependencies.
Too many external providers.
Too much code added by fast AI agents.

So start with Atoms.

```text
component
relation
capability
state
effect
authority
trust_relation
contract
semantic
```

Observe them.
Record them as an ArchMap.
Choose a LawPolicy.
Run ArchSig.

This lets us read meaningful architecture boundaries without pretending we can understand the entire codebase at once.

What AI-era architecture analysis needs is not a larger natural-language summary.

It needs the right unit of observation.

Atom is all you need.

## The Review Experience This Enables

Future review could look like this.

First, generate an ArchMap delta from a codebase or pull request.

Then run ArchSig using the team's selected LawPolicy.

The reviewer no longer has to read the entire diff as a flat pile of changes.

They can focus on the boundaries that require design judgment.

```text
This change touches:
  - authority boundary
  - generated output mediation
  - state/effect reconciliation
  - async provider job path

Measured pressure:
  - nonzero on permission coverage axis
  - positive path continuation defect on effect axis
  - architectural hole on output promotion path

Review focus:
  - entrypoint-level permission evidence
  - job finalization behavior
  - provider failure handling
  - persistence gate before domain promotion
```

AI agents can read the same packet.

They can implement with more than a request like:

> Just add the feature.

They can receive architectural constraints:

> Preserve this Atom.
>
> Do not cross this boundary.
>
> Do not increase pressure on this law axis.
>
> Do not treat these paths as equivalent; their effect order differs.

That matters because AI agents are strongly shaped by context.

If you give them only the codebase, you also give them every existing shortcut.

If you give them the ArchMap and the ArchSig analysis packet, you also give them the architecture's structural pressure and semantic coupling.

## Closing

ArchSig is not a tool for grading code.

It is an architecture analyzer for reading a codebase as an Atom map, then using AAT to surface design pressure, semantic coupling, holes, and repair preconditions.

It does not replace dependency graphs, lint, coverage, or security tools.

Those are still important.

But there are questions they do not answer:

- Where do authority and generated output intersect?
- Where does state/effect order diverge?
- Are two paths that create the same artifact really the same architecture operation?
- Would this repair candidate transfer complexity to another boundary?

Those are the questions ArchSig is built to make visible.

Start from Atoms.
Record them in ArchMap.
Read them through AAT.
Analyze them with ArchSig.

That is the architecture analysis shape I wanted to introduce.

## What Comes Next: SFT and FieldSig

We are also working on the next layer of this research.

AAT makes software architecture locally algebraic.

ArchSig becomes an observation instrument for that local algebra: it takes Atom observations and law-relative structure from a codebase and turns them into an analysis packet.

Beyond that is SFT, Software Field Theory.

SFT is about software evolution.

It does not only ask about the current architecture state.

It asks how review, AI agents, CI, operational feedback, and organizational decisions change the space of possible future software states.

FieldSig is the next measurement surface.

It reads ArchSig analysis packets and workflow evidence in order to make software evolution more computable.

ArchSig is the entrance.

That said, ArchSig is still at v0.3.1.

I do not want it to be judged as a finished product yet.

I want people to try it on many different repositories and tell us what it reads well, what it misses, and where the model feels wrong.

Good reads and bad reads are both valuable for the research.

You can get the ArchSig release bundles here:

[AlgebraicArchitectureTheoryV2 Releases](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/releases)
