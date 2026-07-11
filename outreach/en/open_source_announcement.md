---
title: "I Open-Sourced the AAT / SFT Research Repository"
published: false
description: "A short introduction to the AAT / SFT repository: Lean formalization, ArchSig tooling, and research notes for making software evolution computable."
tags: opensource, architecture, lean, softwareengineering
---

I open-sourced the AAT / SFT research repository.

Repository:

https://github.com/iroha1203/AlgebraicArchitectureTheoryV2

This repository is for building theory and tools that treat software architecture not only as a blueprint or a list of best practices, but as something that keeps evolving through changes, reviews, CI, operations, and proposals from AI agents.

The larger goal is to make the evolution of software and computers something we can measure, compare, and reason about, instead of only looking back after the fact.

## What This Research Is About

The repository is organized around three ideas.

```text
AAT makes architecture locally algebraic.
ArchSig makes architecture observable.
SFT makes software evolution computable.
```

**AAT** stands for Algebraic Architecture Theory.

It treats software architecture as a local algebraic structure.

In more practical terms, it asks questions like these:

- Did this design change preserve dependency direction?
- Did it cross a layer boundary?
- Does it still depend on abstractions instead of concrete details?
- Did it make failures easier to spread?

**ArchSig** is a set of tools for extracting architecture signals from real codebases and pull requests.

It is not meant to produce one big "good / bad" score. Instead, it separates different kinds of risk: dependency cycles, boundary violations, abstraction leaks, unmeasured parts of the system, and other signals that should be read separately.

**SFT** stands for Software Field Theory.

It treats software evolution as a sequence of changes and tries to make that evolution computable.

PRDs, issues, pull requests, reviews, CI, organizations, and AI agents do not only affect the current change. They also shape what kind of change is likely to happen next.

For example, a vague PRD can invite an ad hoc implementation. A codebase with clear boundaries tends to make the next change easier to place cleanly. SFT develops concepts for reasoning about what futures become easier to reach after a change.

## Why I Am Building This

AI can generate working code very quickly.

But whether a fast diff makes future changes easier, or instead adds more ad hoc implementation, is a different question.

The question is not only:

> Do the tests pass?

I also want to ask:

- Did this change preserve the design properties we care about?
- If not, what code or dependency shows the problem?
- Is the problem a dependency cycle, a boundary violation, or an abstraction leak?
- Does this PRD, issue, or pull request make the next change easier to move in a good direction?
- Can review and CI stop risky change patterns early?

The motivation behind this repository is to turn those questions into something we can formalize, observe, and eventually support with tools.

## What Is In The Repository

The repository currently contains:

- Lean formalization for AAT
- Research notes for AAT and SFT
- Rust implementation of the ArchSig tools
- Open proof tasks and a Lean theorem index
- A static website for reading AAT, SFT, and ArchSig

On the Lean side, I am building small theorem packages with explicit assumptions.

On the Rust tooling side, I am working toward reports that extract design signals from codebases and pull requests, then make them readable in review and CI.

On the website side, I am preparing public-facing research notes and manuals for AAT, SFT, and ArchSig.

## This Is Still Research

This repository is a working research space, not a finished product.

I separate different kinds of claims:

- what has been proved mathematically,
- what has only been defined so far,
- what I want to prove later,
- and what should be checked against real development data.

For example, a theorem proved in Lean does not automatically predict the future of a real project.

There is a difference between a tool saying "this dependency was observed," Lean proving "this property follows under these assumptions," and empirical work saying "this trend seems to appear in real development data."

The repository keeps those claims separate.

## Where To Start

The README is the best entry point.

https://github.com/iroha1203/AlgebraicArchitectureTheoryV2

If you want to go deeper, I recommend this order:

1. Research goal
2. AAT algebraic-geometric mathematical text
3. AAT / SFT interface
4. Software Field Theory
5. Lean definitions and theorem index
6. ArchSig tooling documentation

## Website

There is also a website for reading AAT, SFT, and ArchSig as connected research notes.

https://iroha1203.dev

If you want the big picture before reading code or proof details, the website is the easier place to start.

## Closing

The short version is:

> I want to treat software architecture and software evolution as things we can observe, diagnose, and compute.

I do not want design principles to remain slogans.

I want to ask what properties they preserve, what failures they reveal, and what futures they make easier to reach.

This repository is where I am building the theory, formalization, tools, and public notes for that direction.
