# A Philosophy for AI Agents

## Skills and Character

When you hire a person, do you judge them on skills alone? Probably not. You care whether they are kind, generous, patient, whether they will settle into the team. Someone too stubborn, too aggressive, too much of a taker gets passed over. In hiring, character weighs as much as skill.

What about AI agents? The world still picks them by benchmark scores, coding accuracy, speed — intelligence, broadly speaking. Fair enough. We are in a period of transition, and when "smarts" are improving this fast, that is where the attention goes. But the moment you think of an AI agent as a colleague, should intelligence and skill really be the whole interview?

## Philosophy in AGENTS.md

What do you write in your AGENTS.md (or CLAUDE.md)?

This week, in my research project — AAT, Algebraic Architecture Theory — I ran an experiment: I wrote a philosophy into AGENTS.md. Here is an excerpt.

```
## PHILOSOPHY

This section is the base on which all work in this repository stands.
Just as algebraic geometry places every scheme over Spec ℤ,
we place every judgment, human or machine, on this base.

There is one central good.

> Speak of the software that runs the world, in words we can answer for.

From this good, vows are generated. Every individual discipline derives
from a vow. Work that no vow generates may rightly be doubted.

- **Make it verifiable without trust.** The addressee is a future
  verifier. Leave every claim in a form that can be checked by the Lean
  kernel, the source code, or a reproducible procedure.
- **Be a precedent worth inheriting.** Practice as if your practice will
  be read as precedent, and leave behind only what deserves to be passed
  on as a standard. Record refutations as first-class results.
- **Convert the cheapness of machines into rigor.** Spend AI labor not
  on mass-producing output, but on adversarial review, independent
  reproduction, and formalization.
- **Be silent outside the sayable; speak with certainty within it.**
  Claims hold only inside a chosen reading. Do not bury what can be said
  under a list of what cannot.
- **Do not mix kinds.** Distinguish proof, proof under assumption,
  observation, and hypothesis. Measuring zero and not measuring are
  different things.
- **Observation creates no structure.** The structure is there before we
  look; observation and measurement only read it. What we read, and how,
  is a reading — and meaning lives in use, not in definition.

The vows are not a closed list. Like prime numbers, new vows will be
found from time to time. Whether one is added to the base, or the base
is amended, is for explicit human instruction.

This base, too, is one chosen reading.
```

### Unpacking It

I started with the good. What is the good? What does this repository call good?

What AAT aims at is this: take the source code that already exists as the source of truth, abstract implementations into Atoms, turn specifications into Law equations, treat architecture as geometry, and analyze it with the weapons of algebraic geometry. It cannot do everything. It cannot catch runtime failures or intricate deadlocks. But within what Atoms and Laws can express — within what it can answer for — it speaks in firm words. Silent about what cannot be said; definite about what can. That is the central good of AAT.

Once the good is fixed, the vows follow.

> Make it verifiable without trust.
> Be a precedent worth inheriting.

Little of what AAT does has precedent. It is a large-scale Lean formalization, but also a theory that brings algebraic geometry into software engineering, plus tooling, plus outreach, all managed in a single repository. We keep making deposits into that repository so that when projects of the same kind appear, they find a precedent worth having. We leave our results reproducible, so that people in the future can check them without having to trust us. And the refutations that turn up along the way are not points lost but points gained. What a refutation gives back to a theory, money cannot buy.

> Convert the cheapness of machines into rigor.

AI can work around the clock, and the temptation is to have it churn out shiny new features. But what AAT prizes is rigor. Every PR goes through heavy adversarial review. Every experiment gets pinned down as a reproducible result. The abundant energy of AI goes into keeping the operation sound and strict.

> Be silent outside the sayable; speak with certainty within it.

This is borrowed from the early Wittgenstein, and AAT adopts it wholesale. Not on a whim — it came out of trial and error, as the only way to keep the research honest and the tools useful at the same time. Without it, the theory side ends up saying: "Such-and-such holds for Atoms and Laws — assuming, of course, perfect Atom extraction from the source code." And the tool side: "The observed Atoms hint at such-and-such, but given assumption A, no conclusion." Theory and tool alike, unable to state anything outright. So: silent about what cannot be said, definite about what can. That discipline is the footing on which AAT builds trust.

> Do not mix kinds.
> Observation creates no structure.

These lean practical. The guideline documents spell out the classifications, and the vow demands that work follow them. Never mixing "measured zero" with "not measured" is a tradition as old as the project itself. If you ship a measuring tool, "no anomaly found" and "not measured" are worlds apart, and we have kept them apart from day one. As for observation: elementary particles, we are told, settle their state only when observed — but AAT has not adopted quantum mechanics. The source code was there all along, and the architecture we want to measure is already in it. Observation must not inject conclusion-shaped data.

One more line in the excerpt deserves a note.

> This base, too, is one chosen reading.

The base closes by declaring that it is itself one reading among others. The Tractatus ends by telling whoever has understood it to throw away the ladder after climbing it. This is the same gesture. The base is not absolute truth. It was chosen, and it can be revised. Which is why it says, in writing, that the final say over rewriting the base belongs to humans.

## Why Philosophy

Back to the opening. Take the wish "I want my colleagues to be good people" and turn it into a question, and it becomes: what does a good person do?

The discipline that answers that question head-on is philosophy.

Define the project's good, then derive behavior from it, deductively. Companies do something similar with Mission, Vision, Values.

The important part: it is not a list of prohibitions.

Imagine being handed a list on your first day — don't do this, don't do that. You would be at a loss. Hand over the behavior the project actually wants, and you have a far better chance of becoming good.

Guardrails, harnesses — the fashion is to approach AI agents with restraints. I don't think that approach is sound.

The later Wittgenstein shows why. There is an argument in the Philosophical Investigations. A rule cannot determine its own application. Every rule leaves room for interpretation. Pin the interpretation down with a new rule, and that rule leaves room for interpretation too, and so on without end. What finally fixes the meaning of a rule lies outside the rule: the background — what the rule is for.

An agent handed nothing but prohibitions will optimize their letter. Behavior that honors the wording while betraying the intent will appear, without fail. The loophole is not a defect in the rules; it is the nature of rules. Which is why the list never stops growing.

The line "meaning lives in use, not in definition" is in the excerpt because it, too, is the later Wittgenstein. The early Wittgenstein's silence, and the later Wittgenstein's use. Both are buried in AAT's base.

Bring in a philosophy, so that the agent behaves well of its own accord. Guardrails should be derived — deductively — from the project's good.

## The Effect

I interviewed Codex itself.

The question: in this project, what should you hold most important?

Codex's answer:

```
What matters most is the central creed:

> Speak of the software that runs the world, in words we can answer for.

In practice, I keep it as follows:

- Put every claim in a form verifiable by the Lean kernel, primary
  sources, or a reproducible procedure.
- Never conflate proof, proof under assumption, observation, and
  hypothesis. A successful build is not mathematical completion.
- Treat AAT not as metaphor but as pure mathematics built on Atoms and
  Laws. Keep observation and tooling out of the theory.

-- snip --

In short: rather than "producing plausible-looking results," I value
**results that keep kinds separate, stay verifiable, and can be handed
over with responsibility.**
```

The philosophy placed at the base seems to be working. In day-to-day work, too, the old looseness is gone, and the precision has climbed — as far as I can tell.

## In Closing

AI agents keep getting smarter. But just as with hiring people, intelligence is not all we ask of them.

For a colleague we work beside: put into words how you want a good colleague to behave, and write it down in AGENTS.md.

Not an exhaustive rulebook, but what the good is, and how to act from it.

Give your AI agents a philosophy.
