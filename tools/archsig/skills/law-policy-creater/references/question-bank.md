# LawPolicy Question Bank

Ask only the questions needed for the target scope. Prefer 3-6 high-signal questions over a long interview.

## Core Scope

- Which subsystem or repository slice should this LawPolicy govern?
- Is the policy intended for strict review, exploratory diagnosis, release gating, or migration planning?
- Should the policy apply to all code, or only selected routes/services/jobs/models/providers?

## Dependency And Layering

- Are there dependency directions that must hold?
- Which components are allowed to depend on infrastructure, repositories, providers, or frameworks?
- Are cyclic dependencies forbidden, tolerated, or out of scope?

## Authority And Tenancy

- Which permission checks are mandatory for routes or commands?
- What tenant/workspace/org boundaries must be preserved?
- Are admin bypasses allowed, and if so under what explicit constraints?

## State, Effects, And Runtime

- Which operations must be idempotent or replay-safe?
- Which state changes must commit before or after external effects?
- What retry, compensation, rollback, or finalization behavior is required?
- What runtime traces, logs, or tests are required before a zero axis is trusted?

## Provider, LLM, And External Boundary

- Which provider outputs must be validated, filtered, or translated before persistence?
- Are LLM/tool outputs allowed to become domain facts directly?
- Which secrets, tokens, webhook signatures, or provider identities are trust boundaries?

## Semantic Contracts

- Which domain meanings or DTO/API contracts are important enough to become selected laws?
- Which tests or docs define semantic correctness for the target scope?
- Which mismatches should become ArchSig obstruction witnesses versus review-only concern hints?

## Coverage And Exactness

- What evidence is required for zero-reading to be meaningful?
- Which evidence is unavailable and must remain an observation gap?
- Which claims must the policy explicitly exclude?

## ACTS / Spectrum Profile

- Which review decision should `ArchitectureSpectrumReport` support: hotspot triage, split planning, migration planning, release review, or evidence-gap discovery?
- Which selected axes should enter `spectrumMeasurementProfile.selectedAxisRefs`, and what repo/user-approved law justifies each axis?
- Which witness rules are measured, and what ArchMap atom families or source refs support those witnesses?
- Which distance kinds are defensible for each axis: boolean mismatch, witness mismatch count, support overlap, calibrated severity, or another project-defined distance?
- Are weights unit weights, bounded ordinal weights, or calibrated from repository evidence?
- What should count as transfer evidence: shared witness support, shared Atom refs, shared molecule support, runtime trace overlap, or an explicitly documented dependency relation?
- What should the report rank first: nonzero hotspots, recurrent obstruction modes, witness clusters, coverage gaps, or boundary-preparation actions?
- Which missing docs, tests, traces, logs, or source refs should block zero-reflection and remain unresolved questions?

## Homotopy / Holonomy / Stokes Profile

- Which path alternatives should `ArchitectureHomotopyReport` compare: interface/implementation, cache/repository, policy/runtime, source/DTO, provider/domain, or another project-specific path pair?
- Which selected axes justify comparing those paths, and what repo/user-approved law backs each axis?
- What evidence is required before an LLM may propose a candidate path: ArchMap observations, source refs, docs, tests, runtime traces, or explicit user intent?
- What endpoint policy should hold for candidate paths: shared source refs, shared Atom refs, same domain object, same operation, same API contract, or another bounded relation?
- What counts as filler evidence: contract docs, tests, runtime traces, policy docs, source implementations, review notes, or explicit user confirmation?
- Which missing filler evidence should become an architectural hole instead of a violation finding?
- Which distance kind is defensible for holonomy: selected-axis continuation distance, boolean mismatch, semantic witness mismatch, state/effect mismatch, or project-defined distance?
- Which coverage gaps should block zero and Stokes-style local-curvature readings: missing tests, missing runtime traces, missing policy docs, unresolved source refs, or ambiguous endpoints?
- Which claims must be excluded: path truth, global homology, architecture score, automatic violation proof, future incident prediction, or repair-safety proof?
