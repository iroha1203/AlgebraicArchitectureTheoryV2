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
