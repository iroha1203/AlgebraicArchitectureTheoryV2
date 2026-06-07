# LawPolicy v1 Question Bank

Ask only what is needed to select evaluator manifests.

## Scope

- Which subsystem or repository slice should the policy cover?
- Should the policy be advisory review, strict CI gate, or exploratory diagnosis?
- Which source id prefixes should be in `scope`?

## Policy Selection

- Does the repository explicitly adopt SOLID? If yes, use `pack: "solid@1"`.
- Is domain-to-infrastructure dependency forbidden? If yes, use `domain.no-direct-infra-dependency@1`.
- Are there project-specific policies that need a registry evaluator before they can be selected?

## Basis

- Which docs, ADRs, standards, or direct user decisions justify the policy?
- Should the basis be `policy-basis:solid`, `policy-basis:layering`, or a future registry basis ref?

## Severity

- Should a measured violation be review-only, warning, or error?

## Out Of Scope

Do not ask users to hand-author:

- witness predicates
- signature axes
- coverage rules
- exactness assumptions
- distance formulas
- spectrum or homotopy profiles

If those are needed, the evaluator registry must grow first.
