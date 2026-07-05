# Coupon Forecast Descriptor Builder

## Scope

- tools/archsig/src/artifact_descriptor.rs
- tools/archsig/src/main.rs
- docs/tool/roadmap.md#phase-b13-sft-forecaster-implemented-pipeline

## Audience

- archsig-cli
- sft-forecaster-pipeline
- review-ci

## Request

Add a CLI command that reads a Markdown PRD and emits artifact-descriptor-schema050 JSON.
The descriptor should keep source refs, action class candidates, scope, missing
evidence, measurement boundary, and forecast non-conclusions.

The first implementation should include a fixture and validator test.

## Non-goals

- operation-support-estimate
- forecast-cone-probability
- causal-outcome-prediction

## Open Questions

- TODO: runtime traces are not available in this Markdown input.
