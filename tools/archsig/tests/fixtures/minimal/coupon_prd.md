# Coupon PRD Forecast Pipeline

## Scope

- tools/archsig/src/main.rs
- tools/archsig/src/artifact_descriptor.rs
- tools/archsig/src/operation_support_estimate.rs
- tools/archsig/src/sft_forecasting.rs
- docs/tool/roadmap.md#phase-b13-sft-forecaster-implemented-pipeline

## Audience

- archsig-cli
- sft-forecaster-pipeline
- review-ci

## Request

Add an end-to-end CLI command that reads this Markdown PRD and emits
artifact-descriptor-v0, operation-support-estimate-v0, forecast-cone-skeleton-v0,
and consequence-envelope-report-v0 JSON artifacts.

The command should keep source refs, selected scope, measurement boundary,
forecast boundary, unknown remainder, and forecast non-conclusions across every
intermediate artifact.

The first implementation should include a Coupon PRD fixture, validator test,
and golden output for reviewer / CI inspection.

## Non-goals

- probability assignment
- causal outcome prediction
- global safety proof
- Lean theorem claim
- extractor completeness

## Open Questions

- TODO: runtime traces are not available in this Markdown PRD.
- TODO: accepted future PR history is not known at forecast time.
