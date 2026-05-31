---
name: archsig-reader
description: Run ArchMap artifacts through ArchSig, read archsig-analysis-packet-v0 outputs, compare the findings against source code evidence, and propose bounded architecture improvements. Use when Codex is asked to analyze an ArchMap with ArchSig, interpret ArchSig output, review workflow risk / spectral / transfer bridge / split readiness readings, validate ArchSig artifacts, or turn ArchSig analysis into concrete source-review and improvement proposals.
---

# ArchSig Reader

## Purpose

Turn a supplied `archmap-observation-map-v0` into an ArchSig analysis, read the
resulting structured packet as an architecture quality measurement over the
supplied `ArchMap + LawPolicy`, and propose practical improvements.

For user-facing reports, state the measured conclusion first. ArchSig should
read as a structural measurement over the supplied ArchMap + LawPolicy: "for
this input model, these axes are nonzero, these hotspots were measured, and
these loops are unfilled." Claim boundaries remain available as metadata, but
they should not dilute the main verdict.

When the reader is used during ArchMap authoring, treat the output as a
complete-first feedback source. `blockedByCoverageGap`, unfilled loops,
missing filler evidence, and unmeasured spectrum support are repair targets for
the authoring pass, not final user homework. Report only truly
unavailable/private/out-of-scope evidence as residual gaps.

This skill must work with only:

- a built `archsig` executable
- this skill directory, including `references/`
- the user's ArchMap, source repository, and any supplied LawPolicy

Do not require the ArchSig source repository, `docs/tool`, AAT mathematical documents, test fixtures, Cargo project files, or Git history. Those may help during development, but they are not runtime dependencies for the released skill bundle.

## Inputs

Collect:

- ArchMap path, usually `.archsig/<scope>/archmap.json` or `.archsig/archmap/archmap.json`
- LawPolicy path, if supplied
- output directory for fresh artifacts
- repository root or source paths needed for evidence comparison
- user goal: quick diagnosis, detailed review, improvement proposals, public note, or PR planning

If the user does not provide a LawPolicy, look for one in this order:

1. the ArchMap directory, such as `law_policy.json` or `interpretation_profile.json`
2. existing sibling output packet `selectedLawPolicyRef.path`

State which LawPolicy was used. If no project-specific LawPolicy is found, stop before user-facing analysis and ask for a LawPolicy or explicit approval to run the bundled baseline policy as a smoke check.

The bundled `references/default_law_policy.json` is not an analysis default. It exists only so a released skill bundle can verify that the ArchSig binary and packet-reading workflow operate without the ArchSig source repository. Use it only when the user explicitly asks for a generic baseline / smoke test, or explicitly approves that the output will be LawPolicy-generic and not a project-specific architectural diagnosis.

## Run Workflow

Use a fresh output directory. Do not overwrite user-authored ArchMap files.

Resolve the skill directory from the loaded skill path when possible. In examples below, set `SKILL_DIR` to this `archsig-reader` directory.

Resolve the ArchSig binary before running:

1. use `ARCHSIG_BIN` when the environment variable is set
2. use `archsig` from `PATH`
3. look for released binaries near the skill bundle, such as `bin/archsig`, `../bin/archsig`, or `../../bin/archsig`
4. if working inside a source checkout, optionally use an already-built checkout binary such as `tools/archsig/target/release/archsig` or `tools/archsig/target/debug/archsig`

If none exists, stop and ask the user for the binary path. Do not require Cargo or the ArchSig source tree in a released skill-only environment.

Before passing a LawPolicy-like file to ArchSig, verify it is JSON with `schemaVersion: "law-policy-v0"`. The file may be named `interpretation_profile.json`, but the schema must still be `law-policy-v0`. If the schema is absent or different, do not pass it as LawPolicy; continue the search order or ask the user.

```bash
SKILL_DIR=<path-to-archsig-reader-skill>
LAW_POLICY=<project-law-policy.json>
ARCHSIG_BIN=${ARCHSIG_BIN:-archsig}

"$ARCHSIG_BIN" analyze \
  --archmap <archmap.json> \
  --law-policy "$LAW_POLICY" \
  --out-dir <out-dir>
```

Expected files:

- `archmap-validation.json`
- `law-policy-validation.json`
- `archsig-analysis-packet.json`
- `archsig-analysis-validation.json`
- `llm-interpretation-packet.json`

Then summarize the packet with ArchSig:

```bash
"$ARCHSIG_BIN" analysis-summary \
  --packet <out-dir>/archsig-analysis-packet.json \
  --archmap-validation <out-dir>/archmap-validation.json \
  --law-policy-validation <out-dir>/law-policy-validation.json \
  --analysis-validation <out-dir>/archsig-analysis-validation.json \
  --out <out-dir>/archsig-analysis-summary.json
```

Read `references/output-reading-guide.md` from this skill directory for the field priority.

## Standalone Resource Checklist

Before assuming a path exists, check whether it is part of the release bundle:

- `analysis-summary` is provided by the `archsig` binary.
- `references/output-reading-guide.md` is bundled and may be read for packet interpretation.
- `references/default_law_policy.json` is bundled only for explicit generic baseline / smoke-test runs. Do not silently use it for project analysis.
- Repository docs, fixtures, and source-code tests are not bundled; never make them required for this skill to operate.

## Reading Workflow

Read in this order:

1. Validation summaries
   - Stop and report blockers if any failed check exists.
   - Keep warnings visible; warnings are often coverage or projection boundaries, not tool failures.

2. Verdict and quality measurement
   - Prefer `archsig-analysis-summary.json` when available.
   - Read the whole summary before opening raw packet details. Start with
     `verdict`, `qualityMeasurement`, `dominantFindings`, `actionQueue`,
     `axisSummary`, `workflowRiskSummary`, `architecturalHoleSummary`,
     `bridgeSummary`, `coverageGapSummary`, `detailIndex`, and
     `measurementBasis`.
   - Say what the supplied ArchMap + LawPolicy measured: flat/nonflat under selected policy, nonzero axes, hotspots, recurrent pressure, architectural holes, workflow risk, bridge pressure, and review action queue.
   - Treat `actionQueue` as the full compact queue. Its entries should carry
     `detailRefs`; do not expect nested support/source/witness evidence arrays
     in the summary.
   - If the run is part of complete ArchMap authoring, convert coverage
     blockers into a missing-evidence queue before handing the artifact to the
     user.
   - If the bundled baseline LawPolicy was explicitly used, label the output as a generic baseline run and avoid project-specific obstruction conclusions unless source comparison and user context justify them.

3. Analysis basis
   - Record `archMapRef`, `selectedLawPolicyRef`, `currentStateEvolutionBoundary`, `excludedReadings`, `metadata.nonConclusions`, and the `detailIndex`.
   - Treat the basis as input metadata, not as the lead diagnosis.

4. Flatness and signature axes
   - Prefer `axisSummary` and `coverageGapSummary` in the summary.
   - Use `detailRefs` / `detailIndex` to inspect `flatnessReading.status`, `zeroSignatureAxisRefs`, `nonzeroSignatureAxisRefs`, `blockedByCoverageGaps`, and `signatureAxes[]` in the packet only when source-level detail is needed.
   - Treat nonzero axes as measured architecture pressure under the selected policy.
   - Treat coverage gaps as measurement basis for why zero was not measured.

5. Dominant pressure
   - Use `dominantFindings`, `actionQueue`, `workflowRiskSummary`, `architecturalHoleSummary`, and `bridgeSummary` before opening raw packet sections.
   - Follow summary `detailRefs` into `architectureSpectrumReport` when the review needs full hotspot, recurrent obstruction, witness cluster, coverage gap, measured boundary, or review focus detail.
   - Treat the report as a current-state architecture quality measurement over
     the selected axes only after checking `measurementStatus` and
     `readingBoundary`; proxy transfer readings and coverage-blocked rows are
     not measured zero.
   - Move report-level `nonConclusions[]` to metadata or a short appendix.
   - Follow summary `detailRefs` into `architectureHomotopyReport` when the review needs full nonzero holonomy loop, unfilled loop, local curvature, aggregate reading, coverage gap, measured boundary, or review focus detail.
   - Treat filled/unfilled loops, hole readings, and Stokes-style readings as
     measured review queues only inside their `measurementStatus`,
     `readingBoundary`, filler evidence, and non-fillability witness boundary.
   - Move report-level `nonConclusions[]` to metadata or a short appendix.
   - Follow summary `detailRefs` into `workflowRiskReadings[]` by `riskScore` when needed.
   - Read `spectralAnalysisReadings[]` only as packet detail when the compact summary points to spectral pressure or when source comparison needs dominant workflow rows, dominant axis columns, molecule overlap hubs, obstruction curvature, or operation delta coupling.
   - If workflow risk or spectral readings are empty, do not force a risk narrative. Shift to `signatureAxes[]`, `obstructionCircuits[]`, `repairOperationCandidates[]`, `operationDeltas[]`, and coverage gaps.

6. Transfer bridge and split readiness
   - Start from `bridgeSummary` and `actionQueue` bridge-pressure entries.
   - Follow their `detailRefs` into `transferBridgeReadings[].bridgeAtomFamilies[]` and `edgeBreakdowns[]` before surfacing edge source refs, source ref rationale, dependency kind, cut kind, or review focus.
   - Read `splitReadinessReadings[]` sorted by low `readinessScore`; low score and `blockedByBridgeEdge` usually means boundary preparation should precede refactoring.
   - If transfer bridge or split readiness readings are empty, report that no bridge/split surface was emitted for this packet variant and prioritize obstruction / repair / coverage evidence instead.

7. LLM interpretation packet
   - Use `detailIndex` to reach `llmInterpretationPacket.recommendedHumanReviewFocus`, `structuralReadingReviewSummary`, `currentStateEvolutionBoundarySummary`, and `transferBridgeEdgeSummary` when the compact summary is not enough.
   - Do not treat the LLM packet as a separate source of truth.

8. Packet variant fallback
   - Some valid packets are obstruction/repair/coverage-heavy and have empty `workflowRiskReadings`, `spectralAnalysisReadings`, `transferBridgeReadings`, or `splitReadinessReadings`.
   - In that case, summarize nonzero `signatureAxes[]`, constructed `obstructionCircuits[]`, `repairOperationCandidates[]`, `operationDeltas[]`, `flatnessReading.blockedByCoverageGaps`, and child-level `missingEvidence` / `excludedReadings`.
   - Source comparison should then start from obstruction and repair candidate `sourceRefs`, not from workflow or bridge edges.

## Source Comparison Workflow

Always compare high-priority readings against real source evidence before proposing changes.

1. Select a small review queue:
   - top ArchitectureSpectrumReport hotspots with witness refs and coverage gaps
   - recurrent obstruction entries with transfer edge refs
   - top witness clusters that connect several axes or support refs
   - ArchitectureHomotopyReport nonzero holonomy loops, unfilled loops, missing filler evidence, local curvature cells, operation sequences, continuation traces, and recommended review focus
   - top 2-4 workflow risk molecules
   - transfer bridge edges with high `reviewRisk`
   - low split-readiness molecules
   - nonzero signature axes and their source refs
   - coverage gaps blocking the user's decision

2. Resolve source refs:
   - Use ArchMap `sourceUniverse.includedRefs[]` and packet `sourceRefs` to find files, symbols, sections, or tests.
   - If a ref cannot be resolved locally, report it as an evidence gap instead of guessing.

3. Inspect code:
   - Use `rg`, `sed`, language-aware tests, and local docs.
   - Check whether source evidence supports the ArchSig reading.
   - Distinguish confirmed source evidence, plausible but unverified interpretation, and contradicted/stale evidence.

4. Propose improvements:
   - During complete ArchMap authoring, start with evidence repair: read or add
     source refs, docs, tests, runtime traces, policy files, filler evidence,
     or targeted non-fillability gaps. Do this before proposing product or code
     refactors.
   - For user-facing architecture review after the ArchMap is complete, start
     with review actions that reduce uncertainty: route audit, runtime trace
     capture, provider log review, test evidence, model relationship audit.
   - For homotopy readings, start by resolving source refs for path pairs, checking whether filler evidence exists, and deciding whether missing filler evidence should stay as a coverage gap or become a project law question.
   - Then propose architecture changes only where source evidence supports the pressure: policy boundary, transaction boundary, anti-corruption layer, interface contract, idempotency/retry/status finalization, provider output validation.
   - Keep proposals tied to source refs and ArchSig fields.

## Output Shape

For a normal user report, answer in this order:

1. Verdict
2. Quality Measurement
3. Top Hotspots / Holes
4. Action Queue
5. Measurement Basis
6. Source-code comparison findings, when source comparison was requested
7. Metadata / non-conclusions, only when useful for the user's decision

Use concise Japanese when working in this repository.

Recommended phrasing:

- "ArchSig measured this as..."
- "For this ArchMap + LawPolicy, the verdict is..."
- "The selected law axes measured nonzero pressure..."
- "This loop is an unfilled architectural hole in the supplied model..."
- "Source comparison supports / partially supports / does not yet support this reading..."
- "The next useful improvement is..."

Avoid:

- "This proves a violation"
- "This is definitely broken"
- "The architecture score is..."
- "No risk exists because the axis is zero"
- "ArchSig recommends this refactor automatically"
- leading with long caveats before the measured verdict
- treating `ArchitectureSpectrumReport` as FieldSig forecast, future incident prediction, empirical cost amplification, or repair safety evidence
- treating `ArchitectureHomotopyReport` as path truth, global homology, automatic violation proof, a quality score, FieldSig forecast, or repair safety evidence

## Maintainer Validation

When editing this skill inside a source checkout, validate the skill metadata. This command is a maintenance check, not a runtime requirement for released skill users:

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- analysis-summary \
  --packet tools/archsig/tests/fixtures/minimal/archsig_analysis_packet.json \
  --out .lake/archsig-reader-summary-validation.json
```

If the skill-creator validator is available in the local Codex installation, run it too. If it is missing dependencies such as `PyYAML`, report that as an environment issue rather than a skill runtime blocker.

Do not make source-repository tests a prerequisite for released skill usage.
