---
name: archsig-reader
description: Run ArchMap artifacts through ArchSig, read archsig-analysis-packet-v0 outputs, compare the findings against source code evidence, and propose bounded architecture improvements. Use when Codex is asked to analyze an ArchMap with ArchSig, interpret ArchSig output, review workflow risk / spectral / transfer bridge / split readiness readings, validate ArchSig artifacts, or turn ArchSig analysis into concrete source-review and improvement proposals.
---

# ArchSig Reader

## Purpose

Turn a supplied `archmap-observation-map-v0` into an ArchSig analysis, read the resulting structured packet, verify the packet against source evidence, and propose practical improvements without overclaiming.

ArchSig reads current AAT structural state from `ArchMap + LawPolicy`. It does not prove source completeness, architecture lawfulness, semantic correctness, zero curvature, forecast correctness, repair safety, or Lean theorem discharge.

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

2. Analysis boundary
   - Record `archMapRef`, `selectedLawPolicyRef`, `currentStateEvolutionBoundary`, `nonConclusions`, and `excludedReadings`.
   - Avoid saying "the architecture is bad/good"; say "under this selected LawPolicy and bounded ArchMap, ArchSig reads..."
   - If the bundled baseline LawPolicy was explicitly used, label the output as a generic baseline run and avoid project-specific obstruction conclusions unless source comparison and user context justify them.

3. Flatness and signature axes
   - Read `flatnessReading.status`, `zeroSignatureAxisRefs`, `nonzeroSignatureAxisRefs`, `blockedByCoverageGaps`, and `signatureAxes[]`.
   - Treat nonzero axes as review pressure, not defect proof.
   - Treat coverage gaps as unknown remainder, not measured zero.

4. Dominant pressure
   - Read `architectureSpectrumReport` before building the review queue when present.
   - Prioritize `topHotspots[]`, `recurrentObstructions[]`, `topWitnessClusters[]`, `coverageGaps[]`, `measuredBoundary`, and `recommendedReviewFocus[]`.
   - Treat the report as a codebase-inspection surface over current ArchSig measurements, not a quality score, forecast, or repair proof.
   - Preserve report-level `nonConclusions[]` when summarizing.
   - Read top `workflowRiskReadings[]` by `riskScore`.
   - Read `spectralAnalysisReadings[]`, especially dominant workflow row, dominant axis column, molecule overlap hub, obstruction curvature, and operation delta coupling.
   - If workflow risk or spectral readings are empty, do not force a risk narrative. Shift to `signatureAxes[]`, `obstructionCircuits[]`, `repairOperationCandidates[]`, `operationDeltas[]`, and coverage gaps.

5. Transfer bridge and split readiness
   - Read `transferBridgeReadings[].bridgeAtomFamilies[].edgeBreakdowns[]`.
   - Surface each edge's `sourceRefs`, `sourceRefRationale`, `dependencyKind`, `recommendedCutKind`, and `reviewFocus`.
   - Read `splitReadinessReadings[]` sorted by low `readinessScore`; low score and `blockedByBridgeEdge` usually means boundary preparation should precede refactoring.
   - If transfer bridge or split readiness readings are empty, report that no bridge/split surface was emitted for this packet variant and prioritize obstruction / repair / coverage evidence instead.

6. LLM interpretation packet
   - Use `llmInterpretationPacket.recommendedHumanReviewFocus`, `structuralReadingReviewSummary`, `currentStateEvolutionBoundarySummary`, and `transferBridgeEdgeSummary` as a human-review index.
   - Do not treat the LLM packet as a separate source of truth.

7. Packet variant fallback
   - Some valid packets are obstruction/repair/coverage-heavy and have empty `workflowRiskReadings`, `spectralAnalysisReadings`, `transferBridgeReadings`, or `splitReadinessReadings`.
   - In that case, summarize nonzero `signatureAxes[]`, constructed `obstructionCircuits[]`, `repairOperationCandidates[]`, `operationDeltas[]`, `flatnessReading.blockedByCoverageGaps`, and child-level `missingEvidence` / `excludedReadings`.
   - Source comparison should then start from obstruction and repair candidate `sourceRefs`, not from workflow or bridge edges.

## Source Comparison Workflow

Always compare high-priority readings against real source evidence before proposing changes.

1. Select a small review queue:
   - top ArchitectureSpectrumReport hotspots with witness refs and coverage gaps
   - recurrent obstruction entries with transfer edge refs
   - top witness clusters that connect several axes or support refs
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
   - Start with review actions that reduce uncertainty: route audit, runtime trace capture, provider log review, test evidence, model relationship audit.
   - Then propose architecture changes only where source evidence supports the pressure: policy boundary, transaction boundary, anti-corruption layer, interface contract, idempotency/retry/status finalization, provider output validation.
   - Keep proposals tied to source refs and ArchSig fields.

## Output Shape

For a normal user report, answer in this order:

1. Run result and artifact paths
2. Validation status
3. Main architecture readings
4. Source-code comparison findings
5. Improvement proposals and next checks
6. Claim boundary / non-conclusions

Use concise Japanese when working in this repository.

Recommended phrasing:

- "ArchSig reads this as..."
- "The packet marks this as `needsReview` because..."
- "Source comparison supports / partially supports / does not yet support this reading..."
- "The next useful improvement is..."

Avoid:

- "This proves a violation"
- "This is definitely broken"
- "The architecture score is..."
- "No risk exists because the axis is zero"
- "ArchSig recommends this refactor automatically"
- treating `ArchitectureSpectrumReport` as FieldSig forecast, future incident prediction, empirical cost amplification, or repair safety evidence

## Maintainer Validation

When editing this skill inside a source checkout, validate the skill metadata. This command is a maintenance check, not a runtime requirement for released skill users:

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- analysis-summary \
  --packet tools/archsig/tests/fixtures/minimal/archsig_analysis_packet.json \
  --out .lake/archsig-reader-summary-validation.json
```

If the skill-creator validator is available in the local Codex installation, run it too. If it is missing dependencies such as `PyYAML`, report that as an environment issue rather than a skill runtime blocker.

Do not make source-repository tests a prerequisite for released skill usage.
