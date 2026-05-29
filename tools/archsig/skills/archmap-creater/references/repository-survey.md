# Repository Survey Guide

Use this guide before drafting ArchMap for an unfamiliar repository or unfamiliar subsystem. The goal is to build a bounded source inventory, not to understand the whole codebase.

## Survey Order

1. Read entry documents.
   - `README.md`, language-specific README files, tool README files
   - architecture docs when present
   - tool docs and policy docs when present
   - AAT/SFT boundary docs when present

2. Identify executable and library entrypoints.
   - CLI command definitions
   - application main files
   - package/module roots
   - public library exports
   - workflow or job entrypoints

3. Identify architecture source candidates.
   - domain services, controllers, routes, handlers
   - core modules, adapters, framework integration points
   - policy/config files
   - tests that express contract, behavior, or invariants
   - runtime edge artifacts, logs, traces, or adapter output when supplied

4. Identify semantic evidence.
   - tests with domain names or contract language
   - docs that define responsibilities, layers, policies, workflows, or state transitions
   - theorem names, Lean definitions, examples, fixtures, golden outputs
   - event, saga, workflow, projection, migration, or lifecycle code

5. Identify blind spots.
   - generated code
   - dynamic import or plugin loading
   - framework convention expansion
   - private policies, private registries, private customer rules
   - runtime traces that are absent
   - external services that are referenced but not inspected

## Fast File Discovery

Prefer fast, bounded discovery:

```bash
rg --files
rg -n "SEARCH_PATTERN" <selected-path>
```

Useful search patterns:

```text
import|from .* import|require\(
route|handler|controller|service|adapter|repository
workflow|operation|command|event|state|transition
saga|compensation|rollback|projection|read model|event store
policy|layer|boundary|dependency|forbidden|allowed
contract|invariant|golden|fixture|example|theorem
runtime|trace|plugin|dynamic|framework|convention
```

Use the results to select evidence. Do not add all matches to the source inventory.

## Source Inventory Construction

Create a compact inventory with these groups:

- `includedRefs`: evidence actually read and used
- `excludedRefs`: intentionally out-of-scope files, generated artifacts, vendor/build outputs
- `unavailableRefs`: relevant artifacts known to exist but unavailable
- `privateRefs`: relevant private artifacts not inspected
- `knownBlindSpots`: dynamic/framework/runtime areas that may affect interpretation
- `selectionBoundary`: one sentence explaining the bounded slice

Prefer 5-20 high-value included refs for an initial ArchMap. A small accurate ArchMap is better than a large speculative one.

## Reading Depth

Read enough to support claims:

- For component existence atom observations, read the declaration, module boundary, or entrypoint evidence.
- For relation atom observations, read both endpoints and the connecting evidence.
- For capability, state, effect, authority, trust, contract, runtime, or semantic atom observations, read the specific source that supports that primitive fact.
- For molecule observations such as responsibility, read the atom observations plus the policy/doc/test/code that gives the composed role meaning.
- For semantic observations, read the test/spec/doc/fixture/code that observes the behavior, workflow, meaning, or commutation cue.
- For SFT projection hints, read the operation/workflow/state source and record missing runtime/calibration evidence.

If a claim requires more reading than the current scope allows, keep it out of `atomObservations[]` / `semanticObservations[]` or record it as an `observationGaps[]` entry.

## Drafting Order

Draft observations in this order:

1. `atomObservations[]` for selected primitive facts: existence, relation, capability, state, effect, authority, trust, contract, semantic fact, or runtime interaction.
2. `moleculeObservations[]` for composed roles such as responsibility over atom observation refs.
3. `semanticObservations[]` for source-supported meanings, workflows, contract readings, behavior readings, or commutation cues.
4. `observationGaps[]` for runtime, framework convention, generated code, dynamic loading, private, unavailable, or unsupported evidence.
5. `projectionInfo[]` for downstream AAT/SFT handoff hints such as `operationCandidate`, `workflowCandidate`, `stateTransitionCandidate`, or `testOracleCandidate`.
6. `concernHints[]` for review cues over observations, never for obstruction circuits.

After drafting, revise coverage:

- semantic observations require semantic source support
- runtime atom observations require runtime evidence, otherwise record a gap
- policy readings require assumed or measured policy source support
- dynamic/framework boundaries should not become measured zero

## Stop Conditions

Stop surveying when:

- the selected source inventory is enough to support the requested architecture slice
- remaining files would broaden scope rather than improve evidence
- relevant evidence is private or unavailable and can be recorded as such
- validation can be run on a bounded draft

Do not keep reading indefinitely to chase global completeness. ArchMap is selected, bounded evidence.
