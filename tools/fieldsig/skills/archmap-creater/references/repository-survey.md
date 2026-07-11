# Repository Survey Guide

Use this guide before drafting ArchMap for an unfamiliar repository or unfamiliar subsystem. The goal is to build a bounded source inventory, not to understand the whole codebase.

## Survey Order

1. Read entry documents.
   - `README.md`, language-specific README files, tool README files
   - architecture docs when present
   - architecture docs, tool docs, and policy docs when present
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

- For component atoms, read the declaration or module boundary.
- For relation atoms, read both endpoints and the connecting evidence.
- For policy or contract atoms, read the relevant code and the policy/doc/test that gives it meaning.
- For context and cover membership, read the selected source and record only resolvable ids.
- For runtime or SFT readings, record the available source descriptor and keep unavailable evidence in review notes.

If a claim requires more reading than the current scope allows, keep it out of `atoms[]` or record the limitation in the source inventory and review notes.

## Drafting Order

Draft items in this order:

1. `sources` entries for the selected evidence.
2. `atoms` entries for source-grounded components, relations, or contracts.
3. `contexts` entries for selected finite site regions and atom membership.
4. `covers` entries for selected context coverage.

After drafting, revise coverage:

- semantic items require semantic coverage
- runtime claims require runtime coverage or missing evidence
- policy claims require assumed or measured policy coverage
- dynamic/framework boundaries should not become measured zero

## Stop Conditions

Stop surveying when:

- the selected source inventory is enough to support the requested architecture slice
- remaining files would broaden scope rather than improve evidence
- relevant evidence is private or unavailable and can be recorded as such
- validation can be run on a bounded draft

Do not keep reading indefinitely to chase global completeness. ArchMap is selected, bounded evidence.
