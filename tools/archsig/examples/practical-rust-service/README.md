# Practical Rust Commerce Fulfillment Example

This example is a production-shaped ArchSig demo target. It is a 3,000+ line
Rust commerce fulfillment service with domain objects, application ports,
in-memory infrastructure adapters, policy evaluation, telemetry, and an
executable demo scenario.

ArchSig itself is not modified by this example. The demo supplies source code,
an `archmap/v0.5.0` observation artifact, and a `law-policy/v0.5.0` selector,
then runs the existing `archsig analyze` workflow.

## What This Demonstrates

- A realistic Rust application using layered architecture, dependency inversion,
  port/adapter boundaries, value objects, and explicit policy rules.
- ArchMap atom extraction constrained to the current AAT atom vocabulary:
  `component`, `relation`, `capability`, `state`, `effect`, `authority`,
  `contract`, `semantic`, and `runtime`.
- ArchMap atoms are source-grounded observations only. They do not pre-label
  mismatch, obstruction, violation, safety, or lawfulness; those readings belong
  to LawPolicy-selected evaluators and generated ArchSig artifacts.
- A latest-shape `archmap/v0.5.0` finite poset site with contexts and a selected
  cover.
- A `law-policy/v0.5.0` policy that selects SOLID/layering rules and an AG
  measurement profile for `archsig-measurement-packet/v0.5.0`.
- Rich viewer output through `archsig-atom-viewer-data/v0.5.0`: 60 atom nodes,
  78 atom edges, 7 context groups, 10 visual scenes, guided tours, an insight
  queue, and an action queue.

## Layout

```text
sample/
  Cargo.toml
  src/
    domain.rs     # value objects, aggregates, events, decisions
    app.rs        # application service and port traits
    store.rs      # in-memory adapter bundle implementing the ports
    policy.rs     # production-style policy catalog and evaluator
    telemetry.rs  # trace and presentation surface
    scenario.rs   # executable demo scenario
archmap/
  source_inventory.json
  archmap.json    # latest archmap/v0.5.0 source-grounded observation
law_policy/
  law_policy.json # law-policy/v0.5.0 selector and measurement profile
runtime/
  place_order_trace.json
  concurrent_reservation_trace.json
scripts/
  run_archsig_demo.sh
```

## Run The Application

```bash
cargo test --manifest-path tools/archsig/examples/practical-rust-service/sample/Cargo.toml
cargo run --manifest-path tools/archsig/examples/practical-rust-service/sample/Cargo.toml
```

The smoke run prints the released order, reservation count, payment,
shipment, risk score, trace count, satisfied policy count, and insight tags.

## Run ArchSig

```bash
tools/archsig/examples/practical-rust-service/scripts/run_archsig_demo.sh
```

Or run the core analysis directly:

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- analyze \
  --archmap tools/archsig/examples/practical-rust-service/archmap/archmap.json \
  --law-policy tools/archsig/examples/practical-rust-service/law_policy/law_policy.json \
  --out-dir .tmp/archsig-practical-rust-service
```

The generated artifacts include:

- `.tmp/archsig-practical-rust-service/archsig-measurement-packet.json`
- `.tmp/archsig-practical-rust-service/archsig-analysis-summary.json`
- `.tmp/archsig-practical-rust-service/archsig-insight-report.json`
- `.tmp/archsig-practical-rust-service/archsig-insight-brief.md`
- `.tmp/archsig-practical-rust-service/archsig-atom-viewer-data.json`
- `.tmp/archsig-practical-rust-service/archsig-run-manifest.json`

## Viewer

Open ArchView:

```text
tools/archview/archview.html
```

Load:

```text
.tmp/archsig-practical-rust-service/archsig-atom-viewer-data.json
```

The viewer data is a projection of the supplied ArchMap, LawPolicy, and
measurement packet. It is not a new analyzer and does not infer facts outside
the selected evidence contract.

## Current Insight

For the bundled demo, `archsig analyze` reports:

```text
NO_MEASURED_H1_OBSTRUCTION_UNDER_PROFILE
```

This means the selected commerce fulfillment cover produced a profile-relative
positive reading: no selected H1 glue mismatch was measured under the supplied
MeasurementProfile. That mismatch vocabulary is not authored into ArchMap; it is
introduced by the selected LawPolicy evaluator. The useful engineering insight
is that the checkout service, ports, infrastructure adapter, policy catalog,
runtime trace, and shared interpretation overlap are visible in one bounded
viewer surface, while the summary preserves the measurement boundary and
assumption ledger.

The result is bounded to this `ArchMap + LawPolicy + evidence contract`. It is
not a Lean proof, not a source extraction completeness proof, and not a global
claim about all possible runtime behavior.
