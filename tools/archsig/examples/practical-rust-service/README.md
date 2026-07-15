# The One-Cent Drift — a practical ArchSig demo

A pull request lands in a realistic Rust commerce service. Every unit test is
green in every build configuration. Every hunk of the diff is locally
justified, reviewed, and defensible. And the PR makes the customer's card get
charged one cent more than the checkout page displayed.

This example shows ArchSig doing the one thing local review cannot:
**measuring that a set of individually correct modules no longer glues into a
consistent whole**, blocking the PR in CI with a concrete, source-grounded
mismatch support — and passing the repaired version.

## The story

The service is a 3,000+ line commerce fulfillment application (`sample/`)
with layered architecture, ports and adapters, a policy engine, and an
executable checkout scenario. VIP customers get a loyalty discount of 250
basis points (2.5%).

Money amounts flow through three modules, and after the PR under review they
speak **three different conventions**:

| Module | Convention | Justification in review |
| --- | --- | --- |
| Checkout / domain (`domain.rs`) | discount rounded **half-up on the grand total** | marketing displays one total; existing behavior |
| Payment adapter (`store.rs`) | discount re-derived **per line, rounded half-to-even** | the PSP validates line items; its spec requires per-line allocation |
| Settlement ledger (`ledger.rs`, new) | **exact ten-thousandths of a cent, never rounds** | finance wants an exact book of record |

For the demo basket (subtotal 33,990 cents), the exact discount is 849.75
cents. The three conventions produce **850 / 849 / 849.75** — so the checkout
page displays $331.40, the PSP captures $331.41, and the monthly
reconciliation job cannot explain the difference:

```text
--- head (PR under review) ---
displayed total 33140 cents (33990 minus 850 loyalty discount)
payment pay-1 authorized for 33141 cents
settlement reconciliation for order-demo-100
display total 33140 cents / psp captured 33141 cents / exact 33140.2500 cents
RECONCILIATION MISMATCH: psp captured +1 cents against the displayed total
```

### Why conventional review misses it

- Every module's unit tests pass, because each module is **locally correct
  under its own convention** — that is exactly what its owner's spec says.
- The port signature never changes; there is no type error and nothing for a
  linter to see.
- Each diff hunk is individually reasonable, so a file-by-file human or LLM
  review approves it. The defect is not in any hunk: it is in the **loop**
  checkout → payment → settlement → shared events → checkout, which no
  single diff view contains.
- With only **two** conventions, some single module could always be adapted
  at its boundary. With **three conventions on a cycle**, no assignment of
  per-module fixes reconciles the loop — the disagreement is essentially
  global. That distinction (repairable locally vs. obstructed globally) is
  precisely what a Čech H¹ class over the selected cover measures, and it is
  invisible to pairwise interface checks.

ArchSig measures it directly: the money-convention section values declared in
the ArchMap fail to glue over the selected cover, the F2 Čech 1-cocycle is
not a coboundary, and the analysis names the exact overlap edges and section
atoms that carry the obstruction.

## Run the demo

```bash
tools/archsig/examples/practical-rust-service/scripts/run_archsig_demo.sh
```

The script walks four acts and prints one conclusion per step:

```text
[analyze base]           NO_MEASURED_H1_OBSTRUCTION_UNDER_PROFILE
[analyze head]           MEASURED_H1_OBSTRUCTION_UNDER_PROFILE
[compare base->head]     RUNS_NOT_COMPARABLE_WITHOUT_COMPARISON_DATA
[gate head]              BLOCKED_BY_GATE_POLICY
[analyze repaired]       NO_MEASURED_H1_OBSTRUCTION_UNDER_PROFILE
[compare head->repaired] MEASURED_OBSTRUCTION_NO_LONGER_RECORDED_AFTER_CHANGE
[gate repaired]          PASS_WITHIN_GATE_POLICY
```

Notes on the two comparisons:

- base→head is reported **not comparable at row level** because the PR adds a
  new context (`ctx:settlement`), changing the site itself. ArchSig refuses
  to claim class transport across different sites; it juxtaposes the
  independent conclusions (zero → nonzero) instead, and the gate blocks on
  the absolute rule `measured_nonzero → block`.
- head→repaired keeps the same site, so the comparison is row-comparable and
  records that the measured obstruction is no longer recorded after the
  change; the gate passes.

## The three states

The sample crate reproduces all three states of the story with Cargo
features; each state has a matching ArchMap observation:

| State | Build | ArchMap | analyze conclusion |
| --- | --- | --- | --- |
| base (main) | `cargo run` | `archmap/archmap.json` | `NO_MEASURED_H1_OBSTRUCTION_UNDER_PROFILE` |
| head (PR under review) | `cargo run --features psp-compliance` | `archmap/archmap_head.json` | `MEASURED_H1_OBSTRUCTION_UNDER_PROFILE` |
| repaired | `cargo run --features settlement-authority` | `archmap/archmap_repaired.json` | `NO_MEASURED_H1_OBSTRUCTION_UNDER_PROFILE` |

All three build states pass `cargo test` — that is the point of the demo.

Every context in the ArchMap declares the money convention its code actually
implements as a Čech section value (`axis: "cech"`, `predicate:
"sectionValue"`), grounded in the source symbols that carry the convention
(`Order::pricing`, `InMemoryCommercePlatform::capture_amount`,
`SettlementLedger`). The base conclusion is therefore a non-vacuous zero:
conventions were observed everywhere and they glue. In the head state the
cover's nerve contains the cycle `ctx:application` – `ctx:settlement` –
`ctx:infrastructure` – `ctx:ports`, with three distinct section values along
it; the resulting 1-cocycle has odd support on that cycle and cannot be a
coboundary.

Where to look in the head run output:

```text
.tmp/archsig-practical-rust-service/head/archsig-measurement-packet.json
  computedInvariants -> cech-cohomology -> classSupport.edgeRefs
    ctx:application->ctx:settlement
    ctx:infrastructure->ctx:ports
    ctx:infrastructure->ctx:settlement
    ...
  classSupport.supportAtomRefs
    atom:cech-money-application, atom:cech-money-infrastructure,
    atom:cech-money-settlement, ...
```

## The repair

The repaired PR (`--features settlement-authority`) does what payment systems
actually do: it designates **one money authority** (the checkout total),
keeps submitting PSP line items per the processor spec, and sends the
per-line rounding residue as an **explicit adjustment line**. The settlement
ledger books the exact value and records the rounding residual as its own
entry instead of silently disagreeing:

```text
display total 33140 cents / psp captured 33140 cents / exact 33140.2500 cents
reconciled: capture matches display; rounding residual +2500 tenk-cents booked explicitly
```

In the ArchMap this is one shared section value on every context — the
sections glue again, H¹ support is gone, and the gate passes.

## Layout

```text
sample/
  Cargo.toml        # features: psp-compliance (head), settlement-authority (repaired)
  src/
    domain.rs       # value objects, aggregates, Order::pricing (grand-total half-up)
    app.rs          # CheckoutService and port traits
    store.rs        # in-memory adapters; capture_amount carries the drift
    ledger.rs       # settlement ledger (head/repaired states only)
    policy.rs       # policy catalog and evaluator
    telemetry.rs    # trace and presentation surface
    scenario.rs     # executable demo scenario and reconciliation report
archmap/
  source_inventory.json
  archmap.json           # base observation
  archmap_head.json      # head observation (adds ctx:settlement, three conventions)
  archmap_repaired.json  # repaired observation (one authoritative convention)
law_policy/
  law_policy.json          # selects ag.cech-obstruction
  measurement_profile.json # F2, cover:commerce-fulfillment
  gate_policy.json         # CI mapping: measured_nonzero -> block
runtime/
  place_order_trace.json
  concurrent_reservation_trace.json
scripts/
  run_archsig_demo.sh
```

Individual commands, if you want to drive the acts by hand:

```bash
cargo test --manifest-path tools/archsig/examples/practical-rust-service/sample/Cargo.toml
cargo run --manifest-path tools/archsig/examples/practical-rust-service/sample/Cargo.toml --features psp-compliance

cargo run --manifest-path tools/archsig/Cargo.toml -- analyze \
  --archmap tools/archsig/examples/practical-rust-service/archmap/archmap_head.json \
  --law-policy tools/archsig/examples/practical-rust-service/law_policy/law_policy.json \
  --measurement-profile tools/archsig/examples/practical-rust-service/law_policy/measurement_profile.json \
  --law-surface tools/archsig/tests/fixtures/ag_measurement/law_surface_practical_v052.json \
  --out-dir .tmp/archsig-practical-rust-service/head
```

## Viewer

Open `tools/archview/archview.html` and load
`.tmp/archsig-practical-rust-service/head/archsig-atom-viewer-data.json` to
see the eight contexts, the settlement cycle, and the mismatch support in
3D. The viewer data (`archsig-atom-viewer-data/v0.5.3`) is a projection of
the supplied ArchMap, LawPolicy, and measurement packet; it is not a new
analyzer.

## Boundary

Every conclusion above is relative to this `ArchMap + LawPolicy +
MeasurementProfile` evidence contract: the selected cover, the F2
coefficient, and the declared section values. ArchSig does not extract
conventions from Rust source by itself, does not claim the sample has no
other defects, and does not prove production correctness. The head/base
comparison deliberately refuses row-level comparability across different
sites rather than inventing class transport. None of this is a Lean proof;
it is a bounded measurement that makes a specific global inconsistency
visible and reviewable.
