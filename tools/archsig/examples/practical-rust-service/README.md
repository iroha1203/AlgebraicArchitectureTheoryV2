# The One-Cent Drift — a practical ArchSig demo, measured as a SAGA

A pull request lands in a realistic Rust commerce service. Every unit test is
green in every build configuration. Every hunk of the diff is locally
justified, reviewed, and defensible. And the PR makes the customer's card get
charged one cent more than the checkout page displayed.

This example shows ArchSig doing the one thing local review cannot:
**measuring that a set of individually correct modules no longer glues into a
consistent whole** — and it now walks the full SAGA diagnostic staircase from
v0.5.2/v0.5.4 to do it. The checkout → payment → settlement flow *is* a saga,
and the staircase names each step of its failure precisely:

1. **Grounding** — every module satisfies its own displayed money law
   (`DISPLAYED_LAWS_HOLD_ON_SELECTED_CHARTS`). The fixed chart-local observation check is clean.
2. **Descent** — the residual derived from the observed sections under the
   selected descent law contract has a **nonzero** boundary-membership result
   on the ArchMap-derived 1-skeleton (`MEASURED_NONGLUING_RESIDUAL`). A named
   `Z1/B1` class is emitted only when a derived triple face is actually checked.
3. **Comparison** — `compare` derives the difference of the head and repaired
   residuals and tests its membership in `B1`
   (`residualDifferenceReading`; here `difference_not_in_B1`).
4. **Gate** — CI blocks the PR; after the repair, the residual glues
   (`REPAIR_GLUES_WITHIN_SELECTED_COMPLEX`) and the gate passes.

On the side, a cost-model-supplied **harmonic debt** reading prices the
repair: the drift has an essential component that no free local adjustment
removes, and its lower bound is exactly the quarter-cent rounding residue.

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
  The SAGA grounding stage measures this directly: the per-chart
  The derived holds-criterion raw check comes back clean on every chart.
- The port signature never changes; there is no type error and nothing for a
  linter to see.
- Each diff hunk is individually reasonable, so a file-by-file human or LLM
  review approves it. The defect is not in any hunk: it is in the **loop**
  checkout → payment → settlement → shared events → checkout, which no
  single diff view contains.
- With only **two** conventions, some single module could always be adapted
  at its boundary. With **three conventions on a cycle**, no assignment of
  per-module fixes reconciles the loop — the disagreement is essentially
  global. The descent stage states this as mathematics: the reconciliation
  residual carries odd drift parity around the money loop, so it is a
  1-cocycle that is not a coboundary, and its class in `Z1/B1` is nonzero.

## The SAGA staircase: observation and law unlock vocabulary

ArchSig only speaks a diagnostic vocabulary carried by the two input families:
observation (ArchMap) and law / equations (LawPolicy, law surface,
MeasurementProfile). The SAGA finite complex is derived from the selected
ArchMap cover and observed restriction relations:

| Input | Where in this demo | Vocabulary it unlocks |
| --- | --- | --- |
| Observation (atoms / contexts / covers) | `archmap/archmap*.json` | raw section values, Čech H¹, **derived residual** |
| Selected finite complex | selected ArchMap cover and restrictions | residual boundary membership on the derived 1-skeleton |
| Triple faces | shared observed atoms across three selected contexts | residual class in `Z1/B1` when the derived face parity is checked |
| Run pair of measurement records | two `analyze` out-dirs | `residualDifferenceReading` (with its `δ⁰` witness when the difference is in `B1`) derived by `compare` |
| Grounded law/equation declarations | `law_policy/law_surface*.json` | law-grounded defect quotient; ArchSig derives chart and observation rows from the selected ArchMap cover |
| Cost model (`analytic.costModel`) | `law_policy/measurement_profile_drift.json` | `essentialRepairLowerBound` |

The base, head, and repaired acts use the same two input families. Their
different SAGA readings come from the source-grounded observations and the
ArchMap-derived finite complex.

## Run the demo

```bash
tools/archsig/examples/practical-rust-service/scripts/run_archsig_demo.sh
```

The script walks five acts and prints one conclusion per step:

```text
[analyze base]           REPAIR_GLUES_WITHIN_SELECTED_COMPLEX
[saga base]              measured_zero         (derived residual in B1)
[grounding head]         measured_zero         (every chart's own law holds)
[descent head]           measured_nonzero      (residual outside B1)
[harmonic debt head]     0.353553              (quarter-cent essential debt)
[analyze head]           MEASURED_NONGLUING_RESIDUAL
[compare base->head]     RUNS_NOT_COMPARABLE_WITHOUT_COMPARISON_DATA
[gate head]              BLOCKED_BY_GATE_POLICY
[descent repaired]       measured_zero         (residual glues)
[harmonic debt repaired] 0.0                   (residue booked explicitly)
[analyze repaired]       REPAIR_GLUES_WITHIN_SELECTED_COMPLEX
[compare head->repaired] MEASURED_OBSTRUCTION_NO_LONGER_RECORDED_AFTER_CHANGE
[residual difference reading head->repaired] difference_not_in_B1  (repair success is the repaired run's own zero residual)
[gate repaired]          PASS_WITHIN_GATE_POLICY
```

Notes on the two comparisons:

- base→head is reported **not comparable at row level** because the PR adds a
  new context (`ctx:settlement`), changing the site itself. ArchSig refuses
  to claim class transport across different sites; it juxtaposes the
  independent conclusions instead, and the gate blocks on the absolute rule
  `measured_nonzero → block`.
- head→repaired keeps the same site, so the comparison is row-comparable and
  records that the measured obstruction is no longer recorded after the
  change; the gate passes.

## The three states

The sample crate reproduces all three states of the story with Cargo
features; each state has a matching ArchMap observation:

| State | Build | ArchMap | analyze conclusion |
| --- | --- | --- | --- |
| base (main) | `cargo run` | `archmap/archmap.json` | `REPAIR_GLUES_WITHIN_SELECTED_COMPLEX` |
| head (PR under review) | `cargo run --features psp-compliance` | `archmap/archmap_head.json` | `MEASURED_NONGLUING_RESIDUAL` |
| repaired | `cargo run --features settlement-authority` | `archmap/archmap_repaired.json` | `REPAIR_GLUES_WITHIN_SELECTED_COMPLEX` |

All three build states pass `cargo test` — that is the point of the demo.

Every context in the ArchMap declares the money convention its code actually
implements as a Čech section value (`axis: "cech"`, `predicate:
"sectionValue"`), grounded in the source symbols that carry the convention
(`Order::pricing`, `InMemoryCommercePlatform::capture_amount`,
`SettlementLedger`). The base conclusion is therefore a non-vacuous zero:
conventions were observed everywhere and they glue.

## How each stage is grounded

**Grounding.** The head/repaired law surface declares the money-convention
law over the four overlap edges of the money loop. ArchSig derives the
selected chart set, section support, and per-chart square-free law-defect
observation from the selected ArchMap cover and its validated atoms. The
observation contains no defect atom for any chart — module test suites are
green — so the fixed empty-witness-set check passes chart by chart and the grounded packet fires
`DISPLAYED_LAWS_HOLD_ON_SELECTED_CHARTS`. That is the precise sense in which
"every module is right and the whole is wrong."

**Descent.** ArchSig derives the finite repair complex from the selected
ArchMap cover and observed restriction relations over the eight contexts: the money loop
`ctx:application – ctx:settlement – ctx:infrastructure – ctx:ports`, and
the policy/runtime edges. The residual is **derived, not supplied**: ArchSig
compares the observed `cech/sectionValue` atoms across each overlap of the
loop and finds three mismatching convention boundaries; the derivation record
(`saga-descent:residual-derivation`) names the observed support atoms.
Odd parity around a closed loop is not a coboundary: boundary membership
fails. This run's ArchMap does not provide a shared observed face for a checked
triple, so the class vocabulary remains withheld as a named boundary statement.

**Comparison.** `compare` reads the two measurement records (head and
repaired) and derives the run-pair reading itself: the residual delta on the
shared overlap complex and, when the pair is comparable and the delta is in
`B1`, its C⁰ witness (`residualDifferenceReading`). Here the delta is
`difference_not_in_B1`; the repair reading is carried by the repaired run's
zero residual and the gate.

**Harmonic debt.** A second measurement profile
(`measurement_profile_drift.json`, coefficient `R`, selected by the
`ag.harmonic-debt` policy row via `profileRef`) reads the reconciliation
cells observed in the runtime context: the deviation of the displayed total
and the PSP capture from the exact book of record, in cents. In the head
state those cells hold `-0.25` and `+0.75`: the disagreement between the two
cells is coexact (a local transfer can fix it — and the repair does exactly
that), but the common quarter-cent deviation is **harmonic** — no rounding
scheme removes it. Under the declared inner product and Lipschitz cost model
the essential repair lower bound is `0.353553` (= 0.25·√2). The repaired
state books that residue explicitly as its own ledger line, so the
unexplained deviation — and the bound — drop to `0.0`.

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

In the ArchMap this is one shared section value on every context. The derived
residual support is empty on every overlap. The residual lies in `B1`, global coherence is
`measured_zero`, and the summary upgrades from "no obstruction" to the
stronger SAGA reading: the derived finite complex **glues** within the selected
cover.

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
  archmap.json           # base observation (+ drift cells at rest)
  archmap_head.json      # head observation (three conventions, drift witness, drift cells)
  archmap_repaired.json  # repaired observation (one authoritative convention)
law_policy/
  law_policy.json               # cech-obstruction + saga-grounded + saga-descent + harmonic-debt
  law_surface.json              # head/repaired surface: money law and equation declarations
  law_surface_base.json         # base surface (no settlement edges), same SAGA declarations
  measurement_profile.json      # F2, cover:commerce-fulfillment
  measurement_profile_drift.json# R, analytic inner product + Lipschitz cost model
  gate_policy.json              # CI mapping: measured_nonzero -> block
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
  --measurement-profile tools/archsig/examples/practical-rust-service/law_policy/measurement_profile_drift.json \
  --law-surface tools/archsig/examples/practical-rust-service/law_policy/law_surface.json \
  --out-dir "$OUT/head"
```

## Viewer

Open `tools/archview/archview.html` and load
`$OUT/head/archsig-atom-viewer-data.json` (the demo prints the concrete `$OUT` directory).
Besides the eight contexts and the settlement cycle, the v0.5.4 SAGA view
renders the diagnostic staircase itself (`sagaDescent.stages`): grounding
(measured_zero), descent measurement with the residual boundary membership and
the harmonic-debt reading, the comparison transfer contract, and the silence
stage. The named residual-class vocabulary appears only when a derived triple
face has been checked. Load the base run's viewer data to see the same
staircase in full typed silence. The viewer data is a projection of the supplied ArchMap,
LawPolicy, and measurement packet; it is not a new analyzer.

## Boundary

Every conclusion above is relative to the two input families: observation
(`archmap/v0.5.4`) and law / equations (`law-policy` + `law-equation-surface`
+ `measurement-profile`). ArchSig derives the finite SAGA complex from the
selected ArchMap cover and observed restrictions. Enumeration completeness and
the law-surface quotient
sheaf condition are recorded in the packet's assumption ledger as
assumptions, not theorems. ArchSig does not extract conventions from Rust source by itself,
does not claim the sample has no other defects, and does not prove
production correctness. The harmonic-debt bound is relative to the declared
inner product and cost model. The head/base comparison deliberately refuses
row-level comparability across different sites rather than inventing class
transport. None of this is a Lean proof; it is a bounded measurement that
makes a specific global inconsistency visible, priceable, and reviewable.
