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
   (`DISPLAYED_LAWS_HOLD_ON_SELECTED_CHARTS`). The defect is not in any chart.
2. **Descent** — the supplied repair primitives leave a residual whose class
   in `Z1/B1` is **nonzero**: no assignment of per-module fixes reconciles
   the loop (`MEASURED_NONGLUING_RESIDUAL_CLASS`).
3. **Comparison** — a supplied, contract-checked cochain map transports the
   class to the Čech side (`SAGA_COMPARISON_ESTABLISHED_UNDER_SUPPLIED_DATA`).
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
  `holdsCriterion` raw check comes back clean on every chart.
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

## The SAGA staircase: supplied data unlocks vocabulary

ArchSig only speaks a diagnostic vocabulary after the artifact that grounds
it has been supplied and validated. The demo supplies every slot of the
staircase for head and repaired, and deliberately supplies none of them for
base — so the base run shows what typed silence looks like:

| Supplied artifact | Where in this demo | Vocabulary it unlocks |
| --- | --- | --- |
| Observation (atoms / contexts / covers) | `archmap/archmap*.json` | raw section values, Čech H¹ |
| Repair primitives (`complex` + `primitives`) | `saga/repair_plan_*.json` | residual boundary membership |
| Faithfulness data (`faithfulness.supplied`) | same RepairPlan | global coherence |
| Triple + F₂ coefficient + true-sheaf certificate + gluing data | same RepairPlan | **residual class in `Z1/B1`** |
| Comparison data (incidence bridge + checked cochain map) | same RepairPlan | class transport to the Čech side |
| Grounded law surface (`skeleton` / `defectSources` / `holdsCriterion`) | `law_policy/law_surface*.json` | law-grounded conclusions, per-chart law defect detector |
| Cost model (`analytic.costModel`) | `law_policy/measurement_profile_drift.json` | `essentialRepairLowerBound` |

Without a RepairPlan (the base act), the same LawPolicy rows produce
`not_computed` verdicts with `silence_by_design` boundary statements — not
failures, and not permission to speak.

## Run the demo

```bash
tools/archsig/examples/practical-rust-service/scripts/run_archsig_demo.sh
```

The script walks five acts and prints one conclusion per step:

```text
[analyze base]           NO_MEASURED_H1_OBSTRUCTION_UNDER_PROFILE
[saga base]              not_computed          (typed silence: no RepairPlan)
[grounding head]         measured_zero         (every chart's own law holds)
[descent head]           measured_nonzero      (residual class in Z1/B1)
[comparison head]        established           (checked cochain-map transport)
[harmonic debt head]     0.353553              (quarter-cent essential debt)
[analyze head]           MEASURED_NONGLUING_RESIDUAL_CLASS
[compare base->head]     RUNS_NOT_COMPARABLE_WITHOUT_COMPARISON_DATA
[gate head]              BLOCKED_BY_GATE_POLICY
[descent repaired]       measured_zero         (residual glues)
[harmonic debt repaired] 0.0                   (residue booked explicitly)
[analyze repaired]       REPAIR_GLUES_WITHIN_SELECTED_COMPLEX
[compare head->repaired] MEASURED_OBSTRUCTION_NO_LONGER_RECORDED_AFTER_CHANGE
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
| base (main) | `cargo run` | `archmap/archmap.json` | `NO_MEASURED_H1_OBSTRUCTION_UNDER_PROFILE` |
| head (PR under review) | `cargo run --features psp-compliance` | `archmap/archmap_head.json` | `MEASURED_NONGLUING_RESIDUAL_CLASS` |
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
law over the four overlap edges of the money loop, a `skeleton` of the eight
per-context section atoms, and per-chart `defectSources` whose observable is
the square-free law-defect axis. The observation contains no defect atom for
any chart — module test suites are green — so the `holdsCriterion`
empty-witness-set check passes chart by chart and the grounded packet fires
`DISPLAYED_LAWS_HOLD_ON_SELECTED_CHARTS`. That is the precise sense in which
"every module is right and the whole is wrong."

**Descent.** `saga/repair_plan_head.json` supplies the finite repair complex
over the eight contexts: the money loop
`ctx:application – ctx:settlement – ctx:infrastructure – ctx:ports`, one
triangle (`application/domain/shared`) as the supplied triple overlap, and
the policy/runtime edges. The reconciliation residual assigns the observed
drift witness (`drift:one-cent`, an ArchMap atom recorded by the settlement
reconciliation) to the three convention boundaries of the loop. Odd parity
around a closed loop is not a coboundary: boundary membership fails, and —
because triple, coefficient, true-sheaf certificate, and gluing data are all
supplied and checked — ArchSig is allowed to say **class**, not just
"mismatch": `saga-descent:residual-class` is `measured_nonzero`.

**Comparison.** The RepairPlan supplies an explicit incidence bridge and a
degree-0/1/2 cochain map onto the Čech side of the same finite complex.
ArchSig recomputes both-sided invertibility, difference preservation, zero
preservation in degree 2, and differential commutativity from the supplied
finite tables — declared booleans are not accepted — then transports the
class at quotient level.

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

In the ArchMap this is one shared section value on every context; in the
RepairPlan (`saga/repair_plan_repaired.json`) the residual support is empty
on every overlap. The residual lies in `B1`, global coherence is
`measured_zero`, and the summary upgrades from "no obstruction" to the
stronger SAGA reading: the supplied repair **glues** within the selected
complex.

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
  archmap.json           # base observation (+ drift cells at rest)
  archmap_head.json      # head observation (three conventions, drift witness, drift cells)
  archmap_repaired.json  # repaired observation (one authoritative convention)
law_policy/
  law_policy.json               # cech-obstruction + saga-grounded + saga-descent + harmonic-debt
  law_surface.json              # head/repaired surface: money law + skeleton/defectSources/holdsCriterion
  law_surface_base.json         # base surface (no settlement edges), same SAGA declarations
  measurement_profile.json      # F2, cover:commerce-fulfillment
  measurement_profile_drift.json# R, analytic inner product + Lipschitz cost model
  gate_policy.json              # CI mapping: measured_nonzero -> block
saga/
  repair_plan_head.json      # supplied complex, primitives, faithfulness, triple/coefficient,
                             # true-sheaf certificate, gluing data, comparison, grounding
  repair_plan_repaired.json  # same complex, empty residual support
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
  --repair-plan tools/archsig/examples/practical-rust-service/saga/repair_plan_head.json \
  --out-dir .tmp/archsig-practical-rust-service/head
```

## Viewer

Open `tools/archview/archview.html` and load
`.tmp/archsig-practical-rust-service/head/archsig-atom-viewer-data.json`.
Besides the eight contexts and the settlement cycle, the v0.5.4 SAGA view
renders the diagnostic staircase itself (`sagaDescent.stages`): grounding
(measured_zero), descent measurement with the residual class and the
harmonic-debt reading, the comparison transfer contract, and the silence
stage. Load the base run's viewer data to see the same staircase in full
typed silence. The viewer data is a projection of the supplied ArchMap,
LawPolicy, and measurement packet; it is not a new analyzer.

## Boundary

Every conclusion above is relative to this `ArchMap + LawPolicy +
MeasurementProfile + RepairPlan` evidence contract: the selected cover, the
F₂ coefficient, the declared section values, and the author-supplied repair
complex. Enumeration completeness of the repair complex, the global sheaf
condition behind the true-sheaf certificate, and the supplied faithfulness
law are recorded in the packet's assumption ledger as assumptions, not
theorems. ArchSig does not extract conventions from Rust source by itself,
does not claim the sample has no other defects, and does not prove
production correctness. The harmonic-debt bound is relative to the declared
inner product and cost model. The head/base comparison deliberately refuses
row-level comparability across different sites rather than inventing class
transport. None of this is a Lean proof; it is a bounded measurement that
makes a specific global inconsistency visible, priceable, and reviewable.
