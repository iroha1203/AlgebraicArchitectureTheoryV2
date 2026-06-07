# Practical Rust Service Example

This example is a small source universe for practical ArchSig validation. The
sample application is intentionally ordinary Rust code: a domain model, an
application service, and an in-memory infrastructure adapter.

The first use of this directory is source-grounded ArchMap v1 authoring. The
Rust sample gives an agent concrete source refs for atoms and explicit molecule
membership. ArchSig analysis artifacts should be generated under the repository
`.tmp/` directory rather than inside this example tree.

## Layout

```text
sample/
  Cargo.toml
  src/
    domain.rs  # domain invariants and order / reservation objects
    app.rs     # OrderService and InventoryStore port
    store.rs   # InMemoryInventoryStore adapter
    main.rs    # executable smoke flow
archmap/
  source_inventory.json
  archmap.json
law_policy/
  law_policy.json
runtime/
  place_order_trace.json
  concurrent_reservation_trace.json
production/
  inventory-store.toml
```

## Run

```bash
cargo test --manifest-path tools/archsig/examples/practical-rust-service/sample/Cargo.toml
cargo run --manifest-path tools/archsig/examples/practical-rust-service/sample/Cargo.toml
```

Expected smoke output includes a reserved order and remaining stock snapshot.

## Validate ArchMap And LawPolicy

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- archmap \
  --input tools/archsig/examples/practical-rust-service/archmap/archmap.json \
  --out .tmp/archsig-practical-rust-service/archmap-validation.json

cargo run --manifest-path tools/archsig/Cargo.toml -- law-policy \
  --input tools/archsig/examples/practical-rust-service/law_policy/law_policy.json \
  --out .tmp/archsig-practical-rust-service/law-policy-validation.json
```

## Analyze

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- analyze \
  --archmap tools/archsig/examples/practical-rust-service/archmap/archmap.json \
  --law-policy tools/archsig/examples/practical-rust-service/law_policy/law_policy.json \
  --out-dir .tmp/archsig-practical-rust-service \
  --emit-raw-artifacts \
  --strict-distance
```

The output is the v1 typed evaluator and architecture distance artifact chain:
`normalized-archmap.json`, `typed-evaluator-results.json`,
`architecture-distance.json`, `archsig-analysis-summary.json`,
`archsig-atom-viewer-data.json`, and `archsig-run-manifest.json` by default,
plus raw packet / detail / LLM artifacts with `--emit-raw-artifacts`. The public
summary, viewer data, and LLM packet are conclusion-first and use architecture
distance naming. The artifacts are bounded to the example ArchMap and LawPolicy
and are not a Lean proof or architecture lawfulness certificate.

## ArchSig Reading Targets

- `domain.rs`: source-grounded domain atoms and invariant observations.
- `app.rs`: application orchestration, repository port, and contract boundary.
- `store.rs`: infrastructure adapter and mutable inventory state.
- `main.rs`: bounded executable scenario for smoke evidence.

The sample, ArchMap, and LawPolicy do not claim runtime completeness or
architecture lawfulness by themselves. ArchSig can read bounded diagnostic
conclusions only inside this `ArchMap + LawPolicy + evidence contract`.
