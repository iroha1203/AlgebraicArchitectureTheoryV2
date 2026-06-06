# Practical Rust Service Example

This example is a small source universe for practical ArchSig validation. The
sample application is intentionally ordinary Rust code: a domain model, an
application service, and an in-memory infrastructure adapter.

The first use of this directory is source-grounded ArchMap authoring. The Rust
sample gives an agent concrete source refs for component atoms, dependency
relations, operation contracts, and bounded concern hints. ArchSig analysis
artifacts are generated locally under `analysis/`. They are not checked in
because the current full audit surface is intentionally broader than this small
example.

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
  --out tools/archsig/examples/practical-rust-service/analysis/archmap-validation.json

cargo run --manifest-path tools/archsig/Cargo.toml -- law-policy \
  --input tools/archsig/examples/practical-rust-service/law_policy/law_policy.json \
  --out tools/archsig/examples/practical-rust-service/analysis/law-policy-validation.json
```

## Analysis Boundary

This example intentionally stops at ArchMap / LawPolicy authoring validation.
Current full `analyze` packet validation asks for broader Part IV and structural
surfaces than this small sample intends to claim. Generated `analysis/` output is
therefore local-only and ignored by git until the selected-policy report model is
separated from full audit guardrails.

## ArchSig Reading Targets

- `domain.rs`: source-grounded domain atoms and invariant observations.
- `app.rs`: application orchestration, repository port, and contract boundary.
- `store.rs`: infrastructure adapter and mutable inventory state.
- `main.rs`: bounded executable scenario for smoke evidence.

The sample, ArchMap, and LawPolicy do not claim runtime completeness or
architecture lawfulness by themselves. ArchSig can read bounded diagnostic
conclusions only inside this `ArchMap + LawPolicy + evidence contract`.
