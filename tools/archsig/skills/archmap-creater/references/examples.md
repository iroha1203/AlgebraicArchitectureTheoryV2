# ArchMap v2 Examples

## Minimal

```json
{
  "schema": "archmap/v2",
  "id": "example-service",
  "extractionDoctrineRef": {
    "doctrineId": "doctrine:example-service@1",
    "fingerprint": "sha256:example-service-doctrine",
    "components": ["V", "Gamma", "R", "rho", "E", "N"]
  },
  "sources": {
    "src.order": { "kind": "file", "path": "src/order.rs" },
    "src.inventory": { "kind": "file", "path": "src/inventory.rs" },
    "src.cover": { "kind": "policy", "path": "docs/architecture.md", "section": "order-inventory cover" },
    "src.order.place_order": {
      "kind": "symbol",
      "source": "src.order",
      "symbol": "place_order",
      "line": 12
    },
    "domain.OrderService": {
      "kind": "symbol",
      "source": "src.order",
      "symbol": "OrderService"
    },
    "domain.InventoryService": {
      "kind": "symbol",
      "source": "src.order",
      "symbol": "InventoryService"
    }
  },
  "atoms": [
    {
      "id": "atom:place-order-capability",
      "kind": "capability",
      "subject": "domain.OrderService",
      "axis": "static",
      "predicate": "placesOrder",
      "refs": ["src.order.place_order"],
      "label": "OrderService places an order"
    },
    {
      "id": "atom:inventory-check",
      "kind": "relation",
      "subject": "domain.OrderService",
      "axis": "restriction",
      "predicate": "checksInventoryWith",
      "object": "domain.InventoryService",
      "refs": ["src.order.place_order"],
      "label": "OrderService checks inventory through InventoryService"
    }
  ],
  "contexts": [
    {
      "id": "ctx:order",
      "atoms": ["atom:place-order-capability", "atom:inventory-check"],
      "restrictsTo": ["ctx:shared"],
      "refs": ["src.order.place_order"],
      "label": "order context"
    },
    {
      "id": "ctx:shared",
      "atoms": ["atom:inventory-check"],
      "refs": ["src.cover"],
      "label": "shared order/inventory boundary"
    }
  ],
  "covers": [
    {
      "id": "cover:order-inventory",
      "contexts": ["ctx:order", "ctx:shared"],
      "refs": ["src.cover"],
      "label": "order/inventory cover"
    }
  ]
}
```

## Bad: Removed v0 Field

```json
{
  "schema": "archmap/v2",
  "id": "bad-map",
  "extractionDoctrineRef": {
    "doctrineId": "doctrine:bad@1",
    "fingerprint": "sha256:bad",
    "components": ["V", "Gamma", "R", "rho", "E", "N"]
  },
  "sources": {},
  "atoms": [],
  "contexts": [],
  "covers": [],
  "semanticObservations": []
}
```

Why bad: v2 does not accept removed v0 helper fields. Write a primitive
`semantic` atom if a source-supported meaning is needed.

## Bad: Label-Only Atom

```json
{
  "id": "atom:meaning",
  "kind": "semantic",
  "subject": "src.order.place_order",
  "axis": "static",
  "refs": ["src.order.place_order"],
  "label": "This workflow is safe and follows SOLID"
}
```

Why bad: even if the JSON shape is structurally close, the only content is a
law-relative prose label. Use `predicate` for a controlled semantic token and
leave lawfulness to ArchSig.

## Bad: Coarse Minimal Observation

```json
{
  "id": "atom:order-service",
  "kind": "component",
  "subject": "domain.OrderService",
  "axis": "static",
  "predicate": "component",
  "refs": ["src.order"]
}
```

Why bad when used alone: if `src.order` also shows commands, state mutations,
authority checks, contracts, or domain meanings, this atom is only one primitive
observation. A final ArchMap that stops here is too coarse.

## Good: Semantic From Use

```json
{
  "id": "atom:reservation-hold-meaning",
  "kind": "semantic",
  "subject": "domain.ReservationStatus.Held",
  "axis": "static",
  "predicate": "preventsDoubleAllocation",
  "refs": ["src.inventory.reserve", "test.inventory_prevents_double_allocation"],
  "label": "Held reservations are treated as unavailable inventory in reserve and allocation tests"
}
```

Why good: the meaning is not a dictionary gloss. It is grounded in how the
status is used by code and tests.

## Bad: Diagnostic Shortcut Atom

```json
{
  "id": "atom:payment_inventory_mismatch",
  "kind": "relation",
  "subject": "ctx:payment",
  "object": "ctx:inventory",
  "axis": "cech",
  "predicate": "mismatch",
  "refs": ["src.payment", "src.inventory"]
}
```

Why bad unless doctrine-approved: it names a diagnostic conclusion instead of a
neutral observed relation. Prefer source-grounded relation / contract / state
atoms and let the AG evaluator derive mismatch / obstruction readings.

## Bad: Molecules In v2

```json
{
  "schema": "archmap/v2",
  "id": "bad-map",
  "extractionDoctrineRef": {
    "doctrineId": "doctrine:bad@1",
    "fingerprint": "sha256:bad",
    "components": ["V", "Gamma", "R", "rho", "E", "N"]
  },
  "sources": {},
  "atoms": [],
  "molecules": []
}
```

Why bad: AG measurement v2 primary input uses `contexts` and `covers`; v1
`molecules` are not a primary v2 field.
