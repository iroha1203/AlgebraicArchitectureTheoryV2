# ArchMap v1 Examples

## Minimal

```json
{
  "schema": "archmap/v1",
  "id": "example-service",
  "sources": {
    "src.order": { "kind": "file", "path": "src/order.rs" },
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
      "predicate": "placesOrder",
      "refs": ["src.order.place_order"],
      "label": "OrderService places an order"
    },
    {
      "id": "atom:inventory-check",
      "kind": "relation",
      "subject": "domain.OrderService",
      "predicate": "checksInventoryWith",
      "object": "domain.InventoryService",
      "refs": ["src.order.place_order"],
      "label": "OrderService checks inventory through InventoryService"
    }
  ],
  "molecules": [
    {
      "id": "mol:place-order-flow",
      "atoms": ["atom:place-order-capability", "atom:inventory-check"],
      "refs": ["src.order.place_order"],
      "label": "place_order local flow"
    }
  ]
}
```

## Bad: Removed v0 Field

```json
{
  "schema": "archmap/v1",
  "id": "bad-map",
  "sources": {},
  "atoms": [],
  "molecules": [],
  "semanticObservations": []
}
```

Why bad: v1 does not accept removed v0 helper fields. Write a primitive
`semantic` atom if a source-supported meaning is needed.

## Bad: Label-Only Atom

```json
{
  "id": "atom:meaning",
  "kind": "semantic",
  "diagram": "src.order.place_order",
  "refs": ["src.order.place_order"],
  "label": "This workflow is safe and follows SOLID"
}
```

Why bad: the machine-readable constructor-specific payload is missing, and the
label makes a law-relative claim. Use `meaning` for a controlled semantic
predicate token and leave lawfulness to ArchSig.
