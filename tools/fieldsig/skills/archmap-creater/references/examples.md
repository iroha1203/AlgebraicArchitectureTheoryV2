# ArchMap v0.5.0 Examples

## Minimal source-grounded map

    {
      "schema": "archmap/v0.5.0",
      "id": "archmap:checkout",
      "extractionDoctrineRef": {
        "doctrineId": "doctrine:aat-canonical@1",
        "fingerprint": "sha256:aat-canonical-doctrine-schema050",
        "components": ["V", "Gamma", "R", "rho", "E", "N"]
      },
      "sources": {
        "source:checkout": {
          "kind": "file",
          "path": "src/checkout.rs",
          "symbol": "CheckoutService"
        }
      },
      "atoms": [{
        "id": "atom:checkout-service",
        "kind": "component",
        "subject": "CheckoutService",
        "axis": "semantic",
        "predicate": "service",
        "refs": ["source:checkout"]
      }],
      "contexts": [{
        "id": "context:checkout",
        "atoms": ["atom:checkout-service"],
        "refs": ["source:checkout"]
      }],
      "covers": [{
        "id": "cover:checkout",
        "contexts": ["context:checkout"],
        "refs": ["source:checkout"]
      }]
    }

## Example with a restriction

Use two contexts and record the restriction in the larger context:

    "contexts": [
      {
        "id": "context:order",
        "atoms": ["atom:order", "atom:payment"],
        "restrictsTo": ["context:payment"],
        "refs": ["source:order"]
      },
      {
        "id": "context:payment",
        "atoms": ["atom:payment"],
        "refs": ["source:payment"]
      }
    ]

The referenced ids must exist, and the restriction graph must remain acyclic.
Do not write a structural verdict, obstruction circuit, law selection, or
forecast conclusion into this artifact. ArchSig computes those readings from
the validated ArchMap and selected LawPolicy.

## Example validation workflow

1. Validate ArchMap with the archmap command.
2. Validate LawPolicy together with its MeasurementProfile.
3. Run analyze only after both input reports pass.
4. Read checks, summary, and nonConclusions before handoff.
