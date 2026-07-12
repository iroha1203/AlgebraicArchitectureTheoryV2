# Law-surface examples

These examples are small review fixtures for `law-equation-surface/v0.5.1`.
They are intentionally paired with the validator's fail-closed rules.

## Good: closed equation with an accepted binding

```json
{
  "lawId": "surface:checkout-v051",
  "conditionType": "closed-equational",
  "witnessVariables": [{
    "variable": "x_checkout",
    "binding": {"axis": "square-free", "predicate": "support"}
  }],
  "forbiddenSupportGenerators": [{"support": ["x_checkout"]}]
}
```

The binding pair is selected from
`references/aat-law-surface-binding-vocabulary.json`; the forbidden support is
supplied by the law surface and is not copied from an ArchMap support atom.

## Bad: judgment in an identifier

```json
{"lawId": "surface:bad-lawful-verdict", "conditionType": "closed-equational"}
```

Law ids and variable names must not carry verdict or decision words. The
validator rejects them explicitly.

## Bad: ideal data on a non-closed condition

```json
{
  "lawId": "surface:bad-open-law",
  "conditionType": "descent",
  "forbiddenSupportGenerators": [{"support": ["x"]}]
}
```

Only `closed-equational` laws may declare forbidden support generators. A
non-closed law selects its evaluator condition without silently becoming an
ideal.

## Bad: evaluator reference on a closed equation

```json
{
  "lawId": "surface:bad-evaluator-ref",
  "conditionType": "closed-equational",
  "evaluatorRef": "ag.square-free-repair"
}
```

The evaluator is selected by LawPolicy and the registry mapping. It is not
embedded in a closed law surface entry.
