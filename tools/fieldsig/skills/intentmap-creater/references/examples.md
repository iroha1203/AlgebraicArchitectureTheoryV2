# IntentMap Examples

## Minimal Item

```json
{
  "intentItemId": "intent:coupon-apply-operation",
  "intentKind": "operation",
  "sourceRefs": [
    {
      "sourceRefId": "source:prd:coupon",
      "sourceKind": "prd",
      "pathOrUrl": "docs/prd/coupon.md",
      "stableRef": "section:requirements",
      "evidenceRole": "intent-source"
    }
  ],
  "targetIntentRef": {
    "kind": "operation",
    "name": "checkout.applyCoupon"
  },
  "preserves": ["price invariant", "audit trail"],
  "forgets": ["exact file list", "runtime latency"],
  "claimClassification": "measured",
  "confidence": "high",
  "requiredAssumptions": [],
  "missingDecisions": [],
  "missingEvidence": ["runtime behavior not supplied"],
  "nonConclusions": [
    "This item is intent evidence, not an implementation plan."
  ]
}
```

## Ambiguity Item

Use an ambiguity item when the source text is materially unclear:

```json
{
  "intentItemId": "intent:coupon-ambiguity-stacking",
  "intentKind": "ambiguity",
  "targetIntentRef": {
    "kind": "decision",
    "name": "coupon stacking policy"
  },
  "preserves": [],
  "forgets": ["resolved business rule"],
  "claimClassification": "decision-needed",
  "confidence": "high",
  "missingDecisions": ["whether multiple coupons can be applied together"],
  "missingEvidence": [],
  "nonConclusions": [
    "IntentMap validation does not resolve product policy."
  ]
}
```
