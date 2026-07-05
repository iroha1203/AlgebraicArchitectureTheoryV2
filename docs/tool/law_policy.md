# LawPolicy

LawPolicy is the selected evaluator contract for the current ArchSig
measurement workflow. It is intentionally separate from ArchMap evidence.

Current ArchSig `analyze` reads:

```text
ArchMap finite-poset-site evidence
  + LawPolicy evaluator selection
  + MeasurementProfile selected regime
  -> archsig-measurement-packet/v0.5.0
```

LawPolicy JSON selects evaluator ids, basis refs, scope, severity, and the
measurement profile used by the AG measurement path. It does not embed witness
rules, distance profiles, operation costs, coverage DSLs, repair recipes, or
Lean proof assumptions. Those calculation rules belong to ArchSig evaluator
registry code and MeasurementProfile.

The current handoff to FieldSig is the serialized measurement packet. FieldSig
does not accept old raw analysis packets as the current boundary.

Historical LawPolicy and packet forms are archived under
`docs/archive/2026-07-05-archsig-v1-retirement/`.
