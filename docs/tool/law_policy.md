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

LawPolicy JSON selects evaluator ids, basis refs, scope, severity, and a
`measurementProfileRef`. The selected profile is supplied as a separate
`measurement-profile/v0.5.0` artifact through `--measurement-profile`; LawPolicy
does not embed `measurementProfiles[]`.

`basisLedger[]` declares the basis ids used by `policies[].basis`. ArchSig checks
that policy basis refs resolve inside the ledger, but it does not check that
ledger paths exist. `lawSurfaceRef` and `policies[].profileRef` are reserved
for later law-surface / multi-profile stages and fail closed when present.

MeasurementProfile owns the selected cover, coefficient, witness family,
predicates, certificate selector, verdict discipline, and `finiteBounds`.
`finiteBounds` may lower ArchSig registry hard caps; cap exceedance is a
validation failure. LawPolicy does not embed witness rules, distance profiles,
operation costs, coverage DSLs, repair recipes, or Lean proof assumptions.
Those calculation rules belong to ArchSig evaluator registry code and the
external MeasurementProfile.

The current handoff to FieldSig is the serialized measurement packet. FieldSig
does not accept old raw analysis packets as the current boundary.

Historical LawPolicy and packet forms are archived under
`docs/archive/2026-07-05-archsig-v1-retirement/`.
