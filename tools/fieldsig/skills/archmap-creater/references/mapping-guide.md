# ArchMap v0.5.0 Mapping Guide

Map source evidence into the current finite-poset-site artifact:

| Evidence | Current fields | Rule |
| --- | --- | --- |
| File, module, service, package, or document section | sources + atoms | Add a source descriptor, then an atom with subject, kind, axis, and refs. |
| Static import or explicit dependency | atoms + contexts | Record the observed relation as an atom and place it in the relevant contexts. |
| Test, contract, policy, or acceptance evidence | sources + atoms | Preserve the source key and the narrow observed subject; do not turn it into a law verdict. |
| Workflow or lifecycle fact | atoms + contexts | Record only the supplied observation and its source refs. |
| Runtime trace or generated artifact | sources + atoms | Use the source descriptor kind and traceId/path; do not infer unavailable runtime behavior. |
| Selected finite cover | covers + contexts | List only context ids that resolve in the same document. |

The accepted ArchMap document has sources, atoms, contexts, covers, and the
fixed extractionDoctrineRef. It does not have observation, molecule, semantic,
gap, projection, concern, score, lawfulness, or forecast fields.

Keep atom ids, context ids, cover ids, and source keys unique. Use refs to
connect an atom, context, or cover to the top-level sources map. Validation
checks reference resolution, finite-poset-site shape, and the declared AAT
extraction doctrine.

ArchMap is evidence input. ArchSig and LawPolicy compute structural readings
after validation; this guide does not authorize lawfulness, obstruction,
causality, forecast, or Lean-proof claims.
