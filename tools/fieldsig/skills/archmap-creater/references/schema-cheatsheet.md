# ArchMap v0.5.0 Schema Cheatsheet

Use this reference when authoring the current ArchMap artifact. The accepted
document is deliberately small and source-grounded.

## Top-level shape

    {
      "schema": "archmap/v0.5.0",
      "id": "archmap:example",
      "extractionDoctrineRef": {
        "doctrineId": "doctrine:aat-canonical@1",
        "fingerprint": "sha256:aat-canonical-doctrine-schema050",
        "components": ["V", "Gamma", "R", "rho", "E", "N"]
      },
      "sources": {},
      "atoms": [],
      "contexts": [],
      "covers": []
    }

sources is a map from source key to a source descriptor. A descriptor has a
non-empty kind and may carry path, source, symbol, line, section, or traceId.

## Atoms

Each atoms[] entry has id, kind, subject, and axis, plus optional predicate,
object, refs, and label. refs[] names keys in the top-level sources map.
Keep the atom predicate source-grounded; it is not a law verdict or an
obstruction circuit.

## Contexts and covers

Each contexts[] entry has id and optional atoms, restrictsTo, refs, and label.
Each atom and context reference must resolve within the same document.

Each covers[] entry has id and optional contexts, refs, and label. Cover
contexts must resolve to contexts[].id. The finite-poset-site validation checks
restriction acyclicity and selected cover shape.

## Boundary discipline

Do not add observation, molecule, semantic, gap, projection, concern, score,
lawfulness, or forecast fields to ArchMap. Missing or private evidence belongs
in the source inventory and review notes, not in invented positive atoms.
ArchMap is evidence input; ArchSig computes law-relative readings after
combining it with LawPolicy and MeasurementProfile.

## Validation

Run the current command with all required inputs:

    ${ARCHSIG_BIN:-archsig} archmap \
      --input <archmap.json> \
      --out .archsig/archmap/validation.json

    ${ARCHSIG_BIN:-archsig} law-policy \
      --law-policy <law-policy.json> \
      --measurement-profile <measurement-profile.json> \
      --out .archsig/law-policy/validation.json

Read checks, summary, and nonConclusions before handing the artifact to
analyze. Failures are schema or evidence-boundary problems; they are not
measured zeros and do not constitute Lean proofs.
