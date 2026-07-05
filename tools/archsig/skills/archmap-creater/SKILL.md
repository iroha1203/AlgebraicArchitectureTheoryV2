---
name: archmap-creater
description: Create bounded archmap/v0.5.0 finite-poset-site artifacts from repository evidence.
---

# ArchMap Creater

Use this skill to create `archmap/v0.5.0` documents for current ArchSig
measurement.

## Workflow

1. Survey source files and collect source refs.
2. Emit source-grounded Atom observations.
3. Emit contexts, covers, extraction doctrine, and non-conclusions.
4. Validate with `archsig archmap --input <archmap> --out <report>`.
5. For a full run, use `archsig analyze --archmap <archmap> --law-policy <policy> --measurement-profile <profile> --out-dir <run-dir>`.

Do not output removed helper fields. Do not convert current contexts back into
older compatibility shapes.
