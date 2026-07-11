#!/usr/bin/env bash
set -euo pipefail

[ "$#" -ge 1 ] || { echo "usage: $0 DECLARATIONS_JSONL..." >&2; exit 2; }

python3 - "$@" <<'PY'
import json
import pathlib
import re
import sys

keys = set()
count = 0
old_prefix = "Formal.AG." + "Research"
pattern = re.compile(r"R[34]/[A-Za-z0-9_./'-]+\.lean#[A-Za-z0-9_.$'?!]+")
for filename in sys.argv[1:]:
    for number, raw in enumerate(pathlib.Path(filename).read_text().splitlines(), 1):
        try:
            row = json.loads(raw)
        except json.JSONDecodeError:
            print(f"E_MIGRATION_RECORD_JSON: {filename}:{number}", file=sys.stderr); raise SystemExit(1)
        key = row.get("migration_record", "")
        if not pattern.fullmatch(key) or old_prefix in key or "ResearchLean.AG" in key or "$RESEARCH" in key:
            print(f"E_MIGRATION_RECORD_FORMAT: {filename}:{number}", file=sys.stderr); raise SystemExit(1)
        if key in keys:
            print(f"E_MIGRATION_RECORD_DUPLICATE: {key}", file=sys.stderr); raise SystemExit(1)
        keys.add(key)
        if not isinstance(row.get("canonicalDeclaration"), str) or not row["canonicalDeclaration"]:
            print(f"E_MIGRATION_DECLARATION_MISSING: {key}", file=sys.stderr); raise SystemExit(1)
        for field in ("sourceDigest", "levelDigest", "typeDigest", "valueDigest", "axiomSetDigest"):
            if not isinstance(row.get(field), str) or not row[field]:
                print(f"E_MIGRATION_DIGEST_MISSING: {key}:{field}", file=sys.stderr); raise SystemExit(1)
        count += 1
if count == 0:
    print("E_MIGRATION_RECORD_EMPTY", file=sys.stderr); raise SystemExit(1)
print(f"Migration record catalog passed ({count} globally unique records).")
PY
