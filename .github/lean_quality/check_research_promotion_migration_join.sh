#!/usr/bin/env bash
set -euo pipefail

[ "$#" -ge 2 ] || { echo "usage: $0 PROMOTION_MANIFEST DECLARATIONS_JSONL..." >&2; exit 2; }

python3 - "$@" <<'PY'
import csv, json, pathlib, sys

promotion = pathlib.Path(sys.argv[1])
records = {}
for filename in sys.argv[2:]:
    for raw in pathlib.Path(filename).read_text().splitlines():
        row = json.loads(raw)
        records.setdefault(row.get("migration_record", ""), []).append(row)

count = 0
with promotion.open(newline="") as stream:
    reader = csv.DictReader(stream, delimiter="\t")
    required = {"research_decl", "migration_record"}
    if not reader.fieldnames or not required.issubset(reader.fieldnames):
        print("E_PROMOTION_JOIN_SCHEMA", file=sys.stderr); raise SystemExit(1)
    for row in reader:
        key = row["migration_record"]
        matches = records.get(key, [])
        if len(matches) != 1:
            print(f"E_PROMOTION_MIGRATION_JOIN: {key}", file=sys.stderr); raise SystemExit(1)
        canonical = row["research_decl"].replace("ResearchLean.AG.", "$RESEARCH.", 1)
        if matches[0].get("canonicalDeclaration") != canonical:
            print(f"E_PROMOTION_DECLARATION_JOIN: {key}", file=sys.stderr); raise SystemExit(1)
        count += 1
if count == 0:
    print("E_PROMOTION_JOIN_EMPTY", file=sys.stderr); raise SystemExit(1)
print(f"Promotion migration join passed ({count} records).")
PY
