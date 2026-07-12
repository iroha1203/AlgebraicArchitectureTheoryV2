#!/usr/bin/env bash
set -euo pipefail

[ "$#" -ge 2 ] || {
  echo "usage: $0 CONTRACT_TSV AUDIT_TSV..." >&2
  exit 2
}

contract="$1"
shift
audits=("$@")

[ -f "$contract" ] || { echo "E_BRIDGE_CONTRACT_MISSING: $contract" >&2; exit 2; }
for audit in "${audits[@]}"; do
  [ -f "$audit" ] || { echo "E_BRIDGE_AUDIT_MISSING: $audit" >&2; exit 2; }
done

python3 - "$contract" "${audits[@]}" <<'PY'
import hashlib
import pathlib
import re
import sys

contract_path = pathlib.Path(sys.argv[1])
audit_paths = [pathlib.Path(path) for path in sys.argv[2:]]
digest_pattern = re.compile(r"[0-9a-f]{64}")


def fail(code, detail):
    print(f"{code}: {detail}", file=sys.stderr)
    raise SystemExit(1)


def digest(value):
    return hashlib.sha256(value.encode("utf-8")).hexdigest()


# The checker accepts either the raw output of MigrationAudit
#
#   MIGRATION_DECL module declaration levels type value axioms
#
# or the compact fixture form
#
#   BRIDGE_DECL declaration typeDigest valueDigest
#
# Compact rows keep the negative self-tests independent of Lean startup.
actual = {}
for audit_path in audit_paths:
    for number, raw in enumerate(audit_path.read_text(encoding="utf-8").splitlines(), 1):
        if not raw or raw.startswith("#") or raw.startswith("MIGRATION_META\t"):
            continue
        fields = raw.split("\t")
        if fields[0] == "MIGRATION_DECL":
            if len(fields) != 7:
                fail("E_BRIDGE_AUDIT_FORMAT", f"{audit_path}:{number}")
            declaration = fields[2]
            type_digest = digest(fields[4])
            value_digest = digest(fields[5])
        elif fields[0] == "BRIDGE_DECL":
            if len(fields) != 4 or not digest_pattern.fullmatch(fields[2]) or not digest_pattern.fullmatch(fields[3]):
                fail("E_BRIDGE_AUDIT_FORMAT", f"{audit_path}:{number}")
            declaration, type_digest, value_digest = fields[1:]
        else:
            fail("E_BRIDGE_AUDIT_FORMAT", f"{audit_path}:{number}")
        if declaration in actual:
            fail("E_BRIDGE_AUDIT_DUPLICATE", declaration)
        actual[declaration] = {"type": type_digest, "value": value_digest}

seen_cases = set()
checked = 0
for number, raw in enumerate(contract_path.read_text(encoding="utf-8").splitlines(), 1):
    if not raw or raw.startswith("#"):
        continue
    fields = raw.split("\t")
    if len(fields) != 5:
        fail("E_BRIDGE_CONTRACT_FORMAT", f"{contract_path}:{number}")
    case_id, declaration, facet, expected, error_code = fields
    if case_id in seen_cases:
        fail("E_BRIDGE_CONTRACT_DUPLICATE", case_id)
    seen_cases.add(case_id)
    if facet not in {"presence", "type", "value"}:
        fail("E_BRIDGE_CONTRACT_FORMAT", f"{case_id}: unknown facet {facet}")
    if not error_code.startswith("E_BRIDGE_"):
        fail("E_BRIDGE_CONTRACT_FORMAT", f"{case_id}: invalid error code")
    if expected == "PENDING":
        fail("E_BRIDGE_GOLDEN_PENDING", case_id)
    if facet == "presence":
        if expected != "present":
            fail("E_BRIDGE_CONTRACT_FORMAT", f"{case_id}: presence must be present")
        if declaration not in actual:
            fail(error_code, f"{case_id}: missing {declaration}")
    else:
        if declaration not in actual:
            fail(error_code, f"{case_id}: missing {declaration}")
        if expected.startswith("same-as:"):
            reference = expected.removeprefix("same-as:")
            if reference not in actual:
                fail("E_BRIDGE_CONTRACT_REFERENCE", f"{case_id}: missing {reference}")
            expected_digest = actual[reference][facet]
        else:
            if not digest_pattern.fullmatch(expected):
                fail("E_BRIDGE_CONTRACT_FORMAT", f"{case_id}: invalid digest")
            expected_digest = expected
        if actual[declaration][facet] != expected_digest:
            fail(error_code, f"{case_id}: {declaration} {facet} contract mismatch")
    checked += 1

if checked == 0:
    fail("E_BRIDGE_CONTRACT_EMPTY", contract_path)

print(f"Grounded packet bridge audit passed ({checked} selected contracts).")
PY
