#!/usr/bin/env bash
set -euo pipefail

repo_root="$(git rev-parse --show-toplevel 2>/dev/null || pwd)"
[ "$#" -eq 2 ] || { echo "usage: $0 BASE HEAD" >&2; exit 2; }

if [ -n "${AAT_PUBLIC_ARTIFACT_DIFF_FILE:-}" ]; then
  diff_file="$AAT_PUBLIC_ARTIFACT_DIFF_FILE"
else
  git rev-parse --verify "$1^{commit}" >/dev/null 2>&1 || { echo "E_INVALID_REF: $1" >&2; exit 2; }
  git rev-parse --verify "$2^{commit}" >/dev/null 2>&1 || { echo "E_INVALID_REF: $2" >&2; exit 2; }
  diff_file="$(mktemp)"
  trap 'rm -f "$diff_file"' EXIT
  git diff --no-ext-diff --no-textconv --unified=0 --find-renames "$1...$2" -- >"$diff_file"
fi

python3 - "$diff_file" <<'PY'
import re
import sys

negative = ".github/lean_quality/fixtures/changed_public_artifacts/negative/"
hidden = set(range(0x200B, 0x2010)) | set(range(0x202A, 0x202F)) | set(range(0x2066, 0x206A))
private_patterns = (
    re.compile("/" + "Users/"), re.compile("/" + "home/"),
    re.compile(r"C:\\" + r"Users\\"), re.compile("Docu" + "ments/"),
)
machine_patterns = ("Hello" + "Lean", "private/" + "internal")
primitive = re.compile(r"(?<![A-Za-z0-9_'])(axiom|admit|sorry|unsafe)(?![A-Za-z0-9_'])")

path = ""
new_line = 0
violations = []
for raw in open(sys.argv[1], encoding="utf-8", errors="replace"):
    if raw.startswith("+++ b/"):
        path = raw[6:].rstrip("\n")
        continue
    if raw.startswith("@@"):
        match = re.search(r"\+(\d+)(?:,(\d+))?", raw)
        if not match:
            print("E_DIFF_FORMAT: malformed hunk", file=sys.stderr)
            raise SystemExit(2)
        new_line = int(match.group(1))
        continue
    if not raw.startswith(("+", "-", " ")) or raw.startswith(("+++", "---")):
        continue
    added = raw.startswith("+")
    payload = raw[1:].rstrip("\n")
    line_number = new_line
    if not raw.startswith("-"):
        new_line += 1
    if not added or path.startswith(negative):
        continue
    if any(ord(char) in hidden for char in payload):
        violations.append((path, line_number, "E_HIDDEN_UNICODE"))
    if any(pattern.search(payload) for pattern in private_patterns):
        violations.append((path, line_number, "E_PRIVATE_LOCAL_PATH"))
    if any(token in payload for token in machine_patterns):
        violations.append((path, line_number, "E_MACHINE_IDENTIFIER"))
    if path.endswith(".lean") and primitive.search(payload):
        violations.append((path, line_number, "E_FORBIDDEN_LEAN_PRIMITIVE"))

if violations:
    for path, line, code in sorted(set(violations)):
        print(f"{code}: {path}:{line}", file=sys.stderr)
    raise SystemExit(1)
print("Changed public artifact scan passed.")
PY
