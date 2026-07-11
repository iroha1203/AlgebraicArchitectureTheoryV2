#!/usr/bin/env bash
set -euo pipefail

repo_root="$(git rev-parse --show-toplevel 2>/dev/null || pwd)"
fixture_root="${AAT_RESEARCH_LEGACY_FIXTURE_ROOT:-$repo_root/.github/lean_quality/fixtures/research_legacy_refs/negative}"
expectations="$fixture_root/expectations.tsv"

die() {
  printf '%s\n' "$1" >&2
  exit "${2:-1}"
}

validate_expectations() {
  [ -f "$expectations" ] || die "E_MISSING_EXPECTATIONS: $expectations" 2

  python3 - "$fixture_root" "$expectations" <<'PY'
import pathlib
import sys

root = pathlib.Path(sys.argv[1]).resolve()
manifest = pathlib.Path(sys.argv[2]).resolve()
symlinks = sorted(path.relative_to(root).as_posix() for path in root.rglob("*") if path.is_symlink())
if symlinks:
    print("E_FIXTURE_SYMLINK: " + ", ".join(symlinks), file=sys.stderr)
    raise SystemExit(1)
rows = []
contracts = []
for number, raw in enumerate(manifest.read_text(encoding="utf-8").splitlines(), 1):
    if not raw or raw.startswith("#"):
        continue
    fields = raw.split("\t")
    if len(fields) != 5:
        print(f"E_EXPECTATION_FORMAT: line {number}", file=sys.stderr)
        raise SystemExit(2)
    case_id, relative, command, subject, code = fields
    allowed = {
        "support": {"-"},
        "import-gate": {"E_RESEARCH_REACHABILITY"},
        "legacy-final": {"E_LEGACY_CONTENT", "E_LEGACY_PATH"},
        "legacy-no-new-content": {"E_LEGACY_CONTENT"},
        "legacy-no-new-path": {"E_LEGACY_PATH"},
    }
    if command not in allowed:
        print(f"E_EXPECTATION_COMMAND: line {number}", file=sys.stderr)
        raise SystemExit(2)
    if not case_id or not subject or code not in allowed[command]:
        print(f"E_EXPECTATION_CONTRACT: line {number}", file=sys.stderr)
        raise SystemExit(2)
    subject_path = pathlib.PurePosixPath(subject)
    if command in {"support", "import-gate"}:
        if len(subject_path.parts) != 1 or subject in {".", "..", "-"}:
            print(f"E_EXPECTATION_SUBJECT: line {number}", file=sys.stderr)
            raise SystemExit(2)
    elif command == "legacy-final":
        if subject_path.is_absolute() or ".." in subject_path.parts or subject in {".", "-"}:
            print(f"E_EXPECTATION_SUBJECT: line {number}", file=sys.stderr)
            raise SystemExit(2)
    elif subject != "-":
        print(f"E_EXPECTATION_SUBJECT: line {number}", file=sys.stderr)
        raise SystemExit(2)
    path = (root / relative).resolve()
    try:
        path.relative_to(root)
    except ValueError:
        print(f"E_EXPECTATION_PATH: line {number}", file=sys.stderr)
        raise SystemExit(2)
    if not path.is_file():
        print(f"E_MISSING_FIXTURE: {relative}", file=sys.stderr)
        raise SystemExit(1)
    rows.append((case_id, relative))
    contracts.append((relative, command, subject))
case_ids = [case_id for case_id, _relative in rows]
if len(case_ids) != len(set(case_ids)):
    print("E_DUPLICATE_CASE_ID", file=sys.stderr)
    raise SystemExit(1)
relative_rows = [relative for _case_id, relative in rows]
if len(relative_rows) != len(set(relative_rows)):
    print("E_DUPLICATE_EXPECTATION", file=sys.stderr)
    raise SystemExit(1)
import_cases = {}
support_subjects = set()
for relative, command, subject in contracts:
    if command not in {"support", "import-gate"}:
        continue
    relative_path = pathlib.PurePosixPath(relative)
    if not relative_path.parts or relative_path.parts[0] != subject or relative_path.suffix != ".lean":
        print(f"E_EXPECTATION_PROVENANCE: {relative}", file=sys.stderr)
        raise SystemExit(1)
    module_relative = pathlib.PurePosixPath(*relative_path.parts[1:]).as_posix()
    if not (
        module_relative in {"Formal.lean", "Main.lean", "ResearchLean.lean"}
        or module_relative.startswith("Formal/")
        or module_relative.startswith("ResearchLean/")
    ):
        print(f"E_EXPECTATION_PROVENANCE: {relative}", file=sys.stderr)
        raise SystemExit(1)
    if command == "import-gate":
        import_cases[subject] = import_cases.get(subject, 0) + 1
    else:
        support_subjects.add(subject)
if any(count != 1 for count in import_cases.values()) or support_subjects - set(import_cases):
    print("E_EXPECTATION_SCENARIO", file=sys.stderr)
    raise SystemExit(1)
actual = sorted(
    path.relative_to(root).as_posix()
    for path in root.rglob("*")
    if path.is_file() and path.resolve() != manifest
)
listed = sorted(relative_rows)
missing = sorted(set(actual) - set(listed))
extra = sorted(set(listed) - set(actual))
if missing:
    print("E_UNREGISTERED_FIXTURE: " + ", ".join(missing), file=sys.stderr)
    raise SystemExit(1)
if extra:
    print("E_MISSING_FIXTURE: " + ", ".join(extra), file=sys.stderr)
    raise SystemExit(1)
PY
}

registered_fixture() {
  local path="$1"
  local relative
  case "$path" in
    .github/lean_quality/fixtures/research_legacy_refs/negative/*)
      relative="${path#.github/lean_quality/fixtures/research_legacy_refs/negative/}"
      awk -F '\t' -v wanted="$relative" '$0 !~ /^#/ && $2 == wanted { found = 1 } END { exit !found }' "$expectations"
      ;;
    *) return 1 ;;
  esac
}

allowed_path() {
  local path="$1"
  case "$path" in
    .github/lean_quality/check_research_legacy_refs.sh|\
    .github/lean_quality/fixtures/research_legacy_refs/negative/expectations.tsv|\
    docs/archive/*) return 0 ;;
  esac
  registered_fixture "$path"
}

contains_legacy_ref() {
  LC_ALL=C grep -F -e 'Formal/AG/Research' -e 'Formal.AG.Research' -e 'FormalAGResearch' "$1" >/dev/null 2>&1
}

report_legacy_content() {
  python3 - "$1" "$2" <<'PY'
import pathlib
import sys

path = pathlib.Path(sys.argv[1])
relative = sys.argv[2]
tokens = ("Formal/AG/Research", "Formal.AG.Research", "FormalAGResearch")
for number, line in enumerate(path.read_text(encoding="utf-8", errors="replace").splitlines(), 1):
    for token in tokens:
        if token in line:
            print(f"E_LEGACY_CONTENT: {relative}:{number} token={token}")
PY
}

legacy_path() {
  case "$1" in
    Formal/AG/Research.lean|Formal/AG/Research/*) return 0 ;;
    *) return 1 ;;
  esac
}

validate_expectations

mode="${1:-}"
case "$mode" in
  no-new)
    [ "$#" -eq 3 ] || die "usage: $0 no-new BASE HEAD" 2
    base="$2"
    head="$3"
    diff_file="$(mktemp)"
    trap 'rm -f "$diff_file"' EXIT
    if [ -n "${AAT_RESEARCH_LEGACY_DIFF_FILE:-}" ]; then
      cp "$AAT_RESEARCH_LEGACY_DIFF_FILE" "$diff_file"
    else
      git rev-parse --verify "$base^{commit}" >/dev/null 2>&1 || die "E_INVALID_REF: $base" 2
      git rev-parse --verify "$head^{commit}" >/dev/null 2>&1 || die "E_INVALID_REF: $head" 2
      git diff --no-ext-diff --no-textconv --unified=0 --find-renames "$base...$head" -- >"$diff_file"
    fi
    python3 - "$diff_file" <<'PY' | while IFS=$'\t' read -r path payload; do
import re
import sys

path = ""
for line in open(sys.argv[1], encoding="utf-8", errors="replace"):
    if line.startswith("+++ b/"):
        path = line[6:].rstrip("\n")
    elif line.startswith("+") and not line.startswith("+++"):
        payload = line[1:].rstrip("\n")
        if any(token in payload for token in ("Formal/AG/Research", "Formal.AG.Research", "FormalAGResearch")):
            print(path + "\t" + payload)
PY
      if ! allowed_path "$path"; then
        printf 'E_LEGACY_CONTENT: %s\n' "$path" >&2
        exit 1
      fi
    done
    if [ -n "${AAT_RESEARCH_LEGACY_NAME_FILE:-}" ]; then
      name_source=(cat "$AAT_RESEARCH_LEGACY_NAME_FILE")
    else
      name_source=(git diff --name-only --diff-filter=ACMR "$base...$head" --)
    fi
    while IFS= read -r path; do
      if legacy_path "$path" && ! allowed_path "$path"; then
        die "E_LEGACY_PATH: $path"
      fi
    done < <("${name_source[@]}")
    echo "No new legacy Research references outside the narrow allowlist."
    ;;
  final)
    [ "$#" -eq 1 ] || die "usage: $0 final" 2
    scan_root="${AAT_RESEARCH_LEGACY_SCAN_ROOT:-$repo_root}"
    violations="$(mktemp)"
    trap 'rm -f "$violations"' EXIT
    if [ -n "${AAT_RESEARCH_LEGACY_SCAN_ROOT:-}" ]; then
      while IFS= read -r -d '' absolute; do
        relative="${absolute#"$scan_root"/}"
        if legacy_path "$relative" && ! allowed_path "$relative"; then
          printf 'E_LEGACY_PATH: %s\n' "$relative" >>"$violations"
        fi
        if contains_legacy_ref "$absolute" && ! allowed_path "$relative"; then
          report_legacy_content "$absolute" "$relative" >>"$violations"
        fi
      done < <(find "$scan_root" -type f -print0)
    else
      while IFS= read -r -d '' relative; do
        if legacy_path "$relative" && ! allowed_path "$relative"; then
          printf 'E_LEGACY_PATH: %s\n' "$relative" >>"$violations"
        fi
        if contains_legacy_ref "$repo_root/$relative" && ! allowed_path "$relative"; then
          report_legacy_content "$repo_root/$relative" "$relative" >>"$violations"
        fi
      done < <(git ls-files -z)
    fi
    if [ -s "$violations" ]; then
      sort -u "$violations" >&2
      exit 1
    fi
    echo "Legacy Research reference final gate passed."
    ;;
  *) die "usage: $0 {no-new BASE HEAD|final}" 2 ;;
esac
