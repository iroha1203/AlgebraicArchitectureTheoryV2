#!/usr/bin/env bash
set -euo pipefail

repo_root="$(git rev-parse --show-toplevel)"
fixture="$repo_root/.github/lean_quality/fixtures/research_package_direction/root_imports_research.lean"
root_lakefile="${AAT_ROOT_LAKEFILE:-$repo_root/lakefile.toml}"
research_lakefile="${AAT_RESEARCH_LAKEFILE:-$repo_root/research/lean/lakefile.toml}"

python3 - "$root_lakefile" "$research_lakefile" <<'PY'
import pathlib
import posixpath
import sys
import tomllib

root_path, research_path = map(pathlib.Path, sys.argv[1:])
root = tomllib.loads(root_path.read_text(encoding="utf-8"))
research = tomllib.loads(research_path.read_text(encoding="utf-8"))

def normalized_path(require):
    path = require.get("path")
    return None if not isinstance(path, str) else posixpath.normpath(path.replace("\\", "/"))

for require in root.get("require", []):
    path = normalized_path(require)
    if require.get("name") == "ResearchLean" or path == "research/lean" or (path and path.startswith("research/lean/")):
        print("E_ROOT_REQUIRES_RESEARCH: root lakefile references the Research package", file=sys.stderr)
        raise SystemExit(1)

if not any(
    require.get("name") == "AlgebraicArchitectureTheoryV2" and normalized_path(require) == "../.."
    for require in research.get("require", [])
):
    print("E_RESEARCH_ROOT_DEPENDENCY: Research package does not depend on root", file=sys.stderr)
    raise SystemExit(1)
PY

if [ "${1:-}" = "--execute" ]; then
  output="$(mktemp)"
  trap 'rm -f "$output"' EXIT
  if (cd "$repo_root" && lake env lean "$fixture") >"$output" 2>&1; then
    echo "E_ROOT_CAN_IMPORT_RESEARCH: negative fixture unexpectedly passed" >&2
    exit 1
  fi
  grep -F "unknown module prefix 'ResearchLean'" "$output" >/dev/null || {
    echo "E_ROOT_IMPORT_FAILURE_REASON: negative fixture failed for an unexpected reason" >&2
    cat "$output" >&2
    exit 1
  }
elif [ "$#" -ne 0 ]; then
  echo "usage: $0 [--execute]" >&2
  exit 2
fi

echo "Research package dependency direction check passed."
