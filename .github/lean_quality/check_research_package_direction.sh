#!/usr/bin/env bash
set -euo pipefail

repo_root="$(git rev-parse --show-toplevel)"
fixture="$repo_root/.github/lean_quality/fixtures/research_package_direction/root_imports_research.lean"

if rg -n '^name = "ResearchLean"$|^path = "research-lean"$' "$repo_root/lakefile.toml" >/dev/null; then
  echo "E_ROOT_REQUIRES_RESEARCH: root lakefile references the Research package" >&2
  exit 1
fi

grep -F 'path = ".."' "$repo_root/research-lean/lakefile.toml" >/dev/null || {
  echo "E_RESEARCH_ROOT_DEPENDENCY: Research package does not depend on root" >&2
  exit 1
}

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
