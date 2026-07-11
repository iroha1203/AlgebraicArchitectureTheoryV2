#!/usr/bin/env bash
set -euo pipefail

root="$(git rev-parse --show-toplevel)"
checker="$root/.github/lean_quality/check_research_package_direction.sh"
fixtures="$root/.github/lean_quality/fixtures/research_package_direction"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

"$checker"
for fixture in "$fixtures"/negative/*.toml; do
  if AAT_ROOT_LAKEFILE="$fixture" "$checker" >"$tmp/stdout" 2>"$tmp/stderr"; then
    echo "package direction fixture unexpectedly passed: $(basename "$fixture")" >&2
    exit 1
  fi
  grep -F E_ROOT_REQUIRES_RESEARCH "$tmp/stderr" >/dev/null || {
    cat "$tmp/stderr" >&2
    exit 1
  }
done
echo "Research package dependency direction fixtures passed."
