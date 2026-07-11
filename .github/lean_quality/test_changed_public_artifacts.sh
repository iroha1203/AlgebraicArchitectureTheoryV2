#!/usr/bin/env bash
set -euo pipefail

root="$(git rev-parse --show-toplevel)"
checker="$root/.github/lean_quality/check_changed_public_artifacts.sh"
fixtures="$root/.github/lean_quality/fixtures/changed_public_artifacts"
manifest="$fixtures/negative/expectations.tsv"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

for positive in "$fixtures"/positive/*.diff; do
  AAT_PUBLIC_ARTIFACT_DIFF_FILE="$positive" "$checker" ignored ignored
done

listed="$(mktemp)"
trap 'rm -rf "$tmp"; rm -f "$listed"' EXIT
while IFS=$'\t' read -r case_id relative code extra; do
  case "$case_id" in ''|'#'*) continue ;; esac
  [ -z "${extra:-}" ] || { echo "E_PUBLIC_EXPECTATION_FORMAT" >&2; exit 2; }
  [ -f "$fixtures/negative/$relative" ] || { echo "E_PUBLIC_MISSING_FIXTURE: $relative" >&2; exit 1; }
  printf '%s\n' "$relative" >>"$listed"
  if AAT_PUBLIC_ARTIFACT_DIFF_FILE="$fixtures/negative/$relative" "$checker" ignored ignored >"$tmp/out" 2>"$tmp/err"; then
    echo "fixture unexpectedly passed: $case_id" >&2
    exit 1
  fi
  grep -F "$code" "$tmp/err" >/dev/null || { cat "$tmp/err" >&2; exit 1; }
done <"$manifest"

actual="$(find "$fixtures/negative" -type f ! -name expectations.tsv -exec basename {} \; | sort)"
expected="$(sort "$listed")"
[ "$actual" = "$expected" ] || { echo "E_PUBLIC_UNREGISTERED_FIXTURE" >&2; exit 1; }
echo "Changed public artifact fixtures passed."
