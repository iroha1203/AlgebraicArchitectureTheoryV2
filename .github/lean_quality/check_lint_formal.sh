#!/usr/bin/env bash
set -euo pipefail

entrypoint=".github/lean_quality/LintFormal.lean"
baseline=".github/lean_quality/lint-formal-baseline.txt"
out_dir=".tmp/lean-quality"
raw="$out_dir/lint-formal.raw.txt"
actual="$out_dir/lint-formal.txt"

mkdir -p "$out_dir"

set +e
lake env lean "$entrypoint" >"$raw" 2>&1
status=$?
set -e

sed -E 's#^.*LintFormal\.lean:[0-9]+:[0-9]+: error: ##' "$raw" >"$actual"

if ! diff -u "$baseline" "$actual"; then
  echo
  echo "Lean quality lint output changed."
  echo "Review the new findings. If the change is an intentional baseline update,"
  echo "replace $baseline with $actual in the same PR and document the reason."
  exit 1
fi

if [ "$status" -eq 0 ]; then
  echo "Lean quality lint baseline matched with no lint process error."
else
  echo "Lean quality lint baseline matched existing findings."
fi
