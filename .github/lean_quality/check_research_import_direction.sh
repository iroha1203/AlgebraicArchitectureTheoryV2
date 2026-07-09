#!/usr/bin/env bash
set -euo pipefail

base_ref="${1:-${GITHUB_BASE_REF:-origin/main}}"

if [ -n "${GITHUB_BASE_REF:-}" ]; then
  base_ref="origin/${GITHUB_BASE_REF}"
fi

if ! git rev-parse --verify "$base_ref" >/dev/null 2>&1; then
  base_ref="origin/main"
fi

if [ -n "${AAT_RESEARCH_IMPORT_DIFF_FILE:-}" ]; then
  diff_input="$(cat "$AAT_RESEARCH_IMPORT_DIFF_FILE")"
else
  diff_input="$(git diff --unified=0 "$base_ref" -- 'Formal/**/*.lean' '*.lean')"
fi

violations="$(
  printf '%s\n' "$diff_input" \
    | awk '
      /^\+\+\+ b\// { file = substr($0, 7); next }
      /^\+import Formal\.AG\.Research/ {
        if (file !~ /^Formal\/AG\/Research(\.lean|\/)/) {
          print file ":" substr($0, 2)
        }
      }
    '
)"

if [ -n "$violations" ]; then
  echo "New mainline import(s) from Formal.AG.Research detected:"
  echo "$violations"
  exit 1
fi

echo "No new forbidden Formal.AG.Research imports outside the research sandbox."
