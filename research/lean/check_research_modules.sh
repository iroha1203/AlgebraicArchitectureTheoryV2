#!/usr/bin/env bash
set -euo pipefail

package_root="$(cd "$(dirname "$0")" && pwd)"
manifest="$package_root/research-modules.txt"
[ -f "$manifest" ] || { echo "E_RESEARCH_MODULE_MANIFEST: missing manifest" >&2; exit 2; }

if [ "${1:-}" = "--focused" ]; then
  [ "$#" -eq 2 ] || { echo "usage: $0 --focused SOURCE" >&2; exit 2; }
  source="$2"
  awk -F '\t' -v source="$source" '$0 !~ /^#/ && $2 == source { found = 1 } END { exit !found }' "$manifest" || {
    echo "E_RESEARCH_FOCUSED_NOT_REGISTERED: $source" >&2; exit 1;
  }
  [ -f "$package_root/$source" ] || { echo "E_RESEARCH_MODULE_MISSING: $source" >&2; exit 1; }
  (cd "$package_root" && lake env lean "$source")
  echo "Research single-file focused check passed: $source"
  exit 0
fi

echo "usage: $0 --focused SOURCE" >&2
exit 2
