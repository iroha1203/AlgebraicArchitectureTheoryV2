#!/usr/bin/env bash
set -euo pipefail

package_root="$(cd "$(dirname "$0")" && pwd)"
repo_root="$(git -C "$package_root" rev-parse --show-toplevel)"

resolve_source() {
  local source="$1"
  if [ -f "$package_root/$source" ]; then
    source_candidate="$package_root/$source"
  elif [ -f "$repo_root/$source" ]; then
    source_candidate="$repo_root/$source"
  else
    echo "E_MIGRATION_SOURCE: $source" >&2
    return 1
  fi
  source_abs="$(python3 - "$source_candidate" <<'PY'
import pathlib
import sys
print(pathlib.Path(sys.argv[1]).resolve(strict=True))
PY
)"
  case "$source_abs" in "$repo_root"/*) ;; *) echo "E_MIGRATION_SOURCE_OUTSIDE_REPO: $source" >&2; return 1 ;; esac
}

if [ "${1:-}" = "--resolve-source" ]; then
  [ "$#" -eq 2 ] || { echo "usage: $0 --resolve-source SOURCE" >&2; exit 2; }
  resolve_source "$2"
  printf 'MIGRATION_SOURCE\t%s\n' "${source_abs#"$repo_root"/}"
  exit 0
fi

[ "$#" -eq 3 ] || { echo "usage: $0 MODULE SOURCE OUT_TSV" >&2; exit 2; }
module="$1"
source="$2"
out="$3"
legacy_prefix="Formal.AG.Resear""ch."
case "$module" in "$legacy_prefix"*|ResearchLean.AG.*) ;; *) echo "E_MIGRATION_MODULE: $module" >&2; exit 1 ;; esac
resolve_source "$source"
commit="$(git -C "$repo_root" rev-parse HEAD)"
source_rel="${source_abs#"$repo_root"/}"
source_digest="$(python3 - "$source_abs" <<'PY'
import hashlib, pathlib, sys
print(hashlib.sha256(pathlib.Path(sys.argv[1]).read_bytes()).hexdigest())
PY
)"

tmp="$package_root/.tmp-migration-audit.lean"
trap 'rm -f "$tmp"' EXIT
printf 'import %s\nimport ResearchLean.Tools.MigrationAudit\n#emit_migration_audit %s\n' "$module" "$module" >"$tmp"
[ -n "$commit" ] && [ -n "$source_digest" ] || { echo "E_MIGRATION_META" >&2; exit 1; }
printf 'MIGRATION_META\t%s\t%s\t%s\t%s\n' "$commit" "$module" "$source_rel" "$source_digest" >"$out"
(cd "$package_root" && lake env lean "$(basename "$tmp")") | awk -F '\t' '$1 == "MIGRATION_DECL"' >>"$out"
grep -q '^MIGRATION_DECL' "$out" || { echo "E_MIGRATION_AUDIT_EMPTY: $module" >&2; exit 1; }
