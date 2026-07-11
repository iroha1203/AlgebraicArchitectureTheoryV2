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

[ "${1:-}" = "--all-axioms" ] && [ "$#" -eq 1 ] || {
  echo "usage: $0 {--focused SOURCE|--all-axioms}" >&2; exit 2;
}
[ "${AAT_CI_FULL_AUDIT:-}" = "1" ] || {
  echo "E_RESEARCH_FULL_AUDIT_GUARD: all-module audit is CI-only" >&2; exit 2;
}

seen="$(mktemp)"
trap 'rm -f "$seen"' EXIT
while IFS=$'\t' read -r module source extra; do
  case "$module" in ''|'#'*) continue ;; esac
  [ -z "${extra:-}" ] || { echo "E_RESEARCH_MODULE_MANIFEST: extra column for $module" >&2; exit 2; }
  case "$module" in ResearchLean.AG.*) ;; *) echo "E_RESEARCH_MODULE_NAME: $module" >&2; exit 1 ;; esac
  case "$source" in ResearchLean/*.lean) ;; *) echo "E_RESEARCH_MODULE_SOURCE: $source" >&2; exit 1 ;; esac
  expected="${source%.lean}"; expected="${expected//\//.}"
  [ "$module" = "$expected" ] || { echo "E_RESEARCH_MODULE_MAPPING: $module != $source" >&2; exit 1; }
  [ -f "$package_root/$source" ] || { echo "E_RESEARCH_MODULE_MISSING: $source" >&2; exit 1; }
  grep -Fx "$module" "$seen" >/dev/null && { echo "E_RESEARCH_MODULE_DUPLICATE: $module" >&2; exit 1; }
  printf '%s\n' "$module" >>"$seen"
  (cd "$package_root" && lake env lean "$source")
  audit="$(mktemp)"
  "$package_root/emit_migration_audit.sh" "$module" "$source" "$audit"
  while IFS=$'\t' read -r marker _module _name _levels _type _value axioms extra; do
    [ "$marker" = "MIGRATION_META" ] && continue
    [ "$marker" = "MIGRATION_DECL" ] && [ -z "${extra:-}" ] || { echo "E_RESEARCH_AXIOM_AUDIT_FORMAT: $module" >&2; exit 1; }
    if [ "$axioms" != '$NO_AXIOMS' ]; then
      IFS=',' read -r -a axiom_items <<<"$axioms"
      for axiom in "${axiom_items[@]}"; do
        case "$axiom" in propext|Classical.choice|Quot.sound) ;; *) echo "E_RESEARCH_NONSTANDARD_AXIOM: $module" >&2; exit 1 ;; esac
      done
    fi
  done <"$audit"
  rm -f "$audit"
done <"$manifest"

[ -s "$seen" ] || { echo "E_RESEARCH_MODULE_MANIFEST: no modules" >&2; exit 1; }
actual_sources="$(find "$package_root/ResearchLean/AG" -type f -name '*.lean' -print | sed "s#^$package_root/##" | sort)"
manifest_sources="$(awk -F '\t' '$0 !~ /^#/ && NF { print $2 }' "$manifest" | sort)"
[ "$actual_sources" = "$manifest_sources" ] || { echo "E_RESEARCH_MODULE_COVERAGE" >&2; exit 1; }
echo "Research all-module focused checks and all-declaration axiom audits passed."
