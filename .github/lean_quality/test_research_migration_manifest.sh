#!/usr/bin/env bash
set -euo pipefail

root="$(git rev-parse --show-toplevel)"
checker="$root/.github/lean_quality/check_research_migration_manifest.sh"
record_checker="$root/.github/lean_quality/check_research_migration_records.sh"
join_checker="$root/.github/lean_quality/check_research_promotion_migration_join.sh"
fixture="$root/.github/lean_quality/fixtures/research_migration/good"
promotion_fixture="$root/.github/lean_quality/fixtures/research_migration/promotion"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

run_check() {
  AAT_MIGRATION_TEST_PREFIXES=1 AAT_MIGRATION_TEST_SOURCE_ROOT="$fixture" \
    "$checker" ignored-base ignored-head "$1" "$2" "$3" "$4" "$tmp/out"
}

run_check "$fixture/manifest.tsv" "$fixture/old.audit.tsv" "$fixture/new.audit.tsv" R3
test -s "$tmp/out/declarations.jsonl"
jq -e '.schema == "aat-research-migration/v1" and .moduleCount == 1 and .declarationCount == 4' "$tmp/out/metadata.json" >/dev/null
jq -s -e 'map(.migration_record) | sort == ["R3/Smoke.lean#Shared.Inner.witness", "R3/Smoke.lean#Smoke.witness", "R3/Smoke.lean#commit!", "R3/Smoke.lean#firstFailingSlot?"]' "$tmp/out/declarations.jsonl" >/dev/null
"$record_checker" "$tmp/out/declarations.jsonl"
printf '%s\n' $'research_decl\tmigration_record' \
  $'ResearchLean.AG.Smoke.firstFailingSlot?\tR3/Smoke.lean#firstFailingSlot?' \
  $'ResearchLean.AG.Smoke.commit!\tR3/Smoke.lean#commit!' >"$tmp/symbol-promotion.tsv"
"$join_checker" "$tmp/symbol-promotion.tsv" "$tmp/out/declarations.jsonl"

mkdir -p "$tmp/promotion-out"
AAT_MIGRATION_TEST_PREFIXES=1 AAT_MIGRATION_TEST_SOURCE_ROOT="$promotion_fixture" \
  "$checker" ignored-base ignored-head "$promotion_fixture/manifest.tsv" \
  "$promotion_fixture/old.audit.tsv" "$promotion_fixture/new.audit.tsv" R4 "$tmp/promotion-out"
cp "$tmp/promotion-out/declarations.jsonl" "$tmp/promotion-key.jsonl"
"$record_checker" "$tmp/promotion-key.jsonl"
printf '%s\n' $'research_decl\tmigration_record' \
  $'ResearchLean.AG.QualitySurface.SemanticRepairLawEquationGroundedPacket.lawEquation_constructs_groundedComparisonPacket\tR4/QualitySurface/SemanticRepairLawEquationGroundedPacket.lean#lawEquation_constructs_groundedComparisonPacket' \
  >"$tmp/promotion.tsv"
"$join_checker" "$tmp/promotion.tsv" "$tmp/promotion-key.jsonl"

cp "$tmp/out/declarations.jsonl" "$tmp/duplicate.jsonl"
cat "$tmp/out/declarations.jsonl" >>"$tmp/duplicate.jsonl"
if "$record_checker" "$tmp/duplicate.jsonl" >"$tmp/stdout" 2>"$tmp/stderr"; then
  echo "duplicate migration_record fixture unexpectedly passed" >&2; exit 1
fi
grep -F E_MIGRATION_RECORD_DUPLICATE "$tmp/stderr" >/dev/null

jq -c 'del(.typeDigest)' "$tmp/out/declarations.jsonl" >"$tmp/missing.jsonl"
if "$record_checker" "$tmp/missing.jsonl" >"$tmp/stdout" 2>"$tmp/stderr"; then
  echo "missing digest fixture unexpectedly passed" >&2; exit 1
fi
grep -F E_MIGRATION_DIGEST_MISSING "$tmp/stderr" >/dev/null

jq -c '.migration_record = "bad"' "$tmp/out/declarations.jsonl" >"$tmp/malformed.jsonl"
if "$record_checker" "$tmp/malformed.jsonl" >"$tmp/stdout" 2>"$tmp/stderr"; then
  echo "malformed migration_record fixture unexpectedly passed" >&2; exit 1
fi
grep -F E_MIGRATION_RECORD_FORMAT "$tmp/stderr" >/dev/null

cp "$fixture/new.audit.tsv" "$tmp/bad.audit.tsv"
sed -i.bak 's/type:nat/type:string/' "$tmp/bad.audit.tsv"
if run_check "$fixture/manifest.tsv" "$fixture/old.audit.tsv" "$tmp/bad.audit.tsv" R3 >"$tmp/stdout" 2>"$tmp/stderr"; then
  echo "digest mismatch fixture unexpectedly passed" >&2; exit 1
fi
grep -F E_MIGRATION_DECLARATION_DIGEST "$tmp/stderr" >/dev/null

printf '%s\n' $'MIGRATION_DECL\t$RESEARCH.Smoke\t$RESEARCH.Smoke.witness\t\ttype:nat\tvalue:1\t$NO_AXIOMS' >>"$tmp/bad.audit.tsv"
if run_check "$fixture/manifest.tsv" "$fixture/old.audit.tsv" "$tmp/bad.audit.tsv" R3 >"$tmp/stdout" 2>"$tmp/stderr"; then
  echo "duplicate declaration fixture unexpectedly passed" >&2; exit 1
fi
grep -F E_MIGRATION_DECL_DUPLICATE "$tmp/stderr" >/dev/null

if run_check "$fixture/manifest.tsv" "$fixture/old.audit.tsv" "$fixture/new.audit.tsv" RX >"$tmp/stdout" 2>"$tmp/stderr"; then
  echo "invalid key batch fixture unexpectedly passed" >&2; exit 1
fi
grep -F E_MIGRATION_BATCH "$tmp/stderr" >/dev/null

cp "$fixture/manifest.tsv" "$tmp/bad-manifest.tsv"
sed -i.bak 's#old/Smoke.lean#old/Other.lean#' "$tmp/bad-manifest.tsv"
if run_check "$tmp/bad-manifest.tsv" "$fixture/old.audit.tsv" "$fixture/new.audit.tsv" R3 >"$tmp/stdout" 2>"$tmp/stderr"; then
  echo "source/module provenance fixture unexpectedly passed" >&2; exit 1
fi
grep -F E_MIGRATION_SOURCE_MODULE_PROVENANCE "$tmp/stderr" >/dev/null

cp "$fixture/new.audit.tsv" "$tmp/extra-module.audit.tsv"
printf '%s\n' $'MIGRATION_DECL\t$RESEARCH.Extra\t$RESEARCH.Extra.witness\t\ttype:nat\tvalue:1\t$NO_AXIOMS' >>"$tmp/extra-module.audit.tsv"
if run_check "$fixture/manifest.tsv" "$fixture/old.audit.tsv" "$tmp/extra-module.audit.tsv" R3 >"$tmp/stdout" 2>"$tmp/stderr"; then
  echo "extra audit module fixture unexpectedly passed" >&2; exit 1
fi
grep -F E_MIGRATION_DECLARATION_SET "$tmp/stderr" >/dev/null

component_root="$tmp/component-root"
cp -R "$fixture" "$component_root"
printf '%s\n' 'def dependencyName := "XFixtureOld.AG.Helper"' >>"$component_root/old/Smoke.lean"
printf '%s\n' 'def dependencyName := "XFixtureNew.AG.Helper"' >>"$component_root/research/lean/ResearchLean/AG/Smoke.lean"
if AAT_MIGRATION_TEST_PREFIXES=1 AAT_MIGRATION_TEST_SOURCE_ROOT="$component_root" "$checker" \
    ignored-base ignored-head "$component_root/manifest.tsv" "$component_root/old.audit.tsv" "$component_root/new.audit.tsv" \
    R3 "$tmp/component-out" >"$tmp/stdout" 2>"$tmp/stderr"; then
  echo "non-prefix component drift fixture unexpectedly passed" >&2; exit 1
fi
grep -F E_MIGRATION_SOURCE_DIGEST "$tmp/stderr" >/dev/null

nested_root="$tmp/nested-root"
cp -R "$fixture" "$nested_root"
printf '%s\n' 'def dependencyName := "X.FixtureOld.AG.Helper"' >>"$nested_root/old/Smoke.lean"
printf '%s\n' 'def dependencyName := "X.FixtureNew.AG.Helper"' >>"$nested_root/research/lean/ResearchLean/AG/Smoke.lean"
if AAT_MIGRATION_TEST_PREFIXES=1 AAT_MIGRATION_TEST_SOURCE_ROOT="$nested_root" "$checker" \
    ignored-base ignored-head "$nested_root/manifest.tsv" "$nested_root/old.audit.tsv" "$nested_root/new.audit.tsv" \
    R3 "$tmp/nested-out" >"$tmp/stdout" 2>"$tmp/stderr"; then
  echo "nested non-root prefix drift fixture unexpectedly passed" >&2; exit 1
fi
grep -F E_MIGRATION_SOURCE_DIGEST "$tmp/stderr" >/dev/null

unicode_root="$tmp/unicode-root"
cp -R "$fixture" "$unicode_root"
printf '%s\n' 'def dependencyName := "αFixtureOld.AG.Helper"' >>"$unicode_root/old/Smoke.lean"
printf '%s\n' 'def dependencyName := "αFixtureNew.AG.Helper"' >>"$unicode_root/research/lean/ResearchLean/AG/Smoke.lean"
if AAT_MIGRATION_TEST_PREFIXES=1 AAT_MIGRATION_TEST_SOURCE_ROOT="$unicode_root" "$checker" \
    ignored-base ignored-head "$unicode_root/manifest.tsv" "$unicode_root/old.audit.tsv" "$unicode_root/new.audit.tsv" \
    R3 "$tmp/unicode-out" >"$tmp/stdout" 2>"$tmp/stderr"; then
  echo "Unicode non-prefix drift fixture unexpectedly passed" >&2; exit 1
fi
grep -F E_MIGRATION_SOURCE_DIGEST "$tmp/stderr" >/dev/null

while IFS=$'\t' read -r label suffix; do
  adjacent_root="$tmp/adjacent-$label"
  cp -R "$fixture" "$adjacent_root"
  if [ "$suffix" = '»' ]; then
    printf '%s\n' 'def dependencyName := "«FixtureOld.AG»"' >>"$adjacent_root/old/Smoke.lean"
    printf '%s\n' 'def dependencyName := "«FixtureNew.AG»"' >>"$adjacent_root/research/lean/ResearchLean/AG/Smoke.lean"
  else
    printf 'def dependencyName := "FixtureOld.AG%s"\n' "$suffix" >>"$adjacent_root/old/Smoke.lean"
    printf 'def dependencyName := "FixtureNew.AG%s"\n' "$suffix" >>"$adjacent_root/research/lean/ResearchLean/AG/Smoke.lean"
  fi
  if AAT_MIGRATION_TEST_PREFIXES=1 AAT_MIGRATION_TEST_SOURCE_ROOT="$adjacent_root" "$checker" \
      ignored-base ignored-head "$adjacent_root/manifest.tsv" "$adjacent_root/old.audit.tsv" "$adjacent_root/new.audit.tsv" \
      R3 "$tmp/adjacent-out" >"$tmp/stdout" 2>"$tmp/stderr"; then
    echo "Lean identifier adjacency drift fixture unexpectedly passed: $suffix" >&2; exit 1
  fi
  grep -F E_MIGRATION_SOURCE_DIGEST "$tmp/stderr" >/dev/null
done <<'EOF'
qmark	?
bang	!
quoted	»
EOF

quoted_inner_root="$tmp/quoted-inner-root"
cp -R "$fixture" "$quoted_inner_root"
printf '%s\n' 'def dependencyName := "«X-FixtureOld.AG-Y»"' >>"$quoted_inner_root/old/Smoke.lean"
printf '%s\n' 'def dependencyName := "«X-FixtureNew.AG-Y»"' >>"$quoted_inner_root/research/lean/ResearchLean/AG/Smoke.lean"
if AAT_MIGRATION_TEST_PREFIXES=1 AAT_MIGRATION_TEST_SOURCE_ROOT="$quoted_inner_root" "$checker" \
    ignored-base ignored-head "$quoted_inner_root/manifest.tsv" "$quoted_inner_root/old.audit.tsv" \
    "$quoted_inner_root/new.audit.tsv" R3 "$tmp/quoted-inner-out" >"$tmp/stdout" 2>"$tmp/stderr"; then
  echo "quoted identifier interior drift fixture unexpectedly passed" >&2; exit 1
fi
grep -F E_MIGRATION_SOURCE_DIGEST "$tmp/stderr" >/dev/null

outside_source="$tmp/outside.lean"
printf '%s\n' 'def outside : Nat := 0' >"$outside_source"
outside_relative="$(python3 - "$root/research/lean" "$outside_source" <<'PY'
import os
import sys
print(os.path.relpath(sys.argv[2], sys.argv[1]))
PY
)"
if "$root/research/lean/emit_migration_audit.sh" ResearchLean.AG.Smoke "$outside_relative" \
    "$tmp/outside.audit.tsv" >"$tmp/stdout" 2>"$tmp/stderr"; then
  echo "outside-repository migration source fixture unexpectedly passed" >&2; exit 1
fi
grep -F E_MIGRATION_SOURCE_OUTSIDE_REPO "$tmp/stderr" >/dev/null

echo "Research migration manifest fixtures passed."
