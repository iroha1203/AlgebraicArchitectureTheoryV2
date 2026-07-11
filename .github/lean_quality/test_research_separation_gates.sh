#!/usr/bin/env bash
set -euo pipefail

repo_root="$(git rev-parse --show-toplevel)"
import_gate="$repo_root/.github/lean_quality/check_research_import_direction.sh"
legacy_gate="$repo_root/.github/lean_quality/check_research_legacy_refs.sh"
negative_root="$repo_root/.github/lean_quality/fixtures/research_legacy_refs/negative"
import_fixture_root="$repo_root/.github/lean_quality/fixtures/research_import_direction"
expectations="$negative_root/expectations.tsv"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

expect_pass() {
  local label="$1"
  shift
  if ! "$@" >"$tmp/out" 2>"$tmp/err"; then
    echo "fixture unexpectedly failed: $label" >&2
    cat "$tmp/err" >&2
    exit 1
  fi
}

expect_fail() {
  local label="$1"
  local code="$2"
  shift 2
  if "$@" >"$tmp/out" 2>"$tmp/err"; then
    echo "fixture unexpectedly passed: $label" >&2
    exit 1
  fi
  if ! grep -F "$code" "$tmp/err" >/dev/null; then
    echo "fixture emitted the wrong diagnostic: $label (expected $code)" >&2
    cat "$tmp/err" >&2
    exit 1
  fi
}

copy_registered_fixtures() {
  local destination="$1"
  mkdir -p "$destination/.github/lean_quality/fixtures/research_legacy_refs/negative"
  cp "$expectations" "$destination/.github/lean_quality/fixtures/research_legacy_refs/negative/expectations.tsv"
  while IFS=$'\t' read -r case_id relative command subject code; do
    case "$case_id" in ''|'#'*) continue ;; esac
    mkdir -p "$destination/.github/lean_quality/fixtures/research_legacy_refs/negative/$(dirname "$relative")"
    cp "$negative_root/$relative" \
      "$destination/.github/lean_quality/fixtures/research_legacy_refs/negative/$relative"
  done <"$expectations"
}

expect_pass "clean import graph" "$import_gate" --root "$import_fixture_root/positive"
expect_fail "new-prefix import" "E_RESEARCH_REACHABILITY" \
  "$import_gate" --root "$import_fixture_root/negative/new-prefix"

new_file_root="$tmp/new-file"
cp -R "$import_fixture_root/positive" "$new_file_root"
research_segment="Research"
mkdir -p "$new_file_root/Formal/AG/$research_segment"
printf '%s\n' 'import Formal.AG.'"$research_segment"'.Basic' >"$new_file_root/Formal/AG/NewFile.lean"
printf '%s\n' 'def newResearch : Nat := 0' >"$new_file_root/Formal/AG/$research_segment/Basic.lean"
expect_fail "new untracked-style file" "E_RESEARCH_REACHABILITY" \
  "$import_gate" --root "$new_file_root"

synthetic="$tmp/synthetic"
mkdir -p "$synthetic/.github/lean_quality" "$synthetic/docs/archive"
copy_registered_fixtures "$synthetic"
cp "$legacy_gate" "$synthetic/.github/lean_quality/check_research_legacy_refs.sh"
printf '%s\n' 'archived Formal.AG.'"$research_segment"' reference' >"$synthetic/docs/archive/old.md"
expect_pass "legacy final allowlist" env \
  AAT_RESEARCH_LEGACY_SCAN_ROOT="$synthetic" \
  AAT_RESEARCH_LEGACY_FIXTURE_ROOT="$synthetic/.github/lean_quality/fixtures/research_legacy_refs/negative" \
  "$legacy_gate" final

empty_diff="$tmp/empty.diff"
empty_names="$tmp/empty.names"
: >"$empty_diff"
: >"$empty_names"

while IFS=$'\t' read -r case_id relative command subject code; do
  case "$case_id" in ''|'#'*) continue ;; esac
  fixture="$negative_root/$relative"
  case "$command" in
    support)
      ;;
    import-gate)
      expect_fail "$case_id" "$code" "$import_gate" --root "$negative_root/$subject"
      ;;
    legacy-final)
      target="$synthetic/$subject"
      mkdir -p "$(dirname "$target")"
      cp "$fixture" "$target"
      expect_fail "$case_id" "$code" env \
        AAT_RESEARCH_LEGACY_SCAN_ROOT="$synthetic" \
        AAT_RESEARCH_LEGACY_FIXTURE_ROOT="$synthetic/.github/lean_quality/fixtures/research_legacy_refs/negative" \
        "$legacy_gate" final
      rm "$target"
      ;;
    legacy-no-new-content)
      expect_fail "$case_id" "$code" env \
        AAT_RESEARCH_LEGACY_DIFF_FILE="$fixture" \
        AAT_RESEARCH_LEGACY_NAME_FILE="$empty_names" \
        "$legacy_gate" no-new ignored-base ignored-head
      ;;
    legacy-no-new-path)
      expect_fail "$case_id" "$code" env \
        AAT_RESEARCH_LEGACY_DIFF_FILE="$empty_diff" \
        AAT_RESEARCH_LEGACY_NAME_FILE="$fixture" \
        "$legacy_gate" no-new ignored-base ignored-head
      ;;
    *)
      echo "unexpected manifest command after validation: $command" >&2
      exit 1
      ;;
  esac
done <"$expectations"

repeated="$synthetic/docs/aat/repeated.md"
mkdir -p "$(dirname "$repeated")"
printf '%s\n%s\n' 'Formal.AG.'"$research_segment" 'Formal.AG.'"$research_segment" >"$repeated"
expect_fail "all legacy locations reported" "E_LEGACY_CONTENT" env \
  AAT_RESEARCH_LEGACY_SCAN_ROOT="$synthetic" \
  AAT_RESEARCH_LEGACY_FIXTURE_ROOT="$synthetic/.github/lean_quality/fixtures/research_legacy_refs/negative" \
  "$legacy_gate" final
if [ "$(grep -c 'docs/aat/repeated.md:' "$tmp/err")" -ne 2 ]; then
  echo "legacy final did not report every repeated location" >&2
  cat "$tmp/err" >&2
  exit 1
fi
rm "$repeated"

duplicate_root="$tmp/duplicate-manifest"
cp -R "$negative_root" "$duplicate_root"
first_row="$(awk -F '\t' '$0 !~ /^#/ { print; exit }' "$expectations")"
printf '%s\n' "$first_row" >>"$duplicate_root/expectations.tsv"
expect_fail "duplicate expectation case" "E_DUPLICATE_CASE_ID" env \
  AAT_RESEARCH_LEGACY_SCAN_ROOT="$synthetic" \
  AAT_RESEARCH_LEGACY_FIXTURE_ROOT="$duplicate_root" \
  "$legacy_gate" final

detached_root="$tmp/detached-manifest"
cp -R "$negative_root" "$detached_root"
printf '%s\n' 'detached support' >"$detached_root/detached.fixture"
printf '%s\n' $'detached-support\tdetached.fixture\tsupport\tdirect\t-' >>"$detached_root/expectations.tsv"
expect_fail "detached support provenance" "E_EXPECTATION_PROVENANCE" env \
  AAT_RESEARCH_LEGACY_SCAN_ROOT="$synthetic" \
  AAT_RESEARCH_LEGACY_FIXTURE_ROOT="$detached_root" \
  "$legacy_gate" final

unregistered="$synthetic/.github/lean_quality/fixtures/research_legacy_refs/negative/unregistered.txt"
printf '%s\n' 'unregistered' >"$unregistered"
expect_fail "unregistered negative fixture" "E_UNREGISTERED_FIXTURE" env \
  AAT_RESEARCH_LEGACY_SCAN_ROOT="$synthetic" \
  AAT_RESEARCH_LEGACY_FIXTURE_ROOT="$synthetic/.github/lean_quality/fixtures/research_legacy_refs/negative" \
  "$legacy_gate" final

echo "Research separation gate fixtures passed."
