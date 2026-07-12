#!/usr/bin/env bash
set -euo pipefail

repo_root="$(git rev-parse --show-toplevel)"
checker="$repo_root/.github/lean_quality/check_grounded_packet_bridge_audit.sh"
fixture_root="$repo_root/.github/lean_quality/fixtures/grounded_packet_bridge"
expectations="$fixture_root/negative/expectations.tsv"
semantic_source_rel=".github/lean_quality/fixtures/grounded_packet_bridge/semantic/ResearchLean/AG/Tools/GroundedPacketBridgeSemanticFixture.lean"
semantic_source="$repo_root/$semantic_source_rel"
semantic_module="ResearchLean.AG.Tools.GroundedPacketBridgeSemanticFixture"
signature_source="$fixture_root/signature/GroundedPacketBridgeOriginalTypeAudit.lean"
package_root="$repo_root/research/lean"
semantic_compile_source="$package_root/.tmp/GroundedPacketBridgeSemanticFixture.lean"
signature_compile_source="$package_root/.tmp/GroundedPacketBridgeOriginalTypeAudit.lean"
source_manifest="$repo_root/.github/lean_quality/grounded_packet_bridge_sources.sha256"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"; rm -f "$semantic_compile_source" "$signature_compile_source"' EXIT

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

expect_pass "matching selected declarations" "$checker" \
  "$fixture_root/positive/contract.tsv" "$fixture_root/positive/audit.tsv"

(cd "$repo_root" && shasum -a 256 -c "$source_manifest")

cp "$signature_source" "$signature_compile_source"
(cd "$package_root" && lake env lean "$signature_compile_source") |
  awk -F '\t' '$1 == "MIGRATION_DECL"' >"$tmp/original-type.audit.tsv"
"$package_root/emit_migration_audit.sh" \
  ResearchLean.AG.QualitySurface.SemanticRepairLawEquationGroundedPacketBridge \
  ResearchLean/AG/QualitySurface/SemanticRepairLawEquationGroundedPacketBridge.lean \
  "$tmp/bridge.audit.tsv"
"$package_root/emit_migration_audit.sh" \
  ResearchLean.AG.QualitySurface.SemanticRepairLawEquationGroundedPacketExactBridge \
  ResearchLean/AG/QualitySurface/SemanticRepairLawEquationGroundedPacketExactBridge.lean \
  "$tmp/exact.audit.tsv"
expect_pass "production exact bridge contracts" "$checker" \
  "$repo_root/.github/lean_quality/grounded_packet_bridge_contract.tsv" \
  "$tmp/bridge.audit.tsv" "$tmp/exact.audit.tsv" "$tmp/original-type.audit.tsv"

mkdir -p "$package_root/.lake/build/lib/lean/ResearchLean/AG/Tools"
mkdir -p "$package_root/.tmp"
cp "$semantic_source" "$semantic_compile_source"
(cd "$package_root" && lake env lean \
  -o ".lake/build/lib/lean/ResearchLean/AG/Tools/GroundedPacketBridgeSemanticFixture.olean" \
  "$semantic_compile_source")
"$package_root/emit_migration_audit.sh" \
  "$semantic_module" "$semantic_source_rel" "$tmp/semantic.audit.tsv"

while IFS=$'\t' read -r case_id contract code; do
  case "$case_id" in ''|'#'*) continue ;; esac
  expect_fail "$case_id" "$code" "$checker" \
    "$fixture_root/negative/$contract" "$tmp/semantic.audit.tsv"
done <"$expectations"

echo "Grounded packet bridge semantic negative audit fixtures passed."
