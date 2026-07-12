#!/usr/bin/env bash
# One-cent drift demo: base (main) -> head (PR under review) -> repaired.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../../../.." && pwd)"
EXAMPLE="$ROOT/tools/archsig/examples/practical-rust-service"
OUT="$ROOT/.tmp/archsig-practical-rust-service"
ARCHSIG=(cargo run --quiet --manifest-path "$ROOT/tools/archsig/Cargo.toml" --)
SAMPLE="$EXAMPLE/sample/Cargo.toml"

report_value() {
  python3 -c "import json,sys; print(json.load(open(sys.argv[1]))[sys.argv[2]])" "$1" "$2"
}

expect_value() {
  local path="$1"
  local label="$2"
  local field="$3"
  local expected="$4"
  local actual
  actual="$(report_value "$path" "$field")"
  printf '[%s] %s\n' "$label" "$actual"
  if [ "$actual" != "$expected" ]; then
    printf 'expected [%s] %s, got %s\n' "$label" "$expected" "$actual" >&2
    exit 1
  fi
}

echo "=== Act 1: every feature state builds, tests green, demo runs ==="
cargo test --quiet --manifest-path "$SAMPLE"
cargo test --quiet --manifest-path "$SAMPLE" --features psp-compliance
cargo test --quiet --manifest-path "$SAMPLE" --features settlement-authority
echo "--- base (main): totals agree ---"
cargo run --quiet --manifest-path "$SAMPLE"
echo "--- head (PR under review, --features psp-compliance): the drift ---"
cargo run --quiet --manifest-path "$SAMPLE" --features psp-compliance
echo "--- repaired (--features settlement-authority): reconciled ---"
cargo run --quiet --manifest-path "$SAMPLE" --features settlement-authority

echo
echo "=== Act 2: measure base and head ==="
mkdir -p "$OUT"
"${ARCHSIG[@]}" policy-bundle \
  --law-policy "$EXAMPLE/law_policy/law_policy.json" \
  --law-surface "$ROOT/tools/archsig/tests/fixtures/ag_measurement/law_surface_practical_v051.json" \
  --measurement-profile "$EXAMPLE/law_policy/measurement_profile.json" \
  --out "$OUT/policy-bundle.json" >/dev/null
for state in base:archmap.json head:archmap_head.json; do
  name="${state%%:*}"
  archmap="${state##*:}"
  law_surface="$ROOT/tools/archsig/tests/fixtures/ag_measurement/law_surface_practical_v051.json"
  if [ "$name" = "base" ]; then
    law_surface="$ROOT/tools/archsig/tests/fixtures/ag_measurement/law_surface_practical_base_v051.json"
  fi
  mkdir -p "$OUT/$name"
  if [ "$name" = "head" ]; then
    "${ARCHSIG[@]}" analyze \
      --archmap "$EXAMPLE/archmap/$archmap" \
      --policy-bundle "$OUT/policy-bundle.json" \
      --out-dir "$OUT/$name" >/dev/null
  else
    policy="$OUT/$name/law_policy.json"
    jq --arg law_surface_ref "$(jq -r '.id' "$law_surface")" \
      '.lawSurfaceRef = $law_surface_ref' \
      "$EXAMPLE/law_policy/law_policy.json" > "$policy"
    "${ARCHSIG[@]}" analyze \
      --archmap "$EXAMPLE/archmap/$archmap" \
      --law-policy "$policy" \
      --measurement-profile "$EXAMPLE/law_policy/measurement_profile.json" \
      --law-surface "$law_surface" \
      --out-dir "$OUT/$name" >/dev/null
  fi
  if [ "$name" = "base" ]; then
    expect_value "$OUT/$name/archsig-analysis-summary.json" "analyze $name" conclusion "NO_MEASURED_H1_OBSTRUCTION_UNDER_PROFILE"
  else
    expect_value "$OUT/$name/archsig-analysis-summary.json" "analyze $name" conclusion "MEASURED_H1_OBSTRUCTION_UNDER_PROFILE"
  fi
done

echo
echo "=== Act 3: compare and gate the head run ==="
"${ARCHSIG[@]}" compare \
  --base-run "$OUT/base" --head-run "$OUT/head" \
  --out-dir "$OUT/compare-head" >/dev/null
expect_value "$OUT/compare-head/archsig-comparison-report.json" "compare base->head" conclusionCode "RUNS_NOT_COMPARABLE_WITHOUT_COMPARISON_DATA"
# gate exits 1 on BLOCKED (the CI contract); the demo narrates and continues
"${ARCHSIG[@]}" gate \
  --packet "$OUT/head/archsig-measurement-packet.json" \
  --policy "$EXAMPLE/law_policy/gate_policy.json" \
  --comparison "$OUT/compare-head/archsig-comparison-report.json" \
  --out "$OUT/gate-head.json" >/dev/null || true
expect_value "$OUT/gate-head.json" "gate head" decision "BLOCKED_BY_GATE_POLICY"

echo
echo "=== Act 4: measure, compare, and gate the repaired state ==="
mkdir -p "$OUT/repaired"
"${ARCHSIG[@]}" analyze \
  --archmap "$EXAMPLE/archmap/archmap_repaired.json" \
  --policy-bundle "$OUT/policy-bundle.json" \
  --out-dir "$OUT/repaired" >/dev/null
expect_value "$OUT/repaired/archsig-analysis-summary.json" "analyze repaired" conclusion "NO_MEASURED_H1_OBSTRUCTION_UNDER_PROFILE"
"${ARCHSIG[@]}" compare \
  --base-run "$OUT/head" --head-run "$OUT/repaired" \
  --out-dir "$OUT/compare-repaired" >/dev/null
expect_value "$OUT/compare-repaired/archsig-comparison-report.json" "compare head->repaired" conclusionCode "MEASURED_OBSTRUCTION_NO_LONGER_RECORDED_AFTER_CHANGE"
"${ARCHSIG[@]}" gate \
  --packet "$OUT/repaired/archsig-measurement-packet.json" \
  --policy "$EXAMPLE/law_policy/gate_policy.json" \
  --comparison "$OUT/compare-repaired/archsig-comparison-report.json" \
  --out "$OUT/gate-repaired.json" >/dev/null
expect_value "$OUT/gate-repaired.json" "gate repaired" decision "PASS_WITHIN_GATE_POLICY"

echo
echo "ArchSig artifacts: $OUT"
echo "Mismatch support: $OUT/head/archsig-measurement-packet.json (computedInvariants -> classSupport)"
echo "ArchView app: $ROOT/tools/archview/archview.html"
echo "Load viewer data: $OUT/head/archsig-atom-viewer-data.json"
