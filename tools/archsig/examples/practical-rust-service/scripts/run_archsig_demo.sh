#!/usr/bin/env bash
# One-cent drift demo: base (main) -> head (PR under review) -> repaired,
# measured through the full SAGA diagnostic staircase
# (grounding -> descent -> comparison -> gate, with harmonic debt on the side).
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../../../.." && pwd)"
EXAMPLE="$ROOT/tools/archsig/examples/practical-rust-service"
OUT="$ROOT/.tmp/archsig-practical-rust-service"
ARCHSIG=(cargo run --quiet --manifest-path "$ROOT/tools/archsig/Cargo.toml" --)
SAMPLE="$EXAMPLE/sample/Cargo.toml"

report_value() {
  python3 -c "import json,sys; print(json.load(open(sys.argv[1]))[sys.argv[2]])" "$1" "$2"
}

saga_verdict() {
  python3 -c "
import json, sys
packet = json.load(open(sys.argv[1]))
row = next(row for row in packet['structuralVerdict'] if row['law'] == sys.argv[2])
print(row['verdict'])" "$1" "$2"
}

invariant_value() {
  python3 -c "
import json, sys
packet = json.load(open(sys.argv[1]))
row = next(row for row in packet['computedInvariants'] if row['invariantId'] == sys.argv[2])
value = row
for key in sys.argv[3].split('.'):
    value = value[key]
print(value)" "$1" "$2" "$3"
}

expect() {
  local label="$1"
  local actual="$2"
  local expected="$3"
  printf '[%s] %s\n' "$label" "$actual"
  if [ "$actual" != "$expected" ]; then
    printf 'expected [%s] %s, got %s\n' "$label" "$expected" "$actual" >&2
    exit 1
  fi
}

expect_value() {
  expect "$2" "$(report_value "$1" "$3")" "$4"
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
echo "=== Act 2: measure base — same questions, SAGA data not yet supplied ==="
mkdir -p "$OUT/base"
base_policy="$OUT/base/law_policy.json"
jq --arg ref "$(jq -r '.id' "$EXAMPLE/law_policy/law_surface_base.json")" \
  '.lawSurfaceRef = $ref' \
  "$EXAMPLE/law_policy/law_policy.json" > "$base_policy"
"${ARCHSIG[@]}" analyze \
  --archmap "$EXAMPLE/archmap/archmap.json" \
  --law-policy "$base_policy" \
  --measurement-profile "$EXAMPLE/law_policy/measurement_profile.json" \
  --measurement-profile "$EXAMPLE/law_policy/measurement_profile_drift.json" \
  --law-surface "$EXAMPLE/law_policy/law_surface_base.json" \
  --out-dir "$OUT/base" >/dev/null
expect_value "$OUT/base/archsig-analysis-summary.json" "analyze base" conclusion "NO_MEASURED_H1_OBSTRUCTION_UNDER_PROFILE"
expect "saga base" "$(saga_verdict "$OUT/base/archsig-measurement-packet.json" "law:money-repair-descent")" "not_computed"
echo "    (no RepairPlan supplied: every SAGA stage stays typed silence_by_design)"

echo
echo "=== Act 3: measure head — the full SAGA staircase fires ==="
mkdir -p "$OUT/head"
"${ARCHSIG[@]}" analyze \
  --archmap "$EXAMPLE/archmap/archmap_head.json" \
  --law-policy "$EXAMPLE/law_policy/law_policy.json" \
  --measurement-profile "$EXAMPLE/law_policy/measurement_profile.json" \
  --measurement-profile "$EXAMPLE/law_policy/measurement_profile_drift.json" \
  --law-surface "$EXAMPLE/law_policy/law_surface.json" \
  --repair-plan "$EXAMPLE/saga/repair_plan_head.json" \
  --out-dir "$OUT/head" >/dev/null
head_packet="$OUT/head/archsig-measurement-packet.json"
expect "grounding head" "$(saga_verdict "$head_packet" "law:money-convention")" "measured_zero"
echo "    (every chart satisfies its own displayed money law — that is the trap)"
expect "descent head" "$(saga_verdict "$head_packet" "saga.residual-class")" "measured_nonzero"
expect "comparison head" "$(invariant_value "$head_packet" "saga-comparison:h1-transfer" "status")" "established"
expect "harmonic debt head" "$(invariant_value "$head_packet" "harmonic-debt:profile:money-drift@1" "essentialRepairLowerBound")" "0.353553"
expect_value "$OUT/head/archsig-analysis-summary.json" "analyze head" conclusion "MEASURED_NONGLUING_RESIDUAL_CLASS"

echo
echo "=== Act 4: compare and gate the head run ==="
"${ARCHSIG[@]}" compare \
  --base-run "$OUT/base" --head-run "$OUT/head" \
  --out-dir "$OUT/compare-head" >/dev/null
expect_value "$OUT/compare-head/archsig-comparison-report.json" "compare base->head" conclusionCode "RUNS_NOT_COMPARABLE_WITHOUT_COMPARISON_DATA"
# gate exits 1 on BLOCKED (the CI contract); the demo narrates and continues
"${ARCHSIG[@]}" gate \
  --packet "$head_packet" \
  --policy "$EXAMPLE/law_policy/gate_policy.json" \
  --comparison "$OUT/compare-head/archsig-comparison-report.json" \
  --out "$OUT/gate-head.json" >/dev/null || true
expect_value "$OUT/gate-head.json" "gate head" decision "BLOCKED_BY_GATE_POLICY"

echo
echo "=== Act 5: measure, compare, and gate the repaired state ==="
mkdir -p "$OUT/repaired"
"${ARCHSIG[@]}" analyze \
  --archmap "$EXAMPLE/archmap/archmap_repaired.json" \
  --law-policy "$EXAMPLE/law_policy/law_policy.json" \
  --measurement-profile "$EXAMPLE/law_policy/measurement_profile.json" \
  --measurement-profile "$EXAMPLE/law_policy/measurement_profile_drift.json" \
  --law-surface "$EXAMPLE/law_policy/law_surface.json" \
  --repair-plan "$EXAMPLE/saga/repair_plan_repaired.json" \
  --out-dir "$OUT/repaired" >/dev/null
repaired_packet="$OUT/repaired/archsig-measurement-packet.json"
expect "descent repaired" "$(saga_verdict "$repaired_packet" "saga.global-coherence")" "measured_zero"
expect "harmonic debt repaired" "$(invariant_value "$repaired_packet" "harmonic-debt:profile:money-drift@1" "essentialRepairLowerBound")" "0.0"
expect_value "$OUT/repaired/archsig-analysis-summary.json" "analyze repaired" conclusion "REPAIR_GLUES_WITHIN_SELECTED_COMPLEX"
"${ARCHSIG[@]}" compare \
  --base-run "$OUT/head" --head-run "$OUT/repaired" \
  --out-dir "$OUT/compare-repaired" >/dev/null
expect_value "$OUT/compare-repaired/archsig-comparison-report.json" "compare head->repaired" conclusionCode "MEASURED_OBSTRUCTION_NO_LONGER_RECORDED_AFTER_CHANGE"
"${ARCHSIG[@]}" gate \
  --packet "$repaired_packet" \
  --policy "$EXAMPLE/law_policy/gate_policy.json" \
  --comparison "$OUT/compare-repaired/archsig-comparison-report.json" \
  --out "$OUT/gate-repaired.json" >/dev/null
expect_value "$OUT/gate-repaired.json" "gate repaired" decision "PASS_WITHIN_GATE_POLICY"

echo
echo "ArchSig artifacts: $OUT"
echo "Residual class support: $OUT/head/archsig-measurement-packet.json (computedInvariants -> saga-descent:residual-class)"
echo "SAGA staircase (viewer): $OUT/head/archsig-atom-viewer-data.json (sagaDescent.stages)"
echo "ArchView app: $ROOT/tools/archview/archview.html"
