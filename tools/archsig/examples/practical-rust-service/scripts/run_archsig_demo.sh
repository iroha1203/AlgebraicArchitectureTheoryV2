#!/usr/bin/env bash
# One-cent drift demo: base (main) -> head (PR under review) -> repaired.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../../../.." && pwd)"
EXAMPLE="$ROOT/tools/archsig/examples/practical-rust-service"
OUT="$ROOT/.tmp/archsig-practical-rust-service"
ARCHSIG=(cargo run --quiet --manifest-path "$ROOT/tools/archsig/Cargo.toml" --)
SAMPLE="$EXAMPLE/sample/Cargo.toml"

conclusion() {
  python3 -c "import json,sys; print(json.load(open(sys.argv[1]))[sys.argv[2]])" "$1" "$3" \
    | sed "s/^/[$2] /"
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
for state in base:archmap.json head:archmap_head.json; do
  name="${state%%:*}"
  archmap="${state##*:}"
  "${ARCHSIG[@]}" analyze \
    --archmap "$EXAMPLE/archmap/$archmap" \
    --law-policy "$EXAMPLE/law_policy/law_policy.json" \
    --measurement-profile "$EXAMPLE/law_policy/measurement_profile.json" \
    --out-dir "$OUT/$name" >/dev/null
  conclusion "$OUT/$name/archsig-analysis-summary.json" "analyze $name" conclusion
done

echo
echo "=== Act 3: compare and gate the head run ==="
"${ARCHSIG[@]}" compare \
  --base-run "$OUT/base" --head-run "$OUT/head" \
  --out-dir "$OUT/compare-head" >/dev/null
conclusion "$OUT/compare-head/archsig-comparison-report.json" "compare base->head" conclusionCode
# gate exits 1 on BLOCKED (the CI contract); the demo narrates and continues
"${ARCHSIG[@]}" gate \
  --packet "$OUT/head/archsig-measurement-packet.json" \
  --policy "$EXAMPLE/law_policy/gate_policy.json" \
  --comparison "$OUT/compare-head/archsig-comparison-report.json" \
  --out "$OUT/gate-head.json" >/dev/null || true
conclusion "$OUT/gate-head.json" "gate head" decision

echo
echo "=== Act 4: measure, compare, and gate the repaired state ==="
"${ARCHSIG[@]}" analyze \
  --archmap "$EXAMPLE/archmap/archmap_repaired.json" \
  --law-policy "$EXAMPLE/law_policy/law_policy.json" \
  --measurement-profile "$EXAMPLE/law_policy/measurement_profile.json" \
  --out-dir "$OUT/repaired" >/dev/null
conclusion "$OUT/repaired/archsig-analysis-summary.json" "analyze repaired" conclusion
"${ARCHSIG[@]}" compare \
  --base-run "$OUT/head" --head-run "$OUT/repaired" \
  --out-dir "$OUT/compare-repaired" >/dev/null
conclusion "$OUT/compare-repaired/archsig-comparison-report.json" "compare head->repaired" conclusionCode
"${ARCHSIG[@]}" gate \
  --packet "$OUT/repaired/archsig-measurement-packet.json" \
  --policy "$EXAMPLE/law_policy/gate_policy.json" \
  --comparison "$OUT/compare-repaired/archsig-comparison-report.json" \
  --out "$OUT/gate-repaired.json" >/dev/null
conclusion "$OUT/gate-repaired.json" "gate repaired" decision

echo
echo "ArchSig artifacts: $OUT"
echo "Mismatch support: $OUT/head/archsig-measurement-packet.json (computedInvariants -> classSupport)"
echo "ArchView app: $ROOT/tools/archview/archview.html"
echo "Load viewer data: $OUT/head/archsig-atom-viewer-data.json"
