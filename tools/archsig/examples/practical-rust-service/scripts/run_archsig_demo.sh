#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../../../.." && pwd)"
EXAMPLE="$ROOT/tools/archsig/examples/practical-rust-service"
OUT="$ROOT/.tmp/archsig-practical-rust-service"

cargo test --manifest-path "$EXAMPLE/sample/Cargo.toml"
cargo run --manifest-path "$EXAMPLE/sample/Cargo.toml"
cargo run --manifest-path "$ROOT/tools/archsig/Cargo.toml" -- analyze \
  --archmap "$EXAMPLE/archmap/archmap.json" \
  --law-policy "$EXAMPLE/law_policy/law_policy.json" \
  --measurement-profile "$EXAMPLE/law_policy/measurement_profile.json" \
  --out-dir "$OUT"

echo "ArchSig artifacts: $OUT"
echo "ArchView app: $ROOT/tools/archview/archview.html"
echo "Load viewer data: $OUT/archsig-atom-viewer-data.json"
