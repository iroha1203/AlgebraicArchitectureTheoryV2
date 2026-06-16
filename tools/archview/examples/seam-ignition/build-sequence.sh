#!/usr/bin/env bash
# Build the Seam Ignition demo: measure each frame ArchMap with ArchSig, into an ordered
# packet sequence ArchView plays. Each frame is one real `archsig analyze` run — ArchView
# fabricates no measurement; it only plays the emitted per-frame verdicts over time.
#
# Usage:  tools/archview/examples/seam-ignition/build-sequence.sh [OUT_DIR]
#   OUT_DIR defaults to .tmp/archview-seq
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "$HERE/../../../.." && pwd)"
OUT="${1:-$ROOT/.tmp/archview-seq}"

rm -rf "$OUT"; mkdir -p "$OUT"
for f in 00 01 02; do
  cargo run -q --manifest-path "$ROOT/tools/archsig/Cargo.toml" -- analyze \
    --archmap   "$HERE/frame-$f.archmap.json" \
    --law-policy "$HERE/law_policy.json" \
    --out-dir   "$OUT/frame-$f"
done

# the viewer + the manifest sit at the sequence root, next to the frame-NN/ packet dirs
cp "$HERE/archview-sequence.json" "$OUT/archview-sequence.json"
cp "$ROOT/tools/archview/archview.html" "$OUT/archview.html"

echo "Built sequence in $OUT"
echo "Serve and open:  python3 -m http.server 8000 --directory $OUT  ->  http://localhost:8000/archview.html"
for f in 00 01 02; do
  printf "  frame-%s: " "$f"
  python3 -c "import json,sys;print(json.load(open('$OUT/frame-$f/archsig-atom-viewer-data.json'))['decisionBar']['conclusion'])"
done
