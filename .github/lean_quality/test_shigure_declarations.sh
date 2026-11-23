#!/usr/bin/env bash
set -euo pipefail

mkdir -p .tmp
tmp="$(mktemp -d .tmp/shigure-declarations.XXXXXX)"
trap 'rm -rf -- "$tmp"' EXIT
checker=.github/lean_quality/check_shigure_declarations.lean

cat >"$tmp/Accepted.lean" <<'LEAN'
import Lean.Elab.Tactic

/- These words appear in prose: axiom, sorry, admit, unsafe. -/
def literal : String := "unsafe"
def interpolated : String := s!"axiom{(1 : Nat)}"
def sorry! : Nat := 1
def nativeArithmetic (native : Nat) : Nat := 1 + native
theorem ordinaryDecide : (1 : Nat) = 1 := by decide
LEAN
lake env lean --run "$checker" "$tmp/Accepted.lean"

cat >"$tmp/Rejected.lean" <<'LEAN'
import Lean.Elab.Tactic

def withHole : String := s! "{(show Nat from sorry)}"
def withDebug : Nat := dbg_trace "{(show Nat from sorry)}"; 0
theorem withNativeConfig : True := by decide (native := id true)
unsafe def testUnsafe : Nat := 42
LEAN
if lake env lean --run "$checker" "$tmp/Rejected.lean" >"$tmp/diagnostics" 2>&1; then
  echo "SHIGURE declaration checker accepted the rejection fixture" >&2
  exit 1
fi
test "$(grep -c 'disallowed syntax sorry' "$tmp/diagnostics")" -eq 2
grep -Fq 'disallowed syntax unsafe' "$tmp/diagnostics"
grep -Fq 'nonstandard kernel assumption Lean.ofReduceBool' "$tmp/diagnostics"
echo "SHIGURE declaration checker fixtures passed."
