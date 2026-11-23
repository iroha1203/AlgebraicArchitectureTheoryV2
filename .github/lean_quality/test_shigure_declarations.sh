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

cat >"$tmp/Anonymous.lean" <<'LEAN'
import Lean.Elab.Tactic

example : True := by decide
example : True := by decide (native := id true)
LEAN
if lake env lean --run "$checker" "$tmp/Anonymous.lean" >"$tmp/diagnostics" 2>&1; then
  echo "SHIGURE declaration checker accepted a nonstandard anonymous proof" >&2
  exit 1
fi
grep -Fq 'nonstandard kernel assumption Lean.ofReduceBool' "$tmp/diagnostics"

cat >"$tmp/ModuleClient.lean" <<'LEAN'
module

import Formal.SHIGURE.AssertStandardAxioms

namespace SHIGURE.ModuleClient

theorem nat_add_comm (n m : Nat) : n + m = m + n := Nat.add_comm n m

end SHIGURE.ModuleClient

#shigure_assert_standard_axioms_only SHIGURE.ModuleClient
LEAN
lake env lean --run "$checker" "$tmp/ModuleClient.lean"

mkdir -p "$tmp/Formal/SHIGURE"
audit_fixture="$tmp/Formal/SHIGURE/AxiomAudit.lean"
check_audit_fixture() {
  lake env bash -c 'cd "$1"; lean --run "$2" Formal/SHIGURE/AxiomAudit.lean' \
    bash "$tmp" "$PWD/$checker"
}

cat >"$audit_fixture" <<'LEAN'
import Formal.SHIGURE.AssertStandardAxioms
#exit
#shigure_assert_standard_axioms_only SHIGURE.AxiomAudit
LEAN
if check_audit_fixture >"$tmp/diagnostics" 2>&1; then
  echo "SHIGURE declaration checker accepted an early exit" >&2
  exit 1
fi
grep -Fq 'the Lean frontend did not reach the end of the file' "$tmp/diagnostics"

cat >"$audit_fixture" <<'LEAN'
import Formal.SHIGURE.AssertStandardAxioms
#guard_msgs (drop error) in
#shigure_assert_standard_axioms_only SHIGURE.AxiomAudit
LEAN
if check_audit_fixture >"$tmp/diagnostics" 2>&1; then
  echo "SHIGURE declaration checker accepted a guarded audit" >&2
  exit 1
fi
grep -Fq 'the final command must run the SHIGURE audit at top level' "$tmp/diagnostics"

echo "SHIGURE declaration checker fixtures passed."
