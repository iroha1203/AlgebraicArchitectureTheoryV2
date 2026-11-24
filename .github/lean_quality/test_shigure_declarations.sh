#!/usr/bin/env bash
set -euo pipefail

mkdir -p .tmp
tmp="$(mktemp -d .tmp/shigure-declarations.XXXXXX)"
trap 'rm -rf -- "$tmp"' EXIT
checker=.github/lean_quality/check_shigure_declarations.lean

cat >"$tmp/Accepted.lean" <<'LEAN'
import Lean.Elab.Tactic
import Mathlib.Tactic.NormNum

/- These words appear in prose: axiom, sorry, admit, unsafe. -/
def literal : String := "unsafe"
def interpolated : String := s!"axiom{(1 : Nat)}"
def sorry! : Nat := 1
def nativeArithmetic (native : Nat) : Nat := 1 + native
set_option debug.skipKernelTC false in
theorem ordinaryDecide : (1 : Nat) = 1 := by decide
theorem rationalNormalizes : (2 / 3 : ℚ) * 3 = 2 := by norm_num
LEAN
lake env lean --run "$checker" "$tmp/Accepted.lean"

cat >"$tmp/Rejected.lean" <<'LEAN'
import Lean.Elab.Tactic

def withHole : String := s! "{(show Nat from sorry)}"
def withDebug : Nat := dbg_trace "{(show Nat from sorry)}"; 0
theorem withNativeConfig : True := by decide (native := id true)
unsafe def testUnsafe : Nat := 42
set_option debug.skipKernelTC true in
theorem kernelCheckDisabled : True := True.intro
LEAN
if lake env lean --run "$checker" "$tmp/Rejected.lean" >"$tmp/diagnostics" 2>&1; then
  echo "SHIGURE declaration checker accepted the rejection fixture" >&2
  exit 1
fi
test "$(grep -c 'disallowed syntax sorry' "$tmp/diagnostics")" -eq 2
grep -Fq 'disallowed syntax unsafe' "$tmp/diagnostics"
grep -Fq 'disallowed syntax debug.skipKernelTC' "$tmp/diagnostics"
grep -Fq 'nonstandard kernel assumption Lean.ofReduceBool' "$tmp/diagnostics"

cat >"$tmp/AnonymousReduction.lean" <<'LEAN'
namespace SHIGURE.AnonymousProof

example := Lean.ofReduceNat
def _example : Nat := 0

end SHIGURE.AnonymousProof
LEAN
if lake env lean --run "$checker" "$tmp/AnonymousReduction.lean" >"$tmp/diagnostics" 2>&1; then
  echo "SHIGURE declaration checker accepted a nonstandard anonymous reduction proof" >&2
  exit 1
fi
grep -Fq 'nonstandard kernel assumption Lean.ofReduceNat' "$tmp/diagnostics"

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
lake env lean --run "$checker" "$tmp/Accepted.lean" "$tmp/ModuleClient.lean"

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

cat >"$tmp/CompiledAccepted.lean" <<'LEAN'
theorem checkedTogether : True := True.intro
LEAN
cat >"$tmp/CompiledRejected.lean" <<'LEAN'
private axiom nonstandard : False
theorem compiledDependency : False := nonstandard
LEAN
lake env bash -e -c '
  cd "$1"
  export LEAN_PATH="$LEAN_PATH:$PWD"
  lean -o CompiledAccepted.olean CompiledAccepted.lean
  lean -o CompiledRejected.olean CompiledRejected.lean
  lean --run "$2" --compiled CompiledAccepted.lean
  if lean --run "$2" --compiled CompiledAccepted.lean CompiledRejected.lean > diagnostics 2>&1; then
    echo "SHIGURE compiled declaration checker accepted a nonstandard assumption" >&2
    exit 1
  fi
  grep -Eq "nonstandard kernel assumption .*CompiledRejected.*nonstandard" diagnostics
' bash "$tmp" "$PWD/$checker"

cat >"$tmp/AdjacentExit.lean" <<'LEAN'
theorem beforeExit : True := True.intro#exit
LEAN
if lake env lean --run "$checker" "$tmp/AdjacentExit.lean" >"$tmp/diagnostics" 2>&1; then
  echo "SHIGURE declaration checker accepted an adjacent early exit" >&2
  exit 1
fi
grep -Fq 'the Lean frontend did not reach the end of the file' "$tmp/diagnostics"

lake env lean --run "$checker" --select-source-checks \
  "$tmp/CompiledAccepted.lean" "$tmp/Rejected.lean" "$tmp/Anonymous.lean" \
  "$tmp/AnonymousReduction.lean" "$audit_fixture" "$tmp/AdjacentExit.lean" |
  tr '\0' '\n' >"$tmp/selected"
printf '%s\n' "$tmp/Rejected.lean" "$tmp/Anonymous.lean" \
  "$tmp/AnonymousReduction.lean" "$audit_fixture" "$tmp/AdjacentExit.lean" | diff -u - "$tmp/selected"

echo "SHIGURE declaration checker fixtures passed."
