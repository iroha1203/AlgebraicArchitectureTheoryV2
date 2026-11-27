#!/usr/bin/env bash
set -euo pipefail

mkdir -p .tmp
tmp="$(mktemp -d .tmp/shigure-declarations.XXXXXX)"
trap 'rm -rf -- "$tmp"' EXIT
checker="${SHIGURE_CHECKER_SCRIPT:-.github/lean_quality/check_shigure_declarations.lean}"
case "$checker" in
  /*) checker_abs="$checker" ;;
  *) checker_abs="$PWD/$checker" ;;
esac
checker_dir="${SHIGURE_CHECKER_DIR:-}"
run_checker() {
  if [[ -n "$checker_dir" ]]; then
    lake env bash -e -c 'export LEAN_PATH="$1:$LEAN_PATH"; shift; exec lean --run "$@"' \
      bash "$checker_dir" "$checker_abs" "$@"
  else
    lake env lean --run "$checker_abs" "$@"
  fi
}

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
run_checker "$tmp/Accepted.lean"

cat >"$tmp/Rejected.lean" <<'LEAN'
import Lean.Elab.Tactic

def withHole : String := s! "{(show Nat from sorry)}"
def withDebug : Nat := dbg_trace "{(show Nat from sorry)}"; 0
theorem withNativeConfig : True := by decide (native := id true)
unsafe def testUnsafe : Nat := 42
set_option debug.skipKernelTC true in
theorem kernelCheckDisabled : True := True.intro
LEAN
if run_checker "$tmp/Rejected.lean" >"$tmp/diagnostics" 2>&1; then
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
if run_checker "$tmp/AnonymousReduction.lean" >"$tmp/diagnostics" 2>&1; then
  echo "SHIGURE declaration checker accepted a nonstandard anonymous reduction proof" >&2
  exit 1
fi
grep -Fq 'nonstandard kernel assumption Lean.ofReduceNat' "$tmp/diagnostics"

cat >"$tmp/Anonymous.lean" <<'LEAN'
import Lean.Elab.Tactic

example : True := by decide
example : True := by decide (native := id true)
LEAN
if run_checker "$tmp/Anonymous.lean" >"$tmp/diagnostics" 2>&1; then
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
run_checker "$tmp/Accepted.lean" "$tmp/ModuleClient.lean"

mkdir -p "$tmp/Formal/SHIGURE"
audit_fixture="$tmp/Formal/SHIGURE/AxiomAudit.lean"
check_audit_fixture() {
  lake env bash -c '
    if [[ -n "$3" ]]; then export LEAN_PATH="$3:$LEAN_PATH"; fi
    cd "$1"
    lean --run "$2" Formal/SHIGURE/AxiomAudit.lean
  ' bash "$tmp" "$checker_abs" "$checker_dir"
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
module
import Lean.Elab.Tactic
private theorem compiledDependency : True := by decide (native := id true)
LEAN
lake env bash -e -c '
  if [[ -n "$3" ]]; then export LEAN_PATH="$3:$LEAN_PATH"; fi
  cd "$1"
  export LEAN_PATH="$LEAN_PATH:$PWD"
  lean -o CompiledAccepted.olean CompiledAccepted.lean
  lean -o CompiledRejected.olean CompiledRejected.lean
  test -f CompiledRejected.olean.private
  lean --run "$2" --compiled --separate-out separate.nul CompiledAccepted.lean
  test ! -s separate.nul
  lean --run "$2" --compiled-isolated CompiledAccepted.lean
  if lean --run "$2" --compiled --separate-out separate-rej.nul CompiledAccepted.lean CompiledRejected.lean > diagnostics 2>&1; then
    echo "SHIGURE compiled declaration checker accepted a nonstandard assumption" >&2
    exit 1
  fi
  grep -Fq "nonstandard kernel assumption Lean.ofReduceBool" diagnostics
  if lean --run "$2" --compiled-isolated CompiledRejected.lean > diagnostics-iso 2>&1; then
    echo "SHIGURE isolated compiled checker accepted a nonstandard assumption" >&2
    exit 1
  fi
  grep -Fq "nonstandard kernel assumption Lean.ofReduceBool" diagnostics-iso
' bash "$tmp" "$checker_abs" "$checker_dir"

cat >"$tmp/AdjacentExit.lean" <<'LEAN'
theorem beforeExit : True := True.intro#exit
LEAN
if run_checker "$tmp/AdjacentExit.lean" >"$tmp/diagnostics" 2>&1; then
  echo "SHIGURE declaration checker accepted an adjacent early exit" >&2
  exit 1
fi
grep -Fq 'the Lean frontend did not reach the end of the file' "$tmp/diagnostics"

# Verify cache manifest pruning, reuse, and tamper detection.
python3 - "$tmp/cache-test" "$PWD/.github/lean_quality/shigure_cache_manifest.py" <<'PY'
import os, subprocess, sys
from pathlib import Path

root = Path(sys.argv[1]).resolve()
script = Path(sys.argv[2]).resolve()
src_dir = root / "Formal" / "SHIGURE"
build_root = root / ".lake" / "build" / "lib" / "lean"
stamps = root / "stamps"
manifest = root / "verified-manifest.tsv"
new_manifest = root / "new-manifest.tsv"
source_checks = root / "source-checks.nul"
files_nul = root / "shigure-files"

src_dir.mkdir(parents=True)
(build_root / "Formal" / "SHIGURE").mkdir(parents=True)
stamps.mkdir(parents=True)

(src_dir / "ModA.lean").write_text("theorem a : True := True.intro\n")
(src_dir / "ModB.lean").write_text("#guard_msgs in\ntheorem b : True := True.intro\n")
(src_dir / "AxiomAudit.lean").write_text("-- audit\n")
for mod in ("ModA", "ModB"):
    (build_root / "Formal" / "SHIGURE" / f"{mod}.olean").write_bytes(f"olean-{mod}".encode())
    (build_root / "Formal" / "SHIGURE" / f"{mod}.trace").write_bytes(f"trace-{mod}".encode())
(build_root / "Formal" / "SHIGURE" / "DeletedMod.olean").write_bytes(b"stale")
(stamps / "Formal.SHIGURE.ModA").write_text("checked")
(stamps / "Formal.SHIGURE.ModB").write_text("frontend")

files_nul.write_bytes(
    b"Formal/SHIGURE/ModA.lean\x00Formal/SHIGURE/ModB.lean\x00Formal/SHIGURE/AxiomAudit.lean\x00"
)

def run(*args, expect_ok=True):
    res = subprocess.run([sys.executable, str(script), *args], cwd=root, capture_output=True, text=True)
    if expect_ok and res.returncode != 0:
        raise AssertionError(f"command failed: {args}\n{res.stdout}\n{res.stderr}")
    if not expect_ok and res.returncode == 0:
        raise AssertionError(f"command unexpectedly succeeded: {args}\n{res.stdout}")
    return res

# 1. Verify fresh stamps -> writes manifest & selects ModB + AxiomAudit for frontend checks.
run("verify", "--files", str(files_nul), "--manifest", str(manifest), "--stamps", str(stamps),
    "--build-root", str(build_root), "--new-manifest", str(new_manifest), "--source-checks-out", str(source_checks))
manifest.write_bytes(new_manifest.read_bytes())
selected = [c.decode() for c in source_checks.read_bytes().split(b"\x00") if c]
assert set(selected) == {"Formal/SHIGURE/ModB.lean", "Formal/SHIGURE/AxiomAudit.lean"}, selected

# 2. Prune keeps valid cached modules and deletes stale DeletedMod.olean.
run("prune", "--files", str(files_nul), "--manifest", str(manifest), "--build-root", str(build_root))
assert (build_root / "Formal" / "SHIGURE" / "ModA.olean").is_file()
assert not (build_root / "Formal" / "SHIGURE" / "DeletedMod.olean").exists()

# 3. With empty fresh stamps, unchanged cached modules reuse verified manifest.
for p in stamps.iterdir():
    p.unlink()
run("verify", "--files", str(files_nul), "--manifest", str(manifest), "--stamps", str(stamps),
    "--build-root", str(build_root), "--new-manifest", str(new_manifest), "--source-checks-out", str(source_checks))
selected = [c.decode() for c in source_checks.read_bytes().split(b"\x00") if c]
assert set(selected) == {"Formal/SHIGURE/ModB.lean", "Formal/SHIGURE/AxiomAudit.lean"}, selected

# 4. Modified trace (e.g. rebuild with early #exit) without fresh stamp is rejected.
(build_root / "Formal" / "SHIGURE" / "ModA.trace").write_bytes(b"trace-changed")
res = run("verify", "--files", str(files_nul), "--manifest", str(manifest), "--stamps", str(stamps),
          "--build-root", str(build_root), "--new-manifest", str(new_manifest), "--source-checks-out", str(source_checks),
          expect_ok=False)
assert "did not reach the end of the file" in res.stderr, res.stderr

# 5. Prune removes artifacts for modules whose source/trace changed.
run("prune", "--files", str(files_nul), "--manifest", str(manifest), "--build-root", str(build_root))
assert not (build_root / "Formal" / "SHIGURE" / "ModA.olean").exists()
assert (build_root / "Formal" / "SHIGURE" / "ModB.olean").is_file()
PY

if [[ $# -eq 1 ]]; then
  case "$1" in
    /*) plugin_abs="$1" ;;
    *) plugin_abs="$PWD/$1" ;;
  esac
  cat >"$tmp/Formal/SHIGURE/MacroSource.lean" <<'LEAN'
import Lean.Elab.Tactic
macro "temporary_proof" : command => `(example := Lean.ofReduceNat)
LEAN
  cat >"$tmp/Formal/SHIGURE/MacroClient.lean" <<'LEAN'
import Formal.SHIGURE.MacroSource
temporary_proof
LEAN
  cat >"$tmp/Formal/SHIGURE/RunCommand.lean" <<'LEAN'
import Lean.Elab.Tactic
run_cmd do
  let _proof : True := by decide (native := id true)
  pure ()
LEAN
  cp "$tmp/AdjacentExit.lean" "$tmp/Formal/SHIGURE/AdjacentExit.lean"
  cp "$tmp/Rejected.lean" "$tmp/Formal/SHIGURE/RejectedSyntax.lean"
  cat >"$tmp/Formal/SHIGURE/Guarded.lean" <<'LEAN'
#guard_msgs in
theorem succeeds : True := True.intro
LEAN
  lake env bash -e -c '
    cd "$1"
    export LEAN_PATH="$PWD:$LEAN_PATH"
    export SHIGURE_AUDIT_STAMPS="$PWD/stamps"
    mkdir -p "$SHIGURE_AUDIT_STAMPS"
    lean --plugin="$2" -o Formal/SHIGURE/MacroSource.olean Formal/SHIGURE/MacroSource.lean
    test "$(cat stamps/Formal.SHIGURE.MacroSource)" = checked
    lean --plugin="$2" Formal/SHIGURE/Guarded.lean
    test "$(cat stamps/Formal.SHIGURE.Guarded)" = frontend
    if lean --plugin="$2" Formal/SHIGURE/RejectedSyntax.lean > syntax.log 2>&1; then
      echo "SHIGURE build audit accepted prohibited syntax" >&2
      exit 1
    fi
    test "$(grep -c "disallowed syntax sorry" syntax.log)" -eq 2
    grep -Fq "disallowed syntax unsafe" syntax.log
    grep -Fq "disallowed syntax debug.skipKernelTC" syntax.log
    if lean --plugin="$2" Formal/SHIGURE/MacroClient.lean > macro.log 2>&1; then
      echo "SHIGURE build audit accepted a nonstandard proof from an imported macro" >&2
      exit 1
    fi
    grep -Fq "nonstandard kernel assumption Lean.ofReduceNat" macro.log
    if lean --plugin="$2" Formal/SHIGURE/RunCommand.lean > command.log 2>&1; then
      echo "SHIGURE build audit accepted a nonstandard proof in run_cmd" >&2
      exit 1
    fi
    grep -Fq "nonstandard kernel assumption Lean.ofReduceBool" command.log
    lean --plugin="$2" Formal/SHIGURE/AdjacentExit.lean > exit.log 2>&1
    test ! -e stamps/Formal.SHIGURE.AdjacentExit
  ' bash "$tmp" "$plugin_abs"
fi

echo "SHIGURE declaration checker fixtures passed."
