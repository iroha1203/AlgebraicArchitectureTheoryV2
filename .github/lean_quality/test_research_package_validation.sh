#!/usr/bin/env bash
set -euo pipefail

repo_root="$(git rev-parse --show-toplevel)"
selector="$repo_root/.github/lean_quality/select_research_package_validation.sh"
workflow="$repo_root/.github/workflows/lean.yml"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

assert_selection() {
  local base="$1"
  local head="$2"
  local expected="$3"
  : >"$tmp/output"
  (
    cd "$tmp/repo"
    EVENT_NAME=pull_request \
      PR_BASE="$base" \
      PUSH_BASE=unused \
      HEAD_SHA="$head" \
      GITHUB_OUTPUT="$tmp/output" \
      "$selector"
  )
  test "$(cat "$tmp/output")" = "run=$expected"
}

assert_workflow_dispatch() {
  : >"$tmp/output"
  (
    cd "$tmp/repo"
    EVENT_NAME=workflow_dispatch \
      GITHUB_OUTPUT="$tmp/output" \
      "$selector"
  )
  test "$(cat "$tmp/output")" = "run=true"
}

mkdir -p "$tmp/repo"
git -C "$tmp/repo" init -q
git -C "$tmp/repo" config user.email 'research-validation-test@example.invalid'
git -C "$tmp/repo" config user.name 'research validation test'
touch "$tmp/repo/README.md"
git -C "$tmp/repo" add README.md
git -C "$tmp/repo" commit -q -m 'base'
base="$(git -C "$tmp/repo" rev-parse HEAD)"

mkdir -p "$tmp/repo/research/lean/ResearchLean/AG"
touch "$tmp/repo/research/lean/ResearchLean/AG/Fixture.lean"
git -C "$tmp/repo" add research/lean/ResearchLean/AG/Fixture.lean
git -C "$tmp/repo" commit -q -m 'research change'
assert_selection "$base" "$(git -C "$tmp/repo" rev-parse HEAD)" true

git -C "$tmp/repo" switch -q -C package-config "$base"
touch "$tmp/repo/lakefile.toml"
git -C "$tmp/repo" add lakefile.toml
git -C "$tmp/repo" commit -q -m 'package config change'
assert_selection "$base" "$(git -C "$tmp/repo" rev-parse HEAD)" true

git -C "$tmp/repo" switch -q -C workflow-change "$base"
mkdir -p "$tmp/repo/.github/workflows"
touch "$tmp/repo/.github/workflows/lean.yml"
git -C "$tmp/repo" add .github/workflows/lean.yml
git -C "$tmp/repo" commit -q -m 'workflow change'
assert_selection "$base" "$(git -C "$tmp/repo" rev-parse HEAD)" true

git -C "$tmp/repo" switch -q -C docs-only "$base"
mkdir -p "$tmp/repo/docs"
touch "$tmp/repo/docs/Fixture.md"
git -C "$tmp/repo" add docs/Fixture.md
git -C "$tmp/repo" commit -q -m 'docs change'
assert_selection "$base" "$(git -C "$tmp/repo" rev-parse HEAD)" false
assert_workflow_dispatch

ruby - "$workflow" <<'RUBY'
require "yaml"

workflow = YAML.load_file(ARGV.fetch(0))
step = workflow.fetch("jobs").fetch("research-integrity-gates").fetch("steps").find do |candidate|
  candidate["name"] == "Set up Lean for Research package validation"
end
abort "missing Research package setup step" unless step
expected = { "build" => false, "test" => false, "lint" => false }
abort "unexpected lean-action controls: #{step["with"].inspect}" unless step["with"] == expected
RUBY

echo "Research package validation selection tests passed."
