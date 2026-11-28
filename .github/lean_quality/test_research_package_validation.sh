#!/usr/bin/env bash
set -euo pipefail

repo_root="$(git rev-parse --show-toplevel)"
selector="$repo_root/.github/lean_quality/select_research_package_validation.sh"
unified_selector="$repo_root/.github/lean_quality/select_lean_validation.sh"
workflow="$repo_root/.github/workflows/lean.yml"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

run_target_selector() {
  local repo="$1"
  local target="$2"
  local event_name="$3"
  local pr_base="$4"
  local pr_head="$5"
  local push_base="$6"
  local head_sha="$7"
  local expected="$8"
  local actual

  : >"$tmp/output"
  (
    cd "$repo"
    if [ "$target" = "research-wrapper" ]; then
      EVENT_NAME="$event_name" \
        PR_BASE="$pr_base" \
        PR_HEAD="$pr_head" \
        PUSH_BASE="$push_base" \
        HEAD_SHA="$head_sha" \
        GITHUB_OUTPUT="$tmp/output" \
        "$selector" >/dev/null
    else
      EVENT_NAME="$event_name" \
        PR_BASE="$pr_base" \
        PR_HEAD="$pr_head" \
        PUSH_BASE="$push_base" \
        HEAD_SHA="$head_sha" \
        GITHUB_OUTPUT="$tmp/output" \
        "$unified_selector" "$target" >/dev/null
    fi
  )
  actual="$(cat "$tmp/output")"
  if [ "$actual" != "run=$expected" ]; then
    echo "FAIL: target=$target event=$event_name expected=run=$expected actual=$actual" >&2
    exit 1
  fi
}

assert_selection() {
  local base="$1"
  local head="$2"
  local expected="$3"
  run_target_selector "$tmp/repo" research-wrapper pull_request "$base" "" "" "$head" "$expected"
}

assert_all_targets_pr() {
  local repo="$1"
  local pr_base="$2"
  local pr_head="$3"
  local head_sha="$4"
  local expect_research="$5"
  local expect_ag="$6"
  local expect_shigure="$7"

  run_target_selector "$repo" research-wrapper pull_request "$pr_base" "$pr_head" "" "$head_sha" "$expect_research"
  run_target_selector "$repo" research pull_request "$pr_base" "$pr_head" "" "$head_sha" "$expect_research"
  run_target_selector "$repo" ag pull_request "$pr_base" "$pr_head" "" "$head_sha" "$expect_ag"
  run_target_selector "$repo" shigure pull_request "$pr_base" "$pr_head" "" "$head_sha" "$expect_shigure"
}

assert_all_targets_push() {
  local repo="$1"
  local push_base="$2"
  local head_sha="$3"
  local expect_research="$4"
  local expect_ag="$5"
  local expect_shigure="$6"

  run_target_selector "$repo" research-wrapper push "" "" "$push_base" "$head_sha" "$expect_research"
  run_target_selector "$repo" research push "" "" "$push_base" "$head_sha" "$expect_research"
  run_target_selector "$repo" ag push "" "" "$push_base" "$head_sha" "$expect_ag"
  run_target_selector "$repo" shigure push "" "" "$push_base" "$head_sha" "$expect_shigure"
}

assert_workflow_dispatch() {
  local target
  for target in research-wrapper research ag shigure; do
    run_target_selector "$tmp/repo" "$target" workflow_dispatch "" "" "" "" true
  done
}

make_synthetic_merge() {
  local repo="$1"
  local main_tip="$2"
  local pr_head="$3"
  git -C "$repo" checkout -q --detach "$main_tip" >&2 || return 1
  git -C "$repo" merge -q --no-ff --no-edit "$pr_head" >&2 || return 1
  git -C "$repo" rev-parse HEAD
}

mkdir -p "$tmp/repo"
git -C "$tmp/repo" init -q -b main
git -C "$tmp/repo" config user.email 'research-validation-test@example.invalid'
git -C "$tmp/repo" config user.name 'research validation test'
mkdir -p "$tmp/repo/Formal/SHIGURE"
printf '%s\n' 'base' > "$tmp/repo/README.md"
printf '%s\n' 'module SHIGURE.Keep' > "$tmp/repo/Formal/SHIGURE/Keep.lean"
printf '%s\n' 'module SHIGURE.Moved' > "$tmp/repo/Formal/SHIGURE/Moved.lean"
git -C "$tmp/repo" add README.md Formal/SHIGURE/Keep.lean Formal/SHIGURE/Moved.lean
git -C "$tmp/repo" commit -q -m 'base'
base="$(git -C "$tmp/repo" rev-parse HEAD)"

# 1. Backward-compatible linear pull_request fixtures (no synthetic merge commit)
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

# 2. Main advances with unrelated Lean/Research PRs before synthetic merge commit (#6602 regression)
git -C "$tmp/repo" switch -q -C main-advanced "$base"
mkdir -p "$tmp/repo/Formal/SHIGURE" "$tmp/repo/Formal/AG" "$tmp/repo/research/lean/ResearchLean/AG"
printf '%s\n' 'shigure on main' > "$tmp/repo/Formal/SHIGURE/MainOnly.lean"
printf '%s\n' 'ag on main' > "$tmp/repo/Formal/AG/MainOnly.lean"
printf '%s\n' 'research on main' > "$tmp/repo/research/lean/ResearchLean/AG/MainOnly.lean"
git -C "$tmp/repo" add Formal/SHIGURE/MainOnly.lean Formal/AG/MainOnly.lean research/lean/ResearchLean/AG/MainOnly.lean
git -C "$tmp/repo" commit -q -m 'prior Lean PRs merged into main'
main_advanced="$(git -C "$tmp/repo" rev-parse HEAD)"

# 2a. Non-Lean PR (tools only) branched from base, merged onto main_advanced -> all false
git -C "$tmp/repo" switch -q -C pr-tools-only "$base"
mkdir -p "$tmp/repo/tools/archsig_v0.6.0/src"
printf '%s\n' 'pub fn f() {}' > "$tmp/repo/tools/archsig_v0.6.0/src/lib.rs"
git -C "$tmp/repo" add tools/archsig_v0.6.0/src/lib.rs
git -C "$tmp/repo" commit -q -m 'tools change'
pr_tools_head="$(git -C "$tmp/repo" rev-parse HEAD)"
merge_tools="$(make_synthetic_merge "$tmp/repo" "$main_advanced" "$pr_tools_head")"
assert_all_targets_pr "$tmp/repo" "$base" "$pr_tools_head" "$merge_tools" false false false

# 2b. AG-only PR merged onto main_advanced -> only ag=true
git -C "$tmp/repo" switch -q -C pr-ag-only "$base"
mkdir -p "$tmp/repo/Formal/AG"
printf '%s\n' 'ag pr' > "$tmp/repo/Formal/AG/PrOnly.lean"
git -C "$tmp/repo" add Formal/AG/PrOnly.lean
git -C "$tmp/repo" commit -q -m 'ag change'
pr_ag_head="$(git -C "$tmp/repo" rev-parse HEAD)"
merge_ag="$(make_synthetic_merge "$tmp/repo" "$main_advanced" "$pr_ag_head")"
assert_all_targets_pr "$tmp/repo" "$base" "$pr_ag_head" "$merge_ag" false true false

# 2c. SHIGURE multi-commit PR (1st commit SHIGURE, 2nd commit docs) merged onto main_advanced -> only shigure=true
git -C "$tmp/repo" switch -q -C pr-shigure-multi "$base"
mkdir -p "$tmp/repo/Formal/SHIGURE" "$tmp/repo/docs"
printf '%s\n' 'shigure pr' > "$tmp/repo/Formal/SHIGURE/PrOnly.lean"
git -C "$tmp/repo" add Formal/SHIGURE/PrOnly.lean
git -C "$tmp/repo" commit -q -m 'shigure change'
printf '%s\n' 'docs note' > "$tmp/repo/docs/Note.md"
git -C "$tmp/repo" add docs/Note.md
git -C "$tmp/repo" commit -q -m 'docs follow-up'
pr_shigure_head="$(git -C "$tmp/repo" rev-parse HEAD)"
merge_shigure="$(make_synthetic_merge "$tmp/repo" "$main_advanced" "$pr_shigure_head")"
assert_all_targets_pr "$tmp/repo" "$base" "$pr_shigure_head" "$merge_shigure" false false true

# 2d. Research-only PR merged onto main_advanced -> only research=true
git -C "$tmp/repo" switch -q -C pr-research-only "$base"
mkdir -p "$tmp/repo/research/lean/ResearchLean/AG"
printf '%s\n' 'research pr' > "$tmp/repo/research/lean/ResearchLean/AG/PrOnly.lean"
git -C "$tmp/repo" add research/lean/ResearchLean/AG/PrOnly.lean
git -C "$tmp/repo" commit -q -m 'research change'
pr_research_head="$(git -C "$tmp/repo" rev-parse HEAD)"
merge_research="$(make_synthetic_merge "$tmp/repo" "$main_advanced" "$pr_research_head")"
assert_all_targets_pr "$tmp/repo" "$base" "$pr_research_head" "$merge_research" true false false

# 2e. PR that merged an intermediate main commit into itself, then main advanced again -> all false
git -C "$tmp/repo" switch -q -C main-step1 "$base"
mkdir -p "$tmp/repo/Formal/SHIGURE"
printf '%s\n' 'step1' > "$tmp/repo/Formal/SHIGURE/Step1.lean"
git -C "$tmp/repo" add Formal/SHIGURE/Step1.lean
git -C "$tmp/repo" commit -q -m 'main step 1'
main_step1="$(git -C "$tmp/repo" rev-parse HEAD)"

mkdir -p "$tmp/repo/Formal/AG"
printf '%s\n' 'step2' > "$tmp/repo/Formal/AG/Step2.lean"
git -C "$tmp/repo" add Formal/AG/Step2.lean
git -C "$tmp/repo" commit -q -m 'main step 2'
main_step2="$(git -C "$tmp/repo" rev-parse HEAD)"

git -C "$tmp/repo" switch -q -C pr-merged-main "$base"
mkdir -p "$tmp/repo/tools"
printf '%s\n' 'tool' > "$tmp/repo/tools/only_tool.txt"
git -C "$tmp/repo" add tools/only_tool.txt
git -C "$tmp/repo" commit -q -m 'tool change'
git -C "$tmp/repo" merge -q --no-ff --no-edit "$main_step1"
pr_merged_main_head="$(git -C "$tmp/repo" rev-parse HEAD)"
merge_double="$(make_synthetic_merge "$tmp/repo" "$main_step2" "$pr_merged_main_head")"
assert_all_targets_pr "$tmp/repo" "$base" "$pr_merged_main_head" "$merge_double" false false false

# 2f. Moving a watched file out of Formal/SHIGURE/ still triggers shigure (--no-renames)
git -C "$tmp/repo" switch -q -C pr-rename-out "$base"
mkdir -p "$tmp/repo/docs"
git -C "$tmp/repo" mv Formal/SHIGURE/Moved.lean docs/Moved.md
git -C "$tmp/repo" commit -q -m 'move file out of SHIGURE'
pr_rename_head="$(git -C "$tmp/repo" rev-parse HEAD)"
merge_rename="$(make_synthetic_merge "$tmp/repo" "$main_advanced" "$pr_rename_head")"
assert_all_targets_pr "$tmp/repo" "$base" "$pr_rename_head" "$merge_rename" false false true

# 2g. Updating select_lean_validation.sh itself triggers all three targets
git -C "$tmp/repo" switch -q -C pr-selector-self "$base"
mkdir -p "$tmp/repo/.github/lean_quality"
printf '%s\n' '# selector' > "$tmp/repo/.github/lean_quality/select_lean_validation.sh"
git -C "$tmp/repo" add .github/lean_quality/select_lean_validation.sh
git -C "$tmp/repo" commit -q -m 'selector update'
pr_selector_head="$(git -C "$tmp/repo" rev-parse HEAD)"
merge_selector="$(make_synthetic_merge "$tmp/repo" "$main_advanced" "$pr_selector_head")"
assert_all_targets_pr "$tmp/repo" "$base" "$pr_selector_head" "$merge_selector" true true true

# 3. push events on main
assert_all_targets_push "$tmp/repo" "$base" "$main_advanced" true true true
assert_all_targets_push "$tmp/repo" "$main_advanced" "$merge_tools" false false false
assert_all_targets_push "$tmp/repo" "$main_advanced" "$merge_shigure" false false true
assert_all_targets_push "$tmp/repo" "$main_advanced" "$merge_ag" false true false
assert_all_targets_push "$tmp/repo" "$main_advanced" "$merge_research" true false false
assert_all_targets_push "$tmp/repo" "0000000000000000000000000000000000000000" "$merge_tools" true true true

# 4. Shallow depth=2 clone (mirrors shigure job actions/checkout@v4 fetch-depth: 2)
git -C "$tmp/repo" update-ref refs/pull/1/merge "$merge_tools"
git -C "$tmp/repo" update-ref refs/pull/2/merge "$merge_shigure"

git -C "$tmp/repo" switch -q -C main-multi-push "$base"
mkdir -p "$tmp/repo/Formal/SHIGURE" "$tmp/repo/docs"
printf '%s\n' 'commit1' > "$tmp/repo/Formal/SHIGURE/PushMulti.lean"
git -C "$tmp/repo" add Formal/SHIGURE/PushMulti.lean
git -C "$tmp/repo" commit -q -m 'push 1'
printf '%s\n' 'commit2' > "$tmp/repo/docs/Push2.md"
git -C "$tmp/repo" add docs/Push2.md
git -C "$tmp/repo" commit -q -m 'push 2'
printf '%s\n' 'commit3' > "$tmp/repo/docs/Push3.md"
git -C "$tmp/repo" add docs/Push3.md
git -C "$tmp/repo" commit -q -m 'push 3'
main_multi_push="$(git -C "$tmp/repo" rev-parse HEAD)"
git -C "$tmp/repo" update-ref refs/heads/main "$main_multi_push"

shallow_pr_tools="$tmp/shallow-pr-tools"
mkdir -p "$shallow_pr_tools"
git -C "$shallow_pr_tools" init -q
git -C "$shallow_pr_tools" remote add origin "file://$tmp/repo"
git -C "$shallow_pr_tools" fetch -q --no-tags --depth=2 origin "+refs/pull/1/merge:refs/remotes/pull/1/merge"
git -C "$shallow_pr_tools" checkout -q --detach refs/remotes/pull/1/merge
# Remove origin remote to prove no extra git fetch is performed for PR synthetic merge commits.
git -C "$shallow_pr_tools" remote remove origin
run_target_selector "$shallow_pr_tools" shigure pull_request "$base" "$pr_tools_head" "" "$merge_tools" false

shallow_pr_shigure="$tmp/shallow-pr-shigure"
mkdir -p "$shallow_pr_shigure"
git -C "$shallow_pr_shigure" init -q
git -C "$shallow_pr_shigure" remote add origin "file://$tmp/repo"
git -C "$shallow_pr_shigure" fetch -q --no-tags --depth=2 origin "+refs/pull/2/merge:refs/remotes/pull/2/merge"
git -C "$shallow_pr_shigure" checkout -q --detach refs/remotes/pull/2/merge
git -C "$shallow_pr_shigure" remote remove origin
run_target_selector "$shallow_pr_shigure" shigure pull_request "$base" "$pr_shigure_head" "" "$merge_shigure" true

shallow_push="$tmp/shallow-push"
mkdir -p "$shallow_push"
git -C "$shallow_push" init -q
git -C "$shallow_push" remote add origin "file://$tmp/repo"
git -C "$shallow_push" fetch -q --no-tags --depth=2 origin "+refs/heads/main:refs/remotes/origin/main"
git -C "$shallow_push" checkout -q --detach refs/remotes/origin/main
run_target_selector "$shallow_push" shigure push "" "" "$base" "$main_multi_push" true

ruby - "$workflow" <<'RUBY'
require "yaml"

workflow = YAML.load_file(ARGV.fetch(0))
jobs = workflow.fetch("jobs")

expected_env = {
  "EVENT_NAME" => "${{ github.event_name }}",
  "PR_BASE" => "${{ github.event.pull_request.base.sha }}",
  "PR_HEAD" => "${{ github.event.pull_request.head.sha }}",
  "PUSH_BASE" => "${{ github.event.before }}",
  "HEAD_SHA" => "${{ github.sha }}",
}

[
  ["research-integrity-gates", "Select Research package validation", ".github/lean_quality/select_research_package_validation.sh"],
  ["build", "Select active AAT algebraic geometry build", ".github/lean_quality/select_lean_validation.sh ag"],
  ["shigure", "Select SHIGURE validation", ".github/lean_quality/select_lean_validation.sh shigure"],
].each do |job_name, step_name, expected_run|
  step = jobs.fetch(job_name).fetch("steps").find { |candidate| candidate["name"] == step_name }
  abort "missing step #{job_name} / #{step_name}" unless step
  abort "unexpected env for #{job_name} / #{step_name}: #{step["env"].inspect}" unless step["env"] == expected_env
  abort "unexpected run for #{job_name} / #{step_name}: #{step["run"].inspect}" unless step["run"].to_s.strip == expected_run
end

step = jobs.fetch("research-integrity-gates").fetch("steps").find do |candidate|
  candidate["name"] == "Set up Lean for Research package validation"
end
abort "missing Research package setup step" unless step
expected = {
  "build" => false,
  "test" => false,
  "lint" => false,
  "use-github-cache" => false,
}
abort "unexpected lean-action controls: #{step["with"].inspect}" unless step["with"] == expected
RUBY

echo "Lean validation selection tests passed."
