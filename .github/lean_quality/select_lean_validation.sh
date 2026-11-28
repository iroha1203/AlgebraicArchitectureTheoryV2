#!/usr/bin/env bash
set -euo pipefail

target="${1:?usage: select_lean_validation.sh <research|ag|shigure>}"
event_name="${EVENT_NAME:?EVENT_NAME is required}"
github_output="${GITHUB_OUTPUT:?GITHUB_OUTPUT is required}"

case "$target" in
  research)
    pattern='^(lakefile\.toml$|lake-manifest\.json$|research/lean/|\.github/lean_quality/(check_research_migration|check_research_package|test_research_migration|test_research_package|select_research_package_validation\.sh$|select_lean_validation\.sh$)|\.github/workflows/lean\.yml$)'
    ;;
  ag)
    pattern='^(Formal/AG/|Formal/AG\.lean$|Formal/Util/AssertStandardAxioms[^/]*\.lean$|lakefile\.toml$|lake-manifest\.json$|lean-toolchain$|\.github/lean_quality/|\.github/workflows/lean\.yml$)'
    ;;
  shigure)
    pattern='^(Formal/SHIGURE/|Formal/SHIGURE\.lean$|lakefile\.toml$|lake-manifest\.json$|lean-toolchain$|\.github/lean_quality/(check_shigure_imports\.lean$|check_shigure_declarations\.lean$|ShigureBuildAudit\.lean$|shigure_cache_manifest\.py$|test_shigure_declarations\.sh$|select_lean_validation\.sh$)|\.github/workflows/lean\.yml$)'
    ;;
  *)
    echo "unsupported Lean validation target: $target" >&2
    exit 2
    ;;
esac

if [ "$event_name" = "workflow_dispatch" ]; then
  echo "run=true" >>"$github_output"
  exit 0
fi

ensure_commit() {
  local sha="$1"
  if ! git cat-file -e "${sha}^{commit}" 2>/dev/null; then
    git fetch --no-tags --depth=1 origin "$sha"
  fi
}

head_sha="${HEAD_SHA:?HEAD_SHA is required}"
changed_paths=""

case "$event_name" in
  pull_request)
    second_parent="$(git rev-parse --verify --quiet "${head_sha}^2" || true)"
    use_merge_first_parent=0
    if [ -n "$second_parent" ]; then
      if [ -z "${PR_HEAD:-}" ]; then
        use_merge_first_parent=1
      else
        pr_head_commit="$(git rev-parse --verify --quiet "${PR_HEAD}^{commit}" || printf '%s' "$PR_HEAD")"
        if [ "$second_parent" = "$pr_head_commit" ]; then
          use_merge_first_parent=1
        fi
      fi
    fi

    if [ "$use_merge_first_parent" -eq 1 ]; then
      # GitHub Actions checks out the synthetic merge commit merge(target_tip, pr_head).
      # Comparing HEAD_SHA^1..HEAD_SHA isolates the changes introduced by this PR onto target_tip,
      # excluding commits merged into main after PR_BASE without extra fetches under fetch-depth: 2.
      first_parent="$(git rev-parse --verify "${head_sha}^1")"
      ensure_commit "$first_parent"
      changed_paths="$(git -c core.quotePath=false diff --no-renames --name-only "$first_parent" "$head_sha")"
    else
      pr_head="${PR_HEAD:-$head_sha}"
      base="${PR_BASE:?PR_BASE is required}"
      if [[ "$base" =~ ^0+$ ]]; then
        echo "run=true" >>"$github_output"
        exit 0
      fi
      ensure_commit "$base"
      ensure_commit "$pr_head"
      if git merge-base "$base" "$pr_head" >/dev/null 2>&1; then
        changed_paths="$(git -c core.quotePath=false diff --no-renames --name-only "$base...$pr_head")"
      else
        changed_paths="$(git -c core.quotePath=false diff --no-renames --name-only "$base" "$pr_head")"
      fi
    fi
    ;;
  push)
    base="${PUSH_BASE:?PUSH_BASE is required}"
    if [[ "$base" =~ ^0+$ ]]; then
      echo "run=true" >>"$github_output"
      exit 0
    fi
    ensure_commit "$base"
    changed_paths="$(git -c core.quotePath=false diff --no-renames --name-only "$base" "$head_sha")"
    ;;
  *)
    echo "unsupported EVENT_NAME: $event_name" >&2
    exit 2
    ;;
esac

if [ -n "$changed_paths" ] && grep -Eq "$pattern" <<<"$changed_paths"; then
  echo "run=true" >>"$github_output"
else
  if [ "$target" = "ag" ]; then
    echo "no Lean-relevant changes; Lean build steps are skipped"
  fi
  echo "run=false" >>"$github_output"
fi
