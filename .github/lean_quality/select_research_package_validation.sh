#!/usr/bin/env bash
set -euo pipefail

if [ "${EVENT_NAME:?EVENT_NAME is required}" = "workflow_dispatch" ]; then
  echo "run=true" >>"${GITHUB_OUTPUT:?GITHUB_OUTPUT is required}"
  exit 0
fi

base="${PUSH_BASE:?PUSH_BASE is required}"
if [ "$EVENT_NAME" = "pull_request" ]; then
  base="${PR_BASE:?PR_BASE is required}"
fi
if printf '%s' "$base" | grep -Eq '^0+$'; then
  base="$(git rev-list --max-parents=0 "${HEAD_SHA:?HEAD_SHA is required}" | tail -n 1)"
fi

if git diff --name-only "$base...${HEAD_SHA:?HEAD_SHA is required}" | grep -Eq \
    '^(lakefile\.toml$|lake-manifest\.json$|research/lean/|\.github/lean_quality/(check_research_migration|check_research_package|test_research_migration|test_research_package)|\.github/workflows/lean\.yml$)'; then
  echo "run=true" >>"${GITHUB_OUTPUT:?GITHUB_OUTPUT is required}"
else
  echo "run=false" >>"${GITHUB_OUTPUT:?GITHUB_OUTPUT is required}"
fi
