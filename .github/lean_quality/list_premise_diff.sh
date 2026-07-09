#!/usr/bin/env bash
set -euo pipefail

base_ref="${1:-${GITHUB_BASE_REF:-origin/main}}"
out_dir=".tmp/lean-quality"
out="$out_dir/premise-diff.txt"

if [ -n "${GITHUB_BASE_REF:-}" ]; then
  base_ref="origin/${GITHUB_BASE_REF}"
fi

if ! git rev-parse --verify "$base_ref" >/dev/null 2>&1; then
  base_ref="origin/main"
fi

mkdir -p "$out_dir"

{
  echo "# Premise diff"
  echo
  echo "base: $base_ref"
  echo

  files="$(
    {
      git diff --name-only "$base_ref" -- '*.lean' || true
      git ls-files --others --exclude-standard -- '*.lean' || true
    } | sort -u
  )"
  if [ -z "$files" ]; then
    echo "No changed Lean files."
    exit 0
  fi

  git diff --unified=0 "$base_ref" -- '*.lean' \
    | awk '
      function normalized(s) {
        gsub(/\.\{[^{}]*\}/, ".u", s)
        gsub(/\n/, " ", s)
        return s
      }
      function emit_block() {
        line = normalized(block)
        print "## " file
        print first_line
        while (match(line, /\([^()]*\)|\[[^][]*\]|\{[^{}]*\}/)) {
          print "  premise: " substr(line, RSTART, RLENGTH)
          line = substr(line, RSTART + RLENGTH)
        }
        print ""
        block = ""
        first_line = ""
        in_decl = 0
      }
      /^\+\+\+ b\// { file = substr($0, 7); next }
      /^\+/ {
        text = substr($0, 2)
        if (text ~ /^[[:space:]]*\/-/) { in_comment = 1 }
        if (in_comment) {
          if (text ~ /-\//) { in_comment = 0 }
          next
        }
        if (in_decl) {
          block = block " " text
          if (text ~ /:=|[[:space:]]where[[:space:]]*$/) { emit_block() }
          next
        }
        if (text ~ /^(theorem|lemma|def|abbrev|instance|structure|class|example)[[:space:]:]/) {
          block = text
          first_line = normalized(text)
          if (text ~ /:=|[[:space:]]where[[:space:]]*$/) {
            emit_block()
          } else {
            in_decl = 1
          }
        }
      }
      END { if (in_decl) { emit_block() } }
    '

  git ls-files --others --exclude-standard -- '*.lean' \
    | while IFS= read -r file; do
        awk -v file="$file" '
          function normalized(s) {
            gsub(/\.\{[^{}]*\}/, ".u", s)
            gsub(/\n/, " ", s)
            return s
          }
          function emit_block() {
            line = normalized(block)
            print "## " file
            print first_line
            while (match(line, /\([^()]*\)|\[[^][]*\]|\{[^{}]*\}/)) {
              print "  premise: " substr(line, RSTART, RLENGTH)
              line = substr(line, RSTART + RLENGTH)
            }
            print ""
            block = ""
            first_line = ""
            in_decl = 0
          }
          /^[[:space:]]*\/-/ { in_comment = 1 }
          in_comment {
            if ($0 ~ /-\//) { in_comment = 0 }
            next
          }
          {
            text = $0
            if (in_decl) {
              block = block " " text
              if (text ~ /:=|[[:space:]]where[[:space:]]*$/) { emit_block() }
              next
            }
            if (text ~ /^(theorem|lemma|def|abbrev|instance|structure|class|example)[[:space:]:]/) {
              block = text
              first_line = normalized(text)
              if (text ~ /:=|[[:space:]]where[[:space:]]*$/) {
                emit_block()
              } else {
                in_decl = 1
              }
            }
          }
          END { if (in_decl) { emit_block() } }
        ' "$file"
      done
} >"$out"

cat "$out"
