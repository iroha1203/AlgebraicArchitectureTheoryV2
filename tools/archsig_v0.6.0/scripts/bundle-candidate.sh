#!/bin/sh
# Build only committed inputs; never package a caller-supplied executable.
set -eu
export LC_ALL=C TZ=UTC
usage() { echo "usage: $0 SOURCE_COMMIT NEW_OUTPUT_DIRECTORY" >&2; exit 64; }
[ "$#" -eq 2 ] || usage
repo=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)
commit=$(git -C "$repo" rev-parse --verify "$1^{commit}")
[ "$commit" = "$1" ] || { echo 'SOURCE_COMMIT must be a full commit hash' >&2; exit 64; }
[ ! -e "$2" ] || { echo 'output already exists' >&2; exit 64; }
mkdir -p "$2"
out=$(cd "$2" && pwd)
# Keep the exact source archive for independent rebuilds and provenance checks.
git -C "$repo" archive --format=tar "$commit" tools/archsig_v0.6.0 docs/tool/archsig_v0_6_0_io > "$out/source.tar"
mkdir "$out/source"
tar -xf "$out/source.tar" -C "$out/source"
src="$out/source/tools/archsig_v0.6.0"
# A dirty caller checkout cannot influence the archived build or bundled files.
grep -qx 'version = "0.6.0"' "$src/Cargo.toml" || { echo 'expected ArchSig 0.6.0 source' >&2; exit 65; }
host=$(rustc -vV | sed -n 's/^host: //p')
[ -n "$host" ] || exit 70
name="archsig-0.6.0-$host-candidate"
bundle="$out/$name"
mkdir -p "$bundle/bin" "$bundle/skills" "$bundle/docs"
# Explicit target and path remapping prevent build-directory paths in the CLI.
# Cargo validates reused cache entries against these archived inputs.
export CARGO_TARGET_DIR="${CARGO_TARGET_DIR:-$out/target}"
export RUSTFLAGS="--remap-path-prefix=$out/source=/archsig-source"
unset CARGO_ENCODED_RUSTFLAGS
cargo build --locked --manifest-path "$src/Cargo.toml" --target "$host" --bin archsig -j 1
cp "$CARGO_TARGET_DIR/$host/debug/archsig" "$bundle/bin/archsig"
cp -R "$src/skills/archsig-observe" "$bundle/skills/"
cp -R "$out/source/docs/tool/archsig_v0_6_0_io" "$bundle/docs/io"
cp "$src/BUNDLE.md" "$bundle/README.md"
# Relocate the three repository-relative links; all normative I/O text is retained.
for file in "$bundle"/docs/io/*.md; do
    sed -e 's|../../../tools/archsig_v0.6.0/README.md|../../README.md|g' \
        -e 's|../../../tools/archsig_v0.6.0/skills/|../../skills/|g' \
        -e '/^関連: \[製品コンセプト\]/,$d' "$file" > "$file.tmp"
    mv "$file.tmp" "$file"
done
"$bundle/bin/archsig" version > "$bundle/VERSION.json"
sha() { shasum -a 256 "$1" | cut -d ' ' -f 1; }
{
    echo 'format=archsig-candidate-provenance/1'
    echo "source_commit=$commit"
    echo "source_tree=$(git -C "$repo" rev-parse "$commit^{tree}")"
    echo "source_archive_sha256=$(sha "$out/source.tar")"
    echo "binary_sha256=$(sha "$bundle/bin/archsig")"
    echo "target=$host"
    echo 'profile=dev'
    echo 'command=cargo build --locked --target TARGET --bin archsig -j 1'
    echo 'rustflags=--remap-path-prefix=SOURCE_DIRECTORY=/archsig-source'
    rustc -vV
    cargo -V
} > "$bundle/PROVENANCE.txt"
# Stable member order, ownership, timestamps and gzip header for the same payload.
find "$bundle" -exec touch -t 197001010000 {} +
(cd "$out" && find "$name" -print | sort > members.txt && 
    COPYFILE_DISABLE=1 tar --format=ustar --uid 0 --gid 0 --uname root --gname root \
        --no-recursion -cf "$name.tar" -T members.txt && gzip -n "$name.tar")
(cd "$out" && shasum -a 256 source.tar "$name.tar.gz" > SHA256SUMS)
cat "$out/SHA256SUMS"
echo "bundle=$out/$name.tar.gz"
