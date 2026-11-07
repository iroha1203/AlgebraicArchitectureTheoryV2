#!/bin/sh
# sh run.sh /absolute/path/to/archsig /absolute/new/output finite|integer missing|observed|reobserved [reuse]
set -u
if [ "$#" -lt 4 ] || [ "$#" -gt 5 ]; then
    echo 'usage: sh run.sh CLI OUTPUT finite|integer|assembly missing|observed|reobserved [REUSE]' >&2
    exit 64
fi
cli=$1
out=$2
kind=$3
state=$4
reuse=${5-}
assets=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd) || exit
case "$kind:$state" in
    finite:missing|integer:missing) asks="$assets/$kind-observe.asks" ;;
    finite:observed|finite:reobserved|integer:observed|integer:reobserved) asks="$assets/$kind-choose.asks" ;;
    assembly:observed) asks="$assets/assembly.asks" ;;
    *) echo 'unsupported example or stage' >&2; exit 64 ;;
esac
map="$assets/$kind-$state.archmap.json"
if [ "$kind" = assembly ]; then map="$assets/assembly.archmap.json"; fi
set -- run --atom-definition "$assets/$kind.atoms.json" --law "$assets/$kind.law" --archmap "$map" --out "$out"
if [ -n "$reuse" ]; then set -- "$@" --reuse "$reuse"; fi
while IFS= read -r ask || [ -n "$ask" ]; do
    if [ -n "$ask" ]; then set -- "$@" --ask "$ask"; fi
done < "$asks"
exec "$cli" "$@"
