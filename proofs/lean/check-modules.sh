#!/bin/sh
# check-modules.sh DIR [JOBS]: checks an exported proof split into modules
# (`DIR/Data.lean`, `DIR/S_*.lean`, `DIR/Main.lean`), the slices JOBS at a
# time (2 by default; each can take several GB). The compiled modules go to
# `DIR/../.olean`.
set -e
dir=$(cd "$1" && pwd)
jobs=${2:-2}
root=$(dirname "$dir")
name=$(basename "$dir")
cd "$(dirname "$0")"
olean="$root/.olean"
mkdir -p "$olean/$name"
LEAN_PATH="$(lake env printenv LEAN_PATH):$olean"
export LEAN_PATH
lean --root="$root" -o "$olean/$name/Data.olean" "$dir/Data.lean"
# a slice that fails (or is killed) is reported, and the others still run
ls "$dir" | grep '^S_.*\.lean$' | sed 's/\.lean$//' |
  xargs -P "$jobs" -I{} sh -c 'lean --root="$1" -o "$2/{}.olean" "$3/{}.lean" || { echo "failed: {}"; exit 1; }' \
    sh "$root" "$olean/$name" "$dir" || exit 1
lean --root="$root" "$dir/Main.lean"
