#!/bin/sh
# check-native.sh FILE: checks a proof exported for `native_decide` (`native/`
# of the exports) against the compiled library. Building the library's shared
# object (`lake build Vik:shared`) takes a few minutes the first time.
set -e
file=$(cd "$(dirname "$1")" && pwd)/$(basename "$1")
cd "$(dirname "$0")"
lake build Vik:shared >/dev/null
# the definitions of a large proof nest deeply
ulimit -s unlimited 2>/dev/null || true
lake env lean --load-dynlib=.lake/build/lib/libVik.so --tstack=4000000 "$file"
