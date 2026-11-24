#!/bin/sh
# export.sh LIST OUT [SECONDS]: solves the scripts LIST names, from the
# repository's root, and writes their CPC proofs to OUT (`CpcCorpus`, each
# script within SECONDS, 60 by default). Fails if a script gets no proof.
set -e
root=$(cd "$(dirname "$0")/../.." && pwd)
list=$(cd "$(dirname "$1")" && pwd)/$(basename "$1")
mkdir -p "$2"
out=$(cd "$2" && pwd)
cd "$root"
sbt --server "proofs/runMain io.bovel.vik.proofs.CpcCorpus $list $out ${3:-60}" | tee "$out/export.log" |
  grep -E "^[^[].*	C[0-9]+	" || true
want=$(grep -c . "$list")
got=$(grep -cP '\tC[0-9]+\twritten$' "$out/export.log" || true)
echo "$got of $want scripts exported"
[ "$got" = "$want" ]
