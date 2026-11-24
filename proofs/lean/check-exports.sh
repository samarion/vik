#!/bin/sh
# check-exports.sh DIR [kernel|native] [JOBS]: checks every proof that
# `LeanCorpus` exported to DIR, with `decide +kernel` (`check-modules.sh`, JOBS
# slices at a time) or with `native_decide` (`check-native.sh`), and prints a
# line per proof: its name, `ok` or `failed`, and the seconds it took. Exits
# with 1 if a proof failed.
#
# The end-to-end set, `e2e.txt`, covers the corpus's logics, justifications,
# input reasons, lowering rules and operators, and checks in the kernel in
# about two minutes:
#   proofs/lean/export.sh proofs/lean/e2e.txt out/e2e
#   proofs/lean/check-exports.sh out/e2e
# and the corpus list with `native_decide`:
#   proofs/lean/export.sh proofs/lean/corpus.txt out/corpus
#   proofs/lean/check-exports.sh out/corpus native
# CI runs both (the lean and lean-native jobs).
dir=$(cd "$1" && pwd)
mode=${2:-kernel}
jobs=${3:-2}
here=$(cd "$(dirname "$0")" && pwd)
status=0
for f in $(ls "$dir" | grep '^C[0-9]*\.lean$' | sort); do
  name=${f%.lean}
  start=$(date +%s)
  if [ "$mode" = native ]; then
    "$here/check-native.sh" "$dir/native/$f" >"$dir/$name.log" 2>&1
  else
    "$here/check-modules.sh" "$dir/$name" "$jobs" >"$dir/$name.log" 2>&1
  fi
  code=$?
  # Lean reports a failed theorem as an error without failing on every path
  if [ $code -eq 0 ] && grep -q 'error' "$dir/$name.log"; then code=1; fi
  if [ $code -eq 0 ]; then r=ok; else r=failed; status=1; fi
  printf '%s\t%s\t%s\n' "$name" "$r" "$(($(date +%s) - start))"
done
exit $status
