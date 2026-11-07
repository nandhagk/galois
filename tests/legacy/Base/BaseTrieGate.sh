#!/usr/bin/env bash
# Invoked only by the opt-in Dune runtest action inside the capped Just recipe.
set -euo pipefail

compiler=$1
root=$(cd ../../.. && pwd)
scratch=$(mktemp -d "${TMPDIR:-/tmp}/galois-trie-vm.XXXXXXXX")
trap 'rm -rf "$scratch"' EXIT

printf 'Real trie VM gate\n'
printf 'boundary: compiler startup, imports, VM reduction and kernel checking\n'
printf 'one compiler job; warm dependencies; fresh client compilation in every round\n'
printf 'compiler: %s\n' "$compiler"
printf 'inherited cgroup: '
cat /proc/self/cgroup
slice=$(awk -F: '$1 == "0" {sub(/galois.slice.*/, "galois.slice", $3); print $3}' \
  /proc/self/cgroup)
case "$slice" in
  */galois.slice) ;;
  *) printf 'gate is outside galois.slice\n' >&2; exit 1 ;;
esac
printf 'memory cap: '
cat "/sys/fs/cgroup$slice/memory.max"
printf 'swap cap: '
cat "/sys/fs/cgroup$slice/memory.swap.max"
memory_max=$(cat "/sys/fs/cgroup$slice/memory.max")
test "$memory_max" -gt 0
test "$memory_max" -le 10000000000
test "$(cat "/sys/fs/cgroup$slice/memory.swap.max")" = 0

TIMEFORMAT='%R %U %S'
for round in 1 2 3; do
  for mode in Pure Costed; do
    source="BaseTrieGate${mode}LegacyTest.v"
    mkdir "$scratch/$round-$mode"
    target="$scratch/$round-$mode/$source"
    cp "$source" "$target"
    printf 'round %s %s\n' "$round" "$mode"
    # The source is recompiled directly on every invocation. Dune's result cache
    # covers dependencies and never supplies a measured client compilation.
    if { time "$compiler" compile -w +default \
        -Q "$root/theories/Cost" Galois.Cost \
        -Q "$root/theories/Base" Galois.Base \
        -Q "$root/legacy/theories/Collections" GaloisLegacy.Collections \
        -Q "$root/tests/legacy/Base" Galois.Tests.Legacy.Base \
        "$target"; } 2> "$scratch/time"; then
      :
    else
      status=$?
      cat "$scratch/time" >&2
      exit "$status"
    fi
    cat "$scratch/time"
    awk -v round="$round" -v mode="$mode" \
      'NF == 3 { print round, mode, $1, $2, $3 }' "$scratch/time" >> "$scratch/runs"
  done
done

cat "$scratch/runs"
pure=$(awk '$2 == "Pure" {print $3}' "$scratch/runs" | sort -n | awk 'NR == 2')
costed=$(awk '$2 == "Costed" {print $3}' "$scratch/runs" | sort -n | awk 'NR == 2')
awk -v pure="$pure" -v costed="$costed" 'BEGIN {
  ratio = costed / pure
  printf "median pure %.3f s; median costed %.3f s; ratio %.6f; target 1.5\n", pure, costed, ratio
  if (ratio > 1.5) exit 1
}'
