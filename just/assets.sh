#!/usr/bin/env bash
set -euo pipefail

tag=$1
dir=$(realpath -m "$2")
repo=$(git rev-parse --show-toplevel)
case "$dir/" in
  "$repo/"*) printf 'Asset directory must be outside the repository: %s\n' "$dir" >&2; exit 1 ;;
esac
mkdir -p "$dir"
tmp=$(mktemp -d)
cleanup() {
  git -C "$repo" worktree remove --force "$tmp/tree" 2>/dev/null || true
  rm -rf "$tmp"
}
trap cleanup EXIT

git worktree add --detach "$tmp/tree" "$tag"
nix print-dev-env "$tmp/tree#session" > "$dir/galois-env.sh"
cat >> "$dir/galois-env.sh" <<'ENV'
export GALOIS_JOBS=4 GALOIS_NO_SYSTEMD=1
export DUNE_CACHE=enabled DUNE_CACHE_STORAGE_MODE=copy
export DUNE_CACHE_ROOT="$HOME/.cache/galois/dune"
unset LD_LIBRARY_PATH
ENV
grep -o '/nix/store/[a-z0-9]\{32\}-[-a-zA-Z0-9+._?=]*' "$dir/galois-env.sh" | sort -u | xargs nix-store -qR | sort -u > "$tmp/closure.txt"
tar --zstd -cPf "$dir/galois-toolchain.tar.zst" -T "$tmp/closure.txt"
(cd "$tmp/tree" && DUNE_CACHE_ROOT="$tmp/cache/dune" DUNE_CACHE_STORAGE_MODE=copy GALOIS_JOBS=6 just session-check)
tar --zstd -cf "$dir/galois-dune-cache.tar.zst" -C "$tmp/cache" dune
(cd "$dir" && sha256sum galois-toolchain.tar.zst galois-env.sh galois-dune-cache.tar.zst > SHA256SUMS)
