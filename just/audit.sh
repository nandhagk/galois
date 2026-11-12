#!/usr/bin/env bash
set -euo pipefail
mode=strict
if [[ ${1-} == --admitted-ok ]]; then mode=admitted; shift; fi
built=_build/default/theories
dirs=("$@")
((${#dirs[@]})) || dirs=("")
modules=()
sources=()
for dir in "${dirs[@]}"; do
    [[ -d $built/$dir ]] || { echo "no compiled package $dir" >&2; exit 1; }
    while IFS= read -r file; do
        file=${file#"$built"/}
        file=${file%.vo}
        [[ -f theories/$file.v ]] || continue
        modules+=("Galois.${file//\//.}")
        sources+=("theories/$file.v")
    done < <(find "$built/$dir" -name '*.vo' | sort)
done
((${#modules[@]})) || { echo 'no compiled modules' >&2; exit 1; }
admitted=$(mktemp)
trap 'rm -f "$admitted"' EXIT
if [[ $mode == admitted ]]; then
    perl just/admitted.pl "${sources[@]}" | sort -u > "$admitted"
fi
report=$(just capped rocqchk -silent -o -Q "$built" Galois "${modules[@]}" 2>&1) || {
    echo "$report"; exit 1;
}
printf '%s\n' "$report" | awk -v admitted_file="$admitted" -f just/audit.awk just/audit.allow -
echo "audited ${#modules[@]} modules"
