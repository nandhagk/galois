#!/usr/bin/env bash
set -euo pipefail
paths="docs/sessions/$1.paths"
range=$2
[[ -f $paths ]] || { printf 'missing paths file: %s\n' "$paths" >&2; exit 1; }
patterns=()
while IFS= read -r line || [[ -n $line ]]; do
    [[ -z $line || $line == \#* ]] || patterns+=("$line")
done < "$paths"
failed=0
while IFS= read -r -d '' file; do
    matched=0
    for pattern in "${patterns[@]}"; do
        if [[ $file == $pattern ]]; then matched=1; break; fi
    done
    if (( ! matched )); then printf '%s\n' "$file"; failed=1; fi
done < <(git diff --name-only -z "$range")
exit "$failed"
