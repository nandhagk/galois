import "just/settings.just"

# List the developer workflows.
[default]
list:
    @just --list

# Set the persistent aggregate memory limit in bytes for every build command.
slice-cap size="10000000000":
    systemctl --user set-property galois.slice MemoryMax="$1" MemorySwapMax=0

# Run a command under the memory cap, or directly when no systemd user session exists.
[private]
capped +args:
    @{{ cap }} "$@"

# Check the formatting of every source file.
[private]
fmt-check:
    @just capped dune build -j {{ jobs }} @fmt

# Build the theories and the extraction clients.
build *args:
    @just capped dune build -j {{ jobs }} @theories/default @extraction/default "$@"

# Build the Rocq tests and examples and run the OCaml inline tests.
test *args:
    @just capped dune build -j {{ jobs }} @tests/default @examples/default @runtest "$@"

# Check formatting, build, test, lint and the frozen files.
check: fmt-check build test lint frozen

# Print every lint rule match from just/lint.rules and fail if there is any.
[script("bash", "-euo", "pipefail")]
lint:
    failed=0
    while IFS= read -r line; do
        case "$line" in ''|'#'*) continue ;; esac
        paths=${line%% :: *}
        rest=${line#* :: }
        regex=${rest%% :: *}
        message=${rest#* :: }
        # The pathspecs are split on purpose.
        if matches=$(git grep -nE --untracked "$regex" -- $paths); then
            printf '%s\n%s\n' "$message" "$matches"
            failed=1
        fi
    done < just/lint.rules
    exit "$failed"

# Count the admitted statements in each package.
[script("bash", "-euo", "pipefail")]
admits:
    total=0
    for dir in theories/*/; do
        count=$({ grep -rhoE --include='*.v' 'Admitted\.|Admit Obligations' "$dir" || true; } | wc -l)
        if [ "$count" -gt 0 ]; then
            echo "${dir%/} $count"
            total=$((total + count))
        fi
    done
    echo "total $total"

# Build, then check the compiled modules with rocqchk. Package names limit the modules checked.
[script("bash", "-euo", "pipefail")]
audit *packages: build
    built=_build/default/theories
    dirs=("$@")
    [ ${#dirs[@]} -gt 0 ] || dirs=("")
    modules=()
    for dir in "${dirs[@]}"; do
        [ -d "$built/$dir" ] || { echo "no compiled package $dir" >&2; exit 1; }
        while IFS= read -r file; do
            file=${file#"$built"/}
            file=${file%.vo}
            modules+=("{{ root }}.${file//\//.}")
        done < <(find "$built/$dir" -name '*.vo' | sort)
    done
    [ ${#modules[@]} -gt 0 ] || { echo "no compiled modules" >&2; exit 1; }
    report=$({{ cap }} rocqchk -silent -o -Q "$built" {{ root }} "${modules[@]}" 2>&1) \
        || { echo "$report"; exit 1; }
    echo "$report" | awk -f just/audit.awk just/audit.allow -
    echo "audited ${#modules[@]} modules"

# Check the files listed in just/frozen.sha256, when it has entries.
frozen:
    @if [ -s just/frozen.sha256 ]; then sha256sum --quiet -c just/frozen.sha256; fi

# Generate the HTML API reference for the theories.
doc *args:
    @just capped dune build -j {{ jobs }} @rocq-api "$@"

# Format every source file in place.
fmt:
    @just capped dune fmt

# Remove this worktree's build outputs.
clean:
    @just capped dune clean
