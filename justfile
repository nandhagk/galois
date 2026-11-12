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

# Build the theories.
build *args:
    @just capped dune build -j {{ jobs }} @theories/default "$@"

# Build the Rocq tests and examples.
test *args:
    @just capped dune build -j {{ jobs }} @tests/default @examples/default "$@"

# Build one Rocq source file under the memory cap.
vo file:
    @just capped dune build -j {{ jobs }} "${1%.v}.vo"

# Check the session sources without OCaml.
session-check: fmt-check build test lint frozen

# Check formatting, build, test, lint and the frozen files.
check: fmt-check build test lint frozen

# Print the words that just/lint.rules forbids in code and fail if there are any.
lint:
    @awk -f just/lint.awk just/lint.rules $(git ls-files -co --exclude-standard -- '*.v'); awk -f just/r13.awk $(git ls-files -co --exclude-standard -- '*.v')

# Count admitted statements and placeholder code by package and tag.
admits:
    @mapfile -d '' -t files < <(git ls-files -co --exclude-standard -z -- 'theories/**/*.v' 'tests/**/*.v' 'examples/**/*.v'); awk -f just/admits.awk /dev/null "${files[@]}"

# Print changed files outside a session's owned paths.
owned id range:
    @bash just/owned.sh "$@"

# Build, then check the compiled modules with rocqchk. Package names limit the modules checked.
audit *packages: build
    @bash just/audit.sh "$@"

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
