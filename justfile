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

# Check formatting, then build, then test, then run the checker.
check *args: fmt-check build test
    @just capped dune exec -j {{ jobs }} checker/main.exe -- check "$@"

# Build, then run the final checker audit. Arguments go to the checker, for example --only Cost,Bits.
audit *args: build
    @just capped dune exec -j {{ jobs }} checker/main.exe -- check --final "$@"

# List the admitted statements the checker finds.
admits *args:
    @just capped dune exec -j {{ jobs }} checker/main.exe -- admits "$@"

# Generate the HTML API reference for the theories.
doc *args:
    @just capped dune build -j {{ jobs }} @rocq-api "$@"

# Format every source file in place.
fmt:
    @just capped dune fmt

# Remove this worktree's build outputs.
clean:
    @just capped dune clean
