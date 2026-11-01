import "just/settings.just"

# List the developer workflows.
[default]
list:
    @just --list

# Set the persistent aggregate memory limit in bytes for every build command.
slice-cap size="9000000000":
    systemctl --user set-property galois.slice MemoryMax="$1" MemorySwapMax=0

# Build the given dune targets, or everything when none are given.
build *targets:
    {{ capped }} dune build -j 2 "$@"

# Build the Rocq tests and examples, then run the OCaml inline tests.
test *args:
    {{ capped }} dune build -j 2 @tests/default @examples/default @runtest "$@"

# Check formatting, source hygiene, layout, theorem assumptions and typed extraction.
check *args:
    {{ capped }} bash -c 'dune build -j 2 @fmt @theories/default @examples/default @tests/default @extraction/check tools/galois.exe "$@" && exec dune exec --no-build tools/galois.exe -- check' -- "$@"

# Run reproducible generated workloads and report experimental sizes and timings.
bench *args:
    {{ capped }} dune exec -j 2 tools/galois.exe -- bench "$@"

# Format every source file in place.
fmt:
    {{ capped }} dune fmt
