import "just/settings.just"

# List the developer workflows.
[default]
list:
    @just --list

# Set the persistent aggregate memory limit in bytes for every build command.
slice-cap size="10000000000":
    systemctl --user set-property galois.slice MemoryMax="$1" MemorySwapMax=0

# Build the redesigned theories and their extraction clients.
build-new *args:
    {{ capped }} dune build -j 2 @build-new "$@"

# Build the reference library, clients and tests.
build-legacy *args:
    {{ capped }} dune build -j 2 @legacy/default "$@"

# Build both libraries and the legacy extraction client.
build *args:
    {{ capped }} dune build -j 2 @build-new @legacy/default @extraction/default "$@"

# Build the new Rocq tests and clients and run the OCaml inline tests.
test-new *args:
    {{ capped }} dune build -j 2 @test-new @runtest "$@"

# Build both Rocq test suites and clients and run the OCaml inline tests.
test *args:
    {{ capped }} dune build -j 2 @test-new @legacy/tests/default @legacy/examples/default @runtest "$@"

# Check formatting, source hygiene, layout, theorem assumptions and typed extraction.
check *args:
    {{ capped }} bash -c 'dune build -j 2 @fmt @build-new @test-new @legacy/default @extraction/check @runtest tools/galois.exe "$@" && exec dune exec --no-build tools/galois.exe -- check' -- "$@"

# Generate the HTML API reference for the redesigned theories.
doc *args:
    {{ capped }} dune build -j 2 @rocq-api "$@"

# Remove this worktree's build outputs.
clean:
    {{ capped }} dune clean

# Run reproducible generated workloads and report experimental sizes and timings.
bench *args:
    {{ capped }} dune exec -j 2 tools/galois.exe -- bench "$@"

# Format every source file in place.
fmt:
    {{ capped }} dune fmt
