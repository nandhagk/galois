set shell := ["bash", "-euo", "pipefail", "-c"]
set positional-arguments

# Heavy commands share the persistent aggregate galois.slice memory limit.
capped := "systemd-run --user --scope --quiet --slice=galois.slice --"
