set shell := ["bash", "-euo", "pipefail", "-c"]
set positional-arguments

# Heavy commands share the persistent aggregate galois.slice memory limit when a systemd user
# session exists. Setting GALOIS_NO_SYSTEMD to any nonempty value forces the direct path.
cap := if env("GALOIS_NO_SYSTEMD", "") != "" { "" } else { `systemd-run --user --scope --quiet --slice=galois.slice -- true >/dev/null 2>&1 && echo 'systemd-run --user --scope --quiet --slice=galois.slice --' || true` }

# Parallel dune jobs.
jobs := env("GALOIS_JOBS", "2")

# The logical root of theories/.
root := "Galois"
