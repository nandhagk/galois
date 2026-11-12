# Reads the allowed axioms (just/audit.allow), then the rocqchk report. Prints each offending
# name and exits 1 unless the report has a CONTEXT SUMMARY whose blocks all pass.
BEGIN {
  while ((getline name < admitted_file) > 0) admitted[name] = 1
  close(admitted_file)
}
FILENAME == ARGV[1] {
  if ($0 !~ /^[[:space:]]*(#|$)/) allowed[$1] = 1
  next
}
/^CONTEXT SUMMARY/ { summary = 1 }
/^\* / {
  heading = substr($0, 3)
  sub(/:.*/, "", heading)
  inline = $0
  sub(/^[^:]*:[[:space:]]*/, "", inline)
  block = ""
  if (heading == "Axioms") block = "axioms"
  else if (heading ~ /type-in-type$/) block = "type-in-type"
  else if (heading ~ /unsafe \(co\)fixpoints$/) block = "unsafe (co)fixpoints"
  else if (heading ~ /positivity is assumed$/) block = "assumed positivity"
  if (block != "") {
    seen[block] = 1
    if (block != "axioms" && inline != "" && inline != "<none>") bad(block ": " inline)
  }
  next
}
block != "" && NF > 0 {
  if (block == "axioms") {
    if ($1 in admitted) print "admitted " $1
    else if (!($1 in allowed)) bad("unallowed axiom " $1)
  } else {
    bad(block ": " $1)
  }
}
function bad(message) {
  print message
  failed = 1
}
END {
  if (!summary) bad("no CONTEXT SUMMARY in the rocqchk report")
  else {
    required[1] = "axioms"; required[2] = "type-in-type"
    required[3] = "unsafe (co)fixpoints"; required[4] = "assumed positivity"
    for (i = 1; i <= 4; i++) if (!(required[i] in seen)) bad("the summary lacks the " required[i] " block")
  }
  exit failed
}
