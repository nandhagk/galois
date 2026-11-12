BEGIN { split("CONVERT STUB PLAN-DEFECT SIG-QUESTION OPEN plain STUB-CODE", tags, " ") }
{
  package = FILENAME
  sub(/^[^/]+\//, "", package)
  sub(/\/.*/, "", package)
  if ($0 ~ /Admitted[.]/) {
    tag = "plain"
    for (i = 1; i <= 5; i++)
      if ($0 ~ ("\\(\\*[[:space:]]*" tags[i] "([:[:space:]]|\\*)")) tag = tags[i]
    count[package, tag]++; total[tag]++; packages[package] = 1
  }
  if ($0 ~ /\(\*[[:space:]]*STUB-CODE([:[:space:]]|\*)/) {
    count[package, "STUB-CODE"]++; total["STUB-CODE"]++; packages[package] = 1
  }
}
END {
  for (package in packages) {
    printf "%s", package
    for (i = 1; i <= 7; i++) printf " %s=%d", tags[i], count[package, tags[i]]
    print ""
  }
  printf "total"
  for (i = 1; i <= 7; i++) printf " %s=%d", tags[i], total[tags[i]]
  print ""
}
