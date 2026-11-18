# Usage: awk -f just/codes.awk FILE.v...
# Fails on a numeral written where a table code or a variable number goes. Such a numeral is
# the first argument of a syntax constructor that takes a code or a variable, after an
# optional type argument, or the code of a row (code, [cells]). The Egglog command derives
# programs from inductives and names every code, so files that use it never number one.
# Code is the text outside Rocq comments (which nest) and string literals, read by sentence.
FNR == 1 { depth = 0; instring = 0; sentence = "" }
{
    code = ""
    for (i = 1; i <= length($0); i++) {
        c = substr($0, i, 1); pair = substr($0, i, 2)
        if (instring) { if (pair == "\"\"") i++; else if (c == "\"") instring = 0 }
        else if (pair == "(*") { depth++; i++ }
        else if (depth > 0 && pair == "*)") { depth--; i++; code = code " " }
        else if (c == "\"") { instring = 1; code = code " " }
        else if (depth == 0) code = code c
    }
    if (sentence ~ /^[[:space:]]*$/) first = FNR
    sentence = sentence " " code
    while (match(sentence, /\.([[:space:]]|$)/)) {
        check(substr(sentence, 1, RSTART), first)
        sentence = substr(sentence, RSTART + 1); first = FNR
    }
}
function check(s, line) {
    gsub(/[[:space:]]+/, " ", s); sub(/^ /, "", s)
    if (s ~ /(^|[^A-Za-z0-9_'.])@?(Var|Fun|Prim|Make|Put|Let|OLat|PVar|PNode|POp|Holds|Equals|Computes|Derive|Assign|EApp) ([A-Za-z_][A-Za-z0-9_'.]* )?\(?[0-9]/ \
        || s ~ /\( ?[0-9]+(%positive)? ?, ?\[/)
        found = found FILENAME ":" line ": " s "\n"
}
END {
    if (found != "") {
        print "Name tables and variables. Derive the program from an inductive with the" \
            " Egglog command and use its generated codes.\n" found
        exit 1
    }
}
