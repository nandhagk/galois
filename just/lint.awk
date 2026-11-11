# Usage: awk -f just/lint.awk just/lint.rules FILE.v...
# A rule forbids its words, as whole words in code, in the files under its path prefixes.
# Code is the text outside Rocq comments (which nest) and string literals. A string inside a
# comment is still a string. A word that is a name does not count: part of a qualified name,
# or the word after Module, Type, Section, End, Import, Export or Include.
NR == FNR {
    if ($0 ~ /^#|^$/) next
    split($0, field, / :: /)
    rules++; paths[rules] = field[1]; message[rules] = field[3]
    n = split(field[2], list, " ")
    for (i = 1; i <= n; i++) forbidden[rules, list[i]]
    next
}
FNR == 1 {
    depth = 0; instring = 0
    for (r = 1; r <= rules; r++) {
        applies[r] = 0; n = split(paths[r], prefix, " ")
        for (i = 1; i <= n; i++) if (index(FILENAME, prefix[i] "/") == 1) applies[r] = 1
    }
}
{
    code = " "
    for (i = 1; i <= length($0); i++) {
        c = substr($0, i, 1); pair = substr($0, i, 2)
        if (instring) { if (pair == "\"\"") i++; else if (c == "\"") instring = 0 }
        else if (pair == "(*") { depth++; i++ }
        else if (depth > 0 && pair == "*)") { depth--; i++; code = code " " }
        else if (c == "\"") { instring = 1; code = code " " }
        else if (depth == 0) code = code c
    }
    delete found; prev = ""; end = 1; pos = 1
    while (match(substr(code, pos), /[A-Za-z0-9_']+/)) {
        start = pos + RSTART - 1; word = substr(code, start, RLENGTH); pos = start + RLENGTH
        qualified = substr(code, start - 1, 1) == "." || substr(code, pos, 2) ~ /^\.[A-Za-z_]/
        declared = prev ~ /^(Module|Type|Section|End|Import|Export|Include)$/ \
            && substr(code, end, start - end) ~ /^[ \t]*$/
        if (!qualified && !declared) found[word]
        prev = word; end = pos
    }
    for (r = 1; r <= rules; r++)
        for (word in found)
            if (applies[r] && ((r, word) in forbidden)) {
                matches[r] = matches[r] FILENAME ":" FNR ": " $0 "\n"; break
            }
}
END {
    for (r = 1; r <= rules; r++)
        if (matches[r] != "") { print message[r] "\n" matches[r]; failed = 1 }
    exit failed
}
