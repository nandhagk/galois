# Usage: awk -v words="Class Instance" -f just/lint.awk FILE...
# Print "file:line: text" for each line where a word occurs as a whole word in code, meaning
# outside Rocq comments (which nest) and string literals. A string inside a comment is still
# a string, so a closing comment marker inside it does not close the comment.
BEGIN {
    n = split(words, list, " ")
    for (i = 1; i <= n; i++) forbidden[list[i]]
}

FNR == 1 { depth = 0; instring = 0 }

{
    code = ""
    for (i = 1; i <= length($0); i++) {
        c = substr($0, i, 1)
        pair = substr($0, i, 2)
        if (instring) {
            if (pair == "\"\"") i++
            else if (c == "\"") instring = 0
        } else if (pair == "(*") { depth++; i++ }
        else if (depth > 0 && pair == "*)") { depth--; i++; code = code " " }
        else if (c == "\"") { instring = 1; code = code " " }
        else if (depth == 0) code = code c
    }
    gsub(/[^A-Za-z0-9_']+/, " ", code)
    m = split(code, token, " ")
    for (i = 1; i <= m; i++)
        if (token[i] in forbidden) { print FILENAME ":" FNR ": " $0; break }
}
