# Check complete Rocq sentences after removing nested comments and strings.
FNR == 1 { depth = 0; string = 0; sentence = ""; level = 0 }
{
    code = ""
    for (i = 1; i <= length($0); i++) {
        c = substr($0, i, 1); pair = substr($0, i, 2)
        if (string) { if (pair == "\"\"") i++; else if (c == "\"") string = 0 }
        else if (pair == "(*") { depth++; i++ }
        else if (depth && pair == "*)") { depth--; i++ }
        else if (!depth && c == "\"") string = 1
        else if (!depth) code = code c
        else code = code " "
    }
    sentence = sentence " " code
    while (match(sentence, /\.[[:space:]]|\.$/)) {
        command = substr(sentence, 1, RSTART - 1)
        sentence = substr(sentence, RSTART + 1)
        check(command)
    }
}
function issue(reason) { print FILENAME ":" FNR ": " reason ": " command; failed = 1 }
function check(s, name, kind, tail) {
    gsub(/[[:space:]]+/, " ", s); sub(/^ /, "", s)
    if (s ~ /(^| )Require( |$)/ && s !~ /^From [A-Za-z0-9_'.]+ Require( |$)/)
        issue("Require without From")
    if (s ~ /(^| )Declare Module( |$)/) issue("Declare Module")
    if (s ~ /^Section /) { level++; types[level] = level > 1 ? types[level - 1] : 1; functor[level] = 0; return }
    if (s ~ /^End /) { if (level > 0) level--; return }
    if (s ~ /^Module( Type)? /) {
        tail = s; sub(/^Module( Type)? +[A-Za-z0-9_']+/, "", tail)
        gsub(/\([^()]*\)/, "", tail)
        if (tail ~ /^[[:space:]]*:([^=]|$)/) issue("module ascription with colon")
        if (s ~ /\([^)]*:[^)]*[_]TIME([ )]|$)/) issue("functor parameter uses _TIME")
    }
    if (s ~ /^Module Type /) {
        name = s; sub(/^Module Type +/, "", name); sub(/[^A-Za-z0-9_'].*/, "", name); moduletypes[name] = 1
        if (s !~ /:=/) { level++; types[level] = 1; functor[level] = 0 }
        return
    }
    if (s ~ /^Module /) {
        tail = s; sub(/^Module +[A-Za-z0-9_']+/, "", tail)
        if (s !~ /:=/) { level++; types[level] = 0; functor[level] = tail ~ /^ *\(/ }
        return
    }
    if (s ~ /^Include / && level && !types[level]) {
        name = s; sub(/^Include +/, "", name); sub(/ .*/, "", name)
        if (name !~ /_SPEC$/) {
            includes++; incname[includes] = name; incfile[includes] = FILENAME
            incline[includes] = FNR; inccommand[includes] = command
        }
    }
    if (s ~ /^(Inductive|Record|Variant) /)
        for (kind = 1; kind <= level; kind++) if (functor[kind]) {
            issue("data declaration inside functor"); break
        }
}
END {
    for (i = 1; i <= includes; i++) {
        name = incname[i]; sub(/^.*\./, "", name)
        if (name in moduletypes || name ~ /^[A-Z][A-Z0-9_]*$/) {
            print incfile[i] ":" incline[i] ": Include of non-SPEC module type: " inccommand[i]
            failed = 1
        }
    }
    exit failed
}
