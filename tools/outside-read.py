#!/usr/bin/env python3
"""Read an outside proof file as TEXT and say whether it is only declarations and proofs.

    python3 -I tools/outside-read.py <file saved from a pull request>

A FIRST FILTER, not what makes an outside file safe: that is the sandbox it is built in and the
checker's own rules. It never builds, imports or executes anything: it reads bytes.
The RAW text is searched, comments included, and nothing is stripped: a stripper can be led
astray by a character or string literal (red team, 2026-11-23), so a forbidden word inside a
comment is a FLAG too. Inside a comment only the column-0 rule and a lone # are lifted. Exit 0 PLAIN, 1 FLAG, 2 unreadable.
NO TEXT OF THE FILE IS PRINTED (a founder's law, 2026-11-23: nothing an outsider typed reaches
a seat): a flag is its line number and its reason. The code around a flag, with comments blanked,
is shown only by tools/outside-view.py.

KNOWN LIMIT (red team, read 2026-11-23, YES as a first filter): Lean does not need a newline
between commands, so two commands on one line, or an indented command, are judged by the
forbidden list alone. Against a deliberately formatted file that list is the whole defence
here, and it cannot be complete: the sandbox is what makes a build safe. PLAIN means "nothing
this reader knows to look for", never "safe to build on this machine".
"""
import re, sys

# The four limit options are not flags: they lift Lean's own budgets and run nothing.
LIMIT = re.compile(r"set_option (maxRecDepth|maxHeartbeats|synthInstance\.maxSize|synthInstance\.maxHeartbeats) [0-9]+ in(?![A-Za-z0-9_])")
ALLOWED = re.compile(r"(import |namespace |end( |$)|section( |$)|open |variable( |$)|universe |omit |include |/-|-/|--"
                     r"|(@\[(local )?simp\] )?((private|protected) )?(noncomputable )?(theorem|lemma|def|abbrev)( |$)|noncomputable section"
                     r"|((private|protected) )?(structure|inductive) "
                     r"|[\]})]+[ \t]*$"  # a lone closing bracket, brace or parenthesis (a data list's end)
                     r"|termination_by( |$)|decreasing_by( |$)|where$)")  # why a recursion ends: they run no code (PR 625, 2026-11-23)
FORBIDDEN = re.compile(r"""(?x) " | [\u00ab\u00bb] | simproc | builtin_ | native | bv_decide | ofReduce | reduceNat | reduceBool
 | \b(Lean|System|IO|Elab|Meta|Lake|FS|Process)\b | _root_ | RealWorld | BaseIO | \bEIO\b
 | include_str | notation | [A-Za-z_][A-Za-z0-9_']*[A-Za-z0-9_']% | polyrith | initialize | run_cmd | run_tac | run_elab | run_meta | by_elab | \belab | \bmacro | \bsyntax\b
 | \battribute\b | set_option | \binstance\b | \baxiom\b | \bopaque\b | unsafe | \bpartial\b | sorry | \badmit\b | \#(?!\[)
 | implemented_by | extern | \bderiving\b | \bstructure\b | \binductive\b | \bclass\b | \bmutual\b | \bexport\b | \bscoped\b | \blocal\b
 | `\( | \$\( | %\[ | @\[ | register_ | declare_ | lcProof | lcUnreachable | \binfix | \bprefix\b | \bpostfix\b | binder_predicate | unif_hint | ^\s*add_\w+ | \balias\b | \bexample\b | unseal | compile_inductive | irreducible_def """)
OK_ATTR = re.compile(r"@\[(local )?simp\]")
# SHAPES RULED SAFE BY HAND READS (operator's throughput question under 0j, 2026-11-23; every hand
# read of these came back clean): a data type declared at column 0, and its derived instances from
# Lean's own handlers. They run none of the author's code. The rest of such a line is still read.
DATA_DECL = re.compile(r"^((private|protected) )?(structure|inductive) (?=[A-Za-z_])")
CORE_DERIVE = re.compile(r"\s*deriving (DecidableEq|Repr|BEq|Hashable|Inhabited)(, (DecidableEq|Repr|BEq|Hashable|Inhabited))*\s*")
# A CONTINUATION LINE AT COLUMN 0 (eleven accepted files were flagged for it alone, 2026-11-24):
# a line of a statement or a proof that the author did not indent. It is PLAIN only when (1) a
# theorem, lemma, def or abbrev was opened at column 0 above and no other column-0 command or
# comment has come since, (2) no block comment is open, by a count that can only err towards
# "open", and (3) the line STARTS with a bracket, a quantifier, an arrow, a connective or a
# colon: no Lean command starts with one of these. The words of the line are still read against
# the forbidden list like any other line. Comment prose is never made plain by this.
CHAR_LIT = re.compile(r"(?<![A-Za-z0-9_'.])'(\\.|[^\\'\n])'")
DECL_OPEN = re.compile(r"(@\[(local )?simp\] )?((private|protected) )?(noncomputable )?(theorem|lemma|def|abbrev)( |$)")
CONT_START = re.compile(r"(\(|\{|\[|\u2983|\u2200|\u2203|\u2192|\u2194|\u2227|\u2228|\u00ac|:=?(?=[ \t]|$)|have(?=[ \t]))")
# LIMIT OPTIONS LEADING A LINE (2026-11-24: 288 lines in nine accepted files): one or more scoped
# limit options chained on one line, then nothing, or the declaration they scope on the same line.
LIMIT_LEAD = re.compile(r"(?:%s(?: |$))+" % LIMIT.pattern)
# AN INSTANCE OF A DECIDABILITY CLASS (red team ruling, 2026-11-24 19:32Z): an instance of Decidable,
# DecidableEq, DecidablePred or DecidableRel is benign WHATEVER it is stated on and whatever its binders:
# any two decision procedures for one proposition give the same answer, provably, so such an instance can
# change how a term computes but never what a statement means; the kernel checks every use. PLAIN only
# when all hold: the line is at column 0 outside any comment; it reads `[noncomputable ][local ]instance`,
# an optional name, optional binders, then ` : ` at bracket depth 0 and one of the four class names; no
# priority. Only the keywords before the name are lifted: the name, the binders, the class's arguments and
# the rest of the line are read against the forbidden list as always. Any OTHER class stated on a name
# the file made by def or abbrev is never plain (an abbreviation unfolds to a library class or type):
# the own-type rule below admits only names a `structure` or `inductive` line declared.
DECIDE_HEAD = re.compile(r"((noncomputable|private|protected) )?(local )?instance(?=[ (\[{])")
DECIDE_CLASS = re.compile(r"(Decidable|DecidableEq|DecidablePred|DecidableRel)(?=[ (]|$)")
def decide_instance(line, following=()):
    """The end of the lifted keywords if the line is a decidability instance, else None. R-f (red team,
    2026-11-25): when the type does not end on the line, the following CODE lines are joined (at most 15) up to
    the first := or where at depth 0, and the same test is applied to the joined header."""
    if following and not re.search(r'(?<![A-Za-z0-9_])where$| :=', line):
        joined = line
        for nxt in list(following)[:15]:
            joined += ' ' + nxt.strip()
            if re.search(r' :=|(?<![A-Za-z0-9_])where\b', joined): break
        r = decide_instance(joined)
        return None if r is None else r
    m = DECIDE_HEAD.match(line)
    if not m or 'priority' in line: return None
    depth, i = 0, m.end()
    while i < len(line):
        c = line[i]
        if c in '([{⦃': depth += 1
        elif c in ')]}⦄': depth -= 1
        elif c == ':' and depth == 0:
            if line[i + 1:i + 2] == '=': return None   # `:=` before any type: not this shape
            if line[i - 1:i] != ' ' or line[i + 1:i + 2] != ' ': return None
            k = DECIDE_CLASS.match(line, i + 2)
            if not k: return None
            # The class must be the HEAD of the whole type and the type must END on this line (red team,
            # 19:48Z: `Decidable p -> C a` starts with the class word and is an instance of C): after
            # the class word, at depth 0, the line reaches ` :=` or ends with ` where`, with no arrow, no
            # forall sign, no comma and no second colon on the way.
            d, j = 0, k.end()
            while j < len(line):
                c = line[j]
                if c in '([{\u2983': d += 1
                elif c in ')]}\u2984': d -= 1
                elif d == 0:
                    if line.startswith(' :=', j - 1) and c == ':': return m.end()
                    if c in ',:\u2200\u2192' or line.startswith('->', j): return None
                if d < 0: return None
                j += 1
            return m.end() if d == 0 and re.search(r' where$', line) and not re.search('[,:\u2200\u2192]|->', line[k.end():len(line) - 6]) else None
        if depth < 0: return None
        i += 1
    return None
# PACKED NUMERIC DATA AT COLUMN 0 (red team, in principle, 2026-11-24; three accepted files held for it):
# a line of only decimal literals, commas, the four brackets ( ) [ ] and spaces, inside an open
# declaration, no literal over 20 digits and at most 4,096 literals on the line. Nothing on such a line
# can name or run anything; it keeps the declaration open like any continuation line.
NUM_LINE = re.compile(r"[0-9\[\]\(\), \t]*[0-9][0-9\[\]\(\), \t]*")
# (d-hex), red team 01:34Z: a digit-first column-0 line inside an open bracket holding only numerals, decimal or
# hexadecimal (0x, then digits and a to f; lower case only, stricter than ruled), commas, spaces and closing brackets.
HEX_LINE = re.compile(r"(?:0x[0-9a-f]+|[0-9]+|[ \t,\])}])+")
def hex_line(line):
    """(d-hex): numerals only, hexadecimal ones any length, decimal ones at most 20 digits as the numeric rule."""
    if not line[:1].isdigit() or not HEX_LINE.fullmatch(line): return False
    nums = re.findall(r"0x[0-9a-f]+|[0-9]+", line)
    return len(nums) <= 4096 and all(n.startswith("0x") or len(n) <= 20 for n in nums)
def numeric_line(line):
    if not NUM_LINE.fullmatch(line): return False
    runs = re.findall(r"[0-9]+", line)
    return len(runs) <= 4096 and all(len(r) <= 20 for r in runs)

def comment_depth(line, depth):
    """Block comment depth after this line, read left to right. Outside a comment only an opener
    counts (a closer there is not one to Lean, and counting it first once hid the opener in
    minus-slash-minus: red team, 2026-11-24); an opener inside a line comment counts too, so the
    count errs towards open. The PLAIN shapes also rely on the older flag for a comment marker
    inside a line: a file with such a marker is never clean, whatever this count says."""
    i = 0
    while i < len(line) - 1:
        two = line[i:i + 2]
        if two == '/-': depth += 1; i += 2
        elif two == '-/' and depth > 0: depth -= 1; i += 2
        else: i += 1
    return depth

# AN INSTANCE OF A STRUCTURAL CLASS ON THE FILE'S OWN TYPE (2026-11-24: the one flag left on a
# family of large accepted files). PLAIN only when all hold: the line is at column 0 outside any
# comment; it reads `instance [name] : <Class> <T>` or `<Class> (<T> <plain arguments>)`, with no
# binders and no priority; <Class> is on the short list below; <T> is an unqualified name that a
# column-0 `structure` or `inductive` line of THIS file declared earlier, outside any comment,
# under exactly the namespaces and sections open at the instance line (so the name cannot mean a
# library type). The rest of the line is read against the forbidden list as always. An instance
# on a library type stays a flag (red team, 2026-11-24 09:59Z).
# A `variable` line can bind the type's name as a local type, and the instance would then be one
# for EVERY type (red team, 2026-11-24): so the word `variable` anywhere on a line forgets every
# own type declared so far. DEPENDENCY: the namespace and section stack is right only because the
# public guard refuses an indented namespace, section or end line.
OWN_INSTANCE = re.compile(r"instance( [A-Za-z_][A-Za-z0-9_']*)? : (BEq|LawfulBEq|DecidableEq|Repr|Inhabited|Hashable|Ord|Add|Mul|Neg|Sub|Div|Mod|Inv|One|Zero|Pow|SMul|LE|LT|Max|Min|Nonempty|Fintype) "
                          r"(?:(?P<t>[A-Za-z_][A-Za-z0-9_']*)|\((?P<u>[A-Za-z_][A-Za-z0-9_']*)( [A-Za-z0-9_']+)*\))(?= where$| :=|$)")
DATA_NAME = re.compile(r"((private|protected) )?(structure|inductive) (?P<n>[A-Za-z_][A-Za-z0-9_']*)(?![A-Za-z0-9_'.])")
SCOPE_OPEN = re.compile(r"(namespace|section|noncomputable section)( (?P<n>[A-Za-z_][A-Za-z0-9_'.]*))?[ \t]*$")
SCOPE_END = re.compile(r"end( [A-Za-z_][A-Za-z0-9_'.]*)?[ \t]*$")

COMMENT_LINK = re.compile(r"(?i)://|\bwww\.|\bhttps?\b|[A-Za-z0-9._%+-]+@[A-Za-z0-9-]+\.[a-z]{2,}|\b[a-z0-9-]+\.(com|org|net|io|dev|ai|sh|xyz|me|gg|ly)\b|\b\d{1,3}(\.\d{1,3}){3}\b")
# A TRIPWIRE, not the defence (red team, 2026-11-24): no seat reads a comment (the view blanks
# them, this reader prints none); the list protects the public tree, which other people's tools
# read. It misses plain imperatives and is not to be chased. A flag from it is an outsider sign:
# its pull request number and line number go to the red team, never its text.
COMMENT_ADDRESS = re.compile(r"(?i)\b(you|your|yours|please|instruction|instructions|prompt|assistant|agent|agents|llm|reviewer|maintainer|curl|wget|download|install|execute|password|credential|credentials|secret|token|click|visit|contact|email|sudo|bash|pip|npm|ssh|chatgpt|gpt|claude)\b")

# The two verbs for setting something aside are common in mathematics ("ignore the constant"):
# alone they are plain; they flag only beside another word of the list or one of the words an
# order to a reader goes with (the tripwire's first hit was this false alarm, 2026-11-24).
SET_ASIDE = re.compile(r"(?i)\b(ignore|disregard)\b")
SET_ASIDE_WITH = re.compile(r"(?i)\b(previous|prior|above|earlier|everything|rules)\b")

# Imports: only the library and the project's own modules (the public guard narrows further, to
# the modules a gap lists). Anything else is a flag here.
IMPORT_OK = re.compile(r"import (Mathlib|PEqualNP)(\.[A-Za-z0-9_]+)*\s*")

# THE RED TEAM'S STANDING SHAPES (a) to (h), 2026-11-25, each applied here by the script and tested in the suite.
# (a) a column-0 line whose first character cannot begin a command or a comment (not a letter, underscore, @, #, /,
#     -, the opening double angle quote) continues the declaration above: plain, when the line above is code.
# (c) a backtick followed by an opening bracket is comment text inside a comment (all three comment forms): lifted there.
# (d) a column-0 line inside an open bracket of the code above, whose non-ASCII characters are only Lean's own kinds.
# (e) an addressing word in a comment flags only beside a danger shape: second person, a listed imperative, a path,
#     a link, a command shape. The one-word tripwire alone is plain.
# (f) see decide_instance: an instance type that does not end on its line is joined to the next code lines.
# (g) a link in a comment to a pull request or issue of OUR organisation on the code-hosting service is a reference.
# (h) 'noncomputable' alone on a column-0 line with 'section' first on the next line: one command over two lines.
RA_START = set("_@#/-«")
LEAN_UNICODE = {'Sm', 'So', 'Ps', 'Pe', 'Ll', 'Lu', 'No'}
DANGER_SECOND = re.compile(r"(?i)\b(you|your|yours)\b")
DANGER_IMPER = re.compile(r"(?i)\b(please|ignore|disregard|execute|install|download|click|visit|contact|run|curl|wget|sudo|bash|pip|npm|ssh)\b")
DANGER_PATH = re.compile(r"(/[A-Za-z0-9_.-]+){2,}|~/")
DANGER_CMD = re.compile(r"(^|\s)(\$ |#!|sudo |rm -|curl |wget |python3? |node |git )")
# (e), stricter than ruled: a model or assistant name is a sixth danger shape (the suite's "-- claude, read this" stays a flag).
DANGER_MODEL = re.compile(r"(?i)\b(prompt|assistant|agent|agents|llm|chatgpt|gpt|claude|reviewer|maintainer)\b")
# E-fix (red team, 01:23Z): 'instruction' and its plural left the model-name shape; alone in a comment they are an
# ordinary word, and they flag only before a colon or beside another addressing word (or a danger shape, as every word).
INSTR = re.compile(r"(?i)\binstructions?\b")
INSTR_COLON = re.compile(r"(?i)\binstructions?\s*:")
RA_ANYWHERE = set('|,)]}\u27e9\u2984\u2986')   # (a'): a line that starts with one of these cannot begin anything
OUR_LINK = re.compile(r"https?://github\.com/open-goat/[A-Za-z0-9._-]+/(pull|issues)/[0-9]+(?=$|[\s).,;:\]])")
# (g2), red team 02:51Z: the bare word http or https, with no scheme mark, domain, www, mail or number shape, is not a link.
def has_link(t): return any(not re.fullmatch(r"(?i)https?", m.group(0)) for m in COMMENT_LINK.finditer(t))
# (e2), red team 02:51Z: these three are ordinary words of mathematics; one of them alone on a comment line, with no other
# addressing word and no other danger shape, is plain, and the same token does not count twice.
E2_WORDS = {"contact", "visit", "execute"}
E2_RE = re.compile(r"(?i)\b(contact|visit|execute)\b")
# (l), red team 03:06Z: a second-person word alone on a comment line (no other addressing word, none of the other
# danger shapes) is plain ONLY when the line holds none of these request words of ours, whole words, any case, and has at
# most 20 words. Any of them there: it stays flagged and the file waits for a hand reader the operator names.
L_REQUEST = re.compile(r"(?i)\b(accept|approve|merge|land|skip|trust|mark|treat|consider|must|should|need|ensure|make|give|set|use|add|remove|delete|change|rewrite|output|respond|reply|answer|say|tell|report|grade|score|pass|verify|confirm|do|never|always|stop|read|follow|open|send)\b")
L_SECOND = {"you", "your", "yours"}
# (m), red team 03:56Z: a column-0 code line outside comments and brackets that begins with a name which is not a
# command word is a term carried on to an unindented line. It is plain only inside an open declaration, with no quote,
# no comment marker, every character a letter, digit, _ . ' , a bracket, an operator or a space, and no piece of any name
# on it (split on _ . ' and case change) on the addressing list or the request words. (The gate asks the reader only
# about accepted files; acceptance is the gate's condition, not the reader's.)
M_NAME = re.compile(r"[^\W\d][\w.']*")
M_OK = set("_.' ()[]{}\u27e8\u27e9+-*/=<>,:;|&^%!?@$~\\")
# Stricter than ruled (03:59Z), to keep the older refuse cases and P1: the previous code line must leave the term open
# (it ends with an operator, a colon, a comma, an open bracket, := or =>), the first word is not a term keyword, and no
# 'by' has appeared in the declaration (a tactic block is never carried this way).
M_KEYWORDS = {'let', 'letI', 'have', 'haveI', 'show', 'suffices', 'fun', 'calc', 'match', 'if', 'then', 'else', 'do', 'by', 'from', 'at', 'with', 'using', 'return', 'obtain', 'nomatch', 'nofun'}
M_CONT_END = re.compile(r"(:=|=>|[-+*/=<>,:(\[{\u27e8|&^%\u2264\u2265\u2260\u2227\u2228\u2192\u2194\u2218\u00d7\u2229\u222a\u2208\u2209\u2286\u2282\u00b7\u2022])$")
M_BY = re.compile(r"(?<![\w.'])by(?![\w'])")
# N1, red team 2026-11-25: a name is cut into pieces by MAXIMAL RUNS OF LETTERS (digits, _ . ' and every other
# character end a piece), and a run is cut again at each case change: lower to upper ('mergeThis': merge, This) and the
# last capital of an upper-case run that a lower-case letter follows ('XMLParser2run': XML, Parser, run). Each piece is
# tested against both word lists as a whole word, any case.
def name_pieces(text):
    out = []
    for run in re.findall(r"[^\W\d_]+", text):
        cur = run[0]
        for k in range(1, len(run)):
            a, c = run[k - 1], run[k]
            nxt = run[k + 1] if k + 1 < len(run) else ''
            if (a.islower() and c.isupper()) or (a.isupper() and c.isupper() and nxt.islower()):
                out.append(cur); cur = c
            else: cur += c
        out.append(cur)
    return out
def m_pieces_hit(line):
    return any(COMMENT_ADDRESS.fullmatch(p) or L_REQUEST.fullmatch(p) for n in M_NAME.findall(line) for p in name_pieces(n))
import unicodedata

def main(path):
    try: raw = open(path, 'rb').read()
    except OSError as e: print(f'UNREADABLE: {e}'); return 2
    flags = []
    if len(raw) > 512 * 1024: flags.append('larger than 512 KiB')
    # (i), red team 01:07Z: a carriage return immediately before a line feed is a line ending and is dropped before
    # reading; any other control character, a lone carriage return included, still flags.
    raw = raw.replace(b'\r\n', b'\n')
    if re.search(rb'[\x00-\x08\x0b-\x1f\x7f]', raw): flags.append('control characters in the file')
    try: text = raw.decode('utf-8')
    except UnicodeDecodeError: print('FLAG: not UTF-8'); return 1
    if re.search('[\u200b-\u200f\u202a-\u202e\u2060-\u2069\ufeff]', text): flags.append('invisible or direction-changing characters')
    # Letters that look like Latin ones (Cyrillic, Armenian, Cherokee, fullwidth): no proof here
    # needs them, and they can dress a command word as a name or a name as a command word.
    for no, line in enumerate(text.split('\n'), 1):
        if re.search('[\u0400-\u052f\u0530-\u058f\u13a0-\u13ff\uff01-\uff5e]', line): flags.append(f'line {no}: letters that look like Latin ones')
    theorems = 0
    # COMMENTS (2026-11-24). Two CODE rules are lifted inside a comment and no more: the column-0
    # rule (prose in a block comment may start at column 0) and a lone # (one not followed by a
    # letter). EVERY WORD on the forbidden list is still a flag inside a comment, so a wrong
    # reading of where a comment is can never let a command word through. And the reading is
    # exact in any file that ends PLAIN, because the marker rule below flags every marker that
    # is not where a plain comment has it: a block opens only with /- as the FIRST characters
    # of a line (after spaces), where Lean always reads an opener; it closes only with -/ as the
    # LAST; a line holding both -- and a block marker is flagged; a string cannot hide a marker
    # because a double quote in code is itself a flag. A line comment is read only where -- is
    # the first thing on a line or follows a space, where Lean always reads one; a -- glued to
    # other characters is treated as code. A block never closed is a flag.
    # Rules ABOUT comments stay: a link, words that address a reader or ask for an action, a very
    # long line, and a very large total are flags for a mind; so are the character rules above.
    decl_start = 0
    in_decl, depth = False, 0
    comment_chars = 0; comment_signal = False
    scope, own = [], {}   # open namespaces and sections; the file's own data types and where each was declared
    ALL = text.split('\n'); DSTART = []; _d = 0
    for _l in ALL: DSTART.append(_d); _d = comment_depth(_l, _d)
    def code_line(i): return 0 <= i < len(ALL) and DSTART[i] == 0 and not ALL[i].lstrip().startswith(('--', '/-'))
    bdepth, last_code = 0, False   # bracket depth over CODE (for d); whether the last non-blank line was code (for a)
    by_memo = [-1, 0, False]   # M2: (decl_start, lines scanned up to, a 'by' seen): each line is scanned once per declaration
    def decl_has_by(no):
        if not in_decl: return True
        if by_memo[0] != decl_start: by_memo[:] = [decl_start, decl_start, False]
        while not by_memo[2] and by_memo[1] < no - 1:
            k = by_memo[1]; by_memo[1] += 1
            if code_line(k) and M_BY.search(re.sub(r'(?<=[ \t])--.*$', '', ALL[k])): by_memo[2] = True
        return by_memo[2]
    for no, line in enumerate(ALL, 1):
        st = line.strip()
        before, depth = depth, comment_depth(line, depth)
        col0 = line[:1] not in ('', ' ', '\t')
        lead = LIMIT_LEAD.match(line)
        rest = line[lead.end():] if lead else line   # the line after its leading limit options
        limited = bool(lead) and (rest == '' or bool(DECL_OPEN.match(rest)))
        cont = col0 and in_decl and before == 0 and depth == 0 and bool(CONT_START.match(line))
        numlit = col0 and in_decl and before == 0 and depth == 0 and numeric_line(line)
        hexlit = col0 and before == 0 and depth == 0 and bdepth > 0 and hex_line(line)   # (d-hex)
        cont = cont or numlit or hexlit
        follow = [ALL[k] for k in range(no, min(no + 15, len(ALL))) if code_line(k)] if (col0 and before == 0 and depth == 0) else ()
        decide = decide_instance(line, follow) if (col0 and before == 0 and depth == 0) else None
        is_code_line = before == 0 and not st.startswith(('--', '/-'))
        # (a) and (d) are applied only while a declaration is open (in_decl or an open bracket), and a line that starts
        # with a digit stays under the numeric rule: the earlier refuse cases of the suite hold (stricter than ruled).
        # P1 (red team, 01:04Z): a new command or declaration never starts inside an open bracket, so the depth is
        # reset at every column-0 code line that begins one; an unclosed bracket cannot carry (d) past it.
        if col0 and is_code_line and (ALLOWED.match(line) or DECL_OPEN.match(line)): bdepth = 0
        open_decl = in_decl or bdepth > 0
        # Stricter than ruled, to keep two older refuse cases: a colon-first line goes by the continuation rule (a space after
        # the colon), and a line that opens with closing brackets must not continue with a plain word (prose after a bracket).
        after_close = re.sub(r'^[\])}\u27e9\u2984]+\s*', '', line) if line[:1] in ')]}\u27e9\u2984' else None
        prose_after = after_close is not None and after_close[:1].isalpha()
        ra = col0 and is_code_line and (open_decl or line[:1] in RA_ANYWHERE) and line[:1] not in RA_START and not line[:1].isalpha() and not line[:1].isdigit() and line[:1] != ':' and not prose_after and last_code and all(unicodedata.category(c) in LEAN_UNICODE for c in line if ord(c) > 127)
        rd = col0 and is_code_line and bdepth > 0 and not line[:1].isdigit() and not prose_after and all(unicodedata.category(c) in LEAN_UNICODE for c in line if ord(c) > 127)
        rh = col0 and is_code_line and st == 'noncomputable' and no < len(ALL) and ALL[no].split()[:1] == ['section']
        prev_code = next((re.sub(r'(?<=[ \t])--.*$', '', ALL[k]).rstrip() for k in range(no - 2, -1, -1) if code_line(k) and ALL[k].strip()), '')
        first_word = (M_NAME.match(line) or [''])[0]
        rm = (col0 and is_code_line and in_decl and bdepth == 0 and line[:1].isalpha() and not ALLOWED.match(line)
              and first_word not in M_KEYWORDS and bool(M_CONT_END.search(prev_code))
              and '"' not in line and '--' not in line and '/-' not in line
              and all(c.isalnum() or c in M_OK or unicodedata.category(c) in LEAN_UNICODE for c in line)
              and not m_pieces_hit(line) and not decl_has_by(no))   # (m); M2: the 'by' scan last, lazily
        cont = cont or ra or rd or rh or rm   # a line passed by (a), (d), (h) or (m) keeps the declaration open
        derive = col0 and before == 0 and depth == 0 and bool(CORE_DERIVE.fullmatch(line))
        own_inst = None
        if re.search(r'\bvariable\b', line): own.clear()
        if col0 and before == 0 and depth == 0:
            m = SCOPE_OPEN.match(line)
            if m: scope.append(m.group(0).strip())
            elif SCOPE_END.match(line) and scope: scope.pop()
            m = DATA_NAME.match(line)
            if m: own[m.group('n')] = tuple(scope)
            m = OWN_INSTANCE.match(line)
            if m and own.get(m.group('t') or m.group('u'), None) == tuple(scope): own_inst = m
        if col0 and not cont: in_decl = bool(DECL_OPEN.match(rest)) and (rest is line or limited) and before == 0 and depth == 0
        if col0 and not cont and in_decl: decl_start = no - 1   # (m): where this declaration began
        if '/-' in line or '-/' in line or st.startswith('--'): in_decl = False
        inside = before > 0   # this line lies in a block comment opened on an earlier line
        if inside or st.startswith('--') or st.startswith('/-'): code, ctext = '', line
        else:
            m = re.search(r'(?<=[ \t])--', line)
            code, ctext = (line[:m.start()], line[m.start():]) if m else (line, '')
        if ctext:
            comment_chars += len(ctext)
            clink = OUR_LINK.sub(' ', ctext)   # (g)
            if has_link(clink): flags.append(f'line {no}: a link or an address inside a comment')   # (g2)
            danger = DANGER_SECOND.search(clink) or DANGER_IMPER.search(clink) or DANGER_PATH.search(clink) or has_link(clink) or DANGER_CMD.search(clink) or DANGER_MODEL.search(clink)   # (e), (g2)
            if INSTR.search(clink) and (INSTR_COLON.search(clink) or {w.lower() for w in COMMENT_ADDRESS.findall(clink)} - {'instruction', 'instructions'}): danger = True   # E-fix
            aw = {w.lower() for w in COMMENT_ADDRESS.findall(clink)}
            if COMMENT_ADDRESS.search(clink) or has_link(clink): comment_signal = True   # (j)
            if aw and aw <= L_SECOND:   # (l)
                rest = DANGER_SECOND.sub(' ', clink)
                other = DANGER_IMPER.search(rest) or DANGER_PATH.search(rest) or has_link(rest) or DANGER_CMD.search(rest) or DANGER_MODEL.search(rest)
                if not other and not L_REQUEST.search(clink) and len(re.findall(r"[A-Za-z][A-Za-z']*", clink)) <= 20: danger = None
            if len(aw) == 1 and aw <= E2_WORDS:   # (e2)
                rest = E2_RE.sub(' ', clink)
                danger = DANGER_SECOND.search(rest) or DANGER_IMPER.search(rest) or DANGER_PATH.search(rest) or has_link(rest) or DANGER_CMD.search(rest) or DANGER_MODEL.search(rest)
            if (COMMENT_ADDRESS.search(clink) and danger) or (SET_ASIDE.search(clink) and SET_ASIDE_WITH.search(clink)): flags.append(f'line {no}: a comment that addresses a reader or asks for an action')
            if len(ctext) > 400: flags.append(f'line {no}: a comment line longer than 400 characters')
        if col0 and not inside and not cont and not derive and not limited and not own_inst and decide is None and not ra and not rd and not rh and not ALLOWED.match(line) and not LIMIT.fullmatch(line):
            flags.append(f'line {no}: a column-0 line that is not an allowed command (or is comment prose)')
        if '/-' in st[1:] or '-/' in st[:-2] or ('--' in st and ('/-' in st or '-/' in st) and not st.startswith('/-')):
            flags.append(f'line {no}: a comment marker inside the line')
        # Two honest forms that are not flags (seven accepted files were flagged for them alone,
        # 2026-11-23): a markdown heading that opens a doc comment line (`/-! ### Title -/`: prose,
        # and a command word after it is still read), and `open scoped <Name>`, which brings a
        # library namespace's notation and instances into scope and runs nothing of the author's.
        # The shapes ruled plain are shapes of CODE: none of them is applied to comment text.
        seen = OK_ATTR.sub('', LIMIT.sub('', code))
        # A bit-vector literal, value#width: a # with a decimal digit on BOTH sides, in code. No
        # command is written that way (a command's # is followed by a letter). (2026-11-24: one
        # accepted file carried 162 of them.)
        seen = re.sub(r'(?<=[0-9])#(?=[0-9])', ' ', seen)
        # (k), red team 03:03Z: a hash with an identifier character glued before it and a digit after it, in code, is the
        # fixed-width numeral notation with a variable as the value; a hash command begins a token and never has one glued
        # before it, and a hash followed by a letter stays flagged.
        seen = re.sub(r"(?<=[A-Za-z0-9_'])#(?=[0-9])", ' ', seen)
        seen = re.sub(r'^(\s*/-[-!]\s*)#{1,6} ', r'\1', seen)
        seen = re.sub(r'^(\s*)open scoped (?=[A-Z])', r'\1open ', seen)
        seen = DATA_DECL.sub('', seen)
        if own_inst: seen = seen[own_inst.end():]
        if decide is not None and code: seen = seen[decide:]
        if CORE_DERIVE.fullmatch(seen): seen = ''
        if not code: seen = ''
        ctext_read = re.sub(r'`[\(\[\{]', ' ', OUR_LINK.sub(' ', ctext)) if ctext else ''   # (c), (g)
        seen += ' ' + re.sub(r'^(\s*/-[-!]\s*)#{1,6} ', r'\1', re.sub(r'#(?![A-Za-z])', ' ', ctext_read)) if ctext else ''
        if line.startswith('import') and not IMPORT_OK.fullmatch(line):
            flags.append(f'line {no}: an import outside Mathlib and the project')
        m = FORBIDDEN.search(seen)
        if m: flags.append(f'line {no}: a word on the forbidden list')
        if re.match(r'(@\[(local )?simp\] )?((private|protected) )?theorem ', rest if limited else line): theorems += 1
        # P1: a character literal ('(' and the like) opens no bracket; the count skips single-quoted characters.
        for ch in CHAR_LIT.sub(' ', code):
            if ch in '([{\u27e8\u2983': bdepth += 1
            elif ch in ')]}\u27e9\u2984': bdepth = max(bdepth - 1, 0)
        if st: last_code = is_code_line
    if depth > 0: flags.append('a block comment is never closed')
    # (j), red team 02:51Z: over 20,000 characters of comments is plain only if no comment line holds an addressing word or a
    # link and the total is at most 40,000.
    if comment_chars > 20000 and (comment_signal or comment_chars > 40000): flags.append('more than 20,000 characters of comments')
    if theorems == 0: flags.append('no theorem in the file')
    if flags:
        print(f'FLAG ({len(flags)}): see them with tools/outside-view.py before any record')
        for f in (flags if '--all' in sys.argv else flags[:40]): print('  ' + f)
        return 1
    print(f'PLAIN: {len(text.splitlines())} lines, declarations and proofs only (raw text, nothing stripped)')
    return 0

if __name__ == '__main__':
    args = [a for a in sys.argv[1:] if a != '--all']
    if len(args) != 1: print(__doc__); sys.exit(2)
    sys.exit(main(args[0]))
