#!/usr/bin/env python3
"""THE RUNNER READER'S DECISION (27 Nov; the red team decisions ISOLATED-READER-redteam1-1354 and -redteam2-1355).

    python3 -I tools/read-decision.py <file> <judge blob>    one JSON decision line for the file
    python3 -I tools/read-decision.py --vocab                the closed vocabulary, for the publishing step

Runs ONLY in the authoritative workflow's `read` job: a job that never runs contributor code, inside a network
namespace, as nobody, with no credential and under limits. It reads the one file as bytes (never builds, imports or
runs it) through tools/outside-read.py, then applies the union rule to EVERY flag the reader raised, and prints ONE line:

    {"classifier": VERSION, "authorized": [...], "decision": "PLAIN"|"UNION"|"HOLD", "classes": [...],
     "shapes": [[line, code, first, prev], ...], "nshapes": n}

Every field is a number or a word of the closed lists below, so no byte of the file can reach the output. Any error
prints the fixed HOLD line with the shape code ERROR and nothing else (no message, no traceback).

THE UNION RULE is the script the red team read (auto-record-union.lookup.py, sha256 8b2cc024834614c5...), with these
differences, each stricter or a move of a term to this runner:
  1. nothing is written (no state, no read record, no log); "bytes = judged head" is the intake's match of this job's
     receipt to the check job of the same run attempt;
  2. a FILE-level flag of the reader (control characters, not UTF-8, no theorem, an unclosed block comment, too many
     comment characters, the size) holds the file; the old script looked only at "line N:" flags;
  3. the own-class line (class_ok) and the root-type widening (root_type_ok) are OFF: both look names up in our
     definitions root and the pinned library, which this network-free job does not hold. A class line or a standalone
     deriving of a type the file did not declare holds, as before those rulings;
  4. the instance rule's term 1 is the judge of THIS run: the base checkout's tools/check-lean.mjs must be the tested
     blob, passed in as <judge blob> by the workflow from its own checkout;
  5. a held file names every failing line by shape codes (the old script stopped at the first).
"""
import contextlib, importlib.util, io, json, os, re, sys

VERSION = "rd-1"
AUTHORIZED = ("comment-word", "continuation", "instance", "lookalike")
TESTED_BLOB = "eb4c06d94767d08ae360d1747b706244f146b6b4"   # the instance rule's term 1 (auto-record-instclass.sh)
MAX_SHAPES = 32
MAX_COUNT = 100000

# The reader's labels, by their fixed start, to closed codes. A line flag is "  line N: <label>"; a file flag "  <label>".
LINE_CODES = (("a column-0 line that is not an allowed command", "COL0"), ("a word on the forbidden list", "WORD"),
              ("letters that look like Latin ones", "LOOK"), ("a comment marker inside the line", "MARK"),
              ("a link or an address inside a comment", "LINK"), ("a comment that addresses a reader or asks for an action", "ADDR"),
              ("a comment line longer than 400 characters", "LONGC"), ("an import outside Mathlib and the project", "IMPORT"))
FILE_CODES = (("larger than 512 KiB", "SIZE"), ("control characters in the file", "CTRL"),
              ("invisible or direction-changing characters", "INVIS"), ("a block comment is never closed", "OPENC"),
              ("more than 20,000 characters of comments", "MANYC"), ("no theorem in the file", "NOTHM"))
CODES = tuple(c for _, c in LINE_CODES) + tuple(c for _, c in FILE_CODES) + ("OTHER", "FILE", "UTF8", "UNREAD", "TERM1", "ERROR")
# Token codes for the first code token of a failing line and the last code token of the code line before it.
KEYWORDS = ("import", "namespace", "end", "section", "open", "variable", "universe", "omit", "include", "theorem", "lemma",
            "def", "abbrev", "structure", "inductive", "private", "protected", "noncomputable", "termination_by",
            "decreasing_by", "where", "by", "with", "then", "else", "do", "fun", "match", "calc", "have", "show", "at",
            "instance", "class", "deriving", "attribute", "example", "set_option", "local", "scoped", "export", "mutual",
            "axiom", "opaque", "partial", "unsafe", "notation", "macro", "syntax", "elab", "sorry")
TOKENS = ("empty", "comment", "attr", "bar", "dot", "hash", "open", "close", "num", "ident", "sym") \
         + tuple("kw:" + w for w in KEYWORDS) + tuple(f"cont:{i}" for i in range(18))

HERE = os.path.dirname(os.path.abspath(__file__))
def load_reader():
    spec = importlib.util.spec_from_file_location("outside_read", os.path.join(HERE, "outside-read.py"))
    rd = importlib.util.module_from_spec(spec); spec.loader.exec_module(rd); return rd

# ---- the union rule's pieces, as read (auto-record-union.lookup.py), minus the file and library lookups ----
LOOK = re.compile('[Ѐ-ԯ԰-֏Ꭰ-᏿！-～]')
INST_WORDS = {'instance', 'local', 'export', 'mutual', 'inductive', 'structure'}
DERIVE_OK = {'DecidableEq', 'Repr', 'BEq', 'Hashable', 'Inhabited', 'Ord', 'Fintype'}
STANDALONE = re.compile(r'^deriving\s+instance\s+(.+?)\s+for\s+(.+?)\s*$')
CONT_TOKENS = [':=', '=>', '<|', ',', '(', '[', '{', '⟨', '↦', '∧', '∨', '→', '↔', '=', '+', '*', '$', ':']
COL0, WORD, LOOKL = 'COL0', 'WORD', 'LOOK'

def declared(text, cm, name):
    for m in re.finditer(r'(?m)^[ \t]*(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*(?:inductive|structure)\s+' + re.escape(name) + r'(?![A-Za-z0-9_.\'!?])', text):
        if not cm[m.start() + len(m.group()) - len(name)]: return True
    return False
def root_type_ok(t, text, cm): return False   # OFF (3 above): turned on only by a reviewed patch with a committed name list
def deriving_ok(line, text=None, cm=None):
    sa = STANDALONE.match(line)
    if sa:
        hs = [h.strip() for h in sa.group(1).split(',')]; ts = [t.strip() for t in sa.group(2).split(',')]
        if not (bool(hs) and all(h in DERIVE_OK for h in hs) and bool(ts) and text is not None
                and all(re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*", t) for t in ts)): return False
        return all(declared(text, cm, t) or root_type_ok(t, text, cm) for t in ts)
    d = re.search(r'\bderiving\b(.*)$', line)
    hs = re.findall(r'[A-Za-z_][A-Za-z0-9_.]*', d.group(1)) if d else []
    return bool(hs) and all(h in DERIVE_OK for h in hs)
def class_ok(line, text, cm): return False   # OFF (3 above): the same
def continuation_ok(n, lines, starts, cm):
    j = n - 2
    while j >= 0:
        code = ''.join(ch for k, ch in enumerate(lines[j]) if not cm[starts[j] + k]).rstrip()
        if code.strip(): break
        j -= 1
    if j < 0: return False
    if re.search(r'(?<![A-Za-z0-9_.\'])fun$', code): return True
    return any(code.endswith(t) for t in CONT_TOKENS)
def comment_mask(text):
    m = [False] * len(text); i = 0; mode = 0
    while i < len(text):
        two = text[i:i + 2]
        if mode == 0:
            if two == '--': mode = 1; m[i] = m[i + 1] = True; i += 2; continue
            if two == '/-': mode = 2; depth = 1; m[i] = m[i + 1] = True; i += 2; continue
            if text[i] == '"': mode = 3
        elif mode == 1:
            m[i] = True
            if text[i] == '\n': mode = 0
        elif mode == 2:
            m[i] = True
            if two == '/-': depth += 1; m[i + 1] = True; i += 2; continue
            if two == '-/':
                depth -= 1; m[i + 1] = True; i += 2
                if depth == 0: mode = 0
                continue
        elif mode == 3:
            if text[i] == '\\': i += 2; continue
            if text[i] == '"': mode = 0
        i += 1
    return m

# ---- shape codes: words of the lists above, never a character of the file ----
def code_of(lines, starts, cm, j):
    return ''.join(ch for k, ch in enumerate(lines[j]) if not cm[starts[j] + k])
def first_token(code):
    s = code.strip()
    if not s: return 'empty'
    if s.startswith('@['): return 'attr'
    m = re.match(r"[A-Za-z_][A-Za-z0-9_']*", s)
    if m: return 'kw:' + m.group() if m.group() in KEYWORDS else 'ident'
    c = s[0]
    if c.isdigit(): return 'num'
    if c == '|': return 'bar'
    if c in '·.': return 'dot'
    if c == '#': return 'hash'
    if c in '([{⟨⦃': return 'open'
    if c in ')]}⟩⦄': return 'close'
    return 'sym'
def last_token(code):
    s = code.rstrip()
    if not s.strip(): return 'empty'
    for i, t in enumerate(CONT_TOKENS):
        if s.endswith(t): return f'cont:{i}'
    m = re.search(r"(?<![A-Za-z0-9_.'])([A-Za-z_][A-Za-z0-9_']*)$", s)
    if m: return 'kw:' + m.group(1) if m.group(1) in KEYWORDS else 'ident'
    c = s[-1]
    if c.isdigit(): return 'num'
    if c in ')]}⟩⦄': return 'close'
    return 'sym'
def shape(n, codes, lines, starts, cm):
    if not (1 <= n <= len(lines)): return [0, '+'.join(sorted(codes)), 'empty', 'empty']
    here = code_of(lines, starts, cm, n - 1)
    first = first_token(here) if here.strip() else ('comment' if lines[n - 1].strip() else 'empty')
    prev, j = 'empty', n - 2
    while j >= 0:
        c = code_of(lines, starts, cm, j)
        if c.strip(): prev = last_token(c); break
        j -= 1
    return [n, '+'.join(sorted(codes)), first, prev]

def decide(path, judge):
    rd = load_reader()
    buf = io.StringIO(); argv = sys.argv; sys.argv = ['outside-read.py', '--all']
    try:
        with contextlib.redirect_stdout(buf): code = rd.main(path)
    finally: sys.argv = argv
    out = buf.getvalue()
    if code == 0 and out.startswith('PLAIN'): return 'PLAIN', [], []
    if code != 1: return 'HOLD', [], [[0, 'UNREAD', 'empty', 'empty']]
    if out.startswith('FLAG: not UTF-8'): return 'HOLD', [], [[0, 'UTF8', 'empty', 'empty']]
    labels, filewide = {}, []
    for ln in out.split('\n')[1:]:
        if not ln.startswith('  '): continue
        mm = re.match(r'^  line (\d+): (.*)$', ln)
        if mm:
            labels.setdefault(int(mm.group(1)), set()).add(next((c for L, c in LINE_CODES if mm.group(2).startswith(L)), 'OTHER'))
        else:
            filewide.append(next((c for L, c in FILE_CODES if ln[2:].startswith(L)), 'FILE'))
    text = open(path, 'rb').read().decode('utf-8'); lines = text.split('\n')
    starts = [0]
    for l in lines[:-1]: starts.append(starts[-1] + len(l) + 1)
    cm = comment_mask(text); got = set(); held = []
    for n, labs in sorted(labels.items()):
        if not (1 <= n <= len(lines)): held.append((n, labs)); continue
        line = lines[n - 1]; base = starts[n - 1]
        words = [(x.start(), x.group().strip()) for x in rd.FORBIDDEN.finditer(line)]
        first_c = line.find('--')
        if labs == {WORD} and first_c >= 0 and words and all(p > first_c for p, _ in words) and all(cm[base + p] for p, _ in words):
            got.add('comment-word'); continue
        if labs <= {COL0, WORD} and words and all(w in INST_WORDS or (w == 'deriving' and deriving_ok(line, text, cm)) or (w == 'class' and class_ok(line, text, cm)) for _, w in words) and not any(t in line for t in ('--', '/-', '"')):
            got.add('instance'); continue
        if labs == {COL0} and not words and continuation_ok(n, lines, starts, cm):
            got.add('continuation'); continue
        if labs == {LOOKL}:
            pos = [x.start() for x in LOOK.finditer(line)]
            if pos and all(cm[base + p] for p in pos): got.add('lookalike'); continue
        held.append((n, labs))
    shapes = [[0, c, 'empty', 'empty'] for c in sorted(set(filewide))] + [shape(n, labs, lines, starts, cm) for n, labs in held]
    if not labels and not filewide: shapes = [[0, 'OTHER', 'empty', 'empty']]
    if shapes: return 'HOLD', [], shapes
    if 'instance' in got and judge != TESTED_BLOB: return 'HOLD', [], [[0, 'TERM1', 'empty', 'empty']]
    if not got <= set(AUTHORIZED): return 'HOLD', [], [[0, 'OTHER', 'empty', 'empty']]
    return 'UNION', sorted(got), []

def line_of(decision, classes, shapes):
    return json.dumps({"classifier": VERSION, "authorized": list(AUTHORIZED), "decision": decision, "classes": classes,
                       "shapes": shapes[:MAX_SHAPES], "nshapes": min(len(shapes), MAX_COUNT)}, separators=(',', ':'), ensure_ascii=True)

if __name__ == '__main__':
    if sys.argv[1:] == ['--vocab']:
        print(json.dumps({"classifier": VERSION, "authorized": list(AUTHORIZED), "codes": list(CODES), "tokens": list(TOKENS),
                          "max_shapes": MAX_SHAPES, "max_count": MAX_COUNT}, separators=(',', ':'))); sys.exit(0)
    try:
        if len(sys.argv) != 3 or not re.fullmatch(r'[0-9a-f]{40}', sys.argv[2]): raise ValueError
        d, c, s = decide(sys.argv[1], sys.argv[2])
        s = [[min(max(int(n), 0), MAX_COUNT), k, f, p] for n, k, f, p in s]
        print(line_of(d, c, s))
    except BaseException:
        print(line_of('HOLD', [], [[0, 'ERROR', 'empty', 'empty']]))
    sys.exit(0)
