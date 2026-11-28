"""Private diagnostic worker. The jail emits one bounded bin to the receipt process."""
from bisect import bisect_right
from pathlib import Path
import re
import runpy
import sys
from typing import NamedTuple

BASELINE = runpy.run_path(str(Path(__file__).resolve().with_name('read-decision.py')))
COMMANDS = ('theorem', 'lemma', 'def', 'example', 'abbrev')
COMMAND_HEADS = frozenset(COMMANDS) | {'import', 'namespace', 'end'}
KEYWORDS = frozenset(BASELINE['KEYWORDS']) | {'exact', 'rfl'}
CONSTANTS = frozenset('Nat Nat.succ Nat.zero Eq.refl True True.intro String Char List Prod'.split())
OPENERS, CLOSERS = '([{⟨', ')]}⟩'
ROUND, SQUARE, CURLY, ANGLE, BODY, UNCERTAIN = range(6)
PAD, NAME, NUMBER, STRING, CHAR, KEYWORD, OPERATOR, SEPARATOR, OPEN = range(9)
CLOSE = OPEN + 4
GROUP_OPERAND, GROUP_OTHER, BODY_OTHER, MIXED, UNKNOWN, OVERFLOW = range(6)
UNKNOWN_SHAPE = bytes((2, 5, UNCERTAIN, 0, 0, 0, 0) + (PAD,) * 8)
MAX_SOURCE = 524288
WIDTHS = (2, 4, 2)
WIRE = tuple(f'[2,{i}]\n'.encode('ascii') for i in range(6))

# Match tokens at the cursor only. Unsupported spellings have no fallback token.
IDENT = r'[A-Za-z_][A-Za-z_0-9ₐ₀-₉]*'
WORD = re.compile(IDENT + r'(?:\.' + IDENT + r')*')
LEX = re.compile(r'(?P<space>[ \t\n]+)|(?P<comment>--[^\n]*|/-)|(?P<word>' + WORD.pattern
                 + r')|(?P<number>[0-9]+)|(?P<string>"(?:[^"\\\n]|\\["\\nt])*")'
                 + r"|(?P<char>'(?:[^'\\\n]|\\['\\nt])')|(?P<symbol>:=|[():,=+*\-\[\]{}⟨⟩])")
BLOCK = re.compile(r'/-|-/')
CONTROLS = re.compile(r'[\x00-\x08\x0b-\x1f\x7f\u200b-\u200f\u202a-\u202e\u2060-\u2069\ufeff]')


class Refused(ValueError):
    pass


def require(ok):
    if not ok:
        raise Refused


class Token(NamedTuple):
    word: str
    kind: int
    line: int
    margin: bool


def lex(raw):
    require(len(raw) <= MAX_SOURCE)
    text = raw.decode('utf-8').replace('\r\n', '\n')
    require(not CONTROLS.search(text))
    pos, line = 0, 1
    while pos < len(text):
        match = LEX.match(text, pos)
        require(match)
        end = match.end()
        tag, word = match.lastgroup, match[0]
        if word == '/-':
            require(not text.startswith(('/--', '/-!'), pos))
            depth = 1
            while depth:
                marker = BLOCK.search(text, end)
                require(marker)
                end = marker.end()
                depth += 1 if marker[0] == '/-' else -1
        elif tag not in ('space', 'comment'):
            if tag == 'word':
                kind = KEYWORD if word in KEYWORDS else NAME
            elif tag in ('string', 'char', 'number'):
                kind = {'string': STRING, 'char': CHAR, 'number': NUMBER}[tag]
                word = ''  # discard the literal now
            elif word in OPENERS:
                kind = OPEN + OPENERS.index(word)
            elif word in CLOSERS:
                kind = CLOSE + CLOSERS.index(word)
            else:
                kind = SEPARATOR if word in (',', ':', ':=') else OPERATOR
            # Glued atoms include string prefixes and unsupported numeric formats.
            if tag in ('word', 'number', 'string', 'char') and end < len(text):
                require(not (text[end].isalnum() or text[end] in '_\'"'))
            yield Token(word, kind, line, pos == 0 or text[pos - 1] == '\n')
        line += text.count('\n', pos, end)
        pos = end


class CommandReader:
    """Consume complete commands of the pinned subset before trusting their spans."""
    def __init__(self, tokens):
        self.tokens = tokens
        self.i = 0
        self.ends = {}
        self.commands = []
        self.names = set()

    def token(self):
        return self.tokens[self.i] if self.i < len(self.tokens) else Token('', PAD, 0, False)

    def take(self, word):
        require(self.token().word == word)
        self.i += 1

    def name(self):
        token = self.token()
        require(token.kind == NAME)
        self.i += 1
        return token.word

    def atom(self, depth):
        require(depth <= 64)
        token = self.token()
        if OPEN <= token.kind < CLOSE:
            start = self.i
            self.i += 1
            closer = CLOSERS[token.kind - OPEN]
            if self.token().word != closer or token.word not in ('[', '('):
                self.expression(depth + 1)
                while self.token().word == ',':
                    self.i += 1
                    self.expression(depth + 1)
            self.take(closer)
            self.ends[start] = self.i
        else:
            require(token.kind in (NUMBER, STRING, CHAR) or token.word in self.names
                    or token.word in CONSTANTS or token.word == 'rfl')
            self.i += 1

    def expression(self, depth=0):
        self.atom(depth)
        while True:
            token = self.token()
            if token.kind == OPERATOR:
                self.i += 1
            elif (depth or token.line == self.tokens[self.i - 1].line) and (
                    token.kind in (NUMBER, STRING, CHAR) or OPEN <= token.kind < CLOSE
                    or token.word in self.names or token.word in CONSTANTS):
                pass  # juxtaposed argument within a group or on the same line
            else:
                return
            self.atom(depth)

    def parse(self):
        scopes = []
        while self.i < len(self.tokens):
            start = self.i
            head = self.token()
            require(head.margin and head.kind == KEYWORD)
            self.i += 1
            if head.word in ('import', 'namespace', 'end'):
                name = self.name()
                require(self.tokens[start + 1].line == head.line)
                if head.word == 'import':
                    require(not scopes and not self.commands and name in ('Mathlib', 'PEqualNP.Defs'))
                elif head.word == 'namespace':
                    scopes.append(name)
                else:
                    require(scopes and scopes.pop() == name)
                continue
            require(head.word in COMMANDS)
            if head.word != 'example':
                self.name()
            self.names.clear()
            while self.token().word == '(':
                opening = self.i
                self.i += 1
                binder = self.name()
                require('.' not in binder)
                self.take(':')
                self.expression(1)
                self.take(')')
                self.ends[opening] = self.i
                self.names.add(binder)
            self.take(':')
            self.expression()
            body = self.i
            self.take(':=')
            if self.token().word == 'by':
                self.i += 1
                require(not self.token().margin)
                if self.token().word == 'rfl':
                    self.i += 1
                else:
                    self.take('exact')
                    self.expression()
            else:
                self.expression()
            following = self.token()
            require(self.i == len(self.tokens) or (following.margin and following.word in COMMAND_HEADS))
            self.commands.append((start, body, self.i, COMMANDS.index(head.word)))
        require(not scopes)


def valid(shape):
    if type(shape) is not bytes or len(shape) != 15:
        return False
    if shape == UNKNOWN_SHAPE:
        return True
    version, cmd, group, depth, *bits = shape[:7]
    if (version != 2 or cmd >= 5 or group > BODY or depth > 3
            or (group == BODY) != (depth == 0) or max(bits) > 1 or max(shape[7:]) >= CLOSE + 4):
        return False
    for idx, window in enumerate((shape[7:9][::-1], shape[9:13], shape[13:15])):
        if PAD in window and (bits[idx] or any(window[window.index(PAD):])):
            return False
    return shape[9] != PAD


def encode(cmd, group, depth, tokens, lo, first, after, hi):
    # Intersect each physical slice with the same nearest construct.
    after = min(after, hi)
    counts = (first - lo, after - first, hi - after)
    slices = (tokens[max(lo, first - 2):first], tokens[first:min(first + 4, after)],
              tokens[after:min(after + 2, hi)])
    fields = [2, cmd, group, min(depth, 3), *(int(n > w) for n, w in zip(counts, WIDTHS))]
    for i, (window, width) in enumerate(zip(slices, WIDTHS)):
        values = [t.kind for t in window]
        pad = [PAD] * (width - len(values))
        fields.extend(pad + values if i == 0 else values + pad)
    packet = bytes(fields)
    return packet if valid(packet) else UNKNOWN_SHAPE


def shapes(raw, held):
    tokens = []
    try:
        tokens.extend(lex(raw))
    except (UnicodeError, Refused):
        # A lexical failure cannot serve as an end-of-file command boundary.
        tokens.append(Token('', -1, tokens[-1].line if tokens else 1, False))
    parser = CommandReader(tokens)
    try:
        parser.parse()
    except Refused:
        # Only commands already closed at a proven boundary have spans.
        # Do not scan ahead to a plausible keyword after losing the boundary.
        pass
    lines = [t.line for t in tokens]
    for start, body, end, cmd in parser.commands:
        stack = []
        for i in range(start, end):
            while stack and i >= stack[-1][1]:
                stack.pop()
            line = lines[i]
            if line in held and (i == 0 or lines[i - 1] != line):
                held.remove(line)
                if stack:
                    lo, hi = stack[-1]
                    group = tokens[lo].kind - OPEN
                else:
                    lo, hi, group = body, end, BODY
                if i < lo:
                    yield UNKNOWN_SHAPE
                else:
                    after = bisect_right(lines, line, i, hi)
                    yield encode(cmd, group, len(stack), tokens, lo, i, after, hi)
            if i in parser.ends:
                stack.append((i, parser.ends[i]))
    if held:
        yield UNKNOWN_SHAPE


def file_bin(packets):
    distinct, classes = set(), set()
    for packet in packets:
        # Independent collector check before hashing or indexing the packet.
        if not valid(packet):
            packet = UNKNOWN_SHAPE
        if packet in distinct:
            continue
        if len(distinct) == 4:
            return OVERFLOW
        distinct.add(packet)
        if packet == UNKNOWN_SHAPE:
            classes.add(UNKNOWN)
        elif packet[2] == BODY:
            classes.add(BODY_OTHER)
        elif packet[8] == OPERATOR and packet[9] in (NAME, NUMBER):
            classes.add(GROUP_OPERAND)
        else:
            classes.add(GROUP_OTHER)
    if not classes:
        return UNKNOWN
    return classes.pop() if len(classes) == 1 else MIXED


def observe(path, judge):
    require(re.fullmatch('[0-9a-f]{40}', judge))
    with open(path, 'rb') as source:
        raw = source.read(MAX_SOURCE + 1)
    require(len(raw) <= MAX_SOURCE)
    # The staged proof is read-only. Use main's uncapped decision before line_of
    # truncates the receipt, including its independent holds and union rules.
    decision, _, rows = BASELINE['decide'](path, judge)
    held = {line for line, reasons, _, _ in rows if line > 0 and 'COL0' in reasons.split('+')}
    if decision != 'HOLD' or not held:
        return None  # contradicts frozen receipt membership
    return file_bin(shapes(raw, held))


if __name__ == '__main__':
    try:
        path, judge = sys.argv[1:]
        result = observe(path, judge)
    except Exception:
        result = UNKNOWN
    if result is None:
        sys.exit(3)
    sys.stdout.buffer.write(WIRE[result])
